import data.nat.factorization.basic
import algebra.group.basic
import data.nat.basic
import data.nat.prime
import tactic

lemma add_cancel_thing (n m k : ℕ ) : n + m = n + k → m = k :=
begin
  refine nat.add_left_cancel,
end

lemma inequality_thing (a : ℕ ) (ha : a ≥ 2) : 2*a^2 + 1 ≥ (a + 1)^2 :=
begin
  have h1 : a^2 + 2*a + 1 = (a + 1)^2,
  {
    ring_nf,
  },
  have h2 : a^2 ≥ 2*a,
  {
    simp,
    have h3 := nat.mul_le_mul_right a ha,
    ring_nf at h3,
    refine h3,
  },
  have h3 : a^2 + a^2 = 2*a^2,
  {
    ring_nf,
  },
  rw ← h3,
  rw ← h1,
  have h4 := nat.add_le_add_left h2 (a^2),
  have h5 := nat.add_le_add_right h4 1,
  simp,
  refine h2,
end

lemma a_dvd_b_2 (a b : ℕ ) (hd : a ∣ b^3) (hcfree : ∀ (p : ℕ) , p.prime → p ∣ a → ¬ (p^3 ∣ a)) (hap : a > 0) (hbp : b > 0):
  a ∣ b^2 :=
begin
  have hdb : ∀ (p : ℕ) , p.prime → p ∣ b → p^2 ∣ b^2,
  {
    rintro p,
    rintro hp,
    rintro hd,
    cases hd with k key,
    use k^2,
    rw key,
    ring_nf,
  },
  cases nat.dvd_iff_prime_pow_dvd_dvd (b^2) a with h1 h2,
  apply h2,
  rintro p k,
  rintro hp,
  rintro hpka,
  have hane0 : a ≠ 0,
  {
    linarith,
  },
  have hbne0 : b^2 ≠ 0,
  {
    have h1 := nat.one_le_pow 2 b hbp,
    linarith,
  },
  have hle2 : k ≤ 2,
  {
    by_cases hk : k ≥ 1,
    {
      have hc := hcfree(p),
      have hc1 := hc hp,
      have hpa := nat.dvd_of_pow_dvd hk hpka,
      have hc2 := hc1 hpa,
      by_contradiction,
      have hk3 : k ≥ 3,
      {
        linarith,
      },
      have hp3 : 3 ≤ a.factorization p,
      {
        cases nat.prime.pow_dvd_iff_le_factorization hp hane0 with h3 h4,
        have h5 := h3 hpka,
        linarith,
      },
      have hp3a : p^3 ∣ a,
      {
        cases nat.prime.pow_dvd_iff_le_factorization hp hane0 with h3 h4,
        refine h4 hp3,
      },
      have hf := hc2 hp3a,
      refine false.elim hf,
    },
    {
      linarith,
    },
  },
  by_cases hk : k > 0,
  {
    have hva : 1 ≤ a.factorization p,
    {
      cases nat.prime.pow_dvd_iff_le_factorization hp hane0 with h3 h4,
      have h5 := h3 hpka,
      linarith,
    },
    have ha : p^1 ∣ a,
    {
      cases nat.prime.pow_dvd_iff_le_factorization hp hane0 with h3 h4,
      have h5 := h4 hva,
      refine h5,
    },
    have hb : p ∣ b,
    {
      cases nat.dvd_iff_prime_pow_dvd_dvd (b^3) a with h3 h4,
      have h5 := h3 hd,
      have h5p := h5 p 1,
      have h6 := h5p hp,
      have h7 := h6 ha,
      have hpexp : p^1 = p,
      {
        simp,
      },
      rw hpexp at h7,
      have h8 := nat.prime.dvd_of_dvd_pow hp h7,
      refine h8,
    },
    have hdp := hdb(p),
    have h1 := hdp hp,
    have h2 := h1 hb,
    have hvpkb : k ≤ (b^2).factorization p,
    {
      cases nat.prime.pow_dvd_iff_le_factorization hp hbne0 with h3 h4,
      have h5 := h3 h2,
      linarith,
    },
    cases nat.prime.pow_dvd_iff_le_factorization hp hbne0 with h6 h7,
    refine h7 hvpkb,
  },
  {
    have hk : k = 0,
    {
      linarith,
    },
    have hp1 : p^k = 1,
    {
      rw hk,
      simp,
    },
    rw hp1,
    norm_num,
  },
end

theorem ISL_2021_N1 (a b n : ℕ) (hap : a > 0) (hbp : b > 0) (hnp : n > 0)
  (hcfree : ∀ (p : ℕ) , p.prime → ¬ (p^3 ∣ a^2 + b + 3))
    (hn : n * (a^2 + b + 3) = a*b + 3*b + 8) : n = 2 :=
begin

have hd1 : a^2+b+3 ∣ a*b+3*b+8,
use n,
rw ← hn,
rw mul_comm n (a^2+b+3),
have hd2 : a^2+b+3 ∣ (a+3)*(a^2+b+3),
use a + 3,
rw mul_comm,
have hexpand : (a + 3) * (a^2  + b + 3) = a^3 + a*b + 3*a + 3 * a^2 + 3 * b + 9,
{
  ring_nf,
},
have h1 : a^3 + a*b + 3*a + 3*a^2 + 3*b + 9 = (a*b + 3*b + 8) + a^3 + 3*a^2 + 3*a + 1,
{
  ring_nf,
},
have h2 : a*b + 3*b + 8 + (a^3 + 3*a^2 + 3*a + 1) - (a*b + 3*b + 8) = a^3 + 3*a^2 + 3*a + 1,
{
  refine nat.add_sub_cancel_left (a*b + 3*b + 8) (a^3 + 3*a^2 + 3*a + 1),
},
have h3 : a*b + 3*b + 8 + a^3 + 3*a^2 + 3*a + 1 - (a*b + 3*b + 8) = a*b + 3*b + 8 + (a^3 + 3*a^2 + 3*a + 1) - (a*b + 3*b + 8),
{
  ring_nf,
},
have hdcube : (a + 3) * (a^2 + b + 3) - (a*b + 3*b + 8) = a^3 + 3*a^2 + 3*a + 1,
{
  rw hexpand,
  rw h1,
  rw ← h3 at h2,
  rw h2,
},
have hsimpcube : a^3 + 3*a^2 + 3*a + 1 = (a + 1)^3,
{
  ring_nf,
},
have hcube : (a + 3) * (a^2 + b + 3) - (a*b + 3*b + 8) = (a + 1)^3,
{
  rw hdcube,
  rw hsimpcube,
},
have hineq : a*b + 3*b + 8 ≤ (a + 3) * (a^2 + b + 3),
{
  linarith,
},
have hd3 : a^2 + b + 3 ∣ (a + 1)^3,
{
  have h3 := nat.dvd_sub hineq,
  have h4 := h3 hd2,
  have h5 := h4 hd1,
  rw hcube at h5,
  refine h5,
},
have ha2 : a^2 > 0,
{
  refine nat.one_le_pow 2 a hap, 
},
have hp1 : a^2 + b + 3 > 0,
{
  linarith,
},
have hp2 : a + 1 > 0,
{
  linarith,
},
have hdsquare := a_dvd_b_2 (a^2 + b + 3) (a + 1) hd3 hcfree hp1 hp2,
cases hdsquare with c hc,
have hc1 : c = 1, 
{
  by_contradiction,
  by_cases hc0 : c = 0,
  {
    rw hc0 at hc,
    linarith,
  },
  {
    have hcge2: c ≥ 2,
    {
      cases nat.one_lt_iff_ne_zero_and_ne_one with h3 h4,
      have h5 := h4 ⟨hc0, h⟩,
      linarith,
    },
    have hc2 : (a + 1)^2 ≥ 2 * (a^2 + b + 3),
    {
      rw hc,
      have hr := nat.mul_le_mul_right (a^2 + b + 3) hcge2,
      linarith,
    },
    have hc3 : 2 * a^2 + 6 < 2 * (a^2 + b + 3),
    {
      linarith,
    },
    have hc4 : 2*a^2 + 6 > (a + 1)^2,
    {
      by_cases ha1 : a = 1,
      {
        linarith,
      },
      {
        have hage2 : a ≥ 2,
        {
          linarith,
        },
        have hi := inequality_thing a hage2,
        linarith,
      },
    },
    have hc5 : 2*(a^2 + b + 3) > (a + 1)^2,
    {
      linarith,
    },
    have hc6 : ¬ (a + 1)^2 ≥ 2*(a^2 + b + 3),
    {
      linarith,
    },
    have hc7 := hc6 hc2,
    refine false.elim hc7,
  },
  
},
have ha : a^2 + 2*a + 1 = (a + 1)^2,
{
  ring_nf,
},
rw hc1 at hc,
rw ← ha at hc,
simp at hc,
have hb1 := add_cancel_thing (a^2) (2*a + 1) (b + 3) hc,
have haineq : 3 ≤ 2*a + 1,
{
  linarith,
},
cases nat.sub_eq_iff_eq_add haineq with hsub hadd,
have hb2 := hadd hb1,
simp at hb2,
rw ha at hc,
rw ← hc at hn,
rw ← hb2 at hn,
have ha4 : 2*a - 2 = 2*(a - 1),
{
  linarith,
},
have h248 : 2*4 = 8,
{
  norm_num,
},
have ha3 : a*(2*a - 2) + 3*(2*a - 2) + 8 = 2*(a + 1)^2,
{
  rw ← nat.right_distrib a 3 (2*a - 2),
  rw mul_comm,
  rw ha4,
  rw ← h248,
  rw mul_assoc,
  rw ← nat.left_distrib 2 ((a - 1)*(a + 3)) 4,
  have ha5 : (a - 1)*(a + 3) = a^2 + 2*a - 3,
  {
    rw nat.left_distrib (a - 1) a 3,
    rw nat.mul_sub_right_distrib a 1 a,
    rw nat.mul_sub_right_distrib a 1 3,
    simp,
    rw ← sq,
    have ha6 : a^2 - a + (a*3 - 3) = a^2 + 2*a - 3,
    {
      have hi1 : 3 ≤ a*3,
      {
        linarith,
      },
      have hi2 : a ≤ a^2,
      {
        have hi3 := nat.le_mul_self a,
        rw ← sq at hi3,
        refine hi3,
      },
      rw ← nat.add_sub_assoc hi1 (a^2 - a),
      have ha7 : a^2 - a + a*3 - 3 = a^2 + 2*a - 3,
      {
        rw mul_comm,
        have ha8 : a^2 - a + 3*a = a^2 + 2*a,
        {
          rw ← nat.sub_add_comm hi2,
          ring_nf,
          have ha9 := nat.mul_pred_left (a + 3) a,
          rw ← ha9,
          rw nat.pred_eq_sub_one,
          simp,
        },
        rw ha8,
      },
      rw ha7,
    },
    rw ha6,
  },
  rw ha5,
  simp,
  have ha10 : a^2 + 2*a - 3 + 4 = a^2 + 2*a + 1,
  {
    have ha11 : 3 ≤ 2*a,
    {
      linarith,
    },
    have ha12 : 2*a - 3 + 4 = 2*a + 1,
    {
      rw ← nat.sub_add_comm ha11,
      simp,
    },
    cases add_right_inj (a^2) with ha13 ha14,
    have ha15 := ha14 ha12,
    rw ← add_assoc at ha15,
    rw ← nat.add_sub_assoc ha11 (a^2) at ha15,
    refine ha15,
  },
  rw ha10,
  rw ha,
},
rw ha3 at hn,
have ha1p : 0 < (a + 1)^2,
{
  refine nat.one_le_pow 2 (a + 1) hp2,
},
cases nat.mul_left_inj ha1p with h24 h25,
refine h24 hn,
end