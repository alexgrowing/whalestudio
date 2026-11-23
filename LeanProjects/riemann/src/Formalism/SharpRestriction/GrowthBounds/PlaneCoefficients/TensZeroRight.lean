import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PlaneCoeffOneTTens

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks.T5

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.PairMembershipBlocks

section Lin

variable {σ τ Kf : Type} [Field Kf]

theorem tens_monomial (mo : σ →₀ ℕ) (c : Kf) (G : MvPolynomial τ Kf) :
    tens (monomial mo c) G = monomial mo (c • G) := by
  unfold tens
  by_cases hc : c = 0
  · simp [hc]
  · rw [support_monomial, if_neg hc, Finset.sum_singleton, coeff_monomial, if_pos rfl]

def tensH (G : MvPolynomial τ Kf) (mo : σ →₀ ℕ) : Kf →+ MvPolynomial σ (MvPolynomial τ Kf) where
  toFun c := monomial mo (c • G)
  map_zero' := by simp
  map_add' c c' := by rw [add_smul, map_add]

theorem tens_add_left (A A' : MvPolynomial σ Kf) (G : MvPolynomial τ Kf) :
    tens (A + A') G = tens A G + tens A' G :=
  sumSupp_add (tensH G) A A'

theorem tens_add_right (A : MvPolynomial σ Kf) (G G' : MvPolynomial τ Kf) :
    tens A (G + G') = tens A G + tens A G' := by
  unfold tens
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [smul_add, map_add]

theorem tens_zero_left (G : MvPolynomial τ Kf) : tens (0 : MvPolynomial σ Kf) G = 0 := by simp [tens]

theorem tens_zero_right (A : MvPolynomial σ Kf) : tens A (0 : MvPolynomial τ Kf) = 0 := by simp [tens]

theorem compD_add {ι : Type} {s : ℕ} (d : ι → ℕ) (H H' : MvPolynomial (ι × Fin s) Kf) :
    compD d (H + H') = compD d H + compD d H' :=
  sumFilt_add (fun mo => ∀ x, multideg mo x = d x) (fun mo => (monomial mo : Kf →ₗ[Kf] _).toAddMonoidHom) H H'

theorem compD_zero {ι : Type} {s : ℕ} (d : ι → ℕ) : compD d (0 : MvPolynomial (ι × Fin s) Kf) = 0 := by simp [compD]

theorem compD_monomial {ι : Type} {s : ℕ} (d : ι → ℕ) (mo : ι × Fin s →₀ ℕ) (c : Kf) :
    compD d (monomial mo c) = if (∀ x, multideg mo x = d x) then monomial mo c else 0 := by
  unfold compD
  by_cases hc : c = 0
  · simp [hc]
  · rw [support_monomial, if_neg hc, Finset.filter_singleton]
    split_ifs with h
    · rw [Finset.sum_singleton, coeff_monomial, if_pos rfl]
    · rw [Finset.sum_empty]

theorem add_expand {R M : Type*} [CommSemiring R] [AddCommMonoid M] (f : MvPolynomial σ R → M) (h0 : f 0 = 0)
    (hadd : ∀ x y, f (x + y) = f x + f y) (P : MvPolynomial σ R) :
    f P = ∑ a ∈ P.support, f (monomial a (P.coeff a)) := by
  have h := map_sum (AddMonoidHom.mk ⟨f, h0⟩ hadd) (fun a => monomial a (P.coeff a)) P.support
  conv_lhs => rw [P.as_sum]
  exact h

end Lin

section Lev

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) {O : Type} [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem monomialSubstitution_add (F G : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levP Fr p hk nL (F + G) = levP Fr p hk nL F + levP Fr p hk nL G :=
  sumSupp_add (fun mo => (monomial (plMon Fr p hk nL mo) : KK O →ₗ[KK O] _).toAddMonoidHom) F G

theorem levN_add (F G : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levN Fr p hk nL (F + G) = levN Fr p hk nL F + levN Fr p hk nL G :=
  sumSupp_add (fun mo => (monomial (noMon Fr p hk nL mo) : KK O →ₗ[KK O] _).toAddMonoidHom) F G

theorem monomialSubstitution_zero : levP Fr p hk nL (0 : MvPolynomial (TV n' (m + 1)) (KK O)) = 0 := by simp [levP]

theorem levN_zero : levN Fr p hk nL (0 : MvPolynomial (TV n' (m + 1)) (KK O)) = 0 := by simp [levN]

theorem monomialSubstitution_monomial (mo : TV n' (m + 1) →₀ ℕ) (c : KK O) :
    levP Fr p hk nL (monomial mo c) = monomial (plMon Fr p hk nL mo) c := by
  unfold levP
  by_cases hc : c = 0
  · simp [hc]
  · rw [support_monomial, if_neg hc, Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem levN_monomial (mo : TV n' (m + 1) →₀ ℕ) (c : KK O) :
    levN Fr p hk nL (monomial mo c) = monomial (noMon Fr p hk nL mo) c := by
  unfold levN
  by_cases hc : c = 0
  · simp [hc]
  · rw [support_monomial, if_neg hc, Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem levImg_monomial (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (c : KK O) :
    levImg Fr p hk nL rho dPl dNo (monomial mo c) =
      if InLow Fr p hk nL rho mo ∧ InBlock Fr p hk nL dPl dNo mo then
        monomial (plMon Fr p hk nL mo) (monomial (noMon Fr p hk nL mo) c) else 0 := by
  unfold levImg
  by_cases hc : c = 0
  · simp [hc]
  · rw [support_monomial, if_neg hc, Finset.filter_singleton]
    split_ifs with h
    · rw [Finset.sum_singleton, coeff_monomial, if_pos rfl]
    · rw [Finset.sum_empty]

theorem inBlock_iff (dPl dNo : TL J nL r → ℕ) (mo : TV n' (m + 1) →₀ ℕ) :
    InBlock Fr p hk nL dPl dNo mo ↔
      (∀ x, multideg (plMon Fr p hk nL mo) x = dPl x) ∧ ∀ x, multideg (noMon Fr p hk nL mo) x = dNo x := by
  unfold InBlock multideg plMon noMon
  simp only [Finsupp.coe_equivFunOnFinite_symm]

theorem plMon_eq_zero (mo : TV n' (m + 1) →₀ ℕ) (h : ∀ x a, mo (plVar Fr hk nL x a) = 0) :
    plMon Fr p hk nL mo = 0 := by
  ext v
  simp only [plMon, Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_zero, Pi.zero_apply, h, Nat.zero_div]

theorem noMon_eq_zero (mo : TV n' (m + 1) →₀ ℕ) (h : ∀ x b, mo (noVar Fr hk nL x b) < lowP Fr p x) :
    noMon Fr p hk nL mo = 0 := by
  ext v
  simp only [noMon, Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_zero, Pi.zero_apply]
  exact Nat.div_eq_of_lt (h v.1 v.2)

theorem lev_term (hp : 0 < p) (base d b : TV n' (m + 1) →₀ ℕ) (hd : LowDiv Fr p hk nL d)
    (hd0 : ∀ x c, d (noVar Fr hk nL x c) = 0) (hb : LowDiv Fr p hk nL b) (hb0 : ∀ x a, b (plVar Fr hk nL x a) = 0)
    (hbase : ∀ x c, base (noVar Fr hk nL x c) < lowP Fr p x)
    (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (u v : KK O) :
    levImg Fr p hk nL rho dPl dNo (monomial (base + d) u * monomial b v) =
      if InLow Fr p hk nL rho base then
        tens (compD dPl (levP Fr p hk nL (monomial (base + d) u))) (compD dNo (levN Fr p hk nL (monomial b v)))
      else 0 := by
  have e1 : InLow Fr p hk nL rho (base + d + b) ↔ InLow Fr p hk nL rho base := by
    rw [add_assoc]
    exact inLow_add Fr p hk nL rho base (d + b) (lowDiv_add Fr p hk nL hd hb)
  have e2 : plMon Fr p hk nL (base + d + b) = plMon Fr p hk nL (base + d) := by
    rw [plMon_add Fr p hk nL hp _ _ hb, plMon_eq_zero Fr p hk nL b hb0, add_zero]
  have e3 : noMon Fr p hk nL (base + d + b) = noMon Fr p hk nL b := by
    rw [noMon_add Fr p hk nL hp _ _ hb, noMon_eq_zero Fr p hk nL (base + d), zero_add]
    intro x c
    rw [Finsupp.add_apply, hd0, add_zero]
    exact hbase x c
  rw [monomial_mul, levImg_monomial, monomialSubstitution_monomial, levN_monomial, compD_monomial, compD_monomial, inBlock_iff, e1, e2,
    e3]
  by_cases h1 : InLow Fr p hk nL rho base
  · rw [if_pos h1]
    by_cases h2 : ∀ x, multideg (plMon Fr p hk nL (base + d)) x = dPl x
    · by_cases h3 : ∀ x, multideg (noMon Fr p hk nL b) x = dNo x
      · rw [if_pos ⟨h1, h2, h3⟩, if_pos h2, if_pos h3, tens_monomial, smul_monomial, smul_eq_mul]
      · rw [if_neg (fun h => h3 h.2.2), if_neg h3, tens_zero_right]
    · rw [if_neg (fun h => h2 h.2.1), if_neg h2, tens_zero_left]
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]

theorem lev_mul (hp : 0 < p) (base : TV n' (m + 1) →₀ ℕ) (P Q : MvPolynomial (TV n' (m + 1)) (KK O))
    (hP : ∀ a ∈ P.support, ∃ d, LowDiv Fr p hk nL d ∧ (∀ x c, d (noVar Fr hk nL x c) = 0) ∧ a = base + d)
    (hQ : ∀ b ∈ Q.support, LowDiv Fr p hk nL b ∧ ∀ x a, b (plVar Fr hk nL x a) = 0)
    (hbase : ∀ x c, base (noVar Fr hk nL x c) < lowP Fr p x)
    (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) :
    levImg Fr p hk nL rho dPl dNo (P * Q) =
      if InLow Fr p hk nL rho base then
        tens (compD dPl (levP Fr p hk nL P)) (compD dNo (levN Fr p hk nL Q))
      else 0 := by
  have hL : levImg Fr p hk nL rho dPl dNo (P * Q) = ∑ a ∈ P.support, ∑ b ∈ Q.support,
      levImg Fr p hk nL rho dPl dNo (monomial a (P.coeff a) * monomial b (Q.coeff b)) := by
    rw [add_expand (fun X => levImg Fr p hk nL rho dPl dNo (X * Q)) (by simp [levImg_zero])
      (fun x y => by simp only [add_mul, levImg_add]) P]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact add_expand (fun Y => levImg Fr p hk nL rho dPl dNo (monomial a (P.coeff a) * Y)) (by simp [levImg_zero])
      (fun x y => by simp only [mul_add, levImg_add]) Q
  have hR : tens (compD dPl (levP Fr p hk nL P)) (compD dNo (levN Fr p hk nL Q)) = ∑ a ∈ P.support, ∑ b ∈ Q.support,
      tens (compD dPl (levP Fr p hk nL (monomial a (P.coeff a))))
        (compD dNo (levN Fr p hk nL (monomial b (Q.coeff b)))) := by
    rw [add_expand (fun X => tens (compD dPl (levP Fr p hk nL X)) (compD dNo (levN Fr p hk nL Q)))
      (by simp only [monomialSubstitution_zero, compD_zero, tens_zero_left])
      (fun x y => by simp only [monomialSubstitution_add, compD_add, tens_add_left]) P]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact add_expand (fun Y => tens (compD dPl (levP Fr p hk nL (monomial a (P.coeff a))))
      (compD dNo (levN Fr p hk nL Y))) (by simp only [levN_zero, compD_zero, tens_zero_right])
      (fun x y => by simp only [levN_add, compD_add, tens_add_right]) Q
  have hterm : ∀ a ∈ P.support, ∀ b ∈ Q.support,
      levImg Fr p hk nL rho dPl dNo (monomial a (P.coeff a) * monomial b (Q.coeff b)) =
        if InLow Fr p hk nL rho base then
          tens (compD dPl (levP Fr p hk nL (monomial a (P.coeff a))))
            (compD dNo (levN Fr p hk nL (monomial b (Q.coeff b))))
        else 0 := by
    intro a ha b hb
    obtain ⟨d, hd, hd0, rfl⟩ := hP a ha
    exact lev_term Fr p hk nL hp base d b hd hd0 (hQ b hb).1 (hQ b hb).2 hbase rho dPl dNo _ _
  rw [hL]
  split_ifs with h
  · rw [hR]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    rw [hterm a ha b hb, if_pos h]
  · refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
    rw [hterm a ha b hb, if_neg h]

end Lev

end Formalism.MainNotions.PairMembershipBlocks.T5
