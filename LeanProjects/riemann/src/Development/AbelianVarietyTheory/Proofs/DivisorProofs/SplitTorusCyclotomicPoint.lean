import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointExtensionSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase.PresAll

theorem norm_natCast_of_coprime (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : Nat.Coprime m p) : ‖(m : ℂ_[p])‖ = 1 := by
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one _ m) ?_
  have hpn : ‖(p : ℂ_[p])‖ < 1 := by
    rw [PadicComplexHost.norm_p p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have h1 : ((m : ℤ) * Nat.gcdA m p + (p : ℤ) * Nat.gcdB m p : ℤ) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hm]; rfl
  have h2 : (m : ℂ_[p]) * (Nat.gcdA m p : ℂ_[p]) + (p : ℂ_[p]) * (Nat.gcdB m p : ℂ_[p]) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℂ_[p]) h1
  have ha := IsUltrametricDist.norm_intCast_le_one ℂ_[p] (Nat.gcdA m p)
  have hb := IsUltrametricDist.norm_intCast_le_one ℂ_[p] (Nat.gcdB m p)
  have h3 : (1 : ℝ) ≤ max ‖(m : ℂ_[p]) * (Nat.gcdA m p : ℂ_[p])‖ ‖(p : ℂ_[p]) * (Nat.gcdB m p : ℂ_[p])‖ := by
    have := IsUltrametricDist.norm_add_le_max ((m : ℂ_[p]) * (Nat.gcdA m p : ℂ_[p])) ((p : ℂ_[p]) * (Nat.gcdB m p : ℂ_[p]))
    rwa [h2, norm_one] at this
  have h4 : ‖(p : ℂ_[p]) * (Nat.gcdB m p : ℂ_[p])‖ < 1 := by
    rw [norm_mul]
    calc ‖(p : ℂ_[p])‖ * ‖(Nat.gcdB m p : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ * 1 := by gcongr
      _ < 1 := by rwa [_root_.mul_one]
  have h5 : 1 ≤ ‖(m : ℂ_[p]) * (Nat.gcdA m p : ℂ_[p])‖ := by
    rcases le_max_iff.1 h3 with h | h
    · exact h
    · exact absurd h (not_le.2 h4)
  rw [norm_mul] at h5
  nlinarith [norm_nonneg (m : ℂ_[p]), norm_nonneg (Nat.gcdA m p : ℂ_[p])]

theorem norm_sum_mul_le_one {C : Type} [NormedField C] [IsUltrametricDist C] {g : ℕ} (a b : Fin g → C)
    (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1) : ‖∑ i, a i * b i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ ↦ by
    rw [norm_mul]; exact mul_le_one₀ (ha i) (norm_nonneg _) (hb i)

theorem coprime_div (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (p : ℕ) (hp : p ∈ S) :
    Nat.Coprime ((∏ q ∈ S, q) / p) p := by
  have hpos : 0 < p := (hS p hp).pos
  rw [← Finset.mul_prod_erase S (fun q ↦ q) hp, Nat.mul_div_cancel_left _ hpos]
  refine Nat.Coprime.prod_left fun q hq ↦ ?_
  exact (Nat.coprime_primes (hS q (Finset.mem_of_mem_erase hq)) (hS p hp)).2 (Finset.ne_of_mem_erase hq)

theorem coprime_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (p : ℕ) (hp : p.Prime) (hpS : p ∉ S) :
    Nat.Coprime (∏ q ∈ S, q) p :=
  Nat.Coprime.prod_left fun q hq ↦ (Nat.coprime_primes (hS q hq) hp).2 fun h ↦ hpS (h ▸ hq)

theorem dvd_div (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (p q : ℕ) (hp : p ∈ S) (hq : q ∈ S) (hne : q ≠ p) :
    p ∣ (∏ r ∈ S, r) / q := by
  rw [← Finset.mul_prod_erase S (fun r ↦ r) hq, Nat.mul_div_cancel_left _ (hS q hq).pos]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hne.symm, hp⟩)

theorem sum_natCast_smul {R C : Type} [CommRing R] [NontriviallyNormedField C] [IsUltrametricDist C] {g : ℕ}
    (φ : R →+* ↥(intO C)) (n : ℕ) (h : Fin g → R) (cf : Fin g → C) :
    ∑ i, ((φ (((n : R) • h) i) : ↥(intO C)) : C) * cf i = (n : C) * ∑ i, ((φ (h i) : ↥(intO C)) : C) * cf i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [_root_.mul_assoc]

end GlobalTheory.ArLieBase.PresAll

namespace GlobalTheory.ArLieBase.PresAll

theorem spMap_epsMul_one (A : Type) [CommRing A] : spMap (epsMul (1 : A)) = 𝟙 _ := by
  have : epsMul (1 : A) = RingHom.id _ := by
    refine RingHom.ext fun z ↦ TrivSqZeroExt.ext ?_ ?_ <;> simp [epsMul]
  rw [this]; exact Spec.map_id _

end GlobalTheory.ArLieBase.PresAll

namespace GlobalTheory.ArLieBase

open GlobalTheory.ArLieBase.PresAll in

theorem latPres_of_splitK : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T : Scheme.{0}) [IsLocallyNoetherian T] (t : SAB H T), T.IsSeparated → ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (x : Sp R ⟶ T), (∃ ζ : K, IsPrimitiveRoot ζ (∏ p ∈ S, p)) → GlobalTheory.HtGen.SplitK t (spMap (algebraMap R K) ≫ x) (∏ p ∈ S, p) → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)), GlobalTheory.LineNorm.IsTanBasis t x e → ∃ (M : ℕ) (h : Fin M → Fin g → R), LatPres t x (ArIn.ind S) (fun _ ↦ 0) e h := by
  intro E _ _ _ H T _ t hT S hS R K _ _ _ _ _ _ _ x ⟨ζ, hζ⟩ hK g e he
  haveI : CharZero R := ⟨fun a b hab ↦ Nat.cast_injective (R := K) (by simpa using congrArg (algebraMap R K) hab)⟩
  have hNpos : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp ↦ (hS p hp).pos
  have hdvd : ∀ p ∈ S, p ∣ ∏ q ∈ S, q := fun p hp ↦ Finset.dvd_prod_of_mem (fun q ↦ q) hp
  have hroot : ∀ p ∈ S, ∃ z : R, IsPrimitiveRoot z p := by
    intro p hp
    obtain ⟨k, hk⟩ := hdvd p hp
    have h1 : IsPrimitiveRoot (ζ ^ k) p := hζ.pow hNpos (by rw [hk, mul_comm])
    have hint : IsIntegral R (ζ ^ k) := ⟨Polynomial.X ^ p - Polynomial.C 1,
      Polynomial.monic_X_pow_sub_C 1 (hS p hp).ne_zero, by simp [h1.pow_eq_one]⟩
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    exact ⟨z, IsPrimitiveRoot.of_map_of_injective (f := algebraMap R K) (hz ▸ h1) (IsFractionRing.injective R K)⟩
  have hsplit : ∀ p ∈ S, GlobalTheory.LineNorm.SplitTors t x p := fun p hp ↦
    GlobalTheory.HtChar.splitTors_of_splitK (K := K) x p fun Ω _ io w hw ↦ hK Ω io w (by
      obtain ⟨k, hk⟩ := hdvd p hp
      rw [hk, pow_mul, hw, one_pow])
  choose nf hf hhf using fun p : S ↦
    GlobalTheory.HTMap.hodgeTate_map E H T t R x g e he p.1 (hS _ p.2) (hroot _ p.2) (hsplit _ p.2)
  let Ix := (Σ p : S, Fin (nf p)) ⊕ Fin g
  let hι : Ix → Fin g → R := Sum.elim (fun q ↦ (((∏ r ∈ S, r) / q.1.1 : ℕ) : R) • hf q.1 q.2)
    (fun i ↦ Pi.single i ((∏ r ∈ S, r : ℕ) : R))
  let eqv := Fintype.equivFin Ix
  refine ⟨Fintype.card Ix, fun k ↦ hι (eqv.symm k), ⟨∏ r ∈ S, r, hNpos.ne', fun i ↦ Submodule.subset_span
    ⟨eqv (Sum.inr i), by simp [hι]⟩⟩, ?_⟩
  intro p _ φ
  refine ⟨1, by simp, fun cf w hw ↦ ?_⟩
  rw [spMap_epsMul_one, Category.id_comp]
  suffices key : w ∈ lat t p (spMap ((intO ℂ_[p]).subtype.comp φ) ≫ x) (ArIn.ind S p) ↔
      ∀ a : Ix, ‖∑ i, ((φ (hι a i) : ↥(intO ℂ_[p])) : ℂ_[p]) * cf i‖ ≤ 1 by
    rw [key]; exact ⟨fun h j ↦ h _, fun h a ↦ by simpa using h (eqv a)⟩
  have hnorm1 : ∀ z : ↥(intO ℂ_[p]), ‖(z : ℂ_[p])‖ ≤ 1 := fun z ↦ z.2
  have hin : ∀ (q : S) (j : Fin (nf q)), ‖∑ i, ((φ (hι (Sum.inl ⟨q, j⟩) i) : ↥(intO ℂ_[p])) : ℂ_[p]) * cf i‖ =
      ‖(((∏ r ∈ S, r) / q.1 : ℕ) : ℂ_[p])‖ * ‖∑ i, ((φ (hf q j i) : ↥(intO ℂ_[p])) : ℂ_[p]) * cf i‖ := by
    intro q j
    rw [← norm_mul, ← sum_natCast_smul]
    rfl
  have hir : ∀ i, ‖∑ k, ((φ (hι (Sum.inr i) k) : ↥(intO ℂ_[p])) : ℂ_[p]) * cf k‖ =
      ‖((∏ r ∈ S, r : ℕ) : ℂ_[p])‖ * ‖cf i‖ := by
    intro i
    simp only [hι, Sum.elim_inr]
    rw [GlobalTheory.HTPres.sum_single, map_natCast, norm_mul]
    simp
  have hxC : spMap (intO ℂ_[p]).subtype ≫ spMap φ ≫ x = spMap ((intO ℂ_[p]).subtype.comp φ) ≫ x := by
    rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  rw [Sum.forall, Sigma.forall]
  simp only [hin, hir]
  by_cases hpS : p ∈ S
  · have hlat : ArIn.ind S p = true := by simp [ArIn.ind, hpS]
    have hw' : IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ spMap φ ≫ x)
        (fun i ↦ spMap (dualMap (intO ℂ_[p]).subtype) ≫ spMap (dualMap φ) ≫ e i) cf w := by
      rw [hxC]; simpa only [GlobalTheory.HTPres.bc_bc] using hw
    rw [hlat]
    change w ∈ latHT t p _ ↔ _
    rw [← hxC, GlobalTheory.HTLevel.mem_latHT_iff GlobalTheory.ShFam.Pad.HTBound.htBound E H T t p ℂ_[p] (PadicComplexHost.norm_p p)
      (spMap φ ≫ x) (fun x' hx' ↦ GlobalTheory.HTPres.ext_uniq hT _ _ _ hx') g _ (GlobalTheory.HTPres.isTanBasis_map t he φ)
      (nf ⟨p, hpS⟩) (fun j i ↦ φ (hf ⟨p, hpS⟩ j i)) (hhf ⟨p, hpS⟩ ℂ_[p] φ).1 (hhf ⟨p, hpS⟩ ℂ_[p] φ).2 cf w hw']
    have hNq : ‖(((∏ r ∈ S, r) / p : ℕ) : ℂ_[p])‖ = 1 := norm_natCast_of_coprime p _ (coprime_div S hS p hpS)
    have hNp : ‖((∏ r ∈ S, r : ℕ) : ℂ_[p])‖ = ‖(p : ℂ_[p])‖ := by
      rw [← Nat.mul_div_cancel' (hdvd p hpS), Nat.cast_mul, norm_mul, hNq, _root_.mul_one]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun q j ↦ ?_, fun i ↦ ?_⟩
      · obtain ⟨q, hqS⟩ := q
        by_cases hq : q = p
        · subst hq
          rw [hNq, _root_.one_mul]
          exact h1 j
        · obtain ⟨m, hm⟩ := dvd_div S hS p q hpS hqS hq
          have hA : ‖(p : ℂ_[p])‖ * ‖∑ i, ((φ (hf ⟨q, hqS⟩ j i) : ↥(intO ℂ_[p])) : ℂ_[p]) * cf i‖ ≤ 1 := by
            rw [← norm_mul, Finset.mul_sum]
            simp_rw [mul_left_comm (p : ℂ_[p])]
            exact norm_sum_mul_le_one _ (fun i ↦ (p : ℂ_[p]) * cf i) (fun i ↦ hnorm1 _) h2
          simp only at hm ⊢
          rw [hm, Nat.cast_mul, norm_mul]
          calc ‖(p : ℂ_[p])‖ * ‖(m : ℂ_[p])‖ * ‖∑ i, ((φ (hf ⟨q, hqS⟩ j i) : ↥(intO ℂ_[p])) : ℂ_[p]) * cf i‖ =
              ‖(m : ℂ_[p])‖ * (‖(p : ℂ_[p])‖ * ‖∑ i, ((φ (hf ⟨q, hqS⟩ j i) : ↥(intO ℂ_[p])) : ℂ_[p]) * cf i‖) := by ring
            _ ≤ 1 := mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one _ _) (by positivity) hA
      · rw [hNp, ← norm_mul]
        exact h2 i
    · rintro ⟨h1, h2⟩
      refine ⟨fun j ↦ ?_, fun i ↦ ?_⟩
      · have := h1 ⟨p, hpS⟩ j
        rwa [hNq, _root_.one_mul] at this
      · have := h2 i
        rwa [hNp, ← norm_mul] at this
  · have hlat : ArIn.ind S p = false := by simp [ArIn.ind, hpS]
    rw [hlat]
    change w ∈ latDR t _ ↔ _
    rw [← hxC, GlobalTheory.HTPres.mem_latDR_iff t hT x he ℂ_[p] φ cf w (by rw [hxC]; exact hw)]
    have hN1 : ‖((∏ r ∈ S, r : ℕ) : ℂ_[p])‖ = 1 :=
      norm_natCast_of_coprime p _ (coprime_prod S hS p Fact.out hpS)
    simp only [hN1, _root_.one_mul]
    constructor
    · intro h
      exact ⟨fun q j ↦ mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one _ _) (norm_nonneg _)
        (norm_sum_mul_le_one _ _ (fun i ↦ hnorm1 _) h), h⟩
    · exact fun h ↦ h.2

end GlobalTheory.ArLieBase
