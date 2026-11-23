import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtalePolynomialPlaceToPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenWedgeFormOfFormallyEtaleMvPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerWedgeFormMapEqSmulOfBasisStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FieldPair

theorem formOrd_append_of_ord_eq : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (P : Place cL) (P0 : Place cK),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → P.IsPrimeOf T → P0.IsPrimeOf R →
  (∀ g : R, g ≠ 0 → P.ord (ι g : L) = P0.ord (g : K)) →
  P.formOrd (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) = P0.formOrd (dForm cK (fun i => (x i : K))) := by
  intro K L _ _ cK cL n r R T ι ψ τ x P P0 hE hx hP hP0 hord
  have hιinj : Function.Injective ι := fun a b h => by
    have := congrArg ψ h
    rwa [hE.retr, hE.retr] at this
  haveI : IsFractionRing R K := IsFractionRing.of_field R K fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hE.base.frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, eq_div_of_mul_eq hb0 e⟩
  have hginj : Function.Injective (T.subtype.comp ι) := Subtype.val_injective.comp hιinj
  let j : K →+* L := IsFractionRing.lift hginj
  have hj : ∀ g : R, j (g : K) = (ι g : L) := fun g => IsFractionRing.lift_algebraMap hginj g
  have hordK : ∀ f : K, f ≠ 0 → P.ord (j f) = P0.ord f := by
    intro f hf
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hE.base.frac f
    have ha0 : a ≠ 0 := by rw [← e]; exact mul_ne_zero hf hb0
    have ef : f = a * b⁻¹ := by rw [← e, mul_inv_cancel_right₀ hb0]
    have hjb : j b ≠ 0 := (map_ne_zero j).2 hb0
    have hja : j a ≠ 0 := (map_ne_zero j).2 ha0
    have hga : (⟨a, ha⟩ : R) ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
    have hgb : (⟨b, hb⟩ : R) ≠ 0 := fun h => hb0 (congrArg Subtype.val h)
    have h1 := hord _ hga
    have h2 := hord _ hgb
    rw [← hj] at h1 h2
    rw [ef, map_mul, map_inv₀, P.ord_mul hja (inv_ne_zero hjb), P.ord_inv,
      P0.ord_mul ha0 (inv_ne_zero hb0), P0.ord_inv]
    simp only at h1 h2
    rw [h1, h2]
  have hA : ∀ f ∈ P0.ring, j f ∈ P.ring := by
    intro f hf
    by_cases h0 : f = 0
    · rw [h0, map_zero]; exact P.ring.zero_mem
    · have hj0 : j f ≠ 0 := (map_ne_zero j).2 h0
      rw [← P.ord_nonneg_iff hj0, hordK f h0, P0.ord_nonneg_iff h0]
      exact hf
  have hτ : ∀ i, (τ i : L) ∈ P.ring := fun i => hP.1 _ (τ i).2
  let ρ : P0.ring →+* P.ring := j.restrict P0.ring P.ring hA
  let τ' : Fin r → P.ring := fun i => ⟨τ i, hτ i⟩
  have hc : ρ.comp P0.const = P.const := by
    ext a
    change j (cK a) = cL a
    have := hj ⟨cK a, hE.base.const_mem a⟩
    rw [hE.const a] at this
    exact this
  have hFE := GlobalTheory.T.formallyEtale_polynomialPlace_to_place cK cL r R T ι ψ τ P P0 j hE hP hP0 hj hA hτ

  letI := P0.const.toAlgebra
  letI := cK.toAlgebra
  haveI : IsScalarTower ℂ P0.ring K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType ℂ P0.ring := P0.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ P0.ring
  obtain ⟨t0, ht0⟩ := IsDiscreteValuationRing.exists_irreducible P0.ring
  obtain ⟨m, z, b, -, hb⟩ := exists_basis_kaehler_uniformiser ℂ ht0
  have h1 := trdeg_eq_of_basis_kaehler ℂ K b
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
  rw [h1, Cardinal.mk_fin] at h2
  obtain rfl : n = m + 1 := by exact_mod_cast h2
  have hω0 : IsFreeGen P0.ring (dForm P0.const z) := isFreeGen_dForm z b hb
  have hF : IsFreeGen P.ring (dForm P.const (Fin.append τ' (fun i => ρ (z i)))) :=
    GlobalTheory.T.isFreeGen_wedgeForm_of_formallyEtale_mvPolynomial P0.const P.const ρ hc z b hb τ' hFE
  haveI : Algebra.FormallyEtale P0.ring K := .of_isLocalization (nonZeroDivisors P0.ring)
  let bK : Module.Basis (Fin (m + 1)) K (Omega cK) :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ P0.ring K).basis b
  have hbK : ∀ i, bK i = dFun cK (z i : K) := by
    intro i
    simp only [bK, IsBaseChange.basis_apply, hb]
    exact KaehlerDifferential.map_D ℂ ℂ P0.ring K (z i)
  have hrat0 : P0.toRat (m + 1) (dForm P0.const z) = dForm cK (fun i => (z i : K)) :=
    formMap_dForm _ rfl z
  have hratP : P.toRat (r + (m + 1)) (dForm P.const (Fin.append τ' (fun i => ρ (z i)))) =
      dForm cL (Fin.append (fun i => (τ i : L)) (fun i => j (z i : K))) := by
    refine (formMap_dForm _ rfl _).trans (congrArg _ (funext fun k => ?_))
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp only [Fin.append_left]; rfl
    · simp only [Fin.append_right]; rfl
  obtain ⟨f, hf⟩ := (P0.isFreeGen_toRat hω0).2 (dForm cK (fun i => (x i : K)))
  simp only at hf
  have hxK := isFreeGen_dForm_of_trBasis cK hx
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hf
    exact one_ne_zero (hxK.1 (a₁ := 1) (a₂ := 0) (by simp [← hf]))
  have hK : P0.formOrd (dForm cK (fun i => (x i : K))) = P0.ord f := by
    rw [← hf]; exact P0.formOrd_smul_toRat hω0 hf0
  have key := GlobalTheory.T.kaehlerWedgeForm_map_eq_smul_of_basis cK cL j (RingHom.ext fun a => by
      change j (cK a) = cL a
      have := hj ⟨cK a, hE.base.const_mem a⟩
      rw [hE.const a] at this
      exact this) (fun i => (x i : K)) (fun i => (z i : K)) bK hbK f
    (by rw [← hf, hrat0]) (fun i => (τ i : L))
  have e1 : (fun i => j (x i : K)) = fun i => (ι (x i) : L) := funext fun i => hj (x i)
  rw [e1, ← hratP] at key
  rw [key, P.formOrd_smul_toRat hF ((map_ne_zero j).2 hf0), hordK f hf0, hK]

end GlobalTheory.FieldPair
