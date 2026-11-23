import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfResidueFieldFibres
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh.Wedge

def alt2 {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] M →ₗ[R] N) (hf : ∀ x, f x x = 0) : M [⋀^Fin 2]→ₗ[R] N where
  toFun v := f (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp
  map_update_smul' v i c x := by
    fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j <;> simp_all

theorem alt2_apply {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] M →ₗ[R] N) (hf : ∀ x, f x x = 0) (v : Fin 2 → M) : alt2 f hf v = f (v 0) (v 1) := rfl

theorem bijective_of_fibres {R B C : Type} [CommRing R] [AddCommGroup B] [Module R B] [AddCommGroup C]
    [Module R C] [Module.Finite R B] [Module.Finite R C] [Module.Projective R C] (l : B →ₗ[R] C)
    (h : ∀ q : PrimeSpectrum R, Function.Bijective (l.baseChange q.asIdeal.ResidueField)) :
    Function.Bijective l := by
  have hlt : ∀ q : PrimeSpectrum R, Function.Bijective (l.lTensor q.asIdeal.ResidueField) := by
    intro q
    have e : ⇑(l.lTensor q.asIdeal.ResidueField) = ⇑(l.baseChange q.asIdeal.ResidueField) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    rw [e]; exact h q
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := GlobalTheory.split_injective_of_forall_lTensor_residueField_injective l
      (fun m hm => (hlt ⟨m, hm.isPrime⟩).1)
    exact Function.LeftInverse.injective (g := r) fun x => LinearMap.congr_fun hr x
  · have hQ : Subsingleton (C ⧸ LinearMap.range l) := by
      apply GlobalTheory.subsingleton_of_residueField_fibres R
      intro q
      have h2 := (hlt q).2
      have h3 : Function.Surjective ((LinearMap.range l).mkQ.lTensor q.asIdeal.ResidueField) :=
        LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
      refine ⟨fun a b => ?_⟩
      have key : ∀ a : q.asIdeal.ResidueField ⊗[R] (C ⧸ LinearMap.range l), a = 0 := by
        intro a
        obtain ⟨x, rfl⟩ := h3 a
        obtain ⟨y, rfl⟩ := h2 x
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, LinearMap.range_mkQ_comp]
        simp
      rw [key a, key b]
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    exact hQ

end GlobalTheory.AbCoh.Wedge

namespace GlobalTheory.AbCoh.Wedge

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)

def wedgeMap (hsq : ∀ x : HO1 s, cup _ x x = 0) : ⋀[R]^2 (HO1 s) →ₗ[R] HO2 s :=
  exteriorPower.alternatingMapLinearEquiv (alt2 (cup _) hsq)

theorem wedgeMap_ιMulti (hsq : ∀ x : HO1 s, cup _ x x = 0) (v : Fin 2 → HO1 s) :
    wedgeMap s hsq (exteriorPower.ιMulti R 2 v) = cup _ (v 0) (v 1) := by
  simp only [wedgeMap, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, alt2_apply]

theorem baseChange_wedgeMap_bijective (hsq : ∀ x : HO1 s, cup _ x x = 0) (k : Type) [CommRing k]
    [Algebra R k] (X' : Scheme.{0}) (s' : X' ⟶ Sp k) (φ : X' ⟶ X)
    (hpb : φ ≫ s = s' ≫ spMap (algebraMap R k))
    (e1 : k ⊗[R] HO1 s ≃ₗ[k] HO1 s') (he1 : ∀ c, e1 (1 ⊗ₜ c) = pullHO1 hpb c)
    (e2 : k ⊗[R] HO2 s ≃ₗ[k] HO2 s') (he2 : ∀ c, e2 (1 ⊗ₜ c) = pullHO2 hpb c)
    (w : ⋀[k]^2 (CatCoh.H1 (OAff s')) ≃ₗ[k] CatCoh.H2 (OAff s'))
    (hw : ∀ a b, w (exteriorPower.ιMulti k 2 ![a, b]) = cup _ a b) :
    Function.Bijective ((wedgeMap s hsq).baseChange k) := by
  have hcup := ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.1 R k X X' s s' (algebraMap R k) φ hpb).1
  let β := (GlobalTheory.TopForm.isBaseChange_exteriorPower (TensorProduct.isBaseChange R (HO1 s) k) 2).equiv
  let T : k ⊗[R] ⋀[R]^2 (HO1 s) →ₗ[k] k ⊗[R] HO2 s :=
    e2.symm.toLinearMap ∘ₗ w.toLinearMap ∘ₗ exteriorPower.map 2 e1.toLinearMap ∘ₗ β.toLinearMap
  have hT : T = (wedgeMap s hsq).baseChange k := by
    refine TensorProduct.AlgebraTensorModule.ext fun c x => ?_
    rw [← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul]
    congr 1
    have hl : (T.restrictScalars R) ∘ₗ TensorProduct.mk R k _ 1 =
        (((wedgeMap s hsq).baseChange k).restrictScalars R) ∘ₗ TensorProduct.mk R k _ 1 := by
      apply exteriorPower.linearMap_ext
      ext v
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        LinearMap.restrictScalars_apply, TensorProduct.mk_apply, LinearMap.baseChange_tmul,
        wedgeMap_ιMulti, T, LinearEquiv.coe_coe, β, IsBaseChange.equiv_tmul, one_smul,
        GlobalTheory.exteriorPowerMapOver_ιMulti, exteriorPower.map_apply_ιMulti]
      have hv : (⇑e1 ∘ fun i => (1 : k) ⊗ₜ[R] v i) = ![pullHO1 hpb (v 0), pullHO1 hpb (v 1)] := by
        funext i; fin_cases i <;> simp [he1]
      rw [hv, hw, LinearEquiv.symm_apply_eq, he2, hcup]
    exact LinearMap.congr_fun hl x
  rw [← hT]
  have hm : Function.Bijective (exteriorPower.map 2 e1.toLinearMap) := by
    refine Function.bijective_iff_has_inverse.2 ⟨exteriorPower.map 2 e1.symm.toLinearMap, ?_, ?_⟩
    · intro x
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
      simp [exteriorPower.map_id]
    · intro x
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
      simp [exteriorPower.map_id]
  exact e2.symm.bijective.comp (w.bijective.comp (hm.comp β.bijective))

end GlobalTheory.AbCoh.Wedge

namespace GlobalTheory.AbCoh.Wedge

theorem wedgeO_of_fibres : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Module.Finite R (HO1 s) → Module.Projective R (HO1 s) → Module.Finite R (HO2 s) → Module.Projective R (HO2 s) → StructureSheafH1BaseChange s → StructureSheafH2BaseChange s → (∀ x : HO1 s, cup _ x x = 0) → (∀ (k : Type) [Field k] [Algebra R k] (X' : Scheme.{0}) (s' : X' ⟶ Sp k) (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R k))), WedgeO (OAff s')) → WedgeO (OAff s) := by
  intro R _ X s hF1 hP1 hF2 hP2 hB1 hB2 hsq hfib
  have hbij : Function.Bijective (wedgeMap s hsq) := by
    refine bijective_of_fibres _ fun q => ?_
    obtain ⟨X', s', φ, hpb⟩ : ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp q.asIdeal.ResidueField) (φ : X' ⟶ X),
        IsPullback φ s' s (spMap (algebraMap R q.asIdeal.ResidueField)) :=
      ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
    obtain ⟨e1, he1⟩ := hB1 _ _ _ _ hpb
    obtain ⟨e2, he2⟩ := hB2 _ _ _ _ hpb
    obtain ⟨w, hw⟩ := hfib _ _ _ _ hpb
    exact baseChange_wedgeMap_bijective s hsq _ X' s' φ hpb.w e1 he1 e2 he2 w hw
  exact ⟨LinearEquiv.ofBijective _ hbij, fun a b => by
    rw [LinearEquiv.ofBijective_apply, wedgeMap_ιMulti]; rfl⟩

end GlobalTheory.AbCoh.Wedge
