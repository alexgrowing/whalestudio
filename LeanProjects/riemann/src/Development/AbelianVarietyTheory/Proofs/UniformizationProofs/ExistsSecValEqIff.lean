import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.FiniteCover

variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']

abbrev toField {U : X.Opens} (h : genericPoint X ∈ U) : Γ(X, U) →+* X.functionField :=
  (X.presheaf.germ U (genericPoint X) h).hom

theorem generic_mem {U : X.Opens} {x : X} (h : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, h⟩

theorem generic_inf {U V : X.Opens} (hU : genericPoint X ∈ U) (hV : genericPoint X ∈ V) :
    genericPoint X ∈ U ⊓ V := ⟨hU, hV⟩

theorem generic_top : genericPoint X ∈ (⊤ : X.Opens) := trivial

theorem toField_rs {U V : X.Opens} (h : V ≤ U) (hV : genericPoint X ∈ V) (a : Γ(X, U)) :
    toField hV (rs X h a) = toField (h hV) a :=
  X.presheaf.germ_res_apply (homOfLE h) _ hV a

theorem toField_injective {U : X.Opens} (h : genericPoint X ∈ U) :
    Function.Injective (toField h) := germ_injective_of_isIntegral X _ h

theorem exists_toField_eq {D : X.Opens} (hD : genericPoint X ∈ D) {I : Type} (O : I → X.Opens)
    (hO : ∀ a, O a ≤ D) (hc : D ≤ ⨆ a, O a) (hη : ∀ a, genericPoint X ∈ O a) (x : X.functionField)
    (hx : ∀ a, ∃ y, toField (hη a) y = x) : ∃ y, toField hD y = x := by
  choose y hy using hx
  obtain ⟨z, hz, -⟩ := X.sheaf.existsUnique_gluing' O D (fun a => homOfLE (hO a)) hc y
    fun a b => toField_injective (U := O a ⊓ O b) (generic_inf (hη a) (hη b))
      (((toField_rs inf_le_left _ _).trans (hy a)).trans ((toField_rs inf_le_right _ _).trans (hy b)).symm)
  obtain ⟨a, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc hD)
  exact ⟨z, (toField_rs (hO a) (hη a) z).symm.trans ((congrArg _ (hz a)).trans (hy a))⟩

theorem toField_appLE (φ : X' ⟶ X) [IsDominant φ] {U : X.Opens} {V : X'.Opens} (e : V ≤ φ ⁻¹ᵁ U)
    (hU : genericPoint X ∈ U) (hV : genericPoint X' ∈ V) (a : Γ(X, U)) :
    toField hV ((φ.appLE U V e).hom a) = functionFieldMap φ (toField hU a) := by
  have h₁ : toField hV ((φ.appLE U V e).hom a) = toField (e hV) ((φ.app U).hom a) :=
    toField_rs e hV _
  rw [h₁, functionFieldMap, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  exact (Scheme.Hom.germ_stalkMap_apply φ U (genericPoint X') (e hV) a).symm

variable {M : LB X} {k₀ : M.ι} (h₀ : genericPoint X ∈ M.U k₀)

def secVal {V : X.Opens} (hV : genericPoint X ∈ V) (σ : SecOn M V) : X.functionField :=
  toField (U := V ⊓ M.U k₀) (generic_inf (hV) (h₀)) (GlobalTheory.LB.coord σ k₀)

theorem toField_coord {V : X.Opens} (hV : genericPoint X ∈ V) (σ : SecOn M V) {k : M.ι}
    (hk : genericPoint X ∈ M.U k) :
    toField (U := V ⊓ M.U k) (generic_inf (hV) (hk)) (GlobalTheory.LB.coord σ k) =
      toField (U := M.U k ⊓ M.U k₀) (generic_inf (hk) (h₀)) (M.g k k₀).val * secVal h₀ hV σ := by
  have e := congrArg (toField (U := V ⊓ M.U k ⊓ M.U k₀) (generic_inf (generic_inf hV hk) h₀))
    (SecOn.compat σ k k₀ (O := V ⊓ M.U k ⊓ M.U k₀) inf_le_left (inf_le_inf_right _ inf_le_left)
      (inf_le_inf_right _ inf_le_right))
  rw [map_mul, toField_rs, toField_rs, toField_rs] at e
  exact e

theorem secVal_injective {V : X.Opens} (hV : genericPoint X ∈ V) :
    Function.Injective (secVal h₀ hV) := fun σ τ h => GlobalTheory.LB.sec_ext fun k => by
  by_cases hk : genericPoint X ∈ M.U k
  · refine toField_injective (U := V ⊓ M.U k) (generic_inf (hV) (hk)) ?_
    rw [toField_coord h₀ hV σ hk, toField_coord h₀ hV τ hk, h]
  · have : V ⊓ M.U k = ⊥ := eq_bot_iff.2 fun x hx => (hk (generic_mem hx.2)).elim
    have : Subsingleton Γ(X, V ⊓ M.U k) := this ▸ inferInstance
    exact Subsingleton.elim _ _

theorem secVal_restrict {V W : X.Opens} (h : W ≤ V) (hW : genericPoint X ∈ W) (σ : SecOn M V) :
    secVal h₀ hW (SecOn.restrict M h σ) = secVal h₀ (h hW) σ :=
  toField_rs (inf_le_inf_right _ h) _ _

theorem secVal_smul {V : X.Opens} (hV : genericPoint X ∈ V) (a : Γ(X, V)) (σ : SecOn M V) :
    secVal h₀ hV (a • σ) = toField hV a * secVal h₀ hV σ :=
  (map_mul (toField (U := V ⊓ M.U k₀) (generic_inf (hV) (h₀))) (rs X inf_le_left a) _).trans
    (congrArg (· * secVal h₀ hV σ) (toField_rs _ _ _))

theorem secVal_add {V : X.Opens} (hV : genericPoint X ∈ V) (σ τ : SecOn M V) :
    secVal h₀ hV (σ + τ) = secVal h₀ hV σ + secVal h₀ hV τ :=
  map_add (toField (U := V ⊓ M.U k₀) (generic_inf (hV) (h₀))) _ _

theorem exists_secVal_eq_iff (hM : M.IsLB) {I : Type} (D : I → X.Opens) (hc : ⊤ ≤ ⨆ i, D i)
    (hη : ∀ i, genericPoint X ∈ D i) (τ : ∀ i, SecOn M (D i))
    (hτ : ∀ i k, IsUnit (GlobalTheory.LB.coord (τ i) k)) (x : X.functionField) :
    (∃ σ : SecOn M ⊤, secVal h₀ generic_top σ = x) ↔
      ∀ i, ∃ a ∈ (toField (hη i)).range, x = a * secVal h₀ (hη i) (τ i) := by
  constructor
  · rintro ⟨σ, rfl⟩ i
    have hne : secVal h₀ (hη i) (τ i) ≠ 0 := ((hτ i k₀).map _).ne_zero
    refine ⟨secVal h₀ generic_top σ / secVal h₀ (hη i) (τ i), ?_, (div_mul_cancel₀ _ hne).symm⟩
    refine exists_toField_eq (hη i) (fun k : {k // genericPoint X ∈ M.U k} => D i ⊓ M.U k.1)
      (fun _ => inf_le_left) (fun y hy => ?_) (fun k => (generic_inf (hη i) (k.2))) _ fun k => ?_
    · obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (trivial : y ∈ ⊤))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨k, generic_mem hk⟩, hy, hk⟩
    · obtain ⟨u, hu⟩ := hτ i k.1
      refine ⟨GlobalTheory.LB.coord (SecOn.restrict M le_top σ) k.1 * u⁻¹.val, ?_⟩
      have e₁ := toField_coord h₀ (hη i) (τ i) k.2
      have e₂ := toField_coord h₀ (hη i) (SecOn.restrict M le_top σ) k.2
      have hg : toField (U := M.U k.1 ⊓ M.U k₀) (generic_inf (k.2) (h₀)) (M.g k.1 k₀).val ≠ 0 :=
        ((M.g k.1 k₀).isUnit.map _).ne_zero
      rw [map_mul, map_units_inv, hu, e₁, e₂, secVal_restrict]
      field_simp
  · intro h
    choose a ha hx using h
    choose b hb using ha
    have hv : ∀ i, secVal h₀ (hη i) (b i • τ i) = x := fun i => by
      rw [secVal_smul, hb, hx i]
    obtain ⟨σ, hσ, -⟩ := SecOn.existsUnique_glue D (fun _ => le_top) hc (fun i => b i • τ i)
      fun i j => secVal_injective h₀ (V := D i ⊓ D j) (generic_inf (hη i) (hη j)) (by
        rw [secVal_restrict, secVal_restrict, hv, hv])
    obtain ⟨i, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc generic_top)
    exact ⟨σ, by rw [← hv i, ← hσ i, secVal_restrict]⟩

def secValLin {K : Type} [Field K] (f : X ⟶ Spec (CommRingCat.of K)) [Algebra K X.functionField]
    (hK : ∀ r, algebraMap K X.functionField r = toField generic_top (cst f ⊤ r)) :
    SecOnR f M ⊤ →ₗ[K] X.functionField where
  toFun σ := secVal h₀ generic_top σ
  map_add' σ τ := secVal_add h₀ generic_top σ τ
  map_smul' r σ := (secVal_smul h₀ generic_top (cst f ⊤ r) σ).trans (by
    rw [RingHom.id_apply, Algebra.smul_def, hK])

theorem secVal_pull (φ : X' ⟶ X) [IsDominant φ] {V : X.Opens} (hV : genericPoint X ∈ V)
    (h₀' : genericPoint X' ∈ (M.pull φ).U fun _ => k₀) (hV' : genericPoint X' ∈ φ ⁻¹ᵁ V)
    (σ : SecOn M V) :
    secVal h₀' hV' (SecOn.pull M φ V σ) = functionFieldMap φ (secVal h₀ hV σ) :=
  toField_appLE φ _ _ _ _

end GlobalTheory.FiniteCover
