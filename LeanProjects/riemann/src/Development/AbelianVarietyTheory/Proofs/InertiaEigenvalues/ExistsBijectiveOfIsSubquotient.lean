import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleTensorOfJacquetSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open GlobalTheory.PRep GlobalTheory.SmGL

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.JacFactor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isIrreducible_comp_surj {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (f : G →* H) (hf : Function.Surjective f) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp f : Representation ℂ G V) := by
  let e : Subrepresentation (ρ.comp f : Representation ℂ G V) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        obtain ⟨x, rfl⟩ := hf g
        exact S.apply_mem_toSubmodule x hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  exact e.isSimpleOrder

theorem isSubquotient_comp' {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : IsSubquotient σ ρ) (ψ : G' →* G) : IsSubquotient (σ.comp ψ) (ρ.comp ψ) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (ψ g) hv⟩,
    ⟨f.toLinearMap, fun g => f.isIntertwining' (ψ g)⟩, hf⟩

def piTensorBoolEquiv {R a b : Type} [CommRing R] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {X : Bool → Type} [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]
    (F : ∀ j, Representation ℂ (GL (Two a b j) R) (X j)) :
    Representation.Equiv ((piTensor F).comp (leviTwo R a b).toMonoidHom :
      Representation ℂ (GL a R × GL b R) (⨂[ℂ] j, X j)) (extTensor (F false) (F true)) :=
  .mk (Exponents.boolTensorEquiv (X := X)) fun g => by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    show Exponents.boolTensorEquiv (X := X) (piTensor F (leviTwo R a b g) (PiTensorProduct.tprod ℂ x)) =
      extTensor (F false) (F true) g (Exponents.boolTensorEquiv (X := X) (PiTensorProduct.tprod ℂ x))
    rw [piTensor_tprod, Exponents.boolTensorEquiv_tprod, Exponents.boolTensorEquiv_tprod, extTensor_tmul]
    rfl

theorem exists_extTensor_of_isSubquotient_jac₂ (hGL : GlobalTheory.Published.GeometricLemma) {n : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hπ : IsSmooth π)
    (hirr : π.IsIrreducible) {a b : ℕ} (h : a + b = n) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (GL (Fin a) k × GL (Fin b) k) Y) (hτ : τ.IsIrreducible)
    (hs : IsSubquotient τ (jac₂ (stdSum h) π)) :
    ∃ (W W' : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : AddCommGroup W') (_ : Module ℂ W')
      (σ : Representation ℂ (GL (Fin a) k) W) (ρ : Representation ℂ (GL (Fin b) k) W'),
      IsSmooth σ ∧ σ.IsIrreducible ∧ IsSmooth ρ ∧ ρ.IsIrreducible ∧ IsSubquotient τ (extTensor σ ρ) := by
  let L := leviTwo k (Fin a) (Fin b)
  let τ' : Representation ℂ (Levi k (Two (Fin a) (Fin b))) Y := τ.comp L.symm.toMonoidHom
  have hτ' : τ'.IsIrreducible := isIrreducible_comp_surj τ _ L.symm.surjective hτ
  have hj : (jac₂ (stdSum h) π).comp L.symm.toMonoidHom = jac (two (stdSum h)) π :=
    MonoidHom.ext fun g => by simp [jac₂, L]
  have hs' : IsSubquotient τ' (jac (two (stdSum h)) π) := hj ▸ isSubquotient_comp' hs L.symm.toMonoidHom
  obtain ⟨φ⟩ := LocGL.nonempty_equiv_multiProd_one hπ (JacTensor.oneBlock n) fun _ _ => rfl
  have hinj : Function.Injective (jacMap (two (stdSum h)) φ.toIntertwiningMap) := by
    refine Function.LeftInverse.injective (g := jacMap (two (stdSum h)) φ.symm.toIntertwiningMap) fun x => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (φ.symm (φ v)) = _
    simp
  have h1 : IsSubquotient τ' (jac (two (stdSum h)) (multiProd (JacTensor.oneBlock n) fun _ : Fin 1 => π)) :=
    hs'.trans (.of_injective _ hinj)
  obtain ⟨bm, f, g, t, -, ht⟩ := exists_cell_of_isSubquotient (hGL k).1 (hGL k).2
    (m' := Two (Fin a) (Fin b)) (JacTensor.oneBlock n) (two (stdSum h)) (fun _ => hπ)
    (fun _ => hasFiniteLength_of_isIrreducible hirr) hτ' h1
  let F : ∀ j : Bool, Representation ℂ (GL (Two (Fin a) (Fin b) j) k) _ :=
    fun j => multiProd (g j) fun i => (t i j).ρ
  have h2 : IsSubquotient (τ'.comp L.toMonoidHom) ((piTensor F).comp L.toMonoidHom) :=
    isSubquotient_comp' ht L.toMonoidHom
  have h2' : IsSubquotient τ (τ'.comp L.toMonoidHom) :=
    .of_injective ⟨LinearMap.id, fun g => rfl⟩ Function.injective_id
  have h3 : IsSubquotient ((piTensor F).comp L.toMonoidHom) (extTensor (F false) (F true)) :=
    .of_injective (piTensorBoolEquiv F).toIntertwiningMap (piTensorBoolEquiv F).toLinearEquiv.injective
  exact ⟨_, _, _, _, _, _, F false, F true,
    isSmooth_parInd _ _, JacTensor.isIrreducible_multiProd_fin_one (g false) fun i => t i false,
    isSmooth_parInd _ _, JacTensor.isIrreducible_multiProd_fin_one (g true) fun i => t i true, h2'.trans (h2.trans h3)⟩

theorem isIrreducible_extTensor {R a b W W' : Type} [CommRing R] [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ (GL a R) W) (ρ : Representation ℂ (GL b R) W')
    (hσ : σ.IsIrreducible) (hρ : ρ.IsIrreducible)
    (hSσ : ∀ φ : W →ₗ[ℂ] W, (∀ g x, φ (σ g x) = σ g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id)
    (hSρ : ∀ φ : W' →ₗ[ℂ] W', (∀ g x, φ (ρ g x) = ρ g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id) :
    (extTensor σ ρ).IsIrreducible := by
  have h1 : (piTensor (Exponents.twoRep σ ρ)).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun j => by cases j <;> assumption)
      (fun j => by cases j <;> assumption)
  have h2 := isIrreducible_comp_surj _ (leviTwo R a b).toMonoidHom (leviTwo R a b).surjective h1
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv (piTensorBoolEquiv (Exponents.twoRep σ ρ)) h2

theorem nontrivial_of_isIrreducible {G Y : Type} [Group G] [AddCommGroup Y] [Module ℂ Y]
    {τ : Representation ℂ G Y} (hτ : τ.IsIrreducible) : Nontrivial Y := by
  haveI : IsSimpleOrder (Subrepresentation τ) := hτ
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply (bot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤)
  ext v
  exact ⟨fun _ => trivial, fun _ => Subsingleton.elim v 0⟩

theorem exists_bijective_of_isSubquotient {G Y X : Type} [Group G] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G Y} {χ : Representation ℂ G X}
    (hτ : τ.IsIrreducible) (hχ : χ.IsIrreducible) (h : IsSubquotient τ χ) :
    ∃ ψ : τ.IntertwiningMap χ, Function.Bijective ψ := by
  obtain ⟨S, f, hf⟩ := h
  haveI : IsSimpleOrder (Subrepresentation χ) := hχ
  haveI := nontrivial_of_isIrreducible hτ

  let T : Subrepresentation χ := ⟨(LinearMap.ker f.toLinearMap).map S.toSubmodule.subtype, by
    rintro g _ ⟨v, hv, rfl⟩
    refine ⟨S.toRepresentation g v, ?_, rfl⟩
    have hv' : f v = 0 := hv
    show f (S.toRepresentation g v) = 0
    have h' := LinearMap.congr_fun (f.isIntertwining' g) v
    simp only [LinearMap.comp_apply] at h'
    rw [show f (S.toRepresentation g v) = τ g (f v) from h', hv', map_zero]⟩
  have hinj : Function.Injective f := by
    rcases IsSimpleOrder.eq_bot_or_eq_top T with hT | hT
    · refine (injective_iff_map_eq_zero f).2 fun v hv => ?_
      have : (v : X) ∈ T.toSubmodule := ⟨v, hv, rfl⟩
      rw [hT] at this
      exact Subtype.ext this
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (0 : Y)
      obtain ⟨v, rfl⟩ := hf y
      have : (v : X) ∈ T.toSubmodule := by rw [hT]; trivial
      obtain ⟨w, hw, hwv⟩ := this
      rw [Subtype.ext hwv] at hw
      exact hy hw
  have hS : S = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top S with hS | hS
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (0 : Y)
      obtain ⟨v, rfl⟩ := hf y
      have h0 : S.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule hS
      have : (v : X) ∈ (⊥ : Submodule ℂ X) := h0 ▸ v.2
      have hv : v = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 this)
      rw [hv, map_zero] at hy
      exact hy rfl
    · exact hS
  let e : S.toSubmodule ≃ₗ[ℂ] Y := LinearEquiv.ofBijective f.toLinearMap ⟨hinj, hf⟩
  refine ⟨⟨S.toSubmodule.subtype ∘ₗ e.symm.toLinearMap, fun g => ?_⟩, ?_, ?_⟩
  · ext y
    obtain ⟨v, rfl⟩ := e.surjective y
    have h' := LinearMap.congr_fun (f.isIntertwining' g) v
    simp only [LinearMap.comp_apply] at h'
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      Submodule.subtype_apply]
    have : e.symm (τ g (e v)) = S.toRepresentation g v := by
      rw [LinearEquiv.symm_apply_eq]
      exact h'.symm
    rw [this]
    rfl
  · exact Subtype.val_injective.comp e.symm.injective
  · intro x
    have hx : x ∈ S.toSubmodule := by rw [hS]; trivial
    exact ⟨e ⟨x, hx⟩, by simp⟩

end GlobalTheory.JacFactor

theorem GlobalTheory.JacFactor.exists_extTensor_equiv_of_quotient_jac₂ : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.ZelevinskyPolynomialRing →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → ∀ (a b : ℕ) (h : a + b = n) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (GL (Fin a) k × GL (Fin b) k) Y), IsSmooth τ → τ.IsIrreducible →
    ∀ q : (jac₂ (stdSum h) π).IntertwiningMap τ, Function.Surjective q →
    ∃ (W W' : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : AddCommGroup W') (_ : Module ℂ W')
      (σ : Representation ℂ (GL (Fin a) k) W) (ρ : Representation ℂ (GL (Fin b) k) W'),
      IsSmooth σ ∧ σ.IsIrreducible ∧ IsSmooth ρ ∧ ρ.IsIrreducible ∧
      ∃ ψ : τ.IntertwiningMap (extTensor σ ρ), Function.Bijective ψ := by
  intro hBZ hGL _ k _ _ _ _ n V _ _ π hπ hirr a b h Y _ _ τ _ hτ q hq
  obtain ⟨W, W', i1, i2, i3, i4, σ, ρ, hσs, hσ, hρs, hρ, hsub⟩ :=
    GlobalTheory.JacFactor.exists_extTensor_of_isSubquotient_jac₂ hGL π hπ hirr h τ hτ
      (IsSubquotient.of_surjective q hq)
  have hSσ := GlobalTheory.SchurAdm.schur_admissible _ (GlobalTheory.SplitWeil.KO k (Fin a)) GlobalTheory.SplitFlip.isOpen_KO
    GlobalTheory.SplitFlip.isCompact_KO W σ hσ ((hBZ k).1 (Fin a) W σ hσs hσ)
  have hSρ := GlobalTheory.SchurAdm.schur_admissible _ (GlobalTheory.SplitWeil.KO k (Fin b)) GlobalTheory.SplitFlip.isOpen_KO
    GlobalTheory.SplitFlip.isCompact_KO W' ρ hρ ((hBZ k).1 (Fin b) W' ρ hρs hρ)
  obtain ⟨ψ, hψ⟩ := GlobalTheory.JacFactor.exists_bijective_of_isSubquotient hτ
    (GlobalTheory.JacFactor.isIrreducible_extTensor σ ρ hσ hρ hSσ hSρ) hsub
  exact ⟨W, W', i1, i2, i3, i4, σ, ρ, hσs, hσ, hρs, hρ, ψ, hψ⟩
