import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DblActId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxRationalBasisCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticMemClosureGenerators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDarbouxOperatorsLeviAndDoubleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDarbouxChangeOperatorWithDoubleLowerUnipotStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementRealisedByFourierTransformsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxChangeRealisedCompAndReindexStatement
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

namespace GlobalTheory.TowU

theorem card_two_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ]
    {B : Matrix α β (AE F E) → Matrix α β (AE F E) → AF F} (d : Darboux B κ) :
    Fintype.card κ * 2 = Fintype.card α * Fintype.card β * Module.finrank F E := by
  haveI : Nontrivial (AF F) := (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  haveI : FiniteDimensional F E := Module.Finite.right ℚ F E
  have h1 := d.e.finrank_eq
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_matrix,
    Module.finrank_baseChange] at h1
  omega

noncomputable def reidx {F : Type} [Field F] [NumberField F] {κ κ' : Type} (e : κ' ≃ κ) :
    ((κ' → AF F) × (κ' → AF F)) ≃ₗ[AF F] ((κ → AF F) × (κ → AF F)) where
  toFun p := (p.1 ∘ e.symm, p.2 ∘ e.symm)
  invFun p := (p.1 ∘ e, p.2 ∘ e)
  map_add' p q := rfl
  map_smul' c p := rfl
  left_inv p := by ext i <;> simp
  right_inv p := by ext i <;> simp

noncomputable def reindexD {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (d : Darboux B κ') (e : κ' ≃ κ) : Darboux B κ where
  e := d.e.trans (reidx e)
  form w w' := by
    rw [d.form]
    have h : ∀ u v : κ' → AF F, (u ∘ e.symm) ⬝ᵥ (v ∘ e.symm) = u ⬝ᵥ v := fun u v => by
      simp only [dotProduct, Function.comp_apply]
      exact e.symm.sum_comp (fun j => u j * v j)
    simp only [LinearEquiv.trans_apply]
    exact (congrArg₂ (· - ·) (h _ _) (h _ _)).symm

theorem reindexD_e {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (d : Darboux B κ') (e : κ' ≃ κ) (w : W) :
    (reindexD d e).e w = ((d.e w).1 ∘ e.symm, (d.e w).2 ∘ e.symm) := rfl

theorem realised_of_sp {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    [DecidableEq κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (hg : gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0) :
    ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
      IsOp2 ψ (GlobalTheory.AdelicSvN.act g) S S' := by
  have hcl := GlobalTheory.sympGen F κ g hg
  clear hg
  induction hcl using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with (⟨A, hA, rfl⟩ | ⟨C, hC, rfl⟩) | hx
    · exact GlobalTheory.T.exists_darbouxOperators_levi_and_double F ψ hψ κ A hA
    · exact GlobalTheory.T.exists_darbouxChangeOperatorWithDouble_lowerUnipotent F ψ hψ κ C hC
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact GlobalTheory.T.weylElement_realised_by_fourierTransforms F ψ hψ κ
  | one =>
    obtain ⟨S, S', h⟩ := (GlobalTheory.T.darbouxChange_realised_comp_and_reindex F ψ hψ).2 κ κ (Equiv.refl κ)
    refine ⟨S, S', ?_⟩
    have : GlobalTheory.AdelicSvN.act (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) = fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ Equiv.refl κ, w.2 ∘ Equiv.refl κ) := by
      funext w; rw [GlobalTheory.AdelicSvN.act_one]; rfl
    rw [this]; exact h
  | mul x y _ _ hx hy =>
    obtain ⟨S, S', hS⟩ := hx
    obtain ⟨T, T', hT⟩ := hy
    have : GlobalTheory.AdelicSvN.act (x * y) = GlobalTheory.AdelicSvN.act x ∘ GlobalTheory.AdelicSvN.act (R := AF F) y := by
      funext w; exact GlobalTheory.AdelicSvN.act_mul x y w
    rw [this]
    exact ⟨S ∘ₗ T, T' ∘ₗ S', (GlobalTheory.T.darbouxChange_realised_comp_and_reindex F ψ hψ).1 κ κ κ _ _ T T' S S' hT hS⟩

theorem darboux_change : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ψ : AddChar (AF F) ℂ, IsStd ψ → ∀ (α β κ κ' : Type) [Fintype α] [Fintype β] [Fintype κ] [Fintype κ'] (B : Matrix α β (AE F E) → Matrix α β (AE F E) → AF F) (d : Darboux B κ) (d' : Darboux B κ'), IsRat d → IsRat d' → ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (fun w => d'.e (d.e.symm w)) S S' := by
  intro F E _ _ _ _ _ σ _ ψ hψ α β κ κ' _ _ _ _ B d d' hd hd'
  have hc := card_two_eq F E d
  have hc' := card_two_eq F E d'
  have hκ : Fintype.card κ' = Fintype.card κ := by omega
  let e : κ' ≃ κ := Fintype.equivOfCardEq hκ
  let d'' := reindexD d' e
  have hd'' : IsRat d'' := fun x => by
    obtain ⟨y, z, h⟩ := hd' x
    refine ⟨y ∘ e.symm, z ∘ e.symm, ?_⟩
    rw [reindexD_e, h]; rfl
  obtain ⟨g, hg, hgd⟩ := GlobalTheory.RatDarboux.exists_rat_symplectic F E α β κ B d d'' hc hd hd''
  obtain ⟨S, S', hS⟩ := realised_of_sp ψ hψ g hg
  obtain ⟨T, T', hT⟩ := (GlobalTheory.T.darbouxChange_realised_comp_and_reindex F ψ hψ).2 κ κ' e
  have hs : (fun w => d'.e (d.e.symm w)) = (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) ∘ GlobalTheory.AdelicSvN.act g := by
    funext w
    have := hgd (d.e.symm w)
    simp only [LinearEquiv.apply_symm_apply] at this
    rw [Function.comp_apply, ← this, reindexD_e]
    ext i <;> simp
  rw [hs]
  exact ⟨T ∘ₗ S, S' ∘ₗ T', (GlobalTheory.T.darbouxChange_realised_comp_and_reindex F ψ hψ).1 κ κ κ' _ _ S S' T T' hS hT⟩

end GlobalTheory.TowU
