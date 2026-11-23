import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose

noncomputable section

open scoped TensorProduct
open Module

namespace GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases

def IsForm (LL : Type) {Ks WL : Type} [Field Ks] [Field LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    (WK : Submodule Ks WL) : Prop :=
  ∃ (n : ℕ) (b : Fin n → WL), (∀ i, b i ∈ WK) ∧ LinearIndependent Ks b ∧
    Submodule.span Ks (Set.range b) = WK ∧ LinearIndependent LL b ∧ Submodule.span LL (Set.range b) = ⊤

section

variable {Ks LL WL : Type} [Field Ks] [Field LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
  {WK : Submodule Ks WL}
  (O : Type) {K K'' : Type} [CommRing O] [Field K] [Algebra Ks K] [Field K''] [Algebra O K'']
  {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm]

def IsExt (emb : LL →+* K'') (eF : Fm ≃ₗ[K] K ⊗[Ks] WK) (e : WL →ₛₗ[emb] K'' ⊗[O] Fm) : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → LL) (f : ι → WK),
    e (∑ k, a k • (f k : WL)) = ∑ k, emb (a k) ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] f k)

def CarriesBases {emb : LL →+* K''} (e : WL →ₛₗ[emb] K'' ⊗[O] Fm) : Prop :=
  ∀ (ι : Type) (b : Basis ι LL WL), ∃ b'' : Basis ι K'' (K'' ⊗[O] Fm), ∀ i, b'' i = e (b i)

end

def SemilinearExtension : Prop :=
  ∀ (Ks LL WL : Type) [Field Ks] [Field LL] [Algebra Ks LL]
    [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    (WK : Submodule Ks WL), IsForm LL WK →
  ∀ (O K K'' : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [Algebra Ks K]
    [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
    (emb : LL →+* K''), emb.comp (algebraMap Ks LL) = (algebraMap K K'').comp (algebraMap Ks K) →
  ∀ (Fm : Type) [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]
    (eF : Fm ≃ₗ[K] K ⊗[Ks] WK),
    (∃! e : WL →ₛₗ[emb] K'' ⊗[O] Fm, IsExt O emb eF e) ∧
    (∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm, IsExt O emb eF e → CarriesBases O e) ∧
    (∀ (a : Ks) (m : Fm),
      emb (algebraMap Ks LL a) ⊗ₜ[O] m = (1 : K'') ⊗ₜ[O] (algebraMap Ks K a • m))

example : IsForm ℂ (Submodule.span ℝ {(1 : ℂ)}) := by
  refine ⟨1, fun _ => 1, fun _ => Submodule.subset_span rfl, ?_, ?_, ?_, ?_⟩
  · exact linearIndependent_unique_iff.2 one_ne_zero
  · simp
  · exact linearIndependent_unique_iff.2 one_ne_zero
  · rw [eq_top_iff]; intro z _
    have : z = z • (1 : ℂ) := by simp
    rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

example : ¬ IsForm ℂ (⊤ : Submodule ℝ ℂ) := by
  rintro ⟨n, b, -, h1, h2, h3, h4⟩
  have e1 := finrank_eq_card_basis (Basis.mk h1 h2.ge)
  have e2 := finrank_eq_card_basis (Basis.mk h3 h4.ge)
  simp at e1 e2
  omega

theorem IsExt.apply_coe {Ks LL WL : Type} [Field Ks] [Field LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    {WK : Submodule Ks WL} {O K K'' : Type} [CommRing O] [Field K] [Algebra Ks K] [Field K''] [Algebra O K'']
    {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm]
    {emb : LL →+* K''} {eF : Fm ≃ₗ[K] K ⊗[Ks] WK} {e : WL →ₛₗ[emb] K'' ⊗[O] Fm} (h : IsExt O emb eF e) (f : WK) :
    e f = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] f) := by
  simpa using h Unit (fun _ => 1) (fun _ => f)

end GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases
