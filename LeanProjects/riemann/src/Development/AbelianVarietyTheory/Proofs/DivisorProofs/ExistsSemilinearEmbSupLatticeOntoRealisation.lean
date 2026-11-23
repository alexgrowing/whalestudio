import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.CovTop.SupImage

theorem linearIndependent_of_form {K L V : Type} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V] [Module L V]
    [IsScalarTower K L V] {S : Submodule K V} {n : ℕ} {b : Fin n → V} (hK : LinearIndependent K b)
    (hS : Submodule.span K (Set.range b) = S) (hL : LinearIndependent L b) {ι : Type} {c : ι → S}
    (hc : LinearIndependent K c) : LinearIndependent L fun k => (c k : V) := by
  subst hS
  let B := (Module.Basis.span hK).baseChange L
  let φ : L ⊗[K] Submodule.span K (Set.range b) →ₗ[L] V := (Submodule.span K (Set.range b)).subtype.liftBaseChange L
  have hB : φ ∘ B = b := by
    funext k
    simp [B, φ, Module.Basis.span_apply]
  have hφ : Function.Injective φ :=
    LinearMap.injective_of_linearIndependent (by rw [B.span_eq]) (hB ▸ hL)
  have h1 : LinearIndependent L fun k => (1 : L) ⊗ₜ[K] c k := Module.Flat.linearIndependent_one_tmul hc
  have h2 := h1.map' φ (LinearMap.ker_eq_bot.2 hφ)
  have h3 : (φ ∘ fun k => (1 : L) ⊗ₜ[K] c k) = fun k => (c k : V) := by
    funext k
    simp [φ]
  exact h3 ▸ h2

set_option maxHeartbeats 1000000 in

theorem exists_emb_image_latW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), ∃ ι : VK fw i →ₛₗ[algebraMap T.Q.c.F D.what₂.LL] (Fin (R.nW i) → D.what₂.LL), (∀ (f : VK fw i), ∃ h : (f : T.R ((i : ℕ) + 1)) ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ι f = ((fw.e i ⟨f, h⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)) ∧ (∀ (n : ℕ) (b : Fin n → VK fw i), LinearIndependent T.Q.c.F b → LinearIndependent D.what₂.LL (fun k => ι (b k))) ∧ ι '' (latW (T.U ((i : ℕ) + 1)) (wtZ (wtA (κ i)) (κ i).n) : Set (VK fw i)) = ((R.FW i).MK : Set (Fin (R.nW i) → D.what₂.LL)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ fw i
  have hE : VK fw i = T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := cuspW_wtZ _ _
  let e : VK fw i ≃ₗ[T.Q.c.F] (R.FW i).WK := (LinearEquiv.ofEq _ _ hE).trans (fw.e i)
  have he : ∀ f : VK fw i, e f = fw.e i ⟨f, hE ▸ f.2⟩ := fun _ => rfl
  let ι : VK fw i →ₛₗ[algebraMap T.Q.c.F D.what₂.LL] (Fin (R.nW i) → D.what₂.LL) :=
    { toFun := fun f => (e f : Fin (R.nW i) → D.what₂.LL)
      map_add' := fun f g => by rw [map_add]; rfl
      map_smul' := fun a f => by rw [map_smul, algebraMap_smul]; rfl }
  have key : ∀ f : VK fw i, f ∈ latW (T.U ((i : ℕ) + 1)) (wtZ (wtA (κ i)) (κ i).n) ↔ ι f ∈ (R.FW i).MK := fun f => by
    have en := fun la y => fw.nrm_eq i la y ⟨f.1, hE ▸ f.2⟩
    constructor
    · intro hf
      refine ⟨(e f).2, fun la y => (en la y).trans_le ?_⟩
      exact (T.nrmM_le_one_iff _ la _ _).2 (hf la _ (fw.pt i la y).2)
    · rintro ⟨_, hf⟩ la v hv
      obtain ⟨y, hy⟩ := (fw.pt i la).surjective ⟨v, hv⟩
      have h2 := (en la y).symm.trans_le (hf la y)
      rw [hy] at h2
      exact (T.nrmM_le_one_iff _ la ⟨v, hv⟩ _).1 h2
  refine ⟨ι, fun f => ⟨hE ▸ f.2, rfl⟩, fun n b hb => ?_, ?_⟩
  · obtain ⟨m, c, -, h1, h2, h3, -⟩ := fw.ks i
    exact linearIndependent_of_form h1 h2 h3 (hb.map' e.toLinearMap e.ker)
  · ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (key f).1 hf
    · intro hx
      obtain ⟨f, hf⟩ := e.surjective ⟨x, hx.1⟩
      have hx' : ι f = x := congrArg Subtype.val hf
      exact ⟨f, (key f).2 (hx' ▸ hx), hx'⟩

end GlobalTheory.CovTop.SupImage

end
