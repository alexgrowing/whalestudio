import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.RatTop

theorem exists_linearMap_of_repr_mem_range {K : Type} [Field K] (φ : K →+* ℂ) {VS VT WS WT : Type}
    [AddCommGroup VS] [Module K VS] [AddCommGroup VT] [Module K VT]
    [AddCommGroup WS] [Module ℂ WS] [AddCommGroup WT] [Module ℂ WT]
    (mS : VS →ₛₗ[φ] WS) (mT : VT →ₛₗ[φ] WT) {ι κ : Type} [Fintype ι] [Fintype κ]
    (b0 : Module.Basis ι K VS) (bS : Module.Basis ι ℂ WS) (bT : Module.Basis κ ℂ WT)
    (uS : ι → VS) (uT : κ → VT) (hS : ∀ i, mS (uS i) = bS i) (hT : ∀ k, mT (uT k) = bT k)
    (L : WS →ₗ[ℂ] WT) (hL : ∀ k i, bT.repr (L (bS i)) k ∈ Set.range φ) :
    ∃ f : VS →ₗ[K] VT, ∀ u, L (mS u) = mT (f u) := by
  classical
  haveI : FiniteDimensional K VS := Module.Finite.of_basis b0
  have hli : LinearIndependent K uS := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 : ∑ i, φ (g i) • bS i = 0 := by
      have := congrArg mS hg
      simpa [map_sum, LinearMap.map_smulₛₗ, hS] using this
    have h2 := Fintype.linearIndependent_iff.mp bS.linearIndependent _ h1 i
    exact φ.injective (by rw [h2, map_zero])
  have hsp : Submodule.span K (Set.range uS) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis b0).symm
  let bS' : Module.Basis ι K VS := Module.Basis.mk hli hsp.ge
  choose m hm using hL
  let f : VS →ₗ[K] VT := bS'.constr K fun i => ∑ k, m k i • uT k
  refine ⟨f, fun u => ?_⟩
  have e : (L.comp mS : VS →ₛₗ[φ] WT) = (mT.comp f : VS →ₛₗ[φ] WT) := by
    refine bS'.ext fun i => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Module.Basis.constr_basis, Module.Basis.mk_apply, hS, map_sum]
    conv_lhs => rw [← bT.sum_repr (L (bS i))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.map_smulₛₗ, hT, hm]
  exact LinearMap.congr_fun e u

end GlobalTheory.RatTop

namespace GlobalTheory.KerConjMean

theorem ratTopAt_big : BigC fun _ ch _ _ => RatTopAt ch := by
  refine ⟨0, fun _ _ => ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩⟩
  intro D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ hK
  intro Φ β d hd c j
  obtain ⟨hβ, τ, hτ, hdτ⟩ := hd
  have hr := (hK.isRatAt hβ hτ hdτ c).1 j
  refine GlobalTheory.RatTop.exists_linearMap_of_repr_mem_range D.what₂.embLL (GlobalTheory.CoefModel.mapVV D.what₂.embLL _)
    (GlobalTheory.CoefModel.mapVV D.what₂.embLL _) (bVV D.what₂.LL _) (bVV ℂ _) (bVV ℂ _)
    (fun i => ⟨_, (GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ i).choose_spec.1⟩)
    (fun k => ⟨_, (GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.1⟩) ?_ ?_ _ ?_
  · intro i
    apply Subtype.ext
    rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
    exact ((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ i).choose_spec.2).symm
  · intro k
    apply Subtype.ext
    rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
    exact ((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.2).symm
  · intro k i
    have h := hr k i
    rwa [Normal.kkIn, LinearMap.toMatrix_apply] at h

end GlobalTheory.KerConjMean

end
