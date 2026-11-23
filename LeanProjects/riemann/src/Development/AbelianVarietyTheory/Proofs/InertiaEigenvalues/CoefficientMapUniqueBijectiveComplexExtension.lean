import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasis

noncomputable section

namespace GlobalTheory.CoefExtC

section General

open Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.AdTh.CoefExt

variable {K : Type} [Field K] {σ : K →+* ℂ} {I : Type} [Fintype I] {n : ℕ} {lam : I → DomWeight n}
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_ext (c' : VV K lam →ₛₗ[σ] W) (hs : Submodule.span ℂ (Set.range c') = ⊤)
    (hli : LinearIndependent ℂ fun j => c' (bVV K lam j)) :
    ∃ c : VV ℂ lam →ₗ[ℂ] W, (∀ v, c (up σ lam v) = c' v) ∧ Function.Bijective c ∧
      ∀ d : VV ℂ lam →ₗ[ℂ] W, (∀ v, d (up σ lam v) = c' v) → d = c := by
  classical
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun j => up σ lam (bVV K lam j)) := by
    intro v _
    obtain ⟨a, rfl⟩ := exists_coord σ lam v
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hcard : Fintype.card (VVIdx lam) = Module.finrank ℂ (VV ℂ lam) := (Module.finrank_eq_card_basis (bVV ℂ lam)).symm
  let b : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) := basisOfTopLeSpanOfCardEqFinrank _ hsp hcard
  have hb : ∀ j, b j = up σ lam (bVV K lam j) := fun j => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ hsp hcard) j
  have hsw : ⊤ ≤ Submodule.span ℂ (Set.range fun j => c' (bVV K lam j)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    rw [← (bVV K lam).sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let w : Module.Basis (VVIdx lam) ℂ W := Module.Basis.mk hli hsw
  have hc : ∀ j, (b.equiv w (Equiv.refl _)) (up σ lam (bVV K lam j)) = c' (bVV K lam j) := by
    intro j
    rw [← hb, Module.Basis.equiv_apply]
    exact Module.Basis.mk_apply hli hsw j
  refine ⟨(b.equiv w (Equiv.refl _)).toLinearMap, fun v => ?_, (b.equiv w (Equiv.refl _)).bijective, fun d hd => ?_⟩
  · rw [← (bVV K lam).sum_repr v, up_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smulₛₗ, LinearEquiv.coe_coe, hc]
  · refine b.ext fun j => ?_
    rw [hb, hd, LinearEquiv.coe_coe, hc]

theorem li_basis (c' : VV K lam →ₛₗ[σ] W)
    (h : ∀ (m : ℕ) (b : Fin m → VV K lam), LinearIndependent K b → LinearIndependent ℂ fun j => c' (b j)) :
    LinearIndependent ℂ fun j => c' (bVV K lam j) := by
  let e := Fintype.equivFin (VVIdx lam)
  have h1 := h _ (bVV K lam ∘ e.symm) ((bVV K lam).linearIndependent.comp _ e.symm.injective)
  have h2 := h1.comp e e.injective
  convert h2 using 1
  funext j
  simp

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 800000 in

theorem exists_extC_bijective_unique : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∃ c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, ExtC R i (inC M.c') M.c0' c ∧ Function.Bijective c ∧ ∀ c', ExtC R i (inC M.c') M.c0' c' → c' = c := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ i Tp tup O hP
  obtain ⟨gramR, c0R, c0L, hT, hc⟩ := hP.lift.c0
  have hE : ∀ v, O.c0' (GlobalTheory.AdTh.CoefExt.up O.jL (lamV D i) v) = c0L i v := by
    intro v
    obtain ⟨w, hw, h⟩ := hc v
    rw [show GlobalTheory.AdTh.CoefExt.up O.jL (lamV D i) v = w from Subtype.ext hw.symm]
    exact h
  obtain ⟨-, h2, h3⟩ := hT.mapL i
  obtain ⟨c, h4, h5, h6⟩ := exists_ext (W := (R.cV i).W) O.c0' (GlobalTheory.AdTh.CoefExt.span_top (W := (R.cV i).W) hE h3)
    (li_basis (W := (R.cV i).W) O.c0' fun m b hb => GlobalTheory.AdTh.CoefExt.linearIndependent (W := (R.cV i).W) hE h2 b hb)
  refine ⟨c, fun v v' hv => ?_, h5, fun d hd => h6 d fun v => hd v _ rfl⟩
  rw [show v' = GlobalTheory.AdTh.CoefExt.up (inC O.c') (lamV D i) v from Subtype.ext hv]
  exact h4 v

end GlobalTheory.CoefExtC

end
