import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtZeroIncZeroMemLattice

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PcBFDual

variable {D : D7}

section Proj

variable {T : HSp D} {Λ : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop} (M : Mx D T.rank T.rank)

theorem mulVec_latV (hM : ∀ v, P v → ∀ y ∈ latV T Λ (· = v), M *ᵥ y ∈ latV T Λ (· = v))
    (hΛ : Submodule.IsLattice D.host.E Λ) {y : Fin T.rank → AE D} (hy : y ∈ latV T Λ P) : M *ᵥ y ∈ latV T Λ P := by
  refine (GlobalTheory.FinPlLoc.part_lat P T Λ _ hΛ).2 ⟨GlobalTheory.FinPl.ExtZeroAt.mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy), fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact hM v hv _ (GlobalTheory.FinPlLoc.smul_latV v he hy)

theorem smul_mem_latA_idLat (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) {a s : D.host.E} (ha : a ∈ D.host.AA) (hs : s ∈ I)
    {w : Fin T.rank → AE D} (hw : w ∈ latV T Λ P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] (a * s)) • w ∈ latA T (idLat I Λ) P := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, s • x, Submodule.subset_span ⟨s, hs, x, hx, rfl⟩, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_assoc]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

set_option maxHeartbeats 1000000 in

theorem mulVec_latA_idLat (hM : ∀ v, P v → ∀ y ∈ latV T Λ (· = v), M *ᵥ y ∈ latV T Λ (· = v))
    (hΛ : Submodule.IsLattice D.host.E Λ) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) {z : Fin T.rank → AE D}
    (hz : z ∈ latA T (idLat I Λ) P) : M *ᵥ z ∈ latA T (idLat I Λ) P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    have key : ∀ x ∈ Submodule.span (𝓞 D.host.E) {z | ∃ s ∈ I, ∃ y ∈ Λ, z = s • y}, ∀ c : 𝓞 D.host.E,
        M *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • x) i)) ∈ latA T (idLat I Λ) P := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨s, hs, y, hy, rfl⟩ := hx
        intro c
        have hyv : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * y i)) ∈ latV T Λ P :=
          AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, y, hy, rfl⟩
        have e : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • s • y) i)) =
            ((1 : AF D.host.F) ⊗ₜ[D.host.F] (a * (c • s))) • (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * y i)) := by
          funext i
          rw [← smul_assoc]
          simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_assoc]
        rw [e, Matrix.mulVec_smul]
        exact smul_mem_latA_idLat I ha (Submodule.smul_mem _ c hs) (mulVec_latV M hM hΛ hyv)
      | zero =>
        intro c
        have e : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • (0 : Fin T.rank → D.host.E)) i)) = 0 := by
          funext i; simp only [smul_zero, Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
        rw [e, Matrix.mulVec_zero]; exact zero_mem _
      | add x x' _ _ h h' =>
        intro c
        have e : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • (x + x')) i)) =
            (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • x) i)) +
              (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • x') i)) := by
          funext i; simp only [smul_add, Pi.add_apply, mul_add, TensorProduct.tmul_add]
        rw [e, Matrix.mulVec_add]; exact add_mem (h c) (h' c)
      | smul c' x _ h =>
        intro c
        rw [smul_smul]
        exact h (c * c')
    have := key x hx 1
    simpa only [one_smul] using this
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

end Proj

section Split

theorem projY_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : GlobalTheory.FinPl.Pl D}
    (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) : (d.jY ⬝ d.pY) *ᵥ y ∈ latV S L (· = v) := by
  have e : (d.jY ⬝ d.pY) *ᵥ y = ∑ i, GlobalTheory.FinPl.colMul d.jY i ((d.pY *ᵥ y) i) := by
    rw [← Matrix.mulVec_mulVec]
    funext k
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.colMul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact sum_mem fun i _ => ((h y).1 hy).2.1 i

theorem projX_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : GlobalTheory.FinPl.Pl D}
    (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) : (d.jX ⬝ d.pX) *ᵥ y ∈ latV S L (· = v) := by
  have e : (d.jX ⬝ d.pX) *ᵥ y = ∑ i, GlobalTheory.FinPl.colMul d.jX i ((d.pX *ᵥ y) i) := by
    rw [← Matrix.mulVec_mulVec]
    funext k
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.colMul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact sum_mem fun i _ => ((h y).1 hy).1 i

theorem extend_mem_lattice_iff {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {LV : Lat V} {LV₀ : Lat V₀} {LW : Lat W}
    (hV : IsSelfDualC V LV) (hV₀ : IsSelfDualC V₀ LV₀) (hW : IsSelfDualC W LW) {P : GlobalTheory.FinPl.Pl D → Prop}
    (hm : ∀ v, P v → MonoAt d LV LV₀ v) (w : WO V₀ W) :
    d.ext0 W w ∈ latO V W (LV : Set _) (LW : Set _) P ↔ w ∈ latO V₀ W (LV₀ : Set _) (LW : Set _) P := by
  constructor
  · intro hw
    have hx := GlobalTheory.FinPl.LatMem.latO_mxAt hw
    refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D V₀ W LV₀ LW hV₀ hW P _).2 ⟨?_, fun y hy => ?_⟩
    · have := GlobalTheory.AscFinWit.mxAt_mul' hx d.j0
      rwa [HypDec.matrixExtendByZero_apply, Matrix.mul_assoc, d.p0_j0, Matrix.mul_one] at this
    · have h2 := GlobalTheory.FinPl.LatMem.latO_maps hV hw (GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace d hV.1 hm hy)
      rwa [HypDec.matrixExtendByZero_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc, d.p0_j0, Matrix.mul_one] at h2
  · intro hw
    refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D V W LV LW hV hW P _).2
      ⟨GlobalTheory.AscFinWit.mxAt_mul' (GlobalTheory.FinPl.LatMem.latO_mxAt hw) _, fun y hy => ?_⟩
    rw [HypDec.matrixExtendByZero_apply, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.FinPl.LatMem.latO_maps hV₀ hw (GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits d hV₀.1 hm hy)

theorem left_mem {S W : HSp D} {LS : Lat S} {Λ : Lat W} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {P : GlobalTheory.FinPl.Pl D → Prop}
    (hS : IsSelfDualC S LS) (hW : IsSelfDualC W (idLat I Λ)) (hΛ : Submodule.IsLattice D.host.E Λ) (M : Mx D W.rank W.rank)
    (hM : ∀ v, P v → ∀ y ∈ latV W Λ (· = v), M *ᵥ y ∈ latV W Λ (· = v)) {u : WO S W}
    (hu : u ∈ latO S W (LS : Set _) (idLat I Λ : Set _) P) : M ⬝ u ∈ latO S W (LS : Set _) (idLat I Λ : Set _) P := by
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D S W LS _ hS hW P _).2
    ⟨GlobalTheory.AscFinWit.mxAt_mul _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu), fun y hy => ?_⟩
  show (M * u) *ᵥ y ∈ _
  rw [← Matrix.mulVec_mulVec]
  exact mulVec_latA_idLat M hM hΛ I (GlobalTheory.FinPl.LatMem.latO_maps hS hu hy)

end Split

end GlobalTheory.PcBFDual

namespace GlobalTheory.PcBFDual

theorem dualB : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m),
    (∀ ξ, MxAt (fun _ => True) ξ → (ξ ∈ (pcBF W F ρ h).B₁ ↔ ∀ η ∈ (pcBF W F ρ h).B₂,
      W.ψ (symplO (F.V₀ ρ) _ ((F.dJ ρ h).incX _ ξ) ((F.dJ ρ h).incY _ η)) = 1)) ∧
    ∀ η, MxAt (fun _ => True) η → (η ∈ (pcBF W F ρ h).B₂ ↔ ∀ ξ ∈ (pcBF W F ρ h).B₁,
      W.ψ (symplO (F.V₀ ρ) _ ((F.dJ ρ h).incX _ ξ) ((F.dJ ρ h).incY _ η)) = 1) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h
  have I := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF
  have sd : ∀ X : Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → IsSelfDualC (G.V X) (G.Λ X) :=
    fun X h1 h2 => (G.isV h1 h2).sd
  have hV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    sd _ ⟨h, Nat.zero_le _⟩ (fun j e => by cases e)
  have hΛ : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    sd _ ⟨by omega, Nat.zero_le _⟩ (fun j e => by cases e)
  have hV₀ : IsSelfDualC (F.V₀ ρ) (lat0 F ρ h) := (I.2.1 ρ h).1
  have hW : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0))) :=
    (I.1 (2 * ρ + 1) (by omega)).2.2.2
  have hmV : ∀ v, MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := fun v => ((I.2.1 ρ h).2.1 v).1
  have hmW : ∀ v, MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v :=
    fun v => ((I.2.1 ρ h).2.1 v).2
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hB : ∀ w, (F.dB ρ h).ext0 _ w ∈ latBig G (2 * ρ + 1) ↔
      w ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
        (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) fun _ => True :=
    fun w => extend_mem_lattice_iff (F.dB ρ h) hV hV₀ hW (fun v _ => hmV v) w
  have tY : ∀ u ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
      (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True),
      (F.dJ ρ h).incY _ ((F.dJ ρ h).pY ⬝ u) ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
        (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True) := fun u hu => by
    rw [HypDec.incY_apply, ← Matrix.mul_assoc]
    exact left_mem hV₀ hW hΛ.1 _ (fun v _ y hy => projY_mem _ (hmW v) hy) hu
  have tX : ∀ u ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
      (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True),
      (F.dJ ρ h).incX _ ((F.dJ ρ h).pX ⬝ u) ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
        (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True) := fun u hu => by
    rw [HypDec.incX_apply, ← Matrix.mul_assoc]
    exact left_mem hV₀ hW hΛ.1 _ (fun v _ y hy => projX_mem _ (hmW v) hy) hu
  refine ⟨fun ξ hξ => ?_, fun η hη => ?_⟩
  · refine (hB ((F.dJ ρ h).incX _ ξ)).trans ?_
    refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ hψ _ _ _ _ hV₀ hW _ _ (GlobalTheory.AscFinWit.mxAt_mul (F.dJ ρ h).jX hξ)).trans ?_
    refine ⟨fun H η hη => H _ ((hB ((F.dJ ρ h).incY _ η)).1 hη), fun H u hu => ?_⟩
    exact (congrArg W.ψ (GlobalTheory.AscFinWit.symplO_incX (F.dJ ρ h) _ ξ u)).trans (H _ ((hB ((F.dJ ρ h).incY _ _)).2 (tY u hu)))
  · refine (hB ((F.dJ ρ h).incY _ η)).trans ?_
    refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ hψ _ _ _ _ hV₀ hW _ _ (GlobalTheory.AscFinWit.mxAt_mul (F.dJ ρ h).jY hη)).trans ?_
    refine ⟨fun H ξ hξ => (GlobalTheory.AscFinWit.psi_swap _ _).1 (H _ ((hB ((F.dJ ρ h).incX _ ξ)).1 hξ)), fun H u hu => ?_⟩
    exact (congrArg W.ψ (GlobalTheory.AscFinWit.symplO_incY (F.dJ ρ h) _ η u)).trans
      ((GlobalTheory.AscFinWit.psi_swap _ _).1 (H _ ((hB ((F.dJ ρ h).incX _ _)).2 (tX u hu))))

end GlobalTheory.PcBFDual
