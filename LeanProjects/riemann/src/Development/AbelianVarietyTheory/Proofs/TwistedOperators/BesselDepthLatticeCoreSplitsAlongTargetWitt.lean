import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtZeroIncZeroMemLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportCorrectionCarriesColumnLatticeRowTrace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPointOfDecoratedLatticeUnique

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TgtCoreSplit

variable {D : D7}

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem finPart_pure (α : Af D.host.F) (e : D.host.E) :
    finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e) = α ⊗ₜ[D.host.F] e := by
  unfold finPart
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
  rfl

theorem toEAf_pure (e : D.host.E) :
    toEAf D ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] e) =
      Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) e := by
  unfold toEAf
  rw [RingHom.comp_apply, finPart_pure]
  rfl

theorem rat_mulVec_pure {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (α : Af D.host.F) (t : Fin n → D.host.E) :
    rat M *ᵥ (fun i => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] t i) =
      fun i => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (M *ᵥ t) i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i k) * _ = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem proj_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : Submodule.IsLattice D.host.E L) (hL₀ : Submodule.IsLattice D.host.E L₀) (hm : ∀ v, MonoAt d L L₀ v)
    {t : Fin S.rank → D.host.E} (ht : t ∈ L) : (d.i₀ * d.q0) *ᵥ t ∈ L := by
  have hy : (fun i => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] t i) ∈ latV S L (fun _ => True) :=
    AddSubgroup.subset_closure ⟨1, one_mem_intAf, fun v hv => (hv trivial).elim, 1, rfl, t, ht, by
      funext i; rw [one_mul]⟩
  have h2 := GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace d hL (fun v _ => hm v)
    (GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits d hL₀ (fun v _ => hm v) hy)
  have e : d.j0 *ᵥ (d.p0 *ᵥ (fun i => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] t i)) =
      fun i => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] ((d.i₀ * d.q0) *ᵥ t) i := by
    rw [Matrix.mulVec_mulVec, show d.j0 * d.p0 = rat (d.i₀ * d.q0) by rw [rat_mul]; rfl]
    exact rat_mulVec_pure _ _ _
  rw [e] at h2
  have h3 := (GlobalTheory.Core.Mi.LatMatch.TraceX.latV_iff_hatL S L _ _ (GlobalTheory.FinPlLoc.latV_idAt h2)).1 h2
  simp only [toEAf_pure] at h3
  exact (GlobalTheory.Mem.Col2.PtUniq.mem_iff_hatL (F := D.host.F) hL _).2 h3

theorem mul_mem_latO {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop}
    (M : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (hM : ∀ t ∈ LT, M *ᵥ t ∈ LT) {u : WO S T}
    (hu : u ∈ latO S T LS (LT : Set _) P) : rat M * u ∈ latO S T LS (LT : Set _) P := by
  induction hu using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨α, hα, hαP, a, ha, s, hs, M *ᵥ t, hM t ht, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply]
    generalize (∑ k, star (s k) * S.gram k j) = c
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i k) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    ring
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

theorem mul_mem_smul_homLat {m n : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (M : Matrix (Fin m) (Fin m) D.host.E)
    (hM : ∀ t ∈ Λ', M *ᵥ t ∈ Λ') {x : Matrix (Fin m) (Fin n) D.host.E} (hx : x ∈ I • homLat Λ Λ') :
    M * x ∈ I • homLat Λ Λ' := by
  refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun a b ha hb => ?_)
  · rw [Matrix.mul_smul]
    refine Submodule.smul_mem_smul hr fun z hz => ?_
    rw [← Matrix.mulVec_mulVec]
    exact hM _ (hy z hz)
  · rw [Matrix.mul_add]; exact add_mem ha hb

theorem mul_mem_hatMx {m n : ℕ} (N : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E))
    (M : Matrix (Fin m) (Fin m) D.host.E) (hM : ∀ x ∈ N, M * x ∈ N) {u : Mx D m n} (hu : u ∈ hatMx N) :
    rat M * u ∈ hatMx N := by
  induction hu using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨α, hα, M * x, hM x hx, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i k) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

end GlobalTheory.TgtCoreSplit

open GlobalTheory.TgtCoreSplit in

theorem GlobalTheory.AscFin.latRow_bessel_core_split : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ w : WO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)), (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latRow G (2 * ρ + 1) → (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 ⬝ w)) ∈ latRow G (2 * ρ + 1) := by
  intro D hD T L μ0 hL sc G W M hM F hF ρ h w hw
  have hI := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W M hM F hF
  have hm : ∀ v, MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v :=
    fun v => ((hI.2.1 ρ h).2.1 v).2
  have hL1 : Submodule.IsLattice D.host.E (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (node_isV G hL (X := .grid (2 * ρ + 1) 0) ⟨by omega, Nat.zero_le _⟩).sd.1
  have hL0 : Submodule.IsLattice D.host.E (G.Λ (.core (2 * ρ + 1))) :=
    (node_isV G hL (X := .core (2 * ρ + 1)) (show 2 * ρ + 1 ≤ D.R.m by omega)).sd.1
  have hP : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) *ᵥ t ∈ G.Λ (.grid (2 * ρ + 1) 0) :=
    fun t ht => proj_mem _ hL1 hL0 hm ht
  have e : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 * w)) =
      rat ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) * (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, rat_mul]
    show (F.dJ ρ h).j0 * ((F.dJ ρ h).p0 * w) * (F.dB ρ h).p0 = (F.dJ ρ h).j0 * (F.dJ ρ h).p0 * (w * (F.dB ρ h).p0)
    simp only [Matrix.mul_assoc]
  have hw' : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latO (G.pS (.chi (2 * ρ + 1) 0 : Pair T)) (G.pT (.chi (2 * ρ + 1) 0 : Pair T)) (G.latS (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (G.latT (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (fun _ => True) ∧
      ∀ a : AE D, IsIdemSum a G.pl.W0 → a • (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ hatMx (G.modul • homLat (G.latS (.chi (2 * ρ + 1) 0 : Pair T)) (G.latT (.chi (2 * ρ + 1) 0 : Pair T))) := hw
  rw [e]
  show (rat ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) * (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ∈ latO (G.pS (.chi (2 * ρ + 1) 0 : Pair T)) (G.pT (.chi (2 * ρ + 1) 0 : Pair T)) (G.latS (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (G.latT (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (fun _ => True) ∧
      ∀ a : AE D, IsIdemSum a G.pl.W0 → a • (rat ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) * (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ∈ hatMx (G.modul • homLat (G.latS (.chi (2 * ρ + 1) 0 : Pair T)) (G.latT (.chi (2 * ρ + 1) 0 : Pair T)))
  refine ⟨mul_mem_latO _ hP hw'.1, fun a ha => ?_⟩
  rw [← Matrix.mul_smul]
  exact mul_mem_hatMx _ _ (fun x hx => mul_mem_smul_homLat _ _ hP hx) (hw'.2 a ha)

end
