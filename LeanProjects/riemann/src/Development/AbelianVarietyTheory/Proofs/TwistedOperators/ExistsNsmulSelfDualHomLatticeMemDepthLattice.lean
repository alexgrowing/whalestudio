import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateHalfCommutantActsOnCosetVectorByScalar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.BigRow

theorem exists_nsmul_mem {K : Type} [Field K] [NumberField K] (I : FractionalIdeal (𝓞 K)⁰ K) {𝔪 : Ideal (𝓞 K)}
    (h𝔪 : 𝔪 ≠ ⊥) : ∃ N : ℕ, 0 < N ∧ ∀ a ∈ I, ∃ o ∈ 𝔪, (N : K) * a = algebraMap (𝓞 K) K o := by
  obtain ⟨d, hd, hI⟩ := I.isFractional
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hJ : Ideal.span {d} * 𝔪 ≠ ⊥ := mul_ne_zero (by simpa using hd0) h𝔪
  refine ⟨Ideal.absNorm (Ideal.span {d} * 𝔪), Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), fun a ha => ?_⟩
  obtain ⟨z, hz, hzd⟩ := Ideal.mem_span_singleton_mul.1 (Ideal.absNorm_mem (Ideal.span {d} * 𝔪))
  obtain ⟨b, hb⟩ := hI a ha
  refine ⟨z * b, 𝔪.mul_mem_right _ hz, ?_⟩
  rw [← map_natCast (algebraMap (𝓞 K) K), ← hzd, map_mul, map_mul, hb, Algebra.smul_def]
  ring

variable {D : D7}

theorem nsmul_tmul (N : ℕ) (α : AF D.host.F) (x : D.host.E) :
    (N • (α ⊗ₜ[D.host.F] x) : AE D) = α ⊗ₜ[D.host.F] ((N : D.host.E) * x) := by
  rw [← nsmul_eq_mul]
  exact (map_nsmul (TensorProduct.mk D.host.F (AF D.host.F) D.host.E α) N x).symm

theorem nsmul_mem_latO {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT LT' : Set (Fin T.rank → D.host.E)) (N : ℕ)
    (h : ∀ t ∈ LT, (N : D.host.E) • t ∈ LT') (x : WO S T) (hx : x ∈ latO S T LS LT fun _ => True) :
    N • x ∈ latO S T LS LT' fun _ => True := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, h0, a, ha, s, hs, _, h t ht, ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    rw [nsmul_tmul]
    congr 1
    ring
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem nsmul_mem_hatMx {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ}
    (h : ∀ a ∈ D.host.AA, ∃ o ∈ 𝔪, (N : D.host.E) * a = algebraMap (𝓞 D.host.E) D.host.E o)
    (x : WO S T) (hx : x ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) :
    N • x ∈ hatMx (𝔪 • homLat ΛS ΛT) := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hw
    obtain ⟨o, ho, hoa⟩ := h a ha
    refine AddSubgroup.subset_closure ⟨α, hα, _,
      Submodule.smul_mem_smul ho (GlobalTheory.RowLatChi.genMap_one_mem_homLat hS hs ht), ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, GlobalTheory.LatVac.genMap]
    rw [nsmul_tmul, Algebra.smul_def, ← hoa]
    congr 1
    ring
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem smul_mem_of_idLat {n : ℕ} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) {N : ℕ}
    (h : ∀ a ∈ I, ∃ o ∈ (⊤ : Ideal (𝓞 D.host.E)), (N : D.host.E) * a = algebraMap (𝓞 D.host.E) D.host.E o) :
    ∀ t ∈ idLat I Λ, (N : D.host.E) • t ∈ Λ := by
  intro t ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, y, hy, rfl⟩ := hx
    obtain ⟨o, -, ho⟩ := h s hs
    rw [smul_smul, ho, algebraMap_smul]
    exact Λ.smul_mem o hy
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul o x _ hx => rw [smul_comm]; exact Λ.smul_mem o hx

theorem exists_nsmul_latBig_mem_latRow : OnStd fun {D} _ _ {sc} {G} _ _ => ∀ i, i < D.R.m → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latBig G i, N • u ∈ latRow G i := by
  intro D hq T L μ0 hL sc G W M hM F hF i hi
  obtain ⟨N₁, hN₁, h₁⟩ := exists_nsmul_mem (shiftId G) (𝔪 := ⊤) top_ne_bot
  obtain ⟨N₂, hN₂, h₂⟩ := exists_nsmul_mem D.host.AA (𝔪 := G.modul) (G.pl.modul_ne_bot sc)
  have hsd := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  refine ⟨N₂ * N₁, Nat.mul_pos hN₂ hN₁, fun u hu => ?_⟩
  have k1 := nsmul_mem_latO _ _ (G.Λ (.grid i 0) : Set _) N₁ (smul_mem_of_idLat _ h₁) u hu
  have k2 : N₁ • u ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := GlobalTheory.RowLoc.mem_latO_negSp.2 k1
  rw [mul_smul]
  refine ⟨nsmul_mem k2 N₂, fun e he => ?_⟩
  have hprops := GlobalTheory.IdemSumIdeal.isIdemSum_props e G.pl.W0 (fun _ => 0) he
  exact GlobalTheory.CosScalar.smul_mem_hatMx hsd.1.1 hsd.2.1 G.modul hprops.1 hprops.2.1
    (nsmul_mem_hatMx hsd.1 h₂ _ k2)

end GlobalTheory.BigRow
