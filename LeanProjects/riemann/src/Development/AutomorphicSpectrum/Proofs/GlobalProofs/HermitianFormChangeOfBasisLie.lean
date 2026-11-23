import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CTFrameMatMulGram
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Proj

open GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice
open scoped GlobalTheory.MixModel

variable {D : D7} {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V} {m : ℕ}
  {X : Matrix (Fin V.rank) (Fin m) D.host.E} {T : Finset (Fin m)}

theorem prM_kills_colSpan
    (h : ∀ i ∈ upTo T, ∀ v' : V'.V, V.hT (V.frame.equivFun.symm fun j => X j i) (ι v') = 0)
    {z : Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ colSpan D.host.F X (upTo T)) :
    (adMat D.host.F (prM V V' ι)) *ᵥ z = 0 := by
  have hle : colSpan D.host.F X (upTo T) ≤ LinearMap.ker (adMat D.host.F (prM V V' ι)).mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have h0 : prM V V' ι *ᵥ (fun j => X j i) = 0 := prM_mulVec_eq_zero (h i hi)
    change (adMat D.host.F (prM V V' ι)) *ᵥ ((adMat D.host.F X)ᵀ i) = 0
    have h1 : (adMat D.host.F X)ᵀ i = fun j => inclR (F := D.host.F) (AF D.host.F) (X j i) := rfl
    rw [h1]
    funext k
    have h2 := congrArg (inclR (F := D.host.F) (AF D.host.F)) (congrFun h0 k)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at h2
    simpa [Matrix.mulVec, dotProduct] using h2
  exact hle hz

theorem frameMat_mem_colPerp
    (h : ∀ i ∈ upTo T, ∀ v' : V'.V, V.hT (V.frame.equivFun.symm fun j => X j i) (ι v') = 0)
    (y : Fin V'.rank → AF D.host.F ⊗[D.host.F] D.host.E) :
    (adMat D.host.F (frameMat V V' ι)) *ᵥ y ∈ colPerp D.sp.cm.sig V.gram X (upTo T) := by
  have h0 : ∀ i ∈ upTo T, ∀ l, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram * frameMat V V' ι) i l = 0 := by
    intro i hi l
    have h2 := h i hi (V'.frame l)
    rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord] at h2
    simp only [repr_symm] at h2
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_) h2
    simp only [Formalism.UG.cT, frameMat, LinearMap.toMatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
    rfl
  simp only [colPerp, Submodule.mem_iInf]
  intro i hi
  simp only [LinearMap.mem_ker, LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearMap.proj_apply]
  rw [Matrix.mulVec_mulVec]
  have e : adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram) * adMat D.host.F (frameMat V V' ι) =
      adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram * frameMat V V' ι) := Matrix.map_mul.symm
  rw [e]
  simp [Matrix.mulVec, dotProduct, h0 i hi]

theorem prM_unip_frameMat (hι : HSpace.IsIsomEmb V' V ι)
    (h : ∀ i ∈ upTo T, ∀ v' : V'.V, V.hT (V.frame.equivFun.symm fun j => X j i) (ι v') = 0)
    {a : GA D V} (ha : a ∈ unip D.sp.cm.sig V.gram X T) :
    adMat D.host.F (prM V V' ι) ⬝ (matHom V a).1 ⬝ adMat D.host.F (frameMat V V' ι) = 1 := by
  have hPI : adMat D.host.F (prM V V' ι) ⬝ adMat D.host.F (frameMat V V' ι) = 1 := by
    rw [← Matrix.map_mul, prM_mul_frameMat hι]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  refine Matrix.ext_of_mulVec_single fun j => ?_
  have h1 := ha.2.2 (adMat D.host.F (frameMat V V' ι) *ᵥ Pi.single j 1) (frameMat_mem_colPerp h _)
  have h2 := prM_kills_colSpan h h1
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec (Pi.single j 1) (adMat D.host.F (prM V V' ι)) (adMat D.host.F (frameMat V V' ι)),
    hPI, Matrix.one_mulVec, sub_eq_zero] at h2
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.one_mulVec]
  exact h2

theorem mt_eq_of_mem (hι : HSpace.IsIsomEmb V' V ι)
    (h : ∀ i ∈ upTo T, ∀ v' : V'.V, V.hT (V.frame.equivFun.symm fun j => X j i) (ι v') = 0)
    {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h) {v : GA D V} {u : GA D V'}
    (hvu : v * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T) :
    (matHom V' u).1 = adMat D.host.F (prM V V' ι) ⬝ (matHom V v).1 ⬝ adMat D.host.F (frameMat V V' ι) := by
  have hv : v = (v * (s u)⁻¹) * s u := by group
  have h1 : (matHom V v).1 = (matHom V (v * (s u)⁻¹)).1 * (matHom V (s u)).1 := by
    conv_lhs => rw [hv]
    exact congrArg Units.val (map_mul (matHom V) _ _)
  have h2 : (matHom V (s u)).1 ⬝ adMat D.host.F (frameMat V V' ι) = adMat D.host.F (frameMat V V' ι) ⬝ (matHom V' u).1 := (hs u).1
  rw [h1, Matrix.mul_assoc, Matrix.mul_assoc, h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    prM_unip_frameMat hι h hvu, Matrix.one_mul]

theorem exists_proj : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ (N : Subgroup (GA D V)) (N₁ : Subgroup (GA D V')), (∀ p ∈ N, ∀ a ∈ unip D.sp.cm.sig V.gram X T, p * a * p⁻¹ ∈ unip D.sp.cm.sig V.gram X T) → (∀ v ∈ N, ∃ u ∈ N₁, v * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T) → ∃ π : N →* N₁, Continuous π ∧ (∀ (v : N) (u : N₁), π v = u ↔ (v : GA D V) * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T) ∧ ∀ v : N, (v : GA D V) ∈ GQ V → (π v : GA D V') ∈ GQ V' := by
  intro D V m X Y hW T V' ι hι hr s hs N N₁ hN hcov
  have h : ∀ i ∈ upTo T, ∀ v' : V'.V, V.hT (V.frame.equivFun.symm fun j => X j i) (ι v') = 0 :=
    fun i hi v' => ((hr (ι v')).1 ⟨v', rfl⟩ i hi).1
  have uniq : ∀ (v : GA D V) (u u' : GA D V'), v * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T →
      v * (s u')⁻¹ ∈ unip D.sp.cm.sig V.gram X T → u = u' := fun v u u' h1 h2 =>
    GlobalTheory.MixModel.mt_injective V' ((mt_eq_of_mem hι h hs h1).trans (mt_eq_of_mem hι h hs h2).symm)
  choose f hf1 hf2 using hcov
  let π : N →* N₁ := MonoidHom.mk' (fun v => ⟨f v.1 v.2, hf1 v.1 v.2⟩) fun a b => by
    apply Subtype.ext
    refine uniq (a.1 * b.1) _ _ (hf2 _ (a * b).2) ?_
    have e : a.1 * b.1 * (s (f a.1 a.2 * f b.1 b.2))⁻¹ =
        (a.1 * (b.1 * (s (f b.1 b.2))⁻¹) * a.1⁻¹) * (a.1 * (s (f a.1 a.2))⁻¹) := by
      rw [map_mul]; group
    change a.1 * b.1 * (s (f a.1 a.2 * f b.1 b.2))⁻¹ ∈ unip D.sp.cm.sig V.gram X T
    rw [e]
    exact mul_mem (hN a.1 a.2 _ (hf2 _ b.2)) (hf2 _ a.2)
  have hmat : ∀ v : N, (matHom V' (π v : GA D V')).1 =
      adMat D.host.F (prM V V' ι) ⬝ (matHom V (v : GA D V)).1 ⬝ adMat D.host.F (frameMat V V' ι) := fun v =>
    mt_eq_of_mem hι h hs (hf2 v.1 v.2)
  refine ⟨π, ?_, fun v u => ⟨fun e => e ▸ hf2 v.1 v.2, fun e => Subtype.ext (uniq v.1 _ _ (hf2 v.1 v.2) e)⟩, ?_⟩
  · refine Continuous.subtype_mk (GlobalTheory.MixModel.continuous_of_mt V' ?_) _
    haveI := (ring_facts (F := D.host.F) (E := D.host.E)).1
    have hm : Continuous fun v : N => (matHom V (v : GA D V)).1 :=
      (GlobalTheory.MixModel.continuous_mt V).comp continuous_subtype_val
    exact ((continuous_const.matrix_mul hm).matrix_mul continuous_const).congr fun v => (hmat v).symm
  · intro v hv
    refine (GlobalTheory.MixModel.mem_GQ_iff V' _).2 ?_
    refine (congrArg (· ∈ GlobalTheory.MixModel.ratMx D V'.rank V'.rank) (hmat v)).mpr ?_
    exact GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem _) ((GlobalTheory.MixModel.mem_GQ_iff V _).1 hv))
      (GlobalTheory.MixModel.rat_mem _)

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Proj
end
