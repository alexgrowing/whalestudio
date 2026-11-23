import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CTFrameMatMulGram
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousConjBlockEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

open GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UEmb (hT_col)
open Formalism.UG (cT)

variable {D : D7} {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V}

theorem frameMat_mulVec (z : Fin V'.rank → D.host.E) :
    frameMat V V' ι *ᵥ z = ⇑(V.frame.repr (ι (V'.frame.equivFun.symm z))) := by
  have h := LinearMap.toMatrix_mulVec_repr V'.frame V.frame ι (V'.frame.equivFun.symm z)
  have hz : ⇑(V'.frame.repr (V'.frame.equivFun.symm z)) = z := funext fun i => repr_symm V' z i
  rw [hz] at h
  exact h

theorem symm_frameMat_mulVec (z : Fin V'.rank → D.host.E) :
    V.frame.equivFun.symm (frameMat V V' ι *ᵥ z) = ι (V'.frame.equivFun.symm z) := by
  rw [frameMat_mulVec]
  have h := V.frame.equivFun.symm_apply_apply (ι (V'.frame.equivFun.symm z))
  rwa [Module.Basis.equivFun_apply] at h

theorem hE_eq_hT (V : HSp D) (a b : Fin V.rank → D.host.E) :
    hE D.sp.cm.sig V.gram a b = V.hT (V.frame.equivFun.symm a) (V.frame.equivFun.symm b) := by
  rw [hT_frame]
  rfl

theorem frameMat_isom (hι : HSpace.IsIsomEmb V' V ι) :
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram * frameMat V V' ι = V'.gram := by
  rw [cT_frameMat_mul_gram, Matrix.mul_assoc, prM_mul_frameMat hι, Matrix.mul_one]

theorem pairing_submatrix (hι : HSpace.IsIsomEmb V' V ι) {m m' : ℕ} {e : Fin m' → Fin m}
    {A B : Matrix (Fin V.rank) (Fin m) D.host.E} {A' B' : Matrix (Fin V'.rank) (Fin m') D.host.E}
    (hA : frameMat V V' ι * A' = A.submatrix id e) (hB : frameMat V V' ι * B' = B.submatrix id e) :
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) A' * V'.gram * B' =
      (cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B).submatrix e e := by
  have hc : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι * A') =
      cT (D.sp.cm.sig : D.host.E →+* D.host.E) A' * cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) := by
    simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have h1 : cT (D.sp.cm.sig : D.host.E →+* D.host.E) A' * V'.gram * B' =
      cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι * A') * V.gram * (frameMat V V' ι * B') := by
    rw [← frameMat_isom hι, hc]
    simp only [Matrix.mul_assoc]
  rw [h1, hA, hB]
  ext i j
  simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply, id]

theorem exists_sliceFrame : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∃ (m' : ℕ) (e : Fin m' → Fin m) (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.IsSliceFrame V V' ι X Y T e X' Y' ∧ GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V'.gram X' Y' := by
  intro D V m X Y hW T V' ι hι hrange
  classical
  obtain ⟨hxx, hyy, hxy, hani⟩ := hW
  have hpair : ∀ {p q : ℕ} (A : Matrix (Fin V.rank) (Fin p) D.host.E)
      (B : Matrix (Fin V.rank) (Fin q) D.host.E) (k : Fin p) (i : Fin q),
      V.hT (V.frame.equivFun.symm fun j => A j k) (V.frame.equivFun.symm fun j => B j i) =
        (cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B) k i := by
    intro p q A B k i
    rw [hT_col V A (fun j => B j i) k]
    rfl
  have hne : ∀ i k, i ∉ upTo T → k ∈ upTo T → i ≠ k := by
    rintro i k hi hk rfl
    exact hi hk
  have hxmem : ∀ i, i ∉ upTo T → (V.frame.equivFun.symm fun j => X j i) ∈ LinearMap.range ι := by
    intro i hi
    rw [hrange]
    intro k hk
    constructor
    · rw [hpair X X k i, hxx, Matrix.zero_apply]
    · rw [← V.herm.eq (V.frame.equivFun.symm fun j => X j i) (V.frame.equivFun.symm fun j => Y j k),
        hpair X Y i k, hxy, Matrix.one_apply_ne (hne i k hi hk), map_zero]
  have hymem : ∀ i, i ∉ upTo T → (V.frame.equivFun.symm fun j => Y j i) ∈ LinearMap.range ι := by
    intro i hi
    rw [hrange]
    intro k hk
    constructor
    · rw [hpair X Y k i, hxy, Matrix.one_apply_ne (hne i k hi hk).symm]
    · rw [hpair Y Y k i, hyy, Matrix.zero_apply]
  set S : Finset (Fin m) := Finset.univ.filter (fun i => i ∉ upTo T) with hS
  have he_mono : StrictMono (fun k => S.orderEmbOfFin rfl k) := (S.orderEmbOfFin rfl).strictMono
  have he_range : ∀ i, i ∉ upTo T ↔ i ∈ Set.range (fun k => S.orderEmbOfFin rfl k) := by
    intro i
    have h : Set.range (fun k => S.orderEmbOfFin rfl k) = (S : Set (Fin m)) :=
      Finset.range_orderEmbOfFin S rfl
    rw [h, hS]
    simp
  have he_out : ∀ k, S.orderEmbOfFin rfl k ∉ upTo T := fun k => (he_range _).2 ⟨k, rfl⟩
  have hx' : ∀ k, ∃ w : V'.V, ι w = V.frame.equivFun.symm fun j => X j (S.orderEmbOfFin rfl k) :=
    fun k => LinearMap.mem_range.1 (hxmem _ (he_out k))
  have hy' : ∀ k, ∃ w : V'.V, ι w = V.frame.equivFun.symm fun j => Y j (S.orderEmbOfFin rfl k) :=
    fun k => LinearMap.mem_range.1 (hymem _ (he_out k))
  choose wx hwx using hx'
  choose wy hwy using hy'
  have hsym : ∀ w : V'.V, V'.frame.equivFun.symm (fun a => V'.frame.repr w a) = w := by
    intro w
    have h := V'.frame.equivFun.symm_apply_apply w
    rw [Module.Basis.equivFun_apply] at h
    exact h
  have hcol : ∀ (Z : Matrix (Fin V.rank) (Fin m) D.host.E) (w : Fin S.card → V'.V),
      (∀ k, ι (w k) = V.frame.equivFun.symm fun j => Z j (S.orderEmbOfFin rfl k)) →
      frameMat V V' ι * Matrix.of (fun a k => V'.frame.repr (w k) a) =
        Z.submatrix id (fun k => S.orderEmbOfFin rfl k) := by
    intro Z w hw
    ext a k
    have h := congrFun (frameMat_mulVec (V := V) (V' := V') (ι := ι)
      (fun b => V'.frame.repr (w k) b)) a
    rw [hsym (w k), hw k, repr_symm] at h
    exact h
  refine ⟨S.card, fun k => S.orderEmbOfFin rfl k, Matrix.of (fun a k => V'.frame.repr (wx k) a),
    Matrix.of (fun a k => V'.frame.repr (wy k) a), ?_, ?_⟩
  · exact And.intro he_mono (And.intro he_range (And.intro (hcol X wx hwx) (hcol Y wy hwy)))
  have hXX := pairing_submatrix hι (hcol X wx hwx) (hcol X wx hwx)
  have hYY := pairing_submatrix hι (hcol Y wy hwy) (hcol Y wy hwy)
  have hXY := pairing_submatrix hι (hcol X wx hwx) (hcol Y wy hwy)
  refine GlobalTheory.SiegelSet.IsWittFrame.mk ?_ ?_ ?_ ?_
  · rw [hXX, hxx]
    rfl
  · rw [hYY, hyy]
    rfl
  · rw [hXY, hxy]
    exact Matrix.submatrix_one _ he_mono.injective
  · intro z' h1 h2 h3
    have hz : frameMat V V' ι *ᵥ z' = 0 := by
      apply hani
      · funext i
        rw [← hT_col, symm_frameMat_mulVec]
        by_cases hi : i ∈ upTo T
        · exact ((hrange _).1 (LinearMap.mem_range_self ι _) i hi).1
        · obtain ⟨k, rfl⟩ := (he_range i).1 hi
          rw [← hwx k, hι (wx k) (V'.frame.equivFun.symm z'), ← hsym (wx k)]
          exact (hT_col V' (Matrix.of fun a k => V'.frame.repr (wx k) a) z' k).trans (congrFun h1 k)
      · funext i
        rw [← hT_col, symm_frameMat_mulVec]
        by_cases hi : i ∈ upTo T
        · exact ((hrange _).1 (LinearMap.mem_range_self ι _) i hi).2
        · obtain ⟨k, rfl⟩ := (he_range i).1 hi
          rw [← hwy k, hι (wy k) (V'.frame.equivFun.symm z'), ← hsym (wy k)]
          exact (hT_col V' (Matrix.of fun a k => V'.frame.repr (wy k) a) z' k).trans (congrFun h2 k)
      · rw [hE_eq_hT, symm_frameMat_mulVec,
          hι (V'.frame.equivFun.symm z') (V'.frame.equivFun.symm z'), ← hE_eq_hT V' z' z']
        exact h3
    have h := congrArg (fun w => prM V V' ι *ᵥ w) hz
    simp only [Matrix.mulVec_mulVec, prM_mul_frameMat hι, Matrix.one_mulVec, Matrix.mulVec_zero] at h
    exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice
end
