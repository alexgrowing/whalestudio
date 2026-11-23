import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CTFrameMatMulGram
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Down

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev adV {n : ℕ} (v : Fin n → E) : Fin n → AF F ⊗[F] E := fun i => inclR (F := F) (AF F) (v i)

theorem adMat_mulVec {a c : ℕ} (M : Matrix (Fin a) (Fin c) E) (v : Fin c → E) :
    adMat F M *ᵥ adV (F := F) v = adV (F := F) (M *ᵥ v) :=
  funext fun i => (RingHom.map_mulVec (inclR (F := F) (AF F)) M v i).symm

theorem core (σ : E →ₐ[F] E) {n n' r r' : ℕ} {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin n') (Fin n') E}
    {X : Matrix (Fin n) (Fin r) E} {X' Y' : Matrix (Fin n') (Fin r') E} {T : Finset (Fin r)} {e : Fin r' → Fin r}
    {I : Matrix (Fin n) (Fin n') E} {P : Matrix (Fin n') (Fin n) E}
    (hmono : StrictMono e) (hrange : ∀ i, i ∉ upTo T ↔ i ∈ Set.range e)
    (hIX : I * X' = X.submatrix id e) (hPI : P * I = 1)
    (hg : Formalism.UG.cT (σ : E →+* E) I * J = J' * P)
    (hPl : ∀ l ∈ upTo T, P *ᵥ Xᵀ l = 0)
    (hperp : ∀ x, ∀ l ∈ upTo T, ((Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ (I *ᵥ x)) l = 0)
    (hW' : IsWittFrame σ J' X' Y') (k : Fin r') (g : GAd σ J) (b : GAd σ J')
    (hmat : (matHom _ σ J g).1 = 1 + adMat F I * ((matHom _ σ J' b).1 - 1) * adMat F P)
    (hgm : g ∈ unip σ J X (insert (e k) T)) : b ∈ unip σ J' X' {k} := by
  obtain ⟨M, hM⟩ : ∃ M, M = (matHom _ σ J' b).1 - 1 := ⟨_, rfl⟩
  rw [← hM] at hmat
  have hPI' : adMat F P * adMat F I = 1 := by
    rw [← Matrix.map_mul, hPI, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPIv : ∀ w, adMat F P *ᵥ (adMat F I *ᵥ w) = w := fun w => by rw [mulVec_mulVec, hPI', one_mulVec]
  have hGv : ∀ w, (matHom _ σ J g).1 *ᵥ (adMat F I *ᵥ w) - adMat F I *ᵥ w = adMat F I *ᵥ (M *ᵥ w) := fun w => by
    rw [hmat, Matrix.add_mulVec, one_mulVec, add_sub_cancel_left, ← Matrix.mulVec_mulVec, hPIv, ← Matrix.mulVec_mulVec]
  have hXe : ∀ i, (adMat F X)ᵀ (e i) = adMat F I *ᵥ (adMat F X')ᵀ i := fun i => by
    have h : adMat F I * adMat F X' = adMat F (X.submatrix id e) := by rw [← Matrix.map_mul, hIX]
    funext j
    exact (congrFun (congrFun h j) i).symm
  have hPX : ∀ l ∈ upTo T, adMat F P *ᵥ (adMat F X)ᵀ l = 0 := fun l hl => by
    change adMat F P *ᵥ adV (F := F) (Xᵀ l) = 0
    rw [adMat_mulVec, hPl l hl]
    funext i
    exact map_zero _
  have hPspan : ∀ (A : Set (Fin r)) (N : Submodule (AF F ⊗[F] E) (Fin n' → AF F ⊗[F] E)),
      (∀ i ∈ A, adMat F P *ᵥ (adMat F X)ᵀ i ∈ N) → ∀ y ∈ colSpan F X A, adMat F P *ᵥ y ∈ N := fun A N h y hy => by
    have h1 : colSpan F X A ≤ N.comap (adMat F P).mulVecLin :=
      Submodule.span_le.2 (by rintro _ ⟨i, hi, rfl⟩; exact h i hi)
    exact h1 hy
  have ha : ∀ i : Fin r', i ≤ k → M *ᵥ (adMat F X')ᵀ i = 0 := fun i hi => by
    have h1 := (Subgroup.mem_iInf.1 hgm.1 (e i)).2 ((adMat F X)ᵀ (e i)) (Submodule.subset_span ⟨e i, rfl, rfl⟩)
    rw [hXe, hGv] at h1
    have h2 := hPspan _ ⊥ (fun l hl => by
      obtain ⟨k', hk', hlk, hkj⟩ := hl
      rcases Finset.mem_insert.1 hk' with rfl | h
      · exact absurd hkj (not_lt.2 (hmono.monotone hi))
      · exact (Submodule.mem_bot _).2 (hPX l ⟨k', h, hlk⟩)) _ h1
    rw [hPIv] at h2
    exact (Submodule.mem_bot _).1 h2
  have hfix : M * adMat F (initCols X' k) = 0 := Matrix.ext_col fun i =>
    ha (i.castLE k.2) (Nat.le_of_lt_succ i.2)
  have c1 : ∀ {a c : ℕ} (Z : Matrix (Fin a) (Fin c) E), Formalism.UG.cT (sigR (AF F) σ) (adMat F Z) = adMat F (Formalism.UG.cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have fix : (matHom _ σ J' b).1 * adMat F (initCols X' k) = adMat F (initCols X' k) := by
    rw [hM, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hfix
    exact hfix
  rw [unip_singleton hW' k]
  apply Subgroup.subset_closure
  refine ⟨hM ▸ hfix, ?_, fun x hx => ?_⟩
  · have hu : Formalism.UG.cT (sigR (AF F) σ) (matHom _ σ J' b).1 * adMat F J' * (matHom _ σ J' b).1 = adMat F J' := b.2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, adMat, Matrix.map_mul]
    change adMat F _ * adMat F J' * _ = adMat F _ * adMat F J'
    conv_lhs => rw [← c1, ← fix, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (adMat F J'), hu, c1]
  · have h5 : Formalism.UG.cT (σ : E →+* E) (X.submatrix id e) * J * I = Formalism.UG.cT (σ : E →+* E) X' * J' := by
      rw [← hIX, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ J, hg, Matrix.mul_assoc, hPI,
        Matrix.mul_one]
    have hle : ∀ l, l ∉ upTo T → (∃ k' ∈ insert (e k) T, l ≤ k') → ∃ i, i ≤ k ∧ e i = l := fun l hl ⟨k', hk', hlk⟩ => by
      obtain ⟨i, rfl⟩ := (hrange l).1 hl
      rcases Finset.mem_insert.1 hk' with rfl | h
      · exact ⟨i, hmono.le_iff_le.1 hlk, rfl⟩
      · exact absurd ⟨k', h, hlk⟩ hl
    have hz : ∀ l, (∃ k' ∈ insert (e k) T, l ≤ k') → ((Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ (I *ᵥ x)) l = 0 := fun l hl => by
      by_cases h : l ∈ upTo T
      · exact hperp x l h
      · obtain ⟨i, hi, rfl⟩ := hle l h hl
        rw [mulVec_mulVec]
        have h6 : ((Formalism.UG.cT (σ : E →+* E) X * J * I) *ᵥ x) (e i) = ((Formalism.UG.cT (σ : E →+* E) (X.submatrix id e) * J * I) *ᵥ x) i := rfl
        rw [h6, h5]
        exact congrFun hx ⟨i.val, Nat.lt_succ_of_le hi⟩
    have hp : adV (F := F) (I *ᵥ x) ∈ colPerp σ J X {i | ∃ k' ∈ insert (e k) T, i ≤ k'} := by
      simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
      intro l hl
      change (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ adV (F := F) (I *ᵥ x)) l = 0
      rw [adMat_mulVec]
      change inclR (F := F) (AF F) _ = 0
      rw [hz l hl]
      exact map_zero _
    have h3 := hgm.2.2 _ hp
    rw [← adMat_mulVec, hGv] at h3
    have h4 := hPspan _ (colSpan F X' {i | i ≤ k}) (fun l hl => by
      by_cases h : l ∈ upTo T
      · rw [hPX l h]
        exact zero_mem _
      · obtain ⟨i, hi, rfl⟩ := hle l h hl
        rw [hXe, hPIv]
        exact Submodule.subset_span ⟨i, hi, rfl⟩) _ h3
    rw [hPIv] at h4
    obtain ⟨a, ha'⟩ := mem_colSpan_iff.1 h4
    exact ⟨a, by rw [← hM]; exact ha'.symm⟩

end Core

theorem mem_unip_of_image : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ (m' : ℕ) (e : Fin m' → Fin m) (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.IsSliceFrame V V' ι X Y T e X' Y' → GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V'.gram X' Y' → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ k : Fin m', ∀ b : GA D V', s b ∈ unip D.sp.cm.sig V.gram X (insert (e k) T) → b ∈ unip D.sp.cm.sig V'.gram X' {k} := by
  intro D V m X Y hW T V' ι hι hR m' e X' Y' hS hW' s hs k b hb
  obtain ⟨hmono, hrange, hIX, -⟩ := hS
  refine core D.sp.cm.sig hmono hrange hIX (prM_mul_frameMat hι) cT_frameMat_mul_gram (fun l hl => ?_) (fun x l hl => ?_)
    hW' k (s b) b (mat_eq hι hs b) hb
  · exact prM_mulVec_eq_zero fun v' => ((hR (ι v')).1 ⟨v', rfl⟩ l hl).1
  · have hv : ι (V'.frame.equivFun.symm x) = V.frame.equivFun.symm (frameMat V V' ι *ᵥ x) := by
      apply V.frame.equivFun.injective
      rw [LinearEquiv.apply_symm_apply]
      have h := LinearMap.toMatrix_mulVec_repr V'.frame V.frame ι (V'.frame.equivFun.symm x)
      have h' : V'.frame.repr (V'.frame.equivFun.symm x) = x := funext fun i => repr_symm V' x i
      rw [h'] at h
      exact h.symm
    have h := ((hR (ι (V'.frame.equivFun.symm x))).1 ⟨_, rfl⟩ l hl).1
    rw [hv, hT_frame] at h
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_) h
    rfl

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Down
end
