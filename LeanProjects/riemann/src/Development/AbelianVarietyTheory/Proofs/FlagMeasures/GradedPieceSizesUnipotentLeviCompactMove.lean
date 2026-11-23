import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsSatFlagOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagMeas.SizeMove

section LinAlg

variable {n : ℕ}

theorem detOn_nonneg (g : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : 0 ≤ detOn g W := by
  unfold detOn
  split_ifs
  · exact norm_nonneg _
  · exact le_rfl

theorem detOn_mul (g h : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ))
    (hg : ∀ y ∈ W, g *ᵥ y ∈ W) (hh : ∀ y ∈ W, h *ᵥ y ∈ W) :
    detOn (g * h) W = detOn g W * detOn h W := by
  have hg' : ∀ y ∈ W, Matrix.toLin' g y ∈ W := fun y hy => by
    rw [Matrix.toLin'_apply]; exact hg y hy
  have hh' : ∀ y ∈ W, Matrix.toLin' h y ∈ W := fun y hy => by
    rw [Matrix.toLin'_apply]; exact hh y hy
  have hgh : ∀ y ∈ W, Matrix.toLin' (g * h) y ∈ W := fun y hy => by
    rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]; exact hg _ (hh y hy)
  unfold detOn
  rw [dif_pos hgh, dif_pos hg', dif_pos hh', ← norm_mul, ← LinearMap.det_comp]
  congr 2
  refine LinearMap.ext fun y => Subtype.ext ?_
  simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec]

theorem detOn_unipotent (g : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ))
    (hg : ∀ y ∈ W, g *ᵥ y ∈ W) (r : ℕ) (hr : ∀ y ∈ W, ((Matrix.toLin' g - 1) ^ r) y = 0) :
    detOn g W = 1 := by
  have hg' : ∀ y ∈ W, Matrix.toLin' g y ∈ W := fun y hy => by
    rw [Matrix.toLin'_apply]; exact hg y hy
  unfold detOn
  rw [dif_pos hg']
  set f := (Matrix.toLin' g).restrict hg' with hf
  have key : ∀ k : ℕ, ∀ y : W,
      (((f - 1) ^ k) y : Fin n → ℂ) = ((Matrix.toLin' g - 1) ^ k) (y : Fin n → ℂ) := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      congr 1
  have hN : IsNilpotent (f - 1) := by
    refine ⟨r, LinearMap.ext fun y => Subtype.ext ?_⟩
    rw [key]
    simpa using hr y y.2
  have hc := hN.charpoly_eq_X_pow_finrank
  have he := LinearMap.eval_charpoly (f - 1) (-1)
  rw [hc] at he
  have h2 : algebraMap ℂ (Module.End ℂ W) (-1) - (f - 1) = (-1 : ℂ) • f := by
    rw [Algebra.algebraMap_eq_smul_one]; module
  rw [h2, LinearMap.det_smul] at he
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at he
  have h3 : LinearMap.det f = 1 := by
    have hne : ((-1 : ℂ) ^ Module.finrank ℂ W) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact mul_left_cancel₀ hne (he.symm.trans (mul_one _).symm)
  rw [h3, norm_one]

theorem flagN_nil {ε : Fin n → Bool} {a : ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    (h0 : W 0 = ⊥) (hm : Monotone W) {u : Formalism.REAL.UJ ε} (hu : u ∈ flagN ε W) (i : Fin (a + 1)) :
    (∀ y ∈ W i, uMat u *ᵥ y ∈ W i) ∧ ∀ y ∈ W i, ((Matrix.toLin' (uMat u) - 1) ^ (i : ℕ)) y = 0 := by
  have hstep : ∀ k : Fin a, ∀ y ∈ W k.succ, uMat u *ᵥ y - y ∈ W k.castSucc := hu.1
  have hstab : ∀ i : Fin (a + 1), ∀ y ∈ W i, uMat u *ᵥ y ∈ W i := by
    intro i y hy
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · rw [h0, Submodule.mem_bot] at hy ⊢
      simp [hy]
    · have h1 := hstep k y hy
      have h2 : W k.castSucc ≤ W k.succ := hm (Fin.castSucc_lt_succ (i := k)).le
      have h3 := Submodule.add_mem _ (h2 h1) hy
      simpa using h3
  refine ⟨hstab i, ?_⟩
  have hnil : ∀ m : ℕ, ∀ i : Fin (a + 1), (i : ℕ) = m → ∀ y ∈ W i,
      ((Matrix.toLin' (uMat u) - 1) ^ m) y = 0 := by
    intro m
    induction m with
    | zero =>
      intro i hi y hy
      have hi0 : i = 0 := Fin.ext hi
      subst hi0
      rw [h0, Submodule.mem_bot] at hy
      simp [hy]
    | succ m ih =>
      intro i hi y hy
      have hlt := i.isLt
      have hma : m < a := by omega
      have hik : i = (⟨m, hma⟩ : Fin a).succ := Fin.ext (by simp [hi])
      subst hik
      rw [pow_succ, Module.End.mul_apply]
      apply ih (⟨m, hma⟩ : Fin a).castSucc (by simp)
      simpa [Matrix.toLin'_apply] using hstep ⟨m, hma⟩ y hy
  exact hnil i i rfl

theorem gram_move {r : ℕ} (c : Fin r → Fin n → ℂ) (hc : LinearIndependent ℂ c)
    (g k : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit g.det) (hk : kᴴ * k = 1)
    (hW : ∀ y ∈ Submodule.span ℂ (Set.range c), g *ᵥ y ∈ Submodule.span ℂ (Set.range c)) :
    ‖(Matrix.of fun a b => star ((g * k)⁻¹ *ᵥ c a) ⬝ᵥ ((g * k)⁻¹ *ᵥ c b)).det‖ *
        detOn g (Submodule.span ℂ (Set.range c)) ^ 2 =
      ‖(Matrix.of fun a b => star (c a) ⬝ᵥ c b).det‖ := by
  set W := Submodule.span ℂ (Set.range c) with hWdef
  have hW' : ∀ y ∈ W, Matrix.toLin' g y ∈ W := fun y hy => by
    rw [Matrix.toLin'_apply]; exact hW y hy
  set f := (Matrix.toLin' g).restrict hW' with hf
  set b := Module.Basis.span hc with hb
  set A := LinearMap.toMatrix b b f with hA
  have hdetA : LinearMap.det f = A.det := (LinearMap.det_toMatrix b f).symm
  have hdetOn : detOn g W = ‖A.det‖ := by
    unfold detOn; rw [dif_pos hW', hdetA]
  set C : Matrix (Fin n) (Fin r) ℂ := Matrix.of fun i a => c a i with hC
  have hcol : ∀ a, g *ᵥ c a = ∑ i, A i a • c i := by
    intro a
    have h1 : f (b a) = ∑ i, A i a • b i := by
      rw [hA]; simp only [LinearMap.toMatrix_apply]; exact (b.sum_repr (f (b a))).symm
    have h2 := congrArg Subtype.val h1
    simpa [hf, hb, Module.Basis.span_apply, Matrix.toLin'_apply] using h2
  have hgC : g * C = C * A := by
    ext i a
    have h := congrFun (hcol a) i
    rw [Finset.sum_apply] at h
    simp only [Matrix.mul_apply, hC, Matrix.of_apply]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [h]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hCinj : ∀ z : Fin r → ℂ, C *ᵥ z = 0 → z = 0 := by
    intro z hz
    have h0 : ∑ a, z a • c a = 0 := by
      ext i
      have := congrFun hz i
      simpa [Matrix.mulVec, dotProduct, hC, mul_comm] using this
    exact funext (Fintype.linearIndependent_iff.1 hc z h0)
  have hAdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hz0
    apply hCinj
    have h1 : g *ᵥ (C *ᵥ z) = 0 := by
      rw [Matrix.mulVec_mulVec, hgC, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
    have h3 : C *ᵥ z = g⁻¹ *ᵥ (g *ᵥ (C *ᵥ z)) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hg, Matrix.one_mulVec]
    rw [h3, h1, Matrix.mulVec_zero]
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hAdet
  have hginvC : g⁻¹ * C = C * A⁻¹ := by
    calc g⁻¹ * C = g⁻¹ * C * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv _ hAu, Matrix.mul_one]
      _ = g⁻¹ * (C * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = g⁻¹ * (g * C) * A⁻¹ := by rw [hgC]
      _ = C * A⁻¹ := by rw [← Matrix.mul_assoc g⁻¹, Matrix.nonsing_inv_mul _ hg, Matrix.one_mul]
  have hgram : ∀ N : Matrix (Fin n) (Fin n) ℂ,
      (Matrix.of fun a b => star (N *ᵥ c a) ⬝ᵥ (N *ᵥ c b)) = (N * C)ᴴ * (N * C) := by
    intro N; ext a b
    simp [Matrix.mul_apply, hC, dotProduct, Matrix.conjTranspose_apply, Matrix.mulVec]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hkinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hk
  have hk1 : k * kᴴ = 1 := by
    rw [← hkinv]; exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse hk)
  have hG' : (Matrix.of fun a b => star ((g * k)⁻¹ *ᵥ c a) ⬝ᵥ ((g * k)⁻¹ *ᵥ c b)) =
      (A⁻¹)ᴴ * (Cᴴ * C) * A⁻¹ := by
    rw [hgram, Matrix.mul_inv_rev, hkinv, Matrix.mul_assoc, hginvC]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc k, hk1, Matrix.one_mul]
  have hG : (Matrix.of fun a b => star (c a) ⬝ᵥ c b) = Cᴴ * C := by simpa using hgram 1
  rw [hG', hG, hdetOn, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv']
  have hn : ‖A.det‖ ≠ 0 := norm_ne_zero_iff.2 hAdet
  rw [norm_mul, norm_mul, norm_star, norm_inv]
  field_simp

end LinAlg

variable (I : AutInst)

def crd (v : InfinitePlace I.F) (y : Fin I.n → I.E) : Fin I.n → ℂ := (I.P v)⁻¹ *ᵥ fun l => I.φ v (y l)

theorem norm_det_gram (x : I.GA) (w : InfinitePlace I.E) {r : ℕ} (e : Fin r → Fin I.n → I.E) :
    (Formalism.HN.gramPl (bas I) (frm I x) w e).det.re =
      ‖(Matrix.of fun a b =>
        star ((uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *ᵥ crd I (w.comap (algebraMap I.F I.E)) (e a)) ⬝ᵥ
          ((uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *ᵥ crd I (w.comap (algebraMap I.F I.E)) (e b))).det‖ := by
  set v := w.comap (algebraMap I.F I.E) with hv
  set U := uMat (x.1 v) with hU
  set G : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b =>
    star (U⁻¹ *ᵥ crd I v (e a)) ⬝ᵥ (U⁻¹ *ᵥ crd I v (e b)) with hG
  have hre : G.det.re = ‖G.det‖ := by
   open ComplexOrder in
   · have hpsd : G.PosSemidef := by
       have hGC : G = (Matrix.of fun i a => (U⁻¹ *ᵥ crd I v (e a)) i)ᴴ *
           (Matrix.of fun i a => (U⁻¹ *ᵥ crd I v (e a)) i) := by
         ext a b
         simp [hG, Matrix.mul_apply, dotProduct, Matrix.conjTranspose_apply]
       rw [hGC]
       exact Matrix.posSemidef_conjTranspose_mul_self _
     have h := Finset.prod_nonneg fun i (_ : i ∈ Finset.univ) => hpsd.eigenvalues_nonneg i
     obtain ⟨t, ht0, htz⟩ : ∃ t : ℝ, 0 ≤ t ∧ G.det = (t : ℂ) :=
       ⟨∏ i, hpsd.1.eigenvalues i, h, by rw [hpsd.1.det_eq_prod_eigenvalues]; simp⟩
     rw [htz, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg ht0]
  rw [← hre]
  have hvec : ∀ y : Fin I.n → I.E, Formalism.HermitianLatticesTheory.vecAt (bas I) w y = fun i => w.embedding (y i) := by
    intro y; ext i; simp [Formalism.HermitianLatticesTheory.vecAt]
  by_cases hw : w.embedding = I.φ v
  · have hfr : frm I x w = I.P v * U := by
      simp only [frm, hU, hv]; rw [if_pos hw]
    have hf : ∀ y, Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = U⁻¹ *ᵥ crd I v y := by
      intro y
      rw [Formalism.HermitianLatticesTheory.fcoord, hfr, hvec, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, crd, hw]
    congr 2
    ext a b
    simp [Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, hf, hG, dotProduct]
  · have hw2 : w.embedding = ComplexEmbedding.conjugate (I.φ v) :=
      (GlobalTheory.Count.Test.embedding_cases I w).resolve_left hw
    have hfr : frm I x w = (I.P v * U).map (starRingEnd ℂ) := by
      simp only [frm, hU, hv]; rw [if_neg hw]
    have hmap : ∀ A : Matrix (Fin I.n) (Fin I.n) ℂ, A.map (starRingEnd ℂ) = Aᴴᵀ := by
      intro A; ext i j; simp [Matrix.conjTranspose_apply]
    have hinv : ((I.P v * U).map (starRingEnd ℂ))⁻¹ = ((I.P v * U)⁻¹).map (starRingEnd ℂ) := by
      rw [hmap, hmap, ← Matrix.transpose_nonsing_inv, Matrix.conjTranspose_nonsing_inv]
    have hf : ∀ y, Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y =
        fun i => starRingEnd ℂ ((U⁻¹ *ᵥ crd I v y) i) := by
      intro y
      ext i
      rw [Formalism.HermitianLatticesTheory.fcoord, hfr, hinv, hvec, crd, Matrix.mulVec_mulVec, ← Matrix.mul_inv_rev,
        RingHom.map_mulVec]
      congr 1
      ext l
      simp [hw2, ComplexEmbedding.conjugate_coe_eq]
    have hgr : Formalism.HN.gramPl (bas I) (frm I x) w e = G.map (starRingEnd ℂ) := by
      ext a b
      simp [Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, hf, hG, dotProduct, map_sum]
    have hc := RingHom.map_det (starRingEnd ℂ) G
    rw [RingHom.mapMatrix_apply] at hc
    rw [hgr, ← hc]
    simp

private theorem crd_sum_smul' (v : InfinitePlace I.F) {r : ℕ} (e : Fin r → Fin I.n → I.E) (t : Fin r → I.E) :
    crd I v (∑ a, t a • e a) = ∑ a, I.φ v (t a) • crd I v (e a) := by
  have h : (fun l => I.φ v ((∑ a, t a • e a) l)) = ∑ a, I.φ v (t a) • fun l => I.φ v (e a l) := by
    ext l; simp [Finset.sum_apply, map_sum]
  simp only [crd]
  rw [h, Matrix.mulVec_sum]
  simp [Matrix.mulVec_smul]

private theorem linearIndependent_crd_of_linearIndependent (v : InfinitePlace I.F) {r : ℕ} (e : Fin r → Fin I.n → I.E)
    (he : LinearIndependent I.E e) : LinearIndependent ℂ (fun a => crd I v (e a)) := by
  set M : Matrix (Fin I.n) (Fin r) I.E := Matrix.of fun l a => e a l with hM
  have hinj : LinearMap.ker (Matrix.toLin' M) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro z hz
    have h0 : ∑ a, z a • e a = 0 := by
      ext l
      have := congrFun hz l
      simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, hM, mul_comm, Finset.sum_apply] using this
    exact funext (Fintype.linearIndependent_iff.1 he z h0)
  obtain ⟨h, hh⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  set N := LinearMap.toMatrix' h with hN
  have hNM : N * M = 1 := by
    have h1 : LinearMap.toMatrix' (h ∘ₗ Matrix.toLin' M) = 1 := by rw [hh, LinearMap.toMatrix'_id]
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at h1
  have hNM' : N.map (I.φ v) * M.map (I.φ v) = 1 := by
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Fintype.linearIndependent_iff]
  intro z hz
  have hM' : M.map (I.φ v) *ᵥ z = ∑ a, z a • fun l => I.φ v (e a l) := by
    ext l
    simp [Matrix.mulVec, dotProduct, hM, Finset.sum_apply, mul_comm]
  have h1 : (I.P v)⁻¹ *ᵥ (M.map (I.φ v) *ᵥ z) = 0 := by
    rw [hM', Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    exact hz
  have hPu : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have h2 : M.map (I.φ v) *ᵥ z = 0 := by
    have h3 : M.map (I.φ v) *ᵥ z = I.P v *ᵥ ((I.P v)⁻¹ *ᵥ (M.map (I.φ v) *ᵥ z)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]
    rw [h3, h1, Matrix.mulVec_zero]
  have h3 : z = N.map (I.φ v) *ᵥ (M.map (I.φ v) *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, hNM', Matrix.one_mulVec]
  intro a
  rw [h3, h2, Matrix.mulVec_zero]
  rfl

private theorem span_crd_eq_flagAt_of_spanning {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (i : Fin (a + 1))
    (v : InfinitePlace I.F) {r : ℕ} (e : Fin r → Fin I.n → I.E) (he : ∀ b, e b ∈ S i)
    (hsp : ∀ y ∈ S i, y ∈ Submodule.span I.E (Set.range e)) :
    Submodule.span ℂ (Set.range fun b => crd I v (e b)) = flagAt I S v i := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact Submodule.subset_span ⟨e b, he b, rfl⟩
  · simp only [flagAt]
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun I.E).1 (hsp y hy)
    change crd I v (∑ b, t b • e b) ∈ _
    rw [crd_sum_smul']
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem ht_move {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (i : Fin (a + 1))
    (hS : (S i).FG) (xf : I.Gf) (g k : I.Ginf)
    (hg : ∀ v, ∀ y ∈ flagAt I S v i, uMat (g v) *ᵥ y ∈ flagAt I S v i) (hk : ∀ v, k v ∈ maxK (I.ε v)) :
    Formalism.HN.ht (bas I) (frm I (g * k, xf)) (S i) * (∏ v, detOn (uMat (g v)) (flagAt I S v i)) ^ 2 =
      Formalism.HN.ht (bas I) (frm I (1, xf)) (S i) := by
  classical
  obtain ⟨s, hsS, hspan, hli⟩ := exists_linearIndependent I.E (S i : Set (Fin I.n → I.E))
  have hsfin : s.Finite := hli.setFinite
  haveI := hsfin.fintype
  set σ : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm with hσ
  set e : Fin (Fintype.card s) → Fin I.n → I.E := fun b => (σ b : Fin I.n → I.E) with he
  have hrange : Set.range e = s := by
    ext y
    constructor
    · rintro ⟨b, rfl⟩; exact (σ b).2
    · intro hy; exact ⟨σ.symm ⟨y, hy⟩, by simp [he]⟩
  have heli : LinearIndependent I.E e := hli.comp σ σ.injective
  have heS : ∀ b, e b ∈ S i := fun b => hsS (σ b).2
  have hsp : ∀ y ∈ S i, y ∈ Submodule.span I.E (Set.range e) := by
    intro y hy; rw [hrange, hspan]; exact Submodule.subset_span hy
  have hrk : Formalism.HN.rkK (S i) = Fintype.card s := by
    unfold Formalism.HN.rkK
    have h := finrank_span_eq_card heli
    rw [hrange] at h
    rw [← hspan, h, Fintype.card_fin]
  have hle : Submodule.span (𝓞 I.E) (Set.range e) ≤ S i := by
    rw [Submodule.span_le]; rintro _ ⟨b, rfl⟩; exact heS b
  have hTC : IsTotallyComplex I.E := (GlobalTheory.Count.FrameMajorant.frames_give_majorants I (1, xf)).1
  have key : ∀ x : I.GA, Formalism.HN.ht (bas I) (frm I x) (S i) *
      (((Submodule.span (𝓞 I.E) (Set.range e)).toAddSubgroup.relIndex (S i).toAddSubgroup : ℕ) : ℝ) =
        ∏ w, (Formalism.HN.gramPl (bas I) (frm I x) w e).det.re ∧
      0 < ∏ w, (Formalism.HN.gramPl (bas I) (frm I x) w e).det.re := by
    intro x
    have hu : ∀ w, IsUnit (frm I x w).det := fun w => GlobalTheory.Count.FrameMajorant.frm_unit I x w
    have h := Formalism.HN.htGram I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x) hu _ e heli
    have hp := (Formalism.HN.plLat I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x) hu
      (Submodule.span (𝓞 I.E) (Set.range e)) (Submodule.fg_span (Set.finite_range e))).2.2
    refine ⟨?_, ?_⟩
    · rw [← h.1]; exact h.2 (S i) hS hle hrk
    · rw [← h.1]; exact hp
  obtain ⟨k1, -⟩ := key (g * k, xf)
  obtain ⟨k2, hpos2⟩ := key (1, xf)
  have hidx0 : (((Submodule.span (𝓞 I.E) (Set.range e)).toAddSubgroup.relIndex (S i).toAddSubgroup : ℕ) : ℝ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at k2; rw [← k2] at hpos2; exact lt_irrefl _ hpos2
  have e1 : ∀ v, uMat ((g * k, xf).1 v) = uMat (g v) * uMat (k v) := fun v => rfl
  have e2 : ∀ v, uMat (((1 : I.Ginf), xf).1 v) = 1 := fun v => rfl
  have hplace : ∀ w : InfinitePlace I.E,
      (Formalism.HN.gramPl (bas I) (frm I (g * k, xf)) w e).det.re *
        detOn (uMat (g (w.comap (algebraMap I.F I.E)))) (flagAt I S (w.comap (algebraMap I.F I.E)) i) ^ 2 =
      (Formalism.HN.gramPl (bas I) (frm I (1, xf)) w e).det.re := by
    intro w
    rw [norm_det_gram I (g * k, xf) w e, norm_det_gram I (1, xf) w e, e1, e2, inv_one]
    simp only [Matrix.one_mulVec]
    have hfl := span_crd_eq_flagAt_of_spanning I S i (w.comap (algebraMap I.F I.E)) e heS hsp
    rw [← hfl]
    have hg1 : IsUnit (uMat (g (w.comap (algebraMap I.F I.E)))).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
    have hW : ∀ y ∈ Submodule.span ℂ (Set.range fun b => crd I (w.comap (algebraMap I.F I.E)) (e b)),
        uMat (g (w.comap (algebraMap I.F I.E))) *ᵥ y ∈
          Submodule.span ℂ (Set.range fun b => crd I (w.comap (algebraMap I.F I.E)) (e b)) := by
      rw [hfl]; exact hg _
    exact gram_move _ (linearIndependent_crd_of_linearIndependent I _ e heli) _ _ hg1 (hk _) hW
  have hbij := GlobalTheory.Count.FrameMajorant.comap_bijective I
  have hprod : (∏ w, (Formalism.HN.gramPl (bas I) (frm I (g * k, xf)) w e).det.re) *
      (∏ v, detOn (uMat (g v)) (flagAt I S v i)) ^ 2 =
      ∏ w, (Formalism.HN.gramPl (bas I) (frm I (1, xf)) w e).det.re := by
    rw [← Finset.prod_pow, ← Fintype.prod_bijective _ hbij
      (fun w => detOn (uMat (g (w.comap (algebraMap I.F I.E)))) (flagAt I S (w.comap (algebraMap I.F I.E)) i) ^ 2)
      (fun v => detOn (uMat (g v)) (flagAt I S v i) ^ 2) (fun w => rfl), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ => hplace w
  apply mul_right_cancel₀ hidx0
  rw [k2, ← hprod, ← k1]
  ring

private theorem detOn_pos_of_isUnit_det_of_mapsTo {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit g.det)
    (W : Submodule ℂ (Fin n → ℂ)) (hW : ∀ y ∈ W, g *ᵥ y ∈ W) : 0 < detOn g W := by
  have hW' : ∀ y ∈ W, Matrix.toLin' g y ∈ W := fun y hy => by rw [Matrix.toLin'_apply]; exact hW y hy
  unfold detOn
  rw [dif_pos hW']
  apply norm_pos_iff.2
  apply IsUnit.ne_zero
  apply (LinearMap.isUnit_iff_isUnit_det _).1
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  apply Subtype.ext
  have h1 : g *ᵥ (y : Fin n → ℂ) = 0 := by
    simpa [Matrix.toLin'_apply] using congrArg Subtype.val hy
  have h3 : (y : Fin n → ℂ) = g⁻¹ *ᵥ (g *ᵥ (y : Fin n → ℂ)) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hg, Matrix.one_mulVec]
  rw [h3, h1, Matrix.mulVec_zero]
  rfl

private theorem rpow_mul_sq_rpow_inv_pow_eq (f j : ℕ) (hf : (f : ℝ) ≠ 0) (hj : (j : ℝ) ≠ 0) (h0 q : ℝ) (hh : 0 ≤ h0)
    (hq : 0 ≤ q) :
    ((h0 * q ^ 2) ^ ((1 : ℝ) / (2 * (f : ℝ) * (j : ℝ)))) ^ f =
      (h0 ^ ((1 : ℝ) / (2 * (f : ℝ) * (j : ℝ)))) ^ f * q ^ ((1 : ℝ) / j) := by
  rw [Real.mul_rpow hh (by positivity), mul_pow]
  congr 1
  rw [← Real.rpow_natCast ((q ^ 2) ^ ((1 : ℝ) / (2 * (f : ℝ) * (j : ℝ)))), ← Real.rpow_mul (by positivity),
    ← Real.rpow_natCast q 2, ← Real.rpow_mul hq]
  congr 1
  push_cast
  field_simp

theorem size_move : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∀ u m k : I.Ginf, (∀ v, u v ∈ flagN (I.ε v) (flagAt I S v)) → (∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)) → (∀ v, k v ∈ maxK (I.ε v)) → ∀ i : Fin a, Formalism.HN.sizeQ (bas I) (frm I (u * m * k, xf)) (S i.succ) (S i.castSucc) ^ I.f = Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ I.f * ∏ v, locSize j (flagAt I S v) (uMat (m v)) i := by
  intro I xf a j hj S hsat u m k hu hm hk i
  unfold IsSatFlag at hsat
  obtain ⟨h0, hmono, hrk, hmem, -⟩ := hsat
  have hfgΛ : (lamX I (1, xf)).FG := (GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).2.1
  have hfg : ∀ l, (S l).FG := fun l => Submodule.FG.of_le hfgΛ fun y hy => ((hmem l y).1 hy).1
  have hX : ∀ x : I.GA, ∀ w, IsUnit (frm I x w).det := fun x w => GlobalTheory.Count.FrameMajorant.frm_unit I x w
  have hFM := GlobalTheory.Count.FrameMajorant.frames_give_majorants I (1, xf)
  have hTC : IsTotallyComplex I.E := hFM.1
  have hnPl : Formalism.HN.nPl I.E = I.f := hFM.2.1
  have hsatQ : ∀ x : I.GA, Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (S i.succ) (S i.castSucc) := by
    intro x
    have h := GlobalTheory.Count.PerpStep.sat_inf (bas I) (frm I x) (hX x) (S i.succ) (hfg _)
      (Submodule.span I.E (S i.castSucc : Set (Fin I.n → I.E)))
    convert h using 1
    ext y
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
    constructor
    · intro hy
      exact ⟨hmono (Fin.castSucc_lt_succ (i := i)).le hy, Submodule.subset_span hy⟩
    · rintro ⟨h1, h2⟩
      exact (hmem _ y).2 ⟨((hmem _ y).1 h1).1, h2⟩
  have hhtpos : ∀ x : I.GA, ∀ l, 0 < Formalism.HN.ht (bas I) (frm I x) (S l) := fun x l =>
    (Formalism.HN.plLat I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x) (hX x) (S l) (hfg l)).2.2
  have hhtQ : ∀ x : I.GA, Formalism.HN.htQ (bas I) (frm I x) (S i.succ) (S i.castSucc) =
      Formalism.HN.ht (bas I) (frm I x) (S i.succ) / Formalism.HN.ht (bas I) (frm I x) (S i.castSucc) := by
    intro x
    rw [GlobalTheory.Count.PerpStep.htQ_eq (bas I) (frm I x) (hX x) _ _ (hfg _) (hsatQ x),
      GlobalTheory.Count.PerpStep.ht_eq (bas I) (frm I x) (hX x) _ (hfg _),
      GlobalTheory.Count.PerpStep.ht_eq (bas I) (frm I x) (hX x) _ (hfg _), ← Real.exp_sub]
    congr 1
    ring
  have hflag0 : ∀ v, flagAt I S v 0 = ⊥ := by
    intro v
    simp [flagAt, h0]
    exact Matrix.mulVec_zero _
  have hmonoF : ∀ v, Monotone (flagAt I S v) := fun v l l' hll' =>
    Submodule.span_mono (Set.image_mono (hmono hll'))
  have hWm : ∀ v l, ∀ y ∈ flagAt I S v l, uMat (m v) *ᵥ y ∈ flagAt I S v l :=
    fun v l y hy => (hm v l y hy).1
  have hWu : ∀ v l, ∀ y ∈ flagAt I S v l, uMat (u v) *ᵥ y ∈ flagAt I S v l :=
    fun v l => (flagN_nil (hflag0 v) (hmonoF v) (hu v) l).1
  have hdu : ∀ v l, detOn (uMat (u v)) (flagAt I S v l) = 1 := fun v l =>
    detOn_unipotent _ _ (hWu v l) l (flagN_nil (hflag0 v) (hmonoF v) (hu v) l).2
  have hdet : ∀ v l, detOn (uMat ((u * m) v)) (flagAt I S v l) = detOn (uMat (m v)) (flagAt I S v l) := by
    intro v l
    rw [show uMat ((u * m) v) = uMat (u v) * uMat (m v) from rfl,
      detOn_mul _ _ _ (hWu v l) (hWm v l), hdu, one_mul]
  have hWum : ∀ v l, ∀ y ∈ flagAt I S v l, uMat ((u * m) v) *ᵥ y ∈ flagAt I S v l := by
    intro v l y hy
    rw [show uMat ((u * m) v) = uMat (u v) * uMat (m v) from rfl, ← Matrix.mulVec_mulVec]
    exact hWu v l _ (hWm v l y hy)
  have hmove : ∀ l, Formalism.HN.ht (bas I) (frm I (u * m * k, xf)) (S l) *
      (∏ v, detOn (uMat (m v)) (flagAt I S v l)) ^ 2 = Formalism.HN.ht (bas I) (frm I (1, xf)) (S l) := by
    intro l
    have h := ht_move I S l (hfg l) xf (u * m) k (fun v => hWum v l) hk
    simpa only [hdet] using h
  have hDpos : ∀ l, 0 < ∏ v, detOn (uMat (m v)) (flagAt I S v l) := fun l =>
    Finset.prod_pos fun v _ => detOn_pos_of_isUnit_det_of_mapsTo _ ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)) _ (hWm v l)
  have hls : ∏ v, locSize j (flagAt I S v) (uMat (m v)) i =
      ((∏ v, detOn (uMat (m v)) (flagAt I S v i.castSucc)) /
        ∏ v, detOn (uMat (m v)) (flagAt I S v i.succ)) ^ ((1 : ℝ) / j i) := by
    unfold locSize
    rw [Real.finsetProd_rpow _ _ (fun v _ => div_nonneg (detOn_nonneg _ _) (detOn_nonneg _ _)),
      Finset.prod_div_distrib, neg_div, Real.rpow_neg (div_nonneg (hDpos _).le (hDpos _).le),
      ← Real.inv_rpow (div_nonneg (hDpos _).le (hDpos _).le), inv_div]
  have hjr : ((Formalism.HN.rkK (S i.succ) : ℝ) - Formalism.HN.rkK (S i.castSucc)) = (j i : ℝ) := by
    rw [hrk i]; push_cast; ring
  have hsz : ∀ x : I.GA, Formalism.HN.sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) =
      Formalism.HN.htQ (bas I) (frm I x) (S i.succ) (S i.castSucc) ^ ((1 : ℝ) / (2 * (I.f : ℝ) * (j i : ℝ))) := by
    intro x
    unfold Formalism.HN.sizeQ
    rw [hnPl, hjr]
  have hQ1 : Formalism.HN.htQ (bas I) (frm I (u * m * k, xf)) (S i.succ) (S i.castSucc) =
      Formalism.HN.htQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) *
        ((∏ v, detOn (uMat (m v)) (flagAt I S v i.castSucc)) /
          ∏ v, detOn (uMat (m v)) (flagAt I S v i.succ)) ^ 2 := by
    rw [hhtQ, hhtQ, ← hmove i.succ, ← hmove i.castSucc]
    have h1 := hhtpos (u * m * k, xf) i.succ
    have h2 := hhtpos (u * m * k, xf) i.castSucc
    have h3 := hDpos i.succ
    have h4 := hDpos i.castSucc
    field_simp
  have hf0 : (I.f : ℝ) ≠ 0 := by
    rw [← hnPl]; unfold Formalism.HN.nPl; exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hj0 : (j i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hj i; omega)
  rw [hsz, hsz, hQ1, hls]
  apply rpow_mul_sq_rpow_inv_pow_eq _ _ hf0 hj0
  · rw [hhtQ]; exact div_nonneg (hhtpos _ _).le (hhtpos _ _).le
  · exact div_nonneg (hDpos _).le (hDpos _).le

end GlobalTheory.FlagMeas.SizeMove
