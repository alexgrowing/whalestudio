import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem fixLoc_key (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
    (e : B →ₐ[ℂ] ℂ) {d : ℕ} (g : Fin d → Fin d → L) (A : Matrix (Fin d) (Fin d) ℂ) (t r : Fin d → L)
    (hg : ∀ m l, Val B e (g m l) (A m l)) (hdet : (1 - A).det ≠ 0)
    (hr : ∀ a, r a = t a - ∑ l, g a l * t l) :
    ∃ N : Matrix (Fin d) (Fin d) L, (∀ a l, N a l ∈ loc B e) ∧ Val B e N.det (1 - A).det ∧
      (∀ a, r a = ∑ l, N a l * t l) ∧ ∀ l, InSp (loc B e) r (t l) := by
  obtain ⟨-, ⟨ev, hev⟩, -, hinv⟩ := hV L B e
  have hg' : ∀ m l, ∃ h : g m l ∈ loc B e, ev ⟨_, h⟩ = A m l := fun m l => (hev _ _).1 (hg m l)
  choose hmem hval using hg'
  let G : Matrix (Fin d) (Fin d) (loc B e) := fun m l => ⟨g m l, hmem m l⟩
  let N' : Matrix (Fin d) (Fin d) (loc B e) := 1 - G
  let ι : loc B e →+* L := (loc B e).val.toRingHom
  let ε : loc B e →+* ℂ := ev.toRingHom
  have hN'ε : ε.mapMatrix N' = 1 - A := by
    ext a l
    simp only [N', RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, map_sub]
    have h1 : ε ((1 : Matrix (Fin d) (Fin d) (loc B e)) a l) = (1 : Matrix (Fin d) (Fin d) ℂ) a l := by
      by_cases h : a = l
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    rw [h1]
    congr 1
    exact hval a l
  have hN : (ι.mapMatrix N').det = ι N'.det := (RingHom.map_det ι N').symm
  have hVal : Val B e (ι.mapMatrix N').det (1 - A).det := by
    rw [hN]
    refine (hev _ _).2 ⟨N'.det.2, ?_⟩
    have : ε N'.det = (1 - A).det := by rw [RingHom.map_det, hN'ε]
    exact this
  have hmul : ∀ a, r a = ∑ l, (ι.mapMatrix N') a l * t l := by
    intro a
    rw [hr a]
    have h2 : ∀ l, (ι.mapMatrix N') a l * t l = (if a = l then t l else 0) - g a l * t l := by
      intro l
      have h0 : (ι.mapMatrix N') a l = (if a = l then 1 else 0) - g a l := by
        show ι ((1 - G) a l) = _
        rw [Matrix.sub_apply, map_sub, Matrix.one_apply, apply_ite ι, map_one, map_zero]
        rfl
      rw [h0, sub_mul, ite_mul, one_mul, zero_mul]
    simp only [h2, Finset.sum_sub_distrib]
    simp
  refine ⟨ι.mapMatrix N', fun a l => (N' a l).2, hVal, hmul, fun l => ?_⟩
  obtain ⟨hv0, hvi⟩ := hinv _ _ hVal hdet
  refine ⟨fun a => ((ι.mapMatrix N').det)⁻¹ * (ι.mapMatrix N').adjugate l a, fun a => ?_, ?_⟩
  · refine (loc B e).mul_mem hvi ?_
    rw [← RingHom.map_adjugate]
    exact (N'.adjugate l a).2
  · have h3 : (ι.mapMatrix N').mulVec t = r := by
      ext a; rw [hmul a]; rfl
    have h4 : ((ι.mapMatrix N').adjugate).mulVec r = (ι.mapMatrix N').det • t := by
      rw [← h3, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h5 := congrFun h4 l
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h5
    simp only [mul_assoc]
    rw [← Finset.mul_sum, h5, inv_mul_cancel_left₀ hv0]

theorem UpperTheory.Gal.productCup_of_system.fixLoc_of :
    ValBasic → FixLoc := by
  intro hV F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY e he
  have htan := hY.tan e he
  choose g hgv hgs using htan
  refine fixLoc_key hV (rB ℂ K' (xv x) {0}) e.1 g (A e) (tt K' x) _ hgv (hY.det e he) fun a => ?_
  rw [← hgs a]
  have hd : ofLex (dj (0 : Fin (d + 1)) a) = (a.succ, 0) := by
    show (Fin.succAbove 0 a, (0 : Fin (d + 1))) = _
    rw [Fin.succAbove_zero]
  have hx0 : algebraMap F K' (x 0 : F) ≠ 0 := by simp
  have hy0 : j2 (algebraMap F K (x 0 : F)) ≠ 0 := by simp
  have hmu : (sysY x j2 d).mu (dj 0 a) = algebraMap F K' (x a.succ : F) * j2 (algebraMap F K (x 0 : F))
      - algebraMap F K' (x 0 : F) * j2 (algebraMap F K (x a.succ : F)) := by
    unfold Sys.mu
    rw [hd]
    rfl
  have hu : (((sysY x j2 d).u n11 0 0 (dj 0 a) : K'ˣ) : K') =
      algebraMap F K' (x 0 : F) * j2 (algebraMap F K (x 0 : F)) := by
    unfold Sys.u n11
    simp only [pow_one, Units.val_mul]
    rfl
  unfold Sys.r
  rw [Units.val_inv_eq_inv_val, hu, hmu]
  simp only [tt, map_div₀]
  field_simp
