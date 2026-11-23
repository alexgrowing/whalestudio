import Formalism.LocalToGlobal.GlobalTheory.BlockActions.CTExtUnitary

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

section Gen

theorem inJSym_restrict {κ : Type} [Field κ] {n : ℕ} {k rS t : ℕ} {zl : Bool} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) κ)
    (R : Matrix (Fin n) (Fin n) κ) (hR : ∀ x y, R x y = M x.castSucc y.castSucc) (h : InJSym k rS t zl M) :
    InJSym k rS t false R := by
  obtain ⟨h1, h2, h3, -⟩ := h
  refine ⟨fun x y hxy => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun h => absurd h Bool.false_ne_true⟩
  · rw [hR]; exact h1 _ _ (by simpa only [Fin.val_castSucc] using hxy)
  · rw [hR]; exact h2 _ (by simpa only [Fin.val_castSucc] using hx)
  · rw [hR]; exact h3 _ _ (by simpa only [Fin.val_castSucc] using hx) (by simpa only [Fin.val_castSucc] using hy)

theorem jsym_of_blk {κ : Type} [Field κ] {n N : ℕ} (hN : n + 1 = N) {k rS t : ℕ} (Mm : GL (Fin N) κ)
    (hMm : Mm ∈ JSymG κ N k rS t true) (R : Matrix (Fin n) (Fin n) κ)
    (hR : ∀ x y : Fin n, R x y = Mm.1 ⟨x, by omega⟩ ⟨y, by omega⟩) :
    ∃ M ∈ JSymG κ n k rS t false, M.1 = R := by
  subst hN
  obtain ⟨h1, h2⟩ := hMm
  have hRc : ∀ x y : Fin n, R x y = Mm.1 x.castSucc y.castSucc := fun x y => hR x y
  set R' : Matrix (Fin n) (Fin n) κ := fun x y => (Mm⁻¹ : GL (Fin (n + 1)) κ).1 x.castSucc y.castSucc with hR'
  have hl : ∀ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) κ), InJSym k rS t true M → ∀ x : Fin n,
      M x.castSucc (Fin.last n) = 0 := by
    intro M hM x
    have := (hM.2.2.2 rfl x.castSucc (Fin.last n) (by simp)).1
    simpa [Fin.castSucc_ne_last] using this
  have hmul : ∀ (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) κ), InJSym k rS t true A → ∀ x y : Fin n,
      (A * B) x.castSucc y.castSucc = ∑ j : Fin n, A x.castSucc j.castSucc * B j.castSucc y.castSucc := by
    intro A B hA x y
    rw [mul_apply, Fin.sum_univ_castSucc, hl A hA x, zero_mul, add_zero]
  have e1 : R * R' = 1 := by
    ext x y
    have := congrFun (congrFun (Mm.mul_inv) x.castSucc) y.castSucc
    rw [hmul _ _ h1] at this
    rw [mul_apply]
    simp only [hRc, hR']
    rw [this]
    simp [one_apply, Fin.castSucc_inj]
  have e2 : R' * R = 1 := by
    ext x y
    have := congrFun (congrFun (Mm.inv_mul) x.castSucc) y.castSucc
    rw [hmul _ _ h2] at this
    rw [mul_apply]
    simp only [hRc, hR']
    rw [this]
    simp [one_apply, Fin.castSucc_inj]
  refine ⟨⟨R, R', e1, e2⟩, ⟨?_, ?_⟩, rfl⟩
  · exact inJSym_restrict _ R hRc h1
  · exact inJSym_restrict _ R' (fun x y => rfl) h2

theorem blk_conj {K : Type} [CommRing K] {n N : ℕ} (hN : n + 1 = N) (gm Fm Fm' : Matrix (Fin N) (Fin N) K) (hFm : Fm' * Fm = 1)
    (A : Matrix (Fin N) (Fin n) K) (Fp gk M' : Matrix (Fin n) (Fin n) K) (hM' : Fp * M' = gk * Fp)
    (hgA : gm * A = A * gk) (w : Fin N → K) (hgw : gm *ᵥ w = w)
    (hF1 : ∀ x (b : Fin n) (b' : Fin N), (b : ℕ) = b' → Fm x b' = (A * Fp) x b)
    (hF2 : ∀ x (l : Fin N), (l : ℕ) + 1 = N → Fm x l = w x) :
    ∀ x y : Fin n, (Fm' * gm * Fm) ⟨x, by omega⟩ ⟨y, by omega⟩ = M' x y := by
  subst hN
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of (fun x y : Fin (n + 1) =>
    if h : (x : ℕ) < n ∧ (y : ℕ) < n then M' ⟨x, h.1⟩ ⟨y, h.2⟩ else if (x : ℕ) = y then 1 else 0) with hB
  have hne : ∀ j : Fin n, (j : ℕ) ≠ n := fun j => j.is_lt.ne
  have key : gm * Fm = Fm * B := by
    ext x y
    refine Fin.lastCases ?_ (fun y' => ?_) y
    · have e1 : (gm * Fm) x (Fin.last n) = w x := by
        rw [← congrFun hgw x, mul_apply]
        simp only [mulVec, dotProduct]
        exact Finset.sum_congr rfl (fun j _ => by rw [hF2 j (Fin.last n) (by simp)])
      rw [e1, mul_apply, Fin.sum_univ_castSucc]
      simp [hB, hne, hF2 x (Fin.last n) (by simp)]
    · have eL : (gm * Fm) x y'.castSucc = (A * (Fp * M')) x y' := by
        rw [hM', ← Matrix.mul_assoc, ← hgA, Matrix.mul_assoc, mul_apply, mul_apply]
        exact Finset.sum_congr rfl (fun j _ => by rw [hF1 j y' y'.castSucc (by simp)])
      have eR : (Fm * B) x y'.castSucc = ((A * Fp) * M') x y' := by
        rw [mul_apply, Fin.sum_univ_castSucc, mul_apply]
        have hlast : B (Fin.last n) y'.castSucc = 0 := by
          simp [hB, (hne y').symm]
        rw [hlast, mul_zero, add_zero]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hF1 x j j.castSucc (by simp)]
        simp [hB]
      rw [eL, eR, Matrix.mul_assoc]
  intro x y
  have e : Fm' * gm * Fm = B := by rw [Matrix.mul_assoc, key, ← Matrix.mul_assoc, hFm, Matrix.one_mul]
  rw [e]
  simp [hB]

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem redM_entry {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {m m' : ℕ}
    (X : Matrix (Fin m) (Fin m) (v.adicCompletion F)) (Y : Matrix (Fin m') (Fin m') (v.adicCompletion F))
    (a b : Fin m) (a' b' : Fin m') (h : X a b = Y a' b') : redM F v X a b = redM F v Y a' b' := by
  simp only [redM, h]
  by_cases hY : Y a' b' ∈ v.adicCompletionIntegers F
  · rw [dif_pos (by rw [h]; exact hY), dif_pos hY]
  · rw [dif_neg (by rw [h]; exact hY), dif_neg hY]

set_option maxHeartbeats 4000000 in

theorem lev_bad (Tf : FormsTiedSym D u Ch chOf) (K : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) K.1 G.1)
    (hG : G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hlev : bc (prV (E := D.host.E) v) K ∈ levelVL (sigD D) (gramP D) v Tf.clsP.lev.Lb)
    (i : Fin 2) (h : (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal) :
    bc (prV (E := D.host.E) v) K ∈ Tf.clsP.lev.Uloc v := by
  set Km := (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev
  rw [Tf.glevP.mem i v h _ hlev]
  have hGv : bc (prV (E := D.host.E) v) G ∈ Km.Uloc v := ((Km.U_eq G).1 hG).2 v
  obtain ⟨Mm, hMm, hMmeq⟩ := (Tf.glevM.mem i v h _ (Km.Uloc_lev v hGv)).1 hGv
  obtain ⟨hEv1, hEv2⟩ := isExt_prV v hE
  obtain ⟨hF1, hF2⟩ := Tf.frExt i v h
  have hmatG : Tf.gl.mat i v h (Tf.glevM.fr i v h) (bc (prV (E := D.host.E) v) G) =
      ((Tf.glevM.fr i v h)⁻¹ : GL _ _).1 * (G.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h) * (Tf.glevM.fr i v h).1 := by
    simp only [GLoc.mat, Units.val_mul]; rfl
  have hmatK : Tf.gl.mat i v h (Tf.glevP.fr i v h) (bc (prV (E := D.host.E) v) K) =
      ((Tf.glevP.fr i v h)⁻¹ : GL _ _).1 * (K.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h) * (Tf.glevP.fr i v h).1 := by
    simp only [GLoc.mat, Units.val_mul]; rfl
  have hb := blk_conj (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R)
    ((G.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h)) (Tf.glevM.fr i v h).1 ((Tf.glevM.fr i v h)⁻¹ : GL _ _).1
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
    ((iXm D).map ((Tf.gl.phi i v h).comp (inclE (F := D.host.F) (v.adicCompletion D.host.F))))
    (Tf.glevP.fr i v h).1 ((K.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h))
    (((Tf.glevP.fr i v h)⁻¹ : GL _ _).1 * (K.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h) * (Tf.glevP.fr i v h).1)
    (by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul])
    (by
      have := congrArg (fun M => M.map (Tf.gl.phi i v h)) hEv1
      simp only [Matrix.map_mul, Matrix.map_map] at this
      rw [RingHom.coe_comp]
      exact this)
    (fun a => Tf.gl.phi i v h (inclE (F := D.host.F) (v.adicCompletion D.host.F) (Tf.til.z0 a)))
    (by
      funext a
      exact (RingHom.map_mulVec (Tf.gl.phi i v h) _ _ a).symm.trans (congrArg (fun w => Tf.gl.phi i v h (w a)) hEv2))
    hF1 hF2
  refine jsym_of_blk (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) Mm hMm _ (fun x y => ?_)
  rw [hMmeq]
  refine redM_entry v _ _ _ _ _ _ ?_
  rw [hmatK, hmatG]
  exact (hb x y).symm

set_option maxHeartbeats 4000000 in

theorem lev_mem (Tf : FormsTiedSym D u Ch chOf) (K : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) K.1 G.1)
    (hG : G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U) : K ∈ Tf.clsP.lev.U := by
  have hU : K ∈ UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := lev_unit Tf K.1 G hE hG
  rw [Tf.clsP.lev.U_eq]
  refine ⟨hU, fun v => ?_⟩
  have hu := Formalism.UG.P.base_change_mem_holds _ _ _ (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (sigR (sigD D) (v.adicCompletion D.host.F)) (prV (E := D.host.E) v)
    (Formalism.UG.P.afsplit_prV_comp_sigR (sigD D) v) _ K hU
  have e : ((gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))).map (prV (E := D.host.E) v) =
      (gramP D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F)) := by
    rw [Matrix.map_map]; rfl
  rw [e] at hu
  have hlev : bc (prV (E := D.host.E) v) K ∈ levelVL (sigD D) (gramP D) v Tf.clsP.lev.Lb :=
    Subgroup.mem_inf.mpr ⟨hu, fun x => lev_lat Tf K.1 G hE hG v x⟩
  by_cases hv : v ∈ badG D
  · obtain ⟨i, hi⟩ : ∃ i : Fin 2, (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal := by
      rcases hv with h0 | h1
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
    exact lev_bad Tf K G hE hG v hlev i hi
  · have h1 : ((1 : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
      rw [Nat.cast_one]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    rw [Tf.clsP.lev.Uloc_hyp v hv h1]
    exact hlev

end Formalism.L2.GlobalTheoryTheory.Br
