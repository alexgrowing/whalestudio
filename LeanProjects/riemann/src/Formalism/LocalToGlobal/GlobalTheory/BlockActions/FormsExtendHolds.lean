import Formalism.LocalToGlobal.GlobalTheory.BlockActions.StabFunGen

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section GenB

def blkDg {K : Type} [Zero K] [One K] {n N : ℕ} (_hN : n + 1 = N) (M : Matrix (Fin n) (Fin n) K) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun x y => if h : (x : ℕ) < n ∧ (y : ℕ) < n then M ⟨x, h.1⟩ ⟨y, h.2⟩ else if (x : ℕ) = y then 1 else 0

variable {K : Type} {n : ℕ}

@[simp] theorem blkDg_cc [Zero K] [One K] (h : n + 1 = n + 1) (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    blkDg h M i.castSucc j.castSucc = M i j := by
  simp [blkDg]

@[simp] theorem blkDg_cl [Zero K] [One K] (h : n + 1 = n + 1) (M : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    blkDg h M i.castSucc (Fin.last n) = 0 := by
  simp [blkDg, i.is_lt.ne]

@[simp] theorem blkDg_lc [Zero K] [One K] (h : n + 1 = n + 1) (M : Matrix (Fin n) (Fin n) K) (j : Fin n) :
    blkDg h M (Fin.last n) j.castSucc = 0 := by
  simp [blkDg, j.is_lt.ne']

@[simp] theorem blkDg_ll [Zero K] [One K] (h : n + 1 = n + 1) (M : Matrix (Fin n) (Fin n) K) :
    blkDg h M (Fin.last n) (Fin.last n) = 1 := by
  simp [blkDg]

theorem blkDg_mul [CommRing K] {N : ℕ} (hN : n + 1 = N) (A B : Matrix (Fin n) (Fin n) K) :
    blkDg hN (A * B) = blkDg hN A * blkDg hN B := by
  subst hN
  ext x y
  refine Fin.lastCases ?_ (fun i => ?_) x <;> refine Fin.lastCases ?_ (fun j => ?_) y <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

theorem blkDg_one [CommRing K] {N : ℕ} (hN : n + 1 = N) : blkDg hN (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  subst hN
  ext x y
  refine Fin.lastCases ?_ (fun i => ?_) x <;> refine Fin.lastCases ?_ (fun j => ?_) y <;>
    simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem blk_conj_full [CommRing K] {N : ℕ} (hN : n + 1 = N) (gm Fm Fm' : Matrix (Fin N) (Fin N) K) (hFm : Fm' * Fm = 1)
    (A : Matrix (Fin N) (Fin n) K) (Fp gk M' : Matrix (Fin n) (Fin n) K) (hM' : Fp * M' = gk * Fp)
    (hgA : gm * A = A * gk) (w : Fin N → K) (hgw : gm *ᵥ w = w)
    (hF1 : ∀ x (b : Fin n) (b' : Fin N), (b : ℕ) = b' → Fm x b' = (A * Fp) x b)
    (hF2 : ∀ x (l : Fin N), (l : ℕ) + 1 = N → Fm x l = w x) :
    Fm' * gm * Fm = blkDg hN M' := by
  subst hN
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) K := blkDg rfl M' with hB
  have key : gm * Fm = Fm * B := by
    ext x y
    refine Fin.lastCases ?_ (fun y' => ?_) y
    · have e1 : (gm * Fm) x (Fin.last n) = w x := by
        rw [← congrFun hgw x, mul_apply]
        simp only [mulVec, dotProduct]
        exact Finset.sum_congr rfl (fun j _ => by rw [hF2 j (Fin.last n) (by simp)])
      rw [e1, mul_apply, Fin.sum_univ_castSucc]
      simp [hB, hF2 x (Fin.last n) (by simp)]
    · have eL : (gm * Fm) x y'.castSucc = (A * (Fp * M')) x y' := by
        rw [hM', ← Matrix.mul_assoc, ← hgA, Matrix.mul_assoc, mul_apply, mul_apply]
        exact Finset.sum_congr rfl (fun j _ => by rw [hF1 j y' y'.castSucc (by simp)])
      have eR : (Fm * B) x y'.castSucc = ((A * Fp) * M') x y' := by
        rw [mul_apply, Fin.sum_univ_castSucc, mul_apply]
        rw [hB, blkDg_lc, mul_zero, add_zero]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hF1 x j j.castSucc (by simp), blkDg_cc]
      rw [eL, eR, Matrix.mul_assoc]
  rw [Matrix.mul_assoc, key, ← Matrix.mul_assoc, hFm, Matrix.one_mul]

theorem redM_blkDg {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (hN : n + 1 = N)
    (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) : redM F v (blkDg hN M) = blkDg hN (redM F v M) := by
  funext x y
  by_cases h : (x : ℕ) < n ∧ (y : ℕ) < n
  · have e : blkDg hN (redM F v M) x y = redM F v M ⟨x, h.1⟩ ⟨y, h.2⟩ := by simp [blkDg, h]
    rw [e]
    exact redM_entry v _ _ _ _ _ _ (by simp [blkDg, h])
  · by_cases hxy : (x : ℕ) = y
    · have e1 : blkDg hN M x y = 1 := by simp only [blkDg, Matrix.of_apply, dif_neg h, if_pos hxy]
      have e2 : blkDg hN (redM F v M) x y = 1 := by simp only [blkDg, Matrix.of_apply, dif_neg h, if_pos hxy]
      have hm : blkDg hN M x y ∈ v.adicCompletionIntegers F := by rw [e1]; exact one_mem _
      rw [e2]
      simp only [redM, dif_pos hm]
      have : (⟨blkDg hN M x y, hm⟩ : v.adicCompletionIntegers F) = 1 := Subtype.ext (by simpa using e1)
      rw [this, map_one]
    · have e1 : blkDg hN M x y = 0 := by simp only [blkDg, Matrix.of_apply, dif_neg h, if_neg hxy]
      have e2 : blkDg hN (redM F v M) x y = 0 := by simp only [blkDg, Matrix.of_apply, dif_neg h, if_neg hxy]
      have hm : blkDg hN M x y ∈ v.adicCompletionIntegers F := by rw [e1]; exact zero_mem _
      rw [e2]
      simp only [redM, dif_pos hm]
      have : (⟨blkDg hN M x y, hm⟩ : v.adicCompletionIntegers F) = 0 := Subtype.ext (by simpa using e1)
      rw [this, map_zero]

theorem injsym_blk [Field K] {N k rS t : ℕ} (hN : n + 1 = N) (hr : rSym k rS ≤ n) (M : Matrix (Fin n) (Fin n) K)
    (h : InJSym k rS t false M) : InJSym k rS t true (blkDg hN M) := by
  subst hN
  obtain ⟨h1, h2, h3, -⟩ := h
  have hr' : k + rS < n := by unfold rSym at hr; omega
  refine ⟨fun x y hxy => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun _ x y hy => ?_⟩
  · induction x using Fin.lastCases with
    | last =>
      induction y using Fin.lastCases with
      | last => exact absurd hxy (lt_irrefl _)
      | cast j => exact blkDg_lc _ M j
    | cast i =>
      induction y using Fin.lastCases with
      | last => exact blkDg_cl _ M i
      | cast j => rw [blkDg_cc]; exact h1 i j (by simpa using hxy)
  · induction x using Fin.lastCases with
    | last => simp at hx; omega
    | cast i => rw [blkDg_cc]; exact h2 i (by simpa using hx)
  · induction x using Fin.lastCases with
    | last => simp at hx; omega
    | cast i =>
      induction y using Fin.lastCases with
      | last => simp at hy; omega
      | cast j => rw [blkDg_cc]; exact h3 i j (by simpa using hx) (by simpa using hy)
  · have hyl : y = Fin.last n := Fin.ext (by rw [Fin.val_last]; omega)
    subst hyl
    induction x using Fin.lastCases with
    | last => simp
    | cast i => simp [Fin.castSucc_ne_last]

theorem jsym_blk [Field K] {N k rS t : ℕ} (hN : n + 1 = N) (hr : rSym k rS ≤ n) (Mp : GL (Fin n) K)
    (hMp : Mp ∈ JSymG K n k rS t false) : ∃ Mm ∈ JSymG K N k rS t true, Mm.1 = blkDg hN Mp.1 := by
  refine ⟨⟨blkDg hN Mp.1, blkDg hN (Mp⁻¹ : GL (Fin n) K).1, ?_, ?_⟩, ⟨injsym_blk hN hr _ hMp.1, injsym_blk hN hr _ hMp.2⟩, rfl⟩
  · rw [← blkDg_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, blkDg_one]
  · rw [← blkDg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, blkDg_one]

theorem sum_blkDg {A : Type} [AddCommMonoid A] (f : Fin (n + 1) → Fin (n + 1) → A) (g : Fin n → Fin n → A)
    (h1 : ∀ i j, f i.castSucc j.castSucc = g i j) (h2 : ∀ i, f i (Fin.last n) = 0) (h3 : ∀ j, f (Fin.last n) j = 0) :
    ∑ x, ∑ y, f x y = ∑ i, ∑ j, g i j := by
  simp only [Fin.sum_univ_castSucc, h1, h2, h3, Finset.sum_const_zero, add_zero]

theorem lamSym_blk [Field K] {N : ℕ} (hN : n + 1 = N) (ψ : AddChar K ℂ) (χ : ℕ → MulChar K ℂ) (k rS t nb : ℕ)
    (hb : rSym k rS + nb * t ≤ n) (M : Matrix (Fin n) (Fin n) K) :
    lamSym ψ χ k rS t nb (blkDg hN M) = lamSym ψ χ k rS t nb M := by
  subst hN
  have hr : rSym k rS ≤ n := le_trans (Nat.le_add_right _ _) hb
  unfold lamSym lamJ
  have hsum := sum_blkDg (fun x y : Fin (n + 1) => if (x : ℕ) + 1 = y ∧ (y : ℕ) < rSym k rS ∧ (y : ℕ) ≠ k then
      blkDg rfl M x y else 0)
    (fun x y : Fin n => if (x : ℕ) + 1 = y ∧ (y : ℕ) < rSym k rS ∧ (y : ℕ) ≠ k then M x y else 0)
    (fun i j => by simp)
    (fun i => if_neg (fun hc => by
      have := hc.2.1
      simp only [Fin.val_last] at this
      omega))
    (fun j => by have := j.is_lt; simp; omega)
  rw [hsum]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have hit : i * t + t ≤ nb * t := by
    have := Nat.mul_le_mul_right t (Nat.succ_le_of_lt hi')
    rwa [Nat.succ_mul] at this
  have e : blkMat (rSym k rS) t i (blkDg rfl M) = blkMat (rSym k rS) t i M := by
    funext s s'
    have hs := s.is_lt
    have hs' := s'.is_lt
    have b1 : rSym k rS + i * t + s < n := by linarith
    have b2 : rSym k rS + i * t + s' < n := by linarith
    simp only [blkMat, entN, dif_pos (And.intro b1 b2), dif_pos (And.intro (Nat.lt_succ_of_lt b1) (Nat.lt_succ_of_lt b2))]
    simp [blkDg, b1, b2]
  rw [e]

end GenB

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem rSym_le_N (R : Ranks) : rSym R.k (rSD R) + R.m * R.t ≤ R.N R.m - 1 := by
  rw [rSym_rSD]
  have e : R.m * (R.t + 1) = R.m * R.t + R.m := by ring
  simp only [Ranks.r, Ranks.N, e]
  have := R.two_le_m
  omega

theorem rSym_le_N' (R : Ranks) : rSym R.k (rSD R) ≤ R.N R.m - 1 := le_trans (Nat.le_add_right _ _) (rSym_le_N R)

set_option maxHeartbeats 4000000 in

theorem extB_mat (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal) :
    Tf.gl.mat i v h (Tf.glevM.fr i v h) (bc (prV (E := D.host.E) v) G) =
      blkDg (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (Tf.gl.mat i v h (Tf.glevP.fr i v h) (bc (prV (E := D.host.E) v) κ.1)) := by
  obtain ⟨hEv1, hEv2⟩ := isExt_prV v hE
  obtain ⟨hF1, hF2⟩ := Tf.frExt i v h
  have hmatG : Tf.gl.mat i v h (Tf.glevM.fr i v h) (bc (prV (E := D.host.E) v) G) =
      ((Tf.glevM.fr i v h)⁻¹ : GL _ _).1 * (G.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h) * (Tf.glevM.fr i v h).1 := by
    simp only [GLoc.mat, Units.val_mul]; rfl
  have hmatK : Tf.gl.mat i v h (Tf.glevP.fr i v h) (bc (prV (E := D.host.E) v) κ.1) =
      ((Tf.glevP.fr i v h)⁻¹ : GL _ _).1 * (κ.1.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h) * (Tf.glevP.fr i v h).1 := by
    simp only [GLoc.mat, Units.val_mul]; rfl
  rw [hmatG, hmatK]
  exact blk_conj_full (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R)
    ((G.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h)) (Tf.glevM.fr i v h).1 ((Tf.glevM.fr i v h)⁻¹ : GL _ _).1
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
    ((iXm D).map ((Tf.gl.phi i v h).comp (inclE (F := D.host.F) (v.adicCompletion D.host.F))))
    (Tf.glevP.fr i v h).1 ((κ.1.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h))
    (((Tf.glevP.fr i v h)⁻¹ : GL _ _).1 * (κ.1.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h) * (Tf.glevP.fr i v h).1)
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

set_option maxHeartbeats 4000000 in

theorem extB_mem (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal) :
    bc (prV (E := D.host.E) v) G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Uloc v := by
  rw [Tf.glevM.mem i v h _ (extV_level Tf κ G hE v)]
  have hκv : bc (prV (E := D.host.E) v) κ.1 ∈ Tf.clsP.lev.Uloc v := ((Tf.clsP.lev.U_eq κ.1).1 κ.2).2 v
  obtain ⟨Mp, hMp, hMpeq⟩ := (Tf.glevP.mem i v h _ (Tf.clsP.lev.Uloc_lev v hκv)).1 hκv
  obtain ⟨Mm, hMm, hMmeq⟩ := jsym_blk (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (rSym_le_N' D.R) Mp hMp
  refine ⟨Mm, hMm, ?_⟩
  rw [hMmeq, extB_mat Tf κ G hE i v h, redM_blkDg, hMpeq]

set_option maxHeartbeats 4000000 in

theorem extB_chi (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (hG : G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U) :
    (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi ⟨G, hG⟩ : ℂˣ) : ℂ) = ((Tf.clsP.lev.chi κ : ℂˣ) : ℂ) := by
  rw [Tf.glevM.chi_eq, Tf.glevP.chi_eq]
  refine Finset.prod_congr rfl fun i _ => finprod_congr fun v => finprod_congr fun h => ?_
  congr 1
  rw [Tf.lamM_eq, Tf.eigenvalue_eq₂]
  have e1 := Tf.glevM.red_eq i v h ⟨G, hG⟩
  have e2 := Tf.glevP.red_eq i v h κ
  simp only at e1 e2
  rw [e1, e2, extB_mat Tf κ G hE i v h, redM_blkDg, lamSym_blk _ _ _ _ _ _ _ (rSym_le_N D.R)]

theorem extLoc (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) :
    bc (prV (E := D.host.E) v) G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Uloc v := by
  by_cases hv : v ∈ badG D
  · obtain ⟨i, hi⟩ : ∃ i : Fin 2, (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal := by
      rcases hv with h0 | h1
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
    exact extB_mem Tf κ G hE i v hi
  · by_cases hT : ((D.mem u).A.T : 𝓞 D.host.F) ∈ v.asIdeal
    · rw [(Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.UlocAlt v hT]
      exact Subgroup.mem_inf.mpr ⟨extV_level Tf κ G hE v, extV_fT Tf κ G hE v hT⟩
    · rw [(Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Uloc_hyp v hv hT]
      exact extV_level Tf κ G hE v

theorem extLevL_holds (Tf : FormsTiedSym D u Ch chOf) : ExtLevL Tf :=
  fun κ G hE _ => ⟨fun v => extLoc Tf κ G hE v, fun hG => extB_chi Tf κ G hE hG⟩

theorem forms_extend_holds : FormsCarriedToComplement :=
  forms_of_lattice_extension fun _ _ _ _ Tf => extLevL_holds Tf

end Formalism.L2.GlobalTheoryTheory.Br
