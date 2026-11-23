import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.DvdOfCompl

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.L2.G.Model

section Gen

variable {S : Type} [Fintype S] [DecidableEq S]

theorem tr_bA_emb (K : Type) [CommRing K] {k n : ℕ} (g : S → Matrix (Fin k) (Fin k) K) (s : S)
    (F : MvPolynomial (Fin k × Fin n) K) : blockAct K g (blockEmb K s F) = blockEmb K s (rowAct K (g s) F) :=
  (blockActTensor K K S k n g).1 s F

theorem tr_prod_smul (K : Type) [CommRing K] {k n : ℕ} (c : S → K) (F : S → MvPolynomial (Fin k × Fin n) K) :
    (∏ s, c s) • ∏ s, blockEmb K s (F s) = ∏ s, blockEmb K s (c s • F s) := by
  rw [smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_smul, smul_eq_C_mul]

theorem tr_map_emb {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {k n : ℕ} (s : S)
    (P : MvPolynomial (Fin k × Fin n) R) : map f (blockEmb R s P) = blockEmb R' s (map f P) := by
  unfold blockEmb
  exact map_rename f _ P

theorem map_letter_substitution {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (m : ℕ) (vec : S → Bool)
    (P : MvPolynomial (S × Fin (m + 1)) R) : map f (Th0 R m vec P) = Th0 R' m vec (map f P) := by
  have key : (map f).comp (Th0 R m vec).toRingHom = (Th0 R' m vec).toRingHom.comp (map f) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Th0]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_X, Th0, aeval_X]
      rw [tr_map_emb, map_Nv]
  exact RingHom.congr_fun key P

theorem tr_rowAct_inv (K : Type) [Field K] {k n : ℕ} (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det)
    (x : MvPolynomial (Fin k × Fin n) K) : rowAct K g (rowAct K g⁻¹ x) = x := by
  have := congrArg (fun f => f x) (rowActMul K k n g g⁻¹)
  simp only [AlgHom.comp_apply] at this
  rw [this, Matrix.nonsing_inv_mul g hg, fl_rowAct_one]

theorem tr_multi_twist (K : Type) [Field K] (m : ℕ) (hm : 1 ≤ m) (vec : S → Bool) (d : S → ℕ)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hM : ∀ s, IsUnit (M s).det)
    (G : MvPolynomial (S × Fin (m + 1)) K) (hG : G ∈ Pol K (m + 1) d) :
    (∏ s, (M s).det ^ (letterWt m (d s) (vec s) (Fin.last m))) • blockAct K M (Th0 K m vec G) =
      Th0 K m vec (Lin (fun s => Aa (vec s) (M s)) G) := by
  unfold Formalism.MainNotions.G.Pol at hG
  rw [restrictSupport_eq_span] at hG
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, hμ, rfl⟩ := hx
    beta_reduce
    rw [mono_factor, map_prod, map_prod, map_prod, map_prod]
    simp only [Th0_emb, Lin_emb, tr_bA_emb]
    rw [tr_prod_smul]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [twist_theta K m hm (d s) (vec s) (M s) (hM s) _ (partS_Hd K d μ hμ s)]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, smul_add, hx, hy]
  | smul a x _ hx => simp only [map_smul]; rw [smul_comm, hx]

theorem tr_tens_int (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : S → Fin (m + 1) → ℤ)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : ∀ s, IsUnit (M s).det)
    (y : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf)
    (hy : y ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (lam s) (M s))) :
    ∃ R : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) O,
      (∏ s, (M s).det ^ (lam s (Fin.last m))) • blockAct Kf M y = map (algebraMap O Kf) R := by
  unfold tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    have h1 := fun s => (nablaLTwMem O Kf m (lam s) (M s) (hM s) (F s)).1 (hF s)
    choose G _ hG2 using h1
    refine ⟨∏ s, blockEmb O s (G s), ?_⟩
    rw [map_prod, map_prod]
    simp only [tr_bA_emb]
    rw [tr_prod_smul]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [tr_map_emb, ← hG2 s]
    rfl
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨R1, h1⟩ := hx
    obtain ⟨R2, h2⟩ := hy
    exact ⟨R1 + R2, by rw [map_add, smul_add, h1, h2, map_add]⟩
  | smul a x _ hx =>
    obtain ⟨R1, h1⟩ := hx
    refine ⟨a • R1, ?_⟩
    rw [fl_map_smul, ← h1, ← algebraMap_smul Kf a x, map_smul, smul_comm, algebraMap_smul]

theorem tr_tens_lift (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : S → Fin (m + 1) → ℤ)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : ∀ s, IsUnit (M s).det)
    (sO : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) O)
    (h : sO ∈ tensorLat O O (fun s => dualWeyl O (m + 1) (m + 1) (nuOf (lam s)))) :
    ∃ y ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (lam s) (M s)),
      (∏ s, (M s).det ^ (lam s (Fin.last m))) • blockAct Kf M y = map (algebraMap O Kf) sO := by
  unfold tensorLat at h
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨G, hG, rfl⟩ := hx
    have key : ∀ s, (M s).det ^ (lam s (Fin.last m)) • rowAct Kf (M s)
        (((M s).det ^ (lam s (Fin.last m)))⁻¹ • rowAct Kf (M s)⁻¹ (map (algebraMap O Kf) (G s))) =
        map (algebraMap O Kf) (G s) := by
      intro s
      rw [map_smul, smul_smul, mul_inv_cancel₀ (zpow_ne_zero _ (hM s).ne_zero), one_smul, tr_rowAct_inv _ _ (hM s)]
    refine ⟨∏ s, blockEmb Kf s (((M s).det ^ (lam s (Fin.last m)))⁻¹ •
      rowAct Kf (M s)⁻¹ (map (algebraMap O Kf) (G s))), ?_, ?_⟩
    · apply Submodule.subset_span
      refine ⟨_, fun s => ?_, rfl⟩
      rw [nablaLTwMem O Kf m (lam s) (M s) (hM s), key s]
      exact ⟨G s, hG s, rfl⟩
    · rw [map_prod, map_prod]
      simp only [tr_bA_emb]
      rw [tr_prod_smul]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [tr_map_emb, key s]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨y1, m1, h1⟩ := hx
    obtain ⟨y2, m2, h2⟩ := hy
    exact ⟨y1 + y2, Submodule.add_mem _ m1 m2, by rw [map_add, smul_add, h1, h2, map_add]⟩
  | smul a x _ hx =>
    obtain ⟨y1, m1, h1⟩ := hx
    refine ⟨a • y1, Submodule.smul_mem _ _ m1, ?_⟩
    rw [fl_map_smul, ← h1, ← algebraMap_smul Kf a y1, map_smul, smul_comm, algebraMap_smul]

theorem tr_tens_le (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : S → Fin (m + 1) → ℤ)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : ∀ s, IsUnit (M s).det)
    (y : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf)
    (hy : y ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (lam s) (M s))) :
    y ∈ tensorLat Kf Kf (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lam s))) := by
  unfold tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨F, fun s => ?_, rfl⟩
    obtain ⟨x, hx, hxF⟩ := hF s
    rw [← hxF]
    exact Submodule.smul_mem _ _ (nablaLLe O Kf (m + 1) (m + 1) _ (M s) (hM s) x hx)
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul Kf a x]
    exact Submodule.smul_mem _ _ hx

end Gen

end Formalism.MainNotions.TestSideCounting
