import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraStandardOpenIffPowSmulStatement
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

private theorem sm_image_congr {S S' E ι : Type} [CommRing S] [CommRing S'] [Algebra ℂ S] [Algebra ℂ S']
    [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E) (act' : S' →ₐ[ℂ] Module.End ℂ E)
    (M : Submodule ℂ E) (f : ι → S) (g : ι → S') (h : ∀ k, act (f k) = act' (g k)) (A : Set ι) :
    sm act M (f '' A) = sm act' M (g '' A) := by
  simp only [sm, iSup_image, h]

private theorem sm_range_congr {S S' E ι : Type} [CommRing S] [CommRing S'] [Algebra ℂ S] [Algebra ℂ S']
    [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E) (act' : S' →ₐ[ℂ] Module.End ℂ E)
    (M : Submodule ℂ E) (f : ι → S) (g : ι → S') (h : ∀ k, act (f k) = act' (g k)) :
    sm act M (Set.range f) = sm act' M (Set.range g) := by
  rw [← Set.image_univ, ← Set.image_univ]
  exact sm_image_congr act act' M f g h _

private theorem reg_congr {S S' E : Type} [CommRing S] [CommRing S'] [Algebra ℂ S] [Algebra ℂ S']
    [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E) (act' : S' →ₐ[ℂ] Module.End ℂ E)
    (M : Submodule ℂ E) {d : ℕ} (f : Fin d → S) (g : Fin d → S') (h : ∀ k, act (f k) = act' (g k))
    (hr : Reg act M f) : Reg act' M g := by
  intro k m hm hk
  rw [← sm_image_congr act act' M f g h, ← h k] at hk
  rw [← sm_image_congr act act' M f g h]
  exact hr k m hm hk

section SysLem
variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)

private theorem r_eq (i j : Fin (d + 1)) (l : Fin d) :
    T.r n11 T.mu i j (dj j l) = ((T.X (j.succAbove l) * (T.X i)⁻¹ : Sˣ) : S)
      - ((T.X j * (T.X i)⁻¹ : Sˣ) : S) * ((T.Y (j.succAbove l) * (T.Y j)⁻¹ : Sˣ) : S) := by
  have hY : (T.Y j : S) * ((T.Y j)⁻¹ : Sˣ) = 1 := Units.mul_inv _
  have hd : T.mu (dj j l) = (T.X (j.succAbove l) : S) * T.Y j - T.X j * T.Y (j.succAbove l) := rfl
  simp only [Sys.r, Sys.u, n11, hd, pow_one, mul_inv, Units.val_mul]
  linear_combination ((T.X (j.succAbove l) : S) * ((T.X i)⁻¹ : Sˣ)) * hY

private theorem r_mul (i j : Fin (d + 1)) (l : Fin d) :
    T.r n11 T.mu i j (dj j l) * ((T.X i * (T.X j)⁻¹ : Sˣ) : S) = T.r n11 T.mu j j (dj j l) := by
  have hX : (T.X i : S) * ((T.X i)⁻¹ : Sˣ) = 1 := Units.mul_inv _
  simp only [Sys.r, Sys.u, n11, pow_one, mul_inv, Units.val_mul]
  linear_combination (T.mu (dj j l) * ((T.Y j)⁻¹ : Sˣ) * ((T.X j)⁻¹ : Sˣ)) * hX

private theorem r_mem (hG : T.Good) {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J)
    (l : Fin d) : T.r n11 T.mu i j (dj j l) ∈ T.R I J := by
  rw [r_eq]
  exact sub_mem (hG.memX I J ⟨j, hj⟩ i hi _)
    (mul_mem (hG.memX I J ⟨j, hj⟩ i hi _) (hG.memY I J ⟨i, hi⟩ j hj _))

end SysLem

section Forms
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]

private theorem omB_le_fixed (B : Subalgebra ℂ K) (q : ℕ) {y : DR ℂ K} (hy : y ∈ omB ℂ K B q) :
    y ∈ ⋀[K]^q Ω[K⁄ℂ] := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, -, v, -, rfl⟩ := hz
    exact Submodule.smul_mem _ _ (ExteriorAlgebra.ιMulti_range K q ⟨_, rfl⟩)
  | zero => exact Submodule.zero_mem _
  | add a c _ _ ha hc => exact Submodule.add_mem _ ha hc
  | smul r a _ ha =>
    rw [← algebraMap_smul K r a]
    exact Submodule.smul_mem _ _ ha

private theorem actZ_tmul (u v : K) (y y' : DR ℂ K) :
    actZ K (u ⊗ₜ v) (y ⊗ₜ y') = (u • y) ⊗ₜ[ℂ] (v • y') := by
  simp only [actZ, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul]
  rfl

private theorem actF_tmul (u v : F) (y y' : DR ℂ K) :
    actF F (DR ℂ K) (DR ℂ K) (u ⊗ₜ v) (y ⊗ₜ y') = (u • y) ⊗ₜ[ℂ] (v • y') := by
  simp only [actF, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul]
  rfl

private theorem ctrF_eq (τ : DR ℂ K →ₗ[K] K) (ψ : DR ℂ K →ₗ[F] F) (A B : Submodule ℂ (DR ℂ K)) (w : DR ℂ K)
    (h : ∀ y ∈ A, ψ y = Algebra.trace F K (τ (y * w))) {m : DR ℂ K ⊗[ℂ] DR ℂ K}
    (hm : m ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) A B) :
    ctrF (DR ℂ K) ψ m = mulP F K (muP F K τ m w) := by
  have key : Submodule.map₂ (TensorProduct.mk ℂ (DR ℂ K) (DR ℂ K)) A B ≤
      LinearMap.eqLocus (ctrF (DR ℂ K) ψ) (mulP F K ∘ₗ (muP F K τ).flip w) := by
    refine Submodule.map₂_le.2 fun y hy y' _ => ?_
    simp [ctrF, muP, mulP, h y hy, algebraMap_smul]
  exact key hm

section Sz
variable {d : ℕ} (x : Fin (d + 1) → Fˣ)

private theorem xe (K : Type) [Field K] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (a : ℕ) (p j : Fin (d + 1)) :
    (((sysZ K x a).X p * ((sysZ K x a).X j)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      algebraMap F K ((x p : F) / x j) ⊗ₜ[ℂ] 1 := by
  have h : (sysZ K x a).X p * ((sysZ K x a).X j)⁻¹ =
      Units.map ((Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap F K) : F →+* K ⊗[ℂ] K) : F →* K ⊗[ℂ] K)
        (x p * (x j)⁻¹) := by
    simp only [map_mul, map_inv]
    rfl
  rw [h, div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul]
  rfl

private theorem ye (K : Type) [Field K] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (a : ℕ) (p j : Fin (d + 1)) :
    (((sysZ K x a).Y p * ((sysZ K x a).Y j)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      1 ⊗ₜ[ℂ] algebraMap F K ((x p : F) / x j) := by
  have h : (sysZ K x a).Y p * ((sysZ K x a).Y j)⁻¹ =
      Units.map (((Algebra.TensorProduct.includeRight : K →ₐ[ℂ] K ⊗[ℂ] K).toRingHom.comp (algebraMap F K) : F →+* K ⊗[ℂ] K) :
        F →* K ⊗[ℂ] K) (x p * (x j)⁻¹) := by
    simp only [map_mul, map_inv]
    rfl
  rw [h, div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul]
  rfl

private theorem act_r_diag (a : ℕ) (j : Fin (d + 1)) (l : Fin d) :
    (sysZ K x a).act ((sysZ K x a).r n11 (sysZ K x a).mu j j (dj j l)) = actF F (DR ℂ K) (DR ℂ K) (f0 x j l) := by
  rw [r_eq, mul_inv_cancel, Units.val_one, one_mul, xe, ye]
  refine TensorProduct.ext' fun y y' => ?_
  change actZ K _ _ = _
  simp only [f0, map_sub, LinearMap.sub_apply, actZ_tmul, actF_tmul, one_smul, algebraMap_smul]

private theorem diag_case (hReg : RegLat) (hLat : LatOm) (hDual : DualForm) (hK1 : K1) (hGood : GoodZ)
    (hc : IsFinCover ℂ K (xv x)) (τ : DR ℂ K →ₗ[K] K) (hτ : IsTop ℂ K (xv x) τ) (a : ℕ) (ha : a ≤ d)
    (I J : Finset (Fin (d + 1))) (j : Fin (d + 1)) (hI : j ∈ I) (hJ : j ∈ J) :
    KE (kos (sysZ K x a).act ((sysZ K x a).M I J) fun l => (sysZ K x a).r n11 (sysZ K x a).mu j j (dj j l)) d ∧
    ∀ m ∈ (sysZ K x a).M I J, Acts (F := F) K τ a m 0 →
      m ∈ sm (sysZ K x a).act ((sysZ K x a).M I J)
        (Set.range fun l => (sysZ K x a).r n11 (sysZ K x a).mu j j (dj j l)) := by
  have hG := (hGood F K d x hc a).1
  obtain ⟨hR, hS⟩ := hReg F d x hc.pd (DR ℂ K) (DR ℂ K) I J _ _ (hLat F K d x hc (d - a) I ⟨j, hI⟩).1
    (hLat F K d x hc a J ⟨j, hJ⟩).1 j hI hJ
  have hact : ∀ l, actF F (DR ℂ K) (DR ℂ K) (f0 x j l) =
      (sysZ K x a).act ((sysZ K x a).r n11 (sysZ K x a).mu j j (dj j l)) := fun l => (act_r_diag x a j l).symm
  have hrm := fun l => r_mem (sysZ K x a) hG hI hJ l
  refine ⟨hK1 _ _ (sysZ K x a).act (Fin d) ((sysZ K x a).R I J) _ _ d _ (hG.stab I J ⟨j, hI⟩ ⟨j, hJ⟩) hrm
    (reg_congr _ _ _ _ _ hact hR) fun k => ⟨Pi.single k 1, fun l => ?_, ?_⟩, fun m hm h0 => ?_⟩
  · rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · simp [Pi.single_apply]
  · rw [← sm_range_congr _ _ _ _ _ hact]
    refine hS m hm fun ψ => ?_
    obtain ⟨⟨w, hw, hψ⟩, -⟩ := hDual F K d x hc τ hτ a ha ψ
    rw [ctrF_eq τ ψ _ _ w (fun y hy => hψ y (omB_le_fixed _ _ hy)) hm, h0 w hw, zero_smul]

private theorem loc_om (hc : IsFinCover ℂ K (xv x)) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I)
    (j : Fin (d + 1)) (q : ℕ) {y : DR ℂ K} (hy : y ∈ omB ℂ K (rB ℂ K (xv x) (insert j I)) q) :
    ∃ N : ℕ, (algebraMap F K ((x j : F) / x i)) ^ N • y ∈ omB ℂ K (rB ℂ K (xv x) I) q := by
  by_cases hj : j ∈ I
  · rw [Finset.insert_eq_of_mem hj] at hy
    exact ⟨0, by simpa using hy⟩
  · obtain ⟨N, hN⟩ := (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul ℂ F K d (xv x) hc (insert j I) i (Finset.mem_insert_of_mem hi) q y).1 hy
    refine ⟨N, (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul ℂ F K d (xv x) hc I i hi q _).2 ⟨N, ?_⟩⟩
    rw [Finset.prod_insert hj, map_mul, mul_pow] at hN
    rwa [smul_smul, mul_comm]

private theorem loc_M (a : ℕ) (hc : IsFinCover ℂ K (xv x)) (hG : (sysZ K x a).Good) {I J : Finset (Fin (d + 1))}
    {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) :
    ∀ m ∈ (sysZ K x a).M (insert j I) J, ∃ N : ℕ,
      (sysZ K x a).act ((((sysZ K x a).X j * ((sysZ K x a).X i)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) ^ N) m ∈ (sysZ K x a).M I J := by
  have hst : ∀ N : ℕ, ∀ m ∈ (sysZ K x a).M I J,
      (sysZ K x a).act ((((sysZ K x a).X j * ((sysZ K x a).X i)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) ^ N) m ∈ (sysZ K x a).M I J :=
    fun N m hm => hG.stab I J ⟨i, hi⟩ ⟨j, hj⟩ _ (pow_mem (hG.memX I J ⟨j, hj⟩ i hi j) N) m hm
  intro m hm
  have hm' : m ∈ Submodule.span ℂ (Set.image2 (fun y y' => TensorProduct.mk ℂ (DR ℂ K) (DR ℂ K) y y')
      (omB ℂ K (rB ℂ K (xv x) (insert j I)) (d - a) : Set (DR ℂ K)) (omB ℂ K (rB ℂ K (xv x) J) a : Set (DR ℂ K))) := by
    rw [← Submodule.map₂_eq_span_image2]
    exact hm
  clear hm
  induction hm' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, y', hy', rfl⟩ := hz
    obtain ⟨N, hN⟩ := loc_om x hc hi j (d - a) hy
    refine ⟨N, ?_⟩
    rw [xe, Algebra.TensorProduct.tmul_pow, one_pow]
    change actZ K _ (y ⊗ₜ y') ∈ _
    rw [actZ_tmul, one_smul]
    exact Submodule.apply_mem_map₂ _ hN hy'
  | zero => exact ⟨0, by simp⟩
  | add m₁ m₂ _ _ h₁ h₂ =>
    obtain ⟨N₁, h₁⟩ := h₁
    obtain ⟨N₂, h₂⟩ := h₂
    refine ⟨N₁ + N₂, ?_⟩
    rw [map_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [add_comm, pow_add, map_mul]
      exact hst N₂ _ h₁
    · rw [pow_add, map_mul]
      exact hst N₁ _ h₂
  | smul c m _ h =>
    obtain ⟨N, h⟩ := h
    refine ⟨N, ?_⟩
    rw [map_smul]
    exact Submodule.smul_mem _ c h

end Sz

end Forms

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.colZ_of :
    RegLat → LatOm → DualForm → K1 → LocD → GoodZ → ColZ := by
  intro hReg hLat hDual hK1 hLoc hGood F K _ _ _ _ _ _ d x hc τ hτ a ha I J i hi j hj
  by_cases hij : i = j
  · subst hij
    exact diag_case x hReg hLat hDual hK1 hGood hc τ hτ a ha I J i hi hj
  obtain ⟨l0, hl0⟩ := Fin.exists_succAbove_eq hij
  have hG := (hGood F K d x hc a).1
  have hD := diag_case x hReg hLat hDual hK1 hGood hc τ hτ a ha (insert j I) J j (Finset.mem_insert_self j I) hj
  have hIi : i ∈ insert j I := Finset.mem_insert_of_mem hi
  have hJn : J.Nonempty := ⟨j, hj⟩
  have hIn : I.Nonempty := ⟨i, hi⟩
  have hL := hLoc _ _ (sysZ K x a).act (Fin d) ((sysZ K x a).R I J) ((sysZ K x a).M I J)
    ((sysZ K x a).M (insert j I) J) (fun l => (sysZ K x a).r n11 (sysZ K x a).mu i j (dj j l))
    ((sysZ K x a).X i * ((sysZ K x a).X j)⁻¹)
    (((sysZ K x a).X j * ((sysZ K x a).X i)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K)
    (((sysZ K x a).Y i * ((sysZ K x a).Y j)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) l0 d
    (hG.stab I J hIn hJn) (fun l => r_mem _ hG hi hj l) (hG.memX I J hJn i hi j) (hG.memY I J hIn j hj i)
    (by
      have := r_eq (sysZ K x a) i j l0
      rw [hl0, mul_inv_cancel, Units.val_one] at this
      exact this)
    (hG.monoM I _ J J hIn hJn (Finset.subset_insert j I) subset_rfl) (loc_M x a hc hG hi hj)
    (fun m hm => ⟨hG.stab _ J ⟨i, hIi⟩ hJn _ (hG.memX _ J hJn j (Finset.mem_insert_self j I) i) m hm, by
      rw [mul_inv, inv_inv, mul_comm]
      exact hG.stab _ J ⟨i, hIi⟩ hJn _ (hG.memX _ J hJn i hIi j) m hm⟩)
  have hfun : (fun l => (sysZ K x a).r n11 (sysZ K x a).mu i j (dj j l) *
      (((sysZ K x a).X i * ((sysZ K x a).X j)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K)) =
      fun l => (sysZ K x a).r n11 (sysZ K x a).mu j j (dj j l) := funext fun l => r_mul _ i j l
  rw [hfun] at hL
  refine ⟨hL.1 hD.1, fun m hm h0 => hL.2 m hm (hD.2 m ?_ h0)⟩
  exact hG.monoM I _ J J hIn hJn (Finset.subset_insert j I) subset_rfl hm
