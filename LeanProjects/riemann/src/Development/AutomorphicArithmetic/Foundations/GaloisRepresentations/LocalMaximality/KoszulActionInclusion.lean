import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system.KoszulColumns

section Gen
variable {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E)

private lemma sm_image {ι : Type} (M : Submodule ℂ E) (f : ι → S) (A : Set ι) :
    sm act M (f '' A) = ⨆ k ∈ A, M.map (act (f k)) := by
  exact iSup_image (f := f) (g := fun r => M.map (act r))

private lemma sm_range {ι : Type} (M : Submodule ℂ E) (f : ι → S) :
    sm act M (Set.range f) = ⨆ k, M.map (act (f k)) := by
  exact iSup_range (f := f) (g := fun r => M.map (act r))

end Gen

section Sysx
variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)

private lemma r_formula (i j a : Fin (d + 1)) :
    T.r n11 T.mu i j (toLex (a, j)) =
      ((T.X a * (T.X i)⁻¹ : Sˣ) : S) - ((T.X j * (T.X i)⁻¹ : Sˣ) : S) * ((T.Y a * (T.Y j)⁻¹ : Sˣ) : S) := by
  have h : (T.Y j : S) * (((T.Y j)⁻¹ : Sˣ) : S) = 1 := Units.mul_inv _
  simp only [Sys.r, Sys.u, n11, Sys.mu, pow_one, mul_inv, Units.val_mul, ofLex_toLex]
  linear_combination ((T.X a : S) * (((T.X i)⁻¹ : Sˣ) : S)) * h

end Sysx

section Inst
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

variable (F K) in
private def i0 : F ⊗[ℂ] F →ₐ[ℂ] F ⊗[ℂ] K :=
  Algebra.TensorProduct.map (AlgHom.id ℂ F) (IsScalarTower.toAlgHom ℂ F K)

private lemma koszulAction_inclusion (a : ℕ) (s : F ⊗[ℂ] F) :
    (sysP K x a).act (i0 F K s) = actF F F (DR ℂ K) s := by
  have : ((sysP K x a).act).comp (i0 F K) = actF F F (DR ℂ K) := by
    apply Algebra.TensorProduct.ext'
    intro p q
    apply TensorProduct.ext'
    intro u w
    simp [sysP, i0, actF, Module.endTensorEndAlgHom_apply]
  exact DFunLike.congr_fun this s

private lemma ctrF_eq (ψ : F →ₗ[F] F) (m : F ⊗[ℂ] DR ℂ K) :
    ctrF (DR ℂ K) ψ m = ψ 1 • mulP F K m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | tmul f w =>
    have h1 : ψ f = f * ψ 1 := by
      have := ψ.map_smul f (1 : F)
      simpa using this
    simp only [ctrF, mulP, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
      AlgHom.toLinearMap_apply, Algebra.lsmul_coe, Algebra.linearMap_apply, LinearMap.restrictScalars_apply]
    rw [h1, algebraMap_smul, smul_smul, mul_comm]

end Inst

section Sysy
variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)

private lemma r_mem (hg : T.Good) {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J)
    (a : Fin (d + 1)) : T.r n11 T.mu i j (toLex (a, j)) ∈ T.R I J := by
  rw [r_formula]
  exact sub_mem (hg.memX I J ⟨j, hj⟩ i hi a)
    (mul_mem (hg.memX I J ⟨j, hj⟩ i hi j) (hg.memY I J ⟨i, hi⟩ j hj a))

private lemma r_mul_v (i j a : Fin (d + 1)) :
    T.r n11 T.mu i j (toLex (a, j)) * ((T.X i * (T.X j)⁻¹ : Sˣ) : S) = T.r n11 T.mu j j (toLex (a, j)) := by
  have h : (T.X i : S) * (((T.X i)⁻¹ : Sˣ) : S) = 1 := Units.mul_inv _
  rw [r_formula, r_formula]
  simp only [Units.val_mul]
  linear_combination ((T.X a : S) * (((T.X j)⁻¹ : Sˣ) : S) - (T.X j : S) * (((T.X j)⁻¹ : Sˣ) : S) *
    ((T.Y a : S) * (((T.Y j)⁻¹ : Sˣ) : S))) * h

private lemma koszulEntry_diagonal (i j : Fin (d + 1)) :
    T.r n11 T.mu i j (toLex (i, j)) =
      1 - ((T.X j * (T.X i)⁻¹ : Sˣ) : S) * ((T.Y i * (T.Y j)⁻¹ : Sˣ) : S) := by
  rw [r_formula]
  simp

end Sysy

section Main
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

private lemma r_jj (a : ℕ) (j : Fin (d + 1)) (l : Fin d) :
    (sysP K x a).r n11 (sysP K x a).mu j j (dj j l) = i0 F K (f0 x j l) := by
  have h : (dj j l) = toLex (j.succAbove l, j) := rfl
  rw [h, r_formula]
  simp [sysP, i0, f0, div_eq_mul_inv]

private lemma diag_case (hR : RegLat) (hO : LatOm) (hA : LatA) (hK : K1) (hc : IsFinCover ℂ K (xv x)) (a : ℕ)
    (hg : (sysP K x a).Good) (I J : Finset (Fin (d + 1))) (j : Fin (d + 1)) (hjI : j ∈ I) (hjJ : j ∈ J) :
    KE (kos (sysP K x a).act ((sysP K x a).M I J) fun l => (sysP K x a).r n11 (sysP K x a).mu j j (dj j l)) d ∧
    ∀ m ∈ (sysP K x a).M I J, mulP F K m = 0 →
      m ∈ sm (sysP K x a).act ((sysP K x a).M I J) (Set.range fun l => (sysP K x a).r n11 (sysP K x a).mu j j (dj j l)) := by
  have hL1 := (hA F d x hc.pd I j hjI).1
  have hL2 := (hO F K d x hc a J ⟨j, hjJ⟩).1
  obtain ⟨hreg, hker⟩ := hR F d x hc.pd F (DR ℂ K) I J _ _ hL1 hL2 j hjI hjJ
  have hact : ∀ l, (sysP K x a).act ((sysP K x a).r n11 (sysP K x a).mu j j (dj j l)) = actF F F (DR ℂ K) (f0 x j l) := by
    intro l
    rw [r_jj, koszulAction_inclusion]
  have e : ∀ A : Set (Fin d), sm (sysP K x a).act ((sysP K x a).M I J)
      ((fun l => (sysP K x a).r n11 (sysP K x a).mu j j (dj j l)) '' A) =
      sm (actF F F (DR ℂ K)) ((sysP K x a).M I J) (f0 x j '' A) := by
    intro A
    rw [sm_image, sm_image]
    simp only [hact]
  constructor
  · refine hK _ _ (sysP K x a).act (Fin d) ((sysP K x a).R I J) _ _ d
      (fun l => (sysP K x a).r n11 (sysP K x a).mu j j (dj j l)) (hg.stab I J ⟨j, hjI⟩ ⟨j, hjJ⟩) ?_ ?_ ?_
    · exact fun l => r_mem _ hg hjI hjJ _
    · intro k m hm h
      rw [e] at h ⊢
      rw [hact] at h
      exact hreg k m hm h
    · intro k
      refine ⟨Pi.single k 1, fun l => ?_, ?_⟩
      · by_cases h : l = k
        · subst h; simpa using one_mem _
        · simpa [Pi.single_apply, h] using zero_mem _
      · simp [Pi.single_apply]
  · intro m hm h0
    have e2 : sm (sysP K x a).act ((sysP K x a).M I J)
        (Set.range fun l => (sysP K x a).r n11 (sysP K x a).mu j j (dj j l)) =
        sm (actF F F (DR ℂ K)) ((sysP K x a).M I J) (Set.range (f0 x j)) := by
      rw [sm_range, sm_range]
      simp only [hact]
    rw [e2]
    exact hker m hm fun ψ => by rw [ctrF_eq, h0, smul_zero]

private lemma loc_step (hA : LatA) (hc : IsFinCover ℂ K (xv x)) (a : ℕ) (hg : (sysP K x a).Good)
    (I J : Finset (Fin (d + 1))) (i j : Fin (d + 1)) (hi : i ∈ I) (hj : j ∈ J) :
    ∀ m ∈ (sysP K x a).M (insert j I) J,
      ∃ N : ℕ, (sysP K x a).act ((((sysP K x a).X j * ((sysP K x a).X i)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) ^ N) m ∈
        (sysP K x a).M I J := by
  set aa : F ⊗[ℂ] K := (((sysP K x a).X j * ((sysP K x a).X i)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) with haa
  have hmem : aa ∈ (sysP K x a).R I J := hg.memX I J ⟨j, hj⟩ i hi j
  have hst := hg.stab I J ⟨i, hi⟩ ⟨j, hj⟩
  have hup : ∀ (N k : ℕ) (m : F ⊗[ℂ] DR ℂ K), (sysP K x a).act (aa ^ N) m ∈ (sysP K x a).M I J →
      (sysP K x a).act (aa ^ (N + k)) m ∈ (sysP K x a).M I J := by
    intro N k m h
    rw [add_comm, pow_add, map_mul]
    exact hst _ (pow_mem hmem k) _ h
  have hform : aa = ((x j : F) / x i) ⊗ₜ[ℂ] (1 : K) := by
    simp [haa, sysP, div_eq_mul_inv]
  let P : Submodule ℂ (F ⊗[ℂ] DR ℂ K) :=
    { carrier := {m | ∃ N : ℕ, (sysP K x a).act (aa ^ N) m ∈ (sysP K x a).M I J}
      add_mem' := by
        rintro m m' ⟨N, h⟩ ⟨N', h'⟩
        refine ⟨N + N', ?_⟩
        rw [map_add]
        refine add_mem (hup N N' m h) ?_
        rw [add_comm]
        exact hup N' N m' h'
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c m ⟨N, h⟩
        exact ⟨N, by rw [map_smul]; exact Submodule.smul_mem _ c h⟩ }
  have hle : (sysP K x a).M (insert j I) J ≤ P := by
    refine Submodule.map₂_le.2 fun y hy w hw => ?_
    obtain ⟨N, hN⟩ := (hA F d x hc.pd I i hi).2.2 j y hy
    refine ⟨N, ?_⟩
    have : (sysP K x a).act (aa ^ N) (y ⊗ₜ[ℂ] w) = ((((x j : F) / x i) ^ N * y) ⊗ₜ[ℂ] w) := by
      rw [hform, Algebra.TensorProduct.tmul_pow, one_pow]
      simp [sysP, Module.endTensorEndAlgHom_apply]
      rw [← map_pow]
      rfl
    change (sysP K x a).act (aa ^ N) (y ⊗ₜ[ℂ] w) ∈ _
    rw [this]
    exact Submodule.apply_mem_map₂ _ hN hw
  exact fun m hm => hle hm

end Main

end UpperTheory.Gal.productCup_of_system.KoszulColumns

theorem UpperTheory.Gal.productCup_of_system.colP_of :
    RegLat → LatOm → LatA → K1 → LocD → GoodZ → ColP := by
  intro hR hO hA hK hL hG F K _ _ _ _ _ _ d x hc a I J i hi j hj
  have hg : (sysP K x a).Good := (hG F K d x hc a).2.1
  by_cases hij : i = j
  · subst hij
    exact KoszulColumns.diag_case x hR hO hA hK hc a hg I J i hi hj
  · obtain ⟨l0, hl0⟩ := Fin.exists_succAbove_eq hij
    have Ine : I.Nonempty := ⟨i, hi⟩
    have Jne : J.Nonempty := ⟨j, hj⟩
    have hjI' : j ∈ insert j I := Finset.mem_insert_self j I
    have hiI' : i ∈ insert j I := Finset.mem_insert_of_mem hi
    have Ine' : (insert j I).Nonempty := ⟨j, hjI'⟩
    have D := KoszulColumns.diag_case x hR hO hA hK hc a hg (insert j I) J j hjI' hj
    have hle : (sysP K x a).M I J ≤ (sysP K x a).M (insert j I) J :=
      hg.monoM I (insert j I) J J Ine Jne (Finset.subset_insert j I) subset_rfl
    have hst' := hg.stab (insert j I) J Ine' Jne
    have LD := hL _ _ (sysP K x a).act (Fin d) ((sysP K x a).R I J) ((sysP K x a).M I J) ((sysP K x a).M (insert j I) J)
      (fun l => (sysP K x a).r n11 (sysP K x a).mu i j (dj j l)) ((sysP K x a).X i * ((sysP K x a).X j)⁻¹)
      (((sysP K x a).X j * ((sysP K x a).X i)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K)
      (((sysP K x a).Y i * ((sysP K x a).Y j)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) l0 d
      (hg.stab I J Ine Jne) (fun l => KoszulColumns.r_mem _ hg hi hj _) (hg.memX I J Jne i hi j) (hg.memY I J Ine j hj i)
      (by
        have h : dj j l0 = toLex (i, j) := by rw [← hl0]; rfl
        simp only [h]
        exact KoszulColumns.koszulEntry_diagonal _ i j)
      hle (KoszulColumns.loc_step x hA hc a hg I J i j hi hj)
      (fun m hm => ⟨hst' _ (hg.memX _ J Jne j hjI' i) m hm, by
        have : (((sysP K x a).X i * ((sysP K x a).X j)⁻¹)⁻¹ : (F ⊗[ℂ] K)ˣ) = (sysP K x a).X j * ((sysP K x a).X i)⁻¹ := by
          simp [mul_comm]
        rw [this]
        exact hst' _ (hg.memX _ J Jne i hiI' j) m hm⟩)
    have hrv : (fun l => (sysP K x a).r n11 (sysP K x a).mu i j (dj j l) *
        (((sysP K x a).X i * ((sysP K x a).X j)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K)) =
        fun l => (sysP K x a).r n11 (sysP K x a).mu j j (dj j l) := by
      funext l
      exact KoszulColumns.r_mul_v _ i j _
    rw [hrv] at LD
    exact ⟨LD.1 D.1, fun m hm h0 => LD.2 m hm (D.2 m (hle hm) h0)⟩
