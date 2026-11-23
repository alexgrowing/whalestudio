import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtremalNegativeSets
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemUJsetOfKset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKStableOfMemLowKSub

noncomputable section

open Formalism.MainNotions.S Formalism.IndefR.FWT Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ExtRep

section

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem exists_proj_comm (hσ : IsURepOn (UJset ε) σ) (U : Submodule ℂ H) [FiniteDimensional ℂ U]
    (hU : IsKStableOn ε σ U) :
    ∃ E : H →L[ℂ] H, IsOrthProjOnto E U ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ x, E (σ k x) = σ k (E x) := by
  obtain ⟨E, hE⟩ := GlobalTheory.LowKProj.exists_proj U
  refine ⟨E, hE, fun k hk x => ?_⟩
  have := GlobalTheory.LowKProj.comm_of_stable hE (GlobalTheory.LowKProj.inner_adj hσ hk) (hU k hk)
    (hU _ (Formalism.REAL.Kset_star ε hk))
  exact congrArg (fun F : H →L[ℂ] H => F x) this

theorem isWtOn_proj {E : H →L[ℂ] H} (hE : ∀ k ∈ Formalism.REAL.Kset ε, ∀ x, E (σ k x) = σ k (E x))
    {μ : Fin n → ℝ} {w : H} (hw : IsWtOn (Formalism.REAL.Kset ε) σ μ w) :
    IsWtOn (Formalism.REAL.Kset ε) σ μ (E w) := by
  intro θ hθ
  rw [← hE _ hθ, hw θ hθ, map_smul]

theorem exists_not_orth {lam : Fin n → ℝ} {x : H} (hx : x ∈ lowKSub ε lam σ) (h0 : x ≠ 0) :
    ∃ S, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S ∧ ∃ s ∈ S, ⟪x, s⟫_ℂ ≠ 0 := by
  by_contra h
  push_neg at h
  have h1 : lowKSub ε lam σ ≤ LinearMap.ker (innerSL ℂ x : H →ₗ[ℂ] ℂ) :=
    sSup_le fun S hS s hs => h S hS s hs
  have h2 : ⟪x, x⟫_ℂ = 0 := h1 hx
  exact h0 (inner_self_eq_zero.1 h2)

theorem cdom_of_mem (hσ : IsURepOn (UJset ε) σ) {lam ν : Fin n → ℝ} {x : H} (hx : x ∈ lowKSub ε lam σ)
    (h0 : x ≠ 0) (hw : IsWtOn (Formalism.REAL.Kset ε) σ ν x) : CDom ε ν (Formalism.QuantumDeterminants.lowK ε lam) := by
  obtain ⟨S, hS, s, hs, hne⟩ := exists_not_orth hx h0
  haveI := hS.1
  obtain ⟨E, hE, hc⟩ := exists_proj_comm hσ S hS.2.1
  refine hS.2.2.2.2 ν (E x) (GlobalTheory.LowKProj.apply_mem hE x) (fun h => hne ?_) (isWtOn_proj hc hw)
  rw [← GlobalTheory.LowKProj.fix_of_mem hE s hs, ← hE.2.1, h, inner_zero_left]

theorem exists_ext_mem (hσ : IsURepOn (UJset ε) σ) {lam : Fin n → ℝ} (U : Submodule ℂ H)
    [FiniteDimensional ℂ U] (hU : IsKStableOn ε σ U) (hle : U ≤ lowKSub ε lam σ) {x : H} (hx : x ∈ U)
    (h0 : x ≠ 0) : ∃ u ∈ U, u ≠ 0 ∧
      IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) u := by
  obtain ⟨S, hS, s, hs, hne⟩ := exists_not_orth (hle hx) h0
  obtain ⟨E, hE, hc⟩ := exists_proj_comm hσ U hU
  have hst : IsKStableOn ε σ (S ⊓ LinearMap.ker (E : H →ₗ[ℂ] H)) := by
    intro k hk w hw
    refine ⟨hS.2.1 k hk w hw.1, ?_⟩
    have h1 : E w = 0 := hw.2
    show E (σ k w) = 0
    rw [hc k hk, h1, map_zero]
  have hbot : S ⊓ LinearMap.ker (E : H →ₗ[ℂ] H) = ⊥ := by
    rcases hS.2.2.1 _ inf_le_left hst with h | h
    · exact h
    · exfalso
      apply hne
      have h1 : s ∈ S ⊓ LinearMap.ker (E : H →ₗ[ℂ] H) := by rw [h]; exact hs
      have h2 : E s = 0 := h1.2
      rw [← GlobalTheory.LowKProj.fix_of_mem hE x hx, hE.2.1, h2, inner_zero_right]
  obtain ⟨w, hwS, hw0, hw⟩ := hS.2.2.2.1
  have hK := pM_mem (revNeg ε) (eps_revNeg ε)
  have hn : ‖σ (pM (revNeg ε)) w‖ = ‖w‖ := hσ.2.1 _ (kset_uj hK) w
  refine ⟨E (σ (pM (revNeg ε)) w), GlobalTheory.LowKProj.apply_mem hE _, fun h => hw0 ?_,
    isWtOn_proj hc (isWtOn_perm hσ _ (eps_revNeg ε) hw)⟩
  have h1 : σ (pM (revNeg ε)) w ∈ S ⊓ LinearMap.ker (E : H →ₗ[ℂ] H) := ⟨hS.2.1 _ hK w hwS, h⟩
  rw [hbot, Submodule.mem_bot] at h1
  rw [h1, norm_zero] at hn
  exact norm_eq_zero.1 hn.symm

theorem eq_of_cdom {ν Λ m : Fin n → ℝ} (h : CDom ε ν Λ)
    (hm : ∀ a b, a < b → ε a = ε b → m b < m a) (hle : ∑ a, Λ a * m a ≤ ∑ a, ν a * m a) : ν = Λ := by
  obtain ⟨c, hc, he⟩ := h
  have hr : ∀ a b : Fin n, ∑ i, Formalism.REAL.root a b i * m i = m a - m b := by
    intro a b
    simp [Formalism.REAL.root, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
  have h1 : ∑ a, Λ a * m a - ∑ a, ν a * m a = ∑ a, ∑ b, (c a b : ℝ) * (m a - m b) := by
    rw [← Finset.sum_sub_distrib]
    have : ∀ i, Λ i * m i - ν i * m i = ∑ a, ∑ b, (c a b : ℝ) * (Formalism.REAL.root a b i * m i) := by
      intro i
      have h2 := congrFun he i
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
      rw [← sub_mul, h2]
      simp only [Finset.sum_mul, mul_assoc]
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum, hr]
  have hnn : ∀ a b, 0 ≤ (c a b : ℝ) * (m a - m b) := by
    intro a b
    by_cases h0 : c a b = 0
    · simp [h0]
    · exact mul_nonneg (Nat.cast_nonneg _) (sub_pos.2 (hm a b (hc a b h0).1 (hc a b h0).2)).le
  have h3 : ∑ a, ∑ b, (c a b : ℝ) * (m a - m b) = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hnn a b)
  have h4 : ∀ a b, c a b = 0 := by
    intro a b
    by_contra h0
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => Finset.sum_nonneg fun b _ => hnn a b).1 h3 a
      (Finset.mem_univ _)
    have h6 := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => hnn a b).1 h5 b (Finset.mem_univ _)
    have h7 : (0 : ℝ) < c a b := Nat.cast_pos.2 (Nat.pos_of_ne_zero h0)
    exact (mul_pos h7 (sub_pos.2 (hm a b (hc a b h0).1 (hc a b h0).2))).ne' h6
  simp only [h4, Nat.cast_zero, zero_smul, Finset.sum_const_zero] at he
  exact (sub_eq_zero.1 he).symm

theorem eps_symm (a : Fin n) : ε ((revNeg ε).symm a) = ε a := by
  rw [← eps_revNeg ε ((revNeg ε).symm a), Equiv.apply_symm_apply]

theorem form_anti (a b : Fin n) (hab : a < b) (h : ε a = ε b) :
    (fun a : Fin n => if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ)) ((revNeg ε).symm b) <
      (fun a : Fin n => if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ)) ((revNeg ε).symm a) := by
  simp only [eps_symm]
  cases ha : ε a
  · have hb : ε b = false := h ▸ ha
    simp only [hb, Bool.false_eq_true, if_false, Nat.cast_lt]
    rcases lt_trichotomy ((revNeg ε).symm b) ((revNeg ε).symm a) with h1 | h1 | h1
    · exact h1
    · exact absurd ((revNeg ε).symm.injective h1) hab.ne'
    · have := GlobalTheory.Cmp.ExtremalNegativeSets.revNeg_anti (ε := ε) h1 ((eps_symm a).trans ha) ((eps_symm b).trans hb)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      exact absurd this hab.not_gt
  · have hb : ε b = true := h ▸ ha
    have e1 : (revNeg ε).symm a = a := (Equiv.symm_apply_eq _).2 (revNeg_of_pos ε ha).symm
    have e2 : (revNeg ε).symm b = b := (Equiv.symm_apply_eq _).2 (revNeg_of_pos ε hb).symm
    simp only [hb, if_true, e1, e2, neg_lt_neg_iff, Nat.cast_lt]
    exact hab

theorem wt_eq (hσ : IsURepOn (UJset ε) σ) {lam μ : Fin n → ℝ} {x : H} (hx : x ∈ lowKSub ε lam σ)
    (h0 : x ≠ 0) (hw : IsWtOn (Formalism.REAL.Kset ε) σ μ x)
    (hle : ∑ a : Fin n, Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a) * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ)) ≤
      ∑ a : Fin n, μ a * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ))) :
    μ = fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a) := by
  have hK := pM_mem (revNeg ε).symm (eps_symm (ε := ε))
  have hn : ‖σ (pM (revNeg ε).symm) x‖ = ‖x‖ := hσ.2.1 _ (kset_uj hK) x
  have h1 := cdom_of_mem hσ (GlobalTheory.LowKProj.lowKSub_stable ε lam σ _ hK x hx)
    (fun h => h0 (by rw [h, norm_zero] at hn; exact norm_eq_zero.1 hn.symm))
    (isWtOn_perm hσ _ (eps_symm (ε := ε)) hw)
  have h2 := eq_of_cdom h1 (form_anti (ε := ε)) (by
    rw [← Equiv.sum_comp (revNeg ε), ← Equiv.sum_comp (revNeg ε) (fun a => μ ((revNeg ε).symm a) * _)]
    simpa only [Equiv.symm_apply_apply] using hle)
  funext a
  rw [← h2]
  simp only [Equiv.symm_apply_apply]

end

theorem exists_extremal_same_image : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (X : Type) [AddCommGroup X] [Module ℂ X] (ε : Fin n → Bool) (lam μ : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (π : Matrix (Fin n) (Fin n) ℂ → (X →ₗ[ℂ] X)) (L : Submodule ℂ H) (φ : H →ₗ[ℂ] X) (v : H), IsURepOn (UJset ε) σ → L ≤ lowKSub ε lam σ → IsKStableOn ε σ L → (∀ k ∈ Formalism.REAL.Kset ε, ∀ x ∈ L, φ (σ k x) = π k (φ x)) → v ∈ L → ‖v‖ = 1 → (∀ t : Fin n → ℝ, π (Matrix.diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I)) (φ v) = Complex.exp (((∑ a, μ a * t a : ℝ) : ℂ) * Complex.I) • φ v) → (∀ (ν : Fin n → ℝ) (y : X), y ∈ Submodule.span ℂ {z | ∃ k ∈ Formalism.REAL.Kset ε, z = π k (φ v)} → y ≠ 0 → (∀ t : Fin n → ℝ, π (Matrix.diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I)) y = Complex.exp (((∑ a, ν a * t a : ℝ) : ℂ) * Complex.I) • y) → ∑ a : Fin n, ν a * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ)) ≤ ∑ a : Fin n, μ a * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ))) → ∃ x ∈ L, ‖x‖ = 1 ∧ IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) x ∧ φ x = φ v := by
  intro n H _ _ X _ _ ε lam μ σ π L φ v hσ hL hLs hφ hv hv1 hwt hmax
  set U : Submodule ℂ H := Submodule.span ℂ {z | ∃ k ∈ Formalism.REAL.Kset ε, z = σ k v} with hUdef
  have hUL : U ≤ L := Submodule.span_le.2 (by rintro _ ⟨k, hk, rfl⟩; exact hLs k hk v hv)
  have hfd : FiniteDimensional ℂ U := by
    obtain ⟨S, h1, h2, h3⟩ := GlobalTheory.exists_kStable_of_mem_lowKSub n ε lam H σ v (hL hv)
    have : U ≤ S := Submodule.span_le.2 (by rintro _ ⟨k, hk, rfl⟩; exact h2 k hk v h3)
    exact Submodule.finiteDimensional_of_le this
  have hUs : IsKStableOn ε σ U := by
    intro g hg w hw
    have : U ≤ U.comap (σ g : H →ₗ[ℂ] H) := Submodule.span_le.2 (by
      rintro _ ⟨k, hk, rfl⟩
      refine Submodule.subset_span ⟨g * k, Formalism.REAL.Kset_mul ε hg hk, ?_⟩
      rw [hσ.1.2 g (kset_uj hg) k (kset_uj hk)]
      rfl)
    exact this hw
  have h1K : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε := by
    have := diag_mem (ε := ε) (fun _ => 0)
    simpa using this
  have hvU : v ∈ U := Submodule.subset_span ⟨1, h1K, by rw [hσ.1.1]; rfl⟩
  have hUφ : ∀ u ∈ U, φ u ∈ Submodule.span ℂ {z | ∃ k ∈ Formalism.REAL.Kset ε, z = π k (φ v)} := by
    have : U ≤ (Submodule.span ℂ {z | ∃ k ∈ Formalism.REAL.Kset ε, z = π k (φ v)}).comap φ :=
      Submodule.span_le.2 (by
        rintro _ ⟨k, hk, rfl⟩
        exact Submodule.subset_span ⟨k, hk, hφ k hk v hv⟩)
    exact fun u hu => this hu
  have hU0s : IsKStableOn ε σ (U ⊓ LinearMap.ker φ) := by
    intro k hk w hw
    refine ⟨hUs k hk w hw.1, ?_⟩
    have h1 : φ w = 0 := hw.2
    show φ (σ k w) = 0
    rw [hφ k hk w (hUL hw.1), h1, map_zero]
  haveI : FiniteDimensional ℂ ↥(U ⊓ LinearMap.ker φ) := Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨E, hE, hc⟩ := exists_proj_comm hσ (U ⊓ LinearMap.ker φ) hU0s
  have hU1s : IsKStableOn ε σ (U ⊓ LinearMap.ker (E : H →ₗ[ℂ] H)) := by
    intro k hk w hw
    refine ⟨hUs k hk w hw.1, ?_⟩
    have h1 : E w = 0 := hw.2
    show E (σ k w) = 0
    rw [hc k hk, h1, map_zero]
  haveI : FiniteDimensional ℂ ↥(U ⊓ LinearMap.ker (E : H →ₗ[ℂ] H)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hinj : ∀ w ∈ U ⊓ LinearMap.ker (E : H →ₗ[ℂ] H), φ w = 0 → w = 0 := by
    intro w hw h
    have h1 : E w = 0 := hw.2
    rw [← GlobalTheory.LowKProj.fix_of_mem hE w ⟨hw.1, h⟩, h1]
  have hv0 : E v ∈ U ⊓ LinearMap.ker φ := GlobalTheory.LowKProj.apply_mem hE v
  have hEv1 : E (v - E v) = 0 := by rw [map_sub, GlobalTheory.LowKProj.fix_of_mem hE _ hv0, sub_self]
  have hv1m : v - E v ∈ U ⊓ LinearMap.ker (E : H →ₗ[ℂ] H) := ⟨U.sub_mem hvU hv0.1, hEv1⟩
  have hφ1 : φ (v - E v) = φ v := by
    have h1 : φ (E v) = 0 := hv0.2
    rw [map_sub, h1, sub_zero]
  have hw1 : IsWtOn (Formalism.REAL.Kset ε) σ μ (v - E v) := by
    intro θ hθ
    rw [← sub_eq_zero]
    refine hinj _ (Submodule.sub_mem _ (hU1s _ hθ _ hv1m) (Submodule.smul_mem _ _ hv1m)) ?_
    rw [map_sub, hφ _ hθ _ (hUL hv1m.1), map_smul, hφ1, hwt, sub_self]
  have hw2 : IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) (v - E v) := by
    by_cases h0 : v - E v = 0
    · intro θ hθ
      rw [h0, map_zero, smul_zero]
    · obtain ⟨u, hu, hu0, hwu⟩ := exists_ext_mem hσ (lam := lam) _ hU1s
        (inf_le_left.trans (hUL.trans hL)) hv1m h0
      have h1 := hmax (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) (φ u) (hUφ u hu.1)
        (fun h => hu0 (hinj u hu h)) (fun t => by
          rw [← hφ _ (diag_mem t) u (hUL hu.1), hwu t (diag_mem t), map_smul])
      rw [← wt_eq hσ (hL (hUL hv1m.1)) h0 hw1 h1]
      exact hw1
  by_cases h0 : E v = 0
  · rw [h0, sub_zero] at hw2
    exact ⟨v, hv, hv1, hw2, rfl⟩
  · obtain ⟨u, hu, hu0, hwu⟩ := exists_ext_mem hσ (lam := lam) _ hU0s
      (inf_le_left.trans (hUL.trans hL)) hv0 h0
    have horth : ∀ w ∈ U ⊓ LinearMap.ker φ, ⟪v - E v, w⟫_ℂ = 0 := by
      intro w hw
      rw [← GlobalTheory.LowKProj.fix_of_mem hE w hw, ← hE.2.1, hEv1, inner_zero_left]
    have hm : (((‖E v‖ / ‖u‖ : ℝ) : ℂ) • u) ∈ U ⊓ LinearMap.ker φ := Submodule.smul_mem _ _ hu
    have hnm : ‖(((‖E v‖ / ‖u‖ : ℝ) : ℂ) • u)‖ = ‖E v‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        div_mul_cancel₀ _ (norm_ne_zero_iff.2 hu0)]
    refine ⟨(v - E v) + ((‖E v‖ / ‖u‖ : ℝ) : ℂ) • u, L.add_mem (hUL hv1m.1) (hUL hm.1), ?_, ?_, ?_⟩
    · have p1 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _ (horth _ hm)
      have p2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _ (horth _ hv0)
      rw [sub_add_cancel, hv1] at p2
      rw [hnm, ← p2] at p1
      exact (mul_self_inj_of_nonneg (norm_nonneg _) zero_le_one).1 p1
    · intro θ hθ
      rw [map_add, hw2 θ hθ, isWtOn_smul hwu _ θ hθ, smul_add]
    · have h1 : φ (((‖E v‖ / ‖u‖ : ℝ) : ℂ) • u) = 0 := hm.2
      rw [map_add, hφ1, h1, add_zero]

end GlobalTheory.ExtRep

end
