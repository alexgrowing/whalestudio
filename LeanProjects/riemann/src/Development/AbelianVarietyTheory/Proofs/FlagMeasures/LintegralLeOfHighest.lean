import Mathlib
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.MomOne

open PI.UpqRep

section L2

variable {X Ω : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [MeasurableSpace Ω] {μ : Measure Ω}

theorem lintegral_sq_eq (f : Ω → X) : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ = eLpNorm f 2 μ ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem memLp_of_lt_top {f : Ω → X} (hf : AEStronglyMeasurable f μ)
    (h : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ ≠ ⊤) : MemLp f 2 μ := by
  refine ⟨hf, ?_⟩
  rw [lintegral_sq_eq] at h
  exact lt_top_iff_ne_top.2 fun e => h (by rw [e]; simp)

theorem exists_linear_sq {V : Type} [AddCommGroup V] [Module ℂ V] (T : V → Ω → X)
    (hadd : ∀ v w, T (v + w) =ᵐ[μ] T v + T w) (hsm : ∀ (a : ℂ) v, T (a • v) =ᵐ[μ] a • T v)
    (hL : ∀ v, MemLp (T v) 2 μ) :
    ∃ F : V →ₗ[ℂ] Lp X 2 μ, ∀ v, ∫⁻ x, ENNReal.ofReal (‖T v x‖ ^ 2) ∂μ = ENNReal.ofReal (‖F v‖ ^ 2) := by
  refine ⟨⟨⟨fun v => (hL v).toLp _, fun v w => ?_⟩, fun a v => ?_⟩, fun v => ?_⟩
  · rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (hadd v w)
  · simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (hsm a v)
  · show _ = ENNReal.ofReal (‖(hL v).toLp _‖ ^ 2)
    rw [Lp.norm_toLp, lintegral_sq_eq, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hL v).2.ne]

end L2

section core

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem proj_comm (hτ : IsURepOn (UJset ε) τ) (M : Submodule ℂ H) [FiniteDimensional ℂ M]
    (hM : IsKStableOn ε τ M) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) (x : H) :
    M.starProjection (τ g x) = τ g (M.starProjection x) := by
  obtain ⟨⟨r1, r2⟩, r3, -⟩ := hτ
  have hg' := Kset_star ε hg
  have hgU := GlobalTheory.CayleyChoice.Kset_sub hg
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hM g hg _ (M.starProjection_apply_mem x)) ?_
  intro w hw
  have hs : τ g (τ (star g) w) = w := by
    have := r2 g hgU _ (GlobalTheory.CayleyChoice.Kset_sub hg')
    rw [Matrix.mem_unitaryGroup_iff.1 hg.1, r1] at this
    simpa using (congrArg (fun A : H →L[ℂ] H => A w) this).symm
  have hin := (LinearMap.norm_map_iff_inner_map_map ((τ g : H →L[ℂ] H) : H →ₗ[ℂ] H)).1 (r3 g hgU)
    (x - M.starProjection x) (τ (star g) w)
  simp only [ContinuousLinearMap.coe_coe] at hin
  rw [← map_sub, ← hs, hin]
  exact Submodule.starProjection_inner_eq_zero x _ (hM _ hg' w hw)

theorem isWtOn_smul {Λ : Fin n → ℝ} {v : H} (hv : IsWtOn (Kset ε) τ Λ v) (a : ℂ) :
    IsWtOn (Kset ε) τ Λ (a • v) := by
  intro θ hθ
  rw [map_smul, hv θ hθ, smul_comm]

theorem norm_normalise {v : H} (hv : v ≠ 0) : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1 := by
  rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]

theorem form_le_of_highest (hτ : IsURepOn (UJset ε) τ) (Λ : Fin n → ℝ) (V : Submodule ℂ H) [FiniteDimensional ℂ V]
    (hVs : IsKStableOn ε τ V) (hV : V ≤ sSup {S | IsKTypeOf ε τ Λ S}) (N : H → ℝ)
    (hpar : ∀ x ∈ V, ∀ y ∈ V, N (x + y) + N (x - y) = 2 * N x + 2 * N y)
    (hsm : ∀ (a : ℂ), ∀ x ∈ V, N (a • x) = ‖a‖ ^ 2 * N x) (hcont : Continuous fun v : V => N v)
    (hinv : ∀ g ∈ Kset ε, ∀ x ∈ V, N (τ g x) = N x) (C : ℝ)
    (hw : ∀ S : Submodule ℂ H, S ≤ V → IsKStableOn ε τ S →
      (∀ (μ : Fin n → ℝ) (v : H), v ∈ S → v ≠ 0 → IsWtOn (Kset ε) τ μ v → CDom ε μ Λ) →
      ∀ v ∈ S, ‖v‖ = 1 → IsWtOn (Kset ε) τ Λ v → N v ≤ C) :
    ∀ w ∈ V, ‖w‖ = 1 → N w ≤ C := by
  intro w hwV hw1
  obtain ⟨v0, hv0, hmax⟩ := (isCompact_sphere (0 : V) 1).exists_isMaxOn
    ⟨⟨w, hwV⟩, by simpa using hw1⟩ hcont.continuousOn
  have hv1 : ‖(v0 : H)‖ = 1 := by simpa using hv0
  set c := N v0 with hc
  have hunit : ∀ x ∈ V, ‖x‖ = 1 → N x ≤ c := fun x hx h1 =>
    hmax (a := ⟨x, hx⟩) (by simpa using h1)
  have hN0 : N 0 = 0 := by simpa using hsm 0 0 V.zero_mem
  have hle : ∀ x ∈ V, N x ≤ c * ‖x‖ ^ 2 := by
    intro x hx
    by_cases h0 : x = 0
    · simp [h0, hN0]
    · have h1 := hunit _ (V.smul_mem _ hx) (norm_normalise h0)
      rw [hsm _ x hx, Complex.norm_real, norm_inv, norm_norm, inv_pow] at h1
      have hp : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 h0) 2
      rwa [inv_mul_le_iff₀ hp, mul_comm] at h1
  let M : Submodule ℂ H :=
    { carrier := {x | x ∈ V ∧ N x = c * ‖x‖ ^ 2}
      zero_mem' := ⟨V.zero_mem, by simp [hN0]⟩
      add_mem' := by
        rintro x y ⟨hx, ex⟩ ⟨hy, ey⟩
        refine ⟨V.add_mem hx hy, le_antisymm (hle _ (V.add_mem hx hy)) ?_⟩
        have h1 := hpar x hx y hy
        have h2 := hle _ (V.sub_mem hx hy)
        have h3 := parallelogram_law_with_norm ℂ x y
        have h4 : c * ‖x + y‖ ^ 2 + c * ‖x - y‖ ^ 2 = 2 * (c * ‖x‖ ^ 2) + 2 * (c * ‖y‖ ^ 2) := by
          simp only [sq] at h3 ⊢
          linear_combination c * h3
        linarith
      smul_mem' := by
        rintro a x ⟨hx, ex⟩
        refine ⟨V.smul_mem a hx, ?_⟩
        rw [hsm a x hx, ex, norm_smul]; ring }
  have hMV : M ≤ V := fun x hx => hx.1
  haveI : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le hMV
  have hMs : IsKStableOn ε τ M := by
    rintro g hg x ⟨hx, ex⟩
    exact ⟨hVs g hg x hx, by rw [hinv g hg x hx, ex, hτ.2.1 g (GlobalTheory.CayleyChoice.Kset_sub hg)]⟩
  set P : H →ₗ[ℂ] H := (M.starProjection : H →ₗ[ℂ] H) with hP
  have hPc : ∀ g ∈ Kset ε, ∀ x, P (τ g x) = τ g (P x) := fun g hg x => proj_comm hτ M hMs hg x
  have hPM : ∀ x, P x ∈ M := fun x => M.starProjection_apply_mem x
  have hker : ∀ S : Submodule ℂ H, IsKStableOn ε τ S → IsKStableOn ε τ (S ⊓ LinearMap.ker P) := by
    rintro S hS g hg x ⟨hx, hx0⟩
    refine ⟨hS g hg x hx, ?_⟩
    have hx0' : P x = 0 := hx0
    show P (τ g x) = 0
    rw [hPc g hg, hx0', map_zero]
  have hex : ∃ S, IsKTypeOf ε τ Λ S ∧ S ⊓ LinearMap.ker P = ⊥ := by
    by_contra hne
    push Not at hne
    have h1 : sSup {S | IsKTypeOf ε τ Λ S} ≤ LinearMap.ker P := by
      refine sSup_le fun S hS => ?_
      have := (hS.2.2.1 _ inf_le_left (hker S hS.2.1)).resolve_left (hne S hS)
      rw [← this]; exact inf_le_right
    have h2 : P v0 = 0 := h1 (hV v0.2)
    have h3 : P v0 = v0 := Submodule.starProjection_eq_self_iff.2 ⟨v0.2, by rw [hv1]; simp [hc]⟩
    rw [h3] at h2
    rw [h2] at hv1
    simp at hv1
  obtain ⟨S, ⟨-, hSs, -, ⟨v, hvS, hv0', hvw⟩, hcd⟩, hinj⟩ := hex
  have hz : ∀ x ∈ S, P x = 0 → x = 0 := fun x hx h0 => by
    have : x ∈ S ⊓ LinearMap.ker P := ⟨hx, h0⟩
    rwa [hinj, Submodule.mem_bot] at this
  have hPv : P v ≠ 0 := fun h0 => hv0' (hz v hvS h0)
  have hmapM : S.map P ≤ M := by
    rintro _ ⟨x, -, rfl⟩; exact hPM x
  have hu : ((‖P v‖⁻¹ : ℝ) : ℂ) • P v ∈ S.map P := Submodule.smul_mem _ _ ⟨v, hvS, rfl⟩
  have key := hw (S.map P) (hmapM.trans hMV) ?_ ?_ _ hu (norm_normalise hPv) (isWtOn_smul ?_ _)
  · have e := (hmapM hu).2
    rw [norm_normalise hPv, one_pow, mul_one] at e
    rw [e] at key
    exact (hunit w hwV hw1).trans key
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨τ g x, hSs g hg x hx, hPc g hg x⟩
  · rintro μ _ ⟨x, hx, rfl⟩ h0 hwt
    refine hcd μ x hx (by rintro rfl; simp at h0) fun θ hθ => ?_
    rw [← sub_eq_zero]
    refine hz _ (S.sub_mem (hSs _ hθ x hx) (S.smul_mem _ hx)) ?_
    rw [map_sub, map_smul, hPc _ hθ, hwt θ hθ, sub_self]
  · intro θ hθ
    rw [← hPc _ hθ, hvw θ hθ, map_smul]

theorem lintegral_le_of_highest {X Ω : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [MeasurableSpace Ω]
    {m : Measure Ω} (hτ : IsURepOn (UJset ε) τ) (Λ : Fin n → ℝ) (D : Submodule ℂ H)
    (hD : ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε τ S → S ≤ D) (T : H → Ω → X)
    (hadd : ∀ v ∈ D, ∀ w ∈ D, T (v + w) =ᵐ[m] T v + T w) (hsm : ∀ (a : ℂ), ∀ v ∈ D, T (a • v) =ᵐ[m] a • T v)
    (hme : ∀ v ∈ D, AEStronglyMeasurable (T v) m)
    (hinv : ∀ g ∈ Kset ε, ∀ v ∈ D, ∫⁻ x, ENNReal.ofReal (‖T (τ g v) x‖ ^ 2) ∂m =
      ∫⁻ x, ENNReal.ofReal (‖T v x‖ ^ 2) ∂m) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε τ S →
      (∀ (μ : Fin n → ℝ) (v : H), v ∈ S → v ≠ 0 → IsWtOn (Kset ε) τ μ v → CDom ε μ Λ) →
      ∀ v ∈ S, ‖v‖ = 1 → IsWtOn (Kset ε) τ Λ v → ∫⁻ x, ENNReal.ofReal (‖T v x‖ ^ 2) ∂m ≤ ENNReal.ofReal C)
    (w : H) (hwL : w ∈ sSup {S | IsKTypeOf ε τ Λ S}) (hw1 : ‖w‖ = 1) :
    ∫⁻ x, ENNReal.ofReal (‖T w x‖ ^ 2) ∂m ≤ ENNReal.ofReal C := by
  let W : Submodule ℂ H :=
    { carrier := {x | x ∈ D ∧ MemLp (T x) 2 m}
      zero_mem' := ⟨D.zero_mem, by
        have := hsm 0 0 D.zero_mem
        rw [zero_smul, zero_smul] at this
        exact (memLp_congr_ae this).2 MemLp.zero⟩
      add_mem' := by
        rintro x y ⟨hx, ex⟩ ⟨hy, ey⟩
        exact ⟨D.add_mem hx hy, (memLp_congr_ae (hadd x hx y hy)).2 (ex.add ey)⟩
      smul_mem' := by
        rintro a x ⟨hx, ex⟩
        exact ⟨D.smul_mem a hx, (memLp_congr_ae (hsm a x hx)).2 (ex.const_smul a)⟩ }
  have hLW : sSup {S | IsKTypeOf ε τ Λ S} ≤ W := by
    refine sSup_le fun S hS => ?_
    obtain ⟨hfd, hSs, hirr, ⟨v, hvS, hv0, hvw⟩, hcd⟩ := hS
    have hSD := hD S hfd hSs
    have hst : IsKStableOn ε τ (S ⊓ W) := by
      rintro g hg x ⟨hx, hxD, hxL⟩
      have hgx := hSs g hg x hx
      refine ⟨hgx, hSD hgx, memLp_of_lt_top (hme _ (hSD hgx)) ?_⟩
      rw [hinv g hg x hxD, lintegral_sq_eq]
      exact ENNReal.pow_ne_top hxL.2.ne
    rcases hirr _ inf_le_left hst with e | e
    · exfalso
      have hu := S.smul_mem ((‖v‖⁻¹ : ℝ) : ℂ) hvS
      have : ((‖v‖⁻¹ : ℝ) : ℂ) • v ∈ S ⊓ W := ⟨hu, hSD hu, memLp_of_lt_top (hme _ (hSD hu))
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
          (hw S hfd hSs hcd _ hu (norm_normalise hv0) (isWtOn_smul hvw _)))⟩
      rw [e, Submodule.mem_bot] at this
      have h1 := norm_normalise hv0
      rw [this] at h1
      simp at h1
    · rw [← e]; exact inf_le_right
  obtain ⟨V₀, ⟨hfd, hst⟩, hwV⟩ := PI.UnitaryGroupMassFormula.LowSmooth.exists_finStable_of_mem_sSup (Kset ε) τ
    (F := {S | IsKTypeOf ε τ Λ S}) (fun S hS => ⟨hS.1, hS.2.1⟩) hwL
  set V : Submodule ℂ H := V₀ ⊓ sSup {S | IsKTypeOf ε τ Λ S} with hVdef
  haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le (inf_le_left : V ≤ V₀)
  have hVs : IsKStableOn ε τ V := by
    rintro g hg x ⟨hx, hxL⟩
    refine ⟨hst g hg x hx, ?_⟩
    have : sSup {S | IsKTypeOf ε τ Λ S} ≤
        (sSup {S | IsKTypeOf ε τ Λ S} : Submodule ℂ H).comap ((τ g : H →L[ℂ] H) : H →ₗ[ℂ] H) :=
      sSup_le fun S hS y hy => (le_sSup hS : S ≤ sSup {S | IsKTypeOf ε τ Λ S}) (hS.2.1 g hg y hy)
    exact this hxL
  have hVW : V ≤ W := inf_le_right.trans hLW
  obtain ⟨F, hF⟩ := exists_linear_sq (μ := m) (fun v : V => T v)
    (fun v w => hadd _ (hVW v.2).1 _ (hVW w.2).1) (fun a v => hsm a _ (hVW v.2).1) (fun v => (hVW v.2).2)
  set N : H → ℝ := fun v => (∫⁻ x, ENNReal.ofReal (‖T v x‖ ^ 2) ∂m).toReal with hN
  have hNF : ∀ (v : H) (hv : v ∈ V), N v = ‖F ⟨v, hv⟩‖ ^ 2 := fun v hv => by
    have := hF ⟨v, hv⟩
    simp only [hN]
    rw [this, ENNReal.toReal_ofReal (by positivity)]
  have key := form_le_of_highest hτ Λ V hVs inf_le_right N ?_ ?_ ?_ ?_ C ?_ w ⟨hwV, hwL⟩ hw1
  · have hwV' : w ∈ V := ⟨hwV, hwL⟩
    rw [hNF w hwV'] at key
    exact (hF ⟨w, hwV'⟩).trans_le (ENNReal.ofReal_le_ofReal key)
  · intro x hx y hy
    rw [hNF x hx, hNF y hy, hNF _ (V.add_mem hx hy), hNF _ (V.sub_mem hx hy)]
    have h3 := parallelogram_law_with_norm ℂ (F ⟨x, hx⟩) (F ⟨y, hy⟩)
    rw [← map_add, ← map_sub] at h3
    simp only [sq] at h3 ⊢
    exact h3.trans (by ring)
  · intro a x hx
    rw [hNF x hx, hNF _ (V.smul_mem a hx), ← mul_pow, ← norm_smul, ← map_smul]
    rfl
  · have : (fun v : V => N v) = fun v => ‖F v‖ ^ 2 := funext fun v => hNF v v.2
    rw [this]
    exact (F.continuous_of_finiteDimensional.norm).pow 2
  · intro g hg x hx
    simp only [hN]
    rw [hinv g hg x (hVW hx).1]
  · intro S hSV hSs hcd v hv h1 hwt
    exact ENNReal.toReal_le_of_le_ofReal hC (hw S (Submodule.finiteDimensional_of_le hSV) hSs hcd v hv h1 hwt)

end core

end GlobalTheory.MomOne
