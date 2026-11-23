import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteCompactRepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteLieActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanCompactOrbitLieDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieGrowthOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspFormStatement

open NumberField GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.CuspStabFin

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem zfin_of_comm (T : Module.End ℂ (Sm E a)) (hT : ∀ z ∈ Zalg E a, z * T = T * z) {φ : Sm E a}
    (h : FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a))) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z (T φ)) '' Zalg E a)) := by
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
    Zalg E a)).map T) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z φ, Submodule.subset_span ⟨z, hz, rfl⟩, (LinearMap.congr_fun (hT z hz) φ).symm⟩

theorem zalg_comm_fin (k : GL (Fin a) (Af E)) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    z * finRep E a k = finRep E a k * z := by
  let S := Subalgebra.centralizer ℂ ({finRep E a k} : Set (Module.End ℂ (Sm E a)))
  have hL : ∀ X, lie E a X ∈ S := fun X T hT => by
    rw [Set.mem_singleton_iff.1 hT]; exact (lie_rt_fin X k).symm
  have hE : ∀ τ i j, Eop (a := a) τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hL _) (S.smul_mem (hL _) _)) _
  have hS : Zalg E a ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact (hS hz (finRep E a k) rfl).symm

theorem level_of_le {φ ψ : Sm E a} (h : IsOpen {k | finRep E a k φ = φ})
    (hle : ∀ k, finRep E a k φ = φ → finRep E a k ψ = ψ) : IsOpen {k | finRep E a k ψ = ψ} :=
  isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.mem_nhds (by simp)) fun k hk => hle k hk)

theorem fin_cpt_comm (k : GL (Fin a) (Af E)) (c : Kinf E a) :
    finRep E a k * cptRep E a c = cptRep E a c * finRep E a k := by
  change rt E a (finGL E a k) * rt E a (infGL E a (Unitary.toUnits c)) =
    rt E a (infGL E a (Unitary.toUnits c)) * rt E a (finGL E a k)
  rw [← map_mul, ← map_mul, infGL_comm]

theorem height_mul_le_const (c : GL (Fin a) (Cinf E)) : ∃ B : ℝ, 1 ≤ B ∧ ∀ y, height (y * c) ≤ B * height y := by
  refine ⟨1 + ‖rmul (toL c.val)‖ + ‖lmul (toL (c⁻¹).val)‖, by linarith [norm_nonneg (rmul (toL c.val)), norm_nonneg (lmul (toL (c⁻¹).val))], fun y => ?_⟩
  have h1 : toL (y * c).val = rmul (toL c.val) (toL y.val) := rfl
  have h2 : toL ((y * c)⁻¹).val = lmul (toL (c⁻¹).val) (toL (y⁻¹).val) := by
    rw [_root_.mul_inv_rev]; rfl
  have e1 := (rmul (toL c.val)).le_opNorm (toL y.val)
  have e2 := (lmul (toL (c⁻¹).val)).le_opNorm (toL (y⁻¹).val)
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (rmul (toL c.val))
  have n4 := norm_nonneg (lmul (toL (c⁻¹).val))
  unfold height
  rw [h1, h2]
  nlinarith

theorem growth_mul_const {f : GL (Fin a) (Cinf E) → ℂ} (c : GL (Fin a) (Cinf E))
    (h : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * height y ^ N) :
    ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f (y * c)‖ ≤ C * height y ^ N := by
  obtain ⟨C, N, hC⟩ := h
  obtain ⟨B, hB, hB'⟩ := height_mul_le_const c
  have C0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N := pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left this hp
  refine ⟨C * B ^ N, N, fun y => (hC _).trans ?_⟩
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (y * c)]) (hB' y) N) C0

theorem isCuspForm_act' (hP : GlobalTheory.Published.AutomorphicFormsFiniteGL) (o : Op E a) (φ : Sm E a) (h : IsCuspForm φ) : IsCuspForm (act o φ) := by
  obtain ⟨hA, hC⟩ := h
  cases o with
  | fin k =>
    refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
    · change φ.1 (ratGL E a γ * g * finGL E a k) = φ.1 (g * finGL E a k)
      rw [mul_assoc, hA.left]
    · have e : {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ} =
          (fun k' => k⁻¹ * k' * k) ⁻¹' {k' | finRep E a k' φ = φ} := by
        ext k'
        simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul]
        constructor
        · intro e
          rw [Module.End.mul_apply, Module.End.mul_apply, e, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
            map_one, Module.End.one_apply]
        · intro e
          have := congrArg (finRep E a k) e
          rwa [Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (finRep E a k), ← map_mul,
            mul_inv_cancel, map_one, Module.End.one_apply] at this
      change IsOpen {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ}
      rw [e]
      exact hA.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · have := hA.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun c => cptRep E a c φ)).map
        (finRep E a k)) (Submodule.span_le.2 ?_)
      rintro _ ⟨c, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨c, rfl⟩, (LinearMap.congr_fun (fin_cpt_comm k c) φ)⟩
    · exact zfin_of_comm _ (fun z hz => zalg_comm_fin k hz) hA.zfin
    · obtain ⟨C, N, h1⟩ := hA.growth (g * finGL E a k)
      refine ⟨C, N, fun y => ?_⟩
      change ‖φ.1 (g * infGL E a y * finGL E a k)‖ ≤ _
      rw [mul_assoc, infGL_comm, ← mul_assoc]
      exact h1 y
    · intro r h0 h1 _ _ μ 𝓕 hμ hF g
      change ∫ x in 𝓕, φ.1 (unip x * g * finGL E a k) ∂μ = 0
      simp_rw [mul_assoc]
      exact hC r h0 h1 μ 𝓕 hμ hF (g * finGL E a k)
  | cpt c =>
    refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
    · change φ.1 (ratGL E a γ * g * infGL E a (Unitary.toUnits c)) = φ.1 (g * infGL E a (Unitary.toUnits c))
      rw [mul_assoc, hA.left]
    · exact level_of_le hA.level fun k hk => by
        change finRep E a k (cptRep E a c φ) = cptRep E a c φ
        rw [← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk]
    · have := hA.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun c => cptRep E a c φ))
        (Submodule.span_le.2 ?_)
      rintro _ ⟨c', rfl⟩
      refine Submodule.subset_span ⟨c' * c, ?_⟩
      change _ = (cptRep E a c' * cptRep E a c) φ
      rw [← map_mul]
    · exact zfin_of_comm _ (fun z hz => GlobalTheory.T.mem_zalg_commute_compactRep E a c z hz) hA.zfin
    · obtain ⟨C, N, h1⟩ := growth_mul_const (Unitary.toUnits c) (hA.growth g)
      refine ⟨C, N, fun y => ?_⟩
      change ‖φ.1 (g * infGL E a y * infGL E a (Unitary.toUnits c))‖ ≤ _
      rw [mul_assoc, ← map_mul]
      exact h1 y
    · intro r h0 h1 _ _ μ 𝓕 hμ hF g
      change ∫ x in 𝓕, φ.1 (unip x * g * infGL E a (Unitary.toUnits c)) ∂μ = 0
      simp_rw [mul_assoc]
      exact hC r h0 h1 μ 𝓕 hμ hF (g * infGL E a (Unitary.toUnits c))
  | lie X =>
    refine ⟨⟨fun γ g => ?_, ?_, GlobalTheory.T.finiteDimensional_span_compact_orbit_lieDerivative E a X φ hA.kfin, zfin_of_comm _ (fun z hz => GlobalTheory.T.mem_zalg_commute_lie_action E a X z hz) hA.zfin, GlobalTheory.AutGrowth.lie_growth_of_finite hP E a X φ hA⟩,
      GlobalTheory.T.isCuspidal_lieAction_of_isCuspForm E a X φ ⟨hA, hC⟩⟩
    · change lieD X φ.1 (ratGL E a γ * g) = lieD X φ.1 g
      have e : chart φ.1 (ratGL E a γ * g) = chart φ.1 g := by
        funext x
        unfold chart
        split_ifs
        · rw [mul_assoc, hA.left]
        · rfl
      unfold lieD
      rw [e]
    · exact level_of_le hA.level fun k hk => by
        change finRep E a k (lie E a X φ) = lie E a X φ
        change (rt E a (finGL E a k) * lie E a X) φ = _
        rw [← lie_rt_fin, Module.End.mul_apply]
        exact congrArg (lie E a X) hk

end GlobalTheory.CuspStabFin

theorem GlobalTheory.CuspStabFin.isCuspForm_act : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [IsTotallyComplex E] (a : ℕ) (o : GlobalTheory.CuspRep.Op E a) (φ : GlobalTheory.CuspRep.Sm E a),
    GlobalTheory.CuspRep.IsCuspForm φ → GlobalTheory.CuspRep.IsCuspForm (GlobalTheory.CuspRep.act o φ) :=
  fun hP _ _ _ _ _ o φ h => GlobalTheory.CuspStabFin.isCuspForm_act' hP o φ h
