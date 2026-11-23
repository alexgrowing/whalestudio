import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaComplete
import GroundTheory.PAdicHodge.ExtRobbaFrob
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

abbrev RadIdx := (Set.Ioo (0 : ℝ) 1)ᵒᵈ

instance : Nonempty RadIdx := ⟨OrderDual.toDual ⟨1 / 2, by norm_num, by norm_num⟩⟩

theorem radIdx_le {i j : RadIdx} (h : i ≤ j) :
    ((OrderDual.ofDual j : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ OrderDual.ofDual i := h

def resSys (i j : RadIdx) (h : i ≤ j) :
    T.RobbaExt (OrderDual.ofDual i) →+* T.RobbaExt (OrderDual.ofDual j) :=
  T.res (radIdx_le h)

instance directedSystem_resSys :
    DirectedSystem (fun i : RadIdx => T.RobbaExt (OrderDual.ofDual i))
      fun i j h => T.resSys i j h where
  map_self i x := T.res_self x
  map_map k j i hij hjk x := T.res_res (radIdx_le hij) (radIdx_le hjk) x

abbrev RobbaTilde : Type _ :=
  Ring.DirectLimit (fun i : RadIdx => T.RobbaExt (OrderDual.ofDual i)) fun i j h => T.resSys i j h

def ofRad (ρ0 : Set.Ioo (0 : ℝ) 1) : T.RobbaExt ρ0 →+* T.RobbaTilde :=
  Ring.DirectLimit.of (fun i : RadIdx => T.RobbaExt (OrderDual.ofDual i))
    (fun i j h => T.resSys i j h) (OrderDual.toDual ρ0)

theorem ofRad_res {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) (x : T.RobbaExt ρ0) :
    T.ofRad ρ1 (T.res h x) = T.ofRad ρ0 x :=
  Ring.DirectLimit.of_f (G := fun i : RadIdx => T.RobbaExt (OrderDual.ofDual i))
    (f := fun i j h => T.resSys i j h) (i := OrderDual.toDual ρ0) (j := OrderDual.toDual ρ1) h x

theorem ofRad_injective (ρ0 : Set.Ioo (0 : ℝ) 1) : Function.Injective (T.ofRad ρ0) :=
  Ring.DirectLimit.of_injective (G := fun i : RadIdx => T.RobbaExt (OrderDual.ofDual i))
    (fun i j h => T.resSys i j h) (fun i j h => T.res_injective (radIdx_le h)) _

theorem exists_ofRad (x : T.RobbaTilde) : ∃ ρ0 y, T.ofRad ρ0 y = x := by
  obtain ⟨i, y, hy⟩ := Ring.DirectLimit.exists_of x
  exact ⟨OrderDual.ofDual i, y, hy⟩

theorem exists_ofRad₂ (x y : T.RobbaTilde) :
    ∃ ρ0 x' y', T.ofRad ρ0 x' = x ∧ T.ofRad ρ0 y' = y := by
  obtain ⟨ρ1, x1, rfl⟩ := T.exists_ofRad x
  obtain ⟨ρ2, y2, rfl⟩ := T.exists_ofRad y
  refine ⟨⟨min ρ1 ρ2, lt_min ρ1.2.1 ρ2.2.1, min_lt_of_left_lt ρ1.2.2⟩,
    T.res (ρ1 := ⟨min ρ1 ρ2, lt_min ρ1.2.1 ρ2.2.1, min_lt_of_left_lt ρ1.2.2⟩) (min_le_left _ _) x1,
    T.res (ρ1 := ⟨min ρ1 ρ2, lt_min ρ1.2.1 ρ2.2.1, min_lt_of_left_lt ρ1.2.2⟩) (min_le_right _ _) y2,
    T.ofRad_res _ _, T.ofRad_res _ _⟩

instance instIsDomainRobbaTilde : IsDomain T.RobbaTilde := by
  have hnt : Nontrivial T.RobbaTilde := ⟨⟨0, 1, fun h => by
    have h' : T.ofRad ⟨1 / 2, by norm_num, by norm_num⟩ 0 = T.ofRad ⟨1 / 2, by norm_num, by norm_num⟩ 1 := by
      rw [map_zero, map_one]; exact h
    exact zero_ne_one (T.ofRad_injective _ h')⟩⟩
  have : NoZeroDivisors T.RobbaTilde := ⟨fun {x y} hxy => by
    obtain ⟨ρ0, x', y', rfl, rfl⟩ := T.exists_ofRad₂ x y
    rw [← map_mul, ← map_zero (T.ofRad ρ0)] at hxy
    rcases mul_eq_zero.1 (T.ofRad_injective ρ0 hxy) with h | h
    · exact Or.inl (by rw [h, map_zero])
    · exact Or.inr (by rw [h, map_zero])⟩
  exact NoZeroDivisors.to_isDomain _

def econToTilde (ρ0 : Set.Ioo (0 : ℝ) 1) : T.Econ ρ0 →+* T.RobbaTilde :=
  (T.ofRad ρ0).comp Completion.coeRingHom

theorem econToTilde_incl {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) (b : T.Econ ρ0) :
    T.econToTilde ρ1 (T.incl h b) = T.econToTilde ρ0 b := by
  simp only [econToTilde, RingHom.comp_apply]
  rw [← T.ofRad_res h]
  congr 1
  exact (T.res_coe h b).symm

theorem econToTilde_eq {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} {b : T.B} (h0 : b ∈ T.Econ ρ0)
    (h1 : b ∈ T.Econ ρ1) : T.econToTilde ρ0 ⟨b, h0⟩ = T.econToTilde ρ1 ⟨b, h1⟩ := by
  set m : Set.Ioo (0 : ℝ) 1 := ⟨min ρ0 ρ1, lt_min ρ0.2.1 ρ1.2.1, min_lt_of_left_lt ρ0.2.2⟩
  rw [← T.econToTilde_incl (ρ1 := m) (min_le_left (ρ0 : ℝ) ρ1),
    ← T.econToTilde_incl (ρ1 := m) (min_le_right (ρ0 : ℝ) ρ1)]
  rfl

theorem econToTilde_injective (ρ0 : Set.Ioo (0 : ℝ) 1) : Function.Injective (T.econToTilde ρ0) :=
  (T.ofRad_injective ρ0).comp (T.coe_injective_Econ (ρ0 := ρ0))

def edagRad (b : T.Edag) : Set.Ioo (0 : ℝ) 1 := Classical.choose (T.mem_Edag.1 b.2)

theorem edagRad_spec (b : T.Edag) : (b : T.B) ∈ T.Econ (T.edagRad b) :=
  Classical.choose_spec (T.mem_Edag.1 b.2)

def edagFun (b : T.Edag) : T.RobbaTilde := T.econToTilde (T.edagRad b) ⟨b, T.edagRad_spec b⟩

theorem edagFun_eq (b : T.Edag) {ρ0 : Set.Ioo (0 : ℝ) 1} (h : (b : T.B) ∈ T.Econ ρ0) :
    T.edagFun b = T.econToTilde ρ0 ⟨b, h⟩ := T.econToTilde_eq _ _

theorem edagFun_common (b c : T.Edag) : ∃ ρ0 : Set.Ioo (0 : ℝ) 1,
    (b : T.B) ∈ T.Econ ρ0 ∧ (c : T.B) ∈ T.Econ ρ0 :=
  ⟨⟨min (T.edagRad b) (T.edagRad c), lt_min (T.edagRad b).2.1 (T.edagRad c).2.1,
      min_lt_of_left_lt (T.edagRad b).2.2⟩,
    T.Econ_anti (min_le_left (T.edagRad b : ℝ) (T.edagRad c)) (T.edagRad_spec b),
    T.Econ_anti (min_le_right (T.edagRad b : ℝ) (T.edagRad c)) (T.edagRad_spec c)⟩

def edagToTilde : T.Edag →+* T.RobbaTilde where
  toFun := T.edagFun
  map_one' := by
    rw [T.edagFun_eq 1 ((T.Econ ⟨1 / 2, by norm_num, by norm_num⟩).one_mem)]
    exact map_one _
  map_mul' b c := by
    obtain ⟨ρ0, hb, hc⟩ := T.edagFun_common b c
    rw [T.edagFun_eq b hb, T.edagFun_eq c hc, T.edagFun_eq (b * c) ((T.Econ ρ0).mul_mem hb hc),
      ← map_mul]
    rfl
  map_zero' := by
    rw [T.edagFun_eq 0 ((T.Econ ⟨1 / 2, by norm_num, by norm_num⟩).zero_mem)]
    exact map_zero _
  map_add' b c := by
    obtain ⟨ρ0, hb, hc⟩ := T.edagFun_common b c
    rw [T.edagFun_eq b hb, T.edagFun_eq c hc, T.edagFun_eq (b + c) ((T.Econ ρ0).add_mem hb hc),
      ← map_add]
    rfl

theorem edagToTilde_apply {ρ0 : Set.Ioo (0 : ℝ) 1} {b : T.B} (hb : b ∈ T.Econ ρ0) :
    T.edagToTilde ⟨b, T.Econ_le_Edag ρ0 hb⟩ = T.econToTilde ρ0 ⟨b, hb⟩ :=
  T.econToTilde_eq _ _

theorem edagToTilde_injective : Function.Injective T.edagToTilde := by
  rw [injective_iff_map_eq_zero]
  intro b h
  have h' := h
  change T.edagFun b = 0 at h'
  rw [T.edagFun_eq b (T.edagRad_spec b)] at h'
  have := T.econToTilde_injective _ (h'.trans (map_zero _).symm)
  exact Subtype.ext (by simpa using congrArg Subtype.val this)

namespace TeichFrob

variable {T} (F : T.TeichFrob)

def rootRadius (τ : Set.Ioo (0 : ℝ) 1) : Set.Ioo (0 : ℝ) 1 :=
  ⟨(τ : ℝ) ^ (((p ^ F.a : ℕ) : ℝ)⁻¹), Real.rpow_pos_of_pos τ.2.1 _,
    Real.rpow_lt_one τ.2.1.le τ.2.2 (inv_pos.2 (by exact_mod_cast F.q_pos))⟩

theorem powRadius_rootRadius (τ : Set.Ioo (0 : ℝ) 1) : F.powRadius (F.rootRadius τ) = τ :=
  Subtype.ext (Real.rpow_inv_natCast_pow τ.2.1.le F.q_pos.ne')

theorem gaussNorm_toB_pow {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {b : T.B}
    (hb : ConvergesAt (T.coeffB b) σ) :
    gaussNorm (T.coeffB (F.toB b)) (σ ^ p ^ F.a) = gaussNorm (T.coeffB b) σ ^ p ^ F.a :=
  F.gaussNorm_coeffB_toB hσ0 hσ1 hb

def econFrob (σ : Set.Ioo (0 : ℝ) 1) : T.Econ σ →+* T.Econ (F.powRadius σ) :=
  ((F.toB : T.B →+* T.B).comp (T.Econ σ).subtype).codRestrict _ fun b => F.toB_mem_Econ_iff.2 b.2

theorem coe_econFrob (σ : Set.Ioo (0 : ℝ) 1) (b : T.Econ σ) :
    (F.econFrob σ b : T.B) = F.toB b := rfl

def econFrobSymm (τ : Set.Ioo (0 : ℝ) 1) : T.Econ τ →+* T.Econ (F.rootRadius τ) :=
  ((F.toB.symm : T.B →+* T.B).comp (T.Econ τ).subtype).codRestrict _ fun b =>
    F.toB_mem_Econ_iff.1 (by rw [F.powRadius_rootRadius]; simpa using b.2)

theorem coe_econFrobSymm (τ : Set.Ioo (0 : ℝ) 1) (b : T.Econ τ) :
    (F.econFrobSymm τ b : T.B) = F.toB.symm b := rfl

theorem uniformContinuous_econFrob (σ : Set.Ioo (0 : ℝ) 1) :
    UniformContinuous (F.econFrob σ) := by
  refine uniformContinuous_iInf_rng.2 fun τ => ?_
  have hq : (0 : ℝ) < ((p ^ F.a : ℕ) : ℝ) := by exact_mod_cast F.q_pos
  set s : ℝ := (τ : ℝ) ^ (((p ^ F.a : ℕ) : ℝ)⁻¹) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos τ.2.1 _
  have hsτ : s ^ p ^ F.a = τ := Real.rpow_inv_natCast_pow τ.2.1.le F.q_pos.ne'
  have hsσ : s ≤ σ := by
    have h1 : s ≤ ((σ : ℝ) ^ p ^ F.a) ^ (((p ^ F.a : ℕ) : ℝ)⁻¹) :=
      Real.rpow_le_rpow τ.2.1.le τ.2.2 (inv_pos.2 hq).le
    rwa [Real.pow_rpow_inv_natCast σ.2.1.le F.q_pos.ne'] at h1
  refine uniformContinuous_iInf_dom (i := (⟨s, hs0, hsσ⟩ : Set.Ioc (0 : ℝ) σ)) ?_
  refine (@Metric.uniformContinuous_iff _ _
    (T.gaussSeminorm σ ⟨s, hs0, hsσ⟩).toSeminormedRing.toPseudoMetricSpace
    (T.gaussSeminorm (F.powRadius σ) τ).toSeminormedRing.toPseudoMetricSpace _).2
    fun ε hε => ⟨min 1 ε, lt_min one_pos hε, ?_⟩
  intro a b hab
  rw [dist_uniformAt'] at hab ⊢
  have hconv : ConvergesAt (T.coeffB ((a : T.B) - b)) s :=
    convergesAt_of_le (T.coeffB_neg_exists _) ((T.Econ σ).sub_mem a.2 b.2) hs0 hsσ
  rw [coe_econFrob, coe_econFrob, ← map_sub, ← hsτ,
    F.gaussNorm_toB_pow hs0 (lt_of_le_of_lt hsσ σ.2.2) hconv]
  have h1 : gaussNorm (T.coeffB ((a : T.B) - b)) s < 1 := lt_of_lt_of_le hab (min_le_left _ _)
  calc gaussNorm (T.coeffB ((a : T.B) - b)) s ^ p ^ F.a ≤ gaussNorm (T.coeffB ((a : T.B) - b)) s :=
        pow_le_of_le_one (gaussNorm_nonneg hs0) h1.le F.q_pos.ne'
    _ < ε := lt_of_lt_of_le hab (min_le_right _ _)

theorem uniformContinuous_econFrobSymm (τ : Set.Ioo (0 : ℝ) 1) :
    UniformContinuous (F.econFrobSymm τ) := by
  refine uniformContinuous_iInf_rng.2 fun s => ?_
  have hs0 : 0 < (s : ℝ) := s.2.1
  have hsr : (s : ℝ) ≤ F.rootRadius τ := s.2.2
  have hsq : (s : ℝ) ^ p ^ F.a ≤ τ := by
    have := pow_le_pow_left₀ hs0.le hsr (p ^ F.a)
    rwa [show ((F.rootRadius τ : Set.Ioo (0 : ℝ) 1) : ℝ) ^ p ^ F.a = τ from
      congrArg Subtype.val (F.powRadius_rootRadius τ)] at this
  refine uniformContinuous_iInf_dom
    (i := (⟨(s : ℝ) ^ p ^ F.a, pow_pos hs0 _, hsq⟩ : Set.Ioc (0 : ℝ) τ)) ?_
  refine (@Metric.uniformContinuous_iff _ _
    (T.gaussSeminorm τ ⟨(s : ℝ) ^ p ^ F.a, pow_pos hs0 _, hsq⟩).toSeminormedRing.toPseudoMetricSpace
    (T.gaussSeminorm (F.rootRadius τ) s).toSeminormedRing.toPseudoMetricSpace _).2
    fun ε hε => ⟨ε ^ p ^ F.a, pow_pos hε _, ?_⟩
  intro a b hab
  rw [dist_uniformAt'] at hab ⊢
  rw [coe_econFrobSymm, coe_econFrobSymm, ← map_sub]
  have hconv : ConvergesAt (T.coeffB (F.toB.symm ((a : T.B) - b))) s := by
    have := (F.econFrobSymm τ (a - b)).2
    exact convergesAt_of_le (T.coeffB_neg_exists _) this hs0 hsr
  have key := F.gaussNorm_toB_pow hs0 (lt_of_le_of_lt hsr (F.rootRadius τ).2.2) hconv
  rw [RingEquiv.apply_symm_apply] at key
  change gaussNorm (T.coeffB ((a : T.B) - b)) ((s : ℝ) ^ p ^ F.a) < ε ^ p ^ F.a at hab
  rw [key] at hab
  exact lt_of_pow_lt_pow_left₀ _ hε.le hab

def extFrob (σ : Set.Ioo (0 : ℝ) 1) : T.RobbaExt σ →+* T.RobbaExt (F.powRadius σ) :=
  Completion.mapRingHom (F.econFrob σ) (F.uniformContinuous_econFrob σ).continuous

def extFrobSymm (τ : Set.Ioo (0 : ℝ) 1) : T.RobbaExt τ →+* T.RobbaExt (F.rootRadius τ) :=
  Completion.mapRingHom (F.econFrobSymm τ) (F.uniformContinuous_econFrobSymm τ).continuous

theorem extFrob_coe (σ : Set.Ioo (0 : ℝ) 1) (b : T.Econ σ) :
    F.extFrob σ (b : T.RobbaExt σ) = ((F.econFrob σ b : T.Econ (F.powRadius σ)) : T.RobbaExt _) :=
  Completion.mapRingHom_coe _ b

theorem extFrobSymm_coe (τ : Set.Ioo (0 : ℝ) 1) (b : T.Econ τ) :
    F.extFrobSymm τ (b : T.RobbaExt τ) =
      ((F.econFrobSymm τ b : T.Econ (F.rootRadius τ)) : T.RobbaExt _) :=
  Completion.mapRingHom_coe _ b

theorem powRadius_le {σ σ' : Set.Ioo (0 : ℝ) 1} (h : (σ' : ℝ) ≤ σ) :
    ((F.powRadius σ' : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ F.powRadius σ :=
  pow_le_pow_left₀ σ'.2.1.le h _

theorem rootRadius_le {τ τ' : Set.Ioo (0 : ℝ) 1} (h : (τ' : ℝ) ≤ τ) :
    ((F.rootRadius τ' : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ F.rootRadius τ :=
  Real.rpow_le_rpow τ'.2.1.le h (inv_pos.2 (by exact_mod_cast F.q_pos)).le

theorem res_extFrob {σ σ' : Set.Ioo (0 : ℝ) 1} (h : (σ' : ℝ) ≤ σ) (x : T.RobbaExt σ) :
    T.res (F.powRadius_le h) (F.extFrob σ x) = F.extFrob σ' (T.res h x) :=
  Completion.induction_on x
    (isClosed_eq ((T.continuous_res _).comp Completion.continuous_map)
      (Completion.continuous_map.comp (T.continuous_res _)))
    fun b => by rw [extFrob_coe, res_coe, res_coe, extFrob_coe]; rfl

theorem res_extFrobSymm {τ τ' : Set.Ioo (0 : ℝ) 1} (h : (τ' : ℝ) ≤ τ) (x : T.RobbaExt τ) :
    T.res (F.rootRadius_le h) (F.extFrobSymm τ x) = F.extFrobSymm τ' (T.res h x) :=
  Completion.induction_on x
    (isClosed_eq ((T.continuous_res _).comp Completion.continuous_map)
      (Completion.continuous_map.comp (T.continuous_res _)))
    fun b => by rw [extFrobSymm_coe, res_coe, res_coe, extFrobSymm_coe]; rfl

def tildeFrob : T.RobbaTilde →+* T.RobbaTilde :=
  Ring.DirectLimit.lift (fun i : RadIdx => T.RobbaExt (OrderDual.ofDual i))
    (fun i j h => T.resSys i j h) T.RobbaTilde
    (fun i => (T.ofRad (F.powRadius (OrderDual.ofDual i))).comp (F.extFrob (OrderDual.ofDual i)))
    fun i j hij x => by
      simp only [RingHom.comp_apply, resSys]
      rw [← F.res_extFrob, T.ofRad_res]

def tildeFrobSymm : T.RobbaTilde →+* T.RobbaTilde :=
  Ring.DirectLimit.lift (fun i : RadIdx => T.RobbaExt (OrderDual.ofDual i))
    (fun i j h => T.resSys i j h) T.RobbaTilde
    (fun i => (T.ofRad (F.rootRadius (OrderDual.ofDual i))).comp
      (F.extFrobSymm (OrderDual.ofDual i)))
    fun i j hij x => by
      simp only [RingHom.comp_apply, resSys]
      rw [← F.res_extFrobSymm, T.ofRad_res]

theorem tildeFrob_ofRad (σ : Set.Ioo (0 : ℝ) 1) (x : T.RobbaExt σ) :
    F.tildeFrob (T.ofRad σ x) = T.ofRad (F.powRadius σ) (F.extFrob σ x) := by
  exact Ring.DirectLimit.lift_of ..

theorem tildeFrobSymm_ofRad (τ : Set.Ioo (0 : ℝ) 1) (x : T.RobbaExt τ) :
    F.tildeFrobSymm (T.ofRad τ x) = T.ofRad (F.rootRadius τ) (F.extFrobSymm τ x) := by
  exact Ring.DirectLimit.lift_of ..

theorem rootRadius_powRadius (σ : Set.Ioo (0 : ℝ) 1) : F.rootRadius (F.powRadius σ) = σ :=
  Subtype.ext (Real.pow_rpow_inv_natCast σ.2.1.le F.q_pos.ne')

theorem tildeFrobSymm_tildeFrob (x : T.RobbaTilde) : F.tildeFrobSymm (F.tildeFrob x) = x := by
  obtain ⟨σ, y, rfl⟩ := T.exists_ofRad x
  rw [F.tildeFrob_ofRad, F.tildeFrobSymm_ofRad]
  have hle : (σ : ℝ) ≤ F.rootRadius (F.powRadius σ) := by rw [F.rootRadius_powRadius]
  rw [← T.ofRad_res hle]
  congr 1
  refine Completion.induction_on y (isClosed_eq ((T.continuous_res _).comp
    (Completion.continuous_map.comp Completion.continuous_map)) continuous_id) fun b => ?_
  rw [extFrob_coe, extFrobSymm_coe, res_coe]
  congr 1
  exact Subtype.ext (F.toB.symm_apply_apply (b : T.B))

theorem tildeFrob_tildeFrobSymm (x : T.RobbaTilde) : F.tildeFrob (F.tildeFrobSymm x) = x := by
  obtain ⟨τ, y, rfl⟩ := T.exists_ofRad x
  rw [F.tildeFrobSymm_ofRad, F.tildeFrob_ofRad]
  have hle : (τ : ℝ) ≤ F.powRadius (F.rootRadius τ) := by rw [F.powRadius_rootRadius]
  rw [← T.ofRad_res hle]
  congr 1
  refine Completion.induction_on y (isClosed_eq ((T.continuous_res _).comp
    (Completion.continuous_map.comp Completion.continuous_map)) continuous_id) fun b => ?_
  rw [extFrobSymm_coe, extFrob_coe, res_coe]
  congr 1
  exact Subtype.ext (F.toB.apply_symm_apply (b : T.B))

def tildeEquiv : T.RobbaTilde ≃+* T.RobbaTilde :=
  RingEquiv.ofRingHom F.tildeFrob F.tildeFrobSymm (RingHom.ext F.tildeFrob_tildeFrobSymm)
    (RingHom.ext F.tildeFrobSymm_tildeFrob)

theorem tildeFrob_edagToTilde (b : T.Edag) :
    F.tildeFrob (T.edagToTilde b) = T.edagToTilde (F.edagEquiv b) := by
  obtain ⟨σ, hσ⟩ := T.mem_Edag.1 b.2
  have hb : T.edagToTilde b = T.econToTilde σ ⟨b, hσ⟩ := T.edagFun_eq b hσ
  rw [hb]
  change _ = T.edagFun (F.edagEquiv b)
  rw [T.edagFun_eq (F.edagEquiv b) (F.toB_mem_Econ_iff.2 hσ)]
  simp only [econToTilde, RingHom.comp_apply]
  rw [tildeFrob_ofRad]
  congr 1
  exact F.extFrob_coe σ ⟨b, hσ⟩

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
