import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaOrd
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

structure TeichIso where

  ψ : Γ ≃+* Γ

  g : L ≃+* L
  red_ψ : ∀ x, T.red (ψ x) = g (T.red x)
  ψ_π : ψ T.π = T.π
  norm_g : ∀ c, ‖g c‖ = ‖c‖

namespace TeichIso

variable {T}

def refl : T.TeichIso where
  ψ := RingEquiv.refl Γ
  g := RingEquiv.refl L
  red_ψ _ := rfl
  ψ_π := rfl
  norm_g _ := rfl

def comp (G₁ G₂ : T.TeichIso) : T.TeichIso where
  ψ := G₂.ψ.trans G₁.ψ
  g := G₂.g.trans G₁.g
  red_ψ x := by simp only [RingEquiv.trans_apply, G₁.red_ψ, G₂.red_ψ]
  ψ_π := by simp only [RingEquiv.trans_apply, G₂.ψ_π, G₁.ψ_π]
  norm_g c := by simp only [RingEquiv.trans_apply, G₁.norm_g, G₂.norm_g]

def symm (G : T.TeichIso) : T.TeichIso where
  ψ := G.ψ.symm
  g := G.g.symm
  red_ψ x := by
    apply G.g.injective
    rw [← G.red_ψ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  ψ_π := by rw [RingEquiv.symm_apply_eq, G.ψ_π]
  norm_g c := by rw [← G.norm_g, RingEquiv.apply_symm_apply]

variable (G : T.TeichIso)

@[simp] theorem refl_ψ (x : Γ) : (refl : T.TeichIso).ψ x = x := rfl

@[simp] theorem refl_g (c : L) : (refl : T.TeichIso).g c = c := rfl

@[simp] theorem comp_ψ (G₁ G₂ : T.TeichIso) (x : Γ) : (G₁.comp G₂).ψ x = G₁.ψ (G₂.ψ x) := rfl

@[simp] theorem comp_g (G₁ G₂ : T.TeichIso) (c : L) : (G₁.comp G₂).g c = G₁.g (G₂.g c) := rfl

@[simp] theorem symm_ψ (x : Γ) : G.symm.ψ x = G.ψ.symm x := rfl

@[simp] theorem symm_g (c : L) : G.symm.g c = G.g.symm c := rfl

theorem ψ_teich (c : L) : G.ψ (T.teich c) = T.teich (G.g c) :=
  T.map_teich G.ψ.toRingHom G.g.toRingHom (fun x => G.red_ψ x) c

theorem coeff_map (x : Γ) (n : ℕ) : T.coeff (G.ψ x) n = G.g (T.coeff x n) := by
  have hπ : G.ψ.toRingHom T.π = T.π * 1 := by rw [mul_one]; exact G.ψ_π
  have h1 := T.map_partialSum G.ψ.toRingHom G.g.toRingHom (fun y => G.red_ψ y) hπ x (n + 1)
  have h2 := T.map_sub_map_partialSum_mem G.ψ.toRingHom hπ x (n + 1)
  refine T.coeff_eq_of_mem (a := fun m => G.g (T.coeff x m)) ?_ n le_rfl
  have e : T.finSum (fun m => G.g (T.coeff x m)) (n + 1) =
      G.ψ.toRingHom (T.partialSum x (n + 1)) := by
    rw [h1]; simp [finSum]
  rw [e]; exact h2

theorem zcoeff_map (x : Γ) (n : ℤ) : T.zcoeff (G.ψ x) n = G.g (T.zcoeff x n) := by
  unfold zcoeff
  split_ifs
  · exact G.coeff_map x _
  · exact (map_zero G.g).symm

theorem norm_zcoeff_map (x : Γ) (n : ℤ) : ‖T.zcoeff (G.ψ x) n‖ = ‖T.zcoeff x n‖ := by
  rw [zcoeff_map, norm_g]

theorem convergesAt_zcoeff_map_iff {x : Γ} {ρ : ℝ} :
    ConvergesAt (T.zcoeff (G.ψ x)) ρ ↔ ConvergesAt (T.zcoeff x) ρ := by
  simp only [ConvergesAt, G.norm_zcoeff_map]

theorem gaussNorm_zcoeff_map (x : Γ) (ρ : ℝ) :
    gaussNorm (T.zcoeff (G.ψ x)) ρ = gaussNorm (T.zcoeff x) ρ := by
  simp only [gaussNorm, G.norm_zcoeff_map]

theorem isUnit_map_π : IsUnit ((algebraMap Γ T.B).comp G.ψ.toRingHom T.π) := by
  rw [RingHom.comp_apply]
  change IsUnit (algebraMap Γ T.B (G.ψ T.π))
  rw [G.ψ_π]
  exact IsLocalization.Away.algebraMap_isUnit T.π

def toBHom : T.B →+* T.B := IsLocalization.Away.lift T.π G.isUnit_map_π

theorem toBHom_algebraMap (x : Γ) :
    G.toBHom (algebraMap Γ T.B x) = algebraMap Γ T.B (G.ψ x) := by
  rw [toBHom, IsLocalization.Away.lift_eq]; rfl

theorem toBHom_comp (G₁ G₂ : T.TeichIso) : (G₁.comp G₂).toBHom = G₁.toBHom.comp G₂.toBHom :=
  IsLocalization.ringHom_ext (Submonoid.powers T.π) (RingHom.ext fun x => by
    simp [toBHom_algebraMap])

def toB : T.B ≃+* T.B :=
  RingEquiv.ofRingHom G.toBHom G.symm.toBHom
    (IsLocalization.ringHom_ext (Submonoid.powers T.π) (RingHom.ext fun x => by
      simp [toBHom_algebraMap]))
    (IsLocalization.ringHom_ext (Submonoid.powers T.π) (RingHom.ext fun x => by
      simp [toBHom_algebraMap]))

theorem toB_apply (b : T.B) : G.toB b = G.toBHom b := rfl

theorem toB_algebraMap (x : Γ) : G.toB (algebraMap Γ T.B x) = algebraMap Γ T.B (G.ψ x) :=
  G.toBHom_algebraMap x

theorem toB_comp (G₁ G₂ : T.TeichIso) (b : T.B) : (G₁.comp G₂).toB b = G₁.toB (G₂.toB b) := by
  rw [toB_apply, toB_apply, toB_apply, toBHom_comp]; rfl

theorem toB_eq_self (h : ∀ x, G.ψ x = x) (b : T.B) : G.toB b = b := by
  have : (G.toB : T.B →+* T.B) = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers T.π) (RingHom.ext fun x => by
      simp [toB_algebraMap, h])
  exact congrArg (fun f : T.B →+* T.B => f b) this

theorem toB_symm_apply (b : T.B) : G.toB.symm b = G.symm.toB b := rfl

theorem coeffB_toB (b : T.B) (k : ℤ) : T.coeffB (G.toB b) k = G.g (T.coeffB b k) := by
  obtain ⟨N, x, hx⟩ := IsLocalization.Away.surj T.π b
  have h' : G.toB b * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B (G.ψ x) := by
    have := congrArg G.toB hx
    rwa [map_mul, map_pow, toB_algebraMap, toB_algebraMap, G.ψ_π] at this
  rw [T.coeffB_eq h', T.coeffB_eq hx]
  exact G.zcoeff_map x _

theorem norm_coeffB_toB (b : T.B) (k : ℤ) : ‖T.coeffB (G.toB b) k‖ = ‖T.coeffB b k‖ := by
  rw [coeffB_toB, norm_g]

theorem convergesAt_coeffB_toB_iff {b : T.B} {ρ : ℝ} :
    ConvergesAt (T.coeffB (G.toB b)) ρ ↔ ConvergesAt (T.coeffB b) ρ := by
  simp only [ConvergesAt, G.norm_coeffB_toB]

theorem gaussNorm_coeffB_toB (b : T.B) (ρ : ℝ) :
    gaussNorm (T.coeffB (G.toB b)) ρ = gaussNorm (T.coeffB b) ρ := by
  simp only [gaussNorm, G.norm_coeffB_toB]

theorem toB_mem_Econ_iff {ρ : Set.Ioo (0 : ℝ) 1} {b : T.B} :
    G.toB b ∈ T.Econ ρ ↔ b ∈ T.Econ ρ :=
  G.convergesAt_coeffB_toB_iff

theorem toB_mem_Edag_iff {b : T.B} : G.toB b ∈ T.Edag ↔ b ∈ T.Edag := by
  simp only [mem_Edag, G.toB_mem_Econ_iff]

theorem ordB_toB (b : T.B) : T.ordB (G.toB b) = T.ordB b := by
  simp only [ordB, coeffB_toB, ne_eq, EmbeddingLike.map_eq_zero_iff]

def edagEquiv : T.Edag ≃+* T.Edag where
  toFun b := ⟨G.toB (b : T.B), G.toB_mem_Edag_iff.2 b.2⟩
  invFun b := ⟨G.toB.symm (b : T.B),
    G.toB_mem_Edag_iff.1 (by rw [RingEquiv.apply_symm_apply]; exact b.2)⟩
  left_inv b := Subtype.ext (G.toB.symm_apply_apply (b : T.B))
  right_inv b := Subtype.ext (G.toB.apply_symm_apply (b : T.B))
  map_mul' b c := Subtype.ext (map_mul G.toB (b : T.B) c)
  map_add' b c := Subtype.ext (map_add G.toB (b : T.B) c)

theorem edagEquiv_apply (b : T.Edag) : (G.edagEquiv b : T.B) = G.toB (b : T.B) := rfl

variable (ρ0 : Set.Ioo (0 : ℝ) 1)

def econMap : T.Econ ρ0 →+* T.Econ ρ0 :=
  ((G.toB : T.B →+* T.B).comp (T.Econ ρ0).subtype).codRestrict _ fun b =>
    G.toB_mem_Econ_iff.2 b.2

theorem coe_econMap (b : T.Econ ρ0) : (G.econMap ρ0 b : T.B) = G.toB b := rfl

theorem uniformContinuous_econMap : UniformContinuous (G.econMap ρ0) := by
  refine uniformContinuous_iInf_rng.2 fun τ => ?_
  refine uniformContinuous_iInf_dom (i := τ) ?_
  refine (@Metric.uniformContinuous_iff _ _
    (T.gaussSeminorm ρ0 τ).toSeminormedRing.toPseudoMetricSpace
    (T.gaussSeminorm ρ0 τ).toSeminormedRing.toPseudoMetricSpace _).2 fun ε hε => ⟨ε, hε, ?_⟩
  intro a b hab
  rw [dist_uniformAt'] at hab ⊢
  rwa [coe_econMap, coe_econMap, ← map_sub, G.gaussNorm_coeffB_toB]

def extMap : T.RobbaExt ρ0 →+* T.RobbaExt ρ0 :=
  Completion.mapRingHom (G.econMap ρ0) (G.uniformContinuous_econMap ρ0).continuous

variable {ρ0}

theorem extMap_coe (b : T.Econ ρ0) :
    G.extMap ρ0 (b : T.RobbaExt ρ0) = ((G.econMap ρ0 b : T.Econ ρ0) : T.RobbaExt ρ0) :=
  Completion.mapRingHom_coe _ b

theorem continuous_extMap : Continuous (G.extMap ρ0) := Completion.continuous_map

theorem extNorm_extMap (ρ : Set.Ioc (0 : ℝ) ρ0) (x : T.RobbaExt ρ0) :
    T.extNorm ρ0 ρ (G.extMap ρ0 x) = T.extNorm ρ0 ρ x :=
  Completion.induction_on x
    (isClosed_eq ((T.continuous_extNorm ρ).comp G.continuous_extMap) (T.continuous_extNorm ρ))
    fun b => by rw [extMap_coe, extNorm_coe, extNorm_coe, coe_econMap, gaussNorm_coeffB_toB]

theorem res_extMap {ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) (x : T.RobbaExt ρ0) :
    T.res h (G.extMap ρ0 x) = G.extMap ρ1 (T.res h x) :=
  Completion.induction_on x
    (isClosed_eq ((T.continuous_res _).comp Completion.continuous_map)
      (Completion.continuous_map.comp (T.continuous_res _)))
    fun b => by rw [extMap_coe, res_coe, res_coe, extMap_coe]; rfl

theorem extMap_comp (G₁ G₂ : T.TeichIso) (x : T.RobbaExt ρ0) :
    (G₁.comp G₂).extMap ρ0 x = G₁.extMap ρ0 (G₂.extMap ρ0 x) :=
  Completion.induction_on x
    (isClosed_eq Completion.continuous_map (Completion.continuous_map.comp Completion.continuous_map))
    fun b => by
      rw [extMap_coe, extMap_coe, extMap_coe]
      congr 1
      exact Subtype.ext (toB_comp G₁ G₂ (b : T.B))

theorem extMap_eq_self (h : ∀ x, G.ψ x = x) (y : T.RobbaExt ρ0) : G.extMap ρ0 y = y :=
  Completion.induction_on y (isClosed_eq Completion.continuous_map continuous_id) fun b => by
    rw [extMap_coe]
    congr 1
    exact Subtype.ext (G.toB_eq_self h (b : T.B))

def tildeMap : T.RobbaTilde →+* T.RobbaTilde :=
  Ring.DirectLimit.lift (fun i : RadIdx => T.RobbaExt (OrderDual.ofDual i))
    (fun i j h => T.resSys i j h) T.RobbaTilde
    (fun i => (T.ofRad (OrderDual.ofDual i)).comp (G.extMap (OrderDual.ofDual i)))
    fun i j hij x => by
      simp only [RingHom.comp_apply, resSys]
      rw [← G.res_extMap, T.ofRad_res]

theorem tildeMap_ofRad (σ : Set.Ioo (0 : ℝ) 1) (x : T.RobbaExt σ) :
    G.tildeMap (T.ofRad σ x) = T.ofRad σ (G.extMap σ x) := by
  exact Ring.DirectLimit.lift_of ..

theorem tildeMap_comp (G₁ G₂ : T.TeichIso) (x : T.RobbaTilde) :
    (G₁.comp G₂).tildeMap x = G₁.tildeMap (G₂.tildeMap x) := by
  obtain ⟨σ, y, rfl⟩ := T.exists_ofRad x
  rw [tildeMap_ofRad, tildeMap_ofRad, tildeMap_ofRad, extMap_comp]

theorem tildeMap_eq_self (h : ∀ x, G.ψ x = x) (x : T.RobbaTilde) : G.tildeMap x = x := by
  obtain ⟨σ, y, rfl⟩ := T.exists_ofRad x
  rw [tildeMap_ofRad, G.extMap_eq_self h]

theorem tildeMap_refl (x : T.RobbaTilde) : (refl : T.TeichIso).tildeMap x = x :=
  tildeMap_eq_self _ (fun _ => rfl) x

theorem tildeMap_symm_tildeMap (x : T.RobbaTilde) : G.symm.tildeMap (G.tildeMap x) = x := by
  rw [← tildeMap_comp]
  exact tildeMap_eq_self _ (fun y => by simp) x

theorem tildeMap_tildeMap_symm (x : T.RobbaTilde) : G.tildeMap (G.symm.tildeMap x) = x := by
  rw [← tildeMap_comp]
  exact tildeMap_eq_self _ (fun y => by simp) x

def tildeEquiv : T.RobbaTilde ≃+* T.RobbaTilde :=
  RingEquiv.ofRingHom G.tildeMap G.symm.tildeMap (RingHom.ext G.tildeMap_tildeMap_symm)
    (RingHom.ext G.tildeMap_symm_tildeMap)

theorem tildeEquiv_apply (x : T.RobbaTilde) : G.tildeEquiv x = G.tildeMap x := rfl

theorem tildeMap_edagToTilde (b : T.Edag) :
    G.tildeMap (T.edagToTilde b) = T.edagToTilde (G.edagEquiv b) := by
  obtain ⟨σ, hσ⟩ := T.mem_Edag.1 b.2
  have hb : T.edagToTilde b = T.econToTilde σ ⟨b, hσ⟩ := T.edagFun_eq b hσ
  rw [hb]
  change _ = T.edagFun (G.edagEquiv b)
  rw [T.edagFun_eq (G.edagEquiv b) (G.toB_mem_Econ_iff.2 hσ)]
  simp only [econToTilde, RingHom.comp_apply]
  rw [tildeMap_ofRad]
  congr 1
  exact G.extMap_coe ⟨b, hσ⟩

theorem tildeMap_econToTilde (σ : Set.Ioo (0 : ℝ) 1) (b : T.Econ σ) :
    G.tildeMap (T.econToTilde σ b) = T.econToTilde σ (G.econMap σ b) := by
  simp only [econToTilde, RingHom.comp_apply]
  rw [tildeMap_ofRad]
  congr 1
  exact G.extMap_coe b

theorem tildeOrd_map [CompleteSpace L] (x : T.RobbaTildeˣ) :
    T.tildeOrd (Units.map (G.tildeMap : T.RobbaTilde →* T.RobbaTilde) x) = T.tildeOrd x := by
  rw [T.tildeOrd_eq (b := G.edagEquiv (T.unitPre x)) (by
    rw [← G.tildeMap_edagToTilde, T.unitPre_spec]; rfl), G.edagEquiv_apply, G.ordB_toB]
  rfl

variable (F : T.TeichFrob)

theorem toB_frob_comm (h : ∀ x, G.ψ (F.φ x) = F.φ (G.ψ x)) (b : T.B) :
    G.toB (F.toB b) = F.toB (G.toB b) := by
  have : (G.toB : T.B →+* T.B).comp (F.toB : T.B →+* T.B) =
      (F.toB : T.B →+* T.B).comp (G.toB : T.B →+* T.B) :=
    IsLocalization.ringHom_ext (Submonoid.powers T.π) (RingHom.ext fun x => by
      simp [TeichIso.toB_algebraMap, TeichFrob.toB_algebraMap, h])
  exact congrArg (fun f : T.B →+* T.B => f b) this

theorem extMap_extFrob (h : ∀ x, G.ψ (F.φ x) = F.φ (G.ψ x)) (σ : Set.Ioo (0 : ℝ) 1)
    (x : T.RobbaExt σ) :
    G.extMap (F.powRadius σ) (F.extFrob σ x) = F.extFrob σ (G.extMap σ x) :=
  Completion.induction_on x
    (isClosed_eq (Completion.continuous_map.comp Completion.continuous_map)
      (Completion.continuous_map.comp Completion.continuous_map))
    fun b => by
      rw [TeichFrob.extFrob_coe, extMap_coe, extMap_coe, TeichFrob.extFrob_coe]
      congr 1
      exact Subtype.ext (G.toB_frob_comm F h (b : T.B))

theorem tildeMap_tildeFrob (h : ∀ x, G.ψ (F.φ x) = F.φ (G.ψ x)) (x : T.RobbaTilde) :
    G.tildeMap (F.tildeFrob x) = F.tildeFrob (G.tildeMap x) := by
  obtain ⟨σ, y, rfl⟩ := T.exists_ofRad x
  rw [F.tildeFrob_ofRad, tildeMap_ofRad, tildeMap_ofRad, F.tildeFrob_ofRad, G.extMap_extFrob F h]

end TeichIso

end TeichLift

end GroundTheory.PAdicHodge
