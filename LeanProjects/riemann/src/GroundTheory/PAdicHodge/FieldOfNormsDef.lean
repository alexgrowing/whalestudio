import Mathlib
import GroundTheory.PAdicHodge.FieldOfNormsAPF
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology IntermediateField

section Def

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] {L : IntermediateField K Ω}

variable (K Ω L) in

abbrev FinSub : Type _ := {E : IntermediateField K Ω // E ≤ L ∧ FiniteDimensional K E}

abbrev inclAlgebra {E E' : IntermediateField K Ω} (h : E ≤ E') : Algebra E E' :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

open Classical in

def relNorm {E E' : IntermediateField K Ω} (h : E ≤ E') (y : Ω) : Ω :=
  if hy : y ∈ E' then ((@Algebra.norm E E' _ _ (inclAlgebra h) ⟨y, hy⟩ : E) : Ω) else 0

variable (K Ω L) in

def FieldOfNorms : Type _ :=
  {x : FinSub K Ω L → Ω //
    (∀ E, x E ∈ E.1) ∧ ∀ E E' : FinSub K Ω L, ∀ h : E.1 ≤ E'.1, relNorm h (x E') = x E}

theorem relNorm_of_mem {E E' : IntermediateField K Ω} (h : E ≤ E') {y : Ω} (hy : y ∈ E') :
    relNorm h y = ((@Algebra.norm E E' _ _ (inclAlgebra h) ⟨y, hy⟩ : E) : Ω) := by
  rw [relNorm, dif_pos hy]

theorem relNorm_mem {E E' : IntermediateField K Ω} (h : E ≤ E') (y : Ω) : relNorm h y ∈ E := by
  unfold relNorm
  split_ifs
  · exact SetLike.coe_mem _
  · exact zero_mem _

theorem isScalarTower_inclAlgebra {E E' E'' : IntermediateField K Ω} (h : E ≤ E') (h' : E' ≤ E'') :
    @IsScalarTower E E' E'' (inclAlgebra h).toSMul (inclAlgebra h').toSMul
      (inclAlgebra (h.trans h')).toSMul := by
  letI := inclAlgebra h
  letI := inclAlgebra h'
  letI := inclAlgebra (h.trans h')
  exact IsScalarTower.of_algebraMap_eq fun x ↦ rfl

theorem isScalarTower_base_inclAlgebra {E E' : IntermediateField K Ω} (h : E ≤ E') :
    @IsScalarTower K E E' _ (inclAlgebra h).toSMul _ := by
  letI := inclAlgebra h
  exact IsScalarTower.of_algebraMap_eq fun x ↦ rfl

theorem relNorm_trans {E E' E'' : IntermediateField K Ω} (h : E ≤ E') (h' : E' ≤ E'') {y : Ω}
    (hy : y ∈ E'') : relNorm (h.trans h') y = relNorm h (relNorm h' y) := by
  letI := inclAlgebra h
  letI := inclAlgebra h'
  letI := inclAlgebra (h.trans h')
  haveI := isScalarTower_inclAlgebra h h'
  rw [relNorm_of_mem _ hy, relNorm_of_mem h' hy, relNorm_of_mem h (SetLike.coe_mem _)]
  congr 1
  rw [Subtype.coe_eta]
  exact Algebra.norm_norm.symm

theorem relNorm_self {E : IntermediateField K Ω} (h : E ≤ E) {y : Ω} (hy : y ∈ E) :
    relNorm h y = y := by
  rw [relNorm_of_mem _ hy]
  have hA : inclAlgebra h = Algebra.id E := Algebra.algebra_ext _ _ fun _ ↦ rfl
  have key : @Algebra.norm E E _ _ (inclAlgebra h) = @Algebra.norm E E _ _ (Algebra.id E) := by
    rw [hA]
  rw [key, Algebra.norm_self]
  rfl

theorem relNorm_mul {E E' : IntermediateField K Ω} (h : E ≤ E') {y z : Ω} (hy : y ∈ E')
    (hz : z ∈ E') : relNorm h (y * z) = relNorm h y * relNorm h z := by
  letI := inclAlgebra h
  rw [relNorm_of_mem h (mul_mem hy hz), relNorm_of_mem h hy, relNorm_of_mem h hz]
  rw [← IntermediateField.coe_mul, ← map_mul]
  rfl

end Def

section Tower

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}

namespace NormTower

variable (t : NormTower K Ω p) (L : IntermediateField K Ω)

theorem E_mono {m n : ℕ} (h : m ≤ n) : t.E m ≤ t.E n := t.mono h

structure IsTowerFor : Prop where
  le : ∀ n, t.E n ≤ L
  exists_mem : ∀ x ∈ L, ∃ n, x ∈ t.E n
  relNorm_eq : ∀ n, ∀ y ∈ t.E (n + 1), relNorm (t.E_mono (Nat.le_succ n)) y = t.N n y

variable {t L}

def IsTowerFor.finSub (ht : t.IsTowerFor L) (n : ℕ) : FinSub K Ω L :=
  ⟨t.E n, ht.le n, t.finiteDimensional n⟩

@[simp] theorem IsTowerFor.finSub_val (ht : t.IsTowerFor L) (n : ℕ) : (ht.finSub n).1 = t.E n := rfl

theorem IsTowerFor.exists_le (ht : t.IsTowerFor L) (E : FinSub K Ω L) : ∃ n, E.1 ≤ t.E n := by
  haveI := E.2.2
  let b := Module.finBasis K E.1
  have : ∀ i, ∃ n, (b i : Ω) ∈ t.E n := fun i ↦ ht.exists_mem _ (E.2.1 (b i).2)
  choose N hN using this
  refine ⟨Finset.univ.sup N, fun x hx ↦ ?_⟩
  obtain ⟨z, rfl⟩ : ∃ z : E.1, (z : Ω) = x := ⟨⟨x, hx⟩, rfl⟩
  rw [← b.sum_repr z, IntermediateField.coe_sum]
  refine sum_mem fun i _ ↦ ?_
  rw [IntermediateField.coe_smul]
  exact (t.E _).smul_mem (t.E_mono (Finset.le_sup (Finset.mem_univ i)) (hN i))

theorem IsTowerFor.relNorm_eq_Nto (ht : t.IsTowerFor L) (n m : ℕ) {y : Ω} (hy : y ∈ t.E (n + m)) :
    relNorm (t.E_mono (Nat.le_add_right n m)) y = t.Nto n m y := by
  induction m generalizing y with
  | zero => exact relNorm_self _ hy
  | succ m ih =>
    have hle : t.E (n + m) ≤ t.E (n + m + 1) := t.E_mono (Nat.le_succ _)
    rw [show t.E_mono (Nat.le_add_right n (m + 1)) = (t.E_mono (Nat.le_add_right n m)).trans hle
      from rfl, relNorm_trans (t.E_mono (Nat.le_add_right n m)) hle hy, ht.relNorm_eq (n + m) y hy,
      ih (t.N_mem _ hy), Nto_succ]

def IsTowerFor.toFam (ht : t.IsTowerFor L) (x : FieldOfNorms K Ω L) : t.Fam :=
  ⟨fun n ↦ x.1 (ht.finSub n), fun n ↦
    ⟨x.2.1 (ht.finSub n), by
      rw [← ht.relNorm_eq n _ (x.2.1 (ht.finSub (n + 1)))]
      exact x.2.2 (ht.finSub n) (ht.finSub (n + 1)) (t.E_mono (Nat.le_succ n))⟩⟩

theorem IsTowerFor.toFam_val (ht : t.IsTowerFor L) (x : FieldOfNorms K Ω L) (n : ℕ) :
    (ht.toFam x).1 n = x.1 (ht.finSub n) := rfl

theorem IsTowerFor.relNorm_indep (ht : t.IsTowerFor L) (z : t.Fam) {E : IntermediateField K Ω}
    {m n : ℕ} (hm : E ≤ t.E m) (hn : E ≤ t.E n) :
    relNorm hm (z.1 m) = relNorm hn (z.1 n) := by
  wlog hmn : m ≤ n generalizing m n
  · exact (this hn hm (le_of_not_ge hmn)).symm
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [show hn = hm.trans (t.E_mono (Nat.le_add_right m j)) from rfl,
    relNorm_trans hm (t.E_mono (Nat.le_add_right m j)) (z.2 (m + j)).1,
    ht.relNorm_eq_Nto m j (z.2 (m + j)).1, z.2.Nto_eq]

open Classical in

def IsTowerFor.ofFamFun (ht : t.IsTowerFor L) (z : t.Fam) (E : FinSub K Ω L) : Ω :=
  relNorm (Nat.find_spec (ht.exists_le E)) (z.1 (Nat.find (ht.exists_le E)))

theorem IsTowerFor.ofFamFun_eq (ht : t.IsTowerFor L) (z : t.Fam) (E : FinSub K Ω L) {n : ℕ}
    (hn : E.1 ≤ t.E n) : ht.ofFamFun z E = relNorm hn (z.1 n) := by
  classical
  exact ht.relNorm_indep z _ hn

def IsTowerFor.ofFam (ht : t.IsTowerFor L) (z : t.Fam) : FieldOfNorms K Ω L :=
  ⟨ht.ofFamFun z, fun E ↦ by
    obtain ⟨n, hn⟩ := ht.exists_le E
    rw [ht.ofFamFun_eq z E hn]; exact relNorm_mem _ _, fun E E' h ↦ by
    obtain ⟨n, hn⟩ := ht.exists_le E'
    rw [ht.ofFamFun_eq z E' hn, ht.ofFamFun_eq z E (h.trans hn), relNorm_trans h hn (z.2 n).1]⟩

theorem IsTowerFor.ofFam_val (ht : t.IsTowerFor L) (z : t.Fam) (E : FinSub K Ω L) {n : ℕ}
    (hn : E.1 ≤ t.E n) : (ht.ofFam z).1 E = relNorm hn (z.1 n) :=
  ht.ofFamFun_eq z E hn

variable (t L) in

def IsTowerFor.equiv (ht : t.IsTowerFor L) : FieldOfNorms K Ω L ≃ t.Fam where
  toFun := ht.toFam
  invFun := ht.ofFam
  left_inv x := by
    refine Subtype.ext (funext fun E ↦ ?_)
    obtain ⟨n, hn⟩ := ht.exists_le E
    rw [ht.ofFam_val _ E hn, ht.toFam_val]
    exact x.2.2 E (ht.finSub n) hn
  right_inv z := by
    refine Subtype.ext (funext fun n ↦ ?_)
    rw [ht.toFam_val, ht.ofFam_val z _ (t.E_mono (Nat.le_succ n))]
    exact (ht.relNorm_eq n _ (z.2 (n + 1)).1).trans (z.2 n).2

end NormTower

end Tower

section GaloisNorm

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem relNorm_eq_prod_of_isGalois {E E' : IntermediateField K Ω} (h : E ≤ E') [FiniteDimensional K E']
    [IsGalois K E'] (H : Subgroup Gal(E'/K)) [Fintype H]
    (hH : ∀ g, g ∈ H ↔ ∀ z : E', (z : Ω) ∈ E → (g z : Ω) = z) {y : Ω} (hy : y ∈ E') :
    relNorm h y = ∏ g : H, ((g : Gal(E'/K)) ⟨y, hy⟩ : Ω) := by
  letI := inclAlgebra h
  haveI := isScalarTower_base_inclAlgebra h
  haveI : IsGalois E E' := IsGalois.tower_top_of_isGalois K E E'
  haveI : FiniteDimensional E E' := Module.Finite.of_restrictScalars_finite K E E'
  have hcoe : ∀ e : E, ((algebraMap E E' e : E') : Ω) = e := fun e ↦ rfl
  rw [relNorm_of_mem _ hy, ← hcoe, Algebra.norm_eq_prod_automorphisms, IntermediateField.coe_prod]
  have hmem : ∀ τ : Gal(E'/E), τ.restrictScalars K ∈ H := fun τ ↦ (hH _).mpr fun z hz ↦ by
    obtain ⟨e, rfl⟩ : ∃ e : E, algebraMap E E' e = z := ⟨⟨z, hz⟩, Subtype.ext rfl⟩
    rw [AlgEquiv.restrictScalars_apply, τ.commutes]
  let φ : Gal(E'/E) → H := fun τ ↦ ⟨τ.restrictScalars K, hmem τ⟩
  refine Fintype.prod_bijective φ ⟨fun τ₁ τ₂ h ↦ ?_, fun g ↦ ?_⟩ _ _ fun τ ↦ rfl
  · refine AlgEquiv.ext fun z ↦ ?_
    have := congrArg (fun g : H ↦ ((g : Gal(E'/K)) z)) h
    exact this
  · have hg : ∀ e : E, (g : Gal(E'/K)) (algebraMap E E' e) = algebraMap E E' e := fun e ↦
      Subtype.ext ((hH g).mp g.2 (algebraMap E E' e) (by rw [hcoe]; exact e.2))
    refine ⟨AlgEquiv.ofRingEquiv (f := (g : Gal(E'/K)).toRingEquiv) hg, Subtype.ext ?_⟩
    exact AlgEquiv.ext fun z ↦ rfl

end GaloisNorm

section APF

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
  {L : IntermediateField K Ω} [IsGalois K L]

namespace APFData

variable (d : APFData L)

theorem mem_H_iff (n : ℕ) (g : Gal((d.F (n + 1) : IntermediateField K Ω)/K)) :
    g ∈ d.H n ↔ ∀ z : (d.F (n + 1) : IntermediateField K Ω),
      (z : Ω) ∈ (d.F n : IntermediateField K Ω) → (g z : Ω) = z := by
  constructor
  · intro hg z hz
    have hg' : g ∈ (upperSupFixing K Ω L (d.u n)).map
        (AlgEquiv.restrictNormalHom (upperFieldFG d.apf (d.u (n + 1)) : IntermediateField K Ω)) := by
      rw [map_upperSupFixing d.apf]; exact hg
    obtain ⟨σ, hσ, rfl⟩ := hg'
    rw [← fixingSubgroup_upperField d.apf] at hσ
    exact (AlgEquiv.restrictNormalHom_apply _ σ z).trans
      ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ hz)
  · intro hg
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K)
      (K₁ := (d.F (n + 1) : IntermediateField K Ω)) Ω g
    refine d.restrict_mem_H n ?_
    rw [← fixingSubgroup_upperField d.apf, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨z, rfl⟩ : ∃ z : (d.F (n + 1) : IntermediateField K Ω), (z : Ω) = x :=
      ⟨⟨x, upperField_mono (d.u_mono (Nat.le_succ n)) hx⟩, rfl⟩
    rw [← AlgEquiv.restrictNormalHom_apply]
    exact hg z hx

theorem prod_T_eq (n : ℕ) {y : Ω} (hy : y ∈ (d.F (n + 1) : IntermediateField K Ω)) :
    (∏ σ ∈ d.T n, σ y) =
      ∏ g : d.H n, ((g : Gal((d.F (n + 1) : IntermediateField K Ω)/K)) ⟨y, hy⟩ : Ω) := by
  classical
  rw [T, Finset.prod_image (fun g _ g' _ h ↦ d.lift_injective n h)]
  exact Finset.prod_congr rfl fun g _ ↦ d.lift_apply n g hy

theorem F_le (n : ℕ) : (d.F n : IntermediateField K Ω) ≤ d.F (n + 1) :=
  upperField_mono (d.u_mono (Nat.le_succ n))

theorem relNorm_eq_prod (n : ℕ) {y : Ω} (hy : y ∈ (d.F (n + 1) : IntermediateField K Ω)) :
    relNorm (d.F_le n) y = ∏ σ ∈ d.T n, σ y := by
  rw [d.prod_T_eq n hy]
  exact relNorm_eq_prod_of_isGalois (d.F_le n) (d.H n) (d.mem_H_iff n) hy

theorem isTowerFor (hinf : ¬ FiniteDimensional K L) : (d.tower hinf).IsTowerFor L where
  le n := upperField_le _
  exists_mem x hx := by
    obtain ⟨v, hv⟩ := exists_mem_upperField d.apf hx
    obtain ⟨m, hm⟩ := d.exists_le_u v
    exact ⟨m, upperField_mono hm hv⟩
  relNorm_eq n y hy := d.relNorm_eq_prod n hy

end APFData

end APF

end GroundTheory.PAdicHodge
