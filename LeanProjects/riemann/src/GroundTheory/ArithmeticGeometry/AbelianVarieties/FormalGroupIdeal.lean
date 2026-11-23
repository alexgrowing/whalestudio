import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupInverse

namespace GroundTheory.Arith.Abelian

noncomputable section

def AdicRing (𝒪 : Type*) : Type _ := 𝒪

namespace AdicRing

variable (𝒪 : Type*) [CommRing 𝒪]

instance : CommRing (AdicRing 𝒪) := inferInstanceAs (CommRing 𝒪)

instance : Algebra 𝒪 (AdicRing 𝒪) := inferInstanceAs (Algebra 𝒪 𝒪)

def equiv : 𝒪 ≃+* AdicRing 𝒪 := RingEquiv.refl 𝒪

variable [IsLocalRing 𝒪]

instance : WithIdeal (AdicRing 𝒪) := ⟨IsLocalRing.maximalIdeal 𝒪⟩

variable [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]

theorem completeSpace_and_t2Space : CompleteSpace (AdicRing 𝒪) ∧ T2Space (AdicRing 𝒪) :=
  (IsAdic.isAdicComplete_iff (I := (WithIdeal.i : Ideal (AdicRing 𝒪))) rfl).1
    (inferInstanceAs (IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪))

instance : CompleteSpace (AdicRing 𝒪) := (completeSpace_and_t2Space 𝒪).1

instance : T2Space (AdicRing 𝒪) := (completeSpace_and_t2Space 𝒪).2

end AdicRing

section Eval

variable {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪]

def psEvalAt {σ : Type*} (f : MvPowerSeries σ 𝒪) (a : σ → 𝒪) : 𝒪 :=
  letI : UniformSpace 𝒪 := ⊥
  (AdicRing.equiv 𝒪).symm
    (MvPowerSeries.eval₂ (algebraMap 𝒪 (AdicRing 𝒪)) (fun i => AdicRing.equiv 𝒪 (a i)) f)

theorem hasEval_adicRing {σ : Type*} [Finite σ] {a : σ → 𝒪}
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal 𝒪) :
    MvPowerSeries.HasEval (fun i => AdicRing.equiv 𝒪 (a i)) :=
  ⟨fun i => WithIdeal.isTopologicallyNilpotent_of_mem (ha i),
    by rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩

theorem psEvalAt_X {σ : Type*} (a : σ → 𝒪) (i : σ) : psEvalAt (MvPowerSeries.X i) a = a i := by
  simp [psEvalAt, MvPowerSeries.eval₂_X]

theorem psEvalAt_C {σ : Type*} (a : σ → 𝒪) (r : 𝒪) : psEvalAt (MvPowerSeries.C r) a = r := by
  simp [psEvalAt, MvPowerSeries.eval₂_C]
  rfl

variable [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]

def evAlgHom {σ : Type*} [Finite σ] (a : σ → 𝒪) (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal 𝒪) :
    MvPowerSeries σ 𝒪 →ₐ[𝒪] 𝒪 :=
  letI : UniformSpace 𝒪 := ⊥
  haveI : DiscreteUniformity 𝒪 := ⟨rfl⟩
  have hφ : Continuous (algebraMap 𝒪 (AdicRing 𝒪)) := by
    rw [UniformSpace.toTopologicalSpace_bot]; exact continuous_bot
  { (AdicRing.equiv 𝒪).symm.toRingHom.comp (MvPowerSeries.eval₂Hom hφ (hasEval_adicRing ha)) with
    commutes' := fun r => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, MvPowerSeries.coe_eval₂Hom]
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        MvPowerSeries.eval₂_C]
      rfl }

theorem evAlgHom_apply {σ : Type*} [Finite σ] (a : σ → 𝒪)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal 𝒪) (f : MvPowerSeries σ 𝒪) :
    evAlgHom a ha f = psEvalAt f a := by
  simp [evAlgHom, psEvalAt, MvPowerSeries.coe_eval₂Hom]

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
theorem isClosed_maximalIdeal_adicRing :
    IsClosed ((WithIdeal.i : Ideal (AdicRing 𝒪)) : Set (AdicRing 𝒪)) := by
  have hopen : IsOpen ((WithIdeal.i : Ideal (AdicRing 𝒪)) : Set (AdicRing 𝒪)) := by
    refine (WithIdeal.i : Ideal (AdicRing 𝒪)).toAddSubgroup.isOpen_of_mem_nhds (g := 0) ?_
    have := (Ideal.hasBasis_nhds_zero_adic (WithIdeal.i : Ideal (AdicRing 𝒪))).mem_of_mem
      (i := 1) trivial
    simpa using this
  exact AddSubgroup.isClosed_of_isOpen (WithIdeal.i : Ideal (AdicRing 𝒪)).toAddSubgroup hopen

theorem psEvalAt_mem {σ : Type*} [Finite σ] {f : MvPowerSeries σ 𝒪}
    (hf : MvPowerSeries.constantCoeff f ∈ IsLocalRing.maximalIdeal 𝒪) {a : σ → 𝒪}
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal 𝒪) :
    psEvalAt f a ∈ IsLocalRing.maximalIdeal 𝒪 := by
  let _ : UniformSpace 𝒪 := ⊥
  have _ : DiscreteUniformity 𝒪 := ⟨rfl⟩
  have hφ : Continuous (algebraMap 𝒪 (AdicRing 𝒪)) := by
    rw [UniformSpace.toTopologicalSpace_bot]; exact continuous_bot
  have h := MvPowerSeries.hasSum_eval₂ hφ (hasEval_adicRing ha) f
  have hmem : MvPowerSeries.eval₂ (algebraMap 𝒪 (AdicRing 𝒪)) (fun i => AdicRing.equiv 𝒪 (a i)) f ∈
      (WithIdeal.i : Ideal (AdicRing 𝒪)) := by
    rw [HasSum] at h
    refine isClosed_maximalIdeal_adicRing.mem_of_tendsto h (Filter.Eventually.of_forall fun s => ?_)
    refine Ideal.sum_mem _ fun d _ => ?_
    by_cases hd : d = 0
    · subst hd
      refine Ideal.mul_mem_right _ _ ?_
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hf
    · obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hd
      refine Ideal.mul_mem_left _ _ ?_
      rw [Finsupp.prod]
      refine Ideal.prod_mem _ (i := i) (Finsupp.mem_support_iff.mpr hi) ?_
      exact Ideal.pow_mem_of_mem _ (ha i) _ (Nat.pos_of_ne_zero hi)
  exact hmem

theorem psEvalAt_subst {σ τ : Type*} [Finite σ] [Finite τ] {g : σ → MvPowerSeries τ 𝒪}
    (hg : MvPowerSeries.HasSubst g) (f : MvPowerSeries σ 𝒪) {a : τ → 𝒪}
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal 𝒪) :
    psEvalAt (MvPowerSeries.subst g f) a = psEvalAt f (fun s => psEvalAt (g s) a) := by
  let _ : UniformSpace 𝒪 := ⊥
  have _ : DiscreteUniformity 𝒪 := ⟨rfl⟩
  simp only [psEvalAt]
  rw [MvPowerSeries.eval₂_subst hg (hasEval_adicRing ha)]
  rfl

theorem psEvalAt_powerSeries_subst {τ : Type*} [Finite τ] {g : MvPowerSeries τ 𝒪}
    (hg : PowerSeries.HasSubst g) (f : PowerSeries 𝒪) {a : τ → 𝒪}
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal 𝒪) :
    psEvalAt (PowerSeries.subst g f) a = psEvalAt f (fun _ => psEvalAt g a) := by
  rw [PowerSeries.subst, psEvalAt_subst hg.const f ha]

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
theorem mem_maximalIdeal_of_isNilpotent {x : 𝒪} (hx : IsNilpotent x) :
    x ∈ IsLocalRing.maximalIdeal 𝒪 := by
  obtain ⟨n, hn⟩ := hx
  exact (IsLocalRing.maximalIdeal.isMaximal 𝒪).isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)

def MaxIdealPoint (_F : FormalGroup 𝒪) : Type _ := {x : 𝒪 // x ∈ IsLocalRing.maximalIdeal 𝒪}

variable {F : FormalGroup 𝒪}

namespace MaxIdealPoint

def val (x : MaxIdealPoint F) : 𝒪 := x.1

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
theorem val_mem (x : MaxIdealPoint F) : x.val ∈ IsLocalRing.maximalIdeal 𝒪 := x.2

def mk (x : 𝒪) (hx : x ∈ IsLocalRing.maximalIdeal 𝒪) : MaxIdealPoint F := ⟨x, hx⟩

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
@[simp] theorem val_mk (x : 𝒪) (hx : x ∈ IsLocalRing.maximalIdeal 𝒪) :
    (mk x hx : MaxIdealPoint F).val = x := rfl

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
@[ext] theorem ext {x y : MaxIdealPoint F} (h : x.val = y.val) : x = y := Subtype.ext h

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
theorem val_injective : Function.Injective (val : MaxIdealPoint F → 𝒪) := fun _ _ => ext

instance : Zero (MaxIdealPoint F) := ⟨mk 0 (zero_mem _)⟩

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
@[simp] theorem val_zero : (0 : MaxIdealPoint F).val = 0 := rfl

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
theorem pair_mem (x y : MaxIdealPoint F) :
    ∀ i, (![x.val, y.val] : Fin 2 → 𝒪) i ∈ IsLocalRing.maximalIdeal 𝒪 := by
  intro i; fin_cases i
  exacts [x.val_mem, y.val_mem]

instance : Add (MaxIdealPoint F) where
  add x y := mk (psEvalAt F.toPowerSeries ![x.val, y.val])
    (psEvalAt_mem (by rw [F.zero_constantCoeff]; exact zero_mem _) (pair_mem x y))

instance : Neg (MaxIdealPoint F) where
  neg x := mk (psEvalAt (GroundTheory.LocalField.FormalGroup.inv F : MvPowerSeries Unit 𝒪) fun _ => x.val)
    (psEvalAt_mem (by
      rw [show MvPowerSeries.constantCoeff (GroundTheory.LocalField.FormalGroup.inv F : MvPowerSeries Unit 𝒪)
        = 0 from GroundTheory.LocalField.FormalGroup.constantCoeff_inv F]; exact zero_mem _)
      fun _ => x.val_mem)

theorem val_add (x y : MaxIdealPoint F) :
    (x + y).val = psEvalAt F.toPowerSeries ![x.val, y.val] := rfl

theorem val_neg (x : MaxIdealPoint F) :
    (-x).val = psEvalAt (GroundTheory.LocalField.FormalGroup.inv F : MvPowerSeries Unit 𝒪) fun _ => x.val :=
  rfl

def evalPoint {σ : Type*} [Finite σ] (x : σ → MaxIdealPoint F) (p : F.Point σ) : MaxIdealPoint F :=
  mk (psEvalAt p.val fun i => (x i).val)
    (psEvalAt_mem (mem_maximalIdeal_of_isNilpotent p.prop) fun i => (x i).val_mem)

def pointVar {σ : Type*} (i : σ) : F.Point σ :=
  ⟨MvPowerSeries.X i, by simp [PowerSeries.HasSubst]⟩

theorem evalPoint_pointVar {σ : Type*} [Finite σ] (x : σ → MaxIdealPoint F) (i : σ) :
    evalPoint x (pointVar i) = x i :=
  ext (psEvalAt_X _ i)

theorem evalPoint_zero {σ : Type*} [Finite σ] (x : σ → MaxIdealPoint F) :
    evalPoint x (0 : F.Point σ) = 0 := by
  apply ext
  change psEvalAt 0 _ = 0
  rw [← evAlgHom_apply _ (fun i => (x i).val_mem), map_zero]

theorem evalPoint_add {σ : Type*} [Finite σ] (x : σ → MaxIdealPoint F) (p q : F.Point σ) :
    evalPoint x (p + q) = evalPoint x p + evalPoint x q := by
  apply ext
  change psEvalAt (p + q).val _ = _
  rw [FormalGroup.add_apply, psEvalAt_subst (GroundTheory.LocalField.FormalGroup.point_hasSubst_pair p q)
    _ fun i => (x i).val_mem, val_add]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem evalPoint_neg {σ : Type*} [Finite σ] (x : σ → MaxIdealPoint F) (p : F.Point σ) :
    evalPoint x (-p) = -evalPoint x p := by
  apply ext
  change psEvalAt (-p).val _ = _
  rw [GroundTheory.LocalField.FormalGroup.neg_point_val,
    psEvalAt_powerSeries_subst p.prop _ fun i => (x i).val_mem]
  rfl

instance instAddGroup : AddGroup (MaxIdealPoint F) where
  add_assoc a b c := by
    have h := congrArg (evalPoint ![a, b, c])
      (add_assoc (pointVar 0 : F.Point (Fin 3)) (pointVar 1) (pointVar 2))
    simpa [evalPoint_add, evalPoint_pointVar] using h
  zero_add a := by
    have h := congrArg (evalPoint fun _ : Unit => a) (zero_add (pointVar () : F.Point Unit))
    simpa only [evalPoint_add, evalPoint_pointVar, evalPoint_zero] using h
  add_zero a := by
    have h := congrArg (evalPoint fun _ : Unit => a) (add_zero (pointVar () : F.Point Unit))
    simpa only [evalPoint_add, evalPoint_pointVar, evalPoint_zero] using h
  neg_add_cancel a := by
    have h := congrArg (evalPoint fun _ : Unit => a) (neg_add_cancel (pointVar () : F.Point Unit))
    simpa only [evalPoint_add, evalPoint_neg, evalPoint_pointVar, evalPoint_zero] using h
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instAddCommGroup [F.IsComm] : AddCommGroup (MaxIdealPoint F) where
  add_comm a b := by
    have h := congrArg (evalPoint ![a, b])
      (add_comm (pointVar 0 : F.Point (Fin 2)) (pointVar 1))
    simpa [evalPoint_add, evalPoint_pointVar] using h

end MaxIdealPoint

end Eval

end

end GroundTheory.Arith.Abelian
