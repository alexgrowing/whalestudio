import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductCoboundaryMod
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwIneq

variable {l : ℕ} [Fact l.Prime]

def Ik (c : Coef l) (n : ℕ) : Ideal c.O where
  carrier := {x | ‖(x : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖}
  zero_mem' := by
    show ‖((0 : c.O) : Qbar l)‖ ≤ _
    simp
  add_mem' {a b} ha hb := by
    show ‖((a + b : c.O) : Qbar l)‖ ≤ _
    rw [Subalgebra.coe_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  smul_mem' a x hx := by
    show ‖((a * x : c.O) : Qbar l)‖ ≤ _
    rw [Subalgebra.coe_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (CupCob.norm_le_one_of_mem c a.2)).trans hx

theorem mem_Ik {c : Coef l} {n : ℕ} {x : c.O} : x ∈ Ik c n ↔ ‖(x : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ :=
  Iff.rfl

def Qn (c : Coef l) (n : ℕ) : Type := c.O ⧸ Ik c n

instance (c : Coef l) (n : ℕ) : CommRing (Qn c n) := inferInstanceAs (CommRing (c.O ⧸ Ik c n))
instance (c : Coef l) (n : ℕ) : TopologicalSpace (Qn c n) := ⊥
instance (c : Coef l) (n : ℕ) : DiscreteTopology (Qn c n) := ⟨rfl⟩

def red (c : Coef l) (n : ℕ) : c.O →+* Qn c n := Ideal.Quotient.mk (Ik c n)

theorem red_surjective (c : Coef l) (n : ℕ) : Function.Surjective (red c n) :=
  Ideal.Quotient.mk_surjective

theorem red_eq_zero_iff_mem {c : Coef l} {n : ℕ} (a : c.O) : red c n a = 0 ↔ a ∈ Ik c n :=
  Ideal.Quotient.eq_zero_iff_mem

theorem red_eq_iff {c : Coef l} {n : ℕ} (a b : c.O) : red c n a = red c n b ↔ Cg n (a : Qbar l) (b : Qbar l) := by
  rw [← sub_eq_zero, ← map_sub, red_eq_zero_iff_mem, mem_Ik, Subalgebra.coe_sub]
  rfl

theorem smul_mem_Ik (c : Coef l) (n : ℕ) {a : ℤ_[l]} (ha : a ∈ Ideal.span {(l : ℤ_[l]) ^ n}) (y : c.O) :
    a • y ∈ Ik c n := by
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [mem_Ik, Subalgebra.coe_smul, Algebra.smul_def, norm_mul, map_mul, norm_mul, map_pow, map_natCast]
  have h1 : ‖algebraMap ℤ_[l] (Qbar l) w‖ ≤ 1 := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
    exact PadicInt.norm_le_one w
  have h2 := CupCob.norm_le_one_of_mem c y.2
  calc _ ≤ 1 * ‖((l : ℕ) : Qbar l) ^ n‖ * 1 := by gcongr
    _ = _ := by ring

theorem red_smul (c : Coef l) (n : ℕ) (a : ℤ_[l]) (y : c.O) :
    red c n (a • y) = (PadicInt.toZModPow n a).val • red c n y := by
  rw [← map_nsmul, ← sub_eq_zero, ← map_sub, red_eq_zero_iff_mem]
  have e : a • y - (PadicInt.toZModPow n a).val • y = (a - ((PadicInt.toZModPow n a).val : ℤ_[l])) • y := by
    rw [sub_smul, Nat.cast_smul_eq_nsmul]
  rw [e]
  refine smul_mem_Ik c n ?_ y
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]

theorem kill (c : Coef l) (n : ℕ) (x : Qn c n) : (l ^ n) • x = 0 := by
  obtain ⟨y, rfl⟩ := red_surjective c n x
  rw [← map_nsmul, red_eq_zero_iff_mem]
  have e : (l ^ n) • y = ((l : ℤ_[l]) ^ n) • y := by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [e]
  exact smul_mem_Ik c n (Ideal.mem_span_singleton_self _) y

theorem pow_ne_zero' (n : ℕ) : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero

instance neZeroPow (n : ℕ) : NeZero (l ^ n) := ⟨pow_ne_zero' n⟩

instance (c : Coef l) (n : ℕ) : Module (ZMod (l ^ n)) (Qn c n) := AddCommGroup.zmodModule (kill c n)

instance (c : Coef l) (n : ℕ) : Finite (Qn c n) := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := c.O)
  refine Finite.of_surjective (fun z : Fin k → ZMod (l ^ n) => ∑ i, (z i).val • red c n (s i)) ?_
  intro y
  obtain ⟨x, rfl⟩ := red_surjective c n y
  have hx : x ∈ Submodule.span ℤ_[l] (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).1 hx
  refine ⟨fun i => PadicInt.toZModPow n (a i), ?_⟩
  show ∑ i, _ = _
  rw [← ha, map_sum]
  exact Finset.sum_congr rfl fun i _ => (red_smul c n (a i) (s i)).symm

abbrev Mn (c : Coef l) (n : ℕ) : Type := Fin 2 → Qn c n

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def matQ (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (s : G ℚ Ω) :
    Matrix (Fin 2) (Fin 2) (Qn c n) :=
  Matrix.of fun i j => red c n ⟨mat W s i j, hint s i j⟩

theorem matQ_apply (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (s : G ℚ Ω) (i j : Fin 2) :
    matQ c n W hint s i j = red c n ⟨mat W s i j, hint s i j⟩ := rfl

theorem matQ_one (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) :
    matQ c n W hint 1 = 1 := by
  ext i j
  have e : (⟨mat W 1 i j, hint 1 i j⟩ : c.O) = (1 : Matrix (Fin 2) (Fin 2) c.O) i j := by
    apply Subtype.ext
    simp only [mat, map_one, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply]
    split_ifs <;> simp
  rw [matQ_apply, e, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem matQ_mul (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (s t : G ℚ Ω) :
    matQ c n W hint (s * t) = matQ c n W hint s * matQ c n W hint t := by
  ext i j
  have e : (⟨mat W (s * t) i j, hint _ i j⟩ : c.O) =
      ∑ k, (⟨mat W s i k, hint s i k⟩ : c.O) * ⟨mat W t k j, hint t k j⟩ := by
    apply Subtype.ext
    simp only [mat, map_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply]
    push_cast
    rfl
  rw [matQ_apply, e, map_sum, Matrix.mul_apply]
  simp only [map_mul, matQ_apply]

def rhoG (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) :
    Representation (ZMod (l ^ n)) (G ℚ Ω) (Mn c n) where
  toFun s := (Matrix.mulVecLin (matQ c n W hint s)).toAddMonoidHom.toZModLinearMap (l ^ n)
  map_one' := by
    apply LinearMap.ext
    intro x
    show matQ c n W hint 1 *ᵥ x = x
    rw [matQ_one, Matrix.one_mulVec]
  map_mul' s t := by
    apply LinearMap.ext
    intro x
    show matQ c n W hint (s * t) *ᵥ x = matQ c n W hint s *ᵥ (matQ c n W hint t *ᵥ x)
    rw [matQ_mul, Matrix.mulVec_mulVec]

end GlobalTheory.Ord2.GwIneq

namespace GlobalTheory.Ord2.GwIneq

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem kills_NS {e : ℕ} {S : Finset Pl} {A : ValuationSubring Ω} {W : R2 Ω l} (hW : Nf e S A W) :
    ∀ a ∈ NS Ω (S : Set Pl), W a = 1 := by
  have h := (unramOutside_iff (S : Set Pl) W hW.cont).2 fun v hv B hB σ hσ =>
    hW.unr v (by simpa using hv) B hB (show σ ∈ Ine (F := ℚ) B from hσ)
  exact h

theorem matQ_eq_one (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) {a : G ℚ Ω}
    (ha : W a = 1) : matQ c n W hint a = 1 := by
  rw [← matQ_one c n W hint]
  ext i j
  rw [matQ_apply, matQ_apply]
  congr 2
  simp only [mat, ha, map_one]

def rhoS (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) : Representation (ZMod (l ^ n)) (GS Ω (S : Set Pl)) (Mn c n) :=
  QuotientGroup.lift (NS Ω (S : Set Pl)) (rhoG c n W hint) (fun a ha => by
    apply LinearMap.ext
    intro x
    show matQ c n W hint a *ᵥ x = x
    rw [matQ_eq_one c n W hint (hN a ha), Matrix.one_mulVec])

theorem rhoS_toGS (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (s : G ℚ Ω) (x : Mn c n) :
    rhoS c n W hint S hN (toGS Ω (S : Set Pl) s) x = matQ c n W hint s *ᵥ x := rfl

theorem continuous_matQ_apply (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O)
    (hcont : Continuous W) (i j : Fin 2) : Continuous fun s => matQ c n W hint s i j := by
  have h0 : Continuous fun s => ((W s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp hcont
  have hc : Continuous fun s => mat W s i j := h0.matrix_elem i j
  refine continuous_discrete_rng.2 fun y => ?_
  obtain ⟨z, rfl⟩ := red_surjective c n y
  have e : (fun s => matQ c n W hint s i j) ⁻¹' {red c n z} =
      (fun s => mat W s i j) ⁻¹' Metric.closedBall (z : Qbar l) ‖((l : ℕ) : Qbar l) ^ n‖ := by
    ext s
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_closedBall, dist_eq_norm, matQ_apply]
    exact red_eq_iff _ _
  rw [e]
  have hne : ‖((l : ℕ) : Qbar l) ^ n‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  exact (IsUltrametricDist.isOpen_closedBall _ hne).preimage hc

theorem contAction_rhoS (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (hcont : Continuous W) : ReciprocityTheory.Gal.ContAction (rhoS c n W hint S hN) := by
  unfold ReciprocityTheory.Gal.ContAction
  rw [continuous_prod_of_discrete_right]
  intro x
  rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
  show Continuous fun s => matQ c n W hint s *ᵥ x
  refine continuous_pi fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact ((continuous_matQ_apply c n W hint hcont i 0).mul continuous_const).add
    ((continuous_matQ_apply c n W hint hcont i 1).mul continuous_const)

variable [IsAlgClosure ℚ Ω]

open Classical in

def Av (A : ValuationSubring Ω) (S : Finset Pl) (v : S) : ValuationSubring Ω :=
  if IsPlaceOver A v.1 then A else placeOf Ω v.1

theorem isPlaceOver_Av (A : ValuationSubring Ω) (S : Finset Pl) (v : S) : IsPlaceOver (Av A S v) v.1 := by
  unfold Av
  split_ifs with h
  · exact h
  · exact isPlaceOver_placeOf Ω v.1

def ordZ (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (B : ValuationSubring Ω) :
    Submodule (ZMod (l ^ n)) (Dec (F := ℚ) B → Mn c n) where
  carrier := {f | ∃ x : Qn c n, ∀ s : Dec (F := ℚ) B, f s 1 = matQ c n W hint s 1 1 * x - x}
  zero_mem' := ⟨0, fun s => by simp⟩
  add_mem' := by
    rintro f g ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x + y, fun s => by simp only [Pi.add_apply, hx, hy]; ring⟩
  smul_mem' k f := by
    rintro ⟨x, hx⟩
    refine ⟨k • x, fun s => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ZMod (l ^ n)) = k := ⟨k.val, ZMod.natCast_zmod_val k⟩
    simp only [Pi.smul_apply, hx, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    ring

theorem mem_ordZ {c : Coef l} {n : ℕ} {W : R2 Ω l} {hint : ∀ s i j, mat W s i j ∈ c.O} {B : ValuationSubring Ω}
    (f : Dec (F := ℚ) B → Mn c n) :
    f ∈ ordZ c n W hint B ↔ ∃ x : Qn c n, ∀ s : Dec (F := ℚ) B, f s 1 = matQ c n W hint s 1 1 * x - x := Iff.rfl

def ordCond (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (B : ValuationSubring Ω) :
    Submodule (ZMod (l ^ n)) (H1 ((rhoS c n W hint S hN).comp (locHom (S : Set Pl) B))) :=
  ((ordZ c n W hint B).comap (Z1 ((rhoS c n W hint S hN).comp (locHom (S : Set Pl) B))).subtype).map
    (Submodule.mkQ _)

open Classical in

def Lc (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (A : ValuationSubring Ω) :
    LocCond (rhoS c n W hint S hN) (locFam S (Av A S)) := fun v =>
  if IsPlaceOver A v.1 then ordCond c n W hint S hN (Av A S v)
  else H1ur ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))
    ((Ine (F := ℚ) (Av A S v)).subgroupOf (Dec (F := ℚ) (Av A S v)))

def SelG (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (A : ValuationSubring Ω) :
    Submodule (ZMod (l ^ n)) (H1 (rhoS c n W hint S hN)) :=
  Sel (rhoS c n W hint S hN) (locFam S (Av A S)) (continuous_locFam S (Av A S)) (Lc c n W hint S hN A)

def SelD (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (A : ValuationSubring Ω) (hcont : Continuous W)
    (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ) :
    Submodule (ZMod (l ^ n)) (H1 (twDual μ (rhoS c n W hint S hN))) :=
  Sel (twDual μ (rhoS c n W hint S hN)) (locFam S (Av A S)) (continuous_locFam S (Av A S))
    (perpCond μ (rhoS c n W hint S hN) (locFam S (Av A S))
      (fun v => (contAction_rhoS c n W hint S hN hcont).comp' (continuous_locFam S (Av A S) v))
      (Lc c n W hint S hN A))

end GlobalTheory.Ord2.GwIneq
