import Mathlib
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

def Steps (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  Cls k ∧ MulCls k ∧ Assoc k ∧ Comm k ∧ One k ∧ ProdList k ∧ Tri k ∧ MultOne k ∧ JCls k ∧ JSeg k ∧ AltSum k

def R (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Type 1 := GrothGL k

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace GrothendieckRing

section Bil

variable {ι M : Type*} [AddCommGroup M]

def bil (C : ι → ι → M) (a b : ι →₀ ℤ) : M := a.sum fun x m => b.sum fun y n => (m * n) • C x y

variable (C : ι → ι → M)

theorem bil_add_right (a b c : ι →₀ ℤ) : bil C a (b + c) = bil C a b + bil C a c := by
  unfold bil
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun x _ => ?_
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [mul_add, add_smul])

theorem bil_add_left (a b c : ι →₀ ℤ) : bil C (a + b) c = bil C a c + bil C b c := by
  unfold bil
  refine Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => ?_)
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun y _ => ?_
  rw [add_mul, add_smul]

theorem bil_zero_left (b : ι →₀ ℤ) : bil C 0 b = 0 := by
  simp [bil]

theorem bil_zero_right (a : ι →₀ ℤ) : bil C a 0 = 0 := by
  simp [bil]

theorem bil_smul_left (z : ℤ) (a b : ι →₀ ℤ) : bil C (z • a) b = z • bil C a b := by
  unfold bil
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.smul_sum]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [Finsupp.smul_sum]
  refine Finsupp.sum_congr fun y _ => ?_
  rw [smul_eq_mul, mul_assoc, mul_smul]

theorem bil_smul_right (z : ℤ) (a b : ι →₀ ℤ) : bil C a (z • b) = z • bil C a b := by
  unfold bil
  rw [Finsupp.smul_sum]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.smul_sum]
  refine Finsupp.sum_congr fun y _ => ?_
  rw [smul_eq_mul, mul_left_comm, mul_smul]

theorem bil_single (x y : ι) : bil C (Finsupp.single x 1) (Finsupp.single y 1) = C x y := by
  simp [bil, Finsupp.sum_single_index]

theorem bil_comm (hC : ∀ x y, C x y = C y x) (a b : ι →₀ ℤ) : bil C a b = bil C b a := by
  unfold bil
  rw [Finsupp.sum_comm]
  refine Finsupp.sum_congr fun y _ => Finsupp.sum_congr fun x _ => ?_
  rw [mul_comm, hC]

theorem single_eq_smul_single (x : ι) (m : ℤ) : (Finsupp.single x m : ι →₀ ℤ) = m • Finsupp.single x 1 := by
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

end Bil

section BilAssoc

variable {ι : Type*} (C : ι → ι → ι →₀ ℤ)

theorem bil_assoc (hA : ∀ x y z, bil C (bil C (Finsupp.single x 1) (Finsupp.single y 1)) (Finsupp.single z 1) =
      bil C (Finsupp.single x 1) (bil C (Finsupp.single y 1) (Finsupp.single z 1))) (a b c : ι →₀ ℤ) :
    bil C (bil C a b) c = bil C a (bil C b c) := by
  induction a using Finsupp.induction_linear with
  | zero => simp only [bil_zero_left]
  | add a a' ha ha' => rw [bil_add_left, bil_add_left, bil_add_left, ha, ha']
  | single x m =>
    simp only [single_eq_smul_single x m, bil_smul_left]
    congr 1
    induction b using Finsupp.induction_linear with
    | zero => simp only [bil_zero_left, bil_zero_right]
    | add b b' hb hb' => rw [bil_add_right, bil_add_left, hb, hb', bil_add_left, bil_add_right]
    | single y n =>
      simp only [single_eq_smul_single y n, bil_smul_left, bil_smul_right]
      congr 1
      induction c using Finsupp.induction_linear with
      | zero => simp only [bil_zero_right]
      | add c c' hc hc' => rw [bil_add_right, bil_add_right, hc, hc', bil_add_right]
      | single z p =>
        simp only [single_eq_smul_single z p, bil_smul_right]
        congr 1
        exact hA x y z

theorem bil_one (u : ι →₀ ℤ) (h : ∀ x, bil C u (Finsupp.single x 1) = Finsupp.single x 1) (a : ι →₀ ℤ) :
    bil C u a = a := by
  induction a using Finsupp.induction_linear with
  | zero => rw [bil_zero_right]
  | add a a' ha ha' => rw [bil_add_right, ha, ha']
  | single x m => rw [single_eq_smul_single, bil_smul_right, h]

end BilAssoc

def cm (x y : IrrGL k) : GrothGL k := cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y))

theorem mulR_eq (a b : GrothGL k) : mulR a b = bil cm a b := rfl

theorem sg_eq (x : IrrGL k) : sg x = Finsupp.single x 1 := rfl

theorem mulR_add (a b c : GrothGL k) : mulR a (b + c) = mulR a b + mulR a c := bil_add_right _ a b c

theorem add_mulR (a b c : GrothGL k) : mulR (a + b) c = mulR a c + mulR b c := bil_add_left _ a b c

theorem zero_mulR (a : GrothGL k) : mulR 0 a = 0 := bil_zero_left _ a

theorem mulR_zero (a : GrothGL k) : mulR a 0 = 0 := bil_zero_right _ a

theorem mulR_comm' [Fact (Comm k)] (a b : GrothGL k) : mulR a b = mulR b a := by
  rw [mulR_eq, mulR_eq]
  exact bil_comm _ (fun x y => (Fact.out : Comm k) x y) a b

theorem mulR_assoc' [Fact (Assoc k)] (a b c : GrothGL k) : mulR (mulR a b) c = mulR a (mulR b c) := by
  simp only [mulR_eq]
  refine bil_assoc _ (fun x y z => ?_) a b c
  have h := (Fact.out : Assoc k) x y z
  simp only [mulR_eq, sg_eq] at h
  exact h

theorem unit_mulR [Fact (One k)] (a : GrothGL k) : mulR (GrothGL.unit k) a = a := by
  rw [mulR_eq]
  refine bil_one _ _ (fun x => ?_) a
  have h := (Fact.out : One k) x
  simp only [mulR_eq, sg_eq] at h
  exact h

end GrothendieckRing

open GrothendieckRing

variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

instance instCommRingR : CommRing (R k) :=
  { (inferInstanceAs (AddCommGroup (GrothGL k)) : AddCommGroup (R k)) with
    mul := fun a b => mulR a b
    one := GrothGL.unit k
    left_distrib := fun a b c => mulR_add a b c
    right_distrib := fun a b c => add_mulR a b c
    zero_mul := fun a => zero_mulR a
    mul_zero := fun a => mulR_zero a
    mul_assoc := fun a b c => mulR_assoc' a b c
    one_mul := fun a => unit_mulR a
    mul_one := fun a => (mulR_comm' _ _).trans (unit_mulR a)
    mul_comm := fun a b => mulR_comm' a b }

def toR : GrothGL k ≃+ R k := { Equiv.refl _ with map_add' := fun _ _ => rfl }

theorem toR_mulR (a b : GrothGL k) : toR (mulR a b) = toR a * toR b := rfl

theorem toR_unit : toR (GrothGL.unit k) = 1 := rfl

def phiOf (f : Segment k → IrrGL k) : MvPolynomial (Segment k) ℤ →+* R k :=
  MvPolynomial.eval₂Hom (Int.castRingHom (R k)) fun Δ => toR (sg (f Δ))

theorem phiOf_X (f : Segment k → IrrGL k) (Δ : Segment k) : phiOf f (MvPolynomial.X Δ) = toR (sg (f Δ)) :=
  MvPolynomial.eval₂Hom_X' _ _ _

end CompanionTheory.Groth

end
