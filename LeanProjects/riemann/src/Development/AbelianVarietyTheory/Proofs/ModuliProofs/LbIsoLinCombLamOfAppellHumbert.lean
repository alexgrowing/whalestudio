import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoOfSameFactor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

namespace SharpBundle

def IsFrameAlong {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (L : LB X)
    (fr : L.ι → (Fin g → ℂ) → ℂ) : Prop :=
  (∀ i, DifferentiableOn ℂ (fr i) {z | ⊤ ≤ e z ⁻¹ᵁ L.U i}) ∧ (∀ i z, ⊤ ≤ e z ⁻¹ᵁ L.U i → fr i z ≠ 0) ∧
    ∀ i j z, ⊤ ≤ e z ⁻¹ᵁ (L.U i ⊓ L.U j) → fr i z = valAt' (e z) (L.U i ⊓ L.U j) (L.g i j).val * fr j z

theorem differentiableOn_finset_prod {E κ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E}
    (s : Finset κ) (φ : κ → E → ℂ) (h : ∀ k, DifferentiableOn ℂ (φ k) S) :
    DifferentiableOn ℂ (fun z => ∏ k ∈ s, φ k z) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

theorem IsFrameAlong.linComb {g : ℕ} {X Y : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (L : LB Y) {K : Type}
    [Fintype K] (φ : K → (X ⟶ Y)) (ε : K → ℤ) (fr : K → L.ι → (Fin g → ℂ) → ℂ)
    (h : ∀ k, IsFrameAlong (fun z => e z ≫ φ k) L (fr k)) :
    IsFrameAlong e (LB.LinComb L φ ε) (fun (j : K → L.ι) z => ∏ k, fr k (j k) z ^ ε k) := by
  have hc : ∀ (j : K → L.ι) z, ⊤ ≤ e z ⁻¹ᵁ LB.wchart L φ j → ∀ k, ⊤ ≤ (e z ≫ φ k) ⁻¹ᵁ L.U (j k) :=
    fun j z hz => (CubeValues.le_preimage_wchart (e z) L φ j).1 hz
  refine ⟨fun j => ?_, fun j z hz => ?_, fun j j' z hz => ?_⟩
  · refine differentiableOn_finset_prod Finset.univ (fun k (z : Fin g → ℂ) => fr k (j k) z ^ ε k) fun k => ?_
    refine DifferentiableOn.zpow ?_ (Or.inl fun z hz => (h k).2.1 _ _ (hc j z hz k))
    exact ((h k).1 (j k)).mono fun z hz => hc j z hz k
  · exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ ((h k).2.1 _ _ (hc j z hz k))
  · obtain ⟨h1, h2⟩ := (top_le_preimage_inf (e z) _ _).1 hz
    have e1 := CubeValues.val_linComb (e z) valAt'_rules L φ ε j j' h1 h2
    refine Eq.trans ?_ (congrArg (· * ∏ k, fr k (j' k) z ^ ε k) e1.symm)
    show _ = (∏ k, _) * _
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← mul_zpow]
    exact congrArg (· ^ ε k) ((h k).2.2 (j k) (j' k) z
      ((top_le_preimage_inf _ _ _).2 ⟨hc j z h1 k, hc j' z h2 k⟩))

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem isFrameAlong_comp {n : ℕ} (F : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    IsFrameAlong (fun z => (u.ex (F z)).left) L (fun i z => u.fr i (F z)) :=
  ⟨fun i => (u.fr_hol i).comp (LinearMap.toContinuousLinearMap F).differentiable.differentiableOn fun _ hz => hz,
    fun i z hz => u.fr_ne i (F z) hz, fun i j z hz => u.fr_compat i j (F z) hz⟩

def withFrame {M : LB A.left} (fr : M.ι → (Fin g → ℂ) → ℂ) (h : IsFrameAlong (fun z => (u.ex z).left) M fr) :
    HolUnif A M g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fr
  fr_hol := h.1
  fr_ne := h.2.1
  fr_compat := h.2.2

theorem hermForm_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm, add_dotProduct]

theorem hermForm_add_right (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp [hermForm, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_swap {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = hermForm Hm z w - 2 * Complex.I * ((hermForm Hm z w).im : ℂ) := by
  have h : hermForm Hm w z = starRingEnd ℂ (hermForm Hm z w) := by
    change _ = star (hermForm Hm z w)
    unfold hermForm
    rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq, Matrix.dotProduct_mulVec]
  rw [h]
  apply Complex.ext <;> simp
  ring

variable {u} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem ah_step (h : u.IsAH Hm χ) (l : u.Λ) (i : L.ι) (z : Fin g → ℂ) (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) :
    u.fr i z = χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * u.fr i (z + l) :=
  h.2.2.2 l i z hz

theorem ah_step_add (h : u.IsAH Hm χ) (l m : u.Λ) (i : L.ι) (z : Fin g → ℂ) (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) :
    u.fr i z = χ l * χ m * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l +
      (Real.pi * hermForm Hm (z + l) m + Real.pi / 2 * hermForm Hm m m)) * u.fr i (z + l + m) := by
  have h2 := ah_step h m i (z + l) (by rw [CubeValues.ex_add_period u z l l.2]; exact hz)
  rw [ah_step h l i z hz, h2, Complex.exp_add _ (_ + _)]
  ring

theorem prod_finset_fin_two' (f : Finset (Fin 2) → ℂ) :
    ∏ I : ULift.{0} (Finset (Fin 2)), f I.down = f ∅ * f {0} * f {1} * f {0, 1} := by
  rw [Fintype.prod_equiv Equiv.ulift (fun I : ULift.{0} (Finset (Fin 2)) => f I.down) f fun I => rfl]
  have : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [this, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

theorem lam_step (h : u.IsAH Hm χ) (j : ULift.{0} (Finset (Fin 2)) → L.ι) (x x' : Fin 2 → Fin g → ℂ) (l : Fin 2 → u.Λ)
    (hx' : ∀ a, x' a = x a + l a)
    (hx : ∀ I, ⊤ ≤ (u.ex (∑ a ∈ I.down, x a)).left ⁻¹ᵁ L.U (j I)) :
    ∏ I : ULift.{0} (Finset (Fin 2)), u.fr (j I) (∑ a ∈ I.down, x a) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      Complex.exp (Real.pi * Complex.I * ((hermForm Hm (l 0) (l 1)).im : ℂ) +
        (Real.pi * (hermForm Hm (x 0) (l 1) + hermForm Hm (x 1) (l 0)) +
          Real.pi / 2 * (hermForm Hm (l 0) (l 1) + hermForm Hm (l 1) (l 0)))) *
      ∏ I : ULift.{0} (Finset (Fin 2)), u.fr (j I) (∑ a ∈ I.down, x' a) ^ ((-1 : ℤ) ^ (2 - I.down.card)) := by
  rw [prod_finset_fin_two' fun I => u.fr (j ⟨I⟩) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (2 - I.card)),
    prod_finset_fin_two' fun I => u.fr (j ⟨I⟩) (∑ a ∈ I, x' a) ^ ((-1 : ℤ) ^ (2 - I.card))]
  have c01 : ({0, 1} : Finset (Fin 2)).card = 2 := rfl
  have s01 : ∀ y : Fin 2 → Fin g → ℂ, ∑ a ∈ ({0, 1} : Finset (Fin 2)), y a = y 0 + y 1 := fun y =>
    Finset.sum_pair (by decide)
  have h0 := hx ⟨{0}⟩
  have h1 := hx ⟨{1}⟩
  have h01 := hx ⟨{0, 1}⟩
  simp only [Finset.sum_singleton, s01] at h0 h1 h01
  have e0 := ah_step h (l 0) _ _ h0
  have e1 := ah_step h (l 1) _ _ h1
  have e01 := ah_step_add h (l 0) (l 1) _ _ h01
  have n0 : χ (l 0) ≠ 0 := fun e => by simpa [e] using h.2.2.1 (l 0)
  have n1 : χ (l 1) ≠ 0 := fun e => by simpa [e] using h.2.2.1 (l 1)
  have hs : x 0 + l 0 + (x 1 + l 1) = x 0 + x 1 + l 0 + l 1 := by abel
  simp only [Finset.sum_singleton, s01, Finset.sum_empty, Finset.card_empty, Finset.card_singleton, c01, hx', hs]
  norm_num
  rw [e0, e1, e01]
  have key : Complex.exp (Real.pi * hermForm Hm (x 0 + x 1) (l 0) + Real.pi / 2 * hermForm Hm (l 0) (l 0) +
      (Real.pi * hermForm Hm (x 0 + x 1 + l 0) (l 1) + Real.pi / 2 * hermForm Hm (l 1) (l 1))) =
      Complex.exp (Real.pi * Complex.I * ((hermForm Hm (l 0) (l 1)).im : ℂ) +
        (Real.pi * (hermForm Hm (x 0) (l 1) + hermForm Hm (x 1) (l 0)) +
          Real.pi / 2 * (hermForm Hm (l 0) (l 1) + hermForm Hm (l 1) (l 0)))) *
      Complex.exp (Real.pi * hermForm Hm (x 0) (l 0) + Real.pi / 2 * hermForm Hm (l 0) (l 0)) *
      Complex.exp (Real.pi * hermForm Hm (x 1) (l 1) + Real.pi / 2 * hermForm Hm (l 1) (l 1)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [hermForm_add_left]
    rw [hermForm_swap h.1 (l 0) (l 1)]
    ring
  rw [key]
  have := Complex.exp_ne_zero (Real.pi * hermForm Hm (x 0) (l 0) + Real.pi / 2 * hermForm Hm (l 0) (l 0))
  have := Complex.exp_ne_zero (Real.pi * hermForm Hm (x 1) (l 1) + Real.pi / 2 * hermForm Hm (l 1) (l 1))
  simp only [mul_inv]
  field_simp

theorem sum_symmetrise {n : ℕ} (W : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → Fin n → ℂ) :
    ∑ uv : Fin n × Fin n, (W uv.1 uv.2 : ℂ) * (b uv.1 uv.2 + b uv.2 uv.1) =
      ∑ i, ∑ j, ((W + W.transpose) i j : ℂ) * b i j := by
  simp only [Fintype.sum_prod_type, Matrix.add_apply, Matrix.transpose_apply, Int.cast_add, mul_add, add_mul,
    Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

end SharpBundle

open SharpBundle in

theorem lbIso_linComb_lam_of_appellHumbert : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (P₀ : Out.PolAV (Sp ℂ)) (u₀ : HolUnif P₀.A P₀.L P₀.g) (H₀ : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ₀ : u₀.Λ → ℂ) (pr : Fin 8 → (P.A ⟶ P₀.A)) (R : Fin 8 → ((Fin P.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ))), u.IsAH Hm χ → u₀.IsAH H₀ χ₀ → (∀ i z, u₀.ex (R i z) = u.ex z ≫ pr i) → (∀ z w, hermForm Hm z w = ∑ i, ∑ j, ((W + W.transpose) i j : ℂ) * hermForm H₀ (R i z) (R j w)) → (∀ l : u.Λ, χ l = Complex.exp (Real.pi * Complex.I * ∑ i, ∑ j, (W i j : ℂ) * ((hermForm H₀ (R i l) (R j l)).im : ℂ))) → LBIso P.L (LB.LinComb (abelian₂ P₀.A P₀.L) (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  intro h1 h2 h3 h4 W P u Hm χ P₀ u₀ H₀ χ₀ pr R hu hu₀ hR hH hχ
  let r : Fin 8 × Fin 8 → Fin 2 → Fin 8 := fun uv => ![uv.1, uv.2]
  have hpt : ∀ (uv : Fin 8 × Fin 8) (I : Finset (Fin 2)) z,
      ((u.ex z).left ≫ (lift (pr uv.1) (pr uv.2)).left) ≫ (psum P₀.A (x2 P₀.A) I).left =
        (u₀.ex (∑ a ∈ I, R (r uv a) z)).left := fun uv I z => by
    rw [← Over.comp_left, ← Over.comp_left,
      CubeValues.comp_psum u₀ (u.ex z ≫ lift (pr uv.1) (pr uv.2)) (x2 P₀.A) fun a => R (r uv a) z]
    intro k
    fin_cases k <;> simp [x2, r, hR]
  have hin : ∀ uv : Fin 8 × Fin 8, IsFrameAlong (fun z => (u.ex z).left ≫ (lift (pr uv.1) (pr uv.2)).left)
      (abelian₂ P₀.A P₀.L) (fun (j : ULift.{0} (Finset (Fin 2)) → P₀.L.ι) z =>
        ∏ I : ULift.{0} (Finset (Fin 2)), u₀.fr (j I) (∑ a ∈ I.down, R (r uv a) z) ^ ((-1 : ℤ) ^ (2 - I.down.card))) :=
    fun uv => IsFrameAlong.linComb _ P₀.L (K := ULift.{0} (Finset (Fin 2))) _ _
      (fun I i z => u₀.fr i (∑ a ∈ I.down, R (r uv a) z)) fun I => by
        simp only [hpt]
        simpa only [LinearMap.sum_apply] using isFrameAlong_comp u₀ (∑ a ∈ I.down, R (r uv a))
  have hout := IsFrameAlong.linComb (fun z => (u.ex z).left) (abelian₂ P₀.A P₀.L) (K := Fin 8 × Fin 8)
    (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2) _ hin
  have hΛ : ∀ i (l : u.Λ), R i l ∈ u₀.Λ := fun i l => by
    rw [← u₀.ker, hR, (u.ker _).2 l.2, ← CubeValues.ex_zero u, ← hR, map_zero, CubeValues.ex_zero]
  refine GlobalTheory.lbIso_of_same_factor h1 h2 h3 h4 P _ _ u (withFrame u _ hout) P.isLB
    (LB.isLB_linComb (LB.isLB_linComb P₀.isLB _ _) _ _) rfl fun l i j z hi hj => ?_
  have hj' := (CubeValues.le_preimage_wchart (u.ex z).left (abelian₂ P₀.A P₀.L) _ j).1 hj
  have hst := fun uv : Fin 8 × Fin 8 => lam_step hu₀ (j uv) (fun a => R (r uv a) z) (fun a => R (r uv a) (z + l))
    (fun a => ⟨R (r uv a) l, hΛ _ l⟩) (fun a => map_add _ _ _) fun I => by
      rw [← hpt]
      exact (CubeValues.le_preimage_wchart _ P₀.L _ (j uv)).1 (hj' uv) I
  change u.fr i z * ∏ uv : Fin 8 × Fin 8, _ = u.fr i (z + l) * ∏ uv : Fin 8 × Fin 8, _
  simp only [hst, mul_zpow, Finset.prod_mul_distrib, ← Complex.exp_int_mul, ← Complex.exp_sum]
  rw [ah_step hu l i z hi, hχ, ← Complex.exp_add, hH, hH, ← sum_symmetrise W fun a b => hermForm H₀ (R a z) (R b l),
    ← sum_symmetrise W fun a b => hermForm H₀ (R a l) (R b l), ← Fintype.sum_prod_type' fun a b =>
      (W a b : ℂ) * ((hermForm H₀ (R a l) (R b l)).im : ℂ), Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, mul_comm _ (u.fr i (z + l)), _root_.mul_assoc]
  congr 3
  refine Finset.sum_congr rfl fun uv _ => ?_
  simp only [r, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end GlobalTheory
