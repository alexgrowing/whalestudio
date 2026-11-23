import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnProdOfForall
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueThetaCharAtPoint
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannFormBijectiveOfWeilNondeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRM.TransFrame

private theorem differentiableOn_finprod {E κ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E}
    (s : Finset κ) (φ : κ → E → ℂ) (h : ∀ k, DifferentiableOn ℂ (φ k) S) :
    DifferentiableOn ℂ (fun z => ∏ k ∈ s, φ k z) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

section

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
  (u : HolUnif A L g) (u' : HolUnif A' L' g') {K : Type} [Fintype K] (f : K → (A ⟶ A'))
  (F : K → (Fin g → ℂ) → (Fin g' → ℂ)) (ε : K → ℤ)

def holCombUnif (hF : ∀ k, Differentiable ℂ (F k)) (h : ∀ k z, u'.ex (F k z) = u.ex z ≫ f k) :
    HolUnif A (LB.LinComb L' (fun k => (f k).left) ε) g :=
  have hl : ∀ k z, (u'.ex (F k z)).left = (u.ex z).left ≫ (f k).left := fun k z => by
    rw [h k z]; rfl
  have hc : ∀ (j : K → L'.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ LB.wchart L' (fun k => (f k).left) j →
      ∀ k, ⊤ ≤ (u'.ex (F k z)).left ⁻¹ᵁ L'.U (j k) := fun j z hz k => by
    rw [hl k z]
    exact (CubeValues.le_preimage_wchart (u.ex z).left L' (fun k => (f k).left) j).1 hz k
  { ex := u.ex
    ex_add := u.ex_add
    ex_onto := u.ex_onto
    Λ := u.Λ
    ker := u.ker
    discrete := u.discrete
    full := u.full
    hol := u.hol
    fr := fun (j : K → L'.ι) z => ∏ k, u'.fr (j k) (F k z) ^ ε k
    fr_hol := fun j => by
      refine differentiableOn_finprod Finset.univ
        (fun k (z : Fin g → ℂ) => u'.fr (j k) (F k z) ^ ε k) fun k => ?_
      refine DifferentiableOn.zpow ?_ (Or.inl fun z hz => u'.fr_ne _ _ (hc j z hz k))
      exact (u'.fr_hol (j k)).comp (hF k).differentiableOn fun z hz => hc j z hz k
    fr_ne := fun j z hz => Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (u'.fr_ne _ _ (hc j z hz k))
    fr_compat := fun j j' z hz => by
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf (u.ex z).left _ _).1 hz
      have e := CubeValues.val_linComb (u.ex z).left valAt'_rules L' (fun k => (f k).left) ε j j' h1 h2
      refine Eq.trans ?_ (congrArg (· * ∏ k, u'.fr (j' k) (F k z) ^ ε k) e.symm)
      show _ = (∏ k, _) * _
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← mul_zpow, ← hl k z]
      exact congrArg (· ^ ε k) (u'.fr_compat (j k) (j' k) (F k z)
        ((top_le_preimage_inf _ _ _).2 ⟨hc j z h1 k, hc j' z h2 k⟩)) }

end

variable {A : Over (Sp ℂ)} [GrpObj A]

theorem padd_eq' {T : Over (Sp ℂ)} (a b : T ⟶ A) : padd A a b = a * b := (Hom.mul_def a b).symm

theorem pzero_eq' (T : Over (Sp ℂ)) : pzero A T = 1 := by
  rw [pzero, Hom.one_def]

def pairRight (c : 𝟙_ (Over (Sp ℂ)) ⟶ A) : A ⟶ A ⊗ A := lift (𝟙 A) (toUnit A ≫ c)

def shiftSum (c : 𝟙_ (Over (Sp ℂ)) ⟶ A) (I : ULift.{0} (Finset (Fin 2))) : A ⟶ A :=
  pairRight c ≫ psum A (x2 A) I.down

def shiftVec {g : ℕ} (w : Fin g → ℂ) (I : ULift.{0} (Finset (Fin 2))) (z : Fin g → ℂ) : Fin g → ℂ :=
  (if (0 : Fin 2) ∈ I.down then z else 0) + (if (1 : Fin 2) ∈ I.down then w else 0)

theorem differentiable_shiftVec {g : ℕ} (w : Fin g → ℂ) (I : ULift.{0} (Finset (Fin 2))) :
    Differentiable ℂ (shiftVec w I) := by
  unfold shiftVec
  split_ifs <;> fun_prop

theorem pt_shiftSum (y c : 𝟙_ (Over (Sp ℂ)) ⟶ A) (I : Finset (Fin 2)) :
    y ≫ (pairRight c ≫ psum A (x2 A) I) =
      (if (0 : Fin 2) ∈ I then y else 1) * (if (1 : Fin 2) ∈ I then c else 1) := by
  have h0 : y ≫ pairRight c ≫ fst A A = y := by simp [pairRight]
  have h1 : y ≫ pairRight c ≫ snd A A = c := by
    simp only [pairRight, lift_snd]
    rw [← Category.assoc, toUnit_unique (y ≫ toUnit A) (𝟙 _), Category.id_comp]
  have hI : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by revert I; decide
  rcases hI with rfl | rfl | rfl | rfl <;>
    simp [psum, padd_eq', pzero_eq', x2, List.finRange_succ, comp_mul, comp_one, h0, h1]

theorem ex_shiftVec {M : LB A.left} {g : ℕ} (u : HolUnif A M g) (w : Fin g → ℂ) (I : ULift.{0} (Finset (Fin 2)))
    (z : Fin g → ℂ) : u.ex (shiftVec w I z) = u.ex z ≫ shiftSum (u.ex w) I := by
  rw [shiftSum, pt_shiftSum, shiftVec, u.ex_add]
  split_ifs <;> simp [holUnif_ex_zero_eq_one]

end GlobalTheory.TorusRM.TransFrame

namespace GlobalTheory.TorusRM.TransFrame

variable {A : Over (Sp ℂ)} [GrpObj A]

def expo (I : ULift.{0} (Finset (Fin 2))) : ℤ := (-1) ^ (2 - I.down.card)

theorem chart (M : LB A.left) (c : 𝟙_ (Over (Sp ℂ)) ⟶ A) (x : Sp ℂ ⟶ A.left)
    (J : ((abelian₂ A M).pull (pairRight c).left).ι) :
    (⊤ : (Sp ℂ).Opens) ≤ x ⁻¹ᵁ ((abelian₂ A M).pull (pairRight c).left).U J ↔
      ∀ I, ⊤ ≤ (x ≫ (shiftSum c I).left) ⁻¹ᵁ M.U (J PUnit.unit I) := by
  rw [GlobalTheory.ThetaPoint.top_le_pull_iff]
  show ⊤ ≤ (x ≫ (pairRight c).left) ⁻¹ᵁ
      LB.wchart M (fun I : ULift.{0} (Finset (Fin 2)) => (psum A (x2 A) I.down).left) (J PUnit.unit) ↔ _
  refine (CubeValues.le_preimage_wchart _ M (fun I : ULift.{0} (Finset (Fin 2)) => (psum A (x2 A) I.down).left)
    (J PUnit.unit : ULift.{0} (Finset (Fin 2)) → M.ι)).trans ?_
  simp only [shiftSum, Over.comp_left, Category.assoc]

theorem chart' (M : LB A.left) (c : 𝟙_ (Over (Sp ℂ)) ⟶ A) (x : Sp ℂ ⟶ A.left)
    (j : ULift.{0} (Finset (Fin 2)) → M.ι) :
    (⊤ : (Sp ℂ).Opens) ≤ x ⁻¹ᵁ LB.wchart M (fun I => (shiftSum c I).left) j ↔
      ∀ I, ⊤ ≤ (x ≫ (shiftSum c I).left) ⁻¹ᵁ M.U (j I) :=
  CubeValues.le_preimage_wchart _ _ _ _

theorem val_g (M : LB A.left) (c : 𝟙_ (Over (Sp ℂ)) ⟶ A) (x : Sp ℂ ⟶ A.left)
    (J J' : ((abelian₂ A M).pull (pairRight c).left).ι)
    (h : (⊤ : (Sp ℂ).Opens) ≤ x ⁻¹ᵁ ((abelian₂ A M).pull (pairRight c).left).U J)
    (h' : (⊤ : (Sp ℂ).Opens) ≤ x ⁻¹ᵁ ((abelian₂ A M).pull (pairRight c).left).U J') :
    valAt' x (((abelian₂ A M).pull (pairRight c).left).U J ⊓ ((abelian₂ A M).pull (pairRight c).left).U J')
        (((abelian₂ A M).pull (pairRight c).left).g J J').val =
      valAt' x ((M.LinComb (fun I => (shiftSum c I).left) expo).U (J PUnit.unit) ⊓
          (M.LinComb (fun I => (shiftSum c I).left) expo).U (J' PUnit.unit))
        ((M.LinComb (fun I => (shiftSum c I).left) expo).g (J PUnit.unit) (J' PUnit.unit)).val := by
  refine (GlobalTheory.ThetaPoint.valAt'_pull_g _ _ _ _ _ h h').trans ?_
  have hL := (GlobalTheory.ThetaPoint.top_le_pull_iff _ _ _ _).1 h
  have hL' := (GlobalTheory.ThetaPoint.top_le_pull_iff _ _ _ _).1 h'
  have hc := (chart' M c x (J PUnit.unit)).2 ((chart M c x J).1 h)
  have hc' := (chart' M c x (J' PUnit.unit)).2 ((chart M c x J').1 h')
  refine (CubeValues.val_linComb (x ≫ (pairRight c).left) valAt'_rules M
    (fun I : ULift.{0} (Finset (Fin 2)) => (psum A (x2 A) I.down).left) expo
    (J PUnit.unit : ULift.{0} (Finset (Fin 2)) → M.ι) (J' PUnit.unit : ULift.{0} (Finset (Fin 2)) → M.ι) hL hL').trans ?_
  refine Eq.trans ?_ (CubeValues.val_linComb x valAt'_rules M (fun I => (shiftSum c I).left) expo _ _ hc hc').symm
  simp only [shiftSum, Over.comp_left, Category.assoc]

variable {M : LB A.left} {g : ℕ}

def transUnif (u : HolUnif A M g) (w : Fin g → ℂ) : HolUnif A ((abelian₂ A M).pull (pairRight (u.ex w)).left) g :=
  let u₁ := holCombUnif u u (shiftSum (u.ex w)) (shiftVec w) expo (differentiable_shiftVec w) (ex_shiftVec u w)
  have hc : ∀ (J : ((abelian₂ A M).pull (pairRight (u.ex w)).left).ι) (z : Fin g → ℂ),
      (⊤ : (Sp ℂ).Opens) ≤ (u.ex z).left ⁻¹ᵁ ((abelian₂ A M).pull (pairRight (u.ex w)).left).U J →
      (⊤ : (Sp ℂ).Opens) ≤ (u₁.ex z).left ⁻¹ᵁ
        (M.LinComb (fun I => (shiftSum (u.ex w) I).left) expo).U (J PUnit.unit) :=
    fun J z hz => (chart' M _ _ (J PUnit.unit)).2 ((chart M _ _ J).1 hz)
  { ex := u.ex
    ex_add := u.ex_add
    ex_onto := u.ex_onto
    Λ := u.Λ
    ker := u.ker
    discrete := u.discrete
    full := u.full
    hol := u.hol
    fr := fun J z => u₁.fr (J PUnit.unit) z
    fr_hol := fun J => (u₁.fr_hol (J PUnit.unit)).mono fun z hz => hc J z hz
    fr_ne := fun J z hz => u₁.fr_ne _ z (hc J z hz)
    fr_compat := fun J J' z hz => by
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
      rw [val_g M _ _ J J' h1 h2]
      exact u₁.fr_compat _ _ z ((top_le_preimage_inf _ _ _).2 ⟨hc J z h1, hc J' z h2⟩) }

theorem transUnif_fr (u : HolUnif A M g) (w : Fin g → ℂ) (J : ((abelian₂ A M).pull (pairRight (u.ex w)).left).ι)
    (z : Fin g → ℂ) :
    (transUnif u w).fr J z = ∏ I, u.fr (J PUnit.unit I) (shiftVec w I z) ^ expo I := rfl

end GlobalTheory.TorusRM.TransFrame

namespace GlobalTheory.TorusRM.TransFrame

theorem prod_ulift_finset_fin_two_eq (f : ULift.{0} (Finset (Fin 2)) → ℂ) :
    ∏ I, f I = f ⟨∅⟩ * f ⟨{0}⟩ * f ⟨{1}⟩ * f ⟨{0, 1}⟩ := by
  rw [← Fintype.prod_equiv Equiv.ulift.symm (fun I : Finset (Fin 2) => f ⟨I⟩) f (fun _ => rfl)]
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  ring

variable {A : Over (Sp ℂ)} [GrpObj A] {M : LB A.left} {g : ℕ}

theorem transUnif_factor (u : HolUnif A M g) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hF : IsFactorAH u Hm χ) (w : Fin g → ℂ) (l : u.Λ) (J : ((abelian₂ A M).pull (pairRight (u.ex w)).left).ι)
    (z : Fin g → ℂ) (hz : ⊤ ≤ ((transUnif u w).ex z).left ⁻¹ᵁ ((abelian₂ A M).pull (pairRight (u.ex w)).left).U J) :
    (transUnif u w).fr J z =
      Complex.exp (Real.pi * (w ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * (transUnif u w).fr J (z + l) := by
  have hc : ∀ I, (⊤ : (Sp ℂ).Opens) ≤ (u.ex (shiftVec w I z)).left ⁻¹ᵁ M.U (J PUnit.unit I) := by
    intro I
    rw [ex_shiftVec, Over.comp_left]
    exact (chart M _ _ J).1 hz I
  have hzl : u.ex (z + l) = u.ex z := by rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  have hcl : ∀ I, (⊤ : (Sp ℂ).Opens) ≤ (u.ex (shiftVec w I (z + l))).left ⁻¹ᵁ M.U (J PUnit.unit I) := by
    intro I
    rw [ex_shiftVec, hzl, ← ex_shiftVec]
    exact hc I
  have c1 : (⊤ : (Sp ℂ).Opens) ≤ (u.ex z).left ⁻¹ᵁ M.U (J PUnit.unit ⟨{0}⟩) := by
    simpa [shiftVec] using hc ⟨{0}⟩
  have c3 : (⊤ : (Sp ℂ).Opens) ≤ (u.ex (z + w)).left ⁻¹ᵁ M.U (J PUnit.unit ⟨{0, 1}⟩) := by
    simpa [shiftVec] using hc ⟨{0, 1}⟩
  have n1 : u.fr (J PUnit.unit ⟨{0}⟩) (z + l) ≠ 0 := u.fr_ne _ _ (by simpa [shiftVec] using hcl ⟨{0}⟩)
  have n2 : u.fr (J PUnit.unit ⟨{1}⟩) w ≠ 0 := u.fr_ne _ _ (by simpa [shiftVec] using hc ⟨{1}⟩)
  have nχ : χ l ≠ 0 := by
    intro h0
    have := hF.2.1 l
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have e1 := hF.2.2 l (J PUnit.unit ⟨{0}⟩) z c1
  have e3 := hF.2.2 l (J PUnit.unit ⟨{0, 1}⟩) (z + w) c3
  rw [transUnif_fr, transUnif_fr, prod_ulift_finset_fin_two_eq, prod_ulift_finset_fin_two_eq]
  simp only [shiftVec, expo]
  simp only [Finset.notMem_empty, if_false, Finset.mem_singleton, Finset.mem_insert, Finset.card_empty,
    Finset.card_singleton]
  norm_num
  rw [e1, e3, add_dotProduct, show z + l + w = z + w + l by abel]
  have hexp : Complex.exp (Real.pi * ((z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        (w ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) =
      Complex.exp (Real.pi * (w ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) *
        Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
          Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) := by
    rw [← Complex.exp_add]; ring_nf
  rw [hexp]
  have nE := Complex.exp_ne_zero (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
          Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))
  field_simp

end GlobalTheory.TorusRM.TransFrame

namespace GlobalTheory.TorusRM.TransFrame

theorem gen_div_eq {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (B : LB X) (t : B.Gen) (ht : t.IsGen) (j j' : B.ι)
    (hj : ⊤ ≤ x ⁻¹ᵁ B.U j) (hj' : ⊤ ≤ x ⁻¹ᵁ B.U j') (a b : ℂ)
    (hab : a = valAt' x (B.U j ⊓ B.U j') (B.g j j').val * b) (hb : b ≠ 0) :
    valAt' x (B.U j) (t.s j).val / a = valAt' x (B.U j') (t.s j').val / b := by
  have hm := (top_le_preimage_inf _ _ _).2 ⟨hj, hj'⟩
  have e := congrArg (fun c : Γ(X, B.U j ⊓ B.U j')ˣ => valAt' x _ c.val) (ht j j')
  simp only [res, Units.coe_map, Units.val_mul, MonoidHom.coe_coe] at e
  rw [valAt'_mul, valAt'_map _ _ _ hm, valAt'_map _ _ _ hm] at e
  have n3 : valAt' x (B.U j ⊓ B.U j') (B.g j j').val ≠ 0 := by
    obtain ⟨f, hf⟩ := (valAt'_rules _ x).2.1 _ hm
    rw [hf]
    exact ((B.g j j').isUnit.map f).ne_zero
  rw [e, hab, mul_div_mul_left _ _ n3]

theorem unitValue_ne_zero {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (c : Γ(X, V)ˣ) :
    valAt' x V c.val ≠ 0 := by
  obtain ⟨f, hf⟩ := (valAt'_rules _ x).2.1 _ h
  rw [hf]
  exact (c.isUnit.map f).ne_zero

end GlobalTheory.TorusRM.TransFrame

open GlobalTheory.TorusRM.TransFrame in

theorem GlobalTheory.TorusRM.exists_theta_of_hasGen_lam_pull : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → IsFactorAH u Hm χ → ∀ w : Fin g → ℂ,
    HasGen ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left) →
    ∃ θ : (Fin g → ℂ) → ℂ, Differentiable ℂ θ ∧ (∀ z, θ z ≠ 0) ∧
      ∀ l ∈ u.Λ, ∀ z, θ (z + l) = Complex.exp (Real.pi * (w ⬝ᵥ Hm.mulVec (star l))) * θ z := by
  intro g A _ hA M u Hm χ hM hF w hG
  obtain ⟨t, ht⟩ := hG
  have hρ : lift (𝟙 A) (toUnit A) ≫ lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w) =
      pairRight (u.ex w) := by
    simp [pairRight, comp_lift]
  have key : (fun _ : PUnit => (lift (𝟙 A) (toUnit A)).left ≫
      (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left) =
      (fun _ : PUnit => (pairRight (u.ex w)).left) := by
    funext _
    rw [← Over.comp_left, hρ]
  have H : HasGen (LB.LinComb (abelian₂ A M) (fun _ : PUnit => (lift (𝟙 A) (toUnit A)).left ≫
      (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left) (fun _ => 1)) :=
    ⟨_, ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen (abelian₂ A M) _ _ t ht (lift (𝟙 A) (toUnit A)).left⟩
  rw [key] at H
  obtain ⟨t', ht'⟩ := H

  have hch : ∀ z, ∃ J : ((abelian₂ A M).pull (pairRight (u.ex w)).left).ι,
      ⊤ ≤ ((transUnif u w).ex z).left ⁻¹ᵁ ((abelian₂ A M).pull (pairRight (u.ex w)).left).U J := by
    intro z
    have hI : ∀ I : ULift.{0} (Finset (Fin 2)), ∃ i : M.ι,
        (⊤ : (Sp ℂ).Opens) ≤ ((u.ex z).left ≫ (shiftSum (u.ex w) I).left) ⁻¹ᵁ M.U i := by
      intro I
      have hmem : ((u.ex z).left ≫ (shiftSum (u.ex w) I).left) (default : PrimeSpectrum ℂ) ∈ ⨆ i, M.U i := by
        rw [hM.cover]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
      exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩
    choose c hc using hI
    exact ⟨fun _ => c, (chart M _ _ _).2 hc⟩
  choose J hJ using hch
  have hv : ∀ j j' z, ⊤ ≤ ((transUnif u w).ex z).left ⁻¹ᵁ ((abelian₂ A M).pull (pairRight (u.ex w)).left).U j →
      ⊤ ≤ ((transUnif u w).ex z).left ⁻¹ᵁ ((abelian₂ A M).pull (pairRight (u.ex w)).left).U j' →
      valAt' ((transUnif u w).ex z).left _ (t'.s j).val / (transUnif u w).fr j z =
        valAt' ((transUnif u w).ex z).left _ (t'.s j').val / (transUnif u w).fr j' z := by
    intro j j' z hj hj'
    exact gen_div_eq _ _ t' ht' j j' hj hj' _ _
      ((transUnif u w).fr_compat j j' z ((top_le_preimage_inf _ _ _).2 ⟨hj, hj'⟩))
      ((transUnif u w).fr_ne _ z hj')
  refine ⟨fun z => valAt' ((transUnif u w).ex z).left _ (t'.s (J z)).val / (transUnif u w).fr (J z) z,
    fun z => ?_, fun z => ?_, fun l hl z => ?_⟩
  · obtain ⟨ho, hd⟩ := (transUnif u w).hol _ (t'.s (J z)).val
    have hn := ho.mem_nhds (hJ z)
    have hq := (hd.differentiableAt hn).mul
      ((((transUnif u w).fr_hol (J z)).differentiableAt hn).inv ((transUnif u w).fr_ne _ z (hJ z)))
    refine hq.congr_of_eventuallyEq ?_
    filter_upwards [hn] with y hy
    simp only [Pi.mul_apply, Pi.inv_apply, ← div_eq_mul_inv]
    exact hv (J y) (J z) y (hJ y) hy
  · exact div_ne_zero (unitValue_ne_zero _ _ (hJ z) _) ((transUnif u w).fr_ne _ z (hJ z))
  · have hzl : (transUnif u w).ex (z + l) = (transUnif u w).ex z := by
      rw [(transUnif u w).ex_add, ((transUnif u w).ker l).2 hl, _root_.mul_one]
    have hj : ⊤ ≤ ((transUnif u w).ex (z + l)).left ⁻¹ᵁ ((abelian₂ A M).pull (pairRight (u.ex w)).left).U (J z) := by
      rw [hzl]; exact hJ z
    show _ / _ = _ * (_ / _)
    rw [hv (J (z + l)) (J z) (z + l) (hJ _) hj, hzl,
      transUnif_factor u hF w ⟨l, hl⟩ (J z) z (hJ z)]
    have n := (transUnif u w).fr_ne _ _ hj
    have nE := Complex.exp_ne_zero (Real.pi * (w ⬝ᵥ Hm.mulVec (star l)))
    field_simp
