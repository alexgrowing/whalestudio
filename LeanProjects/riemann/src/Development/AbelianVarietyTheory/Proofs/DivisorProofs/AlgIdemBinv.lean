import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataMatrixActionRingHomProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorActionCompatibleWithDegeneration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataLatticeFactorProps

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.PowLim

section Power

variable {S : Scheme.{0}} {A B : Over S} [GrpObj B] [IsCommMonObj B] {r : ℕ} (pr : Fin r → (A ⟶ B))
  (hl : IsLimit (Fan.mk A pr))

def act (a : Matrix (Fin r) (Fin r) ℤ) : A ⟶ A :=
  hl.lift (Fan.mk A fun i => ∏ j, pr j ^ a i j)

theorem act_pr (a : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : act pr hl a ≫ pr i = ∏ j, pr j ^ a i j :=
  hl.fac _ ⟨i⟩

def inc (i₀ : Fin r) : B ⟶ A :=
  hl.lift (Fan.mk B fun i => if i = i₀ then 𝟙 _ else 1)

theorem inc_pr (i₀ i : Fin r) : inc pr hl i₀ ≫ pr i = if i = i₀ then 𝟙 _ else 1 :=
  hl.fac _ ⟨i⟩

include hl in
theorem hom_ext {X : Over S} {f g : X ⟶ A} (h : ∀ i, f ≫ pr i = g ≫ pr i) : f = g :=
  hl.hom_ext fun ⟨i⟩ => h i

theorem comp_act_pr {X : Over S} (f : X ⟶ A) (a : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    f ≫ act pr hl a ≫ pr i = ∏ j, (f ≫ pr j) ^ a i j := by
  rw [act_pr, GlobalTheory.Mum.TensAct.comp_prod_zpow]

end Power

section Lattice

variable {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {r : ℕ} (xe : X' ≃+ (Fin r → X))

def smulF (s : SymUnit r) (a : TensO s) (z : X') : X' :=
  xe.symm (fun i => ∑ j, TensO.mat s a i j • xe z j)

theorem xe_smulF (s : SymUnit r) (a : TensO s) (z : X') (i : Fin r) :
    xe (smulF xe s a z) i = ∑ j, TensO.mat s a i j • xe z j := by
  simp [smulF]

def mod (s : SymUnit r) : Module (TensO s) X' where
  smul := smulF xe s
  one_smul z := by
    show smulF xe s 1 z = z
    apply xe.injective
    funext i
    rw [xe_smulF]
    simp [TensO.mat_one, Matrix.one_apply, ite_smul]
  mul_smul a b z := by
    show smulF xe s (a * b) z = smulF xe s a (smulF xe s b z)
    apply xe.injective
    funext i
    simp only [xe_smulF, TensO.mat_mul, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  smul_zero a := by
    show smulF xe s a 0 = 0
    apply xe.injective
    funext i
    simp [xe_smulF]
  smul_add a z z' := by
    show smulF xe s a (z + z') = smulF xe s a z + smulF xe s a z'
    apply xe.injective
    funext i
    simp [xe_smulF, smul_add, Finset.sum_add_distrib]
  add_smul a b z := by
    show smulF xe s (a + b) z = smulF xe s a z + smulF xe s b z
    apply xe.injective
    funext i
    simp [xe_smulF, add_smul, Finset.sum_add_distrib]
  zero_smul z := by
    show smulF xe s 0 z = 0
    apply xe.injective
    funext i
    rw [xe_smulF, map_zero]
    exact Finset.sum_eq_zero fun j _ => by
      show (0 : Matrix (Fin r) (Fin r) ℤ) i j • xe z j = 0
      simp

theorem xe_smul (s : SymUnit r) (a : TensO s) (z : X') (i : Fin r) :
    letI := mod xe s
    xe (a • z) i = ∑ j, TensO.mat s a i j • xe z j :=
  xe_smulF xe s a z i

def xi (i₀ : Fin r) : X →+ X' :=
  xe.symm.toAddMonoidHom.comp (AddMonoidHom.single (fun _ => X) i₀)

def xp (i₀ : Fin r) : X' →+ X :=
  (Pi.evalAddMonoidHom (fun _ => X) i₀).comp xe.toAddMonoidHom

theorem xe_xi (i₀ : Fin r) (y : X) : xe (xi xe i₀ y) = Pi.single i₀ y := by
  simp [xi]

end Lattice

end GlobalTheory.Mum.PowLim

namespace GlobalTheory.Mum.PowLim

section Ring

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] {r : ℕ}
  (pr : Fin r → (A ⟶ B)) (hl : IsLimit (Fan.mk A pr))

theorem act_isMonHom (hpr : ∀ i, IsMonHom (pr i)) (a : Matrix (Fin r) (Fin r) ℤ) : IsMonHom (act pr hl a) := by
  have h1 : ∀ {X : Over S}, (1 : X ⟶ A) ≫ act pr hl a = 1 := by
    intro X
    refine hom_ext pr hl fun i => ?_
    rw [Category.assoc, comp_act_pr]
    haveI := hpr i
    simp [MonObj.one_comp]
  have h2 : ∀ {X : Over S} (f g : X ⟶ A), (f * g) ≫ act pr hl a = (f ≫ act pr hl a) * (g ≫ act pr hl a) := by
    intro X f g
    refine hom_ext pr hl fun i => ?_
    haveI := hpr i
    rw [Category.assoc, comp_act_pr, MonObj.mul_comp, Category.assoc, Category.assoc, comp_act_pr, comp_act_pr,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [MonObj.mul_comp, mul_zpow]
  constructor
  · have := h1 (X := 𝟙_ _)
    simpa [Hom.one_def] using this
  · have := h2 (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at this
    rw [this]
    congr 1

theorem act_one : act pr hl 1 = 𝟙 _ := by
  refine hom_ext pr hl fun i => ?_
  rw [act_pr, Category.id_comp, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    rw [Matrix.one_apply_ne hj.symm, zpow_zero]
  · simp

theorem act_mul (a b : Matrix (Fin r) (Fin r) ℤ) : act pr hl (a * b) = act pr hl b ≫ act pr hl a := by
  refine hom_ext pr hl fun i => ?_
  rw [Category.assoc, comp_act_pr, act_pr]
  simp only [act_pr, ← Finset.prod_zpow, ← zpow_mul, Matrix.mul_apply]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  have : ∀ (s : Finset (Fin r)) (n : Fin r → ℤ), pr k ^ (∑ j ∈ s, n j) = ∏ j ∈ s, pr k ^ n j := by
    intro s n
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]
  rw [this]
  simp only [mul_comm]

theorem act_add (hpr : ∀ i, IsMonHom (pr i)) (a b : Matrix (Fin r) (Fin r) ℤ) :
    act pr hl (a + b) = padd A (act pr hl a) (act pr hl b) := by
  show _ = act pr hl a * act pr hl b
  refine hom_ext pr hl fun i => ?_
  haveI := hpr i
  rw [MonObj.mul_comp]
  simp only [act_pr, Matrix.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem inc_isMonHom (hpr : ∀ i, IsMonHom (pr i)) (i₀ : Fin r) : IsMonHom (inc pr hl i₀) := by
  refine ⟨?_, ?_⟩
  · apply Fan.IsLimit.hom_ext hl
    intro i
    have hp : ∀ k, (Fan.mk A pr).proj k = pr k := fun _ => rfl
    simp only [hp, Category.assoc, inc_pr]
    rw [(hpr i).one_hom]
    split_ifs
    · simp
    · rw [comp_one, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  · apply Fan.IsLimit.hom_ext hl
    intro i
    have hp : ∀ k, (Fan.mk A pr).proj k = pr k := fun _ => rfl
    simp only [hp, Category.assoc, inc_pr]
    rw [(hpr i).mul_hom, ← Category.assoc, tensorHom_comp_tensorHom, inc_pr]
    split_ifs
    · simp
    · rw [comp_one]
      have : ((1 : B ⟶ B) ⊗ₘ (1 : B ⟶ B)) = lift (fst _ _ ≫ 1) (snd _ _ ≫ 1) := by
        ext <;> simp
      rw [this, ← Hom.mul_def, comp_one, comp_one, _root_.mul_one]

theorem inc_pr_self (i₀ : Fin r) : inc pr hl i₀ ≫ pr i₀ = 𝟙 _ := by
  simpa using inc_pr pr hl i₀ i₀

theorem pr_inc (i₀ : Fin r) : pr i₀ ≫ inc pr hl i₀ = act pr hl (Matrix.single i₀ i₀ 1) := by
  apply Fan.IsLimit.hom_ext hl
  intro i
  have hp : ∀ k, (Fan.mk A pr).proj k = pr k := fun _ => rfl
  simp only [hp, Category.assoc, inc_pr, act_pr]
  by_cases h : i = i₀
  · subst h
    rw [if_pos rfl, Category.comp_id, Finset.prod_eq_single i]
    · simp [Matrix.single_apply]
    · intro j _ hj
      simp [Matrix.single_apply, Ne.symm hj]
    · simp
  · rw [if_neg h, comp_one]
    symm
    apply Finset.prod_eq_one
    intro j _
    simp [Matrix.single_apply, Ne.symm h]

end Ring

section Points

variable {R : Type} [CommRing R] [IsDomain R]

def cHom (Q : GlobalTheory.PolDeg.Data R) : Q.X →+ Additive (𝟙_ (Over (Sp R)) ⟶ Q.B) where
  toFun x := Additive.ofMul (Q.c x)
  map_zero' := by
    have h : Q.c (0 + 0) = Q.c 0 * Q.c 0 := Q.c_add 0 0
    rw [add_zero] at h
    have h1 : Q.c 0 = 1 := by simpa using h.symm
    rw [h1]; rfl
  map_add' x y := by rw [Q.c_add]; rfl

theorem c_zero (Q : GlobalTheory.PolDeg.Data R) : Q.c 0 = 1 := by
  have h := congrArg Additive.toMul (map_zero (cHom Q))
  exact h

theorem c_sum_zsmul (Q : GlobalTheory.PolDeg.Data R) {r : ℕ} (n : Fin r → ℤ) (x : Fin r → Q.X) :
    Q.c (∑ j, n j • x j) = ∏ j, Q.c (x j) ^ n j := by
  have h := congrArg Additive.toMul (map_sum (cHom Q) (fun j => n j • x j) Finset.univ)
  rw [toMul_sum] at h
  refine h.trans ?_
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_zsmul, toMul_zsmul]
  rfl

variable (Q : GlobalTheory.PolDeg.Data R) (D' : DegPre R) {r : ℕ} (pr : Fin r → (D'.P.A ⟶ Q.B))
  (hl : IsLimit (Fan.mk D'.P.A pr)) (xe : D'.X ≃+ (Fin r → Q.X))

theorem c_smul (hc : ∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) (s : SymUnit r) :
    letI := mod xe s
    ∀ (a : TensO s) (y : D'.X), D'.c (a • y) = D'.c y ≫ act pr hl (TensO.mat s a) := by
  letI := mod xe s
  intro a y
  refine Fan.IsLimit.hom_ext hl _ _ fun i => ?_
  show D'.c (a • y) ≫ pr i = (D'.c y ≫ act pr hl (TensO.mat s a)) ≫ pr i
  rw [hc, Category.assoc, act_pr, xe_smul, c_sum_zsmul Q]
  have h := map_prod (precompHom (M := Q.B) (D'.c y)) (fun j => pr j ^ TensO.mat s a i j) Finset.univ
  refine Eq.trans ?_ h.symm
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_zpow]
  show _ = (D'.c y ≫ pr j) ^ _
  rw [hc]

theorem c_xi (hc : ∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) (i₀ : Fin r) (y : Q.X) :
    D'.c (xi xe i₀ y) = Q.c y ≫ inc pr hl i₀ := by
  apply Fan.IsLimit.hom_ext hl
  intro i
  have hp : ∀ k, (Fan.mk D'.P.A pr).proj k = pr k := fun _ => rfl
  simp only [hp, Category.assoc, inc_pr, hc]
  by_cases h : i = i₀
  · subst h
    simp [xe_xi]
  · rw [if_neg h, comp_one]
    simp [xe_xi, Pi.single_apply, h, c_zero]

end Points

section Lat

variable {X X' : Type} [AddCommGroup X] [Module.Free ℤ X] [AddCommGroup X'] {r : ℕ} (xe : X' ≃+ (Fin r → X))

theorem xe_smul_xi (s : SymUnit r) (a : TensO s) (i₀ : Fin r) (y : X) (i : Fin r) :
    letI := mod xe s
    xe (a • xi xe i₀ y) i = TensO.mat s a i i₀ • y := by
  letI := mod xe s
  rw [xe_smul]
  simp only [xe_xi]
  rw [Finset.sum_eq_single i₀]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem factor_latt (s : SymUnit r) (i₀ : Fin r) :
    letI := mod xe s
    (∀ y, xp xe i₀ (xi xe i₀ y) = y) ∧ (∀ z, xi xe i₀ (xp xe i₀ z) = TensO.idem s i₀ • z) ∧
    Function.Injective (fun y => star (TensO.idem s i₀) • TensO.binv s • xi xe i₀ y) ∧
    ∀ z, ∃ y, star (TensO.idem s i₀) • z = star (TensO.idem s i₀) • TensO.binv s • xi xe i₀ y := by
  letI := mod xe s
  have key : ∀ y i, xe (star (TensO.idem s i₀) • TensO.binv s • xi xe i₀ y) i =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) i i₀ • y := by
    intro y i
    rw [← mul_smul, xe_smul_xi, TensO.mat_star_idem_mul_binv, mul_single_apply']
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    show xe (xi xe i₀ y) i₀ = y
    rw [xe_xi]; simp
  · intro z
    apply xe.injective
    funext i
    rw [xe_xi, xe_smul]
    show Pi.single (M := fun _ => X) i₀ (xe z i₀) i = _
    simp only [TensO.idem, TensO.ofMat, TensO.mat, Matrix.single_apply]
    by_cases hi : i = i₀
    · subst hi; simp
    · simp [hi, Ne.symm hi]
  · intro y y' h
    obtain ⟨i, hi⟩ := SymUnit.inv_col_ne s i₀
    have h' := congrArg (fun z => xe z i) h
    simp only [key] at h'
    exact smul_right_injective X hi h'
  · intro z
    refine ⟨∑ j, (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ j • xe z j, ?_⟩
    apply xe.injective
    funext i
    rw [key, xe_smul, TensO.mat_star_idem, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_single_mul_apply, mul_smul]

end Lat

end GlobalTheory.Mum.PowLim

namespace GlobalTheory.Mum.PowLim

theorem alg_idem_binv {r : ℕ} (s : SymUnit r) (i₀ : Fin r)
    (hp : 0 < (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀) :
    (∃ b : ℕ, 0 < b ∧ Star.star (TensO.idem s i₀) * TensO.idem s i₀ =
        b • (Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀)) ∧
      Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀ =
        Star.star (TensO.idem s i₀) * Star.star (TensO.binv s) * TensO.idem s i₀ ∧
      ∃ g : TensO s, g * (Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀) = TensO.idem s i₀ := by
  have hf : Star.star (TensO.binv s) = TensO.binv s := by
    show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ) = ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ)
    rw [TensO.inv_transpose, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hEE : (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ 1 =
      Matrix.single i₀ i₀ 1 := by simp
  have hET : (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ).transpose = Matrix.single i₀ i₀ 1 := by simp
  have hmain : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
      (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ).transpose * (s.1 : Matrix (Fin r) (Fin r) ℤ) *
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ) =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ) := by
    rw [hET, Matrix.mul_assoc _ (s.1 : Matrix (Fin r) (Fin r) ℤ), Units.mul_inv, Matrix.mul_one, Matrix.mul_assoc, hEE]
  have hefe : Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀ = TensO.binv s * TensO.idem s i₀ := hmain
  refine ⟨⟨((s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀).toNat, by omega, ?_⟩, by rw [hf], TensO.ofMat s s.1, ?_⟩
  · rw [hefe]
    have h : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
        (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ).transpose * (s.1 : Matrix (Fin r) (Fin r) ℤ) *
        Matrix.single i₀ i₀ (1 : ℤ) = ((s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀).toNat •
        (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ)) := by
      rw [hET, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.single i₀ i₀ (1 : ℤ)),
        Matrix.single_mul_mul_single, ← Matrix.mul_smul]
      congr 1
      rw [Matrix.smul_single, nsmul_eq_mul, Int.toNat_of_nonneg hp.le]
      simp
    exact h
  · rw [hefe]
    have h : (s.1 : Matrix (Fin r) (Fin r) ℤ) *
        (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ)) =
        Matrix.single i₀ i₀ (1 : ℤ) := by
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    exact h

end GlobalTheory.Mum.PowLim
