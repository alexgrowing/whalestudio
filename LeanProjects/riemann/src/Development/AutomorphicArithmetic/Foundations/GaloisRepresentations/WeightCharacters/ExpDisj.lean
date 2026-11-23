import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private noncomputable def chiZ (m : ℤ) : Circle →* ℂ where
  toFun z := (z : ℂ) ^ m
  map_one' := by simp
  map_mul' x y := by simp [mul_zpow]

private theorem chiZ_injective : Function.Injective chiZ := by
  intro m n h
  by_contra hmn
  have hk : m - n ≠ 0 := sub_ne_zero.mpr hmn
  set z : Circle := Circle.exp (Real.pi / (m - n : ℤ)) with hz
  have hpow : (z : ℂ) ^ (m - n) = -1 := by
    rw [hz, Circle.coe_exp, ← Complex.exp_int_mul]
    have : ((m - n : ℤ) : ℂ) * (((Real.pi / ((m - n : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
      have hk' : ((m - n : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hk
      push_cast
      push_cast at hk'
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  have h1 : (z : ℂ) ^ m = (z : ℂ) ^ n := DFunLike.congr_fun h z
  have hz0 : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  have h2 : (z : ℂ) ^ (m - n) = 1 := by
    rw [zpow_sub₀ hz0, h1, div_self (zpow_ne_zero _ hz0)]
  rw [h2] at hpow
  norm_num at hpow

theorem UpperTheory.Gal.Wt.expDisj_of :
    UpperTheory.Gal.Wt.ExpDisj := by
  intro s t f hst hle hge
  let v : ℤ → (Circle → ℂ) := fun m z => (z : ℂ) ^ m
  have hli : LinearIndependent ℂ v :=
    (linearIndependent_monoidHom Circle ℂ).comp chiZ chiZ_injective
  have hd : Disjoint (Set.Iic s) (Set.Ici t) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd (lt_of_le_of_lt (Set.mem_Iic.mp hx) hst) (not_lt.mpr (Set.mem_Ici.mp hx'))
  have hdisj := hli.disjoint_span_image hd
  have e1 : ExpLe s = Submodule.span ℂ (v '' Set.Iic s) := by
    unfold ExpLe
    congr 1
    ext g
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
  have e2 : ExpGe t = Submodule.span ℂ (v '' Set.Ici t) := by
    unfold ExpGe
    congr 1
    ext g
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
  rw [e1] at hle
  rw [e2] at hge
  exact Submodule.disjoint_def.mp hdisj f hle hge
