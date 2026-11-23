import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.Wcount

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc

open QuadraticAlgebra Matrix

section Model

variable {K : Type} [Field K] (Δ τ : K)

abbrev EL : Type := Etau (Lsq K Δ) (algebraMap K (Lsq K Δ) τ)

abbrev Sp : Type := Lsq K Δ × EL Δ τ

variable {Δ τ}

def sigL (x : EL Δ τ) : EL Δ τ := ⟨star x.re, star x.im⟩

variable (Δ) in

def ofE (z : Etau K τ) : EL Δ τ := ⟨algebraMap K (Lsq K Δ) z.re, algebraMap K (Lsq K Δ) z.im⟩

def herm (c : K) (m : EL Δ τ) (x y : Sp Δ τ) : Lsq K Δ :=
  algebraMap K (Lsq K Δ) c * x.1 * star y.1 + QuadraticAlgebra.trace (m * x.2 * star (sigL y.2))

def semi (d : EL Δ τ) (x : Sp Δ τ) : Sp Δ τ := (star x.1, d * sigL x.2)

def quo (z : (Etau K τ)ˣ) : Etau K τ := (z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)

variable (Δ) in

def tor (z : (Etau K τ)ˣ) (x : Sp Δ τ) : Sp Δ τ := (x.1, ofE Δ (quo z) * x.2)

structure IsDat (c : K) (d m : EL Δ τ) : Prop where
  reg : τ ^ 2 - 4 ≠ 0
  c_ne : c ≠ 0
  d_norm : d * sigL d = ofE Δ (ω : Etau K τ)
  m_unit : IsUnit m
  m_star : star (sigL m) = m
  m_sig : sigL m = m * d * star (sigL d)

variable (Δ) in

abbrev U3 : Type := Matrix.unitaryGroup (Fin 3) (Lsq K Δ)

variable (Δ) in

def theta : U3 Δ →* U3 Δ where
  toFun g := ⟨(g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map star, by
    have e : ∀ a b : Matrix (Fin 3) (Fin 3) (Lsq K Δ), (a * b).map star = a.map star * b.map star := fun a b =>
      Matrix.map_mul (f := starRingEnd (Lsq K Δ))
    have e1 : (1 : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map star = 1 := Matrix.map_one _ (star_zero _) (star_one _)
    have e2 : star ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map star) = (star (g : Matrix (Fin 3) (Fin 3) (Lsq K Δ))).map star := by
      ext i j <;> simp [Matrix.star_apply]
    constructor
    · rw [e2, ← e, g.2.1, e1]
    · rw [e2, ← e, g.2.2, e1]⟩
  map_one' := Subtype.ext (Matrix.map_one _ (star_zero _) (star_one _))
  map_mul' a b := Subtype.ext (Matrix.map_mul (f := starRingEnd (Lsq K Δ)))

structure Models (c : K) (d m : EL Δ τ) (δ : U3 Δ) (ι : (Etau K τ)ˣ →* U3 Δ)
    (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)) : Prop where
  form : ∀ x y, herm c m x y = ∑ i, P x i * star (P y i)
  semi : ∀ x, P (semi d x) = (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star (P x)
  tor : ∀ z x, P (tor Δ z x) = (ι z : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ P x

open Classical in

def hs (D x : K) : ℂ := if ∃ a b : K, a ^ 2 - D * b ^ 2 = x then 1 else -1

variable (τ) in

def NE : Subgroup Kˣ := (Units.map (QuadraticAlgebra.norm : Etau K τ →* K)).range

end Model

section Lattice

variable (O : Type) [CommRing O] {K : Type} [Field K] [Algebra O K] {Δ τ : K}

abbrev IsInt (x : Lsq K Δ) : Prop := IsIntegral O x

variable (τ) in

def Cint : Subgroup (Etau K τ)ˣ where
  carrier := {z | IsIntegral O (quo z) ∧ IsIntegral O (quo z⁻¹)}
  one_mem' := by simp [quo, isIntegral_one]
  mul_mem' {a b} ha hb := by
    have e : ∀ a b : (Etau K τ)ˣ, quo (a * b) = quo a * quo b := fun a b => by
      simp only [quo, _root_.mul_inv_rev, Units.val_mul, star_mul]; ring
    refine ⟨e a b ▸ ha.1.mul hb.1, ?_⟩
    rw [_root_.mul_inv_rev, e]
    exact hb.2.mul ha.2
  inv_mem' {a} ha := ⟨ha.2, by simpa using ha.1⟩

structure IsFix (c : K) (d m : EL Δ τ) (S : Set (Sp Δ τ)) : Prop where
  fg : ∃ s : Finset (Sp Δ τ), S = Submodule.span O (s : Set (Sp Δ τ))
  dual : ∀ y, y ∈ S ↔ ∀ x ∈ S, IsInt O (herm c m x y)
  stab : semi d '' S = S

variable (Δ τ) in

@[reducible] def torAct : MulAction (Etau K τ)ˣ (Set (Sp Δ τ)) where
  smul z S := tor Δ z '' S
  one_smul S := by
    have : ∀ x : Sp Δ τ, tor Δ (1 : (Etau K τ)ˣ) x = x := fun x => by
      have h : ofE Δ (quo (1 : (Etau K τ)ˣ)) = 1 := by
        ext <;> simp [ofE, quo, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
      simp [tor, h]
    change tor Δ 1 '' S = S
    simp [this]
  mul_smul a b S := by
    have e : quo (a * b) = quo a * quo b := by
      simp only [quo, _root_.mul_inv_rev, Units.val_mul, star_mul]; ring
    have e' : ∀ x y : Etau K τ, ofE Δ (x * y) = ofE Δ x * ofE Δ y := fun x y => by
      ext <;> simp [ofE]
    change tor Δ (a * b) '' S = tor Δ a '' (tor Δ b '' S)
    rw [← Set.image_comp]
    congr 1
    funext x
    simp [tor, e, e', mul_assoc]

open Classical in

def lcount (c : K) (d m : EL Δ τ) : ℂ :=
  letI := torAct (K := K) Δ τ
  wcount (Cint O τ) fun S : Set (Sp Δ τ) => if IsFix O c d m S then 1 else 0

def stabSum (c : K) (d m : EL Δ τ) : ℂ :=
  ∑ᶠ t : Kˣ ⧸ NE τ, lcount O c d (((t.out : Kˣ) : K) • m)

def kapSum (c : K) (d m : EL Δ τ) : ℂ :=
  ∑ᶠ t : Kˣ ⧸ NE τ, hs (τ ^ 2 - 4) ((t.out : Kˣ) : K) * lcount O c d (((t.out : Kˣ) : K) • m)

variable (Δ) in

def KU : Subgroup (U3 Δ) where
  carrier := {g | ∀ i j, IsInt O ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) ∧
    IsInt O (star ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j))}
  one_mem' i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h, isIntegral_one, isIntegral_zero]
  mul_mem' {a b} ha hb i j := by
    rw [Submonoid.coe_mul, Matrix.mul_apply, Fin.sum_univ_three]
    refine ⟨(((ha _ _).1.mul (hb _ _).1).add ((ha _ _).1.mul (hb _ _).1)).add ((ha _ _).1.mul (hb _ _).1), ?_⟩
    simp only [star_add, star_mul']
    exact (((ha _ _).2.mul (hb _ _).2).add ((ha _ _).2.mul (hb _ _).2)).add ((ha _ _).2.mul (hb _ _).2)
  inv_mem' {a} ha i j := by
    change IsInt O (star ((a : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) j i)) ∧
      IsInt O (star (star ((a : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) j i)))
    rw [star_star]
    exact ⟨(ha j i).2, (ha j i).1⟩

variable (K) in

def KG : Subgroup (GL (Fin 2) K) := (GeneralLinearGroup.map (algebraMap O K)).range

variable (K) in

def ZK : Subgroup (GL (Fin 2) K) := (GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).range ⊔ KG O K

open Classical in

def fZK (χ : Kˣ →* ℂˣ) (g : GL (Fin 2) K) : ℂ :=
  if h : ∃ z : Kˣ, (GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * g ∈ KG O K then ((χ h.choose)⁻¹ : ℂˣ) else 0

def Unr (χ : Kˣ →* ℂˣ) : Prop := ∀ u : Oˣ, χ (Units.map (algebraMap O K : O →* K) u) = 1

def gOrb (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (χ : Kˣ →* ℂˣ) (z : (Etau K τ)ˣ) : ℂ :=
  orb (Units.map (j : Etau K τ →* Matrix (Fin 2) (Fin 2) K)) (Cint O τ) (MonoidHom.id _) (ZK O K) (fZK O χ)
    (Units.map (j : Etau K τ →* Matrix (Fin 2) (Fin 2) K) z)

open Classical in

def uOrb (ι : (Etau K τ)ˣ →* U3 Δ) (δ : U3 Δ) : ℂ :=
  orb ι (Cint O τ) (theta Δ) (KU O Δ) (fun g => if g ∈ KU O Δ then 1 else 0) δ

def EvenVal (x : K) : Prop := ∃ (u : Oˣ) (s : K), s ≠ 0 ∧ x = algebraMap O K u * s ^ 2

structure IsLoc [IsDomain O] [IsDiscreteValuationRing O] (Δ : K) : Prop where
  frac : IsFractionRing O K
  compl : IsAdicComplete (IsLocalRing.maximalIdeal O) O
  fin : Finite (IsLocalRing.ResidueField O)
  two : IsUnit (2 : O)
  even : EvenVal O Δ

end Lattice

example : IsDat (K := ℚ) (Δ := -1) (τ := 0) 1 ⟨⟨1 / 2, 1 / 2⟩, ⟨1 / 2, 1 / 2⟩⟩ 1 where
  reg := by norm_num
  c_ne := one_ne_zero
  d_norm := by ext <;> simp [sigL, ofE] <;> norm_num
  m_unit := isUnit_one
  m_star := by ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  m_sig := by ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> norm_num

end UpperTheory.V.Z.Sym.Loc
