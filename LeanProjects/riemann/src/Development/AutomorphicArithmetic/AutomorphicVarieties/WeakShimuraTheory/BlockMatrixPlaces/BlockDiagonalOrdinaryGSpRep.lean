import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws.Bl

section Coc

variable {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup M]

structure IsZ (ρ : Γ → M → M) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Set M) (z : Γ → M) (y : M) : Prop where
  lc : IsLocallyConstant z
  coc : ∀ g h, z (g * h) = z g + ρ g (z h)
  cz : z c = 0
  kill : ∀ g ∈ N, z g = 0
  loc : ∀ h ∈ H, z h - (ρ h y - y) ∈ P

def Zc (ρ : Γ → M → M) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Set M) : Set (Γ → M) := {z | ∃ y, IsZ ρ c N H P z y}

end Coc

section Lev

variable (A : Type) [CommRing A] [IsLocalRing A] (T : Type) [AddCommGroup T] [Module A T]

abbrev lev (n : ℕ) : Submodule A T := (maximalIdeal A ^ n) • ⊤

theorem lev_succ_le (n : ℕ) : lev A T (n + 1) ≤ lev A T n :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right n.le_succ)

def redn (n : ℕ) : (T ⧸ lev A T (n + 1)) →ₗ[A] T ⧸ lev A T n := Submodule.factor (lev_succ_le A T n)

theorem redn_mk (n : ℕ) (x : T) : redn A T n ((lev A T (n + 1)).mkQ x) = (lev A T n).mkQ x := rfl

variable {A T} {Γ : Type} [Group Γ] (ρ : Representation A Γ T)

def modRep (n : ℕ) : Representation A Γ (T ⧸ lev A T n) :=
  ρ.quotient (lev A T n) fun g => by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top

theorem modRep_mk (n : ℕ) (g : Γ) (x : T) : modRep ρ n g ((lev A T n).mkQ x) = (lev A T n).mkQ (ρ g x) := rfl

variable [TopologicalSpace Γ] (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T)

abbrev IsZn (n : ℕ) (z : Γ → T ⧸ lev A T n) (y : T ⧸ lev A T n) : Prop :=
  IsZ (fun g x => modRep ρ n g x) c N H (P.map (lev A T n).mkQ) z y

abbrev Zn (n : ℕ) : Set (Γ → T ⧸ lev A T n) := Zc (fun g x => modRep ρ n g x) c N H (P.map (lev A T n).mkQ)

def Prim {n : ℕ} (z : Γ → T ⧸ lev A T n) : Prop := ∃ g, z g ∉ (lev A T 1).map (lev A T n).mkQ

structure Lat : Prop where
  cont : ∀ n x, IsLocallyConstant fun g => (lev A T n).mkQ (ρ g x)
  stab : ∀ h ∈ H, ∀ x ∈ P, ρ h x ∈ P
  sat : ∀ (a : A) (x : T), a ≠ 0 → a • x ∈ P → x ∈ P
  ne : P ≠ ⊥
  fr : ∃ s ∈ H, Function.Bijective fun x => ρ s x - x

structure IsZT (z : Γ → T) (y : T) : Prop where
  cont : ∀ n, IsLocallyConstant fun g => (lev A T n).mkQ (z g)
  coc : ∀ g h, z (g * h) = z g + ρ g (z h)
  cz : z c = 0
  kill : ∀ g ∈ N, z g = 0
  loc : ∀ h ∈ H, z h - (ρ h y - y) ∈ P

end Lev

section Mat

variable {R : Type} [CommRing R]

variable (R) in

def hAB : Submodule R (M4 R) where
  carrier := {Y | ∀ i j, ¬ lamW i < lamW j → Y i j = 0}
  zero_mem' _ _ _ := rfl
  add_mem' ha hb i j h := by simp [ha i j h, hb i j h]
  smul_mem' c a ha i j h := by simp [ha i j h]

variable (R) in

def uM : Submodule R (M4 R) := hAB R ⊓ sp4 R

def IsSUp (X : M4 R) : Prop := ∀ i j, j ≤ i → X i j = 0

def uPlus (u : M4 R) : Submodule R (uM R) where
  carrier := {Y | IsSUp (adj u * Y.1 * u)}
  zero_mem' i j _ := by simp
  add_mem' ha hb i j h := by
    simp only [Submodule.coe_add, mul_add, add_mul, Matrix.add_apply, ha i j h, hb i j h, add_zero]
  smul_mem' c a ha i j h := by
    simp only [Submodule.coe_smul, mul_smul_comm, smul_mul_assoc, Matrix.smul_apply, ha i j h, smul_zero]

def eAB (R : Type) [CommRing R] : M4 R := Matrix.diagonal ![-1, 1, -1, 1]

theorem hAB_mul_mul {X Y Z : M4 R} (hX : IsBlock X) (hY : Y ∈ hAB R) (hZ : IsBlock Z) : X * Y * Z ∈ hAB R := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases e : lamW b = lamW j
  · rw [Matrix.mul_apply, Finset.sum_eq_zero fun a _ => ?_, zero_mul]
    by_cases e' : lamW i = lamW a
    · rw [hY a b (by rw [← e', e]; exact h), mul_zero]
    · rw [hX i a e', zero_mul]
  · rw [hZ b j e, mul_zero]

theorem hAB_mul_hAB {Y Z : M4 R} (hY : Y ∈ hAB R) (hZ : Z ∈ hAB R) : Y * Z = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases e : lamW i < lamW b
  · have h : ∀ i b j : Fin 4, lamW i < lamW b → ¬ lamW b < lamW j := by decide
    rw [hZ b j (h i b j e), mul_zero]
  · rw [hY i b e, zero_mul]

variable {Γ : Type} [Group Γ]

structure BG (r : Γ →* M4 R) : Prop where
  gsp : ∀ g, ∃ ν, IsGSp ν (r g)
  blk : ∀ g, IsBlock (r g)

theorem BG.mem {r : Γ →* M4 R} (h : BG r) (g : Γ) {Y : M4 R} (hY : Y ∈ uM R) : r g * Y * r g⁻¹ ∈ uM R := by
  refine ⟨hAB_mul_mul (h.blk g) hY.1 (h.blk _), ?_⟩
  obtain ⟨m, -, -, -, o, -, a, p, -⟩ := grp R
  obtain ⟨ν, hν⟩ := h.gsp g
  obtain ⟨ν', hν'⟩ := h.gsp g⁻¹
  have e1 : r g * r g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have e2 : r g⁻¹ * r g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have e3 : ν * ν' = 1 := by
    have := p _ _ _ _ hν hν'
    rw [e1, IsGSp, o, one_mul] at this
    simpa using (congrFun (congrFun this 0) 0).symm
  have e4 : adj Y = -Y := hY.2
  show adj _ = -_
  rw [m, m, a _ _ _ hν e1, a _ _ _ hν' e2, e4, smul_mul_assoc, mul_smul_comm, mul_smul_comm, smul_smul, mul_comm ν', e3, one_smul,
    neg_mul, mul_neg, mul_assoc]

def adU {r : Γ →* M4 R} (h : BG r) : Representation R Γ (uM R) where
  toFun s :=
    { toFun := fun Y => ⟨r s * Y.1 * r s⁻¹, h.mem s Y.2⟩
      map_add' := fun Y Y' => Subtype.ext (by simp [mul_add, add_mul])
      map_smul' := fun c Y => Subtype.ext (by simp) }
  map_one' := LinearMap.ext fun Y => Subtype.ext (by simp)
  map_mul' s t := LinearMap.ext fun Y => Subtype.ext (by simp [mul_assoc])

theorem adU_val {r : Γ →* M4 R} (h : BG r) (g : Γ) (Y : uM R) : (adU h g Y).1 = r g * Y.1 * r g⁻¹ := rfl

structure Sep [IsLocalRing R] (X : M4 R) : Prop where
  off : ∀ i j, i ≠ j → X i j ∈ maximalIdeal R
  unit : ∀ i j, lamW i ≠ lamW j → IsUnit (X i i - X j j)

end Mat

section Gal

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

def neSet (l : ℕ) (K : Subgroup (G ℚ Ω)) : Set (G ℚ Ω) :=
  {g | g ∈ K ∧ ∃ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := ℚ) A}

structure Pos (l : ℕ) [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω) : Prop where
  odd : l ≠ 2
  prime : ∀ p ∈ S, p.Prime
  mem : l ∈ S
  cc : IsCC c
  ovl : B.valuation (l : Ω) < 1
  dec : s ∈ Dec (F := ℚ) B
  cyc : cycZ ℚ Ω l s = 1

structure BlockDiagonalOrdinaryGSpRep (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω) {A : Type} [CommRing A] [IsLocalRing A]
    (r : G ℚ Ω →* M4 A) (u : M4 A) : Prop where
  bg : BG r
  cont : ∀ i j, AdicCont (maximalIdeal A) fun g => r g i j
  unr : ∀ B', Raw.Away S B' → Ine (F := ℚ) B' ≤ r.ker
  sp : IsGSp 1 u
  flag : ∀ h ∈ Dec (F := ℚ) B, IsUp (adj u * r h * u)
  sep : Sep (r s)
  char : ∀ i, (adj u * r s * u) i i - r s i i ∈ maximalIdeal A
  cc : r c = eAB A

end Gal

example {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] (ρ : Γ → M →+ M) (c : Γ) (N : Set Γ) (H : Subgroup Γ) :
    (0 : Γ → M) ∈ Zc (fun g x => ρ g x) c N H {0} :=
  ⟨0, IsLocallyConstant.const 0, by simp, rfl, by simp, by simp⟩

example {R : Type} [CommRing R] : Matrix.single 1 2 (1 : R) ∈ uM R := by
  refine ⟨fun i j h => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [lamW]
  · show adj _ = -_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.single_apply]

end UpperTheory.V.Ws.Bl

end
