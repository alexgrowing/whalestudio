import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open scoped Pointwise

namespace UpperTheory.V

namespace AbF

instance (A : AbF) : NeZero A.m := ⟨A.pos.ne'⟩

def sup (A B : AbF) : AbF :=
  ⟨A.m * B.m, Nat.mul_pos A.pos B.pos,
    A.H.comap (ZMod.unitsMap (dvd_mul_right _ _)) ⊓ B.H.comap (ZMod.unitsMap (dvd_mul_left _ _))⟩

def quad (p : ℕ) : AbF := ⟨max p 1, by omega, (powMonoidHom 2 : (ZMod (max p 1))ˣ →* _).range⟩

end AbF

namespace Two

def withI (M : AbF) : AbF := M.sup (AbF.cyc 4)

def base2 (M : AbF) (q d : ℕ) : AbF := ((withI M).sup (AbF.quad q)).sup (AbF.quad d)

theorem modulus_adjoinISqrtNegPrimes (M : AbF) {q d : ℕ} (hq : 0 < q) (hd : 0 < d) : (base2 M q d).m = M.m * 4 * q * d := by
  simp only [base2, withI, AbF.sup, AbF.cyc, AbF.quad]
  rw [max_eq_left (by omega : 1 ≤ 4), max_eq_left (by omega : 1 ≤ q), max_eq_left (by omega : 1 ≤ d)]

def CardLe (P : Type) (n : ℕ) : Prop := Finite P ∧ Nat.card P ≤ n

theorem CardLe.mono {P : Type} {n n' : ℕ} (h : CardLe P n) (hn : n ≤ n') : CardLe P n' := ⟨h.1, h.2.trans hn⟩

theorem CardLe.of_injective {P Q : Type} {n : ℕ} (h : CardLe Q n) (f : P → Q) (hf : Function.Injective f) : CardLe P n := by
  haveI := h.1
  haveI : Finite P := Finite.of_injective f hf
  exact ⟨inferInstance, (Nat.card_le_card_of_injective f hf).trans h.2⟩

def CharOff {Γ : Type} [Group Γ] [TopologicalSpace Γ] (U : Subgroup Γ) (S : Set Γ) (l : ℕ) :
    Submodule (ZMod l) (U → ZMod l) where
  carrier := {φ | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u : U, u.1 ∈ S → φ u = 0}
  zero_mem' := ⟨IsLocallyConstant.const _, by simp, by simp⟩
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun x y => by simp only [Pi.add_apply, ha.2.1, hb.2.1]; abel,
    fun u h => by simp [ha.2.2 u h, hb.2.2 u h]⟩
  smul_mem' c a ha := ⟨ha.1.comp (c • ·), fun x y => by simp [ha.2.1, mul_add], fun u h => by simp [ha.2.2 u h]⟩

section

variable (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def ineOff (N : ℕ) : Set (G F Ω) := {g | ∃ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 ∧ g ∈ Ine (F := F) A}

variable {F Ω}

def XRk (l N : ℕ) (U : Subgroup (G F Ω)) (r : ℕ) : Prop := CardLe (XDual N U (ZMod l) (ZMod l)) (l ^ r)

def OrbLe (V : Subgroup (G F Ω)) (p n : ℕ) : Prop :=
  ∃ T : Finset (ValuationSubring Ω), T.card ≤ n ∧ (∀ B ∈ T, B.valuation (p : Ω) < 1) ∧
    ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∃ B ∈ T, ∃ v ∈ V, v • B = A

theorem xDual_one (U : Subgroup (G F Ω)) (l : ℕ) : XDual 1 U (ZMod l) (ZMod l) = CharOff U (ineOff F Ω 1) l := by
  ext φ
  constructor
  · rintro ⟨h1, h2, h3, -⟩
    refine ⟨h1, h2, ?_⟩
    rintro u ⟨A, -, hA⟩
    exact h3 A u hA
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_, ?_⟩
    · intro A u hu
      exact h3 u ⟨A, by simp, hu⟩
    · intro A hA
      simp at hA

theorem xDual_le_charOff (N N' : ℕ) (U : Subgroup (G F Ω)) (l : ℕ) :
    XDual N U (ZMod l) (ZMod l) ≤ CharOff U (ineOff F Ω N') l := by
  rintro φ ⟨h1, h2, h3, -⟩
  refine ⟨h1, h2, ?_⟩
  rintro u ⟨A, -, hA⟩
  exact h3 A u hA

theorem XRk.mono {l N : ℕ} {U : Subgroup (G F Ω)} {r r' : ℕ} (hl : 0 < l) (h : XRk l N U r) (hr : r ≤ r') : XRk l N U r' :=
  CardLe.mono h (Nat.pow_le_pow_right hl hr)

theorem XRk.of_one {l : ℕ} {U : Subgroup (G F Ω)} {r : ℕ} (h : XRk l 1 U r) (N : ℕ) : XRk l N U r := by
  have hle : XDual N U (ZMod l) (ZMod l) ≤ XDual 1 U (ZMod l) (ZMod l) := by
    rw [xDual_one]
    exact xDual_le_charOff N 1 U l
  exact CardLe.of_injective h (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

end

section

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem card_roots (m : ℕ) [NeZero m] : Nat.card (rootsOfUnity m Ω) = m := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
  haveI : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne m)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  exact hζ.card_rootsOfUnity

def galChar (m : ℕ) [NeZero m] : G ℚ Ω →* (ZMod m)ˣ where
  toFun g := modularCyclotomicCharacter Ω (card_roots Ω m) g.toRingEquiv
  map_one' := map_one (modularCyclotomicCharacter Ω (card_roots Ω m))
  map_mul' g h := map_mul (modularCyclotomicCharacter Ω (card_roots Ω m)) g.toRingEquiv h.toRingEquiv

variable {Ω} in
theorem galChar_spec (m : ℕ) [NeZero m] (g : G ℚ Ω) (ζ : Ω) (hζ : ζ ^ m = 1) : g ζ = ζ ^ (galChar Ω m g : ZMod m).val := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne m)] at hζ
    exact zero_ne_one hζ
  have hmem : Units.mk0 ζ hζ0 ∈ rootsOfUnity m Ω := by
    rw [mem_rootsOfUnity]
    ext
    simpa using hζ
  exact modularCyclotomicCharacter.spec Ω (card_roots Ω m) g.toRingEquiv hmem

def abU (A : AbF) : Subgroup (G ℚ Ω) := A.H.comap (galChar Ω A.m)

instance (A : AbF) : (abU Ω A).Normal := by unfold abU; infer_instance

end

end Two

end UpperTheory.V

end
