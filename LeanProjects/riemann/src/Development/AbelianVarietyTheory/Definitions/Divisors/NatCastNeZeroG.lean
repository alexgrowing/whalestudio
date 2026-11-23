import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad

namespace GlobalTheory.ConstLat

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def RelFlag {C : CxSt F} {N : ℕ} (A A' : Fin N → Adl C Y) (p n k : ℕ) : Prop :=
  n ≠ 0 ∧ ∃ (V : Cover Y) (W : Y.X.Opens) (ι : Type) (U : ι → V.X.Opens) (M M' : ι → Matrix (Fin N) (Fin N) V.X.functionField)
    (c c' : ι → Fin N → V.G.functionFieldˣ) (P Q : Matrix (Fin N) (Fin N) V.X.functionField), genericPoint Y.X ∈ W ∧
    P * Q = 1 ∧ (∀ i j, IsIntegral ℤ ((n : V.X.functionField) * P i j) ∧ IsIntegral ℤ ((n : V.X.functionField) * Q i j)) ∧
    (∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ a, x ∈ U a) ∧
    (∀ a, ∀ x ∈ U a, ¬ IsUnit (p : V.X.presheaf.stalk x) →
      (∀ i j, RegAt x (M a i j) ∧ RegAt x (M' a i j) ∧ RegAt x ((n : V.X.functionField) * P i j)) ∧
        UnitAt x (M a).det ∧ UnitAt x (M' a).det) ∧
    (∀ a i (z : V.G), V.j z ∈ U a →
      UnitAt z (V.φ (genAt (A i).D (V.π z)) * c a i) ∧ UnitAt z (V.φ (genAt (A' i).D (V.π z)) * c' a i)) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W →
      ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
        (∀ i, (A i).lg v e y =
            Real.log (e.w (valAt z (V.φ (genAt (A i).D (below y.1)) * (c a i : V.G.functionField)))) ∧
          (A' i).lg v e y =
            Real.log (e.w (valAt z (V.φ (genAt (A' i).D (below y.1)) * (c' a i : V.G.functionField))))) ∧
        ∀ b, ⊤ ≤ yt ⁻¹ᵁ U b → ∀ i,
          (∀ j, j < i → e.w (valAt (z ≫ V.j) (((M' a)⁻¹ * P * M b) i j)) ≤ e.w (p : AlgebraicClosure F) ^ k) ∧
          e.w (valAt (z ≫ V.j) (((M' a)⁻¹ * P * M b) i i) -
            valAt z ((c' a i / c b i : V.G.functionFieldˣ) : V.G.functionField)) ≤ e.w (p : AlgebraicClosure F) ^ k

theorem RelFlag.ne_zero {C : CxSt F} {N : ℕ} {A A' : Fin N → Adl C Y} {p n k : ℕ} (h : RelFlag A A' p n k) : n ≠ 0 :=
  h.1

theorem RelFlag.mono {C : CxSt F} {N : ℕ} {A A' : Fin N → Adl C Y} {p n k k' : ℕ} (h : RelFlag A A' p n k)
    (hk : k' ≤ k) : RelFlag A A' p n k' := by
  obtain ⟨hn, V, W, ι, U, M, M', c, c', P, Q, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨hn, V, W, ι, U, M, M', c, c', P, Q, h₁, h₂, h₃, h₄, h₅, h₆, fun v hv e y hy z yt hz hyt a ha => ?_⟩
  obtain ⟨hl, hab⟩ := h₇ v hv e y hy z yt hz hyt a ha
  have hp : e.w (p : AlgebraicClosure F) ^ k ≤ e.w (p : AlgebraicClosure F) ^ k' :=
    pow_le_pow_of_le_one (e.w.nonneg _) ((e.mem_O _).1 (natCast_mem e.O p)) hk
  exact ⟨hl, fun b hb i => ⟨fun j hj => ((hab b hb i).1 j hj).trans hp, (hab b hb i).2.trans hp⟩⟩

namespace RelEx

theorem valAt_natCast {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) (m : ℕ) :
    TrueGeo.valAt y (m : Z.functionField) = m := by
  rw [← map_natCast (algebraMap (Z.presheaf.stalk (below y)) Z.functionField), SmallSec.valAt_algebraMap, map_natCast]

theorem regAt_natCast {Z : Scheme.{0}} [IsIntegral Z] (x : Z) (m : ℕ) : RegAt x (m : Z.functionField) :=
  ⟨m, map_natCast _ _⟩

theorem isUnit_natCast (V : Cover Y) (z : V.G) {m : ℕ} (hm : m ≠ 0) : IsUnit (m : V.G.presheaf.stalk z) := by
  let ψ : F →+* V.G.presheaf.stalk z := (V.G.presheaf.germ ⊤ z trivial).hom.comp
    ((V.π ≫ Y.str).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)
  have h : IsUnit (m : F) := (Nat.cast_ne_zero.2 hm).isUnit
  simpa using h.map ψ

theorem natCast_ne_zero_X (V : Cover Y) {m : ℕ} (hm : m ≠ 0) : (m : V.X.functionField) ≠ 0 := by
  intro h
  let z := genericPoint V.G
  have h1 : (m : V.X.presheaf.stalk (V.j z)) = 0 :=
    IsFractionRing.injective _ V.X.functionField (by rw [map_natCast, map_zero, h])
  have h2 := congrArg (V.j.stalkMap z).hom h1
  rw [map_natCast, map_zero] at h2
  exact (isUnit_natCast V z hm).ne_zero h2

def scaled (C : CxSt F) (Y : Var F) (m : ℕ) : Adl C Y :=
  { Adl.triv C Y with lg := fun v e y => (Adl.triv C Y).lg v e y + Real.log (e.w m) }

end RelEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

def eigAt (a : ℕ → Bool) (R : Option ℝ) (s : ℤ) (k : ℕ) : Sym E →₀ ℤ :=
  match (letters Dw)[k]? with
  | some z => Finsupp.single (a, R, .inl (z.1, (z.2 : ℕ))) s
  | none => 0

def eigSym (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} : Fin g ⊕ Fin g → (Sym E →₀ ℤ)
  | .inl k => eigAt Dw a R 1 k
  | .inr k => eigAt Dw a R (-1) (Fin.rev k)

theorem eigAt_of_lt (a : ℕ → Bool) (R : Option ℝ) (s : ℤ) {k : ℕ} (h : k < (letters Dw).length) :
    eigAt Dw a R s k = Finsupp.single (a, R, .inl ((letters Dw)[k].1, ((letters Dw)[k].2 : ℕ))) s := by
  unfold eigAt
  rw [List.getElem?_eq_getElem h]

@[simp] theorem eigSym_inl (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} (k : Fin g) :
    eigSym Dw a R (.inl k) = eigAt Dw a R 1 k := rfl

@[simp] theorem eigSym_inr (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} (k : Fin g) :
    eigSym Dw a R (.inr k) = eigAt Dw a R (-1) (Fin.rev k) := rfl

theorem expo_eigSym (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} (i : Fin g ⊕ Fin g) :
    expo Dw (eigSym Dw a R i) = expo Dw (wholeSym a R i) := by
  have key : ∀ (s : ℤ) (k : ℕ), expo Dw (eigAt Dw a R s k) = expo Dw (Finsupp.single (a, R, .inr k) s) := by
    intro s k
    funext x
    unfold eigAt expo
    cases h : (letters Dw)[k]? with
    | none => simp [letterOf, h]
    | some z =>
      dsimp only
      rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
      have e : letterOf Dw (.inl (z.1, (z.2 : ℕ))) = letterOf Dw (.inr k) := (dif_pos z.2.2).trans h.symm
      dsimp only
      rw [e]
  cases i <;> exact key _ _

end GlobalTheory.ConstLat

end
