import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharExCol
import Formalism.LocalToGlobal.UnitaryNorms.CharExFacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteEtaGenerators.CompEqEmbedding
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfinityTypeCharacter.ContinuousUnitsMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GlobalFormGenerator.IntValuationConjP
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HostFieldFacts.HostFieldFacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HostPrimeSplitting.FinrankOE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HostPrimeSplitting.DSplit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMTypeEmbeddings.OnePsi
import Formalism.LocalToGlobal.UnitaryNorms.CharExMu

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Col

namespace HeckeEx

open Formalism.L2.Host Formalism.L2.Host.CharEx

section Gen

variable {L : Type} [Field L] [NumberField L]

def compU (w : HeightOneSpectrum (𝓞 L)) : Ideles L →* (w.adicCompletion L)ˣ :=
  Units.map
    { toFun := fun a => a.2 w
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem exists_unifO (w : HeightOneSpectrum (𝓞 L)) : ∃ ϖ : 𝓞 L, ϖ ∈ w.asIdeal ∧ ϖ ∉ w.asIdeal ^ 2 := by
  have hlt : w.asIdeal ^ 2 < w.asIdeal := Ideal.pow_lt_self w.asIdeal w.ne_bot w.isPrime.ne_top 2 le_rfl
  obtain ⟨x, hx, hx2⟩ := SetLike.exists_of_lt hlt
  exact ⟨x, hx, hx2⟩

def resU (w : HeightOneSpectrum (𝓞 L)) (y : 𝓞 L) (hy : y ∉ w.asIdeal) : (𝓞 L ⧸ w.asIdeal)ˣ :=
  haveI := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  Units.mk0 (Ideal.Quotient.mk w.asIdeal y) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])

theorem ne_zero_of_notMem {w : HeightOneSpectrum (𝓞 L)} {y : 𝓞 L} (hy : y ∉ w.asIdeal) : (y : L) ≠ 0 := by
  intro h
  apply hy
  have : y = 0 := by exact_mod_cast h
  rw [this]
  exact w.asIdeal.zero_mem

def unitO {w : HeightOneSpectrum (𝓞 L)} (y : 𝓞 L) (hy : y ∉ w.asIdeal) : Lˣ := Units.mk0 (y : L) (ne_zero_of_notMem hy)

def TameSpec (w : HeightOneSpectrum (𝓞 L)) (ϖ : 𝓞 L) (c : (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ) (lam : (w.adicCompletion L)ˣ →* ℂˣ) : Prop :=
  (∀ x : Lˣ, (x : L) = (ϖ : L) → lam (atFin w x) = 1) ∧
  (∀ x, IsUnitAt w x → ‖((lam x : ℂˣ) : ℂ)‖ = 1) ∧
  (∀ x, IsUnitAt w x → Valued.v ((x : w.adicCompletion L) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) → lam x = 1) ∧
  (∀ (x : Lˣ) (y : 𝓞 L) (cl : (𝓞 L ⧸ w.asIdeal)ˣ), (x : L) = (y : L) →
    (cl : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal y → lam (atFin w x) = c cl)

def TameLocEx : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (ϖ : 𝓞 L), ϖ ∈ w.asIdeal → ϖ ∉ w.asIdeal ^ 2 →
    ∀ c : (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ, ∃ lam : (w.adicCompletion L)ˣ →* ℂˣ, TameSpec w ϖ c lam

def LocRep : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (ϖ : 𝓞 L), ϖ ∈ w.asIdeal → ϖ ∉ w.asIdeal ^ 2 →
    ∀ x : L, x ≠ 0 → ∃ (y z : 𝓞 L) (n : ℤ), y ∉ w.asIdeal ∧ z ∉ w.asIdeal ∧ x * (z : L) = (y : L) * (ϖ : L) ^ n

def tameSet (L : Type) [Field L] [NumberField L] (S : Finset (HeightOneSpectrum (𝓞 L))) : Set (Ideles L) :=
  {u | u ∈ unitIdeles L ∧ ∀ w ∈ S, Valued.v ((u : AdeleRing (𝓞 L) L).2 w - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ))}

def OpenTame : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (S : Finset (HeightOneSpectrum (𝓞 L))), IsOpen (tameSet L S)

end Gen

section Col

variable {X : Fields}

theorem hxConjO_invol (X : Fields) (x : 𝓞 X.E) : X.conjO (X.conjO x) = x := by
  apply RingOfIntegers.ext
  show star (star (x : X.E)) = x
  exact star_star _

def cP (X : Fields) (w : HeightOneSpectrum (𝓞 X.E)) : HeightOneSpectrum (𝓞 X.E) where
  asIdeal := w.asIdeal.comap X.conjO
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    intro h
    have h1 : X.conjO p ∈ w.asIdeal.comap X.conjO := by
      rw [Ideal.mem_comap, hxConjO_invol X]; exact hp
    rw [h, Ideal.mem_bot] at h1
    apply hp0
    rw [← hxConjO_invol X p, h1, map_zero]

theorem mem_cP (w : HeightOneSpectrum (𝓞 X.E)) (r : 𝓞 X.E) : r ∈ (cP X w).asIdeal ↔ X.conjO r ∈ w.asIdeal := Iff.rfl

theorem conj_mem_cP {w : HeightOneSpectrum (𝓞 X.E)} {y : 𝓞 X.E} (hy : y ∈ w.asIdeal) : X.conjO y ∈ (cP X w).asIdeal := by
  rw [mem_cP, hxConjO_invol X]; exact hy

theorem conj_notMem_sq_cP {w : HeightOneSpectrum (𝓞 X.E)} {y : 𝓞 X.E} (hy : y ∉ w.asIdeal ^ 2) :
    X.conjO y ∉ (cP X w).asIdeal ^ 2 := by
  intro h
  have h2 : (cP X w).asIdeal ^ 2 ≤ (w.asIdeal ^ 2).comap X.conjO := Ideal.le_comap_pow _ 2
  have h3 := h2 h
  rw [Ideal.mem_comap, hxConjO_invol X] at h3
  exact hy h3

def conjU (X : Fields) : X.Eˣ →* X.Eˣ := Units.map (starRingEnd X.E).toMonoidHom

def resConj (X : Fields) (w : HeightOneSpectrum (𝓞 X.E)) : 𝓞 X.E ⧸ (cP X w).asIdeal →+* 𝓞 X.E ⧸ w.asIdeal :=
  Ideal.quotientMap w.asIdeal X.conjO le_rfl

variable {Pr : Primes X} {m : ℕ} (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (j : Fin m)

def cW (w : {w // w ∈ Pr.vGs}) : (𝓞 X.E ⧸ w.1.asIdeal)ˣ →* ℂˣ :=
  ((Units.map σ₀.toMonoidHom).comp (Ch.chi j w))⁻¹

def cB (w : {w // w ∈ Pr.vGs}) : (𝓞 X.E ⧸ (cP X w.1).asIdeal)ˣ →* ℂˣ :=
  ((cW Ch σ₀ j w).comp (Units.map (resConj X w.1).toMonoidHom))⁻¹

def unifW (w : HeightOneSpectrum (𝓞 X.E)) : 𝓞 X.E := (exists_unifO w).choose

theorem unifW_mem (w : HeightOneSpectrum (𝓞 X.E)) : unifW w ∈ w.asIdeal := (exists_unifO w).choose_spec.1

theorem unifW_notMem (w : HeightOneSpectrum (𝓞 X.E)) : unifW w ∉ w.asIdeal ^ 2 := (exists_unifO w).choose_spec.2

variable (hT : TameLocEx)

def lamW (w : {w // w ∈ Pr.vGs}) : (w.1.adicCompletion X.E)ˣ →* ℂˣ :=
  (hT X.E w.1 (unifW w.1) (unifW_mem w.1) (unifW_notMem w.1) (cW Ch σ₀ j w)).choose

def lamB (w : {w // w ∈ Pr.vGs}) : ((cP X w.1).adicCompletion X.E)ˣ →* ℂˣ :=
  (hT X.E (cP X w.1) (X.conjO (unifW w.1)) (conj_mem_cP (unifW_mem w.1)) (conj_notMem_sq_cP (unifW_notMem w.1))
    (cB Ch σ₀ j w)).choose

def psiF : Ideles X.E →* ℂˣ :=
  ∏ w : {w // w ∈ Pr.vGs}, ((lamW Ch σ₀ j hT w).comp (compU w.1) * (lamB Ch σ₀ j hT w).comp (compU (cP X w.1)))

variable {Ch σ₀ j hT}

theorem conjPrime_under₂ (hX : X.Ok) (w : HeightOneSpectrum (𝓞 X.E)) : (cP X w).under (𝓞 X.F) = w.under (𝓞 X.F) := by
  apply HeightOneSpectrum.ext
  ext r
  show X.conjO (algebraMap (𝓞 X.F) (𝓞 X.E) r) ∈ w.asIdeal ↔ algebraMap (𝓞 X.F) (𝓞 X.E) r ∈ w.asIdeal
  have e : X.conjO (algebraMap (𝓞 X.F) (𝓞 X.E) r) = algebraMap (𝓞 X.F) (𝓞 X.E) r := by
    apply RingOfIntegers.ext
    show star ((algebraMap (𝓞 X.F) (𝓞 X.E) r : 𝓞 X.E) : X.E) = _
    have e2 : ((algebraMap (𝓞 X.F) (𝓞 X.E) r : 𝓞 X.E) : X.E) = algebraMap X.F X.E (r : X.F) := rfl
    rw [e2, hX.star_F]
  rw [e]

variable (Ch σ₀ j hT)

open Classical in

def ramS : Finset (HeightOneSpectrum (𝓞 X.E)) := Pr.vGs ∪ Pr.vGs.image (cP X)

end Col

section Eta

variable {X : Fields}

open Classical in

structure EtaFactsC (X : Fields) (σ₀ : X.K →+* ℂ) (s0 : X.E) : Prop where
  unram : ∀ P : HeightOneSpectrum (𝓞 X.E), (aboveF (L := X.E) X.F (P.under (𝓞 X.F))).card = 1 →
    P.asIdeal.ramificationIdx (𝓞 X.F) = 1
  onePsi : ∀ w : InfinitePlace X.F,
    (Finset.univ.filter (fun i => InfinitePlace.mk (X.embC σ₀ i) ∈ aboveInf (L := X.E) X.F w)).card = 1
  fixF : ∀ x : X.E, star x = x → ∃ a : X.F, algebraMap X.F X.E a = x
  roots : ∀ z : X.E, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) → z = 1 ∨ z = -1
  sqrt_ne : s0 ≠ 0
  isCMField_complexConj_s_eq_neg : star s0 = -s0
  sqrt_pos : ∀ s : X.Eˣ, (s : X.E) = s0 → ∀ i, ∃ r : ℝ, 0 < r ∧ X.embC σ₀ i (s : X.E) = Complex.I * r
  card4 : 4 ∣ Fintype.card X.Tau
  dsplit : ∀ s : X.Eˣ, (s : X.E) = s0 →
    ∀ P : HeightOneSpectrum (𝓞 X.E), ordF P s ≠ 0 → (aboveF (L := X.E) X.F (P.under (𝓞 X.F))).card ≠ 1

def conjAlg (hX : X.Ok) : X.E →ₐ[X.F] X.E :=
  { starRingEnd X.E with commutes' := fun a => hX.star_F a }

end Eta

end HeckeEx

end Formalism.L2.Col
