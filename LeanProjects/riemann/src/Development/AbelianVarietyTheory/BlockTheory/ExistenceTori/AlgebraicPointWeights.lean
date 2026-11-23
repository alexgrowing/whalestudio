import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def WeightOverFields : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n →
    ∀ (S : Type) [Field S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' →
      evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y

def IntegralDiagUnit : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (t : Ix Dw → T.Frˣ),
    (letI := io.toAlgebra; FrBor t y.1 y'.1) →
      ∀ i : Ix Dw, ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = (t i : T.Fr)

def AlgebraicPointOver : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ),
    OverLa la T.V io e ∧ T.FinRes ∧ Nonempty (letI := io.toAlgebra; FrPt Xo c T.Fr)

def IntegralFrameAfterExt : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    letI := io.toAlgebra
    ∀ y : FrPt Xo c T.Fr, ∃ (T' : CDVR) (io' : c.F →+* T'.Fr),
      letI := io'.toAlgebra
      ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (r : ℕ), 0 < r ∧ (∀ x : T.Fr, vV T'.V (φ x) = (r : ℤ) * vV T.V x) ∧
        φ.toRingHom.Finite ∧ (T.FinRes → T'.FinRes) ∧
        ∃ (z : FrPt Xo c T'.Fr) (y' : IntFr Xo c T' io') (t : Ix Dw → T'.Frˣ), FrMap φ y z ∧ FrBor t z y'.1

structure AlgebraicLaws : Prop where
  weight : WeightOverFields Xo c
  unitDiag : IntegralDiagUnit Xo c
  algPoint : AlgebraicPointOver Xo c
  intFrame : IntegralFrameAfterExt Xo c

variable {Xo c}

theorem unitIndep_of (h₁ : WeightOverFields Xo c) (h₂ : IntegralDiagUnit Xo c) : UnitIndep Xo c := by
  intro a n f hf T io y y' t hb e
  letI := io.toAlgebra
  have hw : evI y' f = wchar (ex Dw a n) t * evI y f := h₁ a n f hf T.Fr t y.1 y'.1 hb
  choose u hu using h₂ T io y y' t hb
  have hU : (wchar (ex Dw a n) t : T.Fr) = algebraMap T.V T.Fr ((∏ i, u i ^ ex Dw a n i : T.Vˣ) : T.V) := by
    simp [wchar, hu]
  rw [hw, hU, nval_mul_unit]
  · exact (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 (Units.ne_zero _)
  · have : valV T.V (algebraMap T.V T.Fr ((∏ i, u i ^ ex Dw a n i : T.Vˣ) : T.V)) = 1 := by
      unfold valV
      rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
      exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h (Units.isUnit _)
    simp only [vV, this, WithZero.log_one, neg_zero]

theorem intFrNe_of (h₁ : AlgebraicPointOver Xo c) (h₂ : IntegralFrameAfterExt Xo c) :
    IntFrNe Xo c (fun _ _ y => y.IsAlg) := by
  intro la
  obtain ⟨T, io, e, ho, hT, ⟨y⟩⟩ := h₁ la
  obtain ⟨T', io', φ, r, hr, hv, -, hfin, z, y', t, -, -⟩ := h₂ la T io e ho y
  letI := io.toAlgebra
  letI := io'.toAlgebra
  have hc : (φ : T.Fr →+* T'.Fr).comp io = io' := RingHom.ext fun x => φ.commutes x
  exact ⟨T', io', r * e, hc ▸ ho.bc (φ : T.Fr →+* T'.Fr) hr hv, y', hfin hT⟩

end GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights
