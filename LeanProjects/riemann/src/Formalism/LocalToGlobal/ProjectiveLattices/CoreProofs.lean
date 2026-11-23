import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Open

variable (Xo : Moduli Dw l) (c : Coeff l)

def WtField : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n →
    ∀ (S : Type) [Field S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S),
      FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y →
      FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y' →
      FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y

def IntDiagUnit : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (t : Ix Dw → T.Frˣ),
    (letI := io.toAlgebra; FrBor t y.1 y'.1) → ∀ i, valV T.V ((t i : T.Frˣ) : T.Fr) = 1

def AlgPtLa : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la T.V io e),
    T.FinRes ∧ ∃ x : Sp T.Fr ⟶ Xo.X, (letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr)

def IntFrExt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr), T.FinRes → ∀ x : Sp T.Fr ⟶ Xo.X, (letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr) →
    ∃ (T' : CDVR) (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r ∧ (∀ z, vV T'.V (i z) = (r : ℤ) * vV T.V z) ∧ T'.FinRes ∧
      ∃ y : IntFr Xo c T' (i.comp io), (letI := (i.comp io).toAlgebra; y.1.x = spMap i ≫ x)

end Open

section Proofs

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem valV_wchar_eq_one {T : CDVR} (e : Ix Dw → ℕ) (t : Ix Dw → T.Frˣ)
    (ht : ∀ i, valV T.V ((t i : T.Frˣ) : T.Fr) = 1) : valV T.V (wchar e t) = 1 := by
  simp [wchar, map_prod, map_pow, ht]

private theorem vV_mul_lemma {T : CDVR} {w x : T.Fr} (hu : valV T.V w = 1) (hx : x ≠ 0) :
    vV T.V (w * x) = vV T.V x := by
  unfold vV
  rw [map_mul, hu, one_mul]

theorem unitIndep_of (hW : WtField Xo c) (hU : IntDiagUnit Xo c) : UnitIndep Xo c := by
  intro a n f hf T io y y' t hb e
  letI := io.toAlgebra
  have hw := hW a n f hf T.Fr t y.1 y'.1 y.2.1 y'.2.1 hb
  have hu := valV_wchar_eq_one (ex Dw a n) t (hU T io y y' t hb)
  unfold nval evI
  rw [hw]
  generalize evR Xo c f y.1 = x at *
  have hne : wchar (ex Dw a n) t ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hu
    exact zero_ne_one hu
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg (mul_ne_zero hne hx), if_neg hx, vV_mul_lemma hu hx]

theorem intFrNe_of (hA : AlgPtLa Xo c) (hE : IntFrExt Xo c) :
    IntFrNe Xo c (fun _ _ y => IntFr.IsAlg y) := by
  intro la
  obtain ⟨T, io, e, hO, hF, x, hx⟩ := hA la
  obtain ⟨T', i, r, hr, hv, hF', y, hy⟩ := hE T io hF x hx
  unfold OverLa IntFr.IsAlg at *
  refine ⟨T', i.comp io, r * e, ⟨Nat.mul_pos hr hO.1, fun a => ?_⟩, y, hF'⟩
  rw [RingHom.comp_apply, hv, hO.2 a]
  push_cast
  ring

end Proofs

end Formalism.L2.Pj
