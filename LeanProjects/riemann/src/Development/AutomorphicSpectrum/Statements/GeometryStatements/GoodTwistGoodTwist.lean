import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj (Rul Ix ex sec Unf IsUnf GoodEmb goodOf rdU laU relab FrPt FrMap FromTest)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

open Classical in

def goodTwist (c : Coeff l) (σ : c.F →+* ℂ) : ℂ →+* ℂ := if GoodEmb c σ then RingHom.id ℂ else starRingEnd ℂ

def letterNorm {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (k : U.Comp) (τ : E →+* ℂ) : ℝ :=
  Real.sqrt (2 * Real.pi * ‖relab c σ τ (U.X k).ξ0‖)

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y S RM Fx}

def ReadsSecAt (Fr : GenFrame Or) {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (cj : ℂ →+* ℂ)
    (z : (Σ k, RM.ι k) → ℂ) (k : U.Comp) (x : FD.Frame (U.X k).Ψ r) (t : Ix D → ℝ) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
    (∀ f ∈ sec Xo c a n, ∃ v : ℂ, HasVal RM.y 0 (Fr.rd f) z v ∧
      ‖v‖ = (U.X k).pnorm (laU U a n k) (rdU U f k) x * ∏ j, t j ^ ex D a n j) ∧
    ∀ (m : ℕ) (as : Fin m → ℂ) (fs : Fin m → Rul Xo c) (v : Fin m → ℂ), (∀ i, fs i ∈ sec Xo c a n) →
      (∀ i, HasVal RM.y 0 (Fr.rd (fs i)) z (v i)) →
      ‖∑ i, cj (as i) * v i‖ =
        (U.X k).pnorm (laU U a n k) (fun x' => ∑ i, as i * rdU U (fs i) k x') x * ∏ j, t j ^ ex D a n j

def ReadsRootsAt (Or : RootOrigin Y S RM Fx) {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (z : (Σ k, RM.ι k) → ℂ) (k : U.Comp) (t : Ix D → ℝ) : Prop :=
  ∀ ρ : RootIx D, ∃ w : ℂ, HasVal RM.y (RM.xdeg ρ) (Or.e ρ)⁻¹ z w ∧
    ‖w‖ = (letterNorm U k ρ.1.1 * t (rootFrameIx D ρ)) ^ HodgeCpt.rootSgn D ρ * (Or.sing ρ).h z

def ReadArchSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (RM : Top.RootModel (CMType H) (D.p + D.q))
    (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
    (Or : RootOrigin Y S RM Fx) (Fr : GenFrame Or) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) →
    ∃ u : MRing RM.ι, IsFormOff (mCoordIdeal RM.y) u ∧
      ∀ (σ : c.F →+* ℂ), ∀ z ∈ mcPts (mCoordIdeal RM.y), (letI := cstAlg Or; LiesOver RM.y σ z) → aeval z u ≠ 0 →
        ∃ (k : (U (goodOf c σ)).Comp) (x : FD.Frame ((U (goodOf c σ)).X k).Ψ r) (t : Ix D → ℝ),
          x ∈ ((U (goodOf c σ)).X k).dom ∧ (∀ τ i, ‖FD.dmin ((U (goodOf c σ)).X k).Gm x τ i‖ = 1) ∧
          (∀ j, 0 < t j) ∧ ReadsSecAt Fr (U (goodOf c σ)) (goodTwist c σ) z k x t ∧
          ReadsRootsAt Or (U (goodOf c σ)) z k t

theorem goodOf_apply (σ : c.F →+* ℂ) (a : c.F) : goodOf c σ a = goodTwist c σ (σ a) := by
  unfold goodOf goodTwist
  split_ifs <;> rfl

theorem goodTwist_goodTwist (σ : c.F →+* ℂ) (a : ℂ) : goodTwist c σ (goodTwist c σ a) = a := by
  unfold goodTwist
  split_ifs <;> simp

theorem norm_goodTwist (σ : c.F →+* ℂ) (a : ℂ) : ‖goodTwist c σ a‖ = ‖a‖ := by
  unfold goodTwist
  split_ifs <;> simp

theorem hasVal_const {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω F : Type} [Field Ω] [Field F]
    [Algebra F Ω] {y : (Σ k, ι k) → Ω} {σ : F →+* ℂ} {z : (Σ k, ι k) → ℂ} (hz : LiesOver y σ z) {θ : F} {v : ℂ}
    (hv : HasVal y 0 (algebraMap F Ω θ) z v) : v = σ θ := by
  obtain ⟨dg, dh, g, h, hg, hh, hd, hy, h0, hw⟩ := hv
  obtain rfl : dg = dh := funext fun k => by simpa using hd k
  have e : ∀ p : MRing ι, eval z (map (Int.castRingHom ℂ) p) = aeval z p := fun p => by
    rw [aeval_def, eval_map]; rfl
  have := hz dg g h θ hg hh hy
  rw [e, e, hw] at this
  exact mul_right_cancel₀ h0 this

example : ‖(1 : ℂ) * Complex.I + Complex.I * 1‖ ≠ ‖(1 : ℂ) * starRingEnd ℂ Complex.I + Complex.I * 1‖ := by
  simp

end GlobalTheory.CompanionTheory.Ar.Small
