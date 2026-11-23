import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeTrivialFlagMod
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivFlagModOfDvd
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivflagNefFibre
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

def zpLocSubring (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [hp : Fact p.Prime] : Subring Ω where
  carrier := {x | ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)}
  mul_mem' := by
    rintro x y ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', ?_, ?_⟩
    · intro h; rcases hp.out.dvd_mul.1 h with h | h <;> contradiction
    · push_cast; rw [div_mul_div_comm]
  one_mem' := ⟨1, 1, hp.out.not_dvd_one, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    have h0 : (b : Ω) ≠ 0 := by
      rintro h; exact hb (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero p)
    have h0' : (b' : Ω) ≠ 0 := by
      rintro h; exact hb' (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero p)
    refine ⟨a * b' + a' * b, b * b', ?_, ?_⟩
    · intro h; rcases hp.out.dvd_mul.1 h with h | h <;> contradiction
    · rw [div_add_div _ _ h0 h0']; push_cast; ring
  zero_mem' := ⟨0, 1, hp.out.not_dvd_one, by simp⟩
  neg_mem' := by
    rintro x ⟨a, b, hb, rfl⟩
    exact ⟨-a, b, hb, by push_cast; ring⟩

theorem rootModel_nefAt_of_hodgeCpt : FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [Fintype (CMType H)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω) (p : ℕ), p ∈ S → HTFree 𝔐 p → Fl.RootLines M.xdeg e → ∀ mu : Top.Wt (CMType H) (D.p + D.q), Top.Dominant mu → M.NefAt p mu 0 := by
  intro hF E _ _ _ H _ D l Xo c O _ β Y S M 𝔐 Fl e p hpS hfree hroot mu hmu
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h0 | hpos
  · intro W _
    unfold Top.RootModel.curveDeg
    refine le_of_eq (Finset.sum_eq_zero fun j _ => ?_).symm
    cases j with
    | none => simp [Top.RootModel.coef]
    | some r => exact absurd r.2.2 (by omega)
  · haveI : Fact p.Prime := ⟨𝔐.S_prime p hpS⟩
    haveI : CharZero M.Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
    let o := zpLocSubring M.Ω p
    letI : Algebra o M.Ω := o.subtype.toAlgebra
    have ho : ∀ x : M.Ω, x ∈ (algebraMap o M.Ω).range ↔
        ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : M.Ω) / (b : M.Ω) := by
      intro x
      change x ∈ o.subtype.range ↔ _
      rw [Subring.range_subtype]
      rfl
    have h1 := trivFlagMod_rootLines_model hF E H D l Xo c O β Y S M.Ω M.K M.ι M.y 𝔐 p hpS hpos o ho Fl
      M.xdeg e hfree hroot
    have hR := 𝔐.R_ge p hpS
    have h2 : ∀ τ, Num.TrivFlagMod o (p : o) M.y (D.p + D.q) (fun i => M.xdeg (τ, i)) := fun τ =>
      trivFlagMod_of_dvd o M.Ω M.K M.ι M.y _ _ _ _ (dvd_pow_self (p : o) (by omega)) (h1 τ)
    exact trivflag_nef_fibre (CMType H) (D.p + D.q) M p o ho h2 mu hmu

end GlobalTheory.CompanionTheory.Ar.HT
