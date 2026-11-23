import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrViaNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkSpecializesCompatRingMap
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory

set_option autoImplicit false

noncomputable section

open GlobalTheory.Toroidal Formalism.L2.Geo

namespace GlobalTheory.CovHt.Link

theorem eq_of_stalkSpecializes {X : Scheme.{0}} {R α : Type} [CommRing R]
    (G : (b : X) → (X.presheaf.stalk b →+* R) → α) {b' b : X} (h : b' ⤳ b) (e : b' = b)
    (ψ' : X.presheaf.stalk b' →+* R) (ψ : X.presheaf.stalk b →+* R)
    (hψ : ∀ a, ψ' ((X.presheaf.stalkSpecializes h).hom a) = ψ a) : G b' ψ' = G b ψ := by
  subst e
  have : ψ' = ψ := by
    ext a
    rw [← hψ]
    simp
  rw [this]

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp)

theorem drAt_spMap_comp (la : AllWt.Weight S.Dw) (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (φ : K →+* ℂ_[p])
    (y : Sp K ⟶ (Φ.C k).Y.X) (f : (Φ.C k).Y.Fn) : drAt Φ k la p (spMap φ ≫ y) f = drVia Φ k la p y φ f := by
  have hb : below (spMap φ ≫ y) = below y := Res.below_comp y φ
  have hs : below (spMap φ ≫ y) ⤳ below y := hb ▸ specializes_rfl
  unfold drAt drVia
  congr 1
  · rw [Res.valAt_comp]
    exact congrArg (fun b => ‖φ (GlobalTheory.TrueGeo.valAt y (f * ((∏ z : Letter S.Dw,
      (((Φ.C k).gr_spec b).choose_spec.choose_spec.choose z.1 z.2) ^ expo S.Dw (drSym la) z : (Φ.C k).Y.Fnˣ) :
        (Φ.C k).Y.Fn)))‖) hb
  · exact eq_of_stalkSpecializes (fun b (ψ : (Φ.C k).Y.X.presheaf.stalk b →+* ℂ_[p]) =>
      Real.exp ((drSym la).sum fun a n => (n : ℝ) * lnStep s.T.Z.t
        (spMap ψ ≫ stalkPt (Φ.C k).Y b ≫ (Φ.C k).π ≫ genι s.T.Z)
        (fun τ i => spMap (dualMap ψ) ≫ ((Φ.C k).gr_spec b).choose_spec.choose.v τ i) p (a.1 p) a.2.2))
      hs hb _ _ fun a => GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes _ y φ hs a

example : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (la : AllWt.Weight S.Dw) (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (φ : K →+* ℂ_[p]) (y : Sp K ⟶ (Φ.C k).Y.X) (f : (Φ.C k).Y.Fn), drAt Φ k la p (spMap φ ≫ y) f = drVia Φ k la p y φ f :=
  fun _ _ _ _ _ _ _ Φ k la p _ K _ φ y f => drAt_spMap_comp Φ k la p K φ y f

end GlobalTheory.CovHt.Link
