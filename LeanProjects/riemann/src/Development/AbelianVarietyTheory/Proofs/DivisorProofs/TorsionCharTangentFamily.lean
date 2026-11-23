import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTorsionCountStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocallyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitAbsoluteValueCriterionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFrameCoverTangentCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFramePrimeTangentCompatStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.HtGen.genOver_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (q : ℕ) [Fact q.Prime], CharFam t ρ' q 2 → ∀ (m : ℕ) (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left)) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d : Y.X → Fin m → Y.Fnˣ), IsFlagFrame t ρ u₀ f d → ∀ (k : ℕ) (hk : k ≤ m), GenOver V (fun y => ((∏ l : Fin k, d y (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn)) (fun v e y => -∑ l : Fin k, stepLog t ρ f q (Fin.castLE hk l) v e y) q := by
  intro E _ _ _ H X _ t hX F _ _ Y V ρ' ρ hρ q _ hC m u₀ f d hf k hk
  obtain ⟨N, c, hc, hh⟩ := hC
  have hch : ∀ x : V.X, ∃ (U : V.X.Opens) (hU : IsAffineOpen U) (g : ℕ)
      (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)) (h : Fin N → Fin g → Γ(V.X, U)),
      x ∈ U ∧ IsTanBasis t (hU.fromSpec ≫ ρ') e ∧
      ∀ (β : Γ(V.X, U) →+* ↥(intO ℂ_[q])) (y : Sp ↥(intO ℂ_[q]) ⟶ V.X), spMap β ≫ hU.fromSpec = y →
        ∀ j, DlogIs t q 2 (c j y) (fun i => spMap (dualMap β) ≫ e i) (fun i => β (h j i)) := by
    intro x
    obtain ⟨⟨U, hU⟩, g, e, hx, he⟩ := GlobalTheory.T.exists_affine_tangent_basis_locally E H X t V.X ρ' x
    obtain ⟨h, hh'⟩ := hh U hU g e he
    exact ⟨U, hU, g, e, h, hx, he, hh'⟩
  choose U hU g e h hx he hd using hch
  choose s hs using fun x => GlobalTheory.T.flag_frame_cover_tangent_compat E H X t F Y V ρ' ρ hρ m u₀ f d hf (U x) (hU x) (g x) (e x) (he x) (Fin N) (h x) k hk
  let eqv := Fintype.equivFin (Fin k → Fin N)
  refine ⟨Fintype.card (Fin k → Fin N), U, fun x J => s x (eqv.symm J), hx, fun x J z hz => ?_,
    fun v ε y z yt hq hzy hyt x hxU => ?_⟩
  · obtain ⟨α, a, -, -, hv⟩ := hs x z hz
    exact ⟨_, (hv _).symm⟩
  · obtain ⟨hp, -, -⟩ := ioOf_spec F v ε
    haveI := Fact.mk hp
    have P := fun x' (hx' : ⊤ ≤ yt ⁻¹ᵁ U x') => GlobalTheory.T.flag_frame_prime_tangent_compat E H X t hX F Y V ρ' ρ hρ q m f d hf.tan
      (fun y K _ ψ => hf.indep y K ψ) k hk N c hc (U x) (U x') (hU x) (hU x') (g x) (g x') (e x) (e x') (h x) (h x')
      (he x) (he x') (hd x) (hd x') (s x) (s x') (hs x) (hs x') v ε y z yt hq hzy hyt hxU hx'
    obtain ⟨hpos, hle, ⟨σ, heq⟩, -⟩ := P x hxU
    have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin k))) rfl fun l _ =>
      GlobalTheory.LineNorm.Chart.stepLog_eq ρ f q (Fin.castLE hk l) v ε y hp _ rfl
    have C := GlobalTheory.T.local_unit_absolute_value_criterion F v ε k _ hpos
    dsimp only
    rw [hsum]
    refine ⟨fun J => (C _).1.2 (hle _), ⟨eqv σ, ?_⟩, fun x' hx' J => (C _).2.2.2 ((P x' hx').2.2.2 _)⟩
    rw [Equiv.symm_apply_apply]
    exact (C _).2.1.2 heq
