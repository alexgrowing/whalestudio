import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine

attribute [local instance] Over.cartesianMonoidalCategory

theorem ratioAt_pull : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → N2 Y → ∀ (Z Z' : Mdl Y i₀) (f : Z'.X ⟶ Z.X), IsMap Z' Z f → (∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) → ∀ st (x : Letter Dw), letterOf Dw st = some x → ∀ (U : Z.X.Opens) (m m' : ℕ) (A : Fin m → Γ(Z.X, U)) (B : Fin m' → Γ(Z.X, U)), RatioAt Z st U A B → ∀ (U' : Z'.X.Opens) (h : U' ≤ f ⁻¹ᵁ U), RatioAt Z' st U' (fun j => (f.appLE U U' h).hom (A j)) (fun j => (f.appLE U U' h).hom (B j)) := by
  intro hB E _ _ _ H Dw Xo p W Y i₀ hp _ hN Z Z' f hf hty st x hx U m m' A B hR U' h
  obtain ⟨τ, mu, hT⟩ := Pull.exists_trans hN hf.1.1 hf.1.2.1
  have rad : ∀ {n : ℕ} (C : Fin n → Γ(Z.X, U)), (p : Γ(Z.X, U)) ∈ (Ideal.span (Set.range C)).radical →
      (p : Γ(Z'.X, U')) ∈ (Ideal.span (Set.range fun j => (f.appLE U U' h).hom (C j))).radical := by
    intro n C hC
    have := Ideal.map_radical_le (f.appLE U U' h).hom (Ideal.mem_map_of_mem _ hC)
    rw [Ideal.map_span, ← Set.range_comp] at this
    rw [map_natCast] at this
    exact this
  refine ⟨rad A hR.1, rad B hR.2.1, fun y a' φ' h' hU => ?_⟩
  obtain ⟨a, φ, e⟩ := Pull.exists_chart hf hT (Pull.range_opn Z' h')
  obtain ⟨c, c0, hc⟩ := Pull.exists_coeff (x := x) hf hT hty h' e
  obtain ⟨P, hP⟩ := Pull.exists_pt hf hT y
  have hU₂ : ⊤ ≤ (y.z ≫ f) ⁻¹ᵁ U := fun q hq => h (hU hq)
  have N := hR.2.2 ⟨y.C, P, y.z ≫ f, hP⟩ a φ (e.trans (Category.assoc _ _ _)) hU₂
  have g₀ : Mdl.Pt.gen (Z := Z) ⟨y.C, P, y.z ≫ f, hP⟩ = y.gen ≫ f := (Category.assoc _ _ _).symm
  have g₁ : y.gen ≫ Z'.π = spMap (intO ↥y.C.S).subtype ≫ y.z ≫ Z'.π := Category.assoc _ _ _
  have g₂ : (y.gen ≫ f) ≫ Z.π = spMap (intO ↥y.C.S).subtype ≫ (y.z ≫ Z'.π) ≫ τ := by
    rw [Category.assoc, Pull.map_π hf hT, reassoc_of% g₁, Category.assoc]
  have F := Pull.chart_frame Z e
  have F' := Pull.push_frame hf hT h' e
  have T := Pull.push_tri hf hT hty h' e
  rw [g₀] at N
  rw [g₂] at N F F' T hc
  have step : ∀ b, lnStep (Y Z'.i).t (y.gen ≫ Z'.π) ((Z'.fr a').bc φ') p b st = Real.log ‖c x.2‖ +
      lnStep (Y Z.i).t (spMap (intO ↥y.C.S).subtype ≫ (y.z ≫ Z'.π) ≫ τ) ((Z.fr a).bc φ) p b st := fun b => by
    rw [g₁, Pull.lnStep_push mu b _ (Pull.ext_unique _ _) (fun σ j => g₁ ▸ ((Pull.chart_frame Z' h').1 σ j).1),
      Pull.lnStep_tri hB hp y.C b _ (Pull.ext_unique _ _) F F' T hx hc]
  have hgen : ⊤ ≤ y.gen ⁻¹ᵁ U' := fun q _ => hU (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))
  have vals : ∀ {n : ℕ} (C : Fin n → Γ(Z.X, U)), (fun j => valF y.gen U' ((f.appLE U U' h).hom (C j))) =
      fun j => valF (y.gen ≫ f) U (C j) := fun C => funext fun j => Pull.valF_appLE f U h hgen _
  rw [step, step, vals, vals]
  linarith

end GlobalTheory.HTLine
