import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

theorem normPull_of_stalks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (j : 𝔐₀.Li →+ 𝔐.Li), CharZero Ω → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (a : Ω₀) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) → (∀ s a, j (Fl₀.b s a) = Fl.b s a) → (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐₀.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐₀.M.GramAt 𝔐₀.t.PP.L (z ≫ h) b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => j (b k)) Γ) → NormPull Fl₀ Fl i h := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl j hc hreg hsl hli hfl hst hgr
    z s a t₀ ν hN
  obtain ⟨hh, b, Γ, hfs, hfr, hb, hG, hP, rfl⟩ := hN
  have hq : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have hbase : Fl.b s = fun k => j (Fl₀.b s k) := funext fun k => (hfl s k).symm
  have hnf : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r ⟨centre z, hq⟩ := fun r hr => not_inFibre 𝔐.ξ z hq hr
  have hV := hst ⟨centre z, hq⟩ hnf s
  have hpush : (⟨centre (z ≫ h), hh⟩ : Cpt 𝔐₀.ξ) = pushCpt hd ⟨centre z, hq⟩ :=
    Subtype.ext (Scheme.Hom.comp_apply z h _)
  have hfr' : (𝔐₀.V s).IsFrameAt b (pushCpt hd ⟨centre z, hq⟩) := hpush ▸ hfr
  refine ⟨hq, fun k => j (b k), Γ, fun s' => ?_, ⟨hli _ b hfr.1, ?_⟩, ?_, hgr z _ b Γ hG, hP, rfl⟩
  · rw [hbase]
    exact FlagPull.flagStep_map_eq hsl hfs s'
  · rw [hV]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨e, he, rfl⟩
      have he' : e ∈ 𝔐₀.V s (pushCpt hd ⟨centre z, hq⟩) := he
      rw [hfr'.2] at he'
      clear he
      show j e ∈ Submodule.span (regAt 𝔐.ξ ⟨centre z, hq⟩) (Set.range fun k => j (b k))
      induction he' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul u x _ hx =>
        have e1 : j (u • x) = (⟨i u, hreg _ _ u.2⟩ : regAt 𝔐.ξ ⟨centre z, hq⟩) • j x := hsl (u : Ω₀) x
        rw [e1]
        exact Submodule.smul_mem _ _ hx
    · rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨b k, ?_, rfl⟩
      show b k ∈ 𝔐₀.V s (pushCpt hd ⟨centre z, hq⟩)
      rw [hfr'.2]
      exact Submodule.subset_span ⟨k, rfl⟩
  · have hm := FlagPull.map_mem_flagStep hsl (Fl₀.b s) a hb
    rw [map_sub, hsl, hfl, ← hbase] at hm
    exact hm

end GlobalTheory.CompanionTheory.Ar.Chg
