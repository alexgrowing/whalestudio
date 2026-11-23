import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.StConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWU4OfLimWU3
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicWeightDefiniteUnitaryAutRep

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Geo (GeoOne)

namespace UpperTheory.Gal.Int.Div

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem apart_cpl {w u : HeightOneSpectrum (𝓞 E)} (hu : IsSplitAt u) : Apart w (cpl u) ↔ Apart w u := by
  unfold Apart
  rw [(GlobalTheory.SplitPts.over_split hu).2.1]

private theorem apart_symm {w u : HeightOneSpectrum (𝓞 E)} (h : Apart w u) : Apart u w := Ne.symm h

private theorem mem_cpl (hC : CplMem) {l : ℕ} {u : HeightOneSpectrum (𝓞 E)} (h : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal) :
    ((l : ℕ) : 𝓞 E) ∈ (cpl u).asIdeal := (hC E u l l (by simp)).2 h

private theorem move (hC : CplMem) (hS : SameOr) {l d : ℕ} (hl : l.Prime) (hd : 0 < d) {x : E} (hx : x ^ 2 = -(d : E))
    {u w : HeightOneSpectrum (𝓞 E)} (hs : IsSplitAt u) (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal) (hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal)
    {p : HeightOneSpectrum (𝓞 E) → Prop} (h1 : p u) (h2 : p (cpl u)) :
    ∃ u', ((l : ℕ) : 𝓞 E) ∈ u'.asIdeal ∧ SameK x u' w ∧ p u' ∧ ∀ y, Apart y u' ↔ Apart y u := by
  rcases hS E l d hl hd x hx u w hu hw with h | h
  · exact ⟨u, hu, h, h1, fun _ => Iff.rfl⟩
  · exact ⟨cpl u, mem_cpl hC hu, h, h2, fun _ => apart_cpl hs⟩

end

theorem seedFinOdd_of (hD : DivAll) (hC : CplMem) (hS : SameOr) (hSat : SatConj) (hTy : TyConj) (hLac : LacConj) (hGap : GapLac)
    (hGen : DGenMul) (hG : GeoOne) : SeedFinOdd := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha hodd d hd T hT w₀ v' hw₀ hs₀ hv' hs' hap U₀ S Y
  refine ⟨∅, by simp, fun U hA hty hwt hsph hsv _ => ?_⟩
  obtain ⟨hd0, x, hx⟩ := hd.1
  have hlac : LacWtAt ι v' U := by
    obtain ⟨-, τ, hτ, h⟩ := hwt
    obtain ⟨lam, hlam⟩ := GlobalTheory.Cong.exists_weight_of_isAutRepU E a U hA.1
    exact ⟨τ, hτ, lam τ, hlam τ, hGap a _ (card_wtJumps _) (h _ (hlam τ) _ (wtJumps_val _))⟩
  have geo : ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∃ u₀ u', SameK x w u' ∧ (∀ y, Apart y u₀ ↔ Apart y w₀) ∧
      (∀ y, Apart y u' ↔ Apart y v') ∧ _ := fun w hw => by
    obtain ⟨u₀, a1, a2, a3, a4⟩ := move hC hS (Fact.out : l.Prime) hd0 hx hs₀ hw₀ hw
      (p := fun u => GlobalTheory.CongW.TyEll E l a u U) hty (hTy E l a U w₀ hs₀ hty)
    obtain ⟨u', b1, b2, b3, b4⟩ := move hC hS (Fact.out : l.Prime) hd0 hx hs' hv' hw
      (p := fun u => (∃ B, SatU U u B) ∧ LacWtAt ι u U) ⟨hsv, hlac⟩ ⟨hSat E a U hA.1 v' hs' hsv, hLac E l ι a ha U v' hlac⟩
    exact ⟨u₀, u', fun y hy => (b2 y hy).symm, a4, b4, hG E Ω l ι a hodd d hd x hx T hT u₀ u' a1 b1
      ((a4 u').2 (apart_symm ((b4 w₀).2 (apart_symm hap)))) (fun y hy => (a2 y hy).trans (b2 y hy).symm) S U hA a3
      (fun y h1 h2 h3 => hsph y h1 ((a4 y).1 h2) h3) b3.1 b3.2⟩
  obtain ⟨_, _, -, -, -, g1, g2, -⟩ := geo v' hv'
  obtain ⟨r, ⟨r1, r2, V, X, v1, v2, v3⟩, hr⟩ := hD E Ω l ι a ha d hd.1 U hA.1 g1
  have hgm : ∀ w B, SatU U w B → GlobalTheory.CongW.GenOf DGen a (normV w) B → GenericMul B := fun w B hB hg =>
    hGen a _ B ha hB.choose_spec.2.card hg
  have hsp : ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → IsSplitAt w := fun w hw => by
    by_contra h
    exact (hd.2.2.2 w h).1 hw
  refine ⟨r, r1, r2, ⟨V, X, v1, v2, fun w h1 h2 h3 _ => v3 w h1 h2 h3⟩, fun w _ h1 h2 _ B hB hg => ?_,
    fun w _ h1 h2 h3 h4 => ?_, fun w _ h1 h2 h3 _ B hB hg => ?_⟩
  · obtain ⟨dd, ρ, k1, k2⟩ := g2 w h1 h2 ⟨B, hB⟩
    exact (hr dd ρ k1 w).1 h1.1 h2 B hB (hgm w B hB hg) (k2 B hB)
  · obtain ⟨u₀, u', c1, c2, c3, -, -, g3⟩ := geo w h1
    obtain ⟨⟨dd, ρ, k1, k2, k3⟩, -⟩ := g3 w h1 c1 ((c2 w).2 h2) ((c3 w).2 h3) (hsph w (hsp w h1) h2 h4)
    exact (hr dd ρ k1 w).2.1 k2 k3
  · obtain ⟨u₀, u', c1, c2, c3, -, -, g3⟩ := geo w h1
    obtain ⟨-, dd, ρ, k1, k2⟩ := g3 w h1 c1 ((c2 w).2 h2) ((c3 w).2 h3) ⟨B, hB⟩
    exact ((hr dd ρ k1 w).2.2 (hsp w h1) B hB (hgm w B hB hg) (k2 B hB)).2.phiAt

end UpperTheory.Gal.Int.Div

end
