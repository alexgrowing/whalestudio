import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

namespace GlobalTheory.CovTop.FromComp

theorem core (ι : Type) [Finite ι] [Nonempty ι] (T D A cs X cc z ρ R Bn δ' E C1 C2 mu : ℝ) (h sl δ dc degc : ι → ℝ)
    (hD : 0 ≤ D) (hT : 3 * D + 5 ≤ T) (hA : 0 < A) (hcs : 0 ≤ cs) (hX : 0 ≤ X) (hcc : 0 ≤ cc) (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hR : 0 ≤ R) (hBn : 0 < Bn) (hδ : 0 < δ') (hE : 1 ≤ E)
    (h1 : ∀ c, δ' ≤ δ c ∧ δ c ≤ δ' / (1 - ρ)) (h2 : ∀ c, Bn * δ c ≤ dc c ∧ (1 - z) * dc c ≤ Bn * δ c)
    (h3 : ∀ c, 0 ≤ h c + cs) (h4 : ∀ c, (1 - ρ) * max 0 (sl c + cs) ≤ h c + cs + cc)
    (h5 : -X ≤ (∑ᶠ c, sl c) / (Nat.card ι : ℝ))
    (h6 : ∀ c, Bn * δ c * (T * h c - 3 * (D + 1) * |h c| - A * Real.log (2 + |h c|) - R) ≤ degc c)
    (h7 : T * X ≤ C1 * E) (h8 : T * cc ≤ C1 * E) (h9 : cs * (6 * D + 10 + T * (z + 2 * ρ)) ≤ C1 * E)
    (h10 : A * Real.log (max A 1) + R ≤ C2 * E)
    (h11 : 2 * ((∑ᶠ c, degc c) / ∑ᶠ c, dc c) ≤ mu) : -((2 * (3 * C1 + C2 + 4)) * E) ≤ mu := by
  letI := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype] at h5
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype] at h11
  rw [Nat.card_eq_fintype_card] at h5
  have := Formalism.ExtensionFiltration.mean_height_sum_bound ι T D A cs X cc z ρ R 0 Bn δ' h sl δ dc degc 0 0 (4 * ((3 * C1 + C2 + 4) * E)) 0 0 0
    (C1 * E) (C1 * E) mu hD hT hA hcs hX hcc hz0 hz1 hρ0 hρ1 hR le_rfl hBn hδ h1 h2 h3 h4 h5
    (fun c => by simpa using h6 c) (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem atPoint (Y : Cov p i) (PP A C1 C2 : ℝ) (hi : (i : ℕ) + 1 < D.R.m) (hg : DeepGoodAt p i Y) (hs : SizeAt p i PP A)
    (hd : ∀ u1, Quo p i PP u1 → DegAt p i Y u1) (hsh : ∀ u1, Quo p i PP u1 → ShareAt p i Y PP u1)
    (hh : ∀ u1, Quo p i PP u1 → HeightAt p i Y PP C1 u1) (hhs : ∀ u1, Quo p i PP u1 → HSAt p i Y PP C2 u1)
    (hsum : SumAt p i Y) : UAt p i Y (2 * (3 * C1 + C2 + 4)) := by
  obtain ⟨-, -, -, -, -, hfin, hne, -⟩ := hg
  obtain ⟨hb1, hbE, -, -, -, -, hq⟩ := hs
  obtain ⟨⟨u1, hu⟩, hq⟩ := hq hi
  obtain ⟨hTD, hρ0, hρ1, hz1⟩ := hq u1 hu
  obtain ⟨δ', hδ, h1⟩ := hd u1 hu
  obtain ⟨cs, cc, X, sl, hcs, hcc, hX, h3, h4, h5, h7, h8, h9⟩ := hh u1 hu
  obtain ⟨B, R, hB, hR, h10, h6⟩ := hhs u1 hu
  have hz0 : 0 ≤ zed p i PP u1 := by
    unfold zed
    positivity
  have hBn : 0 < binT p i PP := by
    unfold binT
    exact_mod_cast Nat.choose_pos (by omega)
  exact core (Comp Y.d.Xo₂ Y.d.c₂) (lenT p i PP) (dimFlag (dat p i)) B cs X cc (zed p i PP u1) (rhoB (dat p i) u1) R
    (binT p i PP) δ' (unitE p) C1 C2 _ (fun Z => Y.ht u1 Z) sl (fun Z => Y.dg u1 Z) (fun Z => Y.rkC (uM p i) Z)
    (fun Z => Y.degC (uM p i) Z) (Nat.cast_nonneg _) (by exact_mod_cast hTD) hB hcs hX hcc hz0 hz1 hρ0 hρ1 hR hBn hδ
    (hb1.trans hbE) h1 (hsh u1 hu) h3 h4 h5 h6 h7 h8 h9 h10 hsum

theorem uLow_of (h1 : DeepGood) (h2 : Size) (h3 : Deg) (h4 : Share) (h5 : Height) (h6 : HS) (h7 : SumC) : ULow := by
  refine Closed.imp (Closed.and h1 (Closed.and h2 (Closed.and h3 (Closed.and h4 (Closed.and h5 (Closed.and h6 h7)))))) ?_
  rintro _ Fm _ _ ⟨⟨_, -, a1⟩, ⟨A, -, a2⟩, ⟨_, -, a3⟩, ⟨_, -, a4⟩, ⟨C1, hC1, a5⟩, ⟨C2, hC2, a6⟩, ⟨_, -, a7⟩⟩
  refine ⟨2 * (3 * C1 + C2 + 4), by positivity, ?_⟩
  obtain ⟨x0, h⟩ := a1.and (a2.and (a3.and (a4.and (a5.and (a6.and a7)))))
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h x hx hle ι p hp
  exact atPoint p i Y _ A C1 C2 hi (b1 i hi Y hY) (b2 i) (b3 i hi Y hY) (b4 i hi Y hY) (b5 i hi Y hY) (b6 i hi Y hY)
    (b7 i hi Y hY)

end GlobalTheory.CovTop.FromComp

end
