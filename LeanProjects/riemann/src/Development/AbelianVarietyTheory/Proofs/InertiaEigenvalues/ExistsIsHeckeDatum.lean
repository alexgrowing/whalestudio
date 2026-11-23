import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallExistsTransfer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeDatumExists

variable {D : D7}

theorem conj_ne_of_split {P : Pl D.host.E} (h : IsSplitPl D.host P) : Formalism.DivisionValues.conjPl P ≠ P := by
  intro hP
  obtain ⟨x, hx, hy⟩ := h
  refine hy (Formalism.DivisionValues.cO D.host.E x) ?_ ?_
  · show starRingAut (x : D.host.E) = D.host.conj (x : D.host.E)
    rw [starRingAut_apply]
    exact Formalism.BasicNotions.bridge_star_holds D.R D.host _
  · have : Formalism.DivisionValues.cO _ x ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hx
    rwa [hP] at this

theorem exists_isDC_levG (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {α : GA D V}
    (hα : α ∈ GfC V) : ∃ R : Finset (GA D V), Bridge.IsDC (Lev.levG V β L) α R := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hle : Lev.levG V β L ≤ GfC V := fun k hk => hk.1
  have hi := GlobalTheory.HeckeLabels.relIndex_conj_ne_zero (L := GfC V) (GlobalTheory.ParahoricCompact.isCompact_levG V β L)
    (GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L) (fun k hk hk' => ⟨hk, hk'⟩) hα
  rw [inf_eq_left.2 hle] at hi
  obtain ⟨R, r1, r2⟩ := GlobalTheory.HeckeLabels.exists_reps hi
  refine ⟨R, fun a ha => ?_, fun g ⟨k₁, k₂, hg⟩ => ?_⟩
  · obtain ⟨k₁, h₁, k₂, h₂, e⟩ := r1 a ha
    exact ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩, e⟩
  · exact r2 g ⟨k₁, k₁.2, k₂, k₂.2, hg⟩

theorem exists_isHeckeDatum : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X),
    ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool), ∀ (k : ℕ) (P : Pl D.host.E), Formalism.MainNotions.IntegralHeckeForms.HkIdx i k P →
      ∃ α R z, ρ.IsHeckeDatum i j b k P α R z := by
  intro D N X ρ _ i j b k P hk
  obtain ⟨-, hkr, hsp, -⟩ := hk
  obtain ⟨e, he⟩ := GlobalTheory.Hk3.SplitMatch.exists_isIdemAt (conj_ne_of_split hsp)
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  obtain ⟨α, R₀, R₀', hα, -⟩ := GlobalTheory.Hk3.SplitMatch.exists_data he h1 h2 (Wc D j)
  have hA := (hα k (hkr.trans (r_le_rank_Wc j))).1
  obtain ⟨R, hR⟩ := exists_isDC_levG (Wc D j) _ _ hA.1
  have hee : e * e = e := he.1.1
  set u : (AE D)ˣ := Matrix.GeneralLinearGroup.det (matHom (Wc D j) (α k)) with hu
  have huv : (u : AE D) * ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := Units.mul_inv u
  let z : (AE D)ˣ := Units.mkOfMulEqOne (e * u + (1 - e)) (e * ((u⁻¹ : (AE D)ˣ) : AE D) + (1 - e)) (by
    linear_combination ((u : AE D) * ((u⁻¹ : (AE D)ˣ) : AE D) - u - ((u⁻¹ : (AE D)ˣ) : AE D) + 1) * hee + e * huv)
  refine ⟨α k, R, z, ⟨e, ϖ, he, h1, h2, hA⟩, hR, ?_⟩
  show (z : AE D) = idemAt P * (mt (Wc D j) (α k)).det + (1 - idemAt P)
  rw [idemAt_eq he]
  rfl

end GlobalTheory.HeckeDatumExists
