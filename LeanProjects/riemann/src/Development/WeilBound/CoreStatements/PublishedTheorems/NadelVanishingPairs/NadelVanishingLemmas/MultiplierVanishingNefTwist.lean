import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.AmpleAddNefIsAmple
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsMultipleBelowThreshold
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CanonicalDivisorOfForm
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierDivisorMultCharacterize
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncBoundaryAmpleDecompositionStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.NefPullbackIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirationalStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.LogResVanish

open GlobalTheory.Cartier.CartierDiv in
private theorem mult_zero₀ {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y) :
    (0 : CartierDiv Y).mult z = 0 := by
  have h := CartierDiv.mult_add (0 : CartierDiv Y) 0 z
  rw [add_zero] at h
  linarith

private theorem mult_nsmul₀ {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (D : CartierDiv Y) (n : ℕ) (z : Y) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero => rw [zero_nsmul, mult_zero₀]; simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

private theorem mult_sub₀ {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (D E : CartierDiv Y) (z : Y) : (D - E).mult z = D.mult z - E.mult z := by
  have h := CartierDiv.mult_add (D - E) E z
  rw [sub_add_cancel] at h
  linarith

private theorem eff_nsmul {Y : Scheme.{0}} [IsIntegral Y] {D : CartierDiv Y} (h : D.Eff) (n : ℕ) :
    (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

private theorem supp_nsmul_le {Y : Scheme.{0}} [IsIntegral Y] (D : CartierDiv Y) (n : ℕ) :
    (n • D).supp ≤ D.supp := by
  induction n with
  | zero => rw [zero_nsmul, (CartierDiv.supp_eq_bot_iff).2 rfl]; exact bot_le
  | succ n ih => rw [succ_nsmul]; exact (CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)

private theorem compactSpace_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

end GlobalTheory.LogResVanish

open GlobalTheory.LogResVanish in

theorem GlobalTheory.Discrepancy.vanishing_logRes_floor : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → ∀ (a : ℕ) (Fd : CartierDiv Y) (A : LB Y) (hA : IsAmpleLB A), (0 < a ∧ Fd.Eff ∧ Fd.supp ≤ B ∧ a • CechPic.pull s (cls M hM) = cls A hA.isLB + toPic Fd) → ∀ (Q : LB Y) (hQ : Q.IsLB), cls Q hQ = CechPic.pull s (cls N hN) - toPic F → ∀ i, 0 < i → Subsingleton (coh (twist (GlobalTheory.structureModule Y) Q) i) := by
  intro k _ _ X _ p n hp η m G Y _ _ s _ K B F hη hm h hF N M T hN hM r hT hr hTc hMn a Fd A hA hAF Q hQ hQc i hi
  obtain ⟨ha, hFd, hFdB, hAc⟩ := hAF
  have hTlb : T.IsLB := by letI := algebraΓOfHom p; exact hT.isLB
  haveI := h.smooth
  haveI : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := GlobalTheory.isNormalScheme_of_smooth (s ≫ p)
  haveI : CompactSpace Y := compactSpace_of_projOver h.proj
  haveI : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'

  set Γ := pullCart s G - m • K with hΓ
  set R := Γ - m • F with hR
  have hRm : ∀ z, R.mult z = Γ.mult z % (m : ℤ) := fun z => by
    rw [hR, mult_sub₀, mult_nsmul₀, hF z, Int.emod_def]
  have hR0 : ∀ z, 0 ≤ R.mult z := fun z => (hRm z).symm ▸ Int.emod_nonneg _ hm0
  have hRlt : ∀ z, R.mult z < m := fun z =>
    (hRm z).symm ▸ Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  have hReff : R.Eff := ((GlobalTheory.T.cartier_divisor_mult_characterize Y R).1).2 hR0
  have hRB : R.supp ≤ B := fun x hx => by
    obtain ⟨z, hzx, hz⟩ := ((GlobalTheory.T.cartier_divisor_mult_characterize Y R).2.1 x).1 hx
    refine h.supp (((GlobalTheory.T.cartier_divisor_mult_characterize Y Γ).2.1 x).2 ⟨z, hzx, fun e => hz ?_⟩)
    rw [hRm, e, Int.zero_emod]

  obtain ⟨b, hab, hb⟩ := GlobalTheory.T.exists_multiple_below_threshold Y R Fd m r a hr hRlt
  set Γ' := (r * b) • R + m • Fd with hΓ'
  have hΓ'eff : Γ'.Eff := (eff_nsmul hReff _).add (eff_nsmul hFd _)
  have hΓ'B : Γ'.supp ≤ B := (CartierDiv.supp_add_le _ _).trans
    (sup_le ((supp_nsmul_le _ _).trans hRB) ((supp_nsmul_le _ _).trans hFdB))

  have hAm : IsAmpleLB (lbPow A m) := (isAmpleLB_pow_iff hA.isLB hm).2 hA
  letI := algebraΓOfHom (s ≫ p)
  have hTp : IsNef k (T.pull s) := GlobalTheory.T.nef_pullback_is_nef k X Y p s hp T hT
  have hMp : IsNef k (M.pull s) := GlobalTheory.T.nef_pullback_is_nef k X Y p s hp M hMn
  obtain ⟨P, hP, hPc⟩ := cls_surj (b • cls (T.pull s) hTp.isLB + (m * (b - a)) • cls (M.pull s) hMp.isLB)
  have hPn : IsNef k P := (hTp.pow hA b).of_cls_eq_add (hMp.pow hA (m * (b - a))) hA hP
    (by rw [hPc, cls_lbPow hTp.isLB, cls_lbPow hMp.isLB])
  obtain ⟨A', hA'lb, hA'c⟩ := cls_surj (cls (lbPow A m) hAm.isLB + cls P hPn.isLB)
  have hA' : IsAmpleLB A' := GlobalTheory.T.ample_add_nef_is_ample k Y (s ≫ p) h.proj (lbPow A m) P A' hAm hPn hA'lb hA'c

  let Kc := CanonLB.all (s ≫ p) n
  have hne : EtaleKlt.ratPull p s n η ≠ 0 := fun e =>
    hη ((GlobalTheory.T.rationalTopFormPullback_bijective_birational k X Y p s h.bir n).1 (e.trans (map_zero _).symm))
  have hK : toPic K = cls Kc.bundle Kc.isLB := (GlobalTheory.T.canonical_divisor_of_form k Y (s ≫ p) n _ hne).2 K h.div Kc
  refine GlobalTheory.T.snc_boundary_ample_decomposition k Y (s ≫ p) n h.proj Kc Q A' hQ hA' B Γ' (m * r * b) h.snc hΓ'eff hΓ'B hb ?_ i hi

  rw [hA'c, cls_lbPow hA.isLB, hPc, cls_pull hTlb, cls_pull hM, hTc, ← hK, hQc]
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  have e1 : toPic Γ' = (r * (a + c)) • (toPic (pullCart s G) - m • toPic K - m • toPic F) +
      m • toPic Fd := by
    rw [hΓ', hR, hΓ]; simp only [map_add, map_nsmul, map_sub]
  have e2 : m • toPic Fd = m • (a • CechPic.pull s (cls M hM) - cls A hA.isLB) := by
    rw [hAc, add_sub_cancel_left]
  rw [e1, add_assoc, e2, toPic_pullCart]
  simp only [map_sub, map_nsmul, Nat.add_sub_cancel_left]
  module
