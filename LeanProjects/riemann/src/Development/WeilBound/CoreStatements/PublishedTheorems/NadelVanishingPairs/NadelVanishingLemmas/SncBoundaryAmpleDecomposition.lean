import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegVanishingStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierDivisorMultCharacterize
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsPrimeDivisorsSncBoundaryStatement

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Div.SncBoundary

noncomputable def multHom {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (z : X) :
    CartierDiv X →+ ℤ :=
  AddMonoidHom.mk' (fun D => D.mult z) fun D E => CartierDiv.mult_add D E z

private theorem regAt_of_ord_eq_zero_of_normal {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X)
    {z : X} (hz : Order.coheight z = 1) {f : X.functionField} (hf : f ≠ 0)
    (h0 : Scheme.ord f z = 0) : RegAt z f := by
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  obtain ⟨hD, hI⟩ := hN z
  have hnf : ¬ IsField (X.presheaf.stalk z) := by
    intro hF
    have h1 := ringKrullDim_stalk_eq_coheight z
    rw [ringKrullDim_eq_zero_of_isField hF, hz] at h1
    norm_num at h1
  haveI : Ring.DimensionLEOne (X.presheaf.stalk z) :=
    ⟨fun hne hp => hp.isMaximal_of_ne_bot hne⟩
  have hDD : IsDedekindDomain (X.presheaf.stalk z) :=
    (isDedekindDomain_iff _ X.functionField).mpr
      ⟨hD, inferInstance, inferInstance, fun hx => (isIntegrallyClosed_iff X.functionField).mp hI hx⟩
  have hTF := IsDiscreteValuationRing.TFAE (X.presheaf.stalk z) hnf
  have hV : ValuationRing (X.presheaf.stalk z) := (hTF.out 2 1).mp hDD
  have hord : Ring.ordFrac (X.presheaf.stalk z) f = 1 := by
    have := (Scheme.ord_eq_iff hz hf).1 h0
    simpa [Scheme.ordHom] using this
  rcases ValuationRing.isInteger_or_isInteger (X.presheaf.stalk z) f with ⟨a, ha⟩ | ⟨r, hr⟩
  · exact ⟨a, ha⟩
  · have hr0 : r ≠ 0 := by
      rintro rfl
      simp only [map_zero] at hr
      exact hf (inv_eq_zero.mp hr.symm)
    have h2 : Ring.ordMonoidWithZeroHom (X.presheaf.stalk z) r = 1 := by
      rw [← Ring.ordFrac_eq_ord (K := X.functionField) _ hr0, hr, map_inv₀, hord, inv_one]
    have hmem : r ∈ nonZeroDivisors (X.presheaf.stalk z) := mem_nonZeroDivisors_of_ne_zero hr0
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hmem)
    rw [Ring.ordMonoidWithZeroHom_eq_coe _ hmem hn.symm] at h2
    have hn1 : Multiplicative.ofAdd (n : ℤ) = 1 := by exact_mod_cast h2
    have hn0 : n = 0 := by
      have : (n : ℤ) = 0 := by simpa using hn1
      exact_mod_cast this
    have h3 : Ring.ord (X.presheaf.stalk z) r = 0 := by rw [← hn, hn0]; rfl
    have hsub : Subsingleton (X.presheaf.stalk z ⧸ Ideal.span {r}) :=
      Module.length_eq_zero_iff.mp h3
    have hu : IsUnit r :=
      Ideal.span_singleton_eq_top.mp (Ideal.Quotient.subsingleton_iff.mp hsub)
    refine ⟨↑hu.unit⁻¹, ?_⟩
    have hm : algebraMap (X.presheaf.stalk z) X.functionField (↑hu.unit⁻¹ : X.presheaf.stalk z) *
        algebraMap (X.presheaf.stalk z) X.functionField r = 1 := by
      rw [← map_mul]
      simp
    rw [hr] at hm
    exact (mul_inv_eq_one₀ hf).1 hm

private theorem cartierDiv_eff_of_mult_eq_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (E : CartierDiv X)
    (h : ∀ z, E.mult z = 0) : E.Eff := by
  haveI : GlobalTheory.IsNormalScheme X := ⟨fun x => (hN x).1, fun x => (hN x).2⟩
  rw [CartierDiv.eff_iff]
  intro x g hg
  apply GlobalTheory.Discrepancy.regAt_of_forall_coheight_eq_one
  intro z hzx hz
  obtain ⟨U, hxU, hU⟩ := hg.exists_nhds
  have hgz : E.IsEqn z g := hU z (hzx.mem_open U.isOpen hxU)
  refine regAt_of_ord_eq_zero_of_normal hN hz g.ne_zero ?_
  rw [← hgz.mult_eq]
  exact h z

private theorem cartierDiv_eq_zero_of_mult_eq_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (E : CartierDiv X)
    (h : ∀ z, E.mult z = 0) : E = 0 := by
  refine CartierDiv.Eff.eq_zero (cartierDiv_eff_of_mult_eq_zero hN E h) (cartierDiv_eff_of_mult_eq_zero hN (-E) fun z => ?_)
  show multHom z (-E) = 0
  rw [map_neg]
  exact neg_eq_zero.mpr (h z)

private theorem cartierDiv_mult_nonneg_of_eff {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {D : CartierDiv X} (hD : D.Eff) (z : X) : 0 ≤ D.mult z := by
  obtain ⟨g, hg⟩ := D.exists_isEqn z
  rw [hg.mult_eq]
  by_cases hz : Order.coheight z = 1
  · obtain ⟨a, ha⟩ := CartierDiv.eff_iff.mp hD z g hg
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp only [map_zero] at ha
      exact g.ne_zero ha.symm
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
    rw [Scheme.le_ord_iff hz g.ne_zero, ← ha]
    have := Ring.ordFrac_ge_one_of_ne_zero (R := X.presheaf.stalk z) (K := X.functionField) ha0
    simpa [Scheme.ordHom] using this
  · simp [Scheme.ord_eq_zero_of_coheight_neq_one hz]

theorem vanishing_ample_snc_cartier : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q → ∀ (Kc : CanonLB q n) (Q A : LB Y) (hQ : Q.IsLB) (hA : IsAmpleLB A) (B : Closeds Y) (Γ : CartierDiv Y) (e : ℕ), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → Γ.Eff → Γ.supp ≤ B → (∀ z, Γ.mult z < e) → e • cls Q hQ = e • cls Kc.bundle Kc.isLB + toPic Γ + cls A hA.isLB → ∀ i, 0 < i → Subsingleton (coh (twist (GlobalTheory.structureModule Y) Q) i) := by
  intro k _ _ Y _ _ q n _ hp Kc Q A hQ hA B Γ e hB hΓ hsupp hmult heq i hi
  have hsm : Smooth q := SmoothOfRelativeDimension.smooth (n := n) (f := q)
  obtain ⟨-, hN, -⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k Y q hsm
  obtain ⟨r, w, D, σ, hw, hD, hBw, hrel⟩ := SncComp.relSnc_components k Y q n hp B hB
  have hnn : ∀ z, 0 ≤ Γ.mult z := cartierDiv_mult_nonneg_of_eff hΓ
  let b : Fin r → ℕ := fun j => (Γ.mult (w j)).toNat
  have hdec : Γ = ∑ j, b j • D j := by
    refine sub_eq_zero.mp (cartierDiv_eq_zero_of_mult_eq_zero hN _ fun z => ?_)
    show multHom z (Γ - ∑ j, b j • D j) = 0
    rw [map_sub, map_sum]
    simp only [map_nsmul]
    show Γ.mult z - ∑ j, b j • (D j).mult z = 0
    by_cases hz : ∃ j, z = w j
    · obtain ⟨j, rfl⟩ := hz
      rw [Finset.sum_eq_single j]
      · rw [(hD j).1]
        simp only [b, nsmul_eq_mul, mul_one]
        have := hnn (w j)
        omega
      · intro l _ hl
        rw [(hD l).2 (w j) (fun h => hl (hw h.symm)), smul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    · push_neg at hz
      rw [Finset.sum_eq_zero fun j _ => by rw [(hD j).2 z (hz j), smul_zero], sub_zero]
      by_contra hne
      obtain ⟨j, hj⟩ := hBw z (CartierDiv.coheight_eq_one_of_mult_ne_zero hne)
        (hsupp (CartierDiv.mem_supp_of_mult_ne_zero hne))
      exact hz j hj
  have he : 0 < e := by
    have h1 := hmult (genericPoint Y)
    have h2 := hnn (genericPoint Y)
    omega
  have hb : ∀ j, b j < e := by
    intro j
    have h1 := hmult (w j)
    have h2 := hnn (w j)
    simp only [b]
    omega
  rw [hdec, map_sum] at heq
  simp only [map_nsmul, toPic_apply] at heq
  exact GlobalTheory.Div.vanishing_ample_snc_charZero k Y q n hp r (fun j => toLB (D j)) σ hrel Kc Q A hQ hA
    e b he hb heq i hi

end GlobalTheory.Div.SncBoundary
