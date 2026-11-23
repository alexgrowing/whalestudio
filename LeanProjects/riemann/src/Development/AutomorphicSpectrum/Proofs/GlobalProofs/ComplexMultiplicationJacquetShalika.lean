import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import GroundTheory.GlobalFields.ComplexMultiplication.HilbertClassField

open NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Published

section

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

theorem latticeCurve_eq_weierstrassCurve (L : PeriodPair) :
    GlobalTheory.latticeCurve L = weierstrassCurve L := by
  simp [GlobalTheory.latticeCurve, weierstrassCurve, neg_div]

theorem j_eq_of_eq {W W' : WeierstrassCurve ℂ} [W.IsElliptic] [W'.IsElliptic] (h : W = W') :
    W.j = W'.j := by
  subst h
  rfl

theorem latticeCurve_j (L : PeriodPair) : (GlobalTheory.latticeCurve L).j = (weierstrassCurve L).j :=
  j_eq_of_eq (latticeCurve_eq_weierstrassCurve L)

theorem under_ne_bot (M : IntermediateField K ℂ) [NumberField M] {P : Ideal (𝓞 M)} (hP : P ≠ ⊥) :
    P.under (𝓞 K) ≠ ⊥ :=
  fun h => hP (Ideal.eq_bot_of_comap_eq_bot h)

theorem isUnramifiedAbelian_hilbertClassField :
    GlobalTheory.Published.IsUnramifiedAbelian (hilbertClassField K ℂ) := by
  have : NumberField (hilbertClassField K ℂ) := NumberField.of_module_finite K _
  refine ⟨inferInstance, inferInstance, fun P hp hP => ?_⟩
  let v : HeightOneSpectrum (𝓞 K) := ⟨P.under (𝓞 K), inferInstance, under_ne_bot _ hP⟩
  exact (isUnramifiedEverywhere_hilbertClassField K ℂ).1 v P hp ⟨rfl⟩

theorem isUnramifiedEverywhere_of_isUnramifiedAbelian [IsTotallyComplex K]
    {M : IntermediateField K ℂ} [NumberField M] (h : GlobalTheory.Published.IsUnramifiedAbelian M) :
    IsUnramifiedEverywhere K M := by
  refine ⟨fun v P hp hv => ?_, fun v w hw => ?_⟩
  · exact h.2.2 P (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P)
  · exact InfinitePlace.isUnramified_iff.2 (Or.inr (hw ▸ IsTotallyComplex.isComplex v))

theorem isHilbertClassField_hilbertClassField [IsTotallyComplex K] :
    GlobalTheory.Published.IsHilbertClassField (hilbertClassField K ℂ) := by
  refine ⟨isUnramifiedAbelian_hilbertClassField, fun M hM => ?_⟩
  have := hM.1
  have := hM.2.1
  have : NumberField M := NumberField.of_module_finite K _
  exact (le_hilbertClassField_iff K ℂ M).2 (isUnramifiedEverywhere_of_isUnramifiedAbelian hM)

theorem isArtinMap_hilbertClassFieldArtinEquiv :
    GlobalTheory.Published.IsArtinMap (hilbertClassFieldArtinEquiv K ℂ).toMonoidHom := by
  intro 𝔭 𝔓 hP hO
  have : NumberField (hilbertClassField K ℂ) := NumberField.of_module_finite K _
  have hne : (𝔭 : Ideal (𝓞 K)) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.1 𝔭.2
  have hpp : (𝔭 : Ideal (𝓞 K)).IsPrime := by
    rw [hO.over]
    exact Ideal.IsPrime.under _ _
  let v : HeightOneSpectrum (𝓞 K) := ⟨𝔭, hpp, hne⟩
  let w : HeightOneSpectrum (𝓞 (hilbertClassField K ℂ)) :=
    ⟨𝔓, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hne 𝔓⟩
  have hwv : w.asIdeal.LiesOver v.asIdeal := hO
  have : Finite (𝓞 (hilbertClassField K ℂ) ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have e : hilbertClassFieldArtinEquiv K ℂ (ClassGroup.mk0 𝔭) = _ :=
    hilbertClassFieldArtinEquiv_mk0 K ℂ v w
  change IsArithFrobAt (𝓞 K) (hilbertClassFieldArtinEquiv K ℂ (ClassGroup.mk0 𝔭)) w.asIdeal
  rw [e]
  exact IsArithFrobAt.arithFrobAt _ _ _

theorem lattice_eq_idealLattice {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {L : PeriodPair}
    (h : GlobalTheory.Published.IsIdealLattice 𝔞 L) : L.lattice = idealLattice (algebraMap K ℂ) 𝔞.1 :=
  SetLike.coe_injective h

theorem latticeEnd_eq_cmRing [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {L : PeriodPair} (h : GlobalTheory.Published.IsIdealLattice 𝔞 L) :
    latticeEnd L = cmRing (algebraMap K ℂ) := by
  rw [← latticeEnd_ideal (algebraMap K ℂ) hK 𝔞]
  ext α
  show (∀ l ∈ L.lattice, α * l ∈ L.lattice) ↔
    ∀ l ∈ (idealPeriodPair (algebraMap K ℂ) hK 𝔞).lattice,
      α * l ∈ (idealPeriodPair (algebraMap K ℂ) hK 𝔞).lattice
  have e : (idealPeriodPair (algebraMap K ℂ) hK 𝔞).lattice = L.lattice := by
    rw [lattice_eq_idealLattice h]
    exact lattice_idealPeriodPair (algebraMap K ℂ) hK 𝔞
  rw [e]

end

theorem complexMultiplicationJ : GlobalTheory.Published.ComplexMultiplicationJSt := by
  intro K _ _ _ _ hK
  refine ⟨hilbertClassField K ℂ, hilbertClassFieldArtinEquiv K ℂ,
    isHilbertClassField_hilbertClassField, isArtinMap_hilbertClassFieldArtinEquiv, ?_, ?_⟩
  · intro 𝔞 L hL
    rw [latticeCurve_j]
    exact adjoin_j_curve_eq_hilbertClassField hK
      (CMCurve.ofLattice (algebraMap K ℂ) L (latticeEnd_eq_cmRing hK hL))
  · intro 𝔞 𝔟 L L' hL hL' x hx
    have hE := latticeEnd_eq_cmRing hK hL
    have hlat : L'.lattice = idealLattice (algebraMap K ℂ) ↑𝔟⁻¹ * L.lattice := by
      rw [lattice_eq_idealLattice hL', lattice_eq_idealLattice hL, Units.val_mul, idealLattice_mul]
    rw [latticeCurve_j] at hx ⊢
    have hx' : x = ⟨(weierstrassCurve L).j, j_weierstrassCurve_mem_hilbertClassField hK L hE⟩ :=
      Subtype.ext hx
    rw [hx']
    exact hilbertClassFieldArtinEquiv_apply_j_weierstrassCurve hK L L' hE 𝔟 hlat

end GlobalTheory.CompanionTheory.Published
