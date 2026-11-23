import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostFieldPadicEmbeddingMemMaxUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceOverPrimeOfPadicAlgClEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobGIsArithFrobAndSignStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.FrobPeriod

theorem norm_int_le_one {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖c (x : E)‖ ≤ 1 := by
  have hx : IsIntegral ℤ (c (x : E)) := map_isIntegral_int c x.isIntegral_coe
  have h : c (x : E) ∈ (NormedField.valuation (K := PadicAlgCl l)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).mem_of_integral
      hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem exists_comp_of_normal {E L : Type} [Field E] [Field L] [CharZero E] [CharZero L]
    [Normal ℚ E] (φ ψ : E →+* L) : ∃ g : E ≃ₐ[ℚ] E, ∀ x, ψ x = φ (g x) := by
  letI : Algebra E L := φ.toAlgebra
  haveI : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  refine ⟨AlgHom.restrictNormal' ψ.toRatAlgHom E, fun x => ?_⟩
  exact (AlgHom.restrictNormal_commutes ψ.toRatAlgHom E x).symm

theorem liesOver_of_mem {E : Type} [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime]
    (v : HeightOneSpectrum (𝓞 E)) (h : ((l : ℕ) : 𝓞 E) ∈ v.asIdeal) :
    v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := by
  constructor
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl.out).irreducible
  refine hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change (algebraMap ℤ (𝓞 E) (l : ℤ)) ∈ v.asIdeal
  simpa using h

theorem card_quot_under {E : Type} [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime]
    (Q : Ideal (𝓞 E)) [h : Q.LiesOver (Ideal.span {(l : ℤ)})] :
    Nat.card (ℤ ⧸ Q.under ℤ) = l := by
  rw [← h.over, Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]

end GlobalTheory.FrobPeriod

open GlobalTheory.FrobPeriod in

theorem GlobalTheory.FrobPeriod.periodFrob_restrict : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (c : D.host.E →+* ↥K.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → ∀ (x : D.host.E) (y : ↥(K0 K)), algebraMap ↥(K0 K) ↥K.1 y = c x → algebraMap ↥(K0 K) ↥K.1 ((P.PD K).σ y) = c (D.host.sigmaOf (DV.frobG D l) x) := by
  intro D l _ P K c h2 hq hd x y hy
  have hlN : ¬ l ∣ D.host.condN := fun h => by
    rcases (D.host.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  let c' : D.host.E →+* PadicAlgCl l := K.1.val.toRingHom.comp c
  have hK : ∀ z, c' z ∈ K0 K := fun z =>
    IntermediateField.mem_inf.2 ⟨(c z).2, GlobalTheory.T.hostField_padicEmbedding_mem_maxUnramified D.host l h2 hq hd c' z⟩
  let c0 : D.host.E →+* ↥(K0 K) := c'.codRestrict (K0 K) hK
  have hc0 : ∀ z, ((c0 z : ↥(K0 K)) : PadicAlgCl l) = c' z := fun z => rfl
  have hyx : y = c0 x := Subtype.ext (congrArg (fun t : ↥K.1 => (t : PadicAlgCl l)) hy)
  let σ0 := (P.PD K).σ
  obtain ⟨g, hg⟩ := exists_comp_of_normal c0 ((σ0 : ↥(K0 K) →+* ↥(K0 K)).comp c0)
  obtain ⟨v, hvl, hv⟩ := GlobalTheory.T.exists_place_over_prime_of_padicAlgCl_embedding l D.host.E c'
  haveI := liesOver_of_mem l v hvl
  have hgl : ∀ z : 𝓞 D.host.E, g • z - z ^ l ∈ v.asIdeal := fun z => by
    refine (hv _).2 ?_
    have h := P.PD_σ K (c0 z) (by rw [hc0]; exact norm_int_le_one c' z)
    have e : ((g • z - z ^ l : 𝓞 D.host.E) : D.host.E) = g (z : D.host.E) - (z : D.host.E) ^ l := by
      push_cast
      rfl
    rw [e, map_sub, map_pow, ← hc0, ← hc0, ← hg]
    exact h
  set F := D.host.sigmaOf (DV.frobG D l) with hFdef
  have hF : ∀ z : 𝓞 D.host.E, F • z - z ^ l ∈ v.asIdeal := fun z => by
    have h := (GlobalTheory.T.frobG_isArithFrobAt_and_sign_eq_jacobiSym D l h2 hq hd).1 v.asIdeal z
    rw [card_quot_under l v.asIdeal] at h
    exact h
  have hin := (D.host.der.frob l hlN v.asIdeal).2.2.2
  have hgF : g * F⁻¹ = 1 := by
    refine (hin _).1 fun z => ?_
    have h := v.asIdeal.sub_mem (hgl (F⁻¹ • z)) (hF (F⁻¹ • z))
    have e : (g * F⁻¹) • z - z = g • F⁻¹ • z - (F⁻¹ • z) ^ l - (F • F⁻¹ • z - (F⁻¹ • z) ^ l) := by
      rw [mul_smul, smul_inv_smul]
      ring
    rw [e]
    exact h
  have hgF' : g = F := by simpa using mul_inv_eq_one.1 hgF
  subst hyx
  apply Subtype.ext
  change (((σ0 (c0 x) : ↥(K0 K)) : PadicAlgCl l)) = c' (F x)
  have := hg x
  simp only [RingHom.comp_apply] at this
  rw [show (σ0 (c0 x)) = c0 (g x) from this, hc0, hgF']
