import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPointSpecializingOutsideBasicOpen
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.Cover.ThroughFibre

theorem exists_algPt_through : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (p : ℕ), p.Prime → ∀ (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ (U : V.X.Opens), ∀ x ∈ U, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), resP v = p ∧ below y.1 ∈ W ∧ z ≫ V.π = y.1 ∧ spMap e.O.subtype ≫ yt = z ≫ V.j ∧ ⊤ ≤ yt ⁻¹ᵁ U ∧ x ⤳ yt (IsLocalRing.closedPoint e.O) := by
  intro F _ _ Y V p hp W hW U x hxU hpx
  have := V.ar.flat
  have : IsProper V.p := by
    obtain ⟨n, c, hc, h⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance

  have hj : IsPreimmersion V.j :=
    MorphismProperty.of_isPullback V.pb.flip (IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F)) (S := F))
  obtain ⟨t, ht, htW⟩ := V.j.isEmbedding.isInducing.isOpen_iff.1 (V.π ⁻¹ᵁ W).isOpen
  obtain ⟨w, hw⟩ := V.π.surjective (genericPoint Y.X)
  have hwt : V.j w ∈ t := by
    have : w ∈ (V.π ⁻¹ᵁ W : Set V.G) := by
      change V.π w ∈ W
      rw [hw]; exact hW
    rw [← htW] at this
    exact this

  obtain ⟨U', hU, hxU', hU'U⟩ := exists_isAffineOpen_mem_and_subset hxU
  have hle : U' ≤ U := hU'U
  have : Nonempty U' := ⟨⟨x, hxU'⟩⟩
  have hηt : genericPoint V.X ∈ t :=
    ((genericPoint_spec V.X).mem_open_set_iff ht).2 ⟨_, trivial, hwt⟩
  have hηU : genericPoint V.X ∈ U' :=
    ((genericPoint_spec V.X).mem_open_set_iff U'.isOpen).2 ⟨x, trivial, hxU'⟩
  obtain ⟨g', hg't, hηg'⟩ := hU.exists_basicOpen_le (V := ⟨t, ht⟩ ⊓ U') ⟨genericPoint V.X, ⟨hηt, hηU⟩⟩ hηU
  have hg0 : g' ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hηg'
    exact hηg'
  have : CharZero Γ(V.X, U') := HorizPt.charZero (V.p ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(V.X, U') := (HorizPt.strHom V.p U').hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(V.X, U') :=
    RingHom.FiniteType.comp (V.p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  have hb : ∀ q : PrimeSpectrum Γ(V.X, U'), hU.fromSpec q ∈ V.X.basicOpen g' ↔ g' ∉ q.asIdeal := by
    intro q
    change q ∈ hU.fromSpec ⁻¹ᵁ V.X.basicOpen g' ↔ _
    rw [hU.fromSpec_preimage_basicOpen]
    rfl

  have hpP : (p : Γ(V.X, U')) ∈ (hU.primeIdealOf ⟨x, hxU'⟩).asIdeal := by
    letI : Algebra Γ(V.X, U') (V.X.presheaf.stalk x) := (V.X.presheaf.germ U' x hxU').hom.toAlgebra
    have := hU.isLocalization_stalk ⟨x, hxU'⟩
    by_contra hn
    apply hpx
    have h := (IsLocalization.AtPrime.isUnit_to_map_iff (V.X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU'⟩).asIdeal (p : Γ(V.X, U'))).2 hn
    rwa [map_natCast] at h
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨x, hxU'⟩).isPrime.ne_top
  obtain ⟨v, e, φ, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(V.X, U') 𝔪 h𝔪 g' hg0
  let yt : Sp e.O ⟶ V.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hwq : (spMap e.O.subtype ≫ yt) ≫ V.p =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [HorizPt.fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  set z := V.pb.lift _ _ hwq with hz
  have hzj : z ≫ V.j = spMap e.O.subtype ≫ yt := V.pb.lift_fst _ _ hwq
  have hzs : z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) := V.pb.lift_snd _ _ hwq
  let y : AlgPt Y := ⟨z ≫ V.π, by rw [Category.assoc]; exact hzs⟩

  have hpv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
    have hm : φ (p : Γ(V.X, U')) ∈ IsLocalRing.maximalIdeal e.O := by
      rw [← Ideal.mem_comap, h₂]; exact hle' hpP
    rw [map_natCast] at hm
    rw [← ExtConj.lies_over e]
    have h := (ValuationSubring.valuation_lt_one_iff e.O _).1 hm
    convert h using 2
    simp
  have hres : resP v = p := by
    have h0 : ((p : ℕ) : 𝓞 F ⧸ v.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hpv
    have hd := ringChar.dvd h0
    have : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
    rcases hp.eq_one_or_self_of_dvd _ hd with h | h
    · exact absurd h (CharP.ringChar_ne_one)
    · exact h
  refine ⟨v, e, y, z, yt, hres, ?_, rfl, hzj.symm, ?_, ?_⟩
  ·
    have hmem : (z ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ V.X.basicOpen g' := by
      rw [hzj]
      refine (hb (PrimeSpectrum.comap φ (PrimeSpectrum.comap e.O.subtype
        (IsLocalRing.closedPoint (AlgebraicClosure F))))).2 fun h => h₃ ?_
      have h' : ((φ g' : e.O) : AlgebraicClosure F) ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F) := h
      rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h'
      exact Subtype.ext h'
    have ht' : V.j (z (IsLocalRing.closedPoint (AlgebraicClosure F))) ∈ t := by
      exact (hg't hmem).1
    have hz' : z (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ (V.π ⁻¹ᵁ W : Set V.G) := by
      rw [← htW]; exact ht'
    exact hz'
  · intro q _
    exact hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)
  · have hx : hU.fromSpec (hU.primeIdealOf ⟨x, hxU'⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hxU'⟩
    have hsp : hU.primeIdealOf ⟨x, hxU'⟩ ⤳ PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O) := by
      rw [← PrimeSpectrum.le_iff_specializes]
      change (hU.primeIdealOf ⟨x, hxU'⟩).asIdeal ≤ (IsLocalRing.maximalIdeal e.O).comap φ
      rw [h₂]; exact hle'
    have := hsp.map hU.fromSpec.continuous
    rw [hx] at this
    exact this

end GlobalTheory.Mean4O.Cover.ThroughFibre
