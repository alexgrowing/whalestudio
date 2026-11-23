import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SummableEvTOfQMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationValuesIntOfAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesTorsionPairingSeparationIntegra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralGauge
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumDHomDegenerationValuesFieldExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfUniformisationOverDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesOfExpansionLawsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantTermRepresentativeDependenceStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TxCosetCriterionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueDescentAutomorphismInvariantMorphismStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisedIsoCommutesFieldAutomorphismOfTorsionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoPolarisedAbelianSchemesDvrOfFieldExtensStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPullbackDegenerationOfValuesIsoDvrStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeometricValuesIsoOfIdentificationDvrStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.IndefiniteRowSideFullHecke.ThetaTowerRecognition
noncomputable section
namespace GlobalTheory.SeriesCompare

section Base
variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {C : Type} [NormedField C] [Algebra (FractionRing V) C]

theorem admissible_base_of_complete_dvr (hV : GlobalTheory.LN.CDvr V) : AdmBase V (IsLocalRing.maximalIdeal V) := by
  obtain ⟨h₁, h₂, h₃⟩ := hV
  exact ⟨inferInstance, inferInstance, inferInstance, h₂⟩

theorem charZero_of (hV : GlobalTheory.LN.CDvr V) : CharZero C := by
  haveI := hV.2.2
  exact (RingHom.charZero_iff (ϕ := (algebraMap (FractionRing V) C).comp (algebraMap V _))
    ((algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V _))).1 inferInstance

theorem exists_one_lt_norm (hV : GlobalTheory.LN.CDvr V) (hC : CExt V (IsLocalRing.maximalIdeal V) C) : ∃ x : C, 1 < ‖x‖ := by
  haveI := hV.1
  obtain ⟨a, ha, h0⟩ := (Submodule.ne_bot_iff _).1 (IsDiscreteValuationRing.not_a_field V)
  refine ⟨(algebraMap (FractionRing V) C (algebraMap V _ a))⁻¹, ?_⟩
  rw [norm_inv]
  refine (one_lt_inv₀ (norm_pos_iff.2 ?_)).2 (hC.2 a ha)
  exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective V _)).2 h0)

theorem isUnit_iff_norm (hC : CExt V (IsLocalRing.maximalIdeal V) C) (n : ℕ) : IsUnit (n : V) ↔ ‖(n : C)‖ = 1 := by
  constructor
  · intro hu
    obtain ⟨m, hm⟩ := hu.exists_right_inv
    have a₁ := hC.1 n
    have a₂ := hC.1 m
    have a₃ := congrArg (fun x => ‖algebraMap (FractionRing V) C (algebraMap V _ x)‖) hm
    simp only [map_mul, map_natCast, map_one, norm_mul, norm_one] at a₁ a₃
    refine le_antisymm a₁ ?_
    calc (1 : ℝ) = _ := a₃.symm
      _ ≤ ‖(n : C)‖ * 1 := by gcongr
      _ = _ := _root_.mul_one _
  · intro h
    by_contra hu
    have := hC.2 n hu
    rw [map_natCast, map_natCast, h] at this
    exact lt_irrefl _ this
end Base

section Gauge
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [Field C] [Algebra (FractionRing R) C]

theorem qkExt_id {k : ℕ} (p : QkPt D C k) : QkExt (RingHom.id C) p p := by
  have e : spMap (RingHom.id C) = 𝟙 _ := Spec.map_id _
  refine ⟨rfl, by rw [e, Category.id_comp], fun χ => ?_⟩
  rw [e]
  exact corr_of_val D.P.isLB fun y J hJ =>
    ((val_pull hJ _ _ _).trans (congrArg (fun r => val (p.g.s χ) r y J) (Category.id_comp _))).symm

theorem qPt_unique' {N : NumD C} (ν : NumOf D C N) {k : ℕ} {p : QkPt D C k} {q q' : N.QT k} (h : ν.QPt p q)
    (h' : ν.QPt p q') : q = q' :=
  Subtype.ext (Prod.ext (Multiplicative.toAdd.injective (ν.eX.injective (h.1.trans h'.1.symm))) (ν.pt_unique h.2 h'.2))

variable (he : D.PsiEven) (hb : D.TauBimult) [IsAlgClosed C] {N : NumD C} (ν : NumOf D C N)
include he hb

theorem exists_val {k : ℕ} (p : QkPt D C k) : ∃ q, ν.QPt p q :=
  (((GtValues.points_correspond R D he hb C N ν).2.2.2.2 k).1 p).exists

theorem exists_pt {k : ℕ} (q : N.QT k) : ∃ p, ν.QPt p q :=
  ((GtValues.points_correspond R D he hb C N ν).2.2.2.2 k).2.1 q

theorem pt_unique {k : ℕ} {p p' : QkPt D C k} {q : N.QT k} (h : ν.QPt p q) (h' : ν.QPt p' q) : p = p' :=
  TorusExt.qk_ext (h.1.symm.trans h'.1) (((GtValues.points_correspond R D he hb C N ν).2.1 _).unique h.2 h'.2)

theorem exists_gaugeMap {M : NumD C} (ν₀ : NumOf D C M) (hth : ν₀.th = ν.th) :
    ∃ I : NumD.Hom (RingHom.id C) N M, I.lam = 1 ∧ (∀ k, Function.Bijective (qMap I k)) ∧
      ∀ k (p : QkPt D C k) q, ν.QPt p q ↔ ν₀.QPt p (qMap I k q) := by
  obtain ⟨I, hl, -, hI⟩ := GaugeHom.exists_hom R D C C (RingHom.id C) (RingHom.id_comp _) N M ν ν₀ hth
  have a : ∀ k (p : QkPt D C k) q q', ν.QPt p q → ν₀.QPt p q' → q' = qMap I k q := fun k p q q' h h' =>
    (qMap_iff I).1 (hI k p p q q' (qkExt_id p) h h')
  have b : ∀ k (p : QkPt D C k) q, ν.QPt p q → ν₀.QPt p (qMap I k q) := fun k p q h => by
    obtain ⟨q', h'⟩ := exists_val he hb ν₀ p
    exact a k p q q' h h' ▸ h'
  have c : ∀ k (p : QkPt D C k) q, ν₀.QPt p (qMap I k q) → ν.QPt p q := fun k p q h => by
    obtain ⟨p', h'⟩ := exists_pt he hb ν q
    exact pt_unique he hb ν₀ (b k p' q h') h ▸ h'
  refine ⟨I, hl, fun k => ⟨fun q q' h => ?_, fun q' => ?_⟩, fun k p q => ⟨b k p q, c k p q⟩⟩
  · obtain ⟨p, hp⟩ := exists_pt he hb ν q
    exact qPt_unique' ν hp (c k p q' (h ▸ b k p q hp))
  · obtain ⟨p, hp⟩ := exists_pt he hb ν₀ q'
    obtain ⟨q, hq⟩ := exists_val he hb ν p
    exact ⟨q, (a k p q q' hq hp).symm⟩
end Gauge

section Integral
variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.LN.CDvr V) (D : DegData V (IsLocalRing.maximalIdeal V))
  {C : Type} [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [Algebra (FractionRing V) C]
  (hC : CExt V (IsLocalRing.maximalIdeal V) C) {N : NumD C} (ν : NumOf D.toPre C N)
include hV hC

theorem exists_integral : ∃ (M : NumD C) (ν₀ : NumOf D.toPre C M) (q : QuadraticMap ℤ M.X ℝ)
    (I : NumD.Hom (RingHom.id C) N M), ν₀.IntN ∧ M.Int q ∧ I.lam = 1 ∧ (∀ k, Function.Bijective (qMap I k)) ∧
      ∀ k (p : QkPt D.toPre C k) q, ν.QPt p q ↔ ν₀.QPt p (qMap I k q) := by
  let S : ValuationSubring C := (NormedField.valuation (K := C)).valuationSubring
  have hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 := fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]; rfl
  obtain ⟨J, hJ, hJ'⟩ := IntegralGauge.exists_integral_gauge V D.toPre C S fun r => (hS _).2 (hC.1 r)
  obtain ⟨M, ν₀, rfl, hth⟩ := GaugeValues.exists_numOf firstFiveLaws.1 V D.toPre D.psi_even D.tau_bimult C J hJ ν.th ν.th_gen
  have hI : ν₀.IntN := ⟨S, hS, hJ'⟩
  obtain ⟨q, hq⟩ := IntVal.main V _ (admissible_base_of_complete_dvr hV) D C hC M ν₀ hI
  obtain ⟨I, h⟩ := exists_gaugeMap D.psi_even D.tau_bimult ν ν₀ hth
  exact ⟨M, ν₀, q, I, hI, hq, h⟩

include ν in

theorem summable_of_data [CompleteSpace C] {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) :
    Summable (N.txT m p) ∧ ∀ j, j ≠ 0 → ∀ r : N.QT j, Summable (N.evT m p r.1.2) := by
  obtain ⟨M, ν₀, q, I, -, hq, hl, -⟩ := exists_integral hV D hC ν
  exact ⟨⟨_, (hasSum_qMap I hl hm p _).1 (summable_txT hq hm.pos.ne' _).hasSum⟩,
    fun j hj r => summable_evT_of_qMap I hm p r (summable_evT hq hm.pos.ne' hj _ _)⟩
end Integral

theorem thetaSeries_iff : ThetaSeriesSt ↔ TXSt ∧ EVSt := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro V _ _ _ I hV rfl D A G _ _ - U C _ _ _ _ _ _ hC N ν m hm Ix p q x hx hq
      obtain ⟨v, hv, H⟩ := (h V hV D A G U C hC N ν m hm Ix p x hx).1
      have e : ∀ i, N.tx m (q i) = v i := fun i => ((hv i).hasSum (hq i)).2
      simpa only [e] using H
    · rintro V _ _ _ I hV rfl D A G _ _ - U C _ _ _ _ _ _ hC N ν m hm Ix p q x hx hq j hj p₀ q₀ z hz hq₀
      obtain ⟨v, hv, H⟩ := (h V hV D A G U C hC N ν m hm Ix p x hx).2 j (by omega) p₀ z hz
      have e : ∀ i, N.ev m (q i) q₀.1.2 = v i := fun i => by
        obtain ⟨q', g, h₁, h₂, h₃⟩ := hv i
        rw [qPt_unique ν (hq i) h₁, ν.pt_unique hq₀.2 h₂]
        exact h₃.tsum_eq
      simpa only [e] using H
  · rintro ⟨hT, hE⟩ V _ _ _ hV D A G _ _ U C _ _ _ _ _ hC N ν m hm Ix p x hx
    letI : NontriviallyNormedField C := ⟨exists_one_lt_norm hV hC⟩
    haveI : CharZero C := charZero_of hV
    haveI := hV.1
    haveI := hV.2.2
    have hG : IsSemiAbelian G := isSemiAbelian_of_unifPre_dvr V D A G U.toUnifPre
    choose q hq using fun i => exists_val D.psi_even D.tau_bimult ν (p i)
    refine ⟨⟨fun i => N.tx m (q i), fun i => ⟨q i, hq i, (summable_of_data hV D hC ν hm _).1.hasSum⟩,
      hT V _ hV rfl D A G hG U C hC N ν m hm Ix p q x hx hq⟩, fun j hj r z hz => ?_⟩
    obtain ⟨s, hs⟩ := exists_val D.psi_even D.tau_bimult ν r
    obtain ⟨r₄, hr₄⟩ := exists_pt D.psi_even D.tau_bimult ν (up (rfl : j * 4 = j * 4) s)
    have e₁ : r₄.y = 4 • r.y := by
      rw [← hr₄.1, ← hs.1, ← map_nsmul]; rfl
    have e₂ : r₄.g = r.g :=
      ((GtValues.points_correspond V _ D.psi_even D.tau_bimult C N ν).2.1 s.1.2).unique hr₄.2 hs.2
    have hz₄ := ((LevelCompat.qkToAkU_level firstFiveLaws V _ (admissible_base_of_complete_dvr hV) D A G hG U C j 4 (j * 4) hj (by norm_num) rfl
      r r₄ z).1 e₁ e₂).1 hz
    have Q := hE V _ hV rfl D A G hG U C hC N ν m hm Ix p q x hx hq (j * 4) (by omega) r₄ _ z hz₄ hr₄
    exact ⟨fun i => N.ev m (q i) s.1.2,
      fun i => ⟨q i, s.1.2, hq i, hs.2, ((summable_of_data hV D hC ν hm _).2 j hj.ne' s).hasSum⟩, Q⟩

section Conclusions
variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.LN.CDvr V) {D D' : DegPre V} (he : D.PsiEven)
  (hb : D.TauBimult) (he' : D'.PsiEven) (hb' : D'.TauBimult)
include hV he hb he' hb'

theorem exists_pullDeg {C : Type} [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C] {N N' : NumD C}
    (ν : NumOf D C N) (ν' : NumOf D' C N') (J : NumD.Iso N N') (hJ : GeoIso ν ν' J.toIso) {k : ℕ} (hk : 3 ≤ k)
    (hσ : ∀ (σ : C ≃ₐ[FractionRing V] C) (p pσ : QkPt D C k) (p' pσ' : QkPt D' C k) (q qσ : N.QT k) (qσ' : N'.QT k),
      QkExt (σ : C →+* C) p pσ → QkExt (σ : C →+* C) p' pσ' → ν.QPt p q → ν.QPt pσ qσ →
      ν'.QPt p' (qMap (TateInh.homOfIso J) k q) → ν'.QPt pσ' qσ' → N'.QEq (qMap (TateInh.homOfIso J) k qσ) qσ') :
    ∃ e : IsPullDeg (RingHom.id V) D D', ∀ (k : ℕ) (p : QkPt D C k) (p' : QkPt D' C k) (q : N.QT k),
      ν.QPt p q → ν'.QPt p' (qMap (TateInh.homOfIso J) k q) → Carries e p p' := by
  haveI := hV.1
  haveI := hV.2.2
  have hL := firstFiveLaws.1
  have hL2 := firstFiveLaws.2.1
  have hk0 : k ≠ 0 := by omega
  obtain ⟨φ, w, wv, g₁, g₂, g₃, g₄, g₅⟩ := hJ
  have pt : ∀ x, lift (𝟙 (TF (R := V) C)) (ν.eA x) ≫ φ.hom ≫ snd _ _ = ν'.eA (J.φ x) := fun x => by
    rw [← Category.assoc, g₃, lift_snd]
  have h1 : lift (𝟙 (TF (R := V) C)) (1 : TF (R := V) C ⟶ D.P.A) ≫ φ.hom ≫ snd _ _ = 1 := by
    have := pt 1
    rwa [map_one, map_one, map_one] at this
  have inv : ∀ (σ : C ≃ₐ[FractionRing V] C) (s : TF (R := V) C ⟶ TF (R := V) C), s.left = spMap (σ : C →+* C) →
      s ▷ D.P.A ≫ φ.hom ≫ snd _ _ = φ.hom ≫ snd _ _ := fun σ s hs => by
    have hf : (σ : C →+* C).comp (algebraMap (FractionRing V) C) = algebraMap (FractionRing V) C :=
      RingHom.ext σ.commutes
    haveI : IsIso s.left := by
      rw [hs]
      exact inferInstanceAs (IsIso (Spec.map σ.toRingEquiv.toCommRingCatIso.hom))
    haveI : IsIso ((Over.forget _).map s) := this
    haveI : IsIso s := isIso_of_reflects_iso s (Over.forget _)
    refine GlobalTheory.T.polarisedIso_commutes_fieldAutomorphism_of_torsion hL _ D.P D'.P C _ φ g₁ h1 ⟨w, g₂⟩ k hk (Nat.cast_ne_zero.2 hk0) (asIso s) fun x hx => ?_
    obtain ⟨b, rfl⟩ := ν.eA.surjective x
    obtain ⟨g, rfl, hg⟩ := QStr.root_over N hk0 1 b (ν.eA.injective (by rw [map_pow, hx]; exact (map_one _).symm))
    let q : N.QT k := ⟨(1, g), hg.trans N.io_zero.symm⟩
    obtain ⟨p, hp⟩ := exists_pt he hb ν q
    obtain ⟨p', hp'⟩ := exists_pt he' hb' ν' (qMap (TateInh.homOfIso J) k q)
    obtain ⟨pσ, hpσ⟩ := (TorusExt.existsUnique_qkExt hb _ hf p).exists
    obtain ⟨pσ', hpσ'⟩ := (TorusExt.existsUnique_qkExt hb' _ hf p').exists
    obtain ⟨qσ, hqσ⟩ := exists_val he hb ν pσ
    obtain ⟨qσ', hqσ'⟩ := exists_val he' hb' ν' pσ'
    obtain ⟨z, hz, hz'⟩ := hσ σ p pσ p' pσ' q qσ qσ' hpσ hpσ' hp hqσ hp' hqσ'
    have y₁ : qσ.1.1.toAdd = q.1.1.toAdd := ν.eX.injective (hqσ.1.trans (hpσ.1.trans hp.1.symm))
    have y₂ : qσ'.1.1.toAdd = J.e q.1.1.toAdd := ν'.eX.injective (hqσ'.1.trans (hpσ'.1.trans hp'.1.symm))
    have z0 : z = 0 := by
      have : J.e q.1.1.toAdd = J.e q.1.1.toAdd + k • z := y₂.symm.trans (hz.trans (congrArg (fun t => J.e t + k • z) y₁))
      rw [left_eq_add, ← natCast_zsmul] at this
      exact (smul_eq_zero.1 this).resolve_left (Int.natCast_ne_zero.2 hk0)
    rw [z0, NumD.io_zero, _root_.mul_one] at hz'
    have rb : ∀ r : N.QT k, (qMap (TateInh.homOfIso J) k r).1.2.b = J.φ r.1.2.b := fun r =>
      ((qMap_iff (TateInh.homOfIso J)).2 rfl).2.1
    have b₁ : s ≫ ν.eA g.b = ν.eA qσ.1.2.b :=
      Over.OverMorphism.ext (by rw [hqσ.2.1, hpσ.2.1, ← hp.2.1, Over.comp_left, hs])
    have b₂ : s ≫ ν'.eA (J.φ g.b) = ν'.eA qσ'.1.2.b :=
      Over.OverMorphism.ext (by rw [hqσ'.2.1, hpσ'.2.1, ← hp'.2.1, Over.comp_left, hs, rb])
    rw [asIso_hom, b₁, pt, pt, b₂, hz', rb]
  obtain ⟨g, hg, -⟩ := GlobalTheory.T.existsUnique_descent_automorphism_invariant_morphism (FractionRing V) C _ (jK V) D.P.A D'.P.A
    (haveI := D'.P.isAb.proper; inferInstance) (Over.homMk (jFK (R := V) C) rfl) rfl (φ.hom ≫ snd _ _) inv
  obtain ⟨Ψ, a₁, a₂, a₃⟩ := GlobalTheory.T.exists_iso_polarisedAbelianSchemes_dvr_of_fieldExtension hL hL2 V D.P D'.P C φ g₁ h1 ⟨w, g₂⟩ _ g hg
  obtain ⟨e, hc⟩ := GlobalTheory.T.exists_pullbackDegeneration_of_values_iso_dvr hL V D D' C N N' ν ν' J Ψ a₁ a₃ φ w g₁ a₂ g₂ g₃
    (fun x => (congrArg _ (g₄ 1).symm).trans ((g₅ x).trans (g₄ x)))
  exact ⟨e, fun k p p' q hq hq' => hc k p p' q _ hq hq' rfl ((qMap_iff (TateInh.homOfIso J)).2 rfl).2⟩

variable {C : Type} [NormedField C] [IsAlgClosed C] [Algebra (FractionRing V) C] {N N' : NumD C}
  (ν : NumOf D C N) (ν' : NumOf D' C N') {n : ℕ} {mt : Match N N' n} {w : TowerIso N N' n}

theorem inducedBy_of_onQ (hn : 2 ≤ n) (h : SameMatch mt w) {j : ℕ} (hj : 1 ≤ j) (hr : w.RationalAt ν ν' j)
    (H : ∃ J : NumD.Iso N N', mt.OnQ J ∧ GeoIso ν ν' J.toIso) :
    ∃ e : IsPullDeg (RingHom.id V) D D', w.InducedBy ν ν' e := by
  haveI : CharZero C := charZero_of hV
  obtain ⟨J, hQ, hJ⟩ := H
  have a : ∀ i (q : N.QT ((n ^ i) ^ 2)), N'.QEq (w.io i q) (qMap (TateInh.homOfIso J) _ q) := fun i q => by
    refine (h i _ _).1 ?_
    revert q
    rw [← pow_mul]
    exact fun q => hQ _ _ _ rfl ((qMap_iff (TateInh.homOfIso J)).2 rfl).2
  have E := N'.qEq_equivalence ((n ^ j) ^ 2)
  obtain ⟨e, he⟩ := exists_pullDeg hV he hb he' hb' ν ν' J hJ (k := (n ^ j) ^ 2)
    (by
      have : 2 ≤ n ^ j := hn.trans (Nat.le_self_pow (by omega) n)
      nlinarith)
    fun σ p pσ p' pσ' q qσ qσ' a₁ a₂ a₃ a₄ a₅ a₆ =>
      E.trans (E.symm (a j qσ)) (hr σ p pσ p' pσ' q qσ _ qσ' a₁ a₂ a₃ a₄ a₅ a₆ (a j q))
  refine ⟨e, fun i q => ?_⟩
  obtain ⟨p, hp⟩ := exists_pt ‹D.PsiEven› hb ν q
  obtain ⟨p', hp'⟩ := exists_pt he' hb' ν' (qMap (TateInh.homOfIso J) _ q)
  exact ⟨p, p', _, hp, hp', he _ p p' q hp hp', a i q⟩

omit he hb he' hb' [IsAlgClosed C] in

theorem onQ_of_inducedBy (hn : n ≠ 0) (h : SameMatch mt w)
    (H : ∃ e : IsPullDeg (RingHom.id V) D D', w.InducedBy ν ν' e) :
    ∃ J : NumD.Iso N N', mt.OnQ J ∧ GeoIso ν ν' J.toIso := by
  haveI := hV.1
  obtain ⟨e, he⟩ := H
  obtain ⟨J, hJ, hc⟩ := GlobalTheory.T.exists_geometric_values_iso_of_identification_dvr firstFiveLaws.1 V D D' e C N N' ν ν'
  refine ⟨J, fun j p p' h₁ h₂ => ?_, hJ⟩
  refine (r_incl mt (sq (n ^ j)) (pow_ne_zero _ hn) p p' (up (sq _) p) (up (sq _) p') rfl rfl rfl rfl).2 ((h j _ _).2 ?_)
  obtain ⟨r, r', q', a₁, a₂, a₃, a₄⟩ := he j (up (sq (n ^ j)) p)
  have b₁ := (qMap_iff (TateInh.homOfIso J)).1 (hc _ r r' _ q' a₁ a₂ a₃)
  have b₂ := (qMap_iff (TateInh.homOfIso J) (p := up (sq (n ^ j)) p) (p' := up (sq (n ^ j)) p')).1
    ⟨(congrArg (n ^ j • ·) h₁).trans (map_nsmul J.e _ _).symm, h₂⟩
  rw [b₂, ← b₁]
  exact a₄
end Conclusions

def RationalRel {V : Type} [CommRing V] [IsDomain V] {D D' : DegPre V} {C : Type} [NormedField C]
    [Algebra (FractionRing V) C] {N N' : NumD C} {n : ℕ} (mt : Match N N' n) (ν : NumOf D C N) (ν' : NumOf D' C N')
    (j : ℕ) : Prop :=
  ∀ (σ : C ≃ₐ[FractionRing V] C) (p pσ : QkPt D C ((n ^ j) ^ 2)) (p' pσ' : QkPt D' C ((n ^ j) ^ 2))
    (q qσ : N.QT ((n ^ j) ^ 2)) (q' qσ' : N'.QT ((n ^ j) ^ 2)),
    QkExt (σ : C →+* C) p pσ → QkExt (σ : C →+* C) p' pσ' → ν.QPt p q → ν.QPt pσ qσ → ν'.QPt p' q' → ν'.QPt pσ' qσ' →
    mt.r _ q q' → mt.r _ qσ qσ'

theorem SameMatch.rational_iff {V : Type} [CommRing V] [IsDomain V] {D D' : DegPre V} {C : Type} [NormedField C]
    [Algebra (FractionRing V) C] {N N' : NumD C} {n : ℕ} {mt : Match N N' n} {w : TowerIso N N' n} (h : SameMatch mt w)
    (ν : NumOf D C N) (ν' : NumOf D' C N') (j : ℕ) : RationalRel mt ν ν' j ↔ w.RationalAt ν ν' j := by
  simp only [RationalRel, TowerIso.RationalAt, h j]

def URecDvrSt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
    ∀ (D D' : DegData V (IsLocalRing.maximalIdeal V))
      (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C →
    ∀ (N N' : NumD C) (ν : NumOf D.toPre C N) (ν' : NumOf D'.toPre C N') (q : QuadraticMap ℤ N.X ℝ)
      (q' : QuadraticMap ℤ N'.X ℝ) (n : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 → N.Int q → N'.Int q' →
      N.Tors n D.toPre.P.g → N'.Tors n D'.toPre.P.g → ∀ mt : Match N N' n, (∃ j, 1 ≤ j ∧ RationalRel mt ν ν' j) →
      ∃ J : NumD.Iso N N', mt.OnQ J ∧ GeoIso ν ν' J.toIso

theorem uRecDvr_of_uRec (h : URecSt) : URecDvrSt :=
  fun V _ _ _ _ D D' C _ _ _ _ _ _ N N' ν ν' q q' n h₁ h₂ h₃ h₄ h₅ h₆ h₇ mt _ =>
    h V D.toPre D'.toPre D.psi_even D.tau_bimult D'.psi_even D'.tau_bimult C N N' ν ν' q q' n h₁ h₂ h₃ h₄ h₅ h₆ h₇ mt

theorem recognition_iff : RecognitionSt ↔ URecDvrSt := by
  constructor
  · rintro h V _ _ _ hV D D' C _ _ _ _ _ hC N N' ν ν' q q' n hn ho h1 hq hq' - - mt ⟨j, hj, hr⟩
    obtain ⟨w, hw⟩ := exists_tower hn.ne_zero mt
    exact onQ_of_inducedBy hV ν ν' hn.ne_zero hw (h V hV D D' n hn ho ((isUnit_iff_norm hC n).2 h1) C hC N N' ν ν' w mt.c₀
      (hw.proportional (fun j p => summable_txT hq (pow_ne_zero _ hn.ne_zero) p)
        fun j p => summable_txT hq' (pow_ne_zero _ hn.ne_zero) p) ⟨j, hj, (hw.rational_iff ν ν' j).1 hr⟩)
  · rintro h V _ _ _ hV D D' n hn ho hu C _ _ _ _ _ hC N N' ν ν' w c₀ hw ⟨j, hj, hr⟩
    letI : NontriviallyNormedField C := ⟨exists_one_lt_norm hV hC⟩
    haveI := hV.1
    have hL := firstFiveLaws.1
    have h1 := (isUnit_iff_norm hC n).1 hu
    have hnC : (n : C) ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact zero_ne_one h1
    have hO : CExt V ⊥ C := ⟨hC.1, fun r hr => hC.2 r (bot_le (a := IsLocalRing.maximalIdeal V) hr)⟩
    obtain ⟨M, ν₀, q, I, hI, hq, hl, hB, hP⟩ := exists_integral hV D hC ν
    obtain ⟨M', ν₀', q', I', hI', hq', hl', hB', hP'⟩ := exists_integral hV D' hC ν'
    have hT := ValuesTorsion.tors_of_integral hL firstFiveLaws.2.1 (GlobalTheory.T.abelianPartValues_of_expansionLaws hL) V _ D.psi_even D.tau_bimult C hO M ν₀
      hI n hn ho h1
    have hT' := ValuesTorsion.tors_of_integral hL firstFiveLaws.2.1 (GlobalTheory.T.abelianPartValues_of_expansionLaws hL) V _ D'.psi_even D'.tau_bimult C hO M'
      ν₀' hI' n hn ho h1
    obtain ⟨w₀, hw₀⟩ := exists_move I I' hB hB' w
    have hp₀ : w₀.Proportional c₀ := fun i p => by
      obtain ⟨p, rfl⟩ := (hB _).2 p
      obtain ⟨v, a, b⟩ := hw i p
      exact ⟨v, (hasSum_qMap I hl ho.pow p v).2 a, by rw [hw₀]; exact (hasSum_qMap I' hl' ho.pow _ _).2 b⟩
    have hc : ∀ i (p p' : M'.QT ((n ^ i) ^ 2)), M'.QEq p p' → M'.tx (n ^ i) p' = M'.tx (n ^ i) p := by
      rintro i p p' ⟨z, a, b⟩
      exact (tsum_congr fun χ => (GlobalTheory.T.thetaConstantTerm_representative_dependence C M' _ ho.pow p p' χ).1 z a b).trans
        ((Equiv.addRight (n ^ i • z)).tsum_eq fun χ => M'.txT (n ^ i) p χ)
    have h0 : c₀ ≠ 0 := by
      rintro rfl
      obtain ⟨t, -, -, ht⟩ := (GlobalTheory.T.tx_coset_norm_one_and_ne_zero C M' q' hq' n _ hn ho h1 hT' 1 le_rfl).2.2 1
      obtain ⟨p, hp⟩ := w₀.onto 1 (1 * t)
      obtain ⟨v, -, b⟩ := hp₀ 1 p
      exact ht ((hc 1 _ _ hp).trans (b.tsum_eq.trans (zero_mul v)))
    obtain ⟨mt, -, hm⟩ := exists_match (io_injective hq) (io_injective hq') hn.ne_zero
      (fun i => (QStr.qStructure C M n _ hnC hT i).2.1) hc w₀ h0 hp₀
    have hr₀ : w₀.RationalAt ν₀ ν₀' j := fun σ p pσ p' pσ' a aσ a' aσ' e₁ e₂ e₃ e₄ e₅ e₆ e₇ => by
      obtain ⟨a, rfl⟩ := (hB _).2 a
      obtain ⟨aσ, rfl⟩ := (hB _).2 aσ
      obtain ⟨a', rfl⟩ := (hB' _).2 a'
      obtain ⟨aσ', rfl⟩ := (hB' _).2 aσ'
      rw [hw₀, qEq_qMap I' (hB' _).1] at e₇ ⊢
      exact hr σ p pσ p' pσ' a aσ a' aσ' e₁ e₂ ((hP _ _ _).2 e₃) ((hP _ _ _).2 e₄) ((hP' _ _ _).2 e₅) ((hP' _ _ _).2 e₆) e₇
    obtain ⟨e, he⟩ := inducedBy_of_onQ hV D.psi_even D.tau_bimult D'.psi_even D'.tau_bimult ν₀ ν₀' hn.two_le hm hj hr₀
      (h V hV D D' C hC M M' ν₀ ν₀' q q' n hn ho h1 hq hq' hT hT' mt ⟨j, hj, (hm.rational_iff ν₀ ν₀' j).2 hr₀⟩)
    refine ⟨e, fun i a => ?_⟩
    obtain ⟨p, p', a', b₁, b₂, b₃, b₄⟩ := he i (qMap I _ a)
    obtain ⟨a', rfl⟩ := (hB' _).2 a'
    rw [hw₀, qEq_qMap I' (hB' _).1] at b₄
    exact ⟨p, p', a', (hP _ _ _).2 b₁, (hP' _ _ _).2 b₂, b₃, b₄⟩

theorem typings_compare :
    (ThetaSeriesSt ↔ TXSt ∧ EVSt) ∧ (RecognitionSt ↔ URecDvrSt) ∧ (URecSt → URecDvrSt) ∧
      (SeriesAndRecognition ↔ TXSt ∧ EVSt ∧ URecDvrSt) ∧ (TXSt ∧ EVSt ∧ URecSt → SeriesAndRecognition) :=
  ⟨thetaSeries_iff, recognition_iff, uRecDvr_of_uRec,
    (and_congr thetaSeries_iff recognition_iff).trans and_assoc,
    fun h => ⟨thetaSeries_iff.2 ⟨h.1, h.2.1⟩, recognition_iff.2 (uRecDvr_of_uRec h.2.2)⟩⟩

end GlobalTheory.SeriesCompare
end
