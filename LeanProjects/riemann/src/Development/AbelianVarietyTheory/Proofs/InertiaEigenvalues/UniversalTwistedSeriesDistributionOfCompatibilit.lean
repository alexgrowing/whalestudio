import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumVectorDropAuxiliaryPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumHeckeIndicatorIntegralEqPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceChartFiniteAdeleTensorLevelsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumUniversalDeterminantDatumCoeffEqPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinMapSplitPlaceUniformiserEqFrobeniusInvStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModulusUnramifiedCharDetHeckeDoubleCosetSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumVectorDropAuxiliaryPlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvNatPowRpowNegHalfEvenEqPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDetRootOfDetAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlNeOfSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenPlacesAdmissibleGoodSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleConjugatePairPlacesEqSelfOfGoodCharsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalCharSpreadCommutesWithRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnivCharWithUnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.DistRel
open Classical
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem specU_grpSum (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) {j : ℕ} {b : Bool} (ch : Set (Pl D.host.E))
    (Q : Finset (Pl D.host.E)) (M k : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (x : (↥(half ch (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) → Y.Fm i j b) :
    Formalism.MainNotions.IntegralHeckeForms.specU Y i j b Q M k χ (grpSum Y ch Q M x) =
      ∑ c, ((χ (Multiplicative.ofAdd (spread Y i Q M ch c)) : (X.Ok i k)ˣ) : X.Ok i k) ⊗ₜ[X.O i] x c := by
  unfold grpSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [Formalism.MainNotions.IntegralHeckeForms.specU, AddMonoidAlgebra.lift_single]

theorem PqF_tmul (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host)
    (y o : X.Ok i k) (f : Y.Fm i j b) :
    GlobalTheory.TwSys.PqF Y i j b k P y (o ⊗ₜ[X.O i] f) = o ⊗ₜ[X.O i] f +
      ∑ n ∈ Finset.Icc 1 D.R.r, ((-1) ^ n * ((normV P : ℕ) : X.Ok i k) ^ (n * (n - 1) / 2) * y ^ n) •
        (o ⊗ₜ[X.O i] Y.hkF i j b n P f) := by
  simp only [GlobalTheory.TwSys.PqF, LinearMap.add_apply, Module.End.one_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.baseChange_tmul]
  rfl

end GlobalTheory.DistRel

namespace GlobalTheory.DistRel
open Classical
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem coord_eq_delOf {Y : NExp D.R D.host D.what₂ D.LL0 N X} (hU : GlobalTheory.UnivChar.IsUnivChar Y) (i : X.Tw) (M : ℕ)
    {Q : Finset (Pl D.host.E)} (hQc : ∀ P ∈ Q, ∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∈ Q) {v : Pl D.host.E} (hv : v ∈ Q)
    (τ : G D.host.E N.Om) :
    Multiplicative.toAdd (coord Y i Q M v τ) =
      Multiplicative.toAdd (GlobalTheory.GalChar.delOf D.host X.cc (X.l i) M (GlobalTheory.GalChar.pair D.host v) τ) := by
  rw [coord_apply Y i Q M hv τ, hU i Q M, GlobalTheory.GalChar.delU_apply, GlobalTheory.GalChar.delCoord_of_closed _ _ _ hQc M hv]

theorem coord_congr {Y : NExp D.R D.host D.what₂ D.LL0 N X} (hU : GlobalTheory.UnivChar.IsUnivChar Y) (i : X.Tw) (M : ℕ)
    {Q Q' : Finset (Pl D.host.E)} (hQc : ∀ P ∈ Q, ∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∈ Q)
    (hQc' : ∀ P ∈ Q', ∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∈ Q') {v : Pl D.host.E} (hv : v ∈ Q) (hv' : v ∈ Q') :
    coord Y i Q M v = coord Y i Q' M v := by
  ext τ
  exact congrArg Multiplicative.ofAdd ((coord_eq_delOf hU i M hQc hv τ).trans (coord_eq_delOf hU i M hQc' hv' τ).symm)

theorem isOpen_coord (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (Q : Finset (Pl D.host.E)) (M : ℕ) (v : Pl D.host.E) :
    IsOpen ((coord Y i Q M v).ker : Set (G D.host.E N.Om)) := by
  by_cases hv : v ∈ Q
  · refine Subgroup.isOpen_mono (H₁ := (Y.delU i Q M).ker) (fun g hg => ?_) (Y.delU_open i Q M)
    refine MonoidHom.mem_ker.2 (Multiplicative.toAdd.injective ?_)
    rw [coord_apply Y i Q M hv, MonoidHom.mem_ker.1 hg]
    rfl
  · have : coord Y i Q M v = 1 := by unfold coord; rw [dif_neg hv]
    rw [this, MonoidHom.ker_one]
    exact isOpen_univ

end GlobalTheory.DistRel

namespace GlobalTheory.DistRel
open Classical
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem isDC_of_rep {ρ : Setup X} (hρ : ρ.Good) {i : X.Tw} (j : Fin D.R.m) (b : Bool) {k : ℕ} {P : Pl D.host.E}
    (hk : Formalism.MainNotions.IntegralHeckeForms.HkIdx i k P) {e : AE D} (he : IsIdemAt e P) {α : GA D (Links.Wc D j)} {R : Finset (GA D (Links.Wc D j))}
    (hαs : SuppAt e (Links.Wc D j) α) (hR : ∀ γ ∈ R, SuppAt e (Links.Wc D j) γ)
    (hc : Mult.IsCosetRep (Links.Wc D j) (Mult.locPart (Links.Wc D j) (KsphC (Links.Wc D j) ∅) e) α R) :
    Bridge.IsDC (ρ.levK i j b) α R ∧ (1 : GA D (Links.Wc D j)) ∈ Mult.locPart (Links.Wc D j) (KsphC (Links.Wc D j) ∅) e := by
  have hoff : GlobalTheory.HeckeParts.OffLevel (V := Links.Wc D j) (Lev.flag1L (ρ.B i j b).G.levT) 1 P := by
    refine ⟨?_, ?_, ?_⟩
    · intro hP
      obtain ⟨x, hx, hy⟩ := hk.2.2.1
      refine hy (GlobalTheory.ChoiceAdm.cnj D x) rfl ?_
      rw [← hP]
      exact Ideal.subset_span ⟨x, hx, by
        change ((GlobalTheory.ChoiceAdm.cnj D x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E)
        rw [GlobalTheory.ChoiceAdm.cnj_coe, GlobalTheory.ChoiceAdm.star_eq_conj]⟩
    · rw [Nat.cast_one]
      exact fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    · rintro PP (hPP | hPP)
      · have hS : PP ∈ X.S0 i := by
          obtain ⟨k', hk'⟩ := hρ.Pg i j b PP hPP
          exact Finset.mem_coe.1 (X.placesOver_subset_exceptional i k' hk')
        exact ⟨fun e => hk.2.2.2 (e ▸ hS), fun hc => hk.2.2.2 (hρ.goodSetup_badPlaces_conj i PP hS P (GlobalTheory.ChoiceAdm.isConjPl_of_lev hc))⟩
      · exact absurd hPP (Finset.notMem_empty _)
  obtain ⟨Lp, hLp, -, hs, hK⟩ := GlobalTheory.HeckeParts.loc_package (hρ.latT i j b) hoff he
  exact ⟨GlobalTheory.HeckeParts.isDC_of_splits hs GlobalTheory.HeckeParts.levG_le_flag ((hLp α).2 hαs) (fun a ha => (hLp a).2 (hR a ha)) hK
    (fun γ hγ => (hc.1 γ hγ).2) hc.2, (hK 1).2 ⟨one_mem _, one_mem _⟩⟩

end GlobalTheory.DistRel

namespace GlobalTheory.DistRel
open Classical
open Formalism.IndefR.Links (PolF)
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem absNorm_eq_normV (P : Pl D.host.E) : Ideal.absNorm P.asIdeal = normV P := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem closed_erase {Q : Finset (Pl D.host.E)} (hQc : ∀ P ∈ Q, ∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∈ Q)
    {P Pb : Pl D.host.E} (hc : Formalism.BasicNotions.IsConjPl D.host P Pb) :
    ∀ v ∈ (Q.erase P).erase Pb, ∀ w, Formalism.BasicNotions.IsConjPl D.host v w → w ∈ (Q.erase P).erase Pb := by
  intro v hv w hw
  have hv1 := Finset.ne_of_mem_erase hv
  have hv2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hv)
  have hvQ := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv)
  refine Finset.mem_erase.2 ⟨fun e => ?_, Finset.mem_erase.2 ⟨fun e => ?_, hQc v hvQ w hw⟩⟩
  · subst e
    exact hv2 (GlobalTheory.GalChar.isConjPl_unique (GlobalTheory.GalChar.isConjPl_symm hw) (GlobalTheory.GalChar.isConjPl_symm hc))
  · subst e
    exact hv1 (GlobalTheory.GalChar.isConjPl_unique (GlobalTheory.GalChar.isConjPl_symm hw) hc)

end GlobalTheory.DistRel

namespace GlobalTheory.DistRel
open Classical
open Formalism.IndefR.Links (PolF)
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

set_option maxHeartbeats 4000000 in

theorem thURel_of_tie {ρ : Setup X} (hρ : ρ.Good) {Y : NExp D.R D.host D.what₂ D.LL0 N X} (rd : Rds Y ρ) (T : Comparison₂ hρ rd)
    (hU : GlobalTheory.UnivChar.IsUnivChar Y) (hH : ∀ i j b, HeckeRead (rd i j b))
    (hR : ∀ i, X.NonzeroIndexPlace i → ∀ j b, RatUniv (rd i j b)) :
    GlobalTheory.TwSys.ThURel Y := by
  intro i hi j hj b
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := (Finset.mem_Icc.1 hj).1; omega⟩
  have hj' : j' < D.R.m := by have := (Finset.mem_Icc.1 hj).2; omega
  set J : Fin D.R.m := ⟨j', hj'⟩ with hJ
  refine ⟨ρ.ch i, true, (hρ.ch i).pair, fun M k χ a => ?_, ?_⟩
  · rw [(T i J b).thU_empty M a]
    simp [Formalism.MainNotions.IntegralHeckeForms.specU]
    rfl
  intro M d Q a _ hQ hcls hlev hgood P Pb hP hPb hne hconj hch k χ χ' hχ σ hσ

  have hQ'Q : ((Q.erase P).erase Pb) ⊆ Q := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hsplit : ∀ v ∈ Q, IsSplitPl D.host v := hQ.1
  have hS0 : Disjoint Q (X.S0 i) := hQ.2.1
  have hclQ : ∀ v ∈ Q, ∀ w, Formalism.BasicNotions.IsConjPl D.host v w → w ∈ Q := hQ.2.2
  have hclQ' := closed_erase hclQ hconj
  have hlQ : ∀ v ∈ Q, v ∉ placesOver D.host.E (X.l i) := fun v hv hl =>
    Finset.disjoint_left.1 hS0 hv (X.twistExcludedPlaces_contains_residueChar i hl)
  have hA : admissibleConjugatePairPlaces X i Q M = Q := GlobalTheory.T.admissibleConjugatePairPlaces_eq_self_of_good_chars D N X i M Q d hsplit hclQ hgood (Or.inr hlQ)
  have hA' : admissibleConjugatePairPlaces X i ((Q.erase P).erase Pb) M = ((Q.erase P).erase Pb) := GlobalTheory.T.admissibleConjugatePairPlaces_eq_self_of_good_chars D N X i M ((Q.erase P).erase Pb) d (fun v hv => hsplit v (hQ'Q hv)) hclQ'
    (fun v hv => hgood v (hQ'Q hv)) (Or.inr fun v hv => hlQ v (hQ'Q hv))
  have hPQ' : P ∉ ((Q.erase P).erase Pb) := fun h => Finset.ne_of_mem_erase (Finset.mem_of_mem_erase h) rfl
  have hPbQ' : Pb ∉ ((Q.erase P).erase Pb) := fun h => Finset.ne_of_mem_erase h rfl
  have hPbch : Pb ∉ ρ.ch i := ((hρ.ch i).pair P Pb hconj hne).1 hch
  set H := half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M) with hHdef
  set H' := half (ρ.ch i) (admissibleConjugatePairPlaces X i ((Q.erase P).erase Pb) M) with hH'def
  have hsubH : ∀ w ∈ H', w ∈ H := fun w hw => by
    rw [hH'def, mem_half, hA'] at hw
    rw [hHdef, mem_half, hA]
    exact ⟨hQ'Q hw.1, hw.2⟩
  have hPH : P ∈ H := by rw [hHdef, mem_half, hA]; exact ⟨hP, hch⟩
  have hHH : ∀ v ∈ H, v ∈ H' ↔ v ≠ P := fun v hv => by
    rw [hHdef, mem_half, hA] at hv
    rw [hH'def, mem_half, hA']
    constructor
    · rintro ⟨h1, -⟩ rfl
      exact hPQ' h1
    · intro h
      refine ⟨Finset.mem_erase.2 ⟨fun e => hPbch (e ▸ hv.2), Finset.mem_erase.2 ⟨h, hv.1⟩⟩, hv.2⟩

  have hclA : ∀ v ∈ admissibleConjugatePairPlaces X i Q M, ∀ w, Formalism.BasicNotions.IsConjPl D.host v w → w ∈ admissibleConjugatePairPlaces X i Q M := by rw [hA]; exact hclQ
  have hclA' : ∀ v ∈ admissibleConjugatePairPlaces X i ((Q.erase P).erase Pb) M, ∀ w, Formalism.BasicNotions.IsConjPl D.host v w → w ∈ admissibleConjugatePairPlaces X i ((Q.erase P).erase Pb) M := by
    rw [hA']; exact hclQ'
  have hcoord : ∀ v ∈ H', coord Y i (admissibleConjugatePairPlaces X i Q M) M v = coord Y i (admissibleConjugatePairPlaces X i ((Q.erase P).erase Pb) M) M v := fun v hv =>
    coord_congr hU i M hclA hclA' (mem_half.1 (hsubH v hv)).1 (mem_half.1 hv).1
  have hdel : ∀ v ∈ H', (univOf Y i (admissibleConjugatePairPlaces X i ((Q.erase P).erase Pb) M) M ρ.rc).del v = (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).del v :=
    fun v hv => by simp only [univOf]; rw [hcoord v hv]
  have hkap : ∀ v ∈ H', (univOf Y i (admissibleConjugatePairPlaces X i ((Q.erase P).erase Pb) M) M ρ.rc).kap v = (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap v :=
    fun v hv => by simp only [univOf]; rw [hcoord v hv]

  have hsplitP := hsplit P hP
  obtain ⟨e0, he0⟩ := GlobalTheory.ChoiceAdm.exists_idem hsplitP
  have he : IsIdemAt (idemAt P) P := by rw [idemAt_eq he0]; exact he0
  obtain ⟨ϖ, hϖ1, hϖ2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := fun h0 => hϖ2 (by rw [show ϖ = 0 from Subtype.ext h0]; exact zero_mem _)
  have hee : idemAt P * idemAt P = idemAt P := he.1.1
  let x : (AE D)ˣ := Units.mkOfMulEqOne (idemAt P * incA D (ϖ : D.host.E) + (1 - idemAt P))
    (idemAt P * incA D (ϖ : D.host.E)⁻¹ + (1 - idemAt P)) (by
      have h1 : incA D (ϖ : D.host.E) * incA D (ϖ : D.host.E)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hϖ0, map_one]
      linear_combination (incA D (ϖ : D.host.E) * incA D (ϖ : D.host.E)⁻¹ - incA D (ϖ : D.host.E) -
        incA D (ϖ : D.host.E)⁻¹ + 1) * hee + idemAt P * h1)
  have hx : (x : AE D) = idemAt P * incA D (ϖ : D.host.E) + (1 - idemAt P) := rfl
  obtain ⟨α, R, -, hαR, -⟩ := GlobalTheory.Hk3.SplitMatch.exists_data he hϖ1 hϖ2 (Links.Wc D J)
  have hα : ∀ k ∈ Finset.Icc 1 (Links.Wc D J).rank, IsHeckeElt (Links.Wc D J) (idemAt P) (ϖ : D.host.E) k (α k) ∧
      (∀ γ ∈ R k, SuppAt (idemAt P) (Links.Wc D J) γ) ∧
      Mult.IsCosetRep (Links.Wc D J) (Mult.locPart (Links.Wc D J) (KsphC (Links.Wc D J) ∅) (idemAt P)) (α k) (R k) :=
    fun k hk => hαR k (Finset.mem_Icc.1 hk).2

  have hadm := GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint D N X ρ hρ i J b (admissibleConjugatePairPlaces X i Q M) (by rw [hA]; exact hsplit) (by rw [hA]; exact hS0)
  have hXi := xi_rel (ρ.B i J b) (hρ.base i J b) (hρ.latT i J b) (hρ.weil_base i J b)
    (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (univOf Y i (admissibleConjugatePairPlaces X i ((Q.erase P).erase Pb) M) M ρ.rc) (ρ.β J) hadm
    (GlobalTheory.UnivGood.univOf_good D N X ρ hρ Y i Q M) (GlobalTheory.UnivGood.univOf_good D N X ρ hρ Y i ((Q.erase P).erase Pb) M) hPH
    (fun w hw => hsubH w hw) hHH hdel hkap hϖ1 hϖ2 x hx α R hα

  have hIR : InRange X i Q := ⟨hsplit, hcls, hS0⟩
  have hIR' : InRange X i ((Q.erase P).erase Pb) := ⟨fun v hv => hsplit v (hQ'Q hv), fun v hv => hcls v (hQ'Q hv),
    Finset.disjoint_of_subset_left hQ'Q hS0⟩
  obtain ⟨x1, hx1, hT1⟩ := (T i J b).thU_of_rat (hR i hi J b) M hIR hlev
  obtain ⟨x2, hx2, hT2⟩ := (T i J b).thU_of_rat (hR i hi J b) M hIR' (Finset.disjoint_of_subset_left hQ'Q hlev)
  change Formalism.MainNotions.IntegralHeckeForms.specU Y i ((J : ℕ) + 1) b Q M k χ (Y.thU i ((J : ℕ) + 1) b Q M a) = GlobalTheory.TwSys.PqF Y i ((J : ℕ) + 1) b k P _
    (Formalism.MainNotions.IntegralHeckeForms.specU Y i ((J : ℕ) + 1) b ((Q.erase P).erase Pb) M k χ' (Y.thU i ((J : ℕ) + 1) b ((Q.erase P).erase Pb) M a))
  rw [hT1, hT2, specU_grpSum, specU_grpSum, map_sum]
  apply (T i J b).injective_rdK k
  funext g

  set E : (↥H → ZMod (X.l i ^ M)) → ℂ := fun c =>
    ρ.eOk i b k ((χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) c)) : (X.Ok i k)ˣ) : X.Ok i k) with hE
  set E' : (↥H' → ZMod (X.l i ^ M)) → ℂ := fun c =>
    ρ.eOk i b k ((χ' (Multiplicative.ofAdd (spread Y i ((Q.erase P).erase Pb) M (ρ.ch i) c)) : (X.Ok i k)ˣ) : X.Ok i k) with hE'
  set Ξ := ρ.xi i J b Y Q M ((T i J b).cls a) ((T i J b).coef a) with hΞ
  set Ξ' := ρ.xi i J b Y ((Q.erase P).erase Pb) M ((T i J b).cls a) ((T i J b).coef a) with hΞ'
  set yv : ℂ := ρ.eOk i b k ((χ' (Y.delU i ((Q.erase P).erase Pb) M σ) : (X.Ok i k)ˣ) : X.Ok i k) with hyv
  set q : ℂ := ((normV P : ℕ) : ℂ) with hq

  have hHk : ∀ n ∈ Finset.Icc 1 D.R.r, ∀ (f : Y.Fm i ((J : ℕ) + 1) b),
      rd i J b (Y.hkF i ((J : ℕ) + 1) b n P f) g = ((((ρ.B i J b).mu x : Circle) : ℂ) ^ n)⁻¹ *
        (q ^ (n * ((Links.Vc D J).rank / 2)))⁻¹ * ∑ γ ∈ R n, rd i J b f (g * γ) := by
    intro n hn f
    have hn' : n ∈ Finset.Icc 1 (Links.Wc D J).rank := by rw [FWT.rank_Wc]; exact hn
    have hk : Formalism.MainNotions.IntegralHeckeForms.HkIdx i n P :=
      ⟨(Finset.mem_Icc.1 hn).1, (Finset.mem_Icc.1 hn).2, hsplitP, fun h => Finset.disjoint_left.1 hS0 hP h⟩
    obtain ⟨hdc, h1⟩ := isDC_of_rep hρ J b hk he (hα n hn').1.2.1 (hα n hn').2.1 (hα n hn').2.2
    have hmu := (GlobalTheory.T.modulus_unramifiedChar_det_heckeDoubleCoset_split D (Links.Wc D J) P (idemAt P) he ϖ hϖ1 hϖ2 x hx n (α n) (hα n hn').1 1 h1 1 h1
      (GlobalTheory.VecInv.detAt (idemAt P) hee (Links.Wc D J) (α n)) (by
        rw [one_mul, mul_one]; exact GlobalTheory.VecInv.isDetAt_detAt _ hee _ _)).2 Circle ((ρ.B i J b).mu)
      (fun y h1 h2 h3 => mu_unram (ρ.B i J b) (hρ.base i J b) hadm hPH y h1 h2 h3)
    rw [hH i J b n P hk (α n) (R n) _ ⟨idemAt P, ϖ, he, hϖ1, hϖ2, (hα n hn').1⟩ hdc
      (GlobalTheory.VecInv.isDetAt_detAt _ hee _ _) f g, hmu]
    push_cast
    rfl

  set δ : ↥H' → ZMod (X.l i ^ M) :=
    Multiplicative.toAdd ((univOf Y i (admissibleConjugatePairPlaces X i ((Q.erase P).erase Pb) M) M ρ.rc).delQ H' x) with hδ
  have hδw : ∀ w : ↥H', δ w = -Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i ((Q.erase P).erase Pb) M) M w.1 σ) := by
    intro w
    have hwA : w.1 ∈ admissibleConjugatePairPlaces X i ((Q.erase P).erase Pb) M := (mem_half.1 w.2).1
    have hwQ' : w.1 ∈ (Q.erase P).erase Pb := by rw [← hA']; exact hwA
    have hPw : P ∉ GlobalTheory.GalChar.pair D.host w.1 := by
      rintro (h | h)
      · exact hPQ' (h ▸ hwQ')
      · exact hPbQ' (GlobalTheory.GalChar.isConjPl_unique hconj (GlobalTheory.GalChar.isConjPl_symm h) ▸ hwQ')
    have hunr : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 P), coord Y i (admissibleConjugatePairPlaces X i ((Q.erase P).erase Pb) M) M w.1 τ = 1 := by
      intro τ hτ
      refine Multiplicative.toAdd.injective ?_
      rw [coord_eq_delOf hU i M hclA' hwA τ,
        (GlobalTheory.GalChar.delOf_laws D.host X.cc (X.l i) M _).2.2.2 P hPw (N.plOm.1 P) (N.plOm.2 P) τ hτ]
    have hart := GlobalTheory.T.artinMap_splitPlaceUniformiser_eq_frobenius_inv D N.Om (Multiplicative (ZMod (X.l i ^ M))) ρ.rc hρ.rc
      (coord Y i (admissibleConjugatePairPlaces X i ((Q.erase P).erase Pb) M) M w.1) (isOpen_coord _ _ _ _ _) P (idemAt P) he ϖ hϖ1 hϖ2 x hx
      (N.plOm.1 P) (N.plOm.2 P) hunr σ hσ
    simp only [hδ, UnivTwist.delQ, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
    change Multiplicative.toAdd (ρ.rc.pull (coord Y i (admissibleConjugatePairPlaces X i ((Q.erase P).erase Pb) M) M w.1) x) = _
    rw [hart, toAdd_inv]
  have hTW : Formalism.MainNotions.NAdm.TWSet X i ((Q.erase P).erase Pb) := fun v hv => ⟨hsplit v (hQ'Q hv), hlQ v (hQ'Q hv)⟩
  have hspδ : spread Y i ((Q.erase P).erase Pb) M (ρ.ch i) δ =
      -Multiplicative.toAdd (Y.delU i ((Q.erase P).erase Pb) M σ) := by
    rw [delU_eq_spread hU hTW (hρ.ch i) σ, ← map_neg]
    congr 1
    funext w
    rw [hδw w]
    rfl
  have hE'shift : ∀ (n : ℕ) (c : ↥H' → ZMod (X.l i ^ M)), E' (c - n • δ) = E' c * yv ^ n := by
    intro n c
    simp only [hE', hyv, map_sub, map_nsmul, hspδ, smul_neg, sub_neg_eq_add, ofAdd_add, ofAdd_nsmul, ofAdd_toAdd, map_mul,
      map_pow, Units.val_mul, Units.val_pow_eq_pow_val]

  have eL : (rdK (rd i J b) hρ k (∑ c, ((χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) c)) : (X.Ok i k)ˣ) : X.Ok i k) ⊗ₜ[X.O i]
      x1 c)) g = ∑ c, E c * Ξ c g := by
    simp only [map_sum, rdK_tmul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hx1]
    rfl
  have eR : (rdK (rd i J b) hρ k (∑ c, GlobalTheory.TwSys.PqF Y i ((J : ℕ) + 1) b k P
      ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt true χ' (Y.delU i ((Q.erase P).erase Pb) M σ) : (X.Ok i k)ˣ) : X.Ok i k)
      (((χ' (Multiplicative.ofAdd (spread Y i ((Q.erase P).erase Pb) M (ρ.ch i) c)) : (X.Ok i k)ˣ) : X.Ok i k) ⊗ₜ[X.O i]
        x2 c))) g =
      ∑ c, (E' c * Ξ' c g + ∑ n ∈ Finset.Icc 1 D.R.r, ((-1) ^ n * q ^ (n * (n - 1) / 2) * yv ^ n) *
        (E' c * (((((ρ.B i J b).mu x : Circle) : ℂ) ^ n)⁻¹ * (q ^ (n * ((Links.Vc D J).rank / 2)))⁻¹ *
          ∑ γ ∈ R n, Ξ' c (g * γ)))) := by
    simp only [map_sum, PqF_tmul, map_add, map_smulₛₗ, rdK_tmul, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hx2]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hHk n hn, hx2]
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, if_true, hyv, hq, hE', hΞ']
  rw [eL, eR]

  have hfib : ∑ c, E c * Ξ c g = ∑ c' : ↥H' → ZMod (X.l i ^ M), E' c' * ∑ c ∈ Finset.univ.filter
      (fun c : ↥H → ZMod (X.l i ^ M) => ∀ v : ↥H', c ⟨v.1, hsubH v.1 v.2⟩ = c' v), Ξ c g := by
    rw [← Finset.sum_fiberwise (s := Finset.univ)
      (g := fun c : ↥H → ZMod (X.l i ^ M) => fun w : ↥H' => c ⟨w.1, hsubH w.1 w.2⟩) (f := fun c => E c * Ξ c g)]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Finset.mul_sum]
    have hfl : Finset.univ.filter (fun c : ↥H → ZMod (X.l i ^ M) => (fun w : ↥H' => c ⟨w.1, hsubH w.1 w.2⟩) = c') =
        Finset.univ.filter (fun c : ↥H → ZMod (X.l i ^ M) => ∀ v : ↥H', c ⟨v.1, hsubH v.1 v.2⟩ = c' v) :=
      Finset.filter_congr fun c _ => funext_iff
    rw [hfl]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc' : (fun w : ↥H' => c ⟨w.1, hsubH w.1 w.2⟩) = c' := funext (Finset.mem_filter.1 hc).2
    congr 1
    simp only [hE, hE']
    rw [hχ, ← hc']
    congr 4
    funext v
    exact GlobalTheory.T.universalChar_spread_commutes_with_restriction D N X Y hU i M (ρ.ch i) (hρ.ch i) Q ((Q.erase P).erase Pb) hQ'Q hA hA' hsubH c v.1 v.2
  have hIcc : Finset.Icc 1 (Links.Wc D J).rank = Finset.Icc 1 D.R.r := by rw [FWT.rank_Wc]
  have hX2 : ∀ c' : ↥H' → ZMod (X.l i ^ M), ∑ c ∈ Finset.univ.filter (fun c : ↥H → ZMod (X.l i ^ M) =>
      ∀ v : ↥H', c ⟨v.1, hsubH v.1 v.2⟩ = c' v), Ξ c g =
      Ξ' c' g + ∑ n ∈ Finset.Icc 1 D.R.r, ((-1 : ℂ) ^ n * q ^ (n * (n - 1) / 2) *
        ((((ρ.B i J b).mu x : Circle) : ℂ) ^ n * q ^ (n * ((Links.Vc D J).rank / 2)))⁻¹) *
        ∑ γ ∈ R n, Ξ' (c' + n • δ) (g * γ) := by
    intro c'
    have h := hXi ((T i J b).cls a) ((T i J b).coef a) c' g
    simp only [hIcc, absNorm_eq_normV] at h
    convert h using 3
  rw [hfib]
  simp only [hX2, mul_add, Finset.sum_add_distrib]
  congr 1
  have hL : ∀ c' : ↥H' → ZMod (X.l i ^ M), E' c' * ∑ n ∈ Finset.Icc 1 D.R.r, ((-1 : ℂ) ^ n * q ^ (n * (n - 1) / 2) *
      ((((ρ.B i J b).mu x : Circle) : ℂ) ^ n * q ^ (n * ((Links.Vc D J).rank / 2)))⁻¹) *
        ∑ γ ∈ R n, Ξ' (c' + n • δ) (g * γ) = ∑ n ∈ Finset.Icc 1 D.R.r, E' c' * (((-1 : ℂ) ^ n * q ^ (n * (n - 1) / 2) *
      ((((ρ.B i J b).mu x : Circle) : ℂ) ^ n * q ^ (n * ((Links.Vc D J).rank / 2)))⁻¹) *
        ∑ γ ∈ R n, Ξ' (c' + n • δ) (g * γ)) := fun c' => Finset.mul_sum _ _ _
  rw [Finset.sum_congr rfl fun c' _ => hL c', Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  conv_lhs => rw [← Equiv.sum_comp (Equiv.subRight (n • δ))]
  refine Finset.sum_congr rfl fun c' _ => ?_
  simp only [Equiv.subRight_apply, sub_add_cancel]
  rw [hE'shift, mul_inv]
  ring

end GlobalTheory.DistRel

namespace GlobalTheory.DistRel
open Classical

theorem thURel_of_exportTie {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : Links.RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
    {v₀ : (j : Fin D.R.m) → (σ : D.what₂.LL →+* ℂ) → (Rl.MW j σ).Vec} (Z : ExportTie YS v₀)
    (hRat : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatUniv (Z.rd i j b)) (hRH : ∀ i j b, RatHecke (Z.rd i j b)) : GlobalTheory.TwSys.ThURel D.nexp :=
  thURel_of_tie Z.good Z.rd Z.tie Z.univ (fun _ _ _ => Z.heckeRead (hRH _ _ _)) hRat

end GlobalTheory.DistRel

namespace GlobalTheory.DistRel
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf

theorem thURel_of_fullTie : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd → Laws hρ rd →
    ThURel D.nexp :=
  fun _ _ hρ rd F L => thURel_of_tie hρ rd F.tie F.univ L.hecke (fun i hi j b => (L.rat i hi j b).2.2)

end GlobalTheory.DistRel
