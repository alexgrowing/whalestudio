import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapAinfInvPrimeBdRPlusInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffGaloisTilt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfIsDomainAndAinfInvPInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffEqMkRootT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLawsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdRStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConcretePeriodDatumPadicFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusSimpleRootsSectionUniqueEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOfUnityPrimeToTeichmullerLiftStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLawsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddValuationNormalised
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsFieldStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section
namespace GlobalTheory.MemLoc.PrimeEx
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

section General
variable {G : Type} [Group G]

def actRing {B : Type} [CommRing B] (s : G → B →+* B) (hm : ∀ g h x, s (g * h) x = s g (s h x))
    (h1 : ∀ x, s 1 x = x) : G →* (B ≃+* B) where
  toFun g :=
    { toFun := s g
      invFun := s g⁻¹
      left_inv := fun x => by rw [← hm, inv_mul_cancel, h1]
      right_inv := fun x => by rw [← hm, mul_inv_cancel, h1]
      map_mul' := map_mul (s g)
      map_add' := map_add (s g) }
  map_one' := RingEquiv.ext h1
  map_mul' g h := RingEquiv.ext (hm g h)

def actAlg {F B : Type} [CommRing F] [CommRing B] [Algebra F B] (s : G → B →+* B)
    (hm : ∀ g h x, s (g * h) x = s g (s h x)) (h1 : ∀ x, s 1 x = x)
    (hc : ∀ g c, s g (algebraMap F B c) = algebraMap F B c) : G →* (B ≃ₐ[F] B) where
  toFun g := { actRing s hm h1 g with commutes' := hc g }
  map_one' := AlgEquiv.ext h1
  map_mul' g h := AlgEquiv.ext (hm g h)

end General

variable {l : ℕ} [Fact l.Prime]

theorem alg_tower (a : Per.Ainf l) : algebraMap (Per.Ainf l) (Per.Acris l) a =
    algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) := GlobalTheory.RingIface.tower l a

theorem dR_inj : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := (GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.1

theorem ev_zero (y : Per.BdRp l) : y ∈ Per.FilP l 0 := by
  obtain ⟨e, he⟩ := BdRField.exists_isEps l
  exact ((GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he).1 0 y).2 (by rw [pow_zero]; exact one_dvd y)

theorem iota_aB (C : Core l) (a : Per.Ainf l) :
    C.ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
  have h := C.ι_j (algebraMap (Per.Ainf l) (Per.Acris l) a)
  have h' : C.j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
    rw [alg_tower, C.j_cris.on0]; rfl
  rw [h', ← GlobalTheory.RingIface.aB_eq_alg] at h
  exact h

theorem aB_inj (C : Core l) : Function.Injective (Per.aB l) := by
  intro a b h
  have h1 := congrArg C.ι h
  rw [iota_aB, iota_aB] at h1
  exact (ainf_isDomain_and_injective l).2.2 (GlobalTheory.T.algebraMap_ainfInvPrime_bdRPlus_injective l (dR_inj h1))

theorem fil0 (C : Core l) (a : Per.Ainf l) : C.ι (Per.aB l a) ∈ Per.FilD l 0 := by
  rw [iota_aB]
  exact ((GlobalTheory.T.bdR_filtration_laws l).2.2.2.2.2.2 0 _).2 (ev_zero _)

theorem fil1 (C : Core l) (a : Per.Ainf l) :
    C.ι (Per.aB l a) ∈ Per.FilD l 1 ↔ ∃ b : Per.Ainf l, a = xi C.ε * b := by
  rw [iota_aB]
  refine ((GlobalTheory.T.bdR_filtration_laws l).2.2.2.2.2.2 1 _).trans ?_
  rw [← (thetaD_props l).2.1, (thetaD_props l).2.2.2.1]
  refine Iff.trans ?_ (theta_eq_zero_iff_xi_dvd l C.ε (core_isEps l C) a)
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

theorem teich (C : Core l) (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ) (hm : 0 < m) (hl : ¬ l ∣ m) (hc : (c : Om l) ^ m = 1)
    (xb : Per.Fl l) (h : IsTiltOf (c : Om l) m xb) : Per.aB l (Per.tm xb) = C.u c := by
  apply (GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.2.2.1
  rw [iota_aB, C.ι_u, ((GlobalTheory.T.rootOfUnity_prime_to_teichmuller_lift l C.o C.o_sec c m hm hl hc).2 xb h).2.2]

theorem sigD_o (C : Core l) (g : GQ l) (x : Om l) :
    Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) (C.o x)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (C.o (g x)) := by
  rw [(ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1, (GlobalTheory.T.bdRPlus_simple_roots_section_unique_equivariant l C.o C.o_sec).2.2]

theorem chi_cyc (C : Core l) (g : GQ l) (m : ℕ) (x : Om l) (hx : x ^ (l ^ m) = 1) :
    ∃ a : ℕ, ‖((C.χ g : ℤ_[l]) : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ∧ g x = x ^ a := by
  refine ⟨_, ?_, C.χ_cyc g m x hx⟩
  have h : ((C.χ g : ℤ_[l]) - ((PadicInt.toZModPow m (C.χ g : ℤ_[l])).val : ℤ_[l])) ∈
      Ideal.span {(l : ℤ_[l]) ^ m} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  have h2 := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 h
  rw [PadicInt.norm_def] at h2
  exact_mod_cast h2

theorem algB (C : Core l) (c : ℚ_[l]) :
    eB C (algebraMap ℚ_[l] (ringsOf C).B c) = C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) := rfl

theorem algU (C : Core l) (c : ↥(MaximalUnramifiedExtension l)) : eB C (algebraMap ↥(MaximalUnramifiedExtension l) (ringsOf C).B c) = C.u c := rfl

theorem algD (C : Core l) (c : ℚ_[l]) : eD C (algebraMap ℚ_[l] (ringsOf C).BdR c) =
    algebraMap (Per.BdRp l) (Per.BdR l) (C.o (algebraMap ℚ_[l] (Om l) c)) := rfl

theorem algO (C : Core l) (x : Om l) : eD C (algebraMap (Om l) (ringsOf C).BdR x) =
    algebraMap (Per.BdRp l) (Per.BdR l) (C.o x) := rfl

def conj {A A' B B' : Type} [CommRing A] [CommRing A'] [CommRing B] [CommRing B'] (e : A ≃+* A') (e' : B ≃+* B')
    (f : A' →+* B') : A →+* B := (e'.symm.toRingHom.comp f).comp e.toRingHom

theorem conj_apply {A A' B B' : Type} [CommRing A] [CommRing A'] [CommRing B] [CommRing B'] (e : A ≃+* A')
    (e' : B ≃+* B') (f : A' →+* B') (x : A) : e' (conj e e' f x) = f (e x) := e'.apply_symm_apply _

def actQ (C : Core l) : GQ l →* ((ringsOf C).B ≃ₐ[ℚ_[l]] (ringsOf C).B) :=
  actAlg (fun g => conj (eB C) (eB C) (Per.σB g))
    (fun g h x => (eB C).injective (by simp only [conj_apply]; exact (ActLaws.act_laws l).1 g h _))
    (fun x => (eB C).injective (by simp only [conj_apply]; exact (ActLaws.act_laws l).2.1 _))
    (fun g c => (eB C).injective (by
      rw [conj_apply, algB]
      exact (GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.1 g _ _ (g.commutes c)))

theorem actQ_apply (C : Core l) (g : GQ l) (b : (ringsOf C).B) : eB C (actQ C g b) = Per.σB g (eB C b) :=
  conj_apply _ _ _ _

def actQdR (C : Core l) : GQ l →* ((ringsOf C).BdR ≃ₐ[ℚ_[l]] (ringsOf C).BdR) :=
  actAlg (fun g => conj (eD C) (eD C) (Per.σD g))
    (fun g h x => (eD C).injective (by simp only [conj_apply]; exact (ActLaws.act_laws l).2.2.1 g h _))
    (fun x => (eD C).injective (by simp only [conj_apply]; exact (ActLaws.act_laws l).2.2.2.1 _))
    (fun g c => (eD C).injective (by rw [conj_apply, algD, sigD_o, g.commutes]))

theorem actQdR_apply (C : Core l) (g : GQ l) (b : (ringsOf C).BdR) :
    eD C (actQdR C g b) = Per.σD g (eD C b) :=
  conj_apply _ _ _ _

def phiB (C : Core l) : (ringsOf C).B →ₐ[ℚ_[l]] (ringsOf C).B :=
  { conj (eB C) (eB C) (Per.φB l) with
    commutes' := fun c => (eB C).injective (by
      refine (conj_apply _ _ _ _).trans ?_
      rw [algB, (GlobalTheory.T.localPeriodRingsData_unramified_laws l C).1, C.σ.commutes]) }

theorem phiB_apply (C : Core l) (b : (ringsOf C).B) : eB C (phiB C b) = Per.φB l (eB C b) :=
  conj_apply _ _ _ _

def iotaB (C : Core l) : (ringsOf C).B →ₐ[ℚ_[l]] (ringsOf C).BdR :=
  { conj (eB C) (eD C) C.ι with
    commutes' := fun c => (eD C).injective (by
      refine (conj_apply _ _ _ _).trans ?_
      rw [algB, algD, C.ι_u]
      rfl) }

theorem iotaB_apply (C : Core l) (b : (ringsOf C).B) : eD C (iotaB C b) = C.ι (eB C b) :=
  conj_apply _ _ _ _

def iA (C : Core l) : Per.Ainf l →+* (ringsOf C).B := (eB C).symm.toRingHom.comp (Per.aB l)

theorem iA_apply (C : Core l) (a : Per.Ainf l) : eB C (iA C a) = Per.aB l a := (eB C).apply_symm_apply _

theorem iA_inj (C : Core l) : Function.Injective (iA C) := fun a b h =>
  aB_inj C (by rw [← iA_apply C, h, iA_apply])

theorem iA_act (C : Core l) (g : GQ l) (a : Per.Ainf l) : iA C (Per.σA g a) = actQ C g (iA C a) :=
  (eB C).injective (by rw [actQ_apply, iA_apply, iA_apply, (ActLaws.act_laws l).2.2.2.2.2.1])

theorem iA_phi (C : Core l) (a : Per.Ainf l) : iA C (WittVector.frobenius a) = phiB C (iA C a) :=
  (eB C).injective (by rw [phiB_apply, iA_apply, iA_apply, (ActLaws.act_laws l).2.2.2.2.2.2.1, GlobalTheory.RingBasics.φA_apply])

theorem iota_iA (C : Core l) (a : Per.Ainf l) : eD C (iotaB C (iA C a)) = C.ι (Per.aB l a) := by
  rw [iotaB_apply, iA_apply]

attribute [local irreducible] actQ actQdR phiB iotaB iA

def pd (C : Core l) (K : FinExt l) :
    WeaklyAdmissibleFiltrations.PeriodData ↥(GK K) ℚ_[l] ↥(K0 K) ↥K.1 (ringsOf C).B (ringsOf C).BdR :=
  (GlobalTheory.T.exists_concretePeriodDatum_padicFiniteExtension l C K).choose

theorem pd_real (C : Core l) (K : FinExt l) : IsRealPD C K (pd C K) := (GlobalTheory.T.exists_concretePeriodDatum_padicFiniteExtension l C K).choose_spec

def prime (C : Core l) : LocPrime l where
  R := ringsOf C
  PD := pd C
  actQ := actQ C
  actQdR := actQdR C
  φB := phiB C
  ιB := iotaB C
  tB := (eB C).symm (algebraMap (Per.Acris l) (Per.Bcris l) C.t)
  χQ := (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp C.χ
  PD_p K := (pd_real C K).p
  PD_actB K g b := (eB C).injective (((pd_real C K).actB g b).trans (actQ_apply C _ b).symm)
  PD_actdR K g b := (eD C).injective (((pd_real C K).actdR g b).trans (actQdR_apply C _ b).symm)
  PD_φ K b := (eB C).injective (((pd_real C K).φ b).trans (phiB_apply C b).symm)
  PD_ι K b := (eD C).injective (((pd_real C K).ι b).trans (iotaB_apply C b).symm)
  period_datum_t_eq K := (eB C).injective ((pd_real C K).t.trans ((eB C).apply_symm_apply _).symm)
  PD_χ K g := (pd_real C K).χ g
  PD_Fil K K' a := Set.ext fun x => ((pd_real C K).fil a x).trans ((pd_real C K').fil a x).symm
  actQ_Kur g c c' h := (eB C).injective (by
    rw [actQ_apply, algU, algU]
    exact (GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.1 g c c' h)
  actQdR_Om g x := (eD C).injective (by rw [actQdR_apply, algO, algO, sigD_o])
  PD_σ K x hx := by
    rw [(pd_real C K).σ x ⟨x, x.2.2⟩ rfl]
    exact (frob_laws l C.σ C.σ_root).1 ⟨x, x.2.2⟩ hx
  χQ_cyc g m ζ h := chi_cyc C g m ζ h
  ζQ := C.ζ
  ζQ_zero := C.ζ_zero
  ζQ_succ := C.ζ_succ
  ζQ_one := C.ζ_one
  v LL := (exists_addValuation_normalised l LL).choose
  v_l LL := (exists_addValuation_normalised l LL).choose_spec.1
  v_O LL := (exists_addValuation_normalised l LL).choose_spec.2

def ainf (C : Core l) : LocAinf l (prime C) where
  actC := actRing Per.σC GlobalTheory.RingBasics.σC_mul GlobalTheory.RingBasics.σC_one
  actC_ext g x := GlobalTheory.RingBasics.σC_coe g x
  actC_norm g y := GlobalTheory.RingBasics.norm_σC g y
  actT := actRing (B := OCb l) Per.σF GlobalTheory.RingBasics.σF_mul GlobalTheory.RingBasics.σF_one
  actT_coeff g x n y h := coeff_galois_tilt l g x n y h
  ζ := rootT C.ε
  ζ_zero := Subtype.ext (by rw [C.ε_root, C.ζ_zero, map_one]; rfl)
  ζ_succ n := Subtype.ext (by
    have h := C.ε_root n
    rw [← C.ζ_succ, map_pow, ← C.ε_root] at h
    exact h.symm)
  ζ_one h := C.ζ_one ((algebraMap (Om l) ℂ_[l]).injective (by rw [← C.ε_root, h, map_one]; rfl))
  ε := C.ε
  ε_coeff n := eps_coeff l C n
  ιA := iA C
  ιA_inj := iA_inj C
  ιA_act g a := by
    have h : WittVector.map (actRing (B := OCb l) Per.σF GlobalTheory.RingBasics.σF_mul GlobalTheory.RingBasics.σF_one g).toRingHom a = Per.σA g a :=
      WittVector.ext fun n => (WittVector.map_coeff _ _ _).trans (GlobalTheory.RingIface.sigA_coeff l g a n).symm
    exact (congrArg (iA C) h).trans (iA_act C g a)
  ιA_φ a := iA_phi C a
  ζ_eq m := C.ε_root m
  ainf_image_mem_filtration_zero K a := ((pd_real C K).fil 0 _).2 ((iota_iA C a).symm ▸ fil0 C a)
  ainf_image_mem_filtration_one_iff K a := ((pd_real C K).fil 1 _).trans (by
    refine Iff.trans ?_ (fil1 C a)
    rw [← iota_iA]
    exact Iff.rfl)
  ιA_teich c m hm hl hc xb h := (eB C).injective
    ((iA_apply C _).trans ((teich C c m hm hl hc xb h).trans (algU C c).symm))

def tied (C : Core l) : LocTied l (prime C) (ainf C) where
  eB := eB C
  eD := eD C
  zB z := (algB C _).trans ((GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.2.1 z)
  zD z := (algD C _).trans ((congrArg _ (C.o_sec.z z)).trans (GlobalTheory.RingIface.zD_eq_alg l z).symm)
  om x := ⟨C.o x, algO C x, C.o_sec.th x⟩
  actB := actQ_apply C
  actD := actQdR_apply C
  frob := phiB_apply C
  incl := by
    have h : ((eD C).toRingHom.comp (iotaB C : (ringsOf C).B →+* (ringsOf C).BdR)).comp
        (eB C).symm.toRingHom = C.ι :=
      RingHom.ext fun b => (iotaB_apply C _).trans (congrArg C.ι ((eB C).apply_symm_apply b))
    exact h.symm ▸ (GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.2.2.2.2
  fil K a x := (pd_real C K).fil a x
  t := ⟨C.j C.t, (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l C.ε C.t (core_isEps l C).1 C.t_log).2.2.2 C.j C.j_cris,
    (iotaB_apply C _).trans ((congrArg C.ι ((eB C).apply_symm_apply _)).trans (C.ι_j C.t))⟩
  ιA a := iA_apply C a

end GlobalTheory.MemLoc.PrimeEx

namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem exists_locPrime_tied : ∀ (l : ℕ) [Fact l.Prime],
    ∃ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) := by
  intro l _
  obtain ⟨C⟩ := nonempty_core l
  exact ⟨PrimeEx.prime C, PrimeEx.ainf C, ⟨PrimeEx.tied C⟩⟩

end GlobalTheory.MemLoc
