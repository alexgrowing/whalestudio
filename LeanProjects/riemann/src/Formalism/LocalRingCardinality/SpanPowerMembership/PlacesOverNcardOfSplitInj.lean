import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.GaloisCohomology.GaloisCohomologyProofs.LdataNonempty
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

abbrev AlgC : Type := ↥(algebraicClosure ℚ ℂ)

instance : IsAlgClosed AlgC := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed

theorem mem_algC_of_isIntegral {x : ℂ} (hx : IsIntegral ℚ x) : x ∈ algebraicClosure ℚ ℂ :=
  mem_algebraicClosure_iff.2 hx.isAlgebraic

variable {R : Ranks} (H : Host R)

def embOm : H.E →+* AlgC :=
  H.φ₀.codRestrict (algebraicClosure ℚ ℂ).toSubfield (fun x =>
    mem_algC_of_isIntegral ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map
      ((H.φ₀.toRatAlgHom))))

instance algOm : Algebra H.E AlgC := (embOm H).toAlgebra

instance : IsScalarTower ℚ H.E AlgC := IsScalarTower.of_algebraMap_eq (fun x => by
  exact (RingHom.ext_rat (algebraMap ℚ AlgC) ((algebraMap H.E AlgC).comp (algebraMap ℚ H.E)) ▸ rfl))

instance isAlgClosure_om : IsAlgClosure H.E AlgC :=
  IsAlgClosure.mk inferInstance ⟨fun x =>
    (algebraicClosure.isAlgebraic ℚ ℂ |>.isAlgebraic x).tower_top H.E⟩

def toyLocalData (p : ℕ) [Fact p.Prime] : Formalism.GaloisCohomology.LData H.E AlgC p :=
  Classical.choice (Formalism.GaloisCohomology.ldata_nonempty p)

def shaExample (p e : ℕ) : ℚ :=
  if h : p.Prime then
    haveI : Fact p.Prime := ⟨h⟩
    ((Formalism.GaloisCohomology.shaLen (toyLocalData H p) (e : ℤ)).toNat : ℚ)
  else 0

theorem shaExample_nonneg (p e : ℕ) : 0 ≤ shaExample H p e := by
  unfold shaExample; split_ifs <;> positivity

def exampleClassGroupCard : ℕ := ∏ k : Fin 2, (Nat.card (GL (Fin R.r) (ZMod (H.g k)))) ^ R.f

theorem exists_genU (k : Fin 2) : ∃ ω : (ZMod (H.g k))ˣ, orderOf ω = H.g k - 1 := by
  have : Fact (H.g k).Prime := ⟨H.g_prime k⟩
  obtain ⟨ω, hω⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (H.g k))ˣ)
  exact ⟨ω, by rw [hω, Nat.card_eq_fintype_card, ZMod.card_units]⟩

def genU (k : Fin 2) : (ZMod (H.g k))ˣ := (exists_genU H k).choose

theorem orderOf_genU (k : Fin 2) : orderOf (genU H k) = H.g k - 1 := (exists_genU H k).choose_spec

structure NHyp (what₂ : Rows.Data R) : Prop where
  hsha : ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < R.t →
    what₂.shaLen p e = ((Formalism.GaloisCohomology.shaLen (toyLocalData H p) (e : ℤ)).toNat : ℚ)
  hcard : what₂.restRowsFiniteGroupCard = exampleClassGroupCard H
  hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E

set_option synthInstance.maxHeartbeats 400000 in

def ndToy (what₂ : Rows.Data R) (h : NHyp H what₂) : NData R H what₂ where
  Om := AlgC
  plOm := ⟨fun v => placeOf AlgC v, fun v => isPlaceOver_placeOf AlgC v⟩
  ldat p _ := toyLocalData H p
  sha_eq := fun p _ e h1 h2 n hn => by
    rw [h.hsha p e h1 h2, hn]
    simp
  Loc := Empty
  l i := i.elim
  lPrime i := i.elim
  j i := i.elim
  j_range i := i.elim
  mu i := i.elim
  w i := i.elim
  w_l i := i.elim
  mu_w i := i.elim
  w_tw i := i.elim
  locs _ _ := ∅
  locs_mem _ _ i := i.elim
  O i := i.elim
  instO i := i.elim
  domO i := i.elim
  dvrO i := i.elim
  algO i := i.elim
  finO i := i.elim
  topO i := i.elim
  trO i := i.elim
  O_adic i := i.elim
  O_complete i := i.elim
  embK i := i.elim
  embK_w i := i.elim
  X i := i.elim
  finX i := i.elim
  neX i := i.elim
  T i := i.elim
  T_local i := i.elim
  T_sep i := i.elim
  Mt i := i.elim
  acgMt i := i.elim
  modMt i := i.elim
  freeMt i := i.elim
  finMt i := i.elim
  act i := i.elim
  act_inj i := i.elim
  prMt i := i.elim
  prMt_span i := i.elim
  prMt_lat i := i.elim
  eig_ne i := i.elim
  chi i := i.elim
  chi_cont i := i.elim
  chi_def i := i.elim
  Z i := i.elim
  Zgood i := i.elim
  s0 i := i.elim
  restNLevelExponent_of_odd i := i.elim
  restNLevelExponent_of_two i := i.elim
  S i := i.elim
  Q i := i.elim
  SQ_disj i := i.elim
  SQ_l i := i.elim
  S_def i := i.elim
  hT i := i.elim
  T_gen i := i.elim
  gam0 i := i.elim
  locNd_chebotarevPlace_mem i := i.elim
  chi_ram_Q i := i.elim
  Bj i := i.elim
  acgBj i := i.elim
  modBj i := i.elim
  freeBj i := i.elim
  finBj i := i.elim
  g_split := h.hg
  PlG _ := Fin R.f
  card_PlG _ := Fintype.card_fin _
  lab _ _ _ := Polynomial.X ^ R.r
  lab_monic k _ _ := by
    have : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    exact ⟨Polynomial.monic_X_pow _, Polynomial.natDegree_X_pow _⟩
  chiT k _ j := genU H k ^ (2 * (j.1 + 1))
  restN_card_levelGroup_eq := h.hcard
  SQ_split i := i.elim
  restN_tameGenerator_generates i := i.elim

theorem ndToy_chiT (what₂ : Rows.Data R) (h : NHyp H what₂) (k v) (j : Fin R.m) :
    (ndToy H what₂ h).chiT k v j = genU H k ^ (2 * (j.1 + 1)) := rfl

theorem conj_mem_algC {x : ℂ} (hx : x ∈ algebraicClosure ℚ ℂ) :
    starRingEnd ℂ x ∈ algebraicClosure ℚ ℂ :=
  mem_algebraicClosure_iff.2
    (((mem_algebraicClosure_iff.1 hx).isIntegral.map (starRingEnd ℂ).toRatAlgHom).isAlgebraic)

def conjAlgC : AlgC ≃+* AlgC where
  toFun x := ⟨starRingEnd ℂ x, conj_mem_algC x.2⟩
  invFun x := ⟨starRingEnd ℂ x, conj_mem_algC x.2⟩
  left_inv _ := Subtype.ext (Complex.conj_conj _)
  right_inv _ := Subtype.ext (Complex.conj_conj _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem baseEmbedding_conj (x : H.E) : H.φ₀ (H.conj x) = starRingEnd ℂ (H.φ₀ x) :=
  H.conjE_apply H.φ₀ x

theorem isCMConjOm_conjAlgC : IsCMConjOm H.E AlgC conjAlgC := by
  refine ⟨⟨(algebraicClosure ℚ ℂ).val.toRingHom, fun x => rfl⟩, fun x => ⟨H.conj x, ?_⟩⟩
  apply Subtype.ext
  change starRingEnd ℂ (H.φ₀ x) = H.φ₀ (H.conj x)
  rw [baseEmbedding_conj]

set_option synthInstance.maxHeartbeats 400000 in

def ntwToy {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) (h : NHyp H what₂) :
    NTw R H what₂ LL0 (ndToy H what₂ h) where
  cc := conjAlgC
  cc_cm := isCMConjOm_conjAlgC H
  Tw := Empty
  O_l i := i.elim
  topO i := i.elim
  trO i := i.elim
  O_adic i := i.elim
  delta_open i := i.elim
  twistCharacterFamily_unramified i := i.elim
  twistCharacterFamily_at_auxiliaryPlaces i := i.elim
  twistCharacterFamily_tame i := i.elim
  hk_zero i := i.elim
  jL_range i := i.elim
  lamG i := i.elim
  lamG_cont i := i.elim
  lamG_unr i := i.elim
  lamG_pD i := i.elim
  lamG_anti i := i.elim
  Xv_def i := i.elim
  qs_conj i := i.elim
  twOf i := i.elim
  twSide i := i.elim
  twOf_l i := i.elim
  twist₂ i := i.elim
  twO_emb i := i.elim
  psiL i := i.elim
  psiL_ord i := i.elim
  psiL_open i := i.elim
  psiL_anti i := i.elim
  psiL_ram i := i.elim
  psiL_l i := i.elim
  chi_tw i := i.elim
  art_univ i := i.elim
  l i := i.elim
  lPrime i := i.elim
  O0 i := i.elim
  crO0 i := i.elim
  twistBaseCoefficientRing_isDomain i := i.elim
  twistBaseCoefficientRing_isDVR i := i.elim
  algO0 i := i.elim
  twistBaseCoefficientRing_finite_padic i := i.elim
  twistBaseCoefficientRing_residueField_finite i := i.elim
  topO0 i := i.elim
  twistBaseCoefficientRing_topologicalRing i := i.elim
  twistBaseCoefficientRing_isAdic i := i.elim
  emb0 i := i.elim
  emb0b i := i.elim
  restX_coefficientEmbedding_conj i := i.elim
  O i := i.elim
  crO i := i.elim
  domO i := i.elim
  dvrO i := i.elim
  algO i := i.elim
  O_inj i := i.elim
  resO_ac i := i.elim
  O_complete i := i.elim
  Ok i := i.elim
  crOk i := i.elim
  domOk i := i.elim
  dvrOk i := i.elim
  algOk i := i.elim
  Ok_inj i := i.elim
  Ok_fin i := i.elim
  zk i := i.elim
  zk_prim i := i.elim
  Ok_gen i := i.elim
  pD i := i.elim
  pD_eq i := i.elim
  delta i := i.elim
  delta_anti i := i.elim
  delta_ram i := i.elim
  delta_15 i := i.elim
  delta_tame i := i.elim
  chi1 i := i.elim
  twistCharacterFamily_continuous i := i.elim
  Sig i := i.elim
  finSig i := i.elim
  jS i := i.elim
  jS_range i := i.elim
  side i := i.elim
  rhoS i := i.elim
  rhoS_cont i := i.elim
  S0 i := i.elim
  twistExcludedPlaces_contains_residueChar i := i.elim
  placesOver_subset_exceptional i := i.elim
  primes_subset_exceptional i := i.elim
  B i := i.elim
  acgB i := i.elim
  modB i := i.elim
  freeB i := i.elim
  finB i := i.elim
  Theta i := i.elim
  ThetaPsi i := i.elim
  ThetaPsi_one i := i.elim
  hk i := i.elim
  hEig i := i.elim
  abelian₂ i := i.elim
  finLam i := i.elim
  jL i := i.elim
  sideL i := i.elim
  s2 i := i.elim
  Xv i := i.elim
  qs i := i.elim
  qs_sq i := i.elim
  RCG i := i.elim
  grpRCG i := i.elim
  finRCG i := i.elim
  RCG_l i := i.elim
  art i := i.elim
  art_surj i := i.elim
  art_cont i := i.elim
  art_anti i := i.elim
  art_unr i := i.elim
  res i := i.elim
  res_art i := i.elim
  th i := i.elim

open Classical in

def chv (χ : Multiset ℂ) : ℂ := if h : ∃ c, χ = {c} then h.choose else 1

open Classical in
theorem chv_singleton (c : ℂ) : chv {c} = c := by
  have h : ∃ c', ({c} : Multiset ℂ) = {c'} := ⟨c, rfl⟩
  unfold chv
  rw [dif_pos h]
  exact (Multiset.singleton_inj.1 h.choose_spec).symm

theorem placesOver_g_nonempty (h : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (k : Fin 2) : (placesOver H.E (H.g k)).Nonempty :=
  Set.nonempty_of_ncard_ne_zero (by rw [h k]; exact Module.finrank_pos.ne')

open Ideal in
open scoped Pointwise in

theorem exists_halfPlaces (p : ℕ) (hp : p.Prime)
    (h : (placesOver H.E p).ncard = Module.finrank ℚ H.E) :
    ∃ pl : Fin R.f → PlE H, (∀ v, pl v ∈ placesOver H.E p) ∧ Function.Injective pl ∧
      ∀ v v', ¬ IsConjPl H (pl v) (pl v') := by
  classical
  have := H.hostE_isGalois
  have : IsGaloisGroup Gal(H.E/ℚ) ℤ (𝓞 H.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ H.E
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (span {(p : ℤ)}).IsPrime := (span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, span_singleton_eq_bot]; exact hpZ.ne_zero)
  have hlo : ∀ w ∈ placesOver H.E p, w.asIdeal.LiesOver (span {(p : ℤ)}) := fun w hw => ⟨by
    have := w.isPrime
    refine hpM.eq_of_le (Ideal.IsPrime.under ℤ w.asIdeal).ne_top ?_
    rw [span_le, Set.singleton_subset_iff]
    change algebraMap ℤ (𝓞 H.E) p ∈ w.asIdeal
    have hw' : ((p : ℕ) : 𝓞 H.E) ∈ w.asIdeal := hw
    simpa using hw'⟩
  have hpos : 0 < Module.finrank ℚ H.E := Module.finrank_pos
  obtain ⟨w0, hw0⟩ : (placesOver H.E p).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have hw0p := w0.isPrime
  have hmem : ∀ σ : Gal(H.E/ℚ), ((p : ℕ) : 𝓞 H.E) ∈ σ • w0.asIdeal := fun σ => by
    have := Ideal.smul_mem_pointwise_smul σ _ _ (show ((p : ℕ) : 𝓞 H.E) ∈ w0.asIdeal from hw0)
    rwa [show σ • ((p : ℕ) : 𝓞 H.E) = p from map_natCast (MulSemiringAction.toRingHom _ _ σ) p] at this
  let act : Gal(H.E/ℚ) → PlE H := fun σ => ⟨σ • w0.asIdeal, inferInstance, fun hb => by
    have := hmem σ
    rw [hb, Ideal.mem_bot] at this
    exact hp.ne_zero (by exact_mod_cast this)⟩
  have himg : act '' Set.univ = placesOver H.E p := by
    ext w
    constructor
    · rintro ⟨σ, -, rfl⟩; exact hmem σ
    · intro hw
      have := w.isPrime
      have := hlo w hw
      have := hlo w0 hw0
      obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isGaloisGroup (span {(p : ℤ)}) w0.asIdeal w.asIdeal Gal(H.E/ℚ)
      exact ⟨σ, trivial, HeightOneSpectrum.ext hσ⟩
  have hinj : Function.Injective act := by
    rw [← Set.injOn_univ]
    refine Set.injOn_of_ncard_image_eq ?_ Set.finite_univ
    rw [himg, h, Set.ncard_univ, IsGalois.card_aut_eq_finrank]
  have hcard : Fintype.card (Fin R.f) = Fintype.card ↥(R.Psi) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, R.toFrame.natCard_Psi]; rfl
  let e := Fintype.equivOfCardEq hcard
  let ge := H.gal
  refine ⟨fun v => act (ge.symm (e v : R.GG)), fun v => hmem _, ?_, ?_⟩
  · intro v v' hv
    exact e.injective (Subtype.ext (ge.symm.injective (hinj hv)))
  · intro v v' hc
    have h1 : act (H.conj * ge.symm (e v : R.GG)) = act (ge.symm (e v' : R.GG)) := by
      apply HeightOneSpectrum.ext
      ext y
      show y ∈ (H.conj * ge.symm (e v : R.GG)) • w0.asIdeal ↔ _
      rw [mul_smul, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      refine hc (H.conj⁻¹ • y) y ?_
      exact (H.conj.apply_symm_apply (y : H.E)).symm
    have h2 := congrArg ge (hinj h1)
    rw [map_mul, ge.apply_symm_apply, ge.apply_symm_apply] at h2
    have h3 : ge H.conj = R.cc := H.galE_conjE
    have h4 : R.cc ∈ R.Psi := by
      have := mul_mem (e v').2 (inv_mem (e v).2)
      rwa [← h2, h3, mul_inv_cancel_right] at this
    exact R.toFrame.cc_notMem_Psi h4

def qPow (w : PlE H) (s : ℝ) : ℂˣ :=
  Units.mk0 (((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) (by
    have : Finite (𝓞 H.E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
    have h0 : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.card_pos (α := 𝓞 H.E ⧸ w.asIdeal)).ne'
    simp [Complex.cpow_eq_zero_iff, h0])

theorem qPow_add (w : PlE H) (s t : ℝ) : qPow H w s * qPow H w t = qPow H w (s + t) := by
  have : Finite (𝓞 H.E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have h0 : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.card_pos (α := 𝓞 H.E ⧸ w.asIdeal)).ne'
  ext
  simp [qPow, Complex.cpow_add _ _ h0]

theorem qPow_zero (w : PlE H) : qPow H w 0 = 1 := by ext; simp [qPow]

open Classical in

def toU (z : ℂ) : ℂˣ := if h : z = 0 then 1 else Units.mk0 z h

theorem toU_val (u : ℂˣ) : toU (u : ℂ) = u := by
  unfold toU; rw [dif_neg u.ne_zero]; ext; rfl

theorem val_toU {z : ℂ} (h : z ≠ 0) : ((toU z : ℂˣ) : ℂ) = z := by
  unfold toU; rw [dif_neg h]; rfl

open Polynomial in
set_option synthInstance.maxHeartbeats 400000 in

def nautToy (what₂ : Rows.Data R) (h : NHyp H what₂) : NAut (ndToy H what₂ h) where
  iotaQ i := i.elim
  iotaQC i := i.elim
  iota_LL i := i.elim
  iotaQ_alg i := i.elim
  locV_unr i := i.elim
  LP _ := Multiset ℂˣ
  lpDim := fun a => Multiset.card a
  lpZero _ := 0
  lpSum := fun a b => a + b
  lpTw := fun {w} a s => a.map (· * qPow H w s)
  lpChar := fun a χ => a.map (· * χ.prod)
  lpUnr _ m := m.map toU
  mono0 := fun _ => True
  unr := fun _ => True
  frobEig := fun a => a.map Units.val
  tempered := fun a => ∀ α ∈ a.map Units.val, ‖α‖ = 1
  tempered_unr _ _ := Iff.rfl
  lpDim_char _ _ _ := Multiset.card_map _ _
  unr_char _ _ _ _ _ := trivial
  monomial_char_iff _ _ _ := Iff.rfl
  inePol := fun a _ => (X - 1) ^ Multiset.card a
  items₂ _ _ _ := 1
  lpDim_zero _ := rfl
  lpDim_sum a b := Multiset.card_add a b
  lpDim_tw a s := Multiset.card_map _ _
  lpUnr_spec _ m hm := ⟨trivial, by
    rw [Multiset.map_map]
    exact (Multiset.map_congr rfl (fun z hz => val_toU (fun h0 => hm (h0 ▸ hz)))).trans (Multiset.map_id' m),
    Multiset.card_map _ _⟩
  unr_sum _ _ := ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
  monomial_sum_iff _ _ := ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
  frobEig_sum a b _ _ := Multiset.map_add _ a b
  unr_tw _ _ := Iff.rfl
  monomial_twist_iff _ _ := Iff.rfl
  frobEig_tw a s _ := by rw [Multiset.map_map, Multiset.map_map]; rfl
  frobEig_char a χ c _ _ _ hχ := by
    obtain ⟨u, rfl, rfl⟩ := Multiset.map_eq_singleton.mp hχ
    rw [Multiset.map_map, Multiset.map_map, Multiset.prod_singleton]; rfl
  lpZero_unr _ := trivial
  frobEig_zero _ := rfl
  lpSum_zero a := add_zero a
  lpSum_comm a b := add_comm a b
  lpSum_assoc a b c := add_assoc a b c
  lpTw_zero a := by simp [qPow_zero]
  lpTw_add a s t := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl (fun z _ => by simp only [Function.comp, mul_assoc, qPow_add])
  lpTw_sum a b s := Multiset.map_add _ a b
  unr_eq_lpUnr a _ := by
    rw [Multiset.map_map]
    exact ((Multiset.map_congr rfl (fun z _ => toU_val z)).trans (Multiset.map_id' a)).symm
  unr_mono0 _ _ := trivial
  frobEig_ne_zero a _ := fun h0 => by
    obtain ⟨u, -, hu⟩ := Multiset.mem_map.mp h0
    exact u.ne_zero hu
  frobEig_card a _ := Multiset.card_map _ _
  inePol_sum a b _ := by rw [Multiset.card_add, pow_add]
  inePol_tw a s _ _ := by rw [Multiset.card_map]
  unr_iff_ine _ := ⟨fun _ => ⟨trivial, fun _ _ => rfl⟩, fun _ => trivial⟩
  inertiaCharpoly_zero _ _ := rfl
  inertiaCharpoly_add _ _ _ _ := (one_mul 1).symm
  CG a := {f : PlE H → Multiset ℂˣ // ∀ w, Multiset.card (f w) = a}
  csd := fun π => ∀ w w', IsConjPl H w w' → π.1 w' = (π.1 w).map (·⁻¹)
  csd_unr := fun π w w' h hc _ => ⟨trivial, by
    rw [h w w' hc, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl (fun u _ => Units.val_inv_eq_inv_val u)⟩
  csd_tw := fun π χ hχ hπ w w' hc => by
    show (π.1 w').map (· * (χ.1 w').prod) = ((π.1 w).map (· * (χ.1 w).prod)).map (·⁻¹)
    rw [hπ w w' hc, hχ w w' hc, Multiset.prod_map_inv', Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl (fun u _ => (mul_inv u _).symm)
  ralg := fun {a} _ => ∀ _ : H.E →+* ℂ, (Multiset.replicate a (0 : ℂ)).Nodup ∧
    ∀ z ∈ Multiset.replicate a (0 : ℂ), ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2
  ralg_def := fun _ => Iff.rfl
  locG := fun π w => π.1 w
  locG_dim := fun π w => π.2 w
  locG_unr_ae := fun _ => Filter.Eventually.of_forall fun _ => trivial
  tw := fun π χ => ⟨fun w => (π.1 w).map (· * (χ.1 w).prod), fun w => (Multiset.card_map _ _).trans (π.2 w)⟩
  locG_tw := fun _ _ _ => rfl
  infG := fun {a} _ _ => Multiset.replicate a 0
  infG_tw := fun _ _ _ s hs => by
    rw [Multiset.replicate_one, Multiset.singleton_inj] at hs
    simp [← hs]
  infG_card := fun _ _ => Multiset.card_replicate _ _
  muC i := i.elim
  etaT := ⟨fun _ => {-1}, fun _ => rfl⟩
  etaTinv := ⟨fun _ => {-1}, fun _ => rfl⟩
  etaT_unr _ := trivial
  etaT_inert _ _ := by simp
  etaTinv_def _ := ⟨trivial, by simp⟩
  etaT_split _ _ _ _ a b ha hb := by
    simp only [Multiset.map_singleton, Multiset.singleton_inj, Units.val_neg, Units.val_one] at ha hb
    rw [← ha, ← hb]; norm_num
  muC_csd i := i.elim
  lab_loc i := i.elim
  wdOf_dim i := i.elim
  wdOf_unr i := i.elim
  wdOf_frob i := i.elim
  wdOf_ine i := i.elim
  wdOf_mono0 i := i.elim
  jumpsInf_def i := i.elim
  locAut_hodgeTateWeightsLevelZero_def i := i.elim
  chi_mu i := i.elim
  AV i := i.elim
  finAV i := i.elim
  ptV i := i.elim
  typeV i := i.elim
  typeV_ne i := i.elim
  typeV_indep i := i.elim
  typeV_top i := i.elim
  pt_surj i := i.elim
  eig_dim i := i.elim
  locV i := i.elim
  satV i := i.elim
  pt_loc i := i.elim
  infWt i := i.elim
  locW i := i.elim
  satW i := i.elim
  plGw k := (exists_halfPlaces H _ (H.g_prime k) (h.hg k)).choose
  plGw_over k := (exists_halfPlaces H _ (H.g_prime k) (h.hg k)).choose_spec.1
  plGw_inj k := (exists_halfPlaces H _ (H.g_prime k) (h.hg k)).choose_spec.2.1
  plGw_nconj k := (exists_halfPlaces H _ (H.g_prime k) (h.hg k)).choose_spec.2.2
  wdOf i := i.elim
  IsCrysW i := i.elim
  IsPotCrysW i := i.elim
  IsdRW i := i.elim
  jumpsW i := i.elim
  wdOf_unrL i := i.elim
  wdOf_mono0L i := i.elim
  jumpsInf i := i.elim
  locAutHodgeTateWeightsLevelZero i := i.elim
  kFbar i := i.elim

theorem shaExample_eq (p : ℕ) [hp : Fact p.Prime] (e : ℕ) :
    shaExample H p e = ((Formalism.GaloisCohomology.shaLen (toyLocalData H p) (e : ℤ)).toNat : ℚ) := by
  unfold shaExample
  rw [dif_pos hp.out]

open Ideal Polynomial in

theorem placesOver_ncard_of_frob (p : ℕ) [hp : Fact p.Prime] (hpN : ¬ p ∣ H.condN)
    (hF : ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
      IsArithFrobAt ℤ σ P → H.galE σ = 1) :
    (placesOver H.E p).ncard = Module.finrank ℚ H.E := by
  classical
  have := H.hostE_isGalois
  have : IsGaloisGroup Gal(H.E/ℚ) ℤ (𝓞 H.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ H.E
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.out
  have hpI : (span {(p : ℤ)}).IsPrime := (span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, span_singleton_eq_bot]; exact hpZ.ne_zero)
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((span {(p : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
  obtain ⟨hex, -, -, hin⟩ := H.der.frob p hpN P

  obtain ⟨σF, hσF⟩ := hex
  have hg1 : H.galE σF = 1 := hF P σF hσF
  have hσ1 : σF = 1 := (H.galE_eq_one_iff σF).1 hg1
  subst hσ1
  have hunder : P.under ℤ = span {(p : ℤ)} := (Ideal.LiesOver.over (P := P) (p := span {(p : ℤ)})).symm
  have hcardZ : Nat.card (ℤ ⧸ span {(p : ℤ)}) = p := by
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hfrob : ∀ x : 𝓞 H.E, x - x ^ p ∈ P := by
    intro x
    have := hσF x
    rw [hunder, hcardZ] at this
    simpa using this

  have hne0 : ∀ I : Ideal (𝓞 H.E), I.LiesOver (span {(p : ℤ)}) → I ≠ ⊥ := by
    rintro I hI rfl
    have h0 : span {(p : ℤ)} = ⊥ := by
      rw [hI.over]; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 H.E))
    exact hpZ.ne_zero (span_singleton_eq_bot.1 h0)
  have hP0 : P ≠ ⊥ := hne0 P hPl
  have hPM : P.IsMaximal := hPp.isMaximal hP0
  let : Field (𝓞 H.E ⧸ P) := Ideal.Quotient.field P
  have : Finite (𝓞 H.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  let : Fintype (𝓞 H.E ⧸ P) := Fintype.ofFinite _
  have hne : (X ^ p - X : (𝓞 H.E ⧸ P)[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hp.out.one_lt
  have hroot : ∀ y : 𝓞 H.E ⧸ P, y ∈ (X ^ p - X : (𝓞 H.E ⧸ P)[X]).roots := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, ← map_pow, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem, ← neg_mem_iff, neg_sub]
    exact hfrob x
  have hle : Fintype.card (𝓞 H.E ⧸ P) ≤ p := by
    calc Fintype.card (𝓞 H.E ⧸ P) = (Finset.univ : Finset (𝓞 H.E ⧸ P)).card := rfl
      _ ≤ (X ^ p - X : (𝓞 H.E ⧸ P)[X]).roots.toFinset.card :=
          Finset.card_le_card (fun y _ => Multiset.mem_toFinset.2 (hroot y))
      _ ≤ (X ^ p - X : (𝓞 H.E ⧸ P)[X]).roots.card := Multiset.toFinset_card_le _
      _ ≤ (X ^ p - X : (𝓞 H.E ⧸ P)[X]).natDegree := card_roots' _
      _ = p := FiniteField.X_pow_card_sub_X_natDegree_eq _ hp.out.one_lt
  have hnorm : absNorm P = p ^ ((span {(p : ℤ)}).inertiaDeg' P) :=
    absNorm_eq_pow_inertiaDeg' P hp.out
  have hcardk : absNorm P = Fintype.card (𝓞 H.E ⧸ P) := by
    rw [absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [← inertiaDeg'_eq_inertiaDeg (span {(p : ℤ)}) P]
    have hpos : 0 < (span {(p : ℤ)}).inertiaDeg' P := by
      rw [inertiaDeg'_eq_inertiaDeg (span {(p : ℤ)}) P]; exact inertiaDeg_pos P ℤ
    have hle' : p ^ (span {(p : ℤ)}).inertiaDeg' P ≤ p ^ 1 := by
      rw [← hnorm, hcardk, pow_one]; exact hle
    have := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hle'
    omega

  have hinert : Nat.card (P.inertia Gal(H.E/ℚ)) = 1 := by
    have : P.inertia Gal(H.E/ℚ) = ⊥ := by
      ext σ
      rw [AddSubgroup.mem_inertia, Subgroup.mem_bot]
      exact hin σ
    rw [this]; exact Subgroup.card_bot
  have key := ncard_primesOver_mul_card_inertia_mul_finrank (G := Gal(H.E/ℚ)) (span {(p : ℤ)}) P
  rw [hinert, hf, mul_one, mul_one, IsGalois.card_aut_eq_finrank] at key

  rw [← key]
  have himg : (fun v : HeightOneSpectrum (𝓞 H.E) => v.asIdeal) '' placesOver H.E p =
      (span {(p : ℤ)}).primesOver (𝓞 H.E) := by
    ext I
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.isPrime, ⟨?_⟩⟩
      have hle : span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
        rw [span_le, Set.singleton_subset_iff]
        change algebraMap ℤ (𝓞 H.E) p ∈ v.asIdeal
        have hv' : ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal := hv
        simpa using hv'
      exact hpM.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle
    · rintro ⟨hI, hIl⟩
      refine ⟨⟨I, hI, hne0 I hIl⟩, ?_, rfl⟩
      change ((p : ℕ) : 𝓞 H.E) ∈ I
      have : (p : ℤ) ∈ I.under ℤ := by rw [← hIl.over]; exact mem_span_singleton_self _
      simpa using this
  rw [← himg, Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h)]

theorem placesOver_ncard_of_art (p : ℕ) [hp : Fact p.Prime] (hpN : p.Coprime H.condN)
    (hart : H.art (ZMod.unitOfCoprime p hpN) = 1) :
    (placesOver H.E p).ncard = Module.finrank ℚ H.E := by
  refine placesOver_ncard_of_frob H p ((Nat.Prime.coprime_iff_not_dvd hp.out).1 hpN) ?_
  intro P _ _ σ hσ
  rw [(H.frob_iff p hpN P σ).1 hσ, hart]

theorem placesOver_ncard_of_split (p : ℕ) [hp : Fact p.Prime] (hpm : p % H.condN = 1) :
    (placesOver H.E p).ncard = Module.finrank ℚ H.E := by
  have h1 : 1 < H.condN := lt_of_lt_of_le (by norm_num)
    (Nat.le_of_dvd (Nat.pos_of_ne_zero H.condN_ne_zero) H.sixteen_dvd_condN)
  have hmod : p ≡ 1 [MOD H.condN] := by
    unfold Nat.ModEq; rw [hpm, Nat.mod_eq_of_lt h1]
  have hpN : p.Coprime H.condN := Nat.coprime_of_mul_modEq_one 1 (by simpa using hmod)
  refine placesOver_ncard_of_art H p hpN ?_
  have : ZMod.unitOfCoprime p hpN = 1 := by
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, Units.val_one, ← Nat.cast_one (R := ZMod H.condN),
      ZMod.natCast_eq_natCast_iff]
    exact hmod
  rw [this, map_one]

theorem placesOver_ncard_of_split_inj (hinj : Function.Injective R.h) (p : ℕ) [hp : Fact p.Prime]
    (hpN : ¬ p ∣ H.condN) (hjq : jacobiSym (-(H.q : ℤ)) p = 1) (hjd : jacobiSym (-(H.d : ℤ)) p = 1)
    (hpm : (p : ZMod (2 ^ (R.e + 2))) = 1 ∨ (p : ZMod (2 ^ (R.e + 2))) = -1) :
    (placesOver H.E p).ncard = Module.finrank ℚ H.E := by
  refine placesOver_ncard_of_frob H p hpN ?_
  intro P _ _ σ hσ
  obtain ⟨h1, h2, u, hu, h3⟩ := (H.der.frob p hpN P).2.2.1 σ hσ
  rw [H.flPS.psAt_prime hp.out hpN] at h1
  have hu1 : Formalism.FrobeniusOrbits.hcl R.e u = 1 := by
    rcases hpm with h | h
    · have : u = 1 := Units.ext (by rw [hu, h]; rfl)
      rw [this]; rfl
    · have : u = -1 := Units.ext (by rw [hu, h]; simp)
      rw [this]; exact Formalism.FrobeniusOrbits.hcl_neg_one
  refine Prod.ext (Prod.ext (Units.ext ?_) (Units.ext ?_)) ?_
  · rw [h1, hjq]; rfl
  · rw [h2, hjd]; rfl
  · rw [hu1, R.toFrame.hH_apply] at h3
    have h4 : R.h (R.iotaInv (H.gal σ).2) = R.h 0 := by rw [map_zero]; exact h3
    exact (R.toFrame.iotaInv_eq_zero_iff _).1 (hinj h4)

theorem g_split_of (hg : ∀ k, H.g k % H.condN = 1) :
    ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E := by
  intro k
  have : Fact (H.g k).Prime := ⟨H.g_prime k⟩
  exact placesOver_ncard_of_split H (H.g k) (hg k)

theorem g_split_of_inj (hinj : Function.Injective R.h)
    (hg : ∀ k, ¬ H.g k ∣ H.condN ∧ jacobiSym (-(H.q : ℤ)) (H.g k) = 1 ∧
      jacobiSym (-(H.d : ℤ)) (H.g k) = 1 ∧
      ((H.g k : ZMod (2 ^ (R.e + 2))) = 1 ∨ (H.g k : ZMod (2 ^ (R.e + 2))) = -1)) :
    ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E := by
  intro k
  have : Fact (H.g k).Prime := ⟨H.g_prime k⟩
  obtain ⟨h1, h2, h3, h4⟩ := hg k
  exact placesOver_ncard_of_split_inj H hinj (H.g k) h1 h2 h3 h4

theorem examplePrimes_split :
    jacobiSym (-571) 127 = 1 ∧ jacobiSym (-599) 127 = 1 ∧ jacobiSym (-571) 337 = 1 ∧
      jacobiSym (-599) 337 = 1 ∧ ((127 : ℕ) : ZMod 16) = -1 ∧ ((337 : ℕ) : ZMod 16) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> decide

set_option synthInstance.maxHeartbeats 400000 in

def nbcToy (what₂ : Rows.Data R) (h : NHyp H what₂) : NBC (nautToy H what₂ h) where
  AU _ := Empty
  multAU _ π := π.elim
  sphAU _ π := π.elim
  locAU _ π := π.elim
  satAU _ π := π.elim
  satAU_card _ π := π.elim
  Wt _ := Empty
  infW _ W := W.elim
  infW_card _ W := W.elim
  infW_alg _ W := W.elim
  wtAU _ π := π.elim
  embAV i := i.elim
  embAV_inj i := i.elim
  embAV_loc i := i.elim
  embAV_sat i := i.elim
  embAV_sph i := i.elim
  embAV_inf i := i.elim

set_option synthInstance.maxHeartbeats 400000 in

def nexpToy {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) (h : NHyp H what₂) :
    NExp R H what₂ LL0 (ndToy H what₂ h) (ntwToy H LL0 h) where
  Fm i := i.elim
  eLL0 _ := 0
  eAlg_def i := i.elim
  thPsi_one i := i.elim
  twPsi_one i := i.elim
  eH i := i.elim
  eH_idem i := i.elim
  MtLat_fg i := i.elim
  MtLat_span i := i.elim
  embB i := i.elim
  embB_inj i := i.elim
  acgFm i := i.elim
  modFmK i := i.elim
  modFmO i := i.elim
  towFm i := i.elim
  fdFm i := i.elim
  actG i := i.elim
  U := ⊥
  psiU i := i.elim
  eAlg i := i.elim
  eAlg_idem i := i.elim
  eAlg_central i := i.elim
  Bsup i := i.elim
  Dat i := i.elim
  th i := i.elim
  lev i := i.elim
  thPsi i := i.elim
  thU i := i.elim
  twPsi i := i.elim
  twDel i := i.elim
  delU i := i.elim
  delU_unr i := i.elim
  delU_l i := i.elim
  delU_anti i := i.elim
  delU_open i := i.elim
  delU_res i := i.elim
  delU_conj i := i.elim
  MtV i := i.elim
  acgMt i := i.elim
  modMtK i := i.elim
  modMtO i := i.elim
  towMt i := i.elim
  fdMt i := i.elim
  MtLat i := i.elim
  thP i := i.elim
  hkF i := i.elim

theorem example_Z_compatibility (what₂ : Rows.Data R) (h : NHyp H what₂) :
    ∀ i x, x ∈ (ndToy H what₂ h).Z i ↔ x ∈ Formalism.MainNotions.N.ZN (ndToy H what₂ h) (nautToy H what₂ h) i :=
  fun i => i.elim

theorem example_goodZ_compatibility (what₂ : Rows.Data R) (h : NHyp H what₂) :
    ∀ i x, x ∈ (ndToy H what₂ h).Zgood i ↔
      x ∈ Formalism.MainNotions.N.ZgoodN (ndToy H what₂ h) (nautToy H what₂ h) i :=
  fun i => i.elim

theorem example_etaJ_compatibility (what₂ : Rows.Data R) (h : NHyp H what₂) (hη : ∀ j w, what₂.etaJ j w = 0) :
    ∀ j w, 1 ≤ j → j ≤ R.m → what₂.etaJ j w = ∑ i ∈ (ndToy H what₂ h).locs j w, (ndToy H what₂ h).etaLoc i := by
  intro j w _ _
  rw [hη]
  rfl

end Formalism.BasicNotions.Examples₂
