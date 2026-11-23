import Formalism.LocalRingCardinality.SpanPowerMembership.NStageTrivialCharacterCoeffEq

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000 in

structure TwCore (R : Ranks) (H : Host R) (what₂ : Rows.Data R) [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) (N : NData R H what₂) where
  cc : N.Om ≃+* N.Om
  cc_cm : IsCMConjOm H.E N.Om cc
  Tw : Type
  l : Tw → ℕ
  [lPrime : ∀ i, Fact (l i).Prime]
  O0 : Tw → Type
  [crO0 : ∀ i, CommRing (O0 i)]
  [twistBaseCoefficientRing_isDomain : ∀ i, IsDomain (O0 i)]
  [twistBaseCoefficientRing_isDVR : ∀ i, IsDiscreteValuationRing (O0 i)]
  [algO0 : ∀ i, Algebra ℤ_[l i] (O0 i)]
  [twistBaseCoefficientRing_finite_padic : ∀ i, Module.Finite ℤ_[l i] (O0 i)]
  twistBaseCoefficientRing_residueField_finite : ∀ i, Finite (IsLocalRing.ResidueField (O0 i))
  [topO0 : ∀ i, TopologicalSpace (O0 i)]
  [twistBaseCoefficientRing_topologicalRing : ∀ i, IsTopologicalRing (O0 i)]
  twistBaseCoefficientRing_isAdic : ∀ i, IsAdic (IsLocalRing.maximalIdeal (O0 i))
  emb0 : ∀ i, LL0 →+* FractionRing (O0 i)
  emb0b : ∀ i, LL0 →+* FractionRing (O0 i)
  restX_coefficientEmbedding_conj : ∀ i (x y : LL0), (y : what₂.LL) = star (x : what₂.LL) → emb0b i x = emb0 i y
  O : Tw → Type
  [crO : ∀ i, CommRing (O i)]
  [domO : ∀ i, IsDomain (O i)]
  [dvrO : ∀ i, IsDiscreteValuationRing (O i)]
  [algO : ∀ i, Algebra (O0 i) (O i)]
  O_inj : ∀ i, Function.Injective (algebraMap (O0 i) (O i))
  O_l : ∀ i, ((l i : ℕ) : O i) ∈ IsLocalRing.maximalIdeal (O i)
  [topO : ∀ i, TopologicalSpace (O i)]
  [trO : ∀ i, IsTopologicalRing (O i)]
  O_adic : ∀ i, IsAdic (IsLocalRing.maximalIdeal (O i))
  resO_ac : ∀ i, IsAlgClosed (IsLocalRing.ResidueField (O i))
  O_complete : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (O i)) (O i)
  Ok : Tw → ℕ → Type
  [crOk : ∀ i k, CommRing (Ok i k)]
  [domOk : ∀ i k, IsDomain (Ok i k)]
  [dvrOk : ∀ i k, IsDiscreteValuationRing (Ok i k)]
  [algOk : ∀ i k, Algebra (O i) (Ok i k)]
  Ok_inj : ∀ i k, Function.Injective (algebraMap (O i) (Ok i k))
  Ok_fin : ∀ i k, Module.Finite (O i) (Ok i k)
  zk : ∀ i k, (Ok i k)ˣ
  zk_prim : ∀ i k, IsPrimitiveRoot ((zk i k : Ok i k)) (l i ^ k)
  Ok_gen : ∀ i k (x : FractionRing (Ok i k)), ∃ p : Polynomial (O i), ∃ d : O i, d ≠ 0 ∧
    x * algebraMap (Ok i k) (FractionRing (Ok i k)) (algebraMap (O i) (Ok i k) d) =
      algebraMap (Ok i k) (FractionRing (Ok i k)) (Polynomial.aeval (zk i k : Ok i k) p)
  pD : Tw → Finset (HeightOneSpectrum (𝓞 H.E))
  pD_eq : ∀ i, (pD i : Set (HeightOneSpectrum (𝓞 H.E))) =
    placesOver H.E (if l i = H.pde then H.pde' else H.pde)
  delta : ∀ i, Formalism.ConjugateSelfDual.G H.E N.Om →* (O0 i)ˣ
  delta_open : ∀ i, IsOpen ((delta i).ker : Set (Formalism.ConjugateSelfDual.G H.E N.Om))
  delta_anti : ∀ i, AntiHom cc (delta i)
  delta_ram : ∀ i, RamExactly (delta i) ↑(pD i)
  delta_15 : ∀ i, ∀ v ∈ pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    Nat.card ((Ine (F := H.E) A).map (delta i)) = 15
  delta_tame : ∀ i, ∀ v ∈ pD i, Ideal.absNorm v.asIdeal % 15 = 1
  RCG : Tw → Finset (HeightOneSpectrum (𝓞 H.E)) → Type
  [grpRCG : ∀ i Q, CommGroup (RCG i Q)]
  [finRCG : ∀ i Q, Fintype (RCG i Q)]
  RCG_l : ∀ i Q (x : RCG i Q), ∃ n : ℕ, x ^ (l i ^ n) = 1
  art : ∀ i Q, Formalism.ConjugateSelfDual.G H.E N.Om →* RCG i Q
  art_surj : ∀ i Q, Function.Surjective (art i Q)
  art_cont : ∀ i Q, IsOpen ((art i Q).ker : Set (Formalism.ConjugateSelfDual.G H.E N.Om))
  art_anti : ∀ i Q, AntiHom cc (art i Q)
  art_unr : ∀ i Q v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := H.E) A, art i Q σ = 1
  art_univ : ∀ i Q, (∀ v ∈ Q, v ∉ placesOver H.E (l i)) → ∀ (A' : Type) [CommGroup A'] [Finite A'],
    (∀ x : A', ∃ n : ℕ, x ^ (l i ^ n) = 1) → ∀ φ : Formalism.ConjugateSelfDual.G H.E N.Om →* A',
    IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G H.E N.Om)) → AntiHom cc φ →
    (∀ v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, φ σ = 1) →
    ∃ f : RCG i Q →* A', f.comp (art i Q) = φ
  res : ∀ i (Q Q' : Finset (HeightOneSpectrum (𝓞 H.E))), Q' ⊆ Q → (RCG i Q →* RCG i Q')
  res_art : ∀ i Q Q' (h : Q' ⊆ Q), (res i Q Q' h).comp (art i Q) = art i Q'
  iC : ∀ i, FractionRing (O i) →+* ℂ_[l i]
  iC_int : ∀ i (x : FractionRing (O i)), ‖iC i x‖ ≤ 1 ↔ x ∈ (algebraMap (O i) (FractionRing (O i))).range
  br : ∀ i (w : HeightOneSpectrum (𝓞 H.E)), w ∈ placesOver H.E (l i) →
    LocBridge (l i) H.E N.Om (Dec (F := H.E) (N.plOm.1 w)) (O0 i)

  br_ind : ∀ i (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (l i)) (x : N.Om),
    x ∈ N.plOm.1 w ↔ ‖(br i w hw).j x‖ ≤ 1
  cover : ∀ p : ℕ, p.Prime → ∀ w : HeightOneSpectrum (𝓞 ↥LL0), ((p : ℕ) : 𝓞 ↥LL0) ∈ w.asIdeal →
    ∃ i, l i = p ∧ ∀ x : 𝓞 ↥LL0, x ∈ w.asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal (O0 i),
      algebraMap (O0 i) (FractionRing (O0 i)) y = emb0 i (x : ↥LL0)

attribute [instance] TwCore.lPrime TwCore.crO0 TwCore.twistBaseCoefficientRing_isDomain TwCore.twistBaseCoefficientRing_isDVR TwCore.algO0 TwCore.twistBaseCoefficientRing_finite_padic TwCore.topO0 TwCore.twistBaseCoefficientRing_topologicalRing TwCore.crO TwCore.domO TwCore.dvrO TwCore.algO TwCore.topO TwCore.trO TwCore.crOk TwCore.domOk TwCore.dvrOk TwCore.algOk TwCore.grpRCG TwCore.finRCG

theorem placesOver_finite (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h : Ideal.span {(p : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast hp
  refine (Ideal.finite_factors h).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.mpr hv

theorem placesOver_disj (E : Type) [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ≠ q) {v} (h1 : v ∈ placesOver E p) : v ∉ placesOver E q :=
  fun h2 => h (PlacesToy.prime_mem_unique v hp hq h1 h2)

namespace TwCore

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} (C : TwCore R H what₂ LL0 N)

theorem delta_unr (i) (v) (hv : v ∉ C.pD i) (A : ValuationSubring N.Om) (hA : IsPlaceOver A v)
    (σ) (hσ : σ ∈ Ine (F := H.E) A) : C.delta i σ = 1 := by
  by_contra hne
  exact hv ((C.delta_ram i v A hA).mp ⟨σ, hσ, hne⟩)

theorem g_not_pD (i k v) (hv : v ∈ placesOver H.E (H.g k)) : v ∉ C.pD i := by
  intro h
  have h2 : v ∈ (C.pD i : Set _) := h
  rw [C.pD_eq] at h2
  split_ifs at h2
  · exact placesOver_disj _ (H.g_prime k) H.pde'_prime (H.pde_ne_g k).2.symm hv h2
  · exact placesOver_disj _ (H.g_prime k) H.pde_prime (H.pde_ne_g k).1.symm hv h2

def chi (i) (b : Bool) : Formalism.ConjugateSelfDual.G H.E N.Om →* (C.O0 i)ˣ := if b then C.delta i else (C.delta i)⁻¹

theorem chi_apply (i b σ) : C.chi i b σ = if b then C.delta i σ else (C.delta i σ)⁻¹ := by
  cases b <;> rfl

theorem chi_cont (i b) : Continuous (fun g => ((C.chi i b g : (C.O0 i)ˣ) : C.O0 i)) := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).mpr fun g => ?_)
  have ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' ((C.delta i).ker : Set (Formalism.ConjugateSelfDual.G H.E N.Om))) :=
    (C.delta_open i).preimage (continuous_const.mul continuous_id)
  filter_upwards [ho.mem_nhds (show g⁻¹ * g ∈ (C.delta i).ker by simp)] with x hx
  have h1 : C.delta i (g⁻¹ * x) = 1 := hx
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  rw [chi_apply, chi_apply, h1]

open Classical in
set_option synthInstance.maxHeartbeats 400000 in

def toTw [hL : IsEmpty N.Loc] : NTw R H what₂ LL0 N where
  cc := C.cc
  cc_cm := C.cc_cm
  Tw := C.Tw
  l := C.l
  lPrime := C.lPrime
  O0 := C.O0
  crO0 := C.crO0
  twistBaseCoefficientRing_isDomain := C.twistBaseCoefficientRing_isDomain
  twistBaseCoefficientRing_isDVR := C.twistBaseCoefficientRing_isDVR
  algO0 := C.algO0
  twistBaseCoefficientRing_finite_padic := C.twistBaseCoefficientRing_finite_padic
  twistBaseCoefficientRing_residueField_finite := C.twistBaseCoefficientRing_residueField_finite
  topO0 := C.topO0
  twistBaseCoefficientRing_topologicalRing := C.twistBaseCoefficientRing_topologicalRing
  twistBaseCoefficientRing_isAdic := C.twistBaseCoefficientRing_isAdic
  emb0 := C.emb0
  emb0b := C.emb0b
  restX_coefficientEmbedding_conj := C.restX_coefficientEmbedding_conj
  O := C.O
  crO := C.crO
  domO := C.domO
  dvrO := C.dvrO
  algO := C.algO
  O_inj := C.O_inj
  O_l := C.O_l
  topO := C.topO
  trO := C.trO
  O_adic := C.O_adic
  resO_ac := C.resO_ac
  O_complete := C.O_complete
  Ok := C.Ok
  crOk := C.crOk
  domOk := C.domOk
  dvrOk := C.dvrOk
  algOk := C.algOk
  Ok_inj := C.Ok_inj
  Ok_fin := C.Ok_fin
  zk := C.zk
  zk_prim := C.zk_prim
  Ok_gen := C.Ok_gen
  pD := C.pD
  pD_eq := C.pD_eq
  delta := C.delta
  delta_open := C.delta_open
  delta_anti := C.delta_anti
  delta_ram := C.delta_ram
  delta_15 := C.delta_15
  delta_tame := C.delta_tame
  RCG := C.RCG
  grpRCG := C.grpRCG
  finRCG := C.finRCG
  RCG_l := C.RCG_l
  art := C.art
  art_surj := C.art_surj
  art_cont := C.art_cont
  art_anti := C.art_anti
  art_unr := C.art_unr
  art_univ := C.art_univ
  res := C.res
  res_art := C.res_art
  chi1 i _ b := C.chi i b
  twistCharacterFamily_continuous i _ b := C.chi_cont i b
  twistCharacterFamily_unramified i _ b v _ _ hv A hA σ hσ := by rw [chi_apply, C.delta_unr i v hv A hA σ hσ]; simp
  twistCharacterFamily_at_auxiliaryPlaces i _ b _ _ _ _ σ _ := C.chi_apply i b σ
  twistCharacterFamily_tame i _ b k v hv _ A hA σ hσ := by
    rw [chi_apply, C.delta_unr i v (C.g_not_pD i k v hv) A hA σ hσ]; simp
  Sig _ := Empty
  jS _ s := s.elim
  jS_range _ s := s.elim
  side _ s := s.elim
  rhoS _ s := s.elim
  rhoS_cont _ s := s.elim
  hEig _ s := s.elim
  S0 i := (placesOver_finite H.E (C.l i) (C.lPrime i).out.ne_zero).toFinset ∪
    (placesOver_finite H.E (H.g 0) (H.g_prime 0).ne_zero).toFinset ∪
    (placesOver_finite H.E (H.g 1) (H.g_prime 1).ne_zero).toFinset ∪ C.pD i
  twistExcludedPlaces_contains_residueChar i v hv := by simp [hv]
  placesOver_subset_exceptional i k v hv := by fin_cases k <;> simp_all
  primes_subset_exceptional i := Finset.subset_union_right
  B _ _ _ := PUnit
  Theta _ _ _ := ⊥
  ThetaPsi _ _ _ _ _ _ := ⊥
  ThetaPsi_one _ _ _ _ := Subsingleton.elim _ _
  hk _ _ _ _ _ := 1
  hk_zero _ _ _ _ := rfl
  abelian₂ _ := Empty
  jL _ s := s.elim
  sideL _ s := s.elim
  s2 _ s := s.elim
  jL_range _ s := s.elim
  lamG _ s := s.elim
  lamG_cont _ s := s.elim
  lamG_unr _ s := s.elim
  lamG_pD _ s := s.elim
  lamG_anti _ s := s.elim
  Xv _ s := s.elim
  Xv_def _ s := s.elim
  qs _ s := s.elim
  qs_sq _ s := s.elim
  qs_conj _ s := s.elim
  th _ _ s := s.elim
  twOf a := hL.elim a
  twSide a := hL.elim a
  twOf_l a := hL.elim a
  twist₂ a := hL.elim a
  twO_emb a := hL.elim a
  psiL a := hL.elim a
  psiL_ord a := hL.elim a
  psiL_open a := hL.elim a
  psiL_anti a := hL.elim a
  psiL_ram a := hL.elim a
  psiL_l a := hL.elim a
  chi_tw a := hL.elim a

variable [hL : IsEmpty N.Loc]

set_option synthInstance.maxHeartbeats 400000 in

def toExp : NExp R H what₂ LL0 N C.toTw where
  Fm _ _ _ := PUnit
  actG _ _ _ := 1
  U := ⊥
  psiU _ _ := 1
  eAlg _ _ := 0
  eLL0 _ := 0
  eAlg_def _ _ _ := by rw [map_zero, map_zero]; rfl
  eAlg_idem _ _ := mul_zero _
  eAlg_central _ _ _ := by rw [zero_mul, mul_zero]
  Bsup _ _ _ := ⊥
  Dat _ _ _ := Empty
  th _ _ _ d := d.elim
  lev _ _ _ d := d.elim
  thPsi _ _ _ _ _ _ d := d.elim
  thPsi_one _ _ _ _ d := d.elim
  thU _ _ _ _ _ d := d.elim
  twPsi _ _ _ _ _ := 0
  twPsi_one _ _ _ _ _ := Subsingleton.elim _ _
  twDel _ _ _ _ _ := 0
  delU _ _ _ := 1
  delU_unr := by intros; rfl
  delU_l := by intros; rfl
  delU_anti _ _ _ _ _ _ := by simp
  delU_open _ _ _ := by simp [MonoidHom.ker_one]
  delU_res := by intros; rfl
  delU_conj _ _ _ _ _ _ _ _ := ⟨1, fun _ => by simp⟩
  MtV _ _ _ _ _ _ := PUnit
  MtLat _ _ _ _ _ _ := ⊥
  MtLat_fg _ _ _ _ _ _ := Submodule.fg_bot
  MtLat_span _ _ _ _ _ _ := Subsingleton.elim _ _
  thP _ _ _ _ _ _ := 0
  hkF _ _ _ _ _ := 1
  embB _ _ _ := 0
  embB_inj _ _ _ _ _ _ := rfl
  eH _ _ _ := 1
  eH_idem _ _ _ := mul_one _

open Classical in
set_option synthInstance.maxHeartbeats 400000 in

def toTh : NTh R H what₂ LL0 N C.toTw C.toExp where
  iC := C.iC
  iC_int := C.iC_int
  aL i := if ∃ k, C.l i = H.g k then 1 else 0
  aL_g i k h := if_pos ⟨k, h⟩
  aL_off i h := if_neg fun ⟨k, hk⟩ => h k hk
  Pt _ _ := Empty
  ev _ _ _ := 0
  ev_smul _ _ _ _ _ y := y.elim
  ev_inj _ _ _ _ _ _ := rfl
  Lt _ _ := PUnit
  Let _ _ := Empty
  Harm _ _ := Set.univ
  Ctr _ _ := Empty
  ctrC _ _ κ := κ.elim
  Harm_def _ _ _ := ⟨fun _ κ => κ.elim, fun _ => trivial⟩
  thV _ _ _ _ y := y.elim
  thV_add _ _ _ _ _ y := y.elim
  thV_smul _ _ _ _ _ y := y.elim
  thV_addP _ _ _ _ _ y := y.elim
  thV_smulP _ _ _ _ _ y := y.elim
  datPhi _ _ _ d := d.elim
  datP _ _ _ d := d.elim
  recDet _ _ y := y.elim
  Kq _ _ _ := PUnit
  actK _ _ _ _ y := y
  actK_one _ _ _ _ := rfl
  actK_mul _ _ _ _ _ _ := rfl
  recDetq _ _ _ y := y.elim
  recDetq_mem _ _ _ y := y.elim
  recDet_act _ _ _ _ y := y.elim
  recDetq_act _ _ _ _ _ y := y.elim
  hkIdx _ _ _ _ := Empty
  hkMove _ _ _ _ c := c.elim
  hkU _ _ _ _ _ c := c.elim
  hk_ev _ _ _ _ _ _ _ _ _ _ y := y.elim
  MaximalUnramifiedExtension _ := ⊤
  FmUr _ _ _ := ⊤
  FmUr_smul := by intros; trivial
  FmUr_span _ _ _ := eq_top_iff.mpr fun x _ => (show x = 0 from rfl) ▸ Submodule.zero_mem _
  Bsup_def _ _ _ := le_antisymm bot_le fun x _ => (show x = 0 from rfl) ▸ Submodule.zero_mem _

end TwCore

def TwCore.toGap (D : D7) (hL : IsEmpty D.nd.Loc) (he : ∀ g, D.ntypes.e0.coeff g = 0)
    (C : TwCore D.R D.host D.what₂ D.LL0 D.nd) : TwGap D where
  ntw := C.toTw
  nexp := C.toExp
  nth := C.toTh
  ntwbr := C.br
  ntwbr_ind := C.br_ind
  nStage_trivialCharacter_coeff_eq g := (map_zero D.what₂.embLL).trans (he g).symm
  cover := C.cover

end Formalism.BasicNotions.Examples₂
