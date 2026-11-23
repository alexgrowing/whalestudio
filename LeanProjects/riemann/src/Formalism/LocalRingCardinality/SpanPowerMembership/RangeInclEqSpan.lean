import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Formalism.LocalRingCardinality.SpanPowerMembership.BasisOfBasisF

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

def scalAct {Γ : Type} [Group Γ] (K V : Type) [Field K] [AddCommGroup V] [Module K V] (ψ : Γ →* Kˣ) :
    Γ →* (V ≃ₗ[K] V) := (DistribMulAction.toModuleAut K V).comp ψ

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂}

set_option synthInstance.maxHeartbeats 400000 in

structure NzIn (C : TwCore R H what₂ LL0 N) : Type 1 where
  eA : ∀ i, Bool → MonoidAlgebra (FractionRing (C.O i)) (G0g N)
  eL : G0g N → LL0
  eA_def : ∀ i b (g : G0g N), (eA i b).coeff g =
    IsFractionRing.map (A := C.O0 i) (B := C.O i) (K := FractionRing (C.O0 i))
      (L := FractionRing (C.O i)) (C.O_inj i) ((if b then C.emb0 i else C.emb0b i) (eL g))
  eA_idem : ∀ i b, eA i b * eA i b = eA i b
  eA_central : ∀ i b x, eA i b * x = x * eA i b
  Psi : ∀ i, G0g N →* (FractionRing (C.O i))ˣ
  hPsi : ∀ i b (V : Type) [AddCommGroup V] [Module (FractionRing (C.O i)) V],
    MonoidAlgebra.lift (FractionRing (C.O i)) (Module.End (FractionRing (C.O i)) V) (G0g N)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (scalAct _ V (Psi i))) (eA i b) = 1
  ix : ℕ → Type
  [ixF : ∀ j, Fintype (ix j)]
  [ixD : ∀ j, DecidableEq (ix j)]
  ix_out : ∀ j, Nonempty (ix j) → 1 ≤ j ∧ j ≤ R.m
  ixM : ℕ → Type
  [ixMF : ∀ j, Fintype (ixM j)]
  [ixMD : ∀ j, DecidableEq (ixM j)]
  rM : ∀ j, ix j → ixM j

attribute [instance] NzIn.ixF NzIn.ixD NzIn.ixMF NzIn.ixMD

namespace TwCore

variable (C : TwCore R H what₂ LL0 N) (I : NzIn C)

def SigN : Type := {p : Fin (R.m + 1) × Bool // 1 ≤ p.1.1 ∧ Nonempty (I.ix p.1.1)}

instance : Finite (SigN C I) := inferInstanceAs (Finite {p : Fin (R.m + 1) × Bool // _})

theorem tmul_single_ne (A K : Type) [CommRing A] [Field K] [Algebra A K] (ι : Type) [Fintype ι] [DecidableEq ι]
    (a : ι) : (1 : K) ⊗ₜ[A] (Pi.single a 1 : ι → A) ≠ 0 := by
  intro h
  have h1 := congrFun (congrArg (TensorProduct.piRight A K K (fun _ : ι => A)) h) a
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, map_zero] at h1
  have h2 := congrArg (TensorProduct.rid A K) (show (1 : K) ⊗ₜ[A] (Pi.single a 1 : ι → A) a = 0 from h1)
  rw [Pi.single_eq_same, TensorProduct.rid_tmul, map_zero, one_smul] at h2
  exact one_ne_zero h2

theorem nonempty_of_ne {ι V : Type} [Zero V] {x : ι → V} (hx : x ≠ 0) : Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  exact hx (Subsingleton.elim _ _)

theorem eq_one_of_smul {K V : Type} [Field K] [AddCommGroup V] [Module K V] {x : V} (hx : x ≠ 0) {c : K}
    (h : x = c • x) : (1 : K) = c := by
  have h2 : (1 - c) • x = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hx)

open Classical in
set_option synthInstance.maxHeartbeats 400000 in

abbrev toTwN [hL : IsEmpty N.Loc] : NTw R H what₂ LL0 N where
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
  Sig _ := SigN C I
  finSig _ := Fintype.ofFinite _
  jS _ s := s.1.1.1
  jS_range _ s := ⟨s.2.1, Nat.lt_succ_iff.mp s.1.1.2⟩
  side _ s := s.1.2
  rhoS _ _ := 1
  rhoS_cont _ _ := continuous_const
  hEig _ _ _ _ := 1
  S0 i := (placesOver_finite H.E (C.l i) (C.lPrime i).out.ne_zero).toFinset ∪
    (placesOver_finite H.E (H.g 0) (H.g_prime 0).ne_zero).toFinset ∪
    (placesOver_finite H.E (H.g 1) (H.g_prime 1).ne_zero).toFinset ∪ C.pD i
  twistExcludedPlaces_contains_residueChar i v hv := by simp [hv]
  placesOver_subset_exceptional i k v hv := by fin_cases k <;> simp_all
  primes_subset_exceptional i := Finset.subset_union_right
  B i j _ := I.ix j → C.O i
  Theta _ _ _ := ⊤
  ThetaPsi _ _ _ _ _ _ := ⊤
  ThetaPsi_one _ _ _ _ := (Submodule.baseChange_top _).symm
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

def incl (A K : Type) [CommRing A] [CommRing K] [Algebra A K] (ι : Type) : (ι → A) →ₗ[A] (ι → K) :=
  (Algebra.linearMap A K).compLeft ι

theorem mem_range_incl {A K : Type} [CommRing A] [CommRing K] [Algebra A K] {ι : Type} (f : ι → K) :
    f ∈ LinearMap.range (incl A K ι) ↔ ∀ y, f y ∈ (algebraMap A K).range := by
  constructor
  · rintro ⟨g, rfl⟩ y
    exact ⟨g y, rfl⟩
  · intro h
    choose g hg using h
    exact ⟨g, funext hg⟩

theorem single_mem_incl {A K : Type} [CommRing A] [CommRing K] [Algebra A K] {ι : Type} [DecidableEq ι] (a : ι) :
    (Pi.single a 1 : ι → K) ∈ LinearMap.range (incl A K ι) :=
  ⟨Pi.single a 1, funext fun y => by
    show algebraMap A K ((Pi.single a 1 : ι → A) y) = _
    by_cases h : y = a
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]⟩

theorem range_incl_eq_span (A K : Type) [CommRing A] [CommRing K] [Algebra A K] (ι : Type) [Fintype ι] [DecidableEq ι] :
    LinearMap.range (incl A K ι) = Submodule.span A (Set.range fun a : ι => (Pi.single a 1 : ι → K)) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    have e : incl A K ι g = ∑ a, g a • (Pi.single a 1 : ι → K) := by
      funext y
      rw [Finset.sum_apply, Finset.sum_eq_single y]
      · show algebraMap A K (g y) = g y • (Pi.single y 1 : ι → K) y
        rw [Pi.single_eq_same, Algebra.smul_def, mul_one]
      · intro b _ hb
        show g b • (Pi.single b 1 : ι → K) y = 0
        rw [Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
      · intro h; exact absurd (Finset.mem_univ y) h
    rw [e]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact single_mem_incl a

theorem span_incl_top (A K : Type) [CommRing A] [Field K] [Algebra A K] (ι : Type) [Fintype ι] [DecidableEq ι] :
    Submodule.span K (LinearMap.range (incl A K ι) : Set (ι → K)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun K ι).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨a, rfl⟩
  rw [Pi.basisFun_apply]
  exact single_mem_incl a

instance (i k) : Algebra.IsIntegral (C.O i) (C.Ok i k) :=
  haveI := C.Ok_fin i k
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in

abbrev toExpN : NExp R H what₂ LL0 N (C.toTwN I) where
  Fm (i : C.Tw) j _ := I.ix j → FractionRing (C.O i)
  actG (i : C.Tw) j _ := scalAct _ _ (I.Psi i)
  U := ⊥
  psiU _ _ := 1
  eAlg := I.eA
  eLL0 := I.eL
  eAlg_def := I.eA_def
  eAlg_idem := I.eA_idem
  eAlg_central := I.eA_central
  Bsup (i : C.Tw) j _ := LinearMap.range (incl (C.O i) (FractionRing (C.O i)) (I.ix j))
  Dat _ j _ := I.ix j
  th (i : C.Tw) j _ (d : I.ix j) := (Pi.single d 1 : I.ix j → FractionRing (C.O i))
  lev _ _ _ _ := ∅
  thPsi (i : C.Tw) j _ k _ _ (d : I.ix j) := {(1 : C.Ok i k) ⊗ₜ[C.O i] (Pi.single d 1 : I.ix j → FractionRing (C.O i))}
  thPsi_one _ _ _ _ _ := rfl
  thU (i : C.Tw) j _ _ _ (d : I.ix j) := (Pi.single d 1 : I.ix j → FractionRing (C.O i)) ⊗ₜ[C.O i] 1
  twPsi (i : C.Tw) j _ k _ := TensorProduct.mk (C.O i) (C.Ok i k) (I.ix j → FractionRing (C.O i)) 1
  twPsi_one _ _ _ _ _ := rfl
  twDel (i : C.Tw) j _ _ _ := (TensorProduct.mk (C.O i) (I.ix j → FractionRing (C.O i)) _).flip 1
  delU _ _ _ := 1
  delU_unr := by intros; rfl
  delU_l := by intros; rfl
  delU_anti _ _ _ _ _ _ := by simp
  delU_open _ _ _ := by simp [MonoidHom.ker_one]
  delU_res := by intros; rfl
  delU_conj _ _ _ _ _ _ _ _ := ⟨1, fun _ => by simp⟩
  MtV (i : C.Tw) j _ k _ _ := I.ixM j → FractionRing (C.Ok i k)
  MtLat (i : C.Tw) j _ k _ _ := LinearMap.range (incl (C.Ok i k) (FractionRing (C.Ok i k)) (I.ixM j))
  MtLat_fg (i : C.Tw) j _ k _ _ := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  MtLat_span (i : C.Tw) j _ k _ _ := span_incl_top _ _ _
  thP (i : C.Tw) j _ k _ _ := (NZ.vecE (C.O i) (C.Ok i k) (I.ix j) (C.Ok_inj i k)).toLinearMap ∘ₗ
    LinearMap.funLeft (C.Ok i k) (FractionRing (C.Ok i k)) (I.rM j)
  hkF _ _ _ _ _ := 1
  embB (i : C.Tw) j _ := incl (C.O i) (FractionRing (C.O i)) (I.ix j)
  embB_inj (i : C.Tw) j _ (x y : I.ix j → C.O i) h := funext fun a => IsFractionRing.injective (C.O i) (FractionRing (C.O i)) (congrFun h a)
  eH _ _ _ := 1
  eH_idem _ _ _ := mul_one _

open Classical in
set_option synthInstance.maxHeartbeats 400000 in

def toThN : NTh R H what₂ LL0 N (C.toTwN I) (C.toExpN I) where
  iC := C.iC
  iC_int := C.iC_int
  aL (i : C.Tw) := if ∃ k, C.l i = H.g k then 1 else 0
  aL_g (i : C.Tw) k h := if_pos ⟨k, h⟩
  aL_off (i : C.Tw) h := if_neg fun ⟨k, hk⟩ => h k hk
  Pt _ j := I.ix j
  ev (i : C.Tw) j _ :=
    { toFun := fun (f : I.ix j → FractionRing (C.O i)) y => C.iC i (f y)
      map_zero' := funext fun _ => map_zero _
      map_add' := fun (f g : I.ix j → FractionRing (C.O i)) => funext fun _ => map_add _ _ _ }
  ev_smul (i : C.Tw) j _ a (f : I.ix j → FractionRing (C.O i)) y := map_mul (C.iC i) a (f y)
  ev_inj (i : C.Tw) j _ (f g : I.ix j → FractionRing (C.O i)) h := funext fun y => (C.iC i).injective (congrFun h y)
  Lt _ j := I.ix j → 𝓞 H.E
  Let _ _ := Empty
  Harm _ _ := Set.univ
  Ctr _ _ := Empty
  ctrC _ _ κ := κ.elim
  Harm_def _ _ _ := ⟨fun _ κ => κ.elim, fun _ => trivial⟩
  thV (i : C.Tw) j (φ : (I.ix j → 𝓞 H.E) → FractionRing (C.O i)) (P : MvPolynomial Empty (C.O i)) (y : I.ix j) :=
    C.iC i (φ (Pi.single y 1)) *
    C.iC i (algebraMap (C.O i) (FractionRing (C.O i)) (MvPolynomial.constantCoeff P))
  thV_add (i : C.Tw) j (φ φ' : (I.ix j → 𝓞 H.E) → FractionRing (C.O i)) P y := by
    show C.iC i (φ _ + φ' _) * _ = _
    rw [map_add, add_mul]
  thV_smul (i : C.Tw) j a (φ : (I.ix j → 𝓞 H.E) → FractionRing (C.O i)) P y := by
    show C.iC i (a * φ _) * _ = _
    rw [map_mul, mul_assoc]
  thV_addP (i : C.Tw) j φ (P P' : MvPolynomial Empty (C.O i)) y := by
    show _ * C.iC i (algebraMap _ _ (MvPolynomial.constantCoeff (P + P'))) = _
    rw [map_add, map_add, map_add, mul_add]
  thV_smulP (i : C.Tw) j (c : C.O i) φ (P : MvPolynomial Empty (C.O i)) y := by
    show _ * C.iC i (algebraMap _ _ (MvPolynomial.constantCoeff (c • P))) = _
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.constantCoeff_C, map_mul, map_mul]
    ring
  datPhi (i : C.Tw) j _ (d : I.ix j) (z : I.ix j → 𝓞 H.E) := if z = Pi.single d 1 then (1 : FractionRing (C.O i)) else 0
  datP _ _ _ _ := 1
  recDet _ _ _ := 1
  Kq _ _ _ := PUnit
  actK _ _ _ _ y := y
  actK_one _ _ _ _ := rfl
  actK_mul _ _ _ _ _ _ := rfl
  recDetq _ _ _ _ := 1
  recDetq_mem _ _ _ _ := one_mem _
  recDet_act := by intros; rfl
  recDetq_act := by intros; rfl
  hkIdx _ _ _ _ := Unit
  hkMove _ _ _ _ _ y := y
  hkU _ _ _ _ _ _ _ := 1
  hk_ev (i : C.Tw) j b k P _ _ _ _ (f : I.ix j → FractionRing (C.O i)) y := by
    rw [Finset.univ_unique, Finset.sum_singleton, one_mul]
    rfl
  MaximalUnramifiedExtension _ := ⊤
  FmUr _ _ _ := ⊤
  FmUr_smul := by intros; trivial
  FmUr_span _ _ _ := eq_top_iff.mpr fun x _ => Submodule.subset_span trivial
  Bsup_def (i : C.Tw) j _ := by
    have e : {f : I.ix j → FractionRing (C.O i) | f ∈ (⊤ : AddSubgroup _) ∧ ∀ y, ‖C.iC i (f y)‖ ≤ 1} =
        (LinearMap.range (incl (C.O i) (FractionRing (C.O i)) (I.ix j)) : Set _) := by
      ext f
      simp only [Set.mem_setOf_eq, AddSubgroup.mem_top, true_and, SetLike.mem_coe, mem_range_incl, C.iC_int]
    exact (Submodule.span_eq _).symm.trans (congrArg _ e.symm)

end TwCore

end Formalism.BasicNotions.Examples₂
