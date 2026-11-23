import Formalism.LocalRingCardinality.DataJet
import Formalism.LocalRingCardinality.SpanPowerMembership.PlacesOverNcardOfSplitInj
import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds
import Formalism.LocalRingCardinality.SpanPowerMembership.UnitsPowSurjective
import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsTameGen

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open Formalism.BasicNotions NumberField IsDedekindDomain Polynomial

attribute [local instance] Classical.propDecidable

def jetToy (R : Ranks) (H : Host R) : ThetaJet R H where
  Sit := Empty
  loc := fun i => i.elim
  l_inert := fun i => i.elim
  jOf := fun i => i.elim
  j_mem := fun i => i.elim
  N0_eq := fun i => i.elim
  N1_eq_exponentN1 := fun i => i.elim
  Sit1 := Empty
  loc1 := fun i => i.elim
  l_inert1 := fun i => i.elim
  j1Of := fun i => i.elim
  firstJetIndex_mem_range := fun i => i.elim
  firstJet_lowerRank_eq := fun i => i.elim
  firstJet_upperRank_eq := fun i => i.elim

section Series

variable (r g : ℕ)

def lab0 : (ZMod g)[X] := (X + C 1) ^ r

theorem labelPolynomial_monic_degree [Fact g.Prime] (hr : r ≠ 0) :
    (lab0 r g).Monic ∧ (lab0 r g).natDegree = r ∧ (lab0 r g).coeff 0 ≠ 0 := by
  refine ⟨(monic_X_add_C 1).pow r, ?_, ?_⟩
  · rw [lab0, (monic_X_add_C 1).natDegree_pow, natDegree_X_add_C, mul_one]
  · rw [coeff_zero_eq_eval_zero]; simp [lab0]

theorem labelPolynomial_not_squarefree [Fact g.Prime] (hr : 2 ≤ r) : ¬ Squarefree (lab0 r g) := fun h =>
  not_isUnit_X_add_C (1 : ZMod g) (h _ (by rw [← pow_two]; exact pow_dvd_pow _ hr))

def trivialSeriesIdempotent (f : (ZMod g)[X]) : MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) :=
  if f = lab0 r g then 1 else 0

theorem exists_sum_trivialSeriesIdempotent_eq_one [Fact g.Prime] (hr : r ≠ 0) : ∃ S : Finset (ZMod g)[X],
    (∀ f, f ∈ S ↔ f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0) ∧ ∑ f ∈ S, trivialSeriesIdempotent r g f = 1 := by
  have : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  have hfin : {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0}.Finite := by
    apply (Set.finite_range (fun a : Fin r → ZMod g => Formalism.CyclotomicNorms.monicOf a)).subset
    rintro f ⟨hm, hd, -⟩
    exact ⟨fun i => f.coeff i, Formalism.CyclotomicNorms.Sqf.monicOf_coeffs f hm hd⟩
  refine ⟨hfin.toFinset, fun f => by simp, ?_⟩
  unfold trivialSeriesIdempotent
  rw [Finset.sum_ite_eq']
  rw [if_pos]
  simpa using labelPolynomial_monic_degree r g hr

end Series

section Types

variable {R : Ranks} (H : Host R) (what₂ : Rows.Data R) (h : NHyp H what₂)

theorem r_ne_zero (R : Ranks) : R.r ≠ 0 := by
  have := R.two_le_m
  unfold Ranks.r
  omega

structure THyp {R : Ranks} (H : Host R) : Prop where
  cond : ∀ k, H.g k % (H.QS * H.q * H.d) = 1
  bb : Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1))
  jac : ∀ k, H.g k ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) (H.g k) = 1

def TameHyp {R : Ranks} (H : Host R) : Prop :=
  ∀ k, ∀ w ∈ placesOver H.E (H.g k), ∃ γ : Formalism.ConjugateSelfDual.G H.E AlgC,
    TameGenAt (ReciprocityTheory.Gal.placeOf AlgC w) γ

theorem tameHyp {R : Ranks} (H : Host R) : TameHyp H := fun k w hw =>
  Tame.exists_tameGen _ _ (H.g_prime k).ne_zero (by
    have := (ReciprocityTheory.Gal.isPlaceOver_placeOf AlgC w ((H.g k : ℕ) : 𝓞 H.E)).mpr hw
    simpa using this)

theorem discr_prime {R : Ranks} (H : Host R) (p : ℕ) (hp : p.Prime) (h : (p : ℤ) ∣ discr H.E) :
    p ∣ H.QS * H.q * H.d :=
  H.der.discr_primes.1 p hp h

theorem galK_comm {R : Ranks} (H : Host R) (σ τ : H.E ≃ₐ[H.K] H.E) : σ * τ = τ * σ := by
  have h : σ.restrictScalars ℚ * τ.restrictScalars ℚ = τ.restrictScalars ℚ * σ.restrictScalars ℚ := by
    apply (H.gal).injective
    rw [map_mul, map_mul, mul_comm]
  ext x
  exact AlgEquiv.congr_fun h x

theorem central_of_support {G : Type} [Group G] (z : MonoidAlgebra ℂ G)
    (h : ∀ g, g ≠ 1 → z.coeff g = 0) : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
  have : z = algebraMap ℂ (MonoidAlgebra ℂ G) (z.coeff 1) := by
    ext g
    by_cases hg : g = 1
    · subst hg; simp
    · rw [h g hg]; simp [Finsupp.single_eq_of_ne hg]
  rw [this]
  exact Subalgebra.algebraMap_mem _ _

set_option synthInstance.maxHeartbeats 400000 in

def toyNtypes (ht : THyp H) (htm : TameHyp H)
    (teichC : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ)
    (teichC_inj : ∀ k, ∀ x y : Fb (H.g k) (H.g_prime k), x ≠ 0 → y ≠ 0 →
      teichC k x = teichC k y → x = y)
    (iota : ∀ k (w : what₂.places.Pl), Fb (H.g k) (H.g_prime k) →*
      Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))
    (iota_inj : ∀ k w, ∀ x y : Fb (H.g k) (H.g_prime k), x ≠ 0 → y ≠ 0 →
      (orderOf x).Coprime (what₂.places.resChar w) → (orderOf y).Coprime (what₂.places.resChar w) →
      iota k w x = iota k w y → x = y) :
    NTypes (nautToy H what₂ h) where
  Mray := H.E
  Mray_gal := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  Mray_ab := galK_comm H
  Mray_unr := discr_prime H
  g_Mray := h.hg
  g_cond := ht.cond
  BB_disj := ht.bb
  bc := fun _ => {(R.r, 1)}
  bc_pos := fun _ p hp => by
    rw [Multiset.mem_singleton.mp hp]; exact ⟨Nat.pos_of_ne_zero (r_ne_zero R), one_pos⟩
  bc_sum := fun _ => by simp
  rbar := fun _ _ => 1
  rbar_open := fun _ _ => by simp
  tg := fun k v => (htm k _ ((nautToy H what₂ h).plGw_over k v)).choose
  tg_mem := fun k v => (htm k _ ((nautToy H what₂ h).plGw_over k v)).choose_spec.1
  tg_gen := fun k v => (htm k _ ((nautToy H what₂ h).plGw_over k v)).choose_spec
  inertiaCharpoly_type := fun k v L hL => by
    have : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    have h0 : Multiset.card (L : Multiset ℂˣ) = 0 := hL.symm.trans natDegree_one
    show (X - 1 : ℂ[X]) ^ Multiset.card (L : Multiset ℂˣ) =
      ((Formalism.CyclotomicNorms.rootsBar (1 : (ZMod (H.g k))[X])).map fun x => X - C (teichC k x)).prod
    rw [h0]
    simp [Formalism.CyclotomicNorms.rootsBar]
  chiT_tg := fun i => i.elim
  heckeLoc_gamma_places := fun i => i.elim
  iota := fun k _ w => iota k w
  iota_inj := fun k _ w => iota_inj k w
  teichC := teichC
  teichC_inj := teichC_inj
  eSer := fun k f => trivialSeriesIdempotent R.r (H.g k) f
  eSer_idem := fun k f => by unfold trivialSeriesIdempotent; split_ifs <;> simp
  eSer_central := fun k f a => by unfold trivialSeriesIdempotent; split_ifs <;> simp
  eSer_orth := fun k f f' hff => by
    unfold trivialSeriesIdempotent
    split_ifs with h1 h2
    · exact absurd (h1.trans h2.symm) hff
    all_goals simp
  eSer_zero := fun k f hf => by
    have : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    unfold trivialSeriesIdempotent
    rw [if_neg]
    rintro rfl
    exact hf (labelPolynomial_monic_degree R.r (H.g k) (r_ne_zero R))
  eSer_sum := fun k => by
    have : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    exact exists_sum_trivialSeriesIdempotent_eq_one R.r (H.g k) (r_ne_zero R)
  cenAmb := fun μ => (Representation.trivial ℂ _ _).asAlgebraHom.comp (Subalgebra.val _)
  cenMt := fun μ j => (Representation.trivial ℂ _ _).asAlgebraHom.comp (Subalgebra.val _)
  Par := Empty
  labPar := fun _ σ => σ.elim
  labPar_monic := fun _ σ => σ.elim
  locPar := fun σ => σ.elim
  locPar_dim := fun σ => σ.elim
  labPar_def := fun _ σ => σ.elim
  MtPar := fun _ _ σ => σ.elim
  AmbPar := fun _ σ => σ.elim

theorem exampleNewtypes_idempotent_zero (ht htm teichC teichC_inj iota iota_inj) (g) :
    (toyNtypes H what₂ h ht htm teichC teichC_inj iota iota_inj).e0.coeff g = 0 := by
  have : Fact (H.g 0).Prime := ⟨H.g_prime 0⟩
  refine finsum_eq_zero_of_forall_eq_zero fun a => ?_
  split_ifs with hg
  · have hf : 0 < R.f := by unfold Ranks.f Ranks.n; positivity
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨0, (⟨0, hf⟩ : Fin R.f)⟩) ?_
    show (trivialSeriesIdempotent _ _ _).coeff _ = 0
    unfold trivialSeriesIdempotent
    rw [if_neg]
    · rfl
    · intro e
      have h2 : 2 ≤ R.r := by have := R.m_add_three_le_k; unfold Ranks.r; omega
      exact labelPolynomial_not_squarefree R.r (H.g 0) h2 (e ▸ (hg 0).1.2.1 (⟨0, hf⟩ : Fin R.f))
  · rfl

theorem toyNtypes_E0Tie [∀ μ, Subsingleton (what₂.Amb μ)] [∀ μ j, Subsingleton (what₂.Mt μ j)]
    (ht htm teichC teichC_inj iota iota_inj) :
    (toyNtypes H what₂ h ht htm teichC teichC_inj iota iota_inj).IdempotentMatchesAction :=
  ⟨fun _ => LinearMap.ext fun _ => Subsingleton.elim _ _,
    fun _ _ => LinearMap.ext fun _ => Subsingleton.elim _ _⟩

def ntypesT (ht : THyp H) (htm : TameHyp H) : NTypes (nautToy H what₂ h) :=
  toyNtypes H what₂ h ht htm
    (fun k => @teichToC (H.g k) ⟨H.g_prime k⟩)
    (fun k _ _ _ _ e => @teichToC_injective (H.g k) ⟨H.g_prime k⟩ _ _ e)
    (fun k w => @teichIota (H.g k) (what₂.places.resChar w) ⟨H.g_prime k⟩ ⟨what₂.places.resChar_prime w⟩)
    (fun k w => @teichIota_inj (H.g k) (what₂.places.resChar w) ⟨H.g_prime k⟩
      ⟨what₂.places.resChar_prime w⟩)

theorem ntypesT_E0Tie [∀ μ, Subsingleton (what₂.Amb μ)] [∀ μ j, Subsingleton (what₂.Mt μ j)]
    (ht htm) : (ntypesT H what₂ h ht htm).IdempotentMatchesAction := toyNtypes_E0Tie H what₂ h _ _ _ _ _ _

theorem newtypes_idempotent_zero (ht htm) (g) : (ntypesT H what₂ h ht htm).e0.coeff g = 0 :=
  exampleNewtypes_idempotent_zero H what₂ h _ _ _ _ _ _ g

end Types

section Theta

variable {R : Ranks} (H : Host R) {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  (LL0 : IntermediateField ℚ what₂.LL) (h : NHyp H what₂)

set_option synthInstance.maxHeartbeats 400000 in

def nthToy : NTh R H what₂ LL0 (ndToy H what₂ h) (ntwToy H LL0 h) (nexpToy H LL0 h) where
  iC := fun i => i.elim
  iC_int := fun i => i.elim
  aL := fun i => i.elim
  aL_g := fun i => i.elim
  aL_off := fun i => i.elim
  Pt := fun i => i.elim
  ev := fun i => i.elim
  ev_smul := fun i => i.elim
  ev_inj := fun i => i.elim
  Lt := fun i => i.elim
  acgLt := fun i => i.elim
  modLt := fun i => i.elim
  freeLt := fun i => i.elim
  finLt := fun i => i.elim
  Let := fun i => i.elim
  finLet := fun i => i.elim
  Harm := fun i => i.elim
  thV := fun i => i.elim
  datPhi := fun i => i.elim
  datP := fun i => i.elim
  recDet := fun i => i.elim
  Ctr := fun i => i.elim
  ctrC := fun i => i.elim
  Harm_def := fun i => i.elim
  thV_add := fun i => i.elim
  thV_smul := fun i => i.elim
  thV_addP := fun i => i.elim
  thV_smulP := fun i => i.elim
  actK_one := fun i => i.elim
  actK_mul := fun i => i.elim
  recDet_act := fun i => i.elim
  recDetq_act := fun i => i.elim
  hkIdx := fun i => i.elim
  finHk := fun i => i.elim
  hkMove := fun i => i.elim
  hkU := fun i => i.elim
  hk_ev := fun i => i.elim
  MaximalUnramifiedExtension := fun i => i.elim
  FmUr := fun i => i.elim
  FmUr_smul := fun i => i.elim
  FmUr_span := fun i => i.elim
  Bsup_def := fun i => i.elim
  Kq := fun i => i.elim
  grpKq := fun i => i.elim
  actK := fun i => i.elim
  recDetq := fun i => i.elim
  recDetq_mem := fun i => i.elim

end Theta

end Formalism.BasicNotions.Examples₂
