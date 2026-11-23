import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCompatiblePullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInhab
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsGoodStatementStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyReindexedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicElementHomogRelationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ImplicitRootAnalyticStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogRelationRatioReindexStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

open MvPolynomial GroundTheory.Heights₂.Heights.Inter
open scoped Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Chg.DegBlock

variable {K₀ K : Type} [Fintype K₀] [Fintype K] {J₀ : K₀ → Type} {J : K → Type} [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)]

theorem isMultiHomog_mul' {f g : MRing J₀} {a b : K₀ → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  have h1 := hf m1 hm1 k
  have h2 := hg m2 hm2 k
  simp [Finset.sum_add_distrib, h1, h2]

theorem isMultiHomog_rename' {κ : K₀ → K} {v : (Σ k, J₀ k) → (Σ k, J k)} (hv : IsBlockMap κ v) {f : MRing J₀}
    {a : K₀ → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (rename v f : MRing J) (Function.extend κ a 0) := by
  intro m hm k'
  rw [support_rename_of_injective hv.2.1] at hm
  obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
  by_cases hk : k' ∈ Set.range κ
  · obtain ⟨k, rfl⟩ := hk
    rw [hv.1.extend_apply, ← hf m0 hm0 k]
    have hex : ∀ i' : J (κ k), ∃ i : J₀ k, v ⟨k, i⟩ = ⟨κ k, i'⟩ := by
      intro i'
      obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
      have h1 : κ p.1 = κ k := by rw [← hv.2.2.1 p, hp]
      obtain ⟨k₁, i⟩ := p
      obtain rfl : k₁ = k := hv.1 h1
      exact ⟨i, hp⟩
    choose g hg using hex
    have hb : Function.Bijective g := by
      constructor
      · intro a b hab
        have : (⟨κ k, a⟩ : Σ k, J k) = ⟨κ k, b⟩ := by rw [← hg a, ← hg b, hab]
        exact eq_of_heq (Sigma.mk.inj this).2
      · intro i
        have hq : ∃ i', v ⟨k, i⟩ = ⟨κ k, i'⟩ := by
          have h1 := hv.2.2.1 ⟨k, i⟩
          generalize v ⟨k, i⟩ = q at h1
          obtain ⟨q1, q2⟩ := q
          simp only at h1
          subst h1
          exact ⟨q2, rfl⟩
        obtain ⟨i', hi'⟩ := hq
        refine ⟨i', ?_⟩
        have h2 : v ⟨k, g i'⟩ = v ⟨k, i⟩ := by rw [hg i', hi']
        exact eq_of_heq (Sigma.mk.inj (hv.2.1 h2)).2
    calc ∑ i', (Finsupp.mapDomain v m0) ⟨κ k, i'⟩ = ∑ i', m0 ⟨k, g i'⟩ := by
          refine Finset.sum_congr rfl fun i' _ => ?_
          rw [← hg i', Finsupp.mapDomain_apply hv.2.1]
      _ = ∑ i, m0 ⟨k, i⟩ := hb.sum_comp fun i => m0 ⟨k, i⟩
  · rw [Function.extend_apply' _ _ _ (by simpa using hk)]
    refine Finset.sum_eq_zero fun i' _ => ?_
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨p, hp⟩
    exact hk ⟨p.1, by rw [← hv.2.2.1 p, hp]⟩

theorem eval_map_rename' (zt : (Σ k, J k) → ℂ) (v : (Σ k, J₀ k) → (Σ k, J k)) (s : MRing J₀) :
    eval zt (map (Int.castRingHom ℂ) (rename v s : MRing J)) = eval (fun p => zt (v p)) (map (Int.castRingHom ℂ) s) := by
  rw [map_rename, eval_rename]
  rfl

theorem imageZ_eq {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (i : Ω₀ →+* Ω) {y₀ : (Σ k, J₀ k) → Ω₀}
    {y : (Σ k, J k) → Ω} {bk : K₀ → K} (bx : ∀ k, J₀ k ≃ J (bk k)) (hbk : Function.Injective bk)
    (hy : ∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) :
    imageZ (blkV bk bx) (mCoordIdeal y) = mCoordIdeal y₀ := by
  refine le_antisymm ?_ (mCoordIdeal_le_imageZ i bx hy)
  intro f hf
  let Φ : MvPolynomial K₀ Ω₀ →+* MvPolynomial K Ω :=
    (rename bk : MvPolynomial K₀ Ω →ₐ[Ω] MvPolynomial K Ω).toRingHom.comp (MvPolynomial.map i)
  have hΦ : Function.Injective Φ :=
    (rename_injective bk hbk).comp (MvPolynomial.map_injective i i.injective)
  have key : ∀ f : MRing J₀, mConeMap y (rename (blkV bk bx) f) = Φ (mConeMap y₀ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap, Φ]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp =>
      obtain ⟨k, a⟩ := n
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, Φ, blkV, hy]
  have h0 : mConeMap y (rename (blkV bk bx) f) = 0 := hf
  rw [key] at h0
  exact hΦ (h0.trans (map_zero Φ).symm)

theorem not_mem_mcPts_top {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] (z : (Σ k, J k) → ℂ) :
    z ∉ mcPts (⊤ : Ideal (MRing J)) := by
  intro h
  have := h.2 1 trivial
  simp at this

theorem sameOrbit_trans' {K : Type} {J : K → Type} {a b c : (Σ k, J k) → ℂ} (h1 : SameOrbit a b) (h2 : SameOrbit b c) :
    SameOrbit a c := by
  obtain ⟨s, hs, rfl⟩ := h1
  obtain ⟨t, ht, rfl⟩ := h2
  exact ⟨fun k => s k * t k, fun k => mul_ne_zero (hs k) (ht k), by funext p; ring⟩

theorem sameOrbit_symm' {K : Type} {J : K → Type} {a b : (Σ k, J k) → ℂ} (h : SameOrbit a b) : SameOrbit b a := by
  obtain ⟨s, hs, rfl⟩ := h
  refine ⟨fun k => (s k)⁻¹, fun k => inv_ne_zero (hs k), ?_⟩
  funext p
  exact (inv_mul_cancel_left₀ (hs p.1) _).symm

theorem sameOrbit_restr {bk : K₀ → K} (bx : ∀ k, J₀ k ≃ J (bk k)) {a b : (Σ k, J k) → ℂ} (h : SameOrbit a b) :
    SameOrbit (fun p => a (blkV bk bx p)) (fun p => b (blkV bk bx p)) := by
  obtain ⟨s, hs, rfl⟩ := h
  exact ⟨fun k => s (bk k), fun k => hs _, rfl⟩

theorem holoMap_id' {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) : HoloMap A A (id : X → X) :=
  ⟨continuous_id, fun j k => A.holo j k⟩

theorem isMultiHomog_one' : IsMultiHomog (1 : MRing J₀) (0 : K₀ → ℕ) := by
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  simp [hm]

theorem isMultiHomog_prod' {X : Type} (s : Finset X) {f : X → MRing J₀} {a : X → K₀ → ℕ}
    (h : ∀ x ∈ s, IsMultiHomog (f x) (a x)) : IsMultiHomog (∏ x ∈ s, f x) (∑ x ∈ s, a x) := by
  induction s using Finset.induction_on with
  | empty => simpa using isMultiHomog_one'
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact isMultiHomog_mul' (h x (Finset.mem_insert_self x s))
      (ih fun u hu => h u (Finset.mem_insert_of_mem hu))

theorem exists_local_section {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀)
    (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (d : ℕ)
    (hy : ∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) (hprime : (mCoordIdeal y₀).IsPrime) (hB₀ : Birational y₀)
    (hfin : letI := i.toAlgebra; Module.finrank Ω₀ Ω = d) (hd : 0 < d) :
    ∃ (G : MRing J₀) (a : K₀ → ℕ), IsMultiHomog G a ∧ G ∉ mCoordIdeal y₀ ∧
      ∀ z ∈ mcPts (mCoordIdeal y), ∀ w₀ ∈ mcPts (mCoordIdeal y₀), SameOrbit (fun p => z (blkV bk bx p)) w₀ →
        eval w₀ (map (Int.castRingHom ℂ) G) ≠ 0 →
        ∃ (V : Set ((Σ k, J₀ k) → ℂ)) (V' : Set ((Σ k, J k) → ℂ)) (f : ((Σ k, J₀ k) → ℂ) → (Σ k, J k) → ℂ),
          IsOpen V ∧ w₀ ∈ V ∧ IsOpen V' ∧ z ∈ V' ∧ AnalyticOnNhd ℂ f V ∧
            ∀ z'' ∈ V' ∩ mcPts (mCoordIdeal y), ∀ w ∈ V ∩ mcPts (mCoordIdeal y₀),
              SameOrbit (fun p => z'' (blkV bk bx p)) w → SameOrbit (f w) z'' := by
  have halg : ∀ α : Ω, (letI := i.toAlgebra; IsAlgebraic Ω₀ α) := by
    letI := i.toAlgebra
    haveI : Module.Finite Ω₀ Ω := Module.finite_of_finrank_pos (by rw [hfin]; exact hd)
    exact fun α => Algebra.IsAlgebraic.isAlgebraic α
  have hdata := fun q r : Σ k, J k => GlobalTheory.T.algebraic_element_homog_relation K₀ J₀ Ω₀ Ω y₀ i (y q / y r) hB₀ (halg _)
  choose n c a G b hc hG hGn hsum hsimple using hdata
  refine ⟨∏ x : (Σ k, J k) × (Σ k, J k), G x.1 x.2, ∑ x : (Σ k, J k) × (Σ k, J k), b x.1 x.2,
    isMultiHomog_prod' _ fun x _ => hG x.1 x.2, ?_, ?_⟩
  · intro hm
    obtain ⟨x, -, hx⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hprime)).1 hm
    exact hGn _ _ hx
  intro z hz w₀ hw₀ hr h0
  have hGw : ∀ q r, eval w₀ (map (Int.castRingHom ℂ) (G q r)) ≠ 0 := by
    intro q r h
    apply h0
    rw [map_prod, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ (q, r)) h
  choose rr hrr using hz.1
  let r : ∀ k, Σ k, J k := fun k => ⟨k, rr k⟩
  have hyr : ∀ k, y (r k) ≠ 0 := by
    intro k h
    apply hrr k
    have hm : (X (r k) : MRing J) ∈ mCoordIdeal y := by
      show mConeMap y (X (r k)) = 0
      simp [mConeMap, h]
    simpa using hz.2 _ hm
  have hroot : ∀ q : Σ k, J k, ∃ (V : Set ((Σ k, J₀ k) → ℂ)) (W : Set ℂ) (g : ((Σ k, J₀ k) → ℂ) → ℂ),
      IsOpen V ∧ w₀ ∈ V ∧ IsOpen W ∧ z q / z (r q.1) ∈ W ∧ AnalyticOnNhd ℂ g V ∧
        ∀ w ∈ V, ∀ τ ∈ W, ∑ j ∈ Finset.range (n q (r q.1) + 1),
          eval w (map (Int.castRingHom ℂ) (c q (r q.1) j)) * τ ^ j = 0 → τ = g w := by
    intro q
    have h1 := GlobalTheory.T.homog_relation_ratio_reindex K₀ K J₀ J Ω₀ Ω y₀ y bk bx i q (r q.1) (n q (r q.1)) (c q (r q.1)) (a q (r q.1)) hy rfl
      (hyr _) (hc _ _) (hsum _ _) z hz (hrr _) w₀ hr
    exact GlobalTheory.T.implicit_root_analytic _ (n q (r q.1)) (fun j w => eval w (map (Int.castRingHom ℂ) (c q (r q.1) j))) w₀ _
      (fun j => AnalyticOnNhd.eval_mvPolynomial _ _ (Set.mem_univ _)) h1
      (hsimple _ _ w₀ hw₀ (hGw _ _) _ h1)
  choose V W g hVo hV hWo hW hga huniq using hroot
  refine ⟨⋂ q, V q, {z'' | ∀ q : Σ k, J k, z'' (r q.1) ≠ 0 ∧ z'' q / z'' (r q.1) ∈ W q}, fun w q => g q w,
    isOpen_iInter_of_finite hVo, Set.mem_iInter.2 hV, ?_, fun q => ⟨hrr _, hW q⟩, ?_, ?_⟩
  · rw [Set.setOf_forall]
    refine isOpen_iInter_of_finite fun q => ?_
    have hc1 : Continuous fun z'' : (Σ k, J k) → ℂ => z'' (r q.1) := continuous_apply _
    have hc2 : Continuous fun z'' : (Σ k, J k) → ℂ => z'' q := continuous_apply _
    have ho : IsOpen {z'' : (Σ k, J k) → ℂ | z'' (r q.1) ≠ 0} := isOpen_ne_fun hc1 continuous_const
    exact (ContinuousOn.isOpen_inter_preimage
      (hc2.continuousOn.div hc1.continuousOn fun _ h => h) ho (hWo q))
  · intro w hw
    have : ∀ q, AnalyticAt ℂ (g q) w := fun q => hga q w (Set.mem_iInter.1 hw q)
    exact AnalyticAt.pi this
  · rintro z'' ⟨hz1, hz2⟩ w ⟨hw1, -⟩ hR
    refine ⟨fun k => (z'' (r k))⁻¹, fun k => inv_ne_zero (hz1 (r k)).1, ?_⟩
    funext q
    have h1 := GlobalTheory.T.homog_relation_ratio_reindex K₀ K J₀ J Ω₀ Ω y₀ y bk bx i q (r q.1) (n q (r q.1)) (c q (r q.1)) (a q (r q.1)) hy rfl
      (hyr _) (hc _ _) (hsum _ _) z'' hz2 (hz1 q).1 w hR
    have h2 := huniq q w (Set.mem_iInter.1 hw1 q) _ (hz1 q).2 h1
    show g q w = (z'' (r q.1))⁻¹ * z'' q
    rw [← h2, div_eq_inv_mul]

theorem exists_count {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀)
    (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (D d : ℕ)
    (hbk : Function.Injective bk) (hy : ∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩))
    (hA₀ : IsArithVar (mCoordIdeal y₀) (D + 1)) (hA : IsArithVar (mCoordIdeal y) (D + 1))
    (hB₀ : Birational y₀) (hB : Birational y) (hfin : letI := i.toAlgebra; Module.finrank Ω₀ Ω = d) (hd : 0 < d) :
    ∃ (G : MRing J₀) (a : K₀ → ℕ), IsMultiHomog G a ∧ G ∉ mCoordIdeal y₀ ∧
      ∀ w ∈ mcPts (mCoordIdeal y₀), eval w (map (Int.castRingHom ℂ) G) ≠ 0 →
        (ptsOverPt (mCoordIdeal y) (blkV bk bx) w).ncard = d := by
  have himg := imageZ_eq i bx hbk hy
  obtain ⟨Gf, ch, hch, hf⟩ := GlobalTheory.T.arith_variety_reindexed K₀ K J₀ J Ω₀ Ω y₀ y bk bx i D d hbk hy hA₀ hA hB₀ hB hfin hd
  obtain ⟨G, a, hG, hGn, hc⟩ := GlobalTheory.T.generic_points_good_statement K₀ J₀ K J bk (blkV bk bx) (mCoordIdeal y) D Gf ch
    (isBlockMap_blkV bx hbk) hA (by rw [himg]; exact hA₀) hch
  rw [himg] at hGn hc
  exact ⟨G, a, hG, hGn, fun w hw h0 => (hc w hw h0).trans hf⟩

theorem isDegreeOff_of_block : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (D d : ℕ) (R₀ : AnLogRes (mCoordIdeal y₀) ⊤ D) (R : AnLogRes (mCoordIdeal y) ⊤ D) (h : R.X → R₀.X), Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → IsArithVar (mCoordIdeal y₀) (D + 1) → IsArithVar (mCoordIdeal y) (D + 1) → Birational y₀ → Birational y → HoloMap R.A R₀.A h → (∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (blkV bk bx p))) → (letI := i.toAlgebra; Module.finrank Ω₀ Ω = d) → 0 < d → ∃ br : Set R₀.X, IsDegreeOff R₀.A R.A h d br := by
  intro K₀ K _ _ J₀ J _ _ Ω₀ Ω _ _ _ y₀ y bk bx i D d R₀ R h hbk hy hA₀ hA hB₀ hB hh hlift hfin hd
  have hv : IsBlockMap bk (blkV bk bx) := isBlockMap_blkV bx hbk
  have hprime : (mCoordIdeal y₀).IsPrime := hA₀.2.1.1
  have himg := imageZ_eq i bx hbk hy
  obtain ⟨G₁, a₁, hG₁, hG₁n, hcount⟩ := exists_count y₀ y bk bx i D d hbk hy hA₀ hA hB₀ hB hfin hd
  obtain ⟨G₂, a₂, hG₂, hG₂n, hloc⟩ := exists_local_section y₀ y bk bx i d hy hprime hB₀ hfin hd
  have hGn : G₁ * G₂ ∉ mCoordIdeal y₀ := fun hm => (hprime.mem_or_mem hm).elim hG₁n hG₂n
  have hGh : IsMultiHomog (G₁ * G₂) (a₁ + a₂) := isMultiHomog_mul' hG₁ hG₂
  have hev : ∀ w : (Σ k, J₀ k) → ℂ, eval w (map (Int.castRingHom ℂ) (G₁ * G₂)) ≠ 0 →
      eval w (map (Int.castRingHom ℂ) G₁) ≠ 0 ∧ eval w (map (Int.castRingHom ℂ) G₂) ≠ 0 := by
    intro w hw
    simp only [map_mul] at hw
    exact ⟨fun h => hw (by rw [h]; simp), fun h => hw (by rw [h]; simp)⟩
  have hrn : rename (blkV bk bx) (G₁ * G₂) ∉ mCoordIdeal y := fun hm =>
    hGn (himg ▸ (show G₁ * G₂ ∈ imageZ (blkV bk bx) (mCoordIdeal y) from hm))
  refine ⟨_, GlobalTheory.T.log_resolution_compatible_pullback K₀ J₀ K J (mCoordIdeal y₀) ⊤ (mCoordIdeal y) ⊤ D R₀.X R₀.A R₀ id R h
    (fun z w => SameOrbit (fun p => z (blkV bk bx p)) w) (G₁ * G₂) (rename (blkV bk bx) (G₁ * G₂)) (a₁ + a₂)
    (Function.extend bk (a₁ + a₂) 0) d rfl hA₀ hA (holoMap_id' R₀.A) (isDegreeOff_id R₀.A) hh hGh hGn
    (isMultiHomog_rename' hv hGh) hrn
    (fun z z₁ w w₁ hr h1 h2 => sameOrbit_trans' (sameOrbit_restr bx h1)
      (sameOrbit_trans' hr (sameOrbit_symm' h2))) ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro x x₀ e
    have e' : x₀ = h x := e
    subst e'
    exact sameOrbit_symm' (hlift x)
  · intro x x₀ hr
    exact R₀.inj x₀ (h x) (not_mem_mcPts_top _) (sameOrbit_trans' (sameOrbit_symm' hr) (sameOrbit_symm' (hlift x)))
  · intro w hw h0
    exact hcount w hw (hev w h0).1
  · intro z hz hzJ
    exact absurd hzJ (not_mem_mcPts_top z)
  · intro z hz w hw hr h0
    rw [eval_map_rename']
    obtain ⟨c, hc, e⟩ := hr
    rw [e, ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_homog _ _ hGh, h0, mul_zero]
  · intro z hz w₀ hw₀ hr h0
    exact hloc z hz w₀ hw₀ hr (hev w₀ h0).2

end GlobalTheory.CompanionTheory.Ar.Chg.DegBlock
