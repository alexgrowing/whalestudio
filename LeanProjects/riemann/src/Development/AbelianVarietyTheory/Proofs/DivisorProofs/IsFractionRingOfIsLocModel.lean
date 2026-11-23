import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.DominatesIffIsLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryEffectiveUpEtaleTowerNormalLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedOfIsEtaleTowerOverNormalLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientLastCoordinateEtaleTowerNormalLocaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleTowerTrBasisAppendCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceDiscKaehlerWedgePermNegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltOfKltRestrictStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivTransportsVarietyPairDataStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.SpecTower

theorem klt_comp_equiv {k L : Type} [Field k] [CharZero k] [Field L] (c : k →+* L) {m m' : ℕ}
    (σ : Fin m ≃ Fin m') (y : Fin m' → L) (R : Subring L) (D : L →₀ ℚ) :
    Klt c m R (dForm c (y ∘ σ)) D ↔ Klt c m' R (dForm c y) D := by
  obtain rfl : m = m' := by simpa using Fintype.card_congr σ
  have hs : dForm c (y ∘ σ) = Equiv.Perm.sign σ • dForm c y := by
    rw [dForm_eq, dForm_eq]
    exact (exteriorPower.ιMulti L m).map_perm (fun i => dFun c (y i)) σ
  have hne : dForm c (y ∘ σ) ≠ 0 ↔ dForm c y ≠ 0 := by
    rw [hs]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hd : ∀ E : Place c, E.disc (dForm c (y ∘ σ)) D = E.disc (dForm c y) D :=
    fun E => (GlobalTheory.T.dvrPlace_disc_kaehlerWedge_perm_neg c m y σ E D).1
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hne.1 h1, h2, fun E hE => hd E ▸ h3 E hE⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hne.2 h1, h2, fun E hE => (hd E).symm ▸ h3 E hE⟩

theorem effAt_comp_equiv {k L : Type} [Field k] [CharZero k] [Field L] (c : k →+* L) {m m' : ℕ}
    (σ : Fin m ≃ Fin m') (y : Fin m' → L) (R : Subring L) (D : L →₀ ℚ) :
    EffAt c m R (dForm c (y ∘ σ)) D ↔ EffAt c m' R (dForm c y) D := by
  obtain rfl : m = m' := by simpa using Fintype.card_congr σ
  have hs : dForm c (y ∘ σ) = Equiv.Perm.sign σ • dForm c y := by
    rw [dForm_eq, dForm_eq]
    exact (exteriorPower.ιMulti L m).map_perm (fun i => dFun c (y i)) σ
  have hne : dForm c (y ∘ σ) ≠ 0 ↔ dForm c y ≠ 0 := by
    rw [hs]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hd : ∀ E : Place c, E.disc (dForm c (y ∘ σ)) D = E.disc (dForm c y) D :=
    fun E => (GlobalTheory.T.dvrPlace_disc_kaehlerWedge_perm_neg c m y σ E D).1
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hne.1 h1, h2, fun E hE => hd E ▸ h3 E hE⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hne.2 h1, h2, fun E hE => (hd E).symm ▸ h3 E hE⟩

theorem exists_equiv_cons_last {α : Type} (r n : ℕ) (τ : Fin (r + 1) → α) (v : Fin n → α) :
    ∃ σ : Fin (r + n + 1) ≃ Fin (r + 1 + n),
      (Fin.cons (τ (Fin.last r)) (Fin.append (fun i => τ (Fin.castSucc i)) v) : Fin (r + n + 1) → α) =
        Fin.append τ v ∘ σ := by
  let s : Fin (r + n + 1) → Fin (r + 1 + n) := fun j =>
    ⟨if (j : ℕ) = 0 then r else if (j : ℕ) ≤ r then (j : ℕ) - 1 else j, by
      have := j.2; split_ifs <;> omega⟩
  have hs : Function.Injective s := by
    intro a b hab
    have := congrArg Fin.val hab
    simp only [s] at this
    ext
    split_ifs at this <;> omega
  have hb : Function.Bijective s :=
    (Fintype.bijective_iff_injective_and_card s).2 ⟨hs, by simp; omega⟩
  refine ⟨Equiv.ofBijective s hb, funext fun j => ?_⟩
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero, Function.comp_apply, Equiv.ofBijective_apply]
    have : s 0 = Fin.castAdd n (Fin.last r) := Fin.ext (by simp [s])
    rw [this, Fin.append_left]
  · simp only [Fin.cons_succ, Function.comp_apply, Equiv.ofBijective_apply]
    refine Fin.addCases (fun i => ?_) (fun m => ?_) j
    · rw [Fin.append_left]
      have : s (Fin.castAdd n i).succ = Fin.castAdd n (Fin.castSucc i) :=
        Fin.ext (by simp [s] <;> first | omega | (split_ifs <;> omega))
      rw [this, Fin.append_left]
    · rw [Fin.append_right]
      have : s (Fin.natAdd r m).succ = Fin.natAdd (r + 1) m :=
        Fin.ext (by simp [s] <;> first | omega | (split_ifs <;> omega))
      rw [this, Fin.append_right]

theorem mapDomain_nonneg {α β : Type} (v : α →₀ ℚ) (hv : ∀ a ∈ v.support, 0 ≤ v a) (f : α → β)
    (b : β) : 0 ≤ Finsupp.mapDomain f v b := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_nonneg fun a ha => ?_
  show 0 ≤ (Finsupp.single (f a) (v a)) b
  rw [Finsupp.single_apply]
  split_ifs
  · exact hv a ha
  · exact le_rfl

example (K : Type) [Field K] (R : Subring K) : Algebra R K := inferInstance
example (K : Type) [Field K] (R : Subring K) : FaithfulSMul R K := inferInstance
example (K : Type) [Field K] (R : Subring K) (a : R) : algebraMap R K a = (a : K) := rfl

end GlobalTheory.FieldPair.SpecTower

namespace GlobalTheory.FieldPair.SpecTower

theorem isFractionRing_of_isLocModel {k K : Type} [Field k] [Field K] {c : k →+* K}
    {R : Subring K} (h : IsLocModel c R) : IsFractionRing R K :=
  IsFractionRing.of_field R K fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h.frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, eq_div_of_mul_eq hb0 e⟩

theorem klt_tower_zero {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n : ℕ)
    (R : Subring K) (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin 0 → T) (x : Fin n → R)
    (φ : R →₀ ℚ) (θ : T →₀ ℚ) (h : IsEtTower cK R cL T ι ψ τ)
    (hx : TrBasis cK (fun i => (x i : K)))
    (hk : Klt cK n R (dForm cK (fun i => (x i : K)))
      (Finsupp.mapDomain (fun g : R => (g : K)) φ + Finsupp.mapDomain (fun g : T => ((ψ g : R) : K)) θ)) :
    Klt cL (0 + n) T (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))))
      (Finsupp.mapDomain (fun g : R => (ι g : L)) φ + Finsupp.mapDomain (fun g : T => (g : L)) θ) := by
  have hb := h.bijective_of_zero
  have hιψ : ∀ t, ι (ψ t) = t := fun t => hb.1 (by rw [h.retr])
  haveI := isFractionRing_of_isLocModel h.base
  haveI := isFractionRing_of_isLocModel h.top
  let e0 : R ≃+* T := (RingEquiv.ofBijective ψ hb).symm
  have he0 : ∀ a, e0 a = ι a := fun a =>
    (RingEquiv.ofBijective ψ hb).symm_apply_eq.2 (h.retr a).symm
  let e : K ≃+* L := IsFractionRing.ringEquivOfRingEquiv e0
  have he : ∀ a : R, e a = (ι a : L) := fun a => by
    have := IsFractionRing.ringEquivOfRingEquiv_algebraMap (K := K) (L := L) e0 a
    rw [he0] at this
    exact this
  have hc : ∀ a, e (cK a) = cL a := fun a => (he ⟨cK a, h.base.const_mem a⟩).trans (h.const a)
  have hmap : R.map e.toRingHom = T := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      have := he ⟨a, ha⟩
      change e a ∈ T
      rw [this]
      exact (ι _).2
    · intro hy
      refine ⟨(ψ ⟨y, hy⟩ : K), (ψ ⟨y, hy⟩).2, ?_⟩
      change e _ = y
      rw [he, hιψ]
  have key := ((GlobalTheory.T.ringEquiv_transports_varietyPair_data cK cL e hc n (fun i => (x i : K)) R _ hx).2.2.1).1 hk
  rw [hmap] at key
  have hx' : (⇑e ∘ fun i => (x i : K)) = fun i => (ι (x i) : L) := funext fun i => he (x i)
  have hD : Finsupp.mapDomain e (Finsupp.mapDomain (fun g : R => (g : K)) φ +
      Finsupp.mapDomain (fun g : T => ((ψ g : R) : K)) θ) =
      Finsupp.mapDomain (fun g : R => (ι g : L)) φ + Finsupp.mapDomain (fun g : T => (g : L)) θ := by
    rw [Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    congr 2
    · funext g; exact he g
    · funext g; simp only [Function.comp_apply]; rw [he, hιψ]
  rw [hx', hD] at key
  rw [Fin.append_left_nil _ _ rfl]
  exact (klt_comp_equiv cL (finCongr (Nat.zero_add n)) _ T _).2 key

end GlobalTheory.FieldPair.SpecTower

namespace GlobalTheory.FieldPair.SpecTower

theorem klt_of_tower (hP : GlobalTheory.Published.Principalisation) (r : ℕ) :
    ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n : ℕ) (R : Subring K)
      (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (φ : R →₀ ℚ)
      (θ : T →₀ ℚ),
    IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → (∀ g ∈ φ.support, g ≠ 0) →
    (∀ g ∈ θ.support, ψ g ≠ 0 ∧ 0 ≤ θ g) →
    EffAt cK n R (dForm cK (fun i => (x i : K))) (Finsupp.mapDomain (fun g : R => (g : K)) φ) →
    Klt cK n R (dForm cK (fun i => (x i : K)))
      (Finsupp.mapDomain (fun g : R => (g : K)) φ + Finsupp.mapDomain (fun g : T => ((ψ g : R) : K)) θ) →
    Klt cL (r + n) T (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))))
      (Finsupp.mapDomain (fun g : R => (ι g : L)) φ + Finsupp.mapDomain (fun g : T => (g : L)) θ) := by
  induction r with
  | zero =>
    intro K L _ _ cK cL n R T ι ψ τ x φ θ h hx _ _ _ hk
    exact klt_tower_zero cK cL n R T ι ψ τ x φ θ h hx hk
  | succ r ih =>
    classical
    intro K L _ _ cK cL n R T ι ψ τ x φ θ h hx hφ hθ hE hk
    obtain ⟨L', _, cL', T', π, ι', ψ', hπs, hker, hf0, h', hψπ, hπι, hcst⟩ :=
      GlobalTheory.T.exists_quotient_lastCoordinate_etaleTowerNormalLocal cK cL r R T ι ψ τ h
    have hψπ' : ∀ t, ψ' (π t) = ψ t := fun t => RingHom.congr_fun hψπ t
    have hπι' : ∀ a, π (ι a) = ι' a := fun a => RingHom.congr_fun hπι a

    let w : Fin (r + n) → T := Fin.append (fun i => τ (Fin.castSucc i)) (fun i => ι (x i))
    let θr : T →₀ ℚ := Finsupp.mapDomain ι φ + θ
    let ψr : T →+* L' := T'.subtype.comp π
    have hrange : ψr.range = T' := by
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        exact (π t).2
      · intro hy
        obtain ⟨t, ht⟩ := hπs ⟨y, hy⟩
        exact ⟨t, by simp [ψr, ht]⟩
    have hkerr : RingHom.ker ψr = Ideal.span {τ (Fin.last r)} := by
      rw [← hker]
      ext t
      simp only [RingHom.mem_ker, ψr, RingHom.comp_apply, Subring.coe_subtype]
      exact ⟨fun e => Subtype.ext e, fun e => by rw [e]; rfl⟩

    let θ' : T' →₀ ℚ := Finsupp.mapDomain π θ
    have hθ' : ∀ g ∈ θ'.support, ψ' g ≠ 0 ∧ 0 ≤ θ' g := by
      intro g hg
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
      refine ⟨by rw [hψπ']; exact (hθ t ht).1, ?_⟩
      exact mapDomain_nonneg θ (fun a ha => (hθ a ha).2) π _
    have hkR : Klt cK n R (dForm cK (fun i => (x i : K)))
        (Finsupp.mapDomain (fun g : R => (g : K)) φ +
          Finsupp.mapDomain (fun g : T' => ((ψ' g : R) : K)) θ') := by
      have e : Finsupp.mapDomain (fun g : T' => ((ψ' g : R) : K)) θ' =
          Finsupp.mapDomain (fun g : T => ((ψ g : R) : K)) θ := by
        rw [← Finsupp.mapDomain_comp]
        congr 1
        funext t
        simp only [Function.comp_apply, hψπ']
      rw [e]
      exact hk
    have ih' := ih cK cL' n R T' ι' ψ' (fun i => π (τ (Fin.castSucc i))) x φ θ' h' hx hφ hθ' hE hkR
    have hw : (fun i => ψr (w i)) =
        Fin.append (fun i => (π (τ (Fin.castSucc i)) : L')) (fun i => (ι' (x i) : L')) := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp [w, ψr, Fin.append_left]
      · simp [w, ψr, Fin.append_right, hπι']
    have hDr : Finsupp.mapDomain ψr θr = Finsupp.mapDomain (fun g : R => (ι' g : L')) φ +
        Finsupp.mapDomain (fun g : T' => (g : L')) θ' := by
      simp only [θr, θ', Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp]
      congr 2
      funext g
      simp [ψr, hπι']
    have hklt' : Klt cL' (r + n) ψr.range (dForm cL' (fun i => ψr (w i)))
        (Finsupp.mapDomain ψr θr) := by
      rw [hrange, hw, hDr]
      exact ih'
    have hloc : IsLocModel cL' ψr.range := hrange ▸ h'.top
    have htr : TrBasis cL' (fun i => ψr (w i)) :=
      hw ▸ GlobalTheory.T.etaleTower_trBasis_append_coordinates cK cL' n r R T' ι' ψ' _ x h' hx
    have hsupp : ∀ g ∈ θr.support, ψr g ≠ 0 := by
      intro g hg
      rcases Finset.mem_union.1 (Finsupp.support_add hg) with hg | hg
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
        intro h0
        have h1 : π (ι a) = 0 := Subtype.ext h0
        apply hφ a ha
        rw [← h.retr a, ← hψπ', h1, map_zero]
      · intro h0
        have h1 : π g = 0 := Subtype.ext h0
        apply (hθ g hg).1
        rw [← hψπ', h1, map_zero]

    obtain ⟨σ, hσ⟩ := exists_equiv_cons_last r n (fun i => (τ i : L)) (fun i => (ι (x i) : L))
    have hcons : (Fin.cons ((τ (Fin.last r) : T) : L) (fun i => (w i : L)) : Fin (r + n + 1) → L) =
        Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)) ∘ σ := by
      rw [← hσ]
      congr 1
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp [w, Fin.append_left]
      · simp [w, Fin.append_right]
    have hDL : Finsupp.mapDomain (fun g : T => (g : L)) θr =
        Finsupp.mapDomain (fun g : R => (ι g : L)) φ + Finsupp.mapDomain (fun g : T => (g : L)) θ := by
      simp only [θr, Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp]
      rfl
    have hθL : ∀ g ∈ θ.support, (g : L) ≠ 0 ∧ 0 ≤ θ g := fun g hg =>
      ⟨fun e => (hθ g hg).1 (by rw [show g = 0 from Subtype.ext e, map_zero]), (hθ g hg).2⟩
    have hEff := GlobalTheory.T.boundaryEffective_up_etale_tower_normal_local cK cL n (r + 1) R T ι ψ τ x φ θ h hx hφ hθL hE
    have hEff' : EffAt cL (r + n + 1) T
        (dForm cL (Fin.cons ((τ (Fin.last r) : T) : L) (fun i => (w i : L)) : Fin (r + n + 1) → L))
        (Finsupp.mapDomain (fun g : T => (g : L)) θr) := by
      rw [hcons, hDL]
      exact (effAt_comp_equiv cL σ _ T _).2 hEff
    have hres := GlobalTheory.T.klt_of_klt_restrict_alt hP cL cL' (r + n) T h.top ψr (τ (Fin.last r)) w θr
      (GlobalTheory.T.isIntegrallyClosed_of_isEtaleTowerOverNormalLocal cK cL (r + 1) R T ι ψ τ h) hcst hkerr hf0 hloc htr hsupp hEff' hklt'
    rw [hcons, hDL] at hres
    exact (klt_comp_equiv cL σ _ T _).1 hres

end GlobalTheory.FieldPair.SpecTower

theorem GlobalTheory.FieldPair.klt_of_isEtTower : GlobalTheory.Published.Principalisation →
  ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (φ : R →₀ ℚ) (θ : T →₀ ℚ),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → (∀ g ∈ φ.support, g ≠ 0) →
  (∀ g ∈ θ.support, ψ g ≠ 0 ∧ 0 ≤ θ g) →
  EffAt cK n R (dForm cK (fun i => (x i : K))) (Finsupp.mapDomain (fun g : R => (g : K)) φ) →
  Klt cK n R (dForm cK (fun i => (x i : K)))
    (Finsupp.mapDomain (fun g : R => (g : K)) φ + Finsupp.mapDomain (fun g : T => ((ψ g : R) : K)) θ) →
  Klt cL (r + n) T (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))))
    (Finsupp.mapDomain (fun g : R => (ι g : L)) φ + Finsupp.mapDomain (fun g : T => (g : L)) θ) :=
  fun hP _ _ _ _ cK cL n r => GlobalTheory.FieldPair.SpecTower.klt_of_tower hP r cK cL n
