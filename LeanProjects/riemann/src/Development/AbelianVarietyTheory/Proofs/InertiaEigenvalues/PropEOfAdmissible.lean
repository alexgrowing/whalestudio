import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ToNatAddValMul

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.ToricFactor

section Algebra

open MvPolynomial

theorem mem_span_of_vanish {σ O O' : Type} [Finite σ] [CommRing O] [CommRing O'] [IsDomain O'] (f : O →+* O')
    (hf : Function.Injective f) (b : σ → MvPolynomial σ O) (S : σ → Finset O') (hS : ∀ i, (S i).Nonempty)
    (hb : ∀ i, map f (b i) = ∏ r ∈ S i, (X i - C r)) (h : MvPolynomial σ O)
    (hev : ∀ x : σ → O', (∀ i, x i ∈ S i) → eval₂ f x h = 0) : h ∈ Ideal.span (Set.range b) := by
  classical
  let _ : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  let m : MonomialOrder σ := MonomialOrder.degLex
  have hdeg : ∀ i, m.degree (b i) = Finsupp.single i (S i).card := by
    intro i
    have h1 : m.degree (map f (b i)) = m.degree (b i) := by
      unfold MonomialOrder.degree
      rw [support_map_of_injective _ hf]
    rw [← h1, hb, m.degree_prod_of_regular]
    · simp [Finset.sum_congr rfl (fun r _ ↦ m.degree_X_sub_C i r)]
    · intro r _
      rw [m.monic_X_sub_C]
      exact isRegular_one
  have hlc : ∀ i, m.leadingCoeff (b i) = 1 := by
    intro i
    apply hf
    have h1 : m.degree (map f (b i)) = m.degree (b i) := by
      unfold MonomialOrder.degree
      rw [support_map_of_injective _ hf]
    have h2 : m.Monic (map f (b i)) := by
      rw [hb]
      exact MonomialOrder.Monic.prod (fun r _ ↦ m.monic_X_sub_C i r)
    have h3 := h2.leadingCoeff_eq_one
    unfold MonomialOrder.leadingCoeff at h3 ⊢
    rw [h1, coeff_map] at h3
    rw [h3, map_one]
  obtain ⟨g, r, hfg, -, hr⟩ := m.div (b := b) (fun i => by rw [hlc]; exact isUnit_one) h
  have hmem : Finsupp.linearCombination (MvPolynomial σ O) b g ∈ Ideal.span (Set.range b) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  suffices r = 0 by rw [hfg, this, add_zero]; exact hmem
  apply map_injective f hf
  rw [map_zero]
  apply eq_zero_of_eval_zero_at_prod_finset _ S
  · intro i
    rw [degreeOf_eq_sup, support_map_of_injective _ hf, Finset.sup_lt_iff (by simp [hS i])]
    intro c hc
    have := hr c hc i
    rw [hdeg, Finsupp.single_le_iff] at this
    exact not_le.1 this
  · intro x hx
    have h0 := hev x hx
    rw [hfg, eval₂_add, Finsupp.linearCombination_apply, Finsupp.sum, eval₂_sum, Finset.sum_eq_zero, zero_add] at h0
    · rw [eval_map, h0]
    · intro i _
      rw [smul_eq_mul, eval₂_mul, ← eval_map f x (b i), hb, map_prod, Finset.prod_eq_zero (hx i), mul_zero]
      simp

theorem mem_span_of_vanish_roots {O O' : Type} [CommRing O] [CommRing O'] [IsDomain O'] [Algebra O O']
    (hf : Function.Injective (algebraMap O O')) {n : ℕ} (hn : 0 < n) {ζ : O'} (hζ : IsPrimitiveRoot ζ n) {R : ℕ}
    (h : MvPolynomial (Fin R ⊕ Fin R) O)
    (hev : ∀ u : Fin R ⊕ Fin R → O'ˣ, (∀ q, u q ^ n = 1) → (∀ a, u (.inr a) = 1) →
      aeval (fun q => ((u q : O'ˣ) : O') - 1) h = 0) :
    h ∈ Ideal.span (Set.range (fun i : Fin R => (X (Sum.inr i) : MvPolynomial (Fin R ⊕ Fin R) O)) ∪
      Set.range (fun i : Fin R => (1 + X (Sum.inl i)) ^ n - 1)) := by
  classical
  have := mem_span_of_vanish (algebraMap O O') hf
    (Sum.elim (fun i : Fin R => (1 + X (Sum.inl i) : MvPolynomial (Fin R ⊕ Fin R) O) ^ n - 1)
      (fun i : Fin R => X (Sum.inr i)))
    (Sum.elim (fun _ => (Polynomial.nthRootsFinset n (1 : O')).image (fun y => y - 1)) (fun _ => {0})) ?_ ?_ h ?_
  · rwa [Set.Sum.elim_range, Set.union_comm] at this
  · rintro (i | i)
    · exact Finset.Nonempty.image ⟨1, Polynomial.one_mem_nthRootsFinset hn⟩ _
    · simp
  · rintro (i | i)
    · have h1 := congrArg (Polynomial.aeval (1 + X (Sum.inl i) : MvPolynomial (Fin R ⊕ Fin R) O'))
        (Polynomial.X_pow_sub_one_eq_prod hn hζ)
      simp only [Sum.elim_inl]
      rw [Finset.prod_image (fun _ _ _ _ h => sub_left_injective h)]
      simp only [map_sub, map_pow, map_add, map_one, map_X, Polynomial.aeval_X, map_prod, Polynomial.aeval_C,
        algebraMap_eq] at h1 ⊢
      rw [h1]
      exact Finset.prod_congr rfl fun y _ => by ring
    · simp
  · intro x hx
    have hx1 : ∀ q, (x q + 1) ^ n = 1 := by
      rintro (i | i)
      · obtain ⟨y, hy, hy'⟩ := Finset.mem_image.1 (hx (.inl i))
        rw [← hy', sub_add_cancel]
        exact (Polynomial.mem_nthRootsFinset hn 1).1 hy
      · have : x (.inr i) = 0 := by simpa using hx (.inr i)
        simp [this]
    have := hev (fun q => Units.ofPowEqOne _ n (hx1 q) hn.ne') (fun q => Units.ext (by simpa using hx1 q))
      (fun a => Units.ext (by simpa using hx (.inr a)))
    simpa [aeval_def] using this

def eR {A : Type} [CommRing A] (Y Y' w : A) (q : ℕ) : A := (1 - Y * w) * (1 - Y' * w) + ((q : A) - 1) * w ^ 2

theorem map_eR {A B F : Type} [CommRing A] [CommRing B] [FunLike F A B] [RingHomClass F A B] (f : F) (Y Y' w : A) (q : ℕ) :
    f (eR Y Y' w q) = eR (f Y) (f Y') (f w) q := by
  simp [eR]

theorem eR_res {σ k : Type} [Field k] (a : σ) (x : kˣ) {n : ℕ} (hn : 0 < n) (hn0 : (n : k) = 0) :
    ∃ (u : MvPolynomial σ k) (e : ℕ), constantCoeff u ≠ 0 ∧ e ≤ 2 ∧
      (1 - C (x : k) * (1 + X a)) * (1 - C ((x⁻¹ : kˣ) : k) * (1 + X a) ^ (n - 1)) = u * X a ^ e := by
  by_cases hx : x = 1
  · subst hx
    refine ⟨∑ j ∈ Finset.range (n - 1), (1 + X a) ^ j, 2, ?_, le_rfl, ?_⟩
    · simp [Nat.cast_sub hn, hn0]
    · have := mul_geom_sum (1 + X a : MvPolynomial σ k) (n - 1)
      simp only [inv_one, Units.val_one, map_one, one_mul]
      linear_combination (-X a) * this
  · refine ⟨_, 0, ?_, by norm_num, by rw [pow_zero, mul_one]⟩
    have h1 : (1 : k) - x ≠ 0 := fun h => hx (Units.ext (sub_eq_zero.1 h).symm)
    have h2 : (1 : k) - (x⁻¹ : kˣ) ≠ 0 := fun h => hx (inv_eq_one.1 (Units.ext (sub_eq_zero.1 h).symm))
    simpa using ⟨h1, by simpa using h2⟩

def chi {A : Type} [CommGroup A] (n : ℕ) [NeZero n] (u : A) (hu : u ^ n = 1) : Multiplicative (ZMod n) →* A where
  toFun a := u ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hu]

end Algebra

section Conj

variable {R : Ranks} {H : Host R}

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  have h1 := H.conjE_apply H.φ₀ (H.conj x)
  have h2 := H.conjE_apply H.φ₀ x
  refine h1.trans ?_
  show starRingEnd ℂ (H.φ₀ (H.conj x)) = _
  rw [h2, Complex.conj_conj]

theorem exists_conj_int (x : 𝓞 H.E) : ∃ y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) :=
  ⟨⟨H.conj (x : H.E), (x.isIntegral_coe).map (H.conj.toAlgHom.restrictScalars ℤ)⟩, rfl⟩

theorem isConjPl_symm {P P' : PlE H} (h : IsConjPl H P P') : IsConjPl H P' P :=
  fun x y hy => (h y x (by rw [hy, conj_conj])).symm

theorem isConjPl_unique {P P' P'' : PlE H} (h : IsConjPl H P P') (h' : IsConjPl H P P'') : P' = P'' := by
  ext y
  obtain ⟨x, hx⟩ := exists_conj_int y
  have : (y : H.E) = H.conj (x : H.E) := by rw [hx, conj_conj]
  rw [← h x y this, h' x y this]

theorem exists_isConjPl (P : PlE H) : ∃ P', IsConjPl H P P' := by
  let c : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv
  have hc : ∀ x, ((c x : 𝓞 H.E) : H.E) = H.conj (x : H.E) := fun x => rfl
  refine ⟨HeightOneSpectrum.comap (c : 𝓞 H.E →+* 𝓞 H.E) c.surjective P, fun x y hy => ?_⟩
  have : c y = x := RingOfIntegers.ext (by rw [hc, hy, conj_conj])
  show _ ↔ c y ∈ P.asIdeal
  rw [this]

theorem ne_of_split {P P' : PlE H} (hs : IsSplitPl H P) (h : IsConjPl H P P') : P ≠ P' := by
  rintro rfl
  obtain ⟨x, hx, hx'⟩ := hs
  obtain ⟨y, hy⟩ := exists_conj_int x
  exact hx' y hy ((h x y hy).1 hx)

end Conj

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

theorem over_conj {P v v' : PlE D.host} (h : Over P v) (h' : IsConjPl D.host v v') : Over P v' := by
  rcases h with rfl | h
  · exact Or.inr h'
  · exact Or.inl (isConjPl_unique h' (isConjPl_symm h))

theorem over_over {P P' v : PlE D.host} (h : Over P v) (h' : Over P' v) : Over P P' := by
  rcases h' with rfl | h'
  · exact h
  · exact over_conj h (isConjPl_symm h')

variable {X}

theorem qOk_of_auxiliary_set {i : X.Tw} {M : ℕ} {ι : Type} {P : ι → PlE D.host} {d} (hA : SlopeTestRemainingChoices X i M ∅ P d) {T : ι → Prop}
    {Q : Finset (PlE D.host)} (hQ : ∀ v, v ∈ Q ↔ ∃ q, T q ∧ Over (P q) v) : QOk X i Q := by
  refine ⟨fun v hv => ?_, Finset.disjoint_left.2 fun v hv => ?_, fun v hv v' h => ?_⟩
  · obtain ⟨q, -, hq⟩ := (hQ v).1 hv
    exact (hA.1 q v hq).1
  · obtain ⟨q, -, hq⟩ := (hQ v).1 hv
    exact (hA.1 q v hq).2.2.2.1
  · obtain ⟨q, hT, hq⟩ := (hQ v).1 hv
    exact (hQ v').2 ⟨q, hT, over_conj hq h⟩

theorem hom_ext {i : X.Tw} {Q : Finset (PlE D.host)} {A : Type} [CommGroup A] {ψ ψ' : X.RCG i Q →* A}
    (h : ∀ g, ψ (X.art i Q g) = ψ' (X.art i Q g)) : ψ = ψ' := by
  ext x
  obtain ⟨g, rfl⟩ := X.art_surj i Q x
  exact h g

theorem res_art' {i : X.Tw} {Q Q' : Finset (PlE D.host)} (h : Q' ⊆ Q) (g : GE N) :
    X.res i Q Q' h (X.art i Q g) = X.art i Q' g :=
  DFunLike.congr_fun (X.res_art i Q Q' h) g

theorem thEval_remove (h10 : adm10 X) {i : X.Tw} (hi : X.NonzeroIndexPlace i) {M : ℕ} {ι : Type} [DecidableEq ι]
    {P : ι → PlE D.host} {d}
    (hA : SlopeTestRemainingChoices X i M ∅ P d) (lam : X.abelian₂ i) {s : ℤ} (hs : SOk X i lam s) (σ : ι → GE N)
    (hσ : ∀ q, IsFrob (N.plOm.1 (P q)) (normV (P q)) (σ q)) (k : ℕ) (T : ι → Prop) (Q₀ : Finset (PlE D.host))
    (hQ₀ : ∀ v, v ∈ Q₀ ↔ ∃ q, T q ∧ Over (P q) v) (ψ₀ : X.RCG i Q₀ →* (X.Ok i k)ˣ) (W : Finset ι) :
    (∀ q ∈ W, ¬ T q) → ∀ (Q : Finset (PlE D.host)), (∀ v, v ∈ Q ↔ ∃ q, (T q ∨ q ∈ W) ∧ Over (P q) v) →
      ∀ ψ : X.RCG i Q →* (X.Ok i k)ˣ, (∀ g, ψ (X.art i Q g) = ψ₀ (X.art i Q₀ g)) →
      thEval X i Q lam k ψ = (∏ q ∈ W,
        eq' (kMap X i k (algebraMap (X.O i) (FractionRing (X.O i)) (X.Xv i lam (P q))) *
                algebraMap (X.Ok i k) (FractionRing (X.Ok i k))
                  ((ψ₀ (X.art i Q₀ (σ q)) : (X.Ok i k)ˣ) : X.Ok i k))
              (((normV (P q) : ℕ) : FractionRing (X.Ok i k)) ^ (-s)) (normV (P q))) * thEval X i Q₀ lam k ψ₀ := by
  classical
  induction W using Finset.induction_on with
  | empty =>
    intro _ Q hQ ψ hψ
    obtain rfl : Q = Q₀ := by
      ext v
      simp [hQ, hQ₀]
    rw [hom_ext hψ]
    simp
  | insert q W hqW ih =>
    intro hW Q hQ ψ hψ
    obtain ⟨Pb, hPb⟩ := exists_isConjPl (P q)
    have hne : P q ≠ Pb := ne_of_split (hA.1 q _ (Or.inl rfl)).1 hPb
    have h1 : P q ∈ Q := (hQ _).2 ⟨q, Or.inr (Finset.mem_insert_self _ _), Or.inl rfl⟩
    have h2 : Pb ∈ Q := (hQ _).2 ⟨q, Or.inr (Finset.mem_insert_self _ _), Or.inr hPb⟩
    have hQ1 : ∀ v, v ∈ (Q.erase (P q)).erase Pb ↔ ∃ q', (T q' ∨ q' ∈ W) ∧ Over (P q') v := by
      intro v
      rw [Finset.mem_erase, Finset.mem_erase, hQ]
      constructor
      · rintro ⟨a, b, q', hq', ho⟩
        refine ⟨q', ?_, ho⟩
        rcases hq' with h | h
        · exact Or.inl h
        · rcases Finset.mem_insert.1 h with rfl | h
          · rcases ho with ho | ho
            · exact absurd ho b
            · exact absurd (isConjPl_unique ho hPb) a
          · exact Or.inr h
      · rintro ⟨q', hq', ho⟩
        have hqq : ¬ Over (P q) v := fun h => by
          obtain rfl := hA.2.1 _ _ (over_over h ho)
          rcases hq' with h | h
          · exact hW _ (Finset.mem_insert_self _ _) h
          · exact hqW h
        exact ⟨fun h => hqq (Or.inr (h ▸ hPb)), fun h => hqq (Or.inl h), q',
          hq'.imp id Finset.mem_insert_of_mem, ho⟩
    have hsub : Q₀ ⊆ (Q.erase (P q)).erase Pb := fun v hv => by
      obtain ⟨q', a, b⟩ := (hQ₀ v).1 hv
      exact (hQ1 v).2 ⟨q', Or.inl a, b⟩
    have e1 := h10 i hi Q (qOk_of_auxiliary_set hA hQ) lam s hs (P q) Pb h1 h2 hne hPb k
      (ψ₀.comp (X.res i _ Q₀ hsub)) (σ q) (hσ q)
    have e2 := ih (fun q' hq' => hW q' (Finset.mem_insert_of_mem hq')) _ hQ1 (ψ₀.comp (X.res i _ Q₀ hsub))
      (fun g => by rw [MonoidHom.comp_apply, res_art'])
    rw [e2, MonoidHom.comp_apply, res_art'] at e1
    rw [Finset.prod_insert hqW, mul_assoc, ← e1]
    congr 1
    apply hom_ext
    intro g
    rw [hψ, MonoidHom.comp_apply, MonoidHom.comp_apply, res_art', res_art']

theorem exists_char {i : X.Tw} {M : ℕ} {ι : Type} [Fintype ι] {P : ι → PlE D.host} {d}
    (hA : SlopeTestRemainingChoices X i M ∅ P d) {T : ι → Prop}
    {Q : Finset (PlE D.host)} (hQ : ∀ v, v ∈ Q ↔ ∃ q, T q ∧ Over (P q) v) {A : Type} [CommGroup A] (u : ι → A)
    (hu : ∀ q, u q ^ (X.l i ^ M) = 1) (hT : ∀ q, ¬ T q → u q = 1) :
    ∃ ψ : X.RCG i Q →* A, ∀ g, ψ (X.art i Q g) = ∏ q, u q ^ (Multiplicative.toAdd (d q g)).val := by
  haveI : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  have key : ∀ q, ∃ f : X.RCG i Q →* A, ∀ g, f (X.art i Q g) = u q ^ (Multiplicative.toAdd (d q g)).val := by
    intro q
    by_cases hq : T q
    · obtain ⟨h1, h2, -, h3, -⟩ := hA.2.2 q
      obtain ⟨f, hf⟩ := X.art_univ i Q (fun v hv h => by
          obtain ⟨q', -, ho⟩ := (hQ v).1 hv
          exact (hA.1 q' v ho).2.2.2.1 (X.twistExcludedPlaces_contains_residueChar i h)) (Multiplicative (ZMod (X.l i ^ M)))
        (fun x => ⟨M, by
          rw [← ofAdd_toAdd x, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]⟩)
        (d q) h1 h2 (fun v hv => h3 v fun ho => hv ((hQ v).2 ⟨q, hq, ho⟩))
      refine ⟨(chi _ (u q) (hu q)).comp f, fun g => ?_⟩
      rw [← hf]
      rfl
    · exact ⟨1, fun g => by simp [hT q hq]⟩
  choose f hf using key
  exact ⟨∏ q, f q, fun g => by simp [MonoidHom.finset_prod_apply, hf]⟩

theorem kMap_algebraMap (i : X.Tw) (k : ℕ) (y : X.O i) :
    kMap X i k (algebraMap (X.O i) (FractionRing (X.O i)) y) =
      algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (algebraMap (X.O i) (X.Ok i k) y) :=
  IsFractionRing.lift_algebraMap _ y

theorem exists_lift {N0 : X.Tw → ℕ} (h9 : adm9 X N0) {i : X.Tw} (hi : X.NonzeroIndexPlace i) (lam : X.abelian₂ i) {s : ℤ}
    (hs : SOk X i lam s) {Q : Finset (PlE D.host)} (hQ : QOk X i Q) {M : ℕ} {ι : Type} [Fintype ι]
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) :
    ∃ f : MvPolynomial ι (X.O i), ∀ (k : ℕ) (u : ι → (X.Ok i k)ˣ) (ψ' : X.RCG i Q →* (X.Ok i k)ˣ),
      (∀ g, ψ' (X.art i Q g) = ∏ q, u q ^ (Multiplicative.toAdd (d q g)).val) →
      algebraMap (X.Ok i k) (FractionRing (X.Ok i k))
          (MvPolynomial.aeval (fun q => ((u q : (X.Ok i k)ˣ) : X.Ok i k) - 1) f) =
        ((X.l i : ℕ) : FractionRing (X.Ok i k)) ^ N0 i * thEval X i Q lam k ψ' := by
  choose y hy using h9 i hi Q hQ lam s hs
  choose g hg using X.art_surj i Q
  refine ⟨∑ δ, MvPolynomial.C (y δ) * ∏ q, (1 + MvPolynomial.X q) ^ (Multiplicative.toAdd (d q (g δ))).val,
    fun k u ψ' h => ?_⟩
  rw [thEval, Finset.mul_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  have e := congrArg (kMap X i k) (hy δ)
  rw [kMap_algebraMap, map_mul, map_pow, map_natCast] at e
  have e2 := h (g δ)
  rw [hg] at e2
  rw [← mul_assoc, ← e, e2, ← map_mul]
  congr 1
  simp

theorem eq'_eq (i : X.Tw) (k : ℕ) (x : (X.O i)ˣ) (t : (X.Ok i k)ˣ) (w : X.O i) (q : ℕ) {s : ℤ} (hs : 0 ≤ s)
    (hw : w * (q : X.O i) ^ s.toNat = 1) :
    eq' (kMap X i k (algebraMap (X.O i) (FractionRing (X.O i)) x) *
        algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (t : X.Ok i k))
      (((q : ℕ) : FractionRing (X.Ok i k)) ^ (-s)) q =
    algebraMap (X.Ok i k) (FractionRing (X.Ok i k))
      (eR (algebraMap (X.O i) (X.Ok i k) x * t) (algebraMap (X.O i) (X.Ok i k) (x⁻¹ : (X.O i)ˣ) * (t⁻¹ : (X.Ok i k)ˣ))
        (algebraMap (X.O i) (X.Ok i k) w) q) := by
  have h1 : algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (algebraMap (X.O i) (X.Ok i k) w) =
      ((q : ℕ) : FractionRing (X.Ok i k)) ^ (-s) := by
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hs
    rw [zpow_neg, zpow_natCast]
    apply eq_inv_of_mul_eq_one_left
    have := congrArg (fun y => algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (algebraMap (X.O i) (X.Ok i k) y)) hw
    simpa using this
  rw [map_eR, h1, kMap_algebraMap, ← map_mul]
  unfold eq' eR
  congr 4
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, mul_mul_mul_comm, ← map_mul]
  simp

def resChar (i : X.Tw) (lam : X.abelian₂ i) : GE N →* (IsLocalRing.ResidueField (X.O i))ˣ :=
  (Units.map (IsLocalRing.residue (X.O i)).toMonoidHom).comp (X.lamG i lam)

theorem isOpen_ker_resChar (i : X.Tw) (lam : X.abelian₂ i) : IsOpen ((resChar i lam).ker : Set (GE N)) := by
  have h1 : IsOpen (IsLocalRing.maximalIdeal (X.O i) : Set (X.O i)) := by
    have := (isAdic_iff.1 (X.O_adic i)).1 1
    rwa [pow_one] at this
  have h2 := h1.preimage ((X.lamG_cont i lam).sub (continuous_const (y := (1 : X.O i))))
  convert h2 using 1
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, resChar, MonoidHom.comp_apply, Units.ext_iff,
    Pi.sub_apply]
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
  rfl

theorem resChar_ne_one {i : X.Tw} (lam : X.abelian₂ i) {z : GE N} (hz : IsTameInertiaElementAtTwistPrime X i z) : resChar i lam z ≠ 1 := by
  intro h1
  obtain ⟨v, hv, A, hA, hzA, hu, hU⟩ := hz
  obtain ⟨n, hn⟩ := X.lamG_pD i lam v hv A hA z hzA
  obtain ⟨m, hm, hzm⟩ := hU (X.delta i).ker (X.delta_open i) inferInstance
  let φ : (X.O0 i)ˣ →* (IsLocalRing.ResidueField (X.O i))ˣ :=
    (Units.map (IsLocalRing.residue (X.O i)).toMonoidHom).comp (Units.map (algebraMap (X.O0 i) (X.O i)).toMonoidHom)
  have e1 : φ (X.delta i z) ^ m = 1 := by
    rw [← map_pow, ← map_pow, (MonoidHom.mem_ker).1 hzm, map_one]
  have e2 : φ (X.delta i z) ^ (Ideal.absNorm v.asIdeal ^ n) = 1 := by
    have := congrArg (Units.map (IsLocalRing.residue (X.O i)).toMonoidHom) hn
    rw [map_pow, map_mul, map_inv, map_one] at this
    change (resChar i lam z * (φ _)⁻¹) ^ _ = 1 at this
    rw [h1, one_mul] at this
    split_ifs at this
    · simpa using this
    · simpa using this
  have e3 : φ (X.delta i z) = 1 := by
    have hc : Nat.Coprime m (Ideal.absNorm v.asIdeal ^ n) := (Nat.Coprime.coprime_mul_left_right hm).pow_right n
    have := pow_gcd_eq_one.2 ⟨e1, e2⟩
    rwa [hc, pow_one] at this
  have e4 := (hu.map (algebraMap (X.O0 i) (X.O i))).map (IsLocalRing.residue (X.O i))
  have e5 : IsLocalRing.residue (X.O i) (algebraMap (X.O0 i) (X.O i) (X.delta i z : (X.O0 i)ˣ)) = 1 :=
    congrArg Units.val e3
  simp [e5] at e4

theorem l_ne_zero (i : X.Tw) : ((X.l i : ℕ) : X.O i) ≠ 0 := by
  intro h
  have h0 : ((X.l i : ℕ) : X.O0 i) = 0 := X.O_inj i (by simpa using h)
  have h1 : X.emb0 i (X.l i : ℕ) = 0 := by
    have := congrArg (algebraMap (X.O0 i) (FractionRing (X.O0 i))) h0
    simpa using this
  rw [map_eq_zero, Nat.cast_eq_zero] at h1
  exact (X.lPrime i).out.ne_zero h1

theorem residue_pow_l (i : X.Tw) {M : ℕ} (hM : 1 ≤ M) :
    ((X.l i ^ M : ℕ) : IsLocalRing.ResidueField (X.O i)) = 0 := by
  have : ((X.l i : ℕ) : IsLocalRing.ResidueField (X.O i)) = 0 := by
    rw [← map_natCast (IsLocalRing.residue (X.O i)), IsLocalRing.residue_eq_zero_iff]
    exact X.O_l i
  rw [Nat.cast_pow, this, zero_pow (by omega)]

theorem residue_norm (i : X.Tw) {M : ℕ} (hM : 1 ≤ M) {q : ℕ} (hq : q % (2 * X.l i ^ M) = 1) :
    ((q : ℕ) : IsLocalRing.ResidueField (X.O i)) = 1 := by
  rw [← Nat.div_add_mod q (2 * X.l i ^ M), hq]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, residue_pow_l i hM]
  simp

theorem exists_w (i : X.Tw) {M : ℕ} (hM : 1 ≤ M) {q : ℕ} (hq : q % (2 * X.l i ^ M) = 1) (n : ℕ) :
    ∃ w : X.O i, w * (q : X.O i) ^ n = 1 ∧ IsLocalRing.residue (X.O i) w = 1 := by
  have h1 := residue_norm i hM hq
  have hu : IsUnit (q : X.O i) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast, h1]
    exact one_ne_zero
  obtain ⟨w, hw⟩ := (hu.pow n).exists_left_inv
  refine ⟨w, hw, ?_⟩
  have := congrArg (IsLocalRing.residue (X.O i)) hw
  simpa [h1] using this

open MvPolynomial in

theorem propE (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (N0 : X.Tw → ℕ)
    (h9 : adm9 X N0) (h10 : adm10 X) : PropE X N0 := by
  classical
  rintro i lam z hi ⟨s, hs⟩ hth hz
  have hs0 : 0 ≤ s := by have := hs.2.1; omega
  have hl := l_ne_zero (X := X) i
  have hQe : QOk X i ∅ := ⟨by simp, by simp, by simp⟩
  choose y hy using h9 i hi ∅ hQe lam s hs
  have hY : algebraMap (X.O i) (FractionRing (X.O i)) (∑ δ, y δ) =
      ((X.l i : ℕ) : FractionRing (X.O i)) ^ N0 i * ∑ δ, X.th i ∅ lam δ := by
    rw [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun δ _ => hy δ
  have hY0 : (∑ δ, y δ) ≠ 0 := by
    intro h
    rw [h, map_zero] at hY
    refine mul_ne_zero (pow_ne_zero _ ?_) hth hY.symm
    rw [← map_natCast (algebraMap (X.O i) (FractionRing (X.O i)))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hl
  refine ⟨(resChar i lam).ker, (IsDiscreteValuationRing.addVal (X.O i) (∑ δ, y δ)).toNat,
    isOpen_ker_resChar i lam, inferInstance, ?_, ?_⟩
  · have e := GlobalTheory.NormValExt.vK_eq (X.l i) hth (a := ∑ δ, y δ) (pow_ne_zero (N0 i) hl)
      (by rw [hY, map_pow, map_natCast, mul_comm])
    have hT : IsDiscreteValuationRing.addVal (X.O i) (X.l i : X.O i) ≠ ⊤ := by
      simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using hl
    have he : ((IsDiscreteValuationRing.addVal (X.O i) (X.l i : X.O i)).toNat : ℝ) ≠ 0 := by
      rw [Nat.cast_ne_zero, Ne, ENat.toNat_eq_zero]
      rintro (h | h)
      · exact (X.O_l i) (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
      · exact hT h
    have e2 : nval (X.O i) (X.l i) ((X.l i : X.O i) ^ N0 i) = N0 i := by
      unfold nval
      rw [IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul, ENat.toNat_mul, ENat.toNat_coe]
      push_cast
      field_simp
    rw [c0, e, e2, sub_add_cancel]
    rfl
  intro M R P d Q hM hA hSt hQ
  have hn1 : 1 < X.l i ^ M := Nat.one_lt_pow (by omega) (X.lPrime i).out.one_lt
  haveI : Fact (1 < X.l i ^ M) := ⟨hn1⟩
  choose σ hσ using fun q => exists_isFrob (N.plOm.2 (P q))
  have hx : ∀ q, X.Xv i lam (P q) = (X.lamG i lam (σ q) : (X.O i)ˣ) := fun q =>
    X.Xv_def i lam (P q) (hA.1 q _ (Or.inl rfl)).2.2.2.1 (σ q) (hσ q)
  have hnm : ∀ q, normV (P q) % (2 * X.l i ^ M) = 1 := fun q => (hA.1 q _ (Or.inl rfl)).2.2.2.2.2
  choose w hw hw1 using fun q => exists_w (X := X) i hM (hnm q) s.toNat
  let T : Fin R ⊕ Fin R → Prop := fun q => ∃ a, q = .inl a
  let Q₁ : Finset (PlE D.host) := Q.filter fun v => ∃ q, T q ∧ Over (P q) v
  have hQ₁ : ∀ v, v ∈ Q₁ ↔ ∃ q, T q ∧ Over (P q) v := fun v => by
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun ⟨q, a, b⟩ => ⟨(hQ v).2 ⟨q, b⟩, q, a, b⟩⟩
  have hQ' : ∀ v, v ∈ Q ↔ ∃ q, True ∧ Over (P q) v := fun v => by simpa using hQ v
  obtain ⟨f, hf⟩ := exists_lift h9 hi lam hs (qOk_of_auxiliary_set hA hQ') d
  obtain ⟨g, hg⟩ := exists_lift h9 hi lam hs (qOk_of_auxiliary_set hA hQ₁) d
  refine ⟨f, ⟨∏ a : Fin R, eR (C (X.lamG i lam (σ (.inr a)) : X.O i) * (1 + MvPolynomial.X (.inl a)))
      (C (((X.lamG i lam (σ (.inr a)))⁻¹ : (X.O i)ˣ) : X.O i) * (1 + MvPolynomial.X (.inl a)) ^ (X.l i ^ M - 1))
      (C (w (.inr a))) (normV (P (.inr a))), g, ?_, ?_, ?_⟩, fun k u ψ' _ h => hf k u ψ' h⟩
  · refine mem_span_of_vanish_roots (X.Ok_inj i M) (by omega) (X.zk_prim i M) _ fun u hu hu1 => ?_
    obtain ⟨ψ, hψ⟩ := exists_char hA hQ' u hu (fun q h => absurd trivial h)
    obtain ⟨ψ₁, hψ₁⟩ := exists_char hA hQ₁ u hu (by
      rintro (a | a) h
      · exact absurd ⟨a, rfl⟩ h
      · exact hu1 a)
    have e := thEval_remove h10 hi hA lam hs σ hσ M T Q₁ hQ₁ ψ₁ (Finset.univ.map Function.Embedding.inr)
      (by simp [T]) Q (fun v => by
        rw [hQ v]
        refine exists_congr fun q => ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
        rcases q with a | a
        · exact Or.inl ⟨a, rfl⟩
        · exact Or.inr (by simp)) ψ (fun g => by rw [hψ, hψ₁])
    have hv : ∀ a, ψ₁ (X.art i Q₁ (σ (.inr a))) = u (.inl a) := by
      intro a
      rw [hψ₁, Fintype.prod_sum_type]
      simp only [hu1, one_pow, Finset.prod_const_one, mul_one, hSt.2 a _ _ (hσ _), toAdd_ofAdd]
      rw [Finset.prod_eq_single a]
      · simp [ZMod.val_one]
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    apply IsFractionRing.injective (X.Ok i M) (FractionRing (X.Ok i M))
    rw [map_sub, map_mul, map_sub, map_mul, hf M u ψ hψ, hg M u ψ₁ hψ₁, e, map_zero, Finset.prod_map, map_prod,
      map_prod, sub_eq_zero, mul_left_comm]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [Function.Embedding.inr_apply]
    rw [hx, hv, eq'_eq i M _ _ _ _ hs0 (hw _), map_eR (aeval (R := X.O i) fun q => ((u q : (X.Ok i M)ˣ) : X.Ok i M) - 1)]
    have hinv : ((u (.inl a))⁻¹ : (X.Ok i M)ˣ) = u (.inl a) ^ (X.l i ^ M - 1) := by
      symm
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hu]
    rw [hinv]
    simp
  · have e := thEval_remove h10 hi hA lam hs σ hσ 0 (fun _ => False) ∅ (by simp) 1
      (Finset.univ.map Function.Embedding.inl) (by simp) Q₁ (fun v => by
        rw [hQ₁ v]
        simp [T, eq_comm]) 1 (fun g => rfl)
    have e1 := hg 0 1 1 (by simp)
    have e2 : thEval X i ∅ lam 0 1 = kMap X i 0 (∑ δ, X.th i ∅ lam δ) := by simp [thEval]
    have e3 := congrArg (kMap X i 0) hY
    rw [kMap_algebraMap, map_mul, map_pow, map_natCast] at e3
    have e4 : g.coeff 0 = (∏ a : Fin R, eR (X.lamG i lam (σ (.inl a)) : X.O i)
        (((X.lamG i lam (σ (.inl a)))⁻¹ : (X.O i)ˣ) : X.O i) (w (.inl a)) (normV (P (.inl a)))) * ∑ δ, y δ := by
      apply X.Ok_inj i 0
      apply IsFractionRing.injective (X.Ok i 0) (FractionRing (X.Ok i 0))
      rw [e, e2, mul_left_comm, ← e3, Finset.prod_map] at e1
      simp only [Pi.one_apply, Units.val_one, sub_self, aeval_zero'] at e1
      rw [map_mul, map_mul, map_prod, map_prod]
      refine e1.trans ?_
      congr 1
      refine Finset.prod_congr rfl fun a _ => ?_
      simp only [Function.Embedding.inl_apply]
      rw [hx, eq'_eq i 0 _ _ _ _ hs0 (hw _), map_eR (algebraMap (X.O i) (X.Ok i 0))]
      simp
    have hu : IsUnit (∏ a : Fin R, eR (X.lamG i lam (σ (.inl a)) : X.O i)
        (((X.lamG i lam (σ (.inl a)))⁻¹ : (X.O i)ˣ) : X.O i) (w (.inl a)) (normV (P (.inl a)))) := by
      refine IsUnit.prod_univ_iff.2 fun a => ?_
      obtain ⟨c, hc⟩ := hSt.1 a _ (hσ _)
      have h1 : resChar i lam (σ (.inl a)) ≠ 1 := by
        intro h
        rw [MonoidHom.mem_ker] at hc
        apply resChar_ne_one lam hz
        simpa [h] using hc
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_eR, hw1, eR, residue_norm i hM (hnm _)]
      simp only [mul_one, sub_self, zero_mul, add_zero]
      refine mul_ne_zero (fun h => h1 (Units.ext (sub_eq_zero.1 h).symm)) (fun h => h1 ?_)
      rw [← inv_eq_one, ← map_inv]
      apply Units.ext
      rw [← map_inv] at h
      exact (sub_eq_zero.1 h).symm
    rw [e4, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu, zero_add,
      ENat.coe_toNat]
    simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using hY0
  · choose u e hu he hue using fun a : Fin R => eR_res (Sum.inl a : Fin R ⊕ Fin R) (resChar i lam (σ (.inr a)))
      (n := X.l i ^ M) (by omega) (residue_pow_l i hM)
    refine ⟨∏ a, u a, e, ?_, he, ?_⟩
    · rw [← constantCoeff_eq, map_prod]
      exact Finset.prod_ne_zero_iff.2 fun a _ => hu a
    · convert Ideal.zero_mem _
      rw [sub_eq_zero, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      have hq : ((normV (P (.inr a)) : ℕ) : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField (X.O i))) = 1 := by
        rw [← map_natCast C, residue_norm i hM (hnm _), map_one]
      rw [← hue, map_eR, eR, hq]
      simp [hw1, resChar]

end GlobalTheory.ToricFactor

end
