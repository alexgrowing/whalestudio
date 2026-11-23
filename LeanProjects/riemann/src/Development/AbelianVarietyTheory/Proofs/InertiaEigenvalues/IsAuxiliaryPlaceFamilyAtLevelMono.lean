import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ToNatAddValMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelOrderExponentsSmallValuationDeterminaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTameInertiaElementAtAuxiliaryPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PropEOfAdmissibleStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.TwistChoice

section Places

variable {R : Ranks} {H : Host R}

theorem conj_conj (H : Host R) (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  have h1 := H.conjE_apply H.φ₀ (H.conj x)
  have h2 := H.conjE_apply H.φ₀ x
  refine h1.trans ?_
  show starRingEnd ℂ (H.φ₀ (H.conj x)) = _
  rw [h2, Complex.conj_conj]

theorem conj_int (H : Host R) (x : 𝓞 H.E) : ∃ y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) :=
  ⟨⟨H.conj (x : H.E), (x.isIntegral_coe).map (H.conj.toAlgHom.restrictScalars ℤ)⟩, rfl⟩

theorem isConjPl_symm {w w' : PlE H} (h : IsConjPl H w w') : IsConjPl H w' w :=
  fun x y hy => (h y x (by rw [hy, conj_conj])).symm

theorem isConjPl_unique {w w' w'' : PlE H} (h : IsConjPl H w w') (h' : IsConjPl H w w'') : w' = w'' := by
  apply HeightOneSpectrum.ext
  ext y
  obtain ⟨x, hx⟩ := conj_int H y
  have : (y : H.E) = H.conj (x : H.E) := by rw [hx, conj_conj]
  exact (h x y this).symm.trans (h' x y this)

end Places

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem over_of_over {P P' v : PlE D.host} (h : Over P v) (h' : Over P' v) : Over P P' := by
  rcases h with rfl | h <;> rcases h' with rfl | h'
  · exact Or.inl rfl
  · exact Or.inr (isConjPl_symm h')
  · exact Or.inr h
  · exact Or.inl (isConjPl_unique (isConjPl_symm h') (isConjPl_symm h))

theorem exists_isQ {ι : Type} [Fintype ι] (P : ι → PlE D.host) :
    ∃ Q : Finset (PlE D.host), IsQ P Q ∧ Q.card ≤ 2 * Fintype.card ι := by
  classical
  have : ∀ q, ∃ v, ∀ w, IsConjPl D.host (P q) w ↔ (w = v ∧ IsConjPl D.host (P q) v) := by
    intro q
    by_cases h : ∃ v, IsConjPl D.host (P q) v
    · obtain ⟨v, hv⟩ := h
      exact ⟨v, fun w => ⟨fun hw => ⟨isConjPl_unique hw hv, hv⟩, fun hw => hw.1 ▸ hw.2⟩⟩
    · exact ⟨P q, fun w => ⟨fun hw => absurd ⟨w, hw⟩ h, fun hw => hw.1 ▸ hw.2⟩⟩
  choose c hc using this
  refine ⟨Finset.univ.image P ∪ (Finset.univ.filter fun q => IsConjPl D.host (P q) (c q)).image c, fun v => ?_, ?_⟩
  · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, Over]
    constructor
    · rintro (⟨q, rfl⟩ | ⟨q, h, rfl⟩)
      · exact ⟨q, Or.inl rfl⟩
      · exact ⟨q, Or.inr h⟩
    · rintro ⟨q, rfl | h⟩
      · exact Or.inl ⟨q, rfl⟩
      · exact Or.inr ⟨q, ((hc q v).1 h).2, ((hc q v).1 h).1.symm⟩
  · refine (Finset.card_union_le _ _).trans ?_
    have h1 : (Finset.univ.image P).card ≤ Fintype.card ι := Finset.card_image_le
    have h2 : ((Finset.univ.filter fun q => IsConjPl D.host (P q) (c q)).image c).card ≤ Fintype.card ι :=
      Finset.card_image_le.trans (Finset.card_le_univ _)
    omega

theorem conjCl_of_isQ {ι : Type} {P : ι → PlE D.host} {Q : Finset (PlE D.host)} (hQ : IsQ P Q) :
    ConjCl (D := D) Q := by
  intro v hv v' h
  obtain ⟨q, hq⟩ := (hQ v).1 hv
  refine (hQ v').2 ⟨q, ?_⟩
  exact over_of_over hq (Or.inr (isConjPl_symm h))

theorem l_ne_zero_Ok (i : X.Tw) (k : ℕ) : ((X.l i : ℕ) : X.Ok i k) ≠ 0 ∧ ((X.l i : ℕ) : X.O i) ≠ 0 ∧
    ((X.l i : ℕ) : X.O0 i) ≠ 0 := by
  have hl : (X.l i).Prime := (X.lPrime i).out
  haveI : NeZero (X.l i ^ 1) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have h1 : ((X.l i ^ 1 : ℕ) : X.Ok i 1) ≠ 0 := (IsPrimitiveRoot.neZero' (X.zk_prim i 1)).out
  rw [pow_one] at h1
  have h2 : ((X.l i : ℕ) : X.O i) ≠ 0 := fun h => h1 (by
    rw [← map_natCast (algebraMap (X.O i) (X.Ok i 1)), h, map_zero])
  refine ⟨fun h => h2 (X.Ok_inj i k (by rw [map_natCast, h, map_zero])), h2, fun h => h2 (by
    rw [← map_natCast (algebraMap (X.O0 i) (X.O i)), h, map_zero])⟩

theorem isLocalHom_Ok (i : X.Tw) (k : ℕ) : IsLocalHom (algebraMap (X.O i) (X.Ok i k)) := by
  haveI := X.Ok_fin i k
  haveI : FaithfulSMul (X.O i) (X.Ok i k) := (faithfulSMul_iff_algebraMap_injective _ _).2 (X.Ok_inj i k)
  infer_instance

theorem l_not_unit (i : X.Tw) (k : ℕ) : ¬ IsUnit ((X.l i : ℕ) : X.Ok i k) ∧ ¬ IsUnit ((X.l i : ℕ) : X.O i) ∧
    ¬ IsUnit ((X.l i : ℕ) : X.O0 i) := by
  have h2 : ¬ IsUnit ((X.l i : ℕ) : X.O i) := X.O_l i
  haveI := isLocalHom_Ok i k
  refine ⟨fun h => h2 (isUnit_of_map_unit (algebraMap (X.O i) (X.Ok i k)) _ (by rwa [map_natCast])), h2,
    fun h => h2 ?_⟩
  rw [← map_natCast (algebraMap (X.O0 i) (X.O i))]
  exact h.map _

theorem isLocalHom_O (i : X.Tw) : IsLocalHom (algebraMap (X.O0 i) (X.O i)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.O0 i)
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨m, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (l_ne_zero_Ok i 0).2.2 hϖ
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hna
  rw [map_mul, map_pow] at ha
  have h1 := (isUnit_pow_iff hn).1 (isUnit_of_mul_isUnit_right ha)
  apply (l_not_unit i 0).2.1
  rw [← map_natCast (algebraMap (X.O0 i) (X.O i)), hw, map_mul, map_pow]
  exact (w.isUnit.map _).mul (h1.pow _)

section Val

variable {S : Type} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] {l : ℕ}

theorem e_pos (h0 : (l : S) ≠ 0) (h1 : ¬ IsUnit (l : S)) :
    0 < (IsDiscreteValuationRing.addVal S (l : S)).toNat := by
  rw [Nat.pos_iff_ne_zero, Ne, ENat.toNat_eq_zero]
  rintro (h | h)
  · exact h1 (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
  · exact h0 (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)

theorem addVal_l_pow (h0 : (l : S) ≠ 0) (n : ℕ) :
    IsDiscreteValuationRing.addVal S ((l : S) ^ n) = ((n * (IsDiscreteValuationRing.addVal S (l : S)).toNat : ℕ) : ℕ∞) := by
  rw [IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul, Nat.cast_mul,
    ENat.coe_toNat (by simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using h0)]

theorem nval_nonneg (x : S) : 0 ≤ nval S l x := by
  unfold nval
  positivity

theorem valE_eq (h0 : (l : S) ≠ 0) (h1 : ¬ IsUnit (l : S)) {x : S} (hx : x ≠ 0) :
    valE S l x = ENNReal.ofReal (nval S l x) := by
  have he := e_pos h0 h1
  have hT : IsDiscreteValuationRing.addVal S x ≠ ⊤ := by
    simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using hx
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hT
  unfold valE nval
  rw [← hm, ENNReal.ofReal_div_of_pos (by exact_mod_cast he)]
  simp

theorem nval_l_pow (h0 : (l : S) ≠ 0) (h1 : ¬ IsUnit (l : S)) (n : ℕ) : nval S l ((l : S) ^ n) = n := by
  have he := e_pos h0 h1
  unfold nval
  rw [IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul, ENat.toNat_mul, ENat.toNat_coe, Nat.cast_mul,
    mul_div_assoc, div_self (by exact_mod_cast he.ne'), mul_one]

end Val

theorem ordHyp_mono {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {l M R n n' v : ℕ}
    {f : MvPolynomial (Fin R ⊕ Fin R) O} (h : OrdHyp O l M R n v f) (hn : n ≤ n') : OrdHyp O l M R n' v f := by
  obtain ⟨Dd, g, h1, h2, u, m, h3, h4, h5⟩ := h
  exact ⟨Dd, g, h1, h2, u, m, h3, fun i => (h4 i).trans hn, h5⟩

theorem isAuxiliaryPlaceFamilyAtLevel_mono {i : X.Tw} {M : ℕ} {A A' : Finset (PlE D.host)} {ι : Type} {P : ι → PlE D.host} {d}
    (h : SlopeTestRemainingChoices X i M A P d) (hA : A' ⊆ A) : SlopeTestRemainingChoices X i M A' P d :=
  ⟨fun q v hv => let ⟨a, b, c, e, f, g⟩ := h.1 q v hv; ⟨a, b, c, e, fun h => f (hA h), g⟩, h.2⟩

theorem steps_mono {i : X.Tw} {M : ℕ} {H H' : Subgroup (GE N)} {z : GE N} {R : ℕ} {P : Fin R ⊕ Fin R → PlE D.host} {d}
    (h : Steps X i M H z P d) (hH : H ≤ H') : Steps X i M H' z P d :=
  ⟨fun a σ hσ => let ⟨g, hg⟩ := h.1 a σ hσ; ⟨g, hH hg⟩, h.2⟩

def prodChar {ι κ A : Type} [Fintype ι] [CommGroup A] (n : ℕ) [NeZero n] (c : ι → κ) (u : ι → A)
    (hu : ∀ q, u q ^ n = 1) : Multiplicative (κ → ZMod n) →* A where
  toFun x := ∏ q, u q ^ (Multiplicative.toAdd x (c q)).val
  map_one' := by simp
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ (hu q)]

theorem totient_bound {l k e : ℕ} (hl : l.Prime) (he : e < k) :
    1 / (Nat.totient (l ^ (k - e)) : ℝ) = (l : ℝ) ^ e / (Nat.totient (l ^ k) : ℝ) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_lt he
  have : e + a + 1 - e = a + 1 := by omega
  rw [this, Nat.totient_prime_pow_succ hl, Nat.totient_prime_pow_succ hl]
  have h1 : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have h2 : ((l - 1 : ℕ) : ℝ) ≠ 0 := by
    have := hl.two_le
    exact_mod_cast (by omega : l - 1 ≠ 0)
  push_cast
  field_simp
  ring

theorem exists_ine {i : X.Tw} {M : ℕ} (hM : 1 ≤ M) {A0 : Finset (PlE D.host)} {ι : Type} [Fintype ι]
    {P : ι → PlE D.host} {d} (h : SlopeTestRemainingChoices X i M A0 P d) {Γ : Type} [CommGroup Γ] (u : ι → Γ) (ψ : GE N →* Γ)
    (hψ : ∀ g, ψ g = ∏ q, u q ^ (Multiplicative.toAdd (d q g)).val) {q : ι} {v : PlE D.host} (hv : Over (P q) v)
    (A : ValuationSubring N.Om) (hA : IsPlaceOver A v) : ∃ σ ∈ Ine (F := D.host.E) A, ψ σ = u q := by
  have hl : (X.l i).Prime := (X.lPrime i).out
  obtain ⟨σ, hσ, h1⟩ := (h.2.2 q).2.2.2.2 v hv A hA (Multiplicative.ofAdd 1)
  refine ⟨σ, hσ, ?_⟩
  haveI : Fact (1 < X.l i ^ M) := ⟨Nat.one_lt_pow (by omega) hl.one_lt⟩
  rw [hψ, Finset.prod_eq_single q, h1, toAdd_ofAdd, ZMod.val_one, pow_one]
  · intro q' _ hq'
    rw [(h.2.2 q').2.2.2.1 v (fun hv' => hq' (h.2.1 q' q (over_of_over hv' hv))) A hA σ hσ]
    simp
  · simp

theorem zk_pow_prim (i : X.Tw) {k e : ℕ} (he : e < k) :
    IsPrimitiveRoot ((X.zk i k ^ (X.l i ^ e) : (X.Ok i k)ˣ) : X.Ok i k) (X.l i ^ (k - e)) := by
  have hl : (X.l i).Prime := (X.lPrime i).out
  rw [Units.val_pow_eq_pow_val]
  refine (X.zk_prim i k).pow (pow_pos hl.pos _) ?_
  rw [← pow_add]
  congr 1
  omega

theorem tameVal_le {S : Type} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] (l : ℕ) (ψ : GE N →* Sˣ)
    (A : ValuationSubring N.Om) {σ : GE N} (hσ : σ ∈ Ine (F := D.host.E) A) (h : ψ σ ≠ 1) :
    tameVal l ψ A ≤ nval S l ((ψ σ : S) - 1) := by
  refine csInf_le ⟨0, ?_⟩ ⟨σ, hσ, h, rfl⟩
  rintro x ⟨τ, -, -, rfl⟩
  exact nval_nonneg _

theorem psiOk_partD (Y : NExp D.R D.host D.what₂ D.LL0 N X) {i : X.Tw} {M k : ℕ} (hM : 1 ≤ M) (hk : 1 ≤ k)
    {A0 : Finset (PlE D.host)} {ι : Type} [Fintype ι]
    {P : ι → PlE D.host} {d} (h : SlopeTestRemainingChoices X i M A0 P d) {Q : Finset (PlE D.host)} (hQ : IsQ P Q) (e : ι → ℕ) {ε : ℝ}
    (he : ∀ q, e q < k ∧ (X.l i : ℝ) ^ e q / (Nat.totient (X.l i ^ k) : ℝ) ≤ ε)
    (ψ' : X.RCG i Q →* (X.Ok i k)ˣ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (hχ : ψ'.comp (X.art i Q) = χ.comp (Y.delU i Q M))
    (hψ : ∀ g, ψ' (X.art i Q g) = ∏ q, (X.zk i k ^ (X.l i ^ e q)) ^ (Multiplicative.toAdd (d q g)).val) :
    PsiOk i A0 Q k ψ' ∧ ∑ v ∈ Q, tameVal (X.l i) (ψ'.comp (X.art i Q)) (N.plOm.1 v) ≤ Q.card * ε := by
  classical
  have hl : (X.l i).Prime := (X.lPrime i).out
  have hF : ∀ q, ((X.zk i k ^ (X.l i ^ e q) : (X.Ok i k)ˣ) : X.Ok i k) - 1 ≠ 0 ∧
      nval (X.Ok i k) (X.l i) (((X.zk i k ^ (X.l i ^ e q) : (X.Ok i k)ˣ) : X.Ok i k) - 1) ≤ ε := by
    intro q
    have := GlobalTheory.T.normalizedValuation_primitiveRoot_prime_pow_sub_one (X.Ok i k) (X.l i) (k - e q) hl (by have := (he q).1; omega) (l_ne_zero_Ok i k).1
      (l_not_unit i k).1 _ (zk_pow_prim i (he q).1)
    refine ⟨this.1, ?_⟩
    rw [this.2, totient_bound hl (he q).1]
    exact (he q).2
  have hne : ∀ q, X.zk i k ^ (X.l i ^ e q) ≠ 1 := fun q h => (hF q).1 (by rw [h]; simp)
  refine ⟨⟨fun v hv => ?_, ?_, hk, ?_, ?_, fun g => ?_, fun v A hA => ⟨?_, fun hv => ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨q, hq⟩ := (hQ v).1 hv
    obtain ⟨a, b, c, -⟩ := h.1 q v hq
    exact ⟨a, b, c⟩
  · rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨q, hq⟩ := (hQ v).1 hv
    obtain ⟨-, -, -, a, b, -⟩ := h.1 q v hq
    rcases Finset.mem_union.1 hv' with h | h
    · exact a h
    · exact b h
  · refine Subgroup.isOpen_mono (H₁ := (X.art i Q).ker) (fun g hg => ?_) (X.art_cont i Q)
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.comp_apply, hg, map_one]
  · intro g g' hg
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, X.art_anti i Q g g' hg, map_inv]
  · rw [MonoidHom.comp_apply, hψ]
    exact prod_mem fun q _ => pow_mem (pow_mem (Subgroup.mem_zpowers _) _) _
  · rintro ⟨σ, hσ, h1⟩
    by_contra hv
    exact h1 (by rw [MonoidHom.comp_apply, X.art_unr i Q v hv A hA σ hσ, map_one])
  · obtain ⟨q, hq⟩ := (hQ v).1 hv
    obtain ⟨σ, hσ, h1⟩ := exists_ine hM h _ (ψ'.comp (X.art i Q)) hψ hq A hA
    exact ⟨σ, hσ, h1 ▸ hne q⟩
  · intro v hv A hA σ hσ
    rw [hχ, MonoidHom.comp_apply, Y.delU_l i Q M v hv A hA σ hσ, map_one]
  · rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun v hv => ?_
    obtain ⟨q, hq⟩ := (hQ v).1 hv
    obtain ⟨σ, hσ, h1⟩ := exists_ine hM h _ (ψ'.comp (X.art i Q)) hψ hq (N.plOm.1 v) (N.plOm.2 v)
    refine (tameVal_le _ _ _ hσ (h1 ▸ hne q)).trans ?_
    rw [h1]
    exact (hF q).2

theorem exists_factor (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (M : ℕ) {Q : Finset (PlE D.host)}
    (hQ : ∀ v ∈ Q, v ∉ X.S0 i) :
    ∃ f : X.RCG i Q →* Multiplicative (DelQM D.host (X.l i) Q M), f.comp (X.art i Q) = Y.delU i Q M := by
  have hl : (X.l i).Prime := (X.lPrime i).out
  haveI : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ hl.ne_zero⟩
  refine X.art_univ i Q (fun v hv h => hQ v hv (X.twistExcludedPlaces_contains_residueChar i h)) _ (fun x => ⟨M, ?_⟩) _ (Y.delU_open i Q M)
    (Y.delU_anti i Q M) (Y.delU_unr i Q M)
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext v
  rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]

theorem psiAt_prod {Γ A ι : Type} [Group Γ] [CommGroup A] [Fintype ι] (b : Bool) (ψ : Γ →* A) (ζ : A) (a n : ι → ℕ) (g : Γ)
    (h : ψ g = ∏ q, (ζ ^ a q) ^ n q) : psiAt b ψ g = ∏ q, ((if b then ζ else ζ⁻¹) ^ a q) ^ n q := by
  cases b
  · simp [psiAt, h]
  · simp [psiAt, h]

theorem side_prim (i : X.Tw) (k : ℕ) (b : Bool) :
    IsPrimitiveRoot (((if b then X.zk i k else (X.zk i k)⁻¹ : (X.Ok i k)ˣ)) : X.Ok i k) (X.l i ^ k) := by
  rw [IsPrimitiveRoot.coe_units_iff]
  have := IsPrimitiveRoot.coe_units_iff.1 (X.zk_prim i k)
  cases b
  · exact this.inv
  · exact this

theorem vK_bounds {S : Type} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] {l : ℕ}
    (h0 : (l : S) ≠ 0) (h1 : ¬ IsUnit (l : S)) {a : S} (ha : a ≠ 0) {n : ℕ} {x : FractionRing S}
    (h : algebraMap S (FractionRing S) a = (l : FractionRing S) ^ n * x) :
    x ≠ 0 ∧ vK S l x = nval S l a - n := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact ha (IsFractionRing.injective S (FractionRing S) (by rw [h, map_zero]))
  refine ⟨hx, ?_⟩
  rw [GlobalTheory.NormValExt.vK_eq l hx (a := a) (pow_ne_zero n h0) (by rw [h, map_pow, map_natCast, mul_comm]),
    nval_l_pow h0 h1]

theorem exists_level (i : X.Tw) (R Dd nmax M₀ : ℕ) (I J : Type) [Finite I] [Finite J] (μ : ℕ) (v : J → ℕ)
    (F : ∀ M, M₀ ≤ M → I → MvPolynomial (Fin R ⊕ Fin R) (X.O0 i))
    (f : ∀ M, M₀ ≤ M → J → MvPolynomial (Fin R ⊕ Fin R) (X.O i))
    (hF : ∀ M h x, ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ Dd ∧
      IsDiscreteValuationRing.addVal (X.O0 i) ((F M h x).coeff m) ≤ μ)
    (hf : ∀ M h y, OrdHyp (X.O i) (X.l i) M R nmax (v y) (f M h y)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (M : ℕ) (h : M₀ ≤ M) (k : ℕ) (e : Fin R ⊕ Fin R → ℕ), 1 ≤ k ∧ k ≤ M ∧
      (∀ q, e q < k ∧ (X.l i : ℝ) ^ e q / (Nat.totient (X.l i ^ k) : ℝ) ≤ ε) ∧
      ∀ ζ : (X.Ok i k)ˣ, IsPrimitiveRoot (ζ : X.Ok i k) (X.l i ^ k) →
        (∀ x, MvPolynomial.eval₂ (phiK X i k) (fun q => ((ζ ^ (X.l i ^ e q) : (X.Ok i k)ˣ) : X.Ok i k) - 1) (F M h x) ≠ 0 ∧
          nval (X.Ok i k) (X.l i)
            (MvPolynomial.eval₂ (phiK X i k) (fun q => ((ζ ^ (X.l i ^ e q) : (X.Ok i k)ˣ) : X.Ok i k) - 1) (F M h x)) ≤
            (μ : ℝ) / ((IsDiscreteValuationRing.addVal (X.O0 i) (X.l i : X.O0 i)).toNat : ℝ) + ε) ∧
        ∀ y, MvPolynomial.aeval (fun q => ((ζ ^ (X.l i ^ e q) : (X.Ok i k)ˣ) : X.Ok i k) - 1) (f M h y) ≠ 0 ∧
          nval (X.Ok i k) (X.l i)
            (MvPolynomial.aeval (fun q => ((ζ ^ (X.l i ^ e q) : (X.Ok i k)ˣ) : X.Ok i k) - 1) (f M h y)) ≤
            (v y : ℝ) / ((IsDiscreteValuationRing.addVal (X.O i) (X.l i : X.O i)).toNat : ℝ) + ε := by
  classical
  have hl : (X.l i).Prime := (X.lPrime i).out
  haveI := X.twistBaseCoefficientRing_residueField_finite i
  haveI := isLocalHom_O i
  choose D1 g hDg using hf
  obtain ⟨M, k, e, hM, hk, hkM, he, H⟩ := GlobalTheory.T.exists_level_order_exponents_small_valuation_determinants (X.O0 i) (X.O i) (X.O_inj i) (X.l i) hl (l_ne_zero_Ok i 0).2.2
    (l_not_unit i 0).2.2 R Dd nmax M₀ I J (fun _ => μ) v (fun M x => if h : M₀ ≤ M then F M h x else 0)
    (fun M x => if h : M₀ ≤ M then f M h x else 0) (fun M x => if h : M₀ ≤ M then D1 M h x else 0)
    (fun M x => if h : M₀ ≤ M then g M h x else 0)
    (fun M h x => by simp only [dif_pos h]; exact hF M h x) (fun M h y => by simp only [dif_pos h]; exact hDg M h y) ε hε
  refine ⟨M, hM, k, e, hk, hkM, he, fun ζ hζ => ?_⟩
  haveI := isLocalHom_Ok i k
  have := H (X.Ok i k) (X.Ok_inj i k) ζ hζ
  simp only [dif_pos hM, MvPolynomial.aeval_def, MvPolynomial.eval₂_map] at this
  simp only [Units.val_pow_eq_pow_val, MvPolynomial.aeval_def]
  exact this

theorem admAB_of_toric_parts (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (N0 : X.Tw → ℕ) (hU : DelUTie bkP.ex) (hAB : PropABCD bkP.ex) (hX : GaloisSideTwistedSelmerAuxiliaryPrimes bkP) (hadm : AdmACD bkP N0) :
    Formalism.MainNotions.IntegralHeckeForms.TwistingCharacterExistence bkP.ex bkP N0 := by
  classical
  intro i hi hS eps' heps F hF A0
  have hl : (X.l i).Prime := (X.lPrime i).out
  obtain ⟨h1, h2, h3, -, h9, h10⟩ := hadm
  obtain ⟨sNC, sSD, sNJ, sth, sS, sr, -⟩ := hS
  obtain ⟨z, hz⟩ := GlobalTheory.TwSys.exists_tameInertiaElementAtAuxiliaryPrime D N X i
  obtain ⟨R, Dd, M₀, hM₀, hR⟩ := hX i {s | goodS bkP i s}
    (fun s hs => ⟨h1 i hi s, h2 i hi s, sSD s hs, sNJ s hs, sNC, h3, sr⟩)
  choose HE vE hHEo hHEn hvE hE using fun lam => GlobalTheory.T.propE_of_admissible D N X N0 h9 h10 i lam z hi (sS lam) (sth lam) hz
  choose HB AB vB nB hHBo hHBn hB using fun y : ↥(Finset.Icc 1 D.R.m) × Bool =>
    hAB i F y.1 y.2 z hi y.1.2 (hF _ y.1.2 _) hz
  have hopen : IsOpen (((⨅ lam, HE lam) ⊓ ⨅ y, HB y : Subgroup (GE N)) : Set (GE N)) := by
    rw [Subgroup.coe_inf, Subgroup.coe_iInf, Subgroup.coe_iInf]
    exact (isOpen_iInter_of_finite hHEo).inter (isOpen_iInter_of_finite hHBo)
  have hnorm : ((⨅ lam, HE lam) ⊓ ⨅ y, HB y : Subgroup (GE N)).Normal := by
    haveI := Subgroup.normal_iInf_normal hHEn
    haveI := Subgroup.normal_iInf_normal hHBn
    infer_instance
  choose H0 S0 d hd hco using fun M (h : M₀ ≤ M) => hU i M hi (hM₀.trans h)
  choose P hPa hPs hPF using fun M (h : M₀ ≤ M) =>
    hR M h _ _ _ (hd M h) z hz _ hopen hnorm (A0 ∪ Finset.univ.biUnion AB)
  choose Q hQ hQc using fun M (h : M₀ ≤ M) => exists_isQ (P M h)
  choose Fs hFs hFc using fun M (h : M₀ ≤ M) (s : {s // goodS bkP i s}) => hPF M h s.1 s.2 (Q M h) (hQ M h)
  choose fE hfE hfE' using fun M (h : M₀ ≤ M) lam => hE lam M R (P M h) _ (Q M h) (hM₀.trans h)
    (isAuxiliaryPlaceFamilyAtLevel_mono (hPa M h) (Finset.empty_subset _)) (steps_mono (hPs M h) (inf_le_left.trans (iInf_le _ lam))) (hQ M h)
  choose fB hfB hfB' using fun M (h : M₀ ≤ M) y => hB y M R (P M h) (d M h) (Q M h) (hM₀.trans h) (hco M h)
    (isAuxiliaryPlaceFamilyAtLevel_mono (hPa M h) ((Finset.subset_biUnion_of_mem AB (Finset.mem_univ y)).trans Finset.subset_union_right))
    (steps_mono (hPs M h) (inf_le_right.trans (iInf_le _ y))) (hQ M h)
  set C : ℝ := (SigG bkP i).card + 2 * D.R.m + D.R.t * (4 * R) + 1 with hC
  have hCpos : 0 < C := by positivity
  have hεC : C * (eps' / C) = eps' := by field_simp
  have hε : 0 < eps' / C := div_pos heps hCpos
  generalize eps' / C = ε at hε hεC
  have hle : ∀ c : ℝ, c ≤ C → c * ε ≤ eps' := fun c hc => hεC ▸ mul_le_mul_of_nonneg_right hc hε.le
  have c1 : (0 : ℝ) ≤ (SigG bkP i).card := Nat.cast_nonneg _
  have c2 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have c3 : (0 : ℝ) ≤ D.R.t * (4 * R) := by positivity
  have he0 := e_pos (l_ne_zero_Ok i 0).2.2 (l_not_unit i 0).2.2
  obtain ⟨M, hM, k, e, hk, hkM, he, Hev⟩ := exists_level i R Dd (2 + ∑ y, nB y) M₀ {s // goodS bkP i s}
    (X.abelian₂ i ⊕ (↥(Finset.Icc 1 D.R.m) × Bool))
    (nu X i * (IsDiscreteValuationRing.addVal (X.O0 i) (X.l i : X.O0 i)).toNat) (Sum.elim vE vB) Fs
    (fun M h => Sum.elim (fE M h) (fB M h))
    (fun M h x => by
      obtain ⟨m, hm, hv⟩ := hFc M h x
      exact ⟨m, hm, hv.trans (addVal_l_pow (l_ne_zero_Ok i 0).2.2 _).le⟩)
    (fun M h y => by
      rcases y with lam | y
      · exact ordHyp_mono (hfE M h lam) (Nat.le_add_right _ _)
      · exact ordHyp_mono (hfB M h y)
          ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)).trans (Nat.le_add_left _ _))) hε
  haveI : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hu : ∀ (b : Bool) q, ((if b then X.zk i k else (X.zk i k)⁻¹) ^ (X.l i ^ e q)) ^ (X.l i ^ M) = 1 := by
    intro b q
    rw [← pow_mul]
    exact ((IsPrimitiveRoot.coe_units_iff.1 (side_prim i k b)).pow_eq_one_iff_dvd _).2
      (Dvd.dvd.mul_left (pow_dvd_pow _ hkM) _)
  have hmem : ∀ q, P M hM q ∈ Q M hM := fun q => (hQ M hM _).2 ⟨q, Or.inl rfl⟩
  let χ : Multiplicative (DelQM D.host (X.l i) (Q M hM) M) →* (X.Ok i k)ˣ :=
    prodChar (X.l i ^ M) (fun q => (⟨P M hM q, hmem q⟩ : ↥(Q M hM))) (fun q => X.zk i k ^ (X.l i ^ e q)) (hu true)
  have hχ : ∀ x : DelQM D.host (X.l i) (Q M hM) M, χ (Multiplicative.ofAdd x) =
      ∏ q, (X.zk i k ^ (X.l i ^ e q)) ^ (x ⟨P M hM q, hmem q⟩).val := fun _ => rfl
  obtain ⟨φ, hφ⟩ := exists_factor bkP.ex i M (Q := Q M hM) (fun v hv => by
    obtain ⟨q, hq⟩ := (hQ M hM v).1 hv
    exact ((hPa M hM).1 q v hq).2.2.2.1)
  have hψχ : (χ.comp φ).comp (X.art i (Q M hM)) = χ.comp (bkP.ex.delU i (Q M hM) M) := by
    rw [MonoidHom.comp_assoc, hφ]
  have hψ : ∀ g, (χ.comp φ) (X.art i (Q M hM) g) =
      ∏ q, (X.zk i k ^ (X.l i ^ e q)) ^ (Multiplicative.toAdd (d M hM (P M hM q) g)).val := by
    intro g
    refine (DFunLike.congr_fun hψχ g).trans ((hχ (Multiplicative.toAdd (bkP.ex.delU i (Q M hM) M g))).trans ?_)
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [hco M hM _ (conjCl_of_isQ (hQ M hM))]
  generalize χ.comp φ = ψ' at hψχ hψ
  obtain ⟨hok, hD⟩ := psiOk_partD bkP.ex (hM₀.trans hM) hk (isAuxiliaryPlaceFamilyAtLevel_mono (hPa M hM) Finset.subset_union_left) (hQ M hM) e he
    ψ' χ hψχ hψ
  refine ⟨Q M hM, k, ψ', hok, ⟨fun _ => ε, fun _ => hε.le, ?_, fun s hs => ?_⟩, fun lam => ?_, ?_,
    M, χ, hψχ, fun _ _ => ε, fun _ _ => hε.le, ?_, fun j hj b Tψ hT hmemT => ?_⟩
  · rw [Finset.sum_const, nsmul_eq_mul]
    exact hle _ (by linarith)
  · obtain ⟨hne, hv⟩ := (Hev _ (side_prim i k (X.side i s))).1 ⟨s, hs⟩
    rw [hFs M hM ⟨s, hs⟩ k _ _ (hu (X.side i s)) (fun g => psiAt_prod _ _ _ _ _ g (hψ g)),
      valE_eq (l_ne_zero_Ok i k).1 (l_not_unit i k).1 hne]
    refine ENNReal.ofReal_le_ofReal (hv.trans (le_of_eq ?_))
    congr 1
    rw [Nat.cast_mul, mul_div_assoc, div_self (by exact_mod_cast he0.ne'), mul_one]
  · obtain ⟨hne, hv⟩ := (Hev _ (side_prim i k (X.sideL i lam))).2 (.inl lam)
    have := hfE' M hM lam k _ (psiAt (X.sideL i lam) ψ') (hu (X.sideL i lam)) (fun g => psiAt_prod _ _ _ _ _ _ (hψ g))
    obtain ⟨hx, hvK⟩ := vK_bounds (l_ne_zero_Ok i k).1 (l_not_unit i k).1 hne this
    simp only [Sum.elim_inl] at hv hvK
    rw [hvE] at hv
    have h0 := hle 1 (by linarith)
    refine ⟨hx, ?_, ?_⟩
    · rw [hvK]
      exact le_sub_iff_add_le.2 (by rw [neg_add_cancel]; exact nval_nonneg _)
    · rw [hvK]
      linarith
  · have hc : ((Q M hM).card : ℝ) ≤ 4 * R := by
      have := hQc M hM
      rw [Fintype.card_sum, Fintype.card_fin] at this
      exact_mod_cast (by omega : (Q M hM).card ≤ 4 * R)
    refine (mul_le_mul_of_nonneg_left (hD.trans (mul_le_mul_of_nonneg_right hc hε.le)) (Nat.cast_nonneg _)).trans ?_
    rw [← mul_assoc]
    exact hle _ (by linarith)
  · have := hle (D.R.m * 2) (by linarith)
    simpa [mul_assoc] using this
  · obtain ⟨hne, hv⟩ := (Hev _ (side_prim i k b)).2 (.inr (⟨j, hj⟩, b))
    have := hfB' M hM (⟨j, hj⟩, b) k _ (psiAt b χ) (hu b) (fun x => psiAt_prod _ _ _ _ _ _ (hχ x)) hne Tψ hT hmemT
    simp only [Sum.elim_inr] at hv
    refine this.trans (add_le_add_right ?_ _)
    linarith

end GlobalTheory.TwistChoice

end
