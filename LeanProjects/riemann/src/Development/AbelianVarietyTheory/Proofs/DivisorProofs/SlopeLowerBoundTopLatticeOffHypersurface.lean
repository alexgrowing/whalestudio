import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRightInvOfSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDegreeGeHeightPolynomialVectorsDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiformHeightLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamComplexTensorNormColumnUnitSpheresLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortColumnsDetNeZeroHilbertSamuelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDeepestFiltrationStepEqRationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowDvdOfSpecialisations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClaimSOfNumbers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetRationalSectionsEqPowProductLinearFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiHomogeneousCofactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetIsMultiHomogeneous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffLinearSubstColumnMemIntegralLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialCountsDegreeAndWeightedSum

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort.SlopeTop

theorem mh_mul {R : Type*} [CommSemiring R] {B n : ℕ} {a a' c : Fin B → ℕ} {p q : MvPolynomial (Fin B × Fin n) R}
    (hp : IsMultiHomogeneous a p) (hq : IsMultiHomogeneous a' q) (hc : ∀ b, c b = a b + a' b) :
    IsMultiHomogeneous c (p * q) := by
  classical
  intro s hs b
  obtain ⟨s1, h1, s2, h2, rfl⟩ := Finset.mem_add.mp (support_mul p q hs)
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, hp s1 h1 b, hq s2 h2 b, hc]

theorem mh_pow {R : Type*} [CommSemiring R] {B n : ℕ} {a : Fin B → ℕ} {p : MvPolynomial (Fin B × Fin n) R}
    (hp : IsMultiHomogeneous a p) (k : ℕ) : IsMultiHomogeneous (fun b => k * a b) (p ^ k) := by
  classical
  induction k with
  | zero =>
    intro s hs b
    have : s = 0 := by
      rw [pow_zero, mem_support_iff, coeff_one] at hs
      by_contra h; exact hs (if_neg (Ne.symm h))
    simp [this]
  | succ k ih =>
    rw [pow_succ]
    exact mh_mul ih hp (fun b => by ring)

theorem ht_pow {F : Type} [Field F] [NumberField F] {B N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} {Λ : ℝ} (hL : Lat w A Λ) {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (ha : IsMultiHomogeneous a f) (k : ℕ) :
    ht w A (f ^ k) = k * ht w A f := by
  induction k with
  | zero => rw [pow_zero, ← C_1, (htMul F B N n w A Λ hL).2 1 one_ne_zero]; simp
  | succ k ih =>
    rw [pow_succ, (htMul F B N n w A Λ hL).1 _ _ _ _ (pow_ne_zero k hf) hf (mh_pow ha k) ha, ih]
    push_cast; ring

theorem map_join {R R' : Type} (φ : R → R') {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) :
    (fun p => φ (join u ξ p)) = join (fun i j => φ (u i j)) (fun j => φ (ξ j)) := by
  funext ⟨i, j⟩
  induction i using Fin.lastCases with
  | last => simp [join_last]
  | cast i => simp [join_castSucc]

theorem eval_spec {F E : Type} [Field F] [Field E] [Algebra F E] {D N : ℕ} (s : Fin D → Fin N → E) (l : Fin N → E)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    eval (fun p : Fin 1 × Fin N => l p.2) (spec s f) = aeval (join s l) f := by
  have hj : ∀ q, eval (fun p : Fin 1 × Fin N => l p.2)
      (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) E)) (fun j => X (0, j)) q) = join s l q := by
    rintro ⟨i, j⟩
    induction i using Fin.lastCases with
    | last => simp [join_last]
    | cast i => simp [join_castSucc]
  induction f using MvPolynomial.induction_on with
  | C a => simp [spec]
  | add p q hp hq => simp only [spec, map_add] at *; rw [hp, hq]
  | mul_X p q hp => simp only [spec, map_mul, aeval_X] at *; rw [hp, hj]

theorem algebraMap_eval {F E σ : Type} [Field F] [Field E] [Algebra F E] (x : σ → F) (p : MvPolynomial σ F) :
    algebraMap F E (eval x p) = aeval (fun i => algebraMap F E (x i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p q hp => simp [map_mul, hp]

theorem sum_three {d : ℕ} (P Q : Fin d → Prop) [DecidablePred P] [DecidablePred Q] (hPQ : ∀ k, P k → ¬ Q k)
    {M : Type*} [AddCommMonoid M] (g : Fin d → M) (x y z : M)
    (hx : ∀ k, P k → g k = x) (hy : ∀ k, Q k → g k = y) (hz : ∀ k, ¬ P k → ¬ Q k → g k = z) :
    ∑ k, g k = (Finset.univ.filter P).card • x + (Finset.univ.filter Q).card • y +
      (Finset.univ.filter fun k => ¬ P k ∧ ¬ Q k).card • z := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P,
    ← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun k => ¬ P k) Q,
    Finset.filter_filter, Finset.filter_filter]
  have e1 : (Finset.univ.filter fun k => ¬ P k ∧ Q k) = Finset.univ.filter Q :=
    Finset.filter_congr fun k _ => ⟨fun h => h.2, fun h => ⟨fun hp => hPQ k hp h, h⟩⟩
  rw [e1, Finset.sum_congr rfl (fun k hk => hx k (Finset.mem_filter.mp hk).2),
    Finset.sum_congr rfl (fun k hk => hy k (Finset.mem_filter.mp hk).2),
    Finset.sum_congr rfl (fun k hk => hz k (Finset.mem_filter.mp hk).2.1 (Finset.mem_filter.mp hk).2.2)]
  simp only [Finset.sum_const, add_assoc]

end GlobalTheory.HSShort.SlopeTop

namespace GlobalTheory.HSShort.SlopeTop

theorem slopeBound : SlopeBound := by
  intro F A _ _ _ _ _ _ S hS δ f Q hδ hfh hfi hQ hflat
  classical
  obtain ⟨d, b, -⟩ := hS.shortT
  have hfin : Module.finrank F (S.V S.T) = d := by simpa using Module.finrank_eq_card_basis b
  have hc : ∀ i, ∃ g : A →ₗ[F] F, g ∘ₗ (S.V S.T).subtype = b.coord i := fun i => LinearMap.exists_extend _
  choose c hc using hc
  have hco : S.IsCo b c := by
    intro i x
    have := congrArg (fun g => g x) (hc i)
    simpa using this
  have hex : ∃ s : Fin S.D → Fin S.N → F, eval (fun p => s p.1 p.2) Q ≠ 0 := by
    by_contra h
    push_neg at h
    apply hQ
    apply MvPolynomial.funext
    intro x
    simpa using h (fun i k => x (i, k))
  have hbd : ∀ s : Fin S.D → Fin S.N → F, eval (fun p => s p.1 p.2) Q ≠ 0 → S.deepRank s ≤ d := by
    intro s hs
    obtain ⟨E, A', _, _, _, _, Φ, -, -, -⟩ := hflat s hs
    rw [← hfin]; exact (GlobalTheory.T.finrank_deepestFiltrationStep_eq_rational F A S hS E A' s δ Φ).2.2
  let P : ℕ → Prop := fun y => ∃ s : Fin S.D → Fin S.N → F, eval (fun p => s p.1 p.2) Q ≠ 0 ∧ S.deepRank s = y
  obtain ⟨s₁, hs₁⟩ := hex
  obtain ⟨s₀, hs₀, hy⟩ : P (Nat.findGreatest P d) := Nat.findGreatest_spec (hbd s₁ hs₁) ⟨s₁, hs₁, rfl⟩
  have hmax : ∀ s : Fin S.D → Fin S.N → F, eval (fun p => s p.1 p.2) Q ≠ 0 → S.deepRank s ≤ Nat.findGreatest P d :=
    fun s hs => Nat.le_findGreatest (hbd s hs) ⟨s, hs, rfl⟩
  obtain ⟨E₀, A₀, _, _, _, _, Φ₀, -, -, -⟩ := hflat s₀ hs₀
  obtain ⟨col, m, ix, hsh, hshort, hcard, hdet⟩ := GlobalTheory.T.exists_short_columns_det_ne_zero_hilbertSamuel F A S hS E₀ A₀ s₀ δ Φ₀ d b c hco
  rw [hy] at hcard
  have hdiv : f ^ S.expo ∣ S.det c col := by
    refine GlobalTheory.HSShortDiv.pow_dvd_of_specialisations F S.D S.N δ S.expo f (S.det c col) Q hδ hfh hfi hQ ?_
    intro s hs
    obtain ⟨E, A', _, _, _, _, Φ, c', hc', hsp⟩ := hflat s hs
    obtain ⟨γ, hγ⟩ := GlobalTheory.T.det_rational_sections_eq_pow_product_linearForms F A S hS E A' s δ Φ d b c hco col m ix hsh (hcard ▸ hmax s hs)
    refine ⟨E, inferInstance, inferInstance, γ / c' ^ S.expo, fun l => ?_⟩
    have h1 := hγ (fun k => algebraMap F E (l k))
    have h2 : aeval (join (fun i k => algebraMap F E (s i k)) (fun k => algebraMap F E (l k))) f =
        c' * ∏ p, ∑ k, algebraMap F E (l k) * Φ.y p k := by
      rw [← eval_spec, hsp]; simp [lin]
    rw [algebraMap_eval, algebraMap_eval, map_join, h1, h2, mul_pow]
    field_simp
  obtain ⟨G', hG'⟩ := hdiv
  obtain ⟨a, ha, hsum⟩ := GlobalTheory.HSShort.det_isMultiHomogeneous F A S d c col
  have hf0 : f ≠ 0 := hfi.ne_zero
  have hfe : IsMultiHomogeneous (fun _ => S.expo * δ) (f ^ S.expo) := mh_pow hfh S.expo
  have hdet' : f ^ S.expo * G' ≠ 0 := hG' ▸ hdet
  have ha2 : IsMultiHomogeneous a (f ^ S.expo * G') := hG' ▸ ha
  obtain ⟨a', ha', hadd⟩ := GlobalTheory.HSShort.isMultiHomogeneous_cofactor F (S.D + 1) S.N a (fun _ => S.expo * δ) (f ^ S.expo) G' hdet' ha2 hfe
  have hG0 : G' ≠ 0 := right_ne_zero_of_mul hdet'
  have hfe0 : f ^ S.expo ≠ 0 := left_ne_zero_of_mul hdet'
  have hht : ht S.w S.fr (S.det c col) = S.expo * ht S.w S.fr f + ht S.w S.fr G' := by
    rw [hG', (htMul F _ _ _ S.w S.fr S.abelian₂ hS.lat).1 _ _ _ _ hfe0 hG0 hfe ha', ht_pow hS.lat hf0 hfh]
  have hlowf := GlobalTheory.T.multiformHeight_lowerBound F (S.D + 1) S.N S.n S.w S.fr S.abelian₂ hS.lat (fun _ => δ) f hf0 hfh
  have hlowG := GlobalTheory.T.multiformHeight_lowerBound F (S.D + 1) S.N S.n S.w S.fr S.abelian₂ hS.lat a' G' hG0 ha'
  let bnd : ℕ → ℝ := fun j => if j = 0 then S.Lam0 else if j = S.D then S.LamD else S.LamT
  let Bd : Fin d → ℝ := fun k => Real.sqrt S.beta ^ (col k).t * bnd (col k).j
  have hbnd1 : ∀ j, 1 ≤ bnd j := by
    intro j; simp only [bnd]
    split_ifs
    · exact hS.hermSysHyp_one_le_lambdaZero
    · exact hS.one_le_LamD
    · exact hS.one_le_LamT
  have hsb : 1 ≤ Real.sqrt S.beta := Real.one_le_sqrt.mpr hS.one_le_beta
  have hBd : ∀ k, 0 < Bd k := fun k => mul_pos (pow_pos (by linarith) _) (by linarith [hbnd1 (col k).j])
  have htop := GlobalTheory.T.lattice_degree_ge_height_polynomialVectors_det F (S.V S.T) (S.nm S.T) (S.M S.T) d b (hS.full S.T le_rfl) (S.D + 1) S.N S.n S.w S.fr S.abelian₂
    hS.lat (Matrix.of fun i k => coordP S.mul (c i) (col k).β ((col k).x : A)) a Bd hdet ha hBd
    (fun k m' => GlobalTheory.T.coeff_linearSubst_column_mem_integralLattice F A S hS d b c hco (col k) (hshort k).1 m')
    (fun k σ u hu => (GlobalTheory.T.hermFamComplexTensorNorm_column_unitSpheres_le F A S hS d b c hco (col k) σ u hu).trans
      (mul_le_mul_of_nonneg_left ((hshort k).2 σ) (pow_nonneg (by linarith) _)))

  have hD1 := hS.one_le
  have hDT := hS.le_T
  have hnum := GlobalTheory.HSShort.monomial_counts S.D S.T hD1 hDT
  let PR : Fin d → Prop := fun k => k ∈ Set.range ix
  let QY : Fin d → Prop := fun k => (col k).j = S.D
  have hPR : ∀ k, PR k → (col k).j = 0 := by rintro k ⟨q, rfl⟩; exact hsh.x_j q
  have hPQ : ∀ k, PR k → ¬ QY k := fun k hk hq => by
    have h0 := hPR k hk; simp only [QY] at hq; omega
  have hRest : ∀ k, ¬ PR k → ¬ QY k → (col k).j = S.T := by
    intro k h1 h2
    rcases hsh.rest k h1 with h | h
    · exact absurd h.1 h2
    · exact h
  have hcardR : (Finset.univ.filter PR).card = (S.T - 1).choose S.D * δ := by
    have : (Finset.univ.filter PR) = Finset.univ.map ix := by ext k; simp [PR]
    rw [this, Finset.card_map, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, ← Nat.card_eq_fintype_card,
      hnum.2.1]
  have hcardQ : (Finset.univ.filter QY).card = Nat.findGreatest P d := hcard
  have hcard3 := sum_three PR QY hPQ (fun _ => (1 : ℕ)) 1 1 1 (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hcard3
  have ht3 := sum_three PR QY hPQ (fun k => (col k).t) S.T (S.T - S.D) 0
    (fun k hk => by have := (col k).add; have h0 := hPR k hk; omega)
    (fun k hk => by have := (col k).add; simp only [QY] at hk; omega)
    (fun k h1 h2 => by have := (col k).add; have hj := hRest k h1 h2; omega)
  simp only [smul_eq_mul, mul_zero, add_zero] at ht3
  have hl3 := sum_three PR QY hPQ (fun k => Real.log (Bd k)) (Real.log (Real.sqrt S.beta ^ S.T * S.Lam0))
    (Real.log (Real.sqrt S.beta ^ (S.T - S.D) * S.LamD)) (Real.log S.LamT)
    (fun k hk => by
      have := (col k).add; have h0 := hPR k hk
      have ht' : (col k).t = S.T := by omega
      simp [Bd, bnd, h0, ht'])
    (fun k hk => by
      have := (col k).add; simp only [QY] at hk
      have hD0 : S.D ≠ 0 := by omega
      have ht' : (col k).t = S.T - S.D := by omega
      simp [Bd, bnd, hk, hD0, ht'])
    (fun k h1 h2 => by
      have := (col k).add; have hj := hRest k h1 h2
      have hT0 : S.T ≠ 0 := by omega
      have hTD : S.T ≠ S.D := by omega
      have ht0 : (col k).t = 0 := by omega
      simp [Bd, bnd, hj, hT0, hTD, ht0])
  simp only [nsmul_eq_mul] at hl3
  have hcountRest : (Finset.univ.filter fun k => ¬ PR k ∧ ¬ QY k).card =
      d - (S.T - 1).choose S.D * δ - Nat.findGreatest P d := by omega
  have hcount : (S.T - 1).choose S.D * δ + Nat.findGreatest P d ≤ d := by omega
  have e1 : ∑ i, a i = (S.D + 1) * (S.expo * δ) + ∑ i, a' i := by
    rw [← Finset.sum_congr rfl (fun i _ => hadd i)]; simp [Finset.sum_add_distrib]
  have hsumE : S.expo * ((S.D + 1) * δ) + ∑ i, a' i =
      (S.T - 1).choose S.D * δ * S.T + Nat.findGreatest P d * (S.T - S.D) := by
    calc _ = ∑ i, a i := by rw [e1]; ring
      _ = _ := by rw [hsum, ht3, hcardR, hcardQ]
  have hlowf' : -(cst (S.n : ℝ) S.abelian₂ * (((S.D : ℝ) + 1) * δ)) ≤ ht S.w S.fr f := by
    have := hlowf
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    exact this
  have hlowG' : -(cst (S.n : ℝ) S.abelian₂ * ((∑ i, a' i : ℕ) : ℝ)) ≤ ht S.w S.fr G' := by
    rw [Nat.cast_sum]; exact hlowG
  have htop' : ht S.w S.fr (S.det c col) - ∑ k, Real.log (Bd k) ≤ deg (S.nm S.T) (S.M S.T) := htop
  rw [hht, hl3, hcardR, hcardQ, hcountRest] at htop'
  have hn1 : (1 : ℝ) ≤ S.n := by
    have : 1 ≤ S.n := by
      by_contra h
      have h0 : S.n = 0 := by omega
      have hsp := hS.lat.spans
      have hN := hS.lat.pos
      have hem : Set.range S.w.col = ∅ := by
        rw [Set.range_eq_empty_iff, h0]; infer_instance
      rw [hem, Submodule.span_empty] at hsp
      have hmem : (Pi.single (⟨0, hN⟩ : Fin S.N) 1 : Fin S.N → F) ∈ (⊥ : Submodule F (Fin S.N → F)) :=
        hsp ▸ Submodule.mem_top
      simp at hmem
    exact_mod_cast this
  have hres := GlobalTheory.HSShortEnd.claimS_of_numbers S.T S.D δ d (Nat.findGreatest P d) (∑ i, a' i) (S.n : ℝ) S.abelian₂ S.beta S.Lam0 S.LamD S.LamT
    (ht S.w S.fr f) (ht S.w S.fr G') (deg (S.nm S.T) (S.M S.T)) hD1 hDT hδ hn1 hS.lat.one_le hS.one_le_beta
    hS.hermSysHyp_one_le_lambdaZero hS.one_le_LamD hS.one_le_LamT hcount S.expo (by simpa [Sys.expo] using hnum.2.2) hsumE
    hlowf' hlowG' htop'
  rw [hfin]
  exact hres

end GlobalTheory.HSShort.SlopeTop
