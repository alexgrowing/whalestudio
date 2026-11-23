import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ArithmeticPointDecomposition
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.LeKerPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNormVEqPrimePowLeFinrank
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.BlockDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SmallCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.WtChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.FrobIn
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PureDet
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerTail

open UpperTheory.GalN.V

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem frobAbs_pow_cong {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω} (ha : A.valuation a ≤ 1)
    (hb : A.valuation b ≤ 1) (h : A.valuation (a - b) < 1) (m : ℕ) : A.valuation (a ^ m - b ^ m) < 1 :=
  _root_.UpperTheory.Reformulated.B.Qf13.pow_cong A ha hb h m

private theorem frobAbs_dec_le {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω}
    {g : G K Ω} (hg : g ∈ Dec (F := K) A) {x : Ω} (hx : A.valuation x ≤ 1) : A.valuation (g x) ≤ 1 :=
  (A.valuation_le_one_iff _).2 ((apply_mem_iff_of_mem_Dec hg x).2 ((A.valuation_le_one_iff _).1 hx))

private theorem frobAbs_isFrob_pow {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    {A : ValuationSubring Ω} {q : ℕ} {g : G K Ω} (hg : IsFrob (F := K) A q g) (n : ℕ) :
    IsFrob (F := K) A (q ^ n) (g ^ n) := by
  induction n with
  | zero => exact ⟨by rw [pow_zero]; exact one_mem _, fun x _ => by simp⟩
  | succ n ih =>
    refine ⟨Subgroup.pow_mem _ hg.1 _, fun x hx => ?_⟩
    have h1 := hg.2 _ (frobAbs_dec_le ih.1 hx)
    have h2 := frobAbs_pow_cong A (frobAbs_dec_le ih.1 hx) (b := x ^ q ^ n)
      (by rw [map_pow]; exact pow_le_one' hx _) (ih.2 x hx) q
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [sub_add_sub_cancel, ← pow_mul, ← pow_succ] at h3
    rw [pow_succ' g, AlgEquiv.mul_apply]
    exact h3

private theorem frobAbs_eig {k : Type} [Field k] [IsAlgClosed k] {n : ℕ} (M N : GL (Fin n) k) {e f : ℕ} (hf : 0 < f)
    (h : M ^ e = N ^ f) {x : k} (hx : (M : Matrix (Fin n) (Fin n) k).charpoly.IsRoot x) :
    ∃ z : k, ((N⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly.IsRoot z⁻¹ ∧ z ^ f = x ^ e := by
  have h1 : x ∈ spectrum k (M : Matrix (Fin n) (Fin n) k) := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hx
  have h2 : x ^ e ∈ spectrum k ((M : Matrix (Fin n) (Fin n) k) ^ e) := spectrum.pow_mem_pow _ e h1
  rw [← Units.val_pow_eq_pow_val, h, Units.val_pow_eq_pow_val, spectrum.map_pow_of_pos _ hf] at h2
  obtain ⟨z, hz, hzx⟩ := h2
  have hz0 : z ≠ 0 := spectrum.ne_zero_of_mem_of_unit hz
  refine ⟨z, Matrix.mem_spectrum_iff_isRoot_charpoly.1 ?_, hzx⟩
  have h3 := (spectrum.inv_mem_iff (r := Units.mk0 z hz0) (a := N)).1 (by simpa using hz)
  simpa using h3

private theorem pos_of_mul_pos_of_pos {a b : ℝ} (ha : 0 < a) (h : 0 < a * b) : 0 < b := (mul_pos_iff_of_pos_left ha).1 h

theorem UpperTheory.V.Ws.Pu.frobAbs_w :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} (ι : PadicAlgCl l ≃+* ℂ) (ρ : G F Ω →* GL (Fin n) (PadicAlgCl l)) (w : HeightOneSpectrum (𝓞 F)) (b : Multiset ℂ), Af.FrobEig ι ρ w b → (∀ z ∈ b, ∀ z' ∈ b, ‖z‖ < (normV w : ℝ) * ‖z'‖) →
      ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ p : ℕ, p.Prime → A.valuation (p : Ω) < 1 → ∀ (f : ℕ) (σ : G F Ω), 0 < f → IsFrob A (p ^ f) σ →
        ∀ x ∈ (W.mat ρ σ).charpoly.roots, ∀ y ∈ (W.mat ρ σ).charpoly.roots, y ≠ 0 → ‖ι x‖ < (p : ℝ) ^ f * ‖ι y‖ := by
  intro F Ω _ _ _ _ _ l _ n ι ρ w b hb ht A hA p hp hpA f σ hf hσ
  have hpw : (p : 𝓞 F) ∈ w.asIdeal := (hA (p : 𝓞 F)).1 (by simpa using hpA)
  obtain ⟨e, he, -, hq⟩ := UpperTheory.exists_normV_eq_prime_pow_le_finrank F p w hp hpw
  obtain ⟨φ, hφ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  obtain ⟨hI, hF⟩ := hb A hA
  have h1 := frobAbs_isFrob_pow hσ e
  have h2 := frobAbs_isFrob_pow hφ f
  rw [hq, ← pow_mul, mul_comm, pow_mul] at h2
  have h3 := hI _ (inv_mul_mem_Ine_of_isFrob h1 h2)
  have h4 : ρ σ ^ e = ρ φ ^ f := by
    rw [map_mul, map_inv, inv_mul_eq_one, map_pow, map_pow] at h3
    first | exact h3 | exact h3.symm
  have key : ∀ x ∈ (W.mat ρ σ).charpoly.roots, ∃ c ∈ b, ‖ι x‖ ^ e = ‖c‖⁻¹ ^ f := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := frobAbs_eig (ρ σ) (ρ φ) hf h4 (isRoot_of_mem_roots hx)
    have h5 := hz.map (f := ι.toRingHom)
    rw [← map_inv ρ, hF φ hφ, IsRoot.def, eval_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map,
      Multiset.mem_map] at h5
    obtain ⟨c, hc, hc0⟩ := h5
    have h6 : (ι z)⁻¹ = c := by
      simpa [sub_eq_zero] using hc0
    refine ⟨c, hc, ?_⟩
    rw [← norm_pow, ← map_pow, ← hzx, map_pow, norm_pow, ← h6, norm_inv, inv_inv]
  intro x hx y hy _
  obtain ⟨c, hc, e1⟩ := key x hx
  obtain ⟨c', hc', e2⟩ := key y hy
  have hq0 : (0 : ℝ) < (normV w : ℕ) := by rw [hq]; exact_mod_cast pow_pos hp.pos e
  have p1 : 0 < ‖c‖ := pos_of_mul_pos_of_pos hq0 (lt_of_le_of_lt (norm_nonneg _) (ht c hc c hc))
  have p2 : 0 < ‖c'‖ := pos_of_mul_pos_of_pos hq0 (lt_of_le_of_lt (norm_nonneg _) (ht c' hc' c' hc'))
  have k : ‖c‖⁻¹ < (normV w : ℝ) * ‖c'‖⁻¹ := by
    rw [← div_eq_mul_inv, lt_div_iff₀ p2, inv_mul_lt_iff₀ p1, mul_comm]
    exact ht c' hc' c hc
  refine lt_of_pow_lt_pow_left₀ e (by positivity) ?_
  rw [mul_pow, e1, e2, ← pow_mul, mul_comm f e, pow_mul, ← mul_pow]
  refine pow_lt_pow_left₀ ?_ (by positivity) hf.ne'
  rwa [hq, Nat.cast_pow] at k

end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem dvd_norm {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime)
    (h : (p : 𝓞 F) ∈ w.asIdeal) : p ∣ Ideal.absNorm w.asIdeal := by
  by_contra hn
  have hc : IsCoprime (p : 𝓞 F) ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 F) :=
    Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)
  obtain ⟨a, b, hab⟩ := hc
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hab]
  exact add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _))

private theorem root_scale {K : Type} [Field K] {P : K[X]} {x : K} (s : K) (hx : x ∈ P.roots) :
    s * x ∈ (P.scaleRoots s).roots := by
  obtain ⟨h0, h1⟩ := mem_roots'.1 hx
  refine mem_roots'.2 ⟨scaleRoots_ne_zero h0 s, ?_⟩
  rw [IsRoot.def, scaleRoots_eval_mul, h1.eq_zero, mul_zero]

theorem UpperTheory.V.Ws.Pu.pureOf_w :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (L : IntermediateField ℚ Ω) [NumberField L]
      (r : G ℚ Ω →* M4 (PadicAlgCl l)) (ρ : G L Ω →* GL (Fin 4) (PadicAlgCl l)) (κ : G L Ω →* (PadicAlgCl l)ˣ) (Z : Set (HeightOneSpectrum (𝓞 L))), Z.Finite →
      (∀ g, (W.mat ρ g).charpoly = (r (resQ L g)).charpoly.scaleRoots (κ g : PadicAlgCl l)) →
      (∀ w ∉ Z, ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ p : ℕ, p.Prime → A.valuation (p : Ω) < 1 → ∀ (f : ℕ) (σ : G L Ω), 0 < f → IsFrob A (p ^ f) σ →
        ∀ x ∈ (W.mat ρ σ).charpoly.roots, ∀ y ∈ (W.mat ρ σ).charpoly.roots, y ≠ 0 → ‖ι x‖ < (p : ℝ) ^ f * ‖ι y‖) → PureW ι r := by
  intro Ω _ _ _ l _ ι L _ r ρ κ Z hZ hcp hab
  classical
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure L Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  refine ⟨L.fixingSubgroup, ∏ w ∈ hZ.toFinset, Ideal.absNorm w.asIdeal, L.fixingSubgroup_isOpen, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun w _ h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  intro p hp hM A hA f σ hf hσ hF x hx y hy hy0
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨p1, p2, -, -⟩ := UpperTheory.V.Base.places L Ω p A
  obtain ⟨w, hw⟩ := p1 fun ht => (p2 ht).2 hA
  have hpw : (p : 𝓞 L) ∈ w.asIdeal := by
    have h1 := hw ((p : ℕ) : 𝓞 L)
    have e : algebraMap L Ω (((p : ℕ) : 𝓞 L) : L) = (p : Ω) := by simp
    rw [e] at h1
    exact h1.1 hA
  have hwZ : w ∉ Z := fun h =>
    hM ((dvd_norm w hp hpw).trans (Finset.dvd_prod_of_mem (fun w : HeightOneSpectrum (𝓞 L) => Ideal.absNorm w.asIdeal) (hZ.mem_toFinset.2 h)))
  let τ : G L Ω := { σ.toRingEquiv with commutes' := fun z => (IntermediateField.mem_fixingSubgroup_iff L σ).1 hσ z.1 z.2 }
  have hτ : resQ L τ = σ := AlgEquiv.ext fun _ => rfl
  have hFτ : IsFrob A (p ^ f) τ := ⟨hF.1, hF.2⟩
  have h := hab w hwZ A hw p hp hA f τ hf hFτ ((κ τ : PadicAlgCl l) * x) (by rw [hcp, hτ]; exact root_scale _ hx)
    ((κ τ : PadicAlgCl l) * y) (by rw [hcp, hτ]; exact root_scale _ hy) (mul_ne_zero (κ τ).ne_zero hy0)
  rw [map_mul, map_mul, norm_mul, norm_mul, mul_left_comm] at h
  exact lt_of_mul_lt_mul_left h (norm_nonneg _)

end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def eAB : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ixA ixB
  invFun := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1]
  left_inv := by decide
  right_inv := by decide

private theorem cp_block {K : Type} [Field K] (X : M4 K) (h : IsBlock X) :
    X.charpoly = (X.submatrix ixA ixA).charpoly * (X.submatrix ixB ixB).charpoly := by
  have e : Matrix.reindex eAB.symm eAB.symm X =
      Matrix.fromBlocks (X.submatrix ixA ixA) (X.submatrix ixA ixB) 0 (X.submatrix ixB ixB) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · exact h (ixB i) (ixA j) (by revert i j; decide)
    · rfl
  rw [← Matrix.charpoly_reindex eAB.symm, e, Matrix.charpoly_fromBlocks_zero₂₁]

private theorem det_two {K : Type} [Field K] [IsAlgClosed K] (A : Matrix (Fin 2) (Fin 2) K) :
    ∃ a ∈ A.charpoly.roots, ∃ b ∈ A.charpoly.roots, A.det = a * b := by
  have hc : A.charpoly.roots.card = 2 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]; simp
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.1 hc
  refine ⟨a, by simp [hab], b, by simp [hab], ?_⟩
  rw [Matrix.det_eq_prod_roots_charpoly, hab]; simp

theorem UpperTheory.V.Ws.pureDet_w :
    ∀ {K : Type} [Field K] [IsAlgClosed K] (ι : K →+* ℂ) (X : M4 K) (Q : ℝ), IsBlock X →
          (∀ x ∈ X.charpoly.roots, ∀ y ∈ X.charpoly.roots, y ≠ 0 → ‖ι x‖ < Q * ‖ι y‖) → (X.submatrix ixB ixB).det ≠ 0 →
          ‖ι (X.submatrix ixA ixA).det‖ < Q ^ 2 * ‖ι (X.submatrix ixB ixB).det‖ := by
  intro K _ _ ι X Q hX h h0
  have hr : X.charpoly.roots =
      (X.submatrix ixA ixA).charpoly.roots + (X.submatrix ixB ixB).charpoly.roots := by
    rw [cp_block X hX, roots_mul (mul_ne_zero (Matrix.charpoly_monic _).ne_zero (Matrix.charpoly_monic _).ne_zero)]
  obtain ⟨a, ha, b, hb, hA⟩ := det_two (X.submatrix ixA ixA)
  obtain ⟨c, hc, d, hd, hB⟩ := det_two (X.submatrix ixB ixB)
  rw [hr] at h
  rw [hB] at h0
  have h1 := h a (Multiset.mem_add.2 (Or.inl ha)) c (Multiset.mem_add.2 (Or.inr hc)) (left_ne_zero_of_mul h0)
  have h2 := h b (Multiset.mem_add.2 (Or.inl hb)) d (Multiset.mem_add.2 (Or.inr hd)) (right_ne_zero_of_mul h0)
  rw [hA, hB, map_mul, map_mul, norm_mul, norm_mul]
  exact (mul_lt_mul'' h1 h2 (norm_nonneg _) (norm_nonneg _)).trans_eq (by ring)

end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def blockChar {H K : Type} [Group H] [CommRing K] (r : H →* M4 K) (h : ∀ g, IsBlock (r g)) (ix : Fin 2 → Fin 4)
    (hix : ix = ixA ∨ ix = ixB) : H →* K where
  toFun g := ((r g).submatrix ix ix).det
  map_one' := by
    rw [map_one, Matrix.submatrix_one ix (by rcases hix with rfl | rfl <;> decide), Matrix.det_one]
  map_mul' a b := by
    rw [← Matrix.det_mul, map_mul]
    congr 1
    have ha := h a
    ext i j
    rcases hix with rfl | rfl
    · have h1 : ∀ i, r a (ixA i) 1 = 0 := fun i => ha _ _ (by revert i; decide)
      have h3 : ∀ i, r a (ixA i) 3 = 0 := fun i => ha _ _ (by revert i; decide)
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, h1, h3, zero_mul, add_zero]
      rfl
    · have h1 : ∀ i, r a (ixB i) 0 = 0 := fun i => ha _ _ (by revert i; decide)
      have h3 : ∀ i, r a (ixB i) 2 = 0 := fun i => ha _ _ (by revert i; decide)
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, h1, h3, zero_mul, add_zero,
        zero_add]
      rfl

theorem UpperTheory.V.Ws.nePure_w :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r u, KPair D 𝔞 r u → (∀ g, IsBlock (r g)) →
      ¬ PureW ι (mapRep ((e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK) r) := by
  intro Ω _ _ _ l hl c D hD ι 𝔞 e he r u hp hb ⟨H, M, hH, hM, hP⟩
  obtain ⟨-, f2, -, f4, -⟩ := facts D hD
  obtain ⟨a1, -, a3⟩ := f2 l (Finset.mem_insert_self _ _)
  set φ : 𝔞.V →+* PadicAlgCl l := (e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK with hφ
  set ρ := mapRep φ r with hρ
  have hb' : ∀ g, IsBlock (ρ g) := fun g i j h => by rw [hρ, mapRep_apply, hb g i j h, map_zero]
  have hc : Continuous ρ := smallCont 𝔞 e he _ hp.small
  haveI : CharZero 𝔞.V := φ.charZero
  have hu : adj u * u = 1 := by simpa [IsGSp] using hp.sp
  have hdet : ∀ s ∈ D.Ip l, ((r s).submatrix ixA ixA).det = 𝔞.a c (D.ps 0 s) * 𝔞.a c (D.ps 2 s) ∧
      ((r s).submatrix ixB ixB).det = 𝔞.a c (D.ps 1 s) * 𝔞.a c (D.ps 3 s) := fun s hs => by
    have h := blockDet (maximalIdeal 𝔞.V) (fun i => 𝔞.a c (D.ps i (D.sg l))) u (adj u) (r (D.sg l)) (r s) hu
      (fun i j hij hm => a3 i j hij (by
        rw [← map_sub, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff] at hm
        exact Ideal.Quotient.eq.2 hm))
      (hb _) (fun i j => by
        have h1 := hp.red (D.sg l) i j
        have h2 : 𝔞.a c (D.r0 (D.sg l) i j) = Matrix.diagonal (fun i => 𝔞.a c (D.ps i (D.sg l))) i j := by
          show 𝔞.a c (Matrix.diagonal (fun i => (D.ps i (D.sg l) : c.O)) i j) = _
          rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
          split_ifs <;> simp
        rwa [h2] at h1)
      (hp.flag _ a1) (hp.char _ a1) (hb _) (hp.flag s (Ine_le_Dec _ hs))
    simpa only [hp.inert s hs] using h
  have hps : ∀ i, ∀ s ∈ D.Ip l ⊓ D.ψ.ker ⊓ D.om.ker, φ (𝔞.a c (D.ps i s)) =
      algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l s : ℤ_[l]) ^ D.wts4 i := fun i s hs => by
    rw [f4 i s hs, Units.val_pow_eq_pow_val, map_pow, map_pow]
    exact congrArg (· ^ _) (he.1 c _)
  have key : ∀ (ix : Fin 2 → Fin 4) (hix : ix = ixA ∨ ix = ixB) (i j : Fin 4),
      (∀ s ∈ D.Ip l, ((r s).submatrix ix ix).det = 𝔞.a c (D.ps i s) * 𝔞.a c (D.ps j s)) →
      ∃ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ g ∈ U, ((ρ g).submatrix ix ix).det =
        algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ (D.wts4 i + D.wts4 j) := fun ix hix i j h => by
    have h1 : ∀ g, r g = 1 → blockChar ρ hb' ix hix g = 1 := fun g hg => by
      have : ρ g = ρ 1 := by
        ext i j
        rw [hρ, mapRep_apply, mapRep_apply, hg, map_one r]
      rw [← map_one (blockChar ρ hb' ix hix)]
      exact congrArg (fun X : M4 _ => (X.submatrix ix ix).det) this
    refine wtChar D hD (blockChar ρ hb' ix hix) _ (hc.matrix_submatrix ix ix).matrix_det
      (fun A hA g hg h2 => h1 g (hp.unr A hA g hg h2)) (fun p h2 g hg => h1 g (hp.atP p h2 g hg)) fun s hs => ?_
    rw [pow_add, ← hps i s hs, ← hps j s hs, ← map_mul, ← h s hs.1.1, RingHom.map_det]
    rfl
  obtain ⟨U, hU, hU'⟩ := key ixA (Or.inl rfl) 0 2 fun s hs => (hdet s hs).1
  obtain ⟨W, hW, hW'⟩ := key ixB (Or.inr rfl) 1 3 fun s hs => (hdet s hs).2
  obtain ⟨p, A, f, σ, h1, h2, h3, h4, h5, h6, h7⟩ := frobIn Ω l (H ⊓ (U ⊓ W)) M (hH.inter (hU.inter hW)) hM
  have hp0 : ((p : ℕ) : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 h1.ne_zero
  have h8 := pureDet_w (ι : PadicAlgCl l →+* ℂ) (ρ σ) _ (hb' σ) (hP p h1 h2 A h3 f σ h4 h5.1 h6) (by
    rw [hW' σ h5.2.2, h7]
    simp [hp0])
  rw [hU' σ h5.2.1, hW' σ h5.2.2, h7] at h8
  simp only [map_pow, map_natCast, norm_pow, Complex.norm_natCast] at h8
  have h10 : ((p : ℝ) ^ f) ^ (D.e + 1 + 1) < ((p : ℝ) ^ f) ^ 2 * ((p : ℝ) ^ f) ^ (D.e + 0) := h8
  rw [← pow_add, show 2 + (D.e + 0) = D.e + 1 + 1 by omega] at h10
  exact lt_irrefl _ h10

end
