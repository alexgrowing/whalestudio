import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.NonemptyLocalFramesOfGoodData
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SmoothPtPartOfSmoothPtAssociatedGraded
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.NonemptyCoverOfRelativePresentationSmoothPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExistsSmoothQuotientByWeightedEquations
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExistsPointDerivationFramedCommutatorTangent
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExistsQuotientDerivationOfShaCocycle
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SixBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement.ExM

private theorem lin_desc {O A B M : Type} [CommRing O] [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
    [AddCommGroup M] [Module O M] (p : A →ₗ[O] B) (hp : Function.Surjective p) (δ : A →ₗ[O] M)
    (h : ∀ y, p y = 0 → δ y = 0) : ∃ δ' : B →ₗ[O] M, ∀ y, δ' (p y) = δ y := by
  refine ⟨((LinearMap.ker p).liftQ δ fun y hy => h y hy).comp (p.quotKerEquivOfSurjective hp).symm.toLinearMap, fun y => ?_⟩
  have : (p.quotKerEquivOfSurjective hp).symm (p y) = Submodule.Quotient.mk y := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, this]
  rfl

private theorem alg_desc {O A B M : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing B] [Algebra O B]
    [CommRing M] [Algebra O M] (p : A →ₐ[O] B) (hp : Function.Surjective p) (δ : A →ₐ[O] M)
    (h : ∀ y, p y = 0 → δ y = 0) : ∃ δ' : B →ₐ[O] M, ∀ y, δ' (p y) = δ y := by
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker p) δ fun y hy => h y hy).comp
    (Ideal.quotientKerAlgEquivOfSurjective hp).symm.toAlgHom, fun y => ?_⟩
  have : (Ideal.quotientKerAlgEquivOfSurjective hp).symm (p y) = Ideal.Quotient.mk _ y := by
    rw [AlgEquiv.symm_apply_eq]; rfl
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]
  erw [this]
  rfl

private theorem tower {O X B U : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [DecidableEq X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [CommRing B] [Algebra O B] [CommRing U] [Algebra O U] {WB : WPres O X B} {hB : WB.HasOrigin} {i : B →ₐ[O] U}
    {W : WPres O X U} {h : W.HasOrigin} {τ κ : Type} {e : WB.σ ⊕ τ ≃ W.σ} {wf : κ → X} {n : X → ℕ}
    (C : Cover WB hB i W h e wf n) (hi : (W.origin h).comp i = WB.origin hB)
    {κ₀ : Type} [Fintype κ₀] (t : κ₀ → U) (w₀ : κ₀ → X) (ht : ∀ k, t k ∈ W.part (w₀ k) ∧ W.origin h (t k) = 0)
    (hind : ∀ k, ∃ δ ∈ PtDer (W.origin h) O, δ (t k) ≠ 0 ∧ ∀ k', k' ≠ k → δ (t k') = 0)
    {ι : Type} (s : ι → U) (w₁ : ι → X) (hs : ∀ k, s k ∈ W.part (w₁ k) ∧ W.origin h (s k) = 0) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (_ : IsDomain R) (W' : WPres O X R) (h' : W'.HasOrigin)
      (n' : X → ℕ) (q : κ ⊕ ι → R) (S : Type) (_ : CommRing S) (_ : Algebra O S) (_ : IsCO O S) (π : R →ₐ[O] S)
      (σ : U →ₐ[O] S) (iR : B →ₐ[O] R),
      (∀ s, ∃ s', W'.wt s = W.wt s') ∧ SmoothPt W'.gr (W'.originA h') n' ∧
      (∀ j, n' j + Nat.card {k // w₀ k = j} = n j + Nat.card {t // W.wt (e (.inr t)) = j}) ∧
      (∀ k, q k ∈ W'.part (Sum.elim wf w₁ k) ∧ W'.origin h' (q k) = 0) ∧
      Function.Surjective π ∧ RingHom.ker π = Ideal.span (Set.range q) ∧ Function.Surjective σ ∧
      π.comp iR = σ.comp i ∧ (W'.origin h').comp iR = WB.origin hB ∧ (∀ k, σ (t k) = 0) ∧ (∀ k, σ (s k) = 0) ∧
      (∀ j, ∀ x ∈ W.part j, ∃ f ∈ W'.part j, π f = σ x) ∧ (∀ f x, π f = σ x → W'.origin h' f = W.origin h x) ∧
      ∀ (a : O) (j : X), (∀ k, w₀ k ≠ j) → ∀ Db ∈ QDer (W.origin h) a, ∀ DB ∈ PtDer (WB.origin hB) O,
        HasWt WB.part j DB → (∀ x, Db (i x) = Ideal.Quotient.mk _ (DB x)) →
        (∀ t, W.wt (e (.inr t)) ≠ j → Db (W.z (e (.inr t))) = 0) → (∀ k, Db (s k) = 0) →
        ∃ δ ∈ PtDer (W'.origin h') O, HasWt W'.part j δ ∧ ∀ f x, π f = σ x → Ideal.Quotient.mk _ (δ f) = Db x := by
  have lift : ∀ j, ∀ x ∈ W.part j, ∃ y ∈ C.WP.part j, C.p y = x := fun j x hx => by
    rw [C.part] at hx; exact hx
  have op : ∀ y, W.origin h (C.p y) = C.WP.origin C.org y := fun y => DFunLike.congr_fun C.org_p y
  choose gt hgt1 hgt2 using fun k => lift _ _ (ht k).1
  choose gs hgs1 hgs2 using fun k => lift _ _ (hs k).1
  obtain ⟨R, i1, i2, i3, i4, q, W', h', n', hq, hwt, hpart, ho, hq0, hqd, hsm, hn⟩ :=
    UpperTheory.exists_smooth_quotient_by_weighted_equations O X C.P C.WP C.org _ C.smooth κ₀ gt w₀ (fun k => ⟨hgt1 k, by rw [← op, hgt2, (ht k).2]⟩) (fun k => by
      obtain ⟨δ, h1, h2, h3⟩ := hind k
      refine ⟨δ ∘ₗ C.p.toLinearMap, fun f g => ?_, by simpa [hgt2] using h2, fun k' hk => by simpa [hgt2] using h3 k' hk⟩
      have := h1 (C.p f) (C.p g)
      simpa [op] using this)
  have oq : ∀ y, W'.origin h' (q y) = C.WP.origin C.org y := fun y => DFunLike.congr_fun ho y
  have pg : ∀ u, C.p (C.g u) = 0 := fun u => by
    have : C.g u ∈ RingHom.ker C.p := by rw [C.ker]; exact Ideal.subset_span ⟨u, rfl⟩
    exact this
  let eq : κ ⊕ ι → R := fun k => q (Sum.elim C.g gs k)
  have heq : ∀ k, eq k ∈ W'.part (Sum.elim wf w₁ k) ∧ W'.origin h' (eq k) = 0 := by
    rintro (u | k)
    · exact ⟨by rw [hpart]; exact ⟨_, C.hg u, rfl⟩, by simp only [eq, Sum.elim_inl]; rw [oq, ← op, pg, map_zero]⟩
    · exact ⟨by rw [hpart]; exact ⟨_, hgs1 k, rfl⟩, by simp only [eq, Sum.elim_inr]; rw [oq, ← op, hgs2, (hs k).2]⟩
  let I : Ideal R := Ideal.span (Set.range eq)
  have hI : ∀ x ∈ I, W'.origin h' x = 0 := fun x hx => by
    have : I ≤ RingHom.ker (W'.origin h') := Ideal.span_le.2 (by rintro _ ⟨k, rfl⟩; exact (heq k).2)
    exact this hx
  have hne : I ≠ ⊤ := fun e => by
    have := hI 1 (e ▸ Submodule.mem_top)
    simp at this
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hne
  let π : R →ₐ[O] R ⧸ I := Ideal.Quotient.mkₐ O I
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective O I
  have hπ0 : ∀ k, π (eq k) = 0 := fun k => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨k, rfl⟩)
  obtain ⟨σ, hσ⟩ := alg_desc C.p C.surj (π.comp q) (fun y hy => by
    have h1 : y ∈ RingHom.ker C.p := hy
    rw [C.ker] at h1
    have : Ideal.span (Set.range C.g) ≤ RingHom.ker (π.comp q) :=
      Ideal.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hπ0 (.inl k))
    exact this h1)
  simp only [AlgHom.comp_apply] at hσ
  have key : ∀ y y', π (q y) = σ (C.p y') → q y - q y' ∈ I := fun y y' e => by
    rw [hσ] at e
    exact Ideal.Quotient.eq.1 e
  refine ⟨R, i1, i2, i3, i4, W', h', n', eq, R ⧸ I, inferInstance, inferInstance, co_quot O R _ π hπ, π, σ, q.comp C.iP,
    fun s => ?_, hsm, hn, heq, hπ, Ideal.Quotient.mkₐ_ker O I, fun x => ?_, ?_, ?_, fun k => ?_, fun k => ?_,
    fun j x hx => ?_, fun f x e => ?_, fun a j hj Db hDb DB hDB k1 k2 k3 k4 => ?_⟩
  · obtain ⟨s', e⟩ := hwt s
    obtain ⟨s'', e'⟩ := C.wts s'
    exact ⟨s'', e.trans e'⟩
  · obtain ⟨x, rfl⟩ := hπ x
    obtain ⟨x, rfl⟩ := hq x
    exact ⟨_, hσ x⟩
  · ext x
    have : C.p (C.iP x) = i x := DFunLike.congr_fun C.comp x
    simp only [AlgHom.comp_apply]
    rw [← this, hσ]
  · ext x
    have : C.p (C.iP x) = i x := DFunLike.congr_fun C.comp x
    simp only [AlgHom.comp_apply]
    rw [oq, ← op, this]
    exact DFunLike.congr_fun hi x
  · rw [← hgt2, hσ, hq0, map_zero]
  · rw [← hgs2, hσ]
    exact hπ0 (.inr k)
  · obtain ⟨y, hy, rfl⟩ := lift j x hx
    exact ⟨q y, by rw [hpart]; exact ⟨_, hy, rfl⟩, (hσ y).symm⟩
  · obtain ⟨y, rfl⟩ := hq f
    obtain ⟨y', rfl⟩ := C.surj x
    have := hI _ (key y y' e)
    rw [map_sub, sub_eq_zero] at this
    rw [this, oq, op]
  · obtain ⟨δ, d1, d2, d3⟩ := C.der a j Db hDb DB hDB k1 k2 k3
    obtain ⟨δ', hδ⟩ := lin_desc q.toLinearMap hq δ (hqd δ d1 fun k => d2 _ (hj k) _ (hgt1 k))
    simp only [AlgHom.toLinearMap_apply] at hδ
    have d4 : δ' ∈ PtDer (W'.origin h') O := fun f g => by
      obtain ⟨y, rfl⟩ := hq f
      obtain ⟨y', rfl⟩ := hq g
      rw [← map_mul, hδ, hδ, hδ, oq, oq]
      exact d1 y y'
    refine ⟨δ', d4, fun j' hj' f hf => ?_, fun f x e => ?_⟩
    · rw [hpart] at hf
      obtain ⟨y, hy, rfl⟩ := hf
      exact (hδ y).trans (d2 j' hj' y hy)
    · have hI' : ∀ x ∈ I, Ideal.Quotient.mk (Ideal.span {a}) (δ' x) = 0 := fun x hx => by
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨u | k, rfl⟩ := hx
          · simp only [eq, Sum.elim_inl]; rw [hδ, d3, pg, map_zero]
          · simp only [eq, Sum.elim_inr]; rw [hδ, d3, hgs2, k4]
        | zero => simp
        | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
        | smul b x hx' hx =>
          rw [smul_eq_mul, d4 b x, hI x hx', zero_smul, add_zero, smul_eq_mul, map_mul, hx, mul_zero]
      obtain ⟨y, rfl⟩ := hq f
      obtain ⟨y', rfl⟩ := C.surj x
      have := hI' _ (key y y' e)
      rw [map_sub, map_sub, sub_eq_zero] at this
      rw [this, hδ, d3]

private def p6 : Fin 6 → Fin 4 × Fin 4 := ![(0, 1), (0, 3), (2, 1), (1, 0), (3, 0), (1, 2)]
private def p4 : Fin 4 → Fin 4 × Fin 4 := ![(0, 2), (2, 0), (0, 0), (1, 1)]
private def p2 : Fin 2 → Fin 4 × Fin 4 := ![(0, 2), (2, 0)]
private def wp (x : Fin 4 × Fin 4) : ℤ × ℤ := wt x.1 x.2

private theorem weight_pairs_six_distinct_weights (k : Fin 6) : lamW (p6 k).1 ≠ lamW (p6 k).2 := by revert k; decide
private theorem weight_pairs_six_distinct (k : Fin 6) : (p6 k).1 ≠ (p6 k).2 := by revert k; decide
private theorem weight_pairs_two_distinct (k : Fin 2) : (p2 k).1 ≠ (p2 k).2 := by revert k; decide
private theorem weight_pairs_six_ne_neg_similitude (k : Fin 6) : wp (p6 k) ≠ -wPs := by revert k; decide

private theorem rootVec (O : Type) [CommRing O] (k : Fin 6) :
    ∃ X ∈ sp4 O, ∀ k', X (p6 k').1 (p6 k').2 = if k' = k then 1 else 0 := by
  have : ∀ X : M4 O, adj X = -X → X ∈ sp4 O := fun X h => h
  fin_cases k
  · refine ⟨!![0,1,0,0;0,0,0,0;0,0,0,-1;0,0,0,0], this _ ?_, fun k' => by fin_cases k' <;> simp [p6]⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]
  · refine ⟨!![0,0,0,1;0,0,0,0;0,0,0,0;0,0,0,0], this _ ?_, fun k' => by fin_cases k' <;> simp [p6]⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]
  · refine ⟨!![0,0,0,0;0,0,0,0;0,1,0,0;0,0,0,0], this _ ?_, fun k' => by fin_cases k' <;> simp [p6]⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]
  · refine ⟨!![0,0,0,0;1,0,0,0;0,0,0,0;0,0,-1,0], this _ ?_, fun k' => by fin_cases k' <;> simp [p6]⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]
  · refine ⟨!![0,0,0,0;0,0,0,0;0,0,0,0;1,0,0,0], this _ ?_, fun k' => by fin_cases k' <;> simp [p6]⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]
  · refine ⟨!![0,0,0,0;0,0,1,0;0,0,0,0;0,0,0,0], this _ ?_, fun k' => by fin_cases k' <;> simp [p6]⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

private theorem Xm_wt (O : Type) [CommRing O] (a b : Fin 4) (h : wt a b ≠ -wPs) : Xm O a b = 0 := by
  fin_cases a <;> fin_cases b <;> first | (exfalso; revert h; decide) | simp [Xm, Matrix.single_apply]

private theorem card_prod {A B : Type} (p : B → Prop) : Nat.card {k : A × B // p k.2} = Nat.card A * Nat.card {b // p b} := by
  rw [← Nat.card_prod]
  exact Nat.card_congr ⟨fun x => (x.1.1, ⟨x.1.2, x.2⟩), fun x => ⟨(x.1, x.2.1), x.2.2⟩, fun _ => rfl, fun _ => rfl⟩

private theorem card_sum {A B : Type} [Finite A] [Finite B] (p : A ⊕ B → Prop) :
    Nat.card {k // p k} = Nat.card {a // p (.inl a)} + Nat.card {b // p (.inr b)} := by
  rw [← Nat.card_sum]
  exact Nat.card_congr Equiv.subtypeSum

private theorem dims (b : ℕ) (a n' : ℤ × ℤ → ℕ) (ha : ∀ j, j ≠ 0 → j ≠ wPs → j ≠ -wPs → a j = 0)
    (h : ∀ j, n' j + (b + 1) * Nat.card {k // wp (p6 k) = j} = dimL j + b * dimP j + a j) :
    n' = tDims (1 + b + a (-wPs)) (2 + b + a wPs) (2 + 2 * b + a 0) := by
  funext j
  have h1 := h j
  have h2 := ha j
  rw [Nat.card_eq_fintype_card] at h1
  by_cases hj : j ∈ wts
  · have : ∀ j ∈ wts, (Fintype.card {k // wp (p6 k) = j} = 1 ∧ dimP j = 1 ∧ j ≠ 0 ∧ j ≠ wPs ∧ j ≠ -wPs ∧
        (((j = wAl ∨ j = wBe ∨ j = wTh) ∧ dimL j = 2) ∨ (¬ (j = wAl ∨ j = wBe ∨ j = wTh) ∧ dimL j = 1))) ∨
        (Fintype.card {k // wp (p6 k) = j} = 0 ∧ ¬ (j = wAl ∨ j = wBe ∨ j = wTh) ∧
          ((j = wPs ∧ dimL j = 2 ∧ dimP j = 1) ∨ (j ≠ wPs ∧ j = -wPs ∧ dimL j = 1 ∧ dimP j = 1) ∨
            (j ≠ wPs ∧ j ≠ -wPs ∧ j = 0 ∧ dimL j = 2 ∧ dimP j = 2))) := by decide
    unfold tDims
    rcases this j hj with ⟨e1, e2, e3, e4, e5, ⟨e6, e7⟩ | ⟨e6, e7⟩⟩ | ⟨e1, e2, ⟨e3, e4, e5⟩ | ⟨e3, e4, e5, e6⟩ | ⟨e3, e4, e5, e6, e7⟩⟩
    · rw [if_pos e6]; rw [e1, e2, e7, h2 e3 e4 e5] at h1; omega
    · rw [if_neg e6, if_neg e4, if_neg e5, if_neg e3]; rw [e1, e2, e7, h2 e3 e4 e5] at h1; omega
    · rw [if_neg e2, if_pos e3, ← e3]; rw [e1, e4, e5] at h1; omega
    · rw [if_neg e2, if_neg e3, if_pos e4, ← e4]; rw [e1, e5, e6] at h1; omega
    · rw [if_neg e2, if_neg e3, if_neg e4, if_pos e5, ← e5]; rw [e1, e6, e7] at h1; omega
  · have n : ∀ x ∈ wts, j ≠ x := fun x hx e => hj (e ▸ hx)
    have e1 := n wAl (by decide)
    have e2 := n wBe (by decide)
    have e3 := n wTh (by decide)
    have e4 := n wPs (by decide)
    have e5 := n (-wPs) (by decide)
    have e6 := n 0 (by decide)
    simp only [dimL, dimP, e1, e2, e3, e4, e6, hj, or_self, if_false, h2 e6 e4 e5] at h1
    simp only [tDims, e1, e2, e3, e4, e5, e6, or_self, if_false]
    omega

private theorem enum {ι R X : Type} [Finite ι] (q : ι → R) (w : ι → X) (j : X) (n : ℕ) (h : Nat.card {k // w k = j} = n) :
    ∃ F : Fin n → R, (∀ i, ∃ k, w k = j ∧ F i = q k) ∧ ∀ k, w k = j → q k ∈ Set.range F := by
  let e := Finite.equivFinOfCardEq h
  exact ⟨fun i => q (e.symm i).1, fun i => ⟨_, (e.symm i).2, rfl⟩, fun k hk => ⟨e ⟨k, hk⟩, by simp⟩⟩

private theorem der_const {O A Q : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup Q] [Module O Q]
    {x : A →ₐ[O] O} {δ : A →ₗ[O] Q} (h : δ ∈ PtDer x Q) (a : O) : δ (algebraMap O A a) = 0 := by
  have h1 := h 1 1
  rw [one_mul, map_one x, one_smul, left_eq_add] at h1
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]

private theorem one_mem_part {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (W : WPres O (ℤ × ℤ) A) (a b : Fin 4) :
    (1 : M4 A) a b ∈ W.part (wt a b) := by
  by_cases h : a = b
  · subst h
    rw [Matrix.one_apply_eq, (wt_eq_zero a a).2 rfl]
    exact SetLike.GradedOne.one_mem
  · rw [Matrix.one_apply_ne h]
    exact zero_mem _

private theorem one_entry (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (a b : Fin 4) :
    (1 : M4 A) a b = algebraMap O A ((1 : M4 O) a b) := by
  by_cases h : a = b <;> simp [Matrix.one_apply, h]

private theorem cnt : Nat.card {k // wp (p4 k) = -wPs} = 1 ∧ Nat.card {k // wp (p4 k) = wPs} = 1 ∧
    Nat.card {k // wp (p4 k) = 0} = 2 ∧ Nat.card {k // wp (p2 k) = -wPs} = 1 ∧ Nat.card {k // wp (p2 k) = wPs} = 1 ∧
    Nat.card {k // wp (p2 k) = 0} = 0 ∧ (∀ k, wp (p4 k) = -wPs ∨ wp (p4 k) = wPs ∨ wp (p4 k) = 0) ∧
    ∀ k, wp (p2 k) = -wPs ∨ wp (p2 k) = wPs ∨ wp (p2 k) = 0 := by
  simp only [Nat.card_eq_fintype_card]
  decide

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
  {L : LocBase D} (F : Fr D L)

private theorem diagonal_rep_off_diagonal_zero (g : G ℚ Ω) {a b : Fin 4} (h : a ≠ b) : D.r0 g a b = 0 := Matrix.diagonal_apply_ne _ h

private noncomputable def tOdd (k : D.T × Fin 6) : F.U :=
  (if k.1 = ⟨l, D.residueChar_mem_levelPrimes⟩ then F.r.hom D.ph else F.α k.1) (p6 k.2).1 (p6 k.2).2

private noncomputable def sEq : (D.Sb × Fin 4) ⊕ Fin 2 → F.U
  | .inl k => (F.α ⟨k.1, D.mem_T k.1.2⟩ - 1) (p4 k.2).1 (p4 k.2).2
  | .inr k => D.hEl F.r.hom (p2 k).1 (p2 k).2

private def wEq (D : Raw Ω c) : (D.Sb × Fin 4) ⊕ Fin 2 → ℤ × ℤ := Sum.elim (fun k => wp (p4 k.2)) fun k => wp (p2 k)

private theorem at0a (v : D.T) (a b : Fin 4) : F.W.origin F.org (F.α v a b) = (1 : M4 c.O) a b :=
  congrFun (congrFun (F.at0α v) a) b

private theorem tOdd_mem (k : D.T × Fin 6) : tOdd F k ∈ F.W.part (wp (p6 k.2)) ∧ F.W.origin F.org (tOdd F k) = 0 := by
  unfold tOdd
  split_ifs
  · exact ⟨F.homr _ _ _, (F.at0r _ _ _).trans (diagonal_rep_off_diagonal_zero _ (weight_pairs_six_distinct _))⟩
  · exact ⟨F.homα _ _ _, (at0a F _ _ _).trans (Matrix.one_apply_ne (weight_pairs_six_distinct _))⟩

private theorem hEl_apply {R : Type} [CommRing R] [Algebra c.O R] (r : G ℚ Ω →* M4 R) (a b : Fin 4) :
    D.hEl r a b = r D.g0 a b + (D.th D.g0 : c.O) • r D.g0⁻¹ a b := by
  rw [Algebra.smul_def]; rfl

private theorem sEq_mem (k) : sEq F k ∈ F.W.part (wEq D k) ∧ F.W.origin F.org (sEq F k) = 0 := by
  rcases k with k | k
  · refine ⟨sub_mem (F.homα _ _ _) (one_mem_part F.W _ _), ?_⟩
    simp only [sEq, Matrix.sub_apply]
    rw [map_sub, at0a, one_entry c.O F.U, AlgHom.commutes]
    exact sub_self _
  · simp only [sEq, hEl_apply]
    refine ⟨add_mem (F.homr _ _ _) (Submodule.smul_mem _ _ (F.homr _ _ _)), ?_⟩
    rw [map_add, map_smul, F.at0r, F.at0r, diagonal_rep_off_diagonal_zero _ (weight_pairs_two_distinct _), diagonal_rep_off_diagonal_zero _ (weight_pairs_two_distinct _), smul_zero, add_zero]

private theorem ph_ne (hD : D.Good) (k : Fin 6) : (D.ps (p6 k).2 D.ph : c.O) - (D.ps (p6 k).1 D.ph : c.O) ≠ 0 := by
  obtain ⟨-, h2, -, -, -, -, -, -, -, h3, -⟩ := facts D hD
  have e : ∀ i, Raw.bar (D.ps i) D.ph = Raw.bar (D.ps i) (D.sg l) := fun i => by
    have := congrFun (congrFun h3 i) i
    simpa [Raw.rbar, Raw.r0, diagRep] using this
  intro h
  apply (h2 l D.residueChar_mem_levelPrimes).2.2 _ _ (weight_pairs_six_distinct_weights k)
  rw [← e, ← e, Raw.bar, Raw.bar, sub_eq_zero.1 h]

private theorem tOdd_ind (hD : D.Good) (k : D.T × Fin 6) :
    ∃ δ ∈ PtDer (F.W.origin F.org) c.O, δ (tOdd F k) ≠ 0 ∧ ∀ k', k' ≠ k → δ (tOdd F k') = 0 := by
  classical
  obtain ⟨v, k⟩ := k
  obtain ⟨X, hX, hk⟩ := rootVec c.O k
  by_cases hv : v = ⟨l, D.residueChar_mem_levelPrimes⟩
  · obtain ⟨δ, d1, d2, d3⟩ := UpperTheory.exists_pointDerivation_framed_commutator_tangent D hD L F X hX 0 (fun _ => zero_mem _) rfl
    have e : ∀ k', δ (F.r.hom D.ph (p6 k').1 (p6 k').2) =
        (if k' = k then 1 else 0) * ((D.ps (p6 k').2 D.ph : c.O) - (D.ps (p6 k').1 D.ph : c.O)) := fun k' => by
      rw [d2, ← hk]
      simp only [Raw.r0, diagRep, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
      ring
    refine ⟨δ, d1, ?_, ?_⟩
    · simp only [tOdd, if_pos hv]
      rw [e, if_pos rfl, one_mul]
      exact ph_ne hD k
    · rintro ⟨v', k'⟩ hne
      unfold tOdd
      split_ifs with h
      · rw [e, if_neg, zero_mul]
        rintro rfl
        exact hne (Prod.ext (h.trans hv.symm) rfl)
      · rw [d3]; rfl
  · obtain ⟨δ, d1, d2, d3⟩ := UpperTheory.exists_pointDerivation_framed_commutator_tangent D hD L F 0 (zero_mem _) (fun v' => if v' = v then X else 0)
      (fun v' => by split_ifs; exacts [hX, zero_mem _]) (if_neg (Ne.symm hv))
    refine ⟨δ, d1, ?_, ?_⟩
    · simp only [tOdd, if_neg hv]
      rw [d3, if_pos rfl, hk, if_pos rfl]
      exact one_ne_zero
    · rintro ⟨v', k'⟩ hne
      unfold tOdd
      split_ifs with h
      · rw [d2, zero_mul, mul_zero, sub_zero]; rfl
      · rw [d3]
        by_cases h' : v' = v
        · rw [if_pos h', hk, if_neg]
          rintro rfl
          exact hne (Prod.ext h' rfl)
        · rw [if_neg h']; rfl

variable {S : Type} [CommRing S] [Algebra c.O S] [IsCO c.O S] (σ : F.U →ₐ[c.O] S)

private theorem off_mem {n : M4 S} {m : M4 (ResidueField c.O)} (h : ∀ a b, res c.O S (n a b) = m a b)
    (hm : ∀ a b, a ≠ b → m a b = 0) (a b : Fin 4) (hab : a ≠ b) : n a b ∈ maximalIdeal S :=
  (res_eq_zero_iff c.O S _).1 ((h a b).trans (hm a b hab))

private theorem al_one (ht : ∀ k, σ (tOdd F k) = 0) (hs : ∀ k, σ (sEq F k) = 0) (v : D.T) : (F.α v).map σ = 1 := by
  by_cases hv : v = ⟨l, D.residueChar_mem_levelPrimes⟩
  · rw [hv, F.fr.atL]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · obtain ⟨p, hp⟩ := v
    have hp' : p ∈ D.Sb := (Finset.mem_insert.1 hp).resolve_left fun e => hv (Subtype.ext e)
    have h1 := Ex.isGSp_map (σ : F.U →+* S) (F.fr.sp ⟨p, hp⟩).1
    rw [map_one] at h1
    have t : ∀ k, σ (F.α ⟨p, hp⟩ (p6 k).1 (p6 k).2) = 0 := fun k => by
      have := ht (⟨p, hp⟩, k)
      simpa only [tOdd, if_neg hv] using this
    have s : ∀ k, σ (F.α ⟨p, hp⟩ (p4 k).1 (p4 k).2) = (1 : M4 S) (p4 k).1 (p4 k).2 := fun k => by
      have := hs (.inl (⟨p, hp'⟩, k))
      simp only [sEq, Matrix.sub_apply] at this
      rw [map_sub, sub_eq_zero, one_entry c.O F.U, AlgHom.commutes, ← one_entry] at this
      exact this
    refine (sixBlock S 1 _ isUnit_one h1 (off_mem (c := c) (m := 1) (fun a b => ?_) fun a b => Matrix.one_apply_ne)
      (t 0) (t 1) (t 2) (t 3) (t 4) (t 5)).2 rfl (s 0) (s 1) (s 2) (s 3)
    exact (res_map σ _).trans (congrFun (congrFun (F.fr.sp ⟨p, hp⟩).2 a) b)

private theorem nrm (ht : ∀ k, σ (tOdd F k) = 0) (hs : ∀ k, σ (sEq F k) = 0) : D.Nrm (F.r.map σ).hom := by
  refine ⟨?_, ?_, ?_⟩
  · have t : ∀ k, σ (F.r.hom D.ph (p6 k).1 (p6 k).2) = 0 := fun k => by
      have := ht (⟨l, D.residueChar_mem_levelPrimes⟩, k)
      simpa only [tOdd, if_pos] using this
    refine (sixBlock S _ _ ((D.th D.ph).isUnit.map _) (Ex.mult_map D σ F.r F.fr.mult D.ph)
      (off_mem (c := c) ((F.r.map σ).red D.ph) fun a b h => ?_) (t 0) (t 1) (t 2) (t 3) (t 4) (t 5)).1
    show residue c.O (D.r0 D.ph a b) = 0
    rw [diagonal_rep_off_diagonal_zero _ h, map_zero]
  · rw [Ex.hEl_map]; exact hs (.inr 0)
  · rw [Ex.hEl_map]; exact hs (.inr 1)

private theorem loc_eq (hα : ∀ v, (F.α v).map σ = 1) (v : D.T) : (L.ρ v).map (σ.comp F.i) = D.loc (F.r.map σ) v := by
  refine Lift.ext (MonoidHom.ext fun g => ?_)
  have h := congrArg (σ : F.U →+* S).mapMatrix (F.fr.loc v g)
  have h1 : (σ : F.U →+* S).mapMatrix (F.α v) = 1 := hα v
  rw [map_mul, map_mul, h1, mul_one, one_mul] at h
  exact h.symm

private theorem isFr_map {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] (y : F.U →ₐ[c.O] R) :
    IsFr L (y.comp F.i) (F.r.map y) fun v => (F.α v).map y := by
  refine ⟨Ex.mult_map D y _ F.fr.mult, Ex.unr_map D y _ F.fr.unr, fun v => ⟨?_, ?_⟩, ?_, fun v g => ?_⟩
  · have h1 := Ex.isGSp_map (y : F.U →+* R) (F.fr.sp v).1
    rwa [map_one] at h1
  · ext a b
    exact (res_map y _).trans (congrFun (congrFun (F.fr.sp v).2 a) b)
  · show (F.α _).map y = 1
    rw [F.fr.atL]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · have h := congrArg (y : F.U →+* R).mapMatrix (F.fr.loc v g)
    rw [map_mul, map_mul] at h
    exact h

private theorem gen (hσ : Function.Surjective σ) (hα : ∀ v, (F.α v).map σ = 1) : (F.r.map σ).Generates := by
  intro R _ _ _ f f' h
  have a : ∀ (f : S →ₐ[c.O] R) v, (F.α v).map (f.comp σ) = 1 := fun f v => by
    have : (F.α v).map (f.comp σ) = ((F.α v).map σ).map f := rfl
    rw [this, hα]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have h' : F.r.map (f.comp σ) = F.r.map (f'.comp σ) := h
  have hi : (f.comp σ).comp F.i = (f'.comp σ).comp F.i := by
    refine (L.univ R _ (L.eqs.map ((f.comp σ).comp F.i))).unique (fun _ => rfl) fun v => ?_
    show (L.ρ v).map _ = (L.ρ v).map _
    rw [loc_eq F _ (a f), loc_eq F _ (a f'), h']
  have := (F.univ R _ _ _ (isFr_map F (f.comp σ))).unique (y₁ := f.comp σ) (y₂ := f'.comp σ) ⟨rfl, rfl, fun _ => rfl⟩
    ⟨hi.symm, h'.symm, fun v => (a f' v).trans (a f v).symm⟩
  ext x
  obtain ⟨x, rfl⟩ := hσ x
  exact DFunLike.congr_fun this x

end

end UpperTheory.V.GradeZeroInterpolatingElement.ExM

open UpperTheory.V.GradeZeroInterpolatingElement.ExM in
theorem UpperTheory.V.GradeZeroInterpolatingElement.exModel :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → LemmaP → PhiCond D.Gam l → D.Nums → Nonempty (LocBase D) → Nonempty (Model D) := by
  intro Ω _ _ _ l _ c D hD hP hΦ hN ⟨L⟩
  obtain ⟨F⟩ := UpperTheory.nonempty_local_frames_of_good_data D hD hP hΦ hN L
  obtain ⟨C⟩ := UpperTheory.nonempty_cover_of_relative_presentation_smoothPt c.O (ℤ × ℤ) L.B F.U L.W L.org F.i F.W F.org F.τ F.κ F.e F.f F.wf _ F.rel
    (UpperTheory.smoothPt_part_of_smoothPt_associatedGraded c.O (ℤ × ℤ) L.B L.W L.org _ L.smooth)
  obtain ⟨R, i1, i2, i3, i4, W, h, n', q, S, j1, j2, j3, π, σ, iR, hwt, hsm, hn, hq, hπ, hker, hσ, hcomp, horg, ht, hs, hhom,
    hat, hder⟩ := tower C F.at0i (tOdd F) (fun k => wp (p6 k.2)) (tOdd_mem F) (tOdd_ind F hD) (sEq F) (wEq D) (sEq_mem F)
  have hT : Nat.card D.T = D.Sb.card + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Raw.T, Finset.card_insert_of_notMem]
    intro hl
    obtain ⟨h1, -⟩ := facts D hD
    exact (h1 l hl).2.1 rfl
  have hb : Nat.card D.Sb = D.Sb.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have hn' := dims D.Sb.card (fun j => Nat.card {t // F.W.wt (F.e (.inr t)) = j}) n' F.numz fun j => by
    rw [← hT, ← card_prod (fun k => wp (p6 k) = j)]
    exact hn j
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := cnt
  have hc : ∀ j, Nat.card {k // Sum.elim F.wf (wEq D) k = j} = Nat.card {u // F.wf u = j} +
      (D.Sb.card * Nat.card {k // wp (p4 k) = j} + Nat.card {k // wp (p2 k) = j}) := fun j => by
    rw [card_sum, card_sum (fun k => Sum.elim F.wf (wEq D) (.inr k) = j), ← hb, ← card_prod (fun k => wp (p4 k) = j)]
    rfl
  obtain ⟨Fq, f1, f2⟩ := enum q _ (-wPs) (1 + D.Sb.card + Nat.card {t // F.W.wt (F.e (.inr t)) = -wPs} + 1) (by
    rw [hc, F.numf, c1, c4, if_neg (by decide), if_pos (Or.inr rfl)]; omega)
  obtain ⟨Eq, e1, e2⟩ := enum q _ wPs (2 + D.Sb.card + Nat.card {t // F.W.wt (F.e (.inr t)) = wPs}) (by
    rw [hc, F.numf, c2, c5, if_neg (by decide), if_pos (Or.inl rfl)]; omega)
  obtain ⟨Zq, z1, z2⟩ := enum q (Sum.elim F.wf (wEq D)) 0 (2 + 2 * D.Sb.card + Nat.card {t // F.W.wt (F.e (.inr t)) = 0}) (by
    rw [hc, F.numf, c3, c6, if_pos rfl]; omega)
  have hw : ∀ k, Sum.elim F.wf (wEq D) k = -wPs ∨ Sum.elim F.wf (wEq D) k = wPs ∨ Sum.elim F.wf (wEq D) k = 0 := by
    rintro (u | k | k)
    · by_contra hne
      simp only [not_or, Sum.elim_inl] at hne
      have h1 := F.numf (F.wf u)
      rw [F.numz _ hne.2.2 hne.2.1 hne.1, if_neg hne.2.2, if_neg (not_or.2 ⟨hne.2.1, hne.1⟩)] at h1
      haveI : Nonempty {u' // F.wf u' = F.wf u} := ⟨⟨u, rfl⟩⟩
      exact Nat.card_pos.ne' h1
    · exact c7 _
    · exact c8 _
  have hα := al_one F σ ht hs
  have hloc : ∀ v : D.T, ((L.ρ v).map iR).map π = D.loc (F.r.map σ) v := fun v => by
    rw [← loc_eq F σ hα v, ← hcomp]; rfl
  have hx : ∀ (v : D.T) g a b, W.origin h (((L.ρ v).map iR).hom g a b) = D.r0At v g a b := fun v g a b =>
    (DFunLike.congr_fun horg _).trans (L.at0 v g a b)
  refine ⟨{ R := R, W := W, wt_mem := fun s => ?_, org := h, r := _, r' := _, m := _, one_le := by omega
            smooth := hn' ▸ hsm, F := Fq, E := Eq, Z := Zq, hF := fun i => ?_, hE := fun i => ?_, hZ := fun i => ?_
            S := S, π := π, surj := hπ, ker := hker.trans (congrArg Ideal.span ?_), ru := F.r.map σ, pt := ?_
            gen := gen F σ hσ hα, hom := fun g i j => hhom _ _ (F.homr g i j)
            at0 := fun g i j f e => (hat f _ e).trans (F.at0r g i j), der := fun a z _ hz => ?_ }⟩
  · obtain ⟨s', e⟩ := hwt s
    obtain ⟨s' | t, rfl⟩ := F.e.surjective s'
    · rw [e, F.rel.1]; exact L.wt_mem _
    · obtain ⟨a, b, e', -⟩ := F.vars t
      rw [e, e']; exact wt_mem a b
  · obtain ⟨k, h1, h2⟩ := f1 i
    rw [h2, ← h1]; exact (hq k).1
  · obtain ⟨k, h1, h2⟩ := e1 i
    rw [h2, ← h1]; exact (hq k).1
  · obtain ⟨k, h1, h2⟩ := z1 i
    rw [h2, ← h1]; exact hq k
  · ext x
    constructor
    · rintro ⟨k, rfl⟩
      rcases hw k with h1 | h1 | h1
      exacts [.inl (.inl (f2 k h1)), .inl (.inr (e2 k h1)), .inr (z2 k h1)]
    · rintro ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
      · obtain ⟨k, -, h2⟩ := f1 i; exact ⟨k, h2.symm⟩
      · obtain ⟨k, -, h2⟩ := e1 i; exact ⟨k, h2.symm⟩
      · obtain ⟨k, -, h2⟩ := z1 i; exact ⟨k, h2.symm⟩
  · exact ⟨Ex.mult_map D σ _ F.fr.mult, Ex.unr_map D σ _ F.fr.unr, nrm F σ ht hs,
      ⟨R, i1, i2, i3, i4, _, (L.eqs.map iR).1, ⟨_, hx ⟨l, D.residueChar_mem_levelPrimes⟩⟩, π, hloc _⟩,
      fun p hp => ⟨R, i1, i2, i3, i4, _, (L.eqs.map iR).2 p hp, ⟨_, hx ⟨p, D.mem_T hp⟩⟩, π, hloc _⟩⟩
  · obtain ⟨Db, b1, DB, b2, b3, b4, b5, b6⟩ := UpperTheory.exists_quotientDerivation_of_shaCocycle D hD L F a z hz
    have b7 : ∀ g i j, Db (F.r.hom g i j) = Ideal.Quotient.mk _ (Xm c.O i j * D.ps j g) * z g := fun g i j => by
      rw [b5, Raw.r0, diagRep, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.mul_diagonal]
    have b8 : ∀ v i j, Db ((F.α v - 1) i j) = 0 := fun v i j => by
      rw [Matrix.sub_apply, map_sub, b6, one_entry c.O, der_const b1, sub_self]
    have z1 : z 1 = 0 := by
      have := hz.coc 1 1
      rw [mul_one, map_one, Units.val_one, map_one, one_mul, left_eq_add] at this
      exact this
    have z2 : z D.g0⁻¹ = 0 := by
      have := hz.coc D.g0⁻¹ D.g0
      rw [inv_mul_cancel, z1, hz.g0, mul_zero, add_zero] at this
      exact this.symm
    obtain ⟨δ, d1, d2, d3⟩ := hder a (-wPs) (fun k => weight_pairs_six_ne_neg_similitude k.2) Db b1 DB b2 b3 b4 (fun t ht => by
      obtain ⟨i, j, e, ⟨g, e'⟩ | ⟨v, e'⟩⟩ := F.vars t
      · rw [e', map_sub, der_const b1, b7, Xm_wt _ _ _ (e ▸ ht), zero_mul, map_zero, zero_mul, sub_self]
      · rw [e', b8]) (by
      rintro (k | k)
      · exact b8 _ _ _
      · simp only [sEq, hEl_apply]
        rw [map_add, map_smul, b7, b7, hz.g0, z2, mul_zero, mul_zero, smul_zero, add_zero])
    refine ⟨δ, d1, d2, fun f hf => Ideal.Quotient.eq_zero_iff_mem.1 ?_, fun g f => ⟨fun e => ?_, fun e => ?_⟩⟩
    · rw [d3 f 0 (hf.trans (map_zero σ).symm), map_zero]
    · rw [d3 f _ e, b7, show Xm c.O 2 0 = 1 by simp [Xm], one_mul]; rfl
    · rw [d3 f _ e, b7, show Xm c.O 3 1 = 1 by simp [Xm], one_mul]; rfl
