import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IsUnitOfValEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.WeakApprox
import Development.AbelianVarietyTheory.Proofs.AlgebraicCurves.PlacesRestrictInjective
import Formalism.LocalToGlobal.ProjectiveLattices.LocalIntegralPolynomials.ExistsValuationAdaptedIndex
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing MvPolynomial

noncomputable section

namespace GlobalTheory.GenSep

section Subst

variable {Ω : Type} [Field Ω] {D N : ℕ}

abbrev Free (D N : ℕ) (j0 : Fin N) : Type := {p : Fin (D + 1) × Fin N // p.1 = 0 ∨ p.2 ≠ j0}

theorem card_free (j0 : Fin N) : Fintype.card (Fin (D + 1) × Fin N) = Fintype.card (Free D N j0) + D := by
  classical
  have h1 := Fintype.card_subtype_compl (fun p : Fin (D + 1) × Fin N => p.1 = 0 ∨ p.2 ≠ j0)
  have h2 : Fintype.card (Fin D) = Fintype.card {p : Fin (D + 1) × Fin N // ¬ (p.1 = 0 ∨ p.2 ≠ j0)} := by
    refine Fintype.card_of_bijective (f := fun i => ⟨(i.succ, j0), by simp⟩) ⟨?_, ?_⟩
    · intro a b hab
      simpa using hab
    · rintro ⟨⟨i, k⟩, hp⟩
      simp only [not_or, ne_eq, not_not] at hp
      obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hp.1
      exact ⟨i', Subtype.ext (Prod.ext rfl hp.2.symm)⟩
  have h3 := Fintype.card_subtype_le (fun p : Fin (D + 1) × Fin N => p.1 = 0 ∨ p.2 ≠ j0)
  rw [Fintype.card_fin] at h2
  have h4 : Fintype.card (Free D N j0) =
    Fintype.card {p : Fin (D + 1) × Fin N // p.1 = 0 ∨ p.2 ≠ j0} := by congr
  omega

open Classical in

def subst (x : Fin N → Ω) (j0 : Fin N) (p : Fin (D + 1) × Fin N) : MvPolynomial (Free D N j0) Ω :=
  if h : p.1 = 0 ∨ p.2 ≠ j0 then X ⟨p, h⟩
  else -∑ k : {k : Fin N // k ≠ j0}, C (x k / x j0) * X ⟨(p.1, k), Or.inr k.2⟩

theorem subst_mem (x : Fin N → Ω) (j0 : Fin N) {W : Subring Ω} (hW : ∀ k, x k / x j0 ∈ W)
    (p : Fin (D + 1) × Fin N) : subst x j0 p ∈ Formalism.L2.Pj.LocAlg.intPoly _ W := by
  unfold subst
  split_ifs
  · exact Formalism.L2.Pj.LocAlg.X_mem_intPoly _
  · exact Subring.neg_mem _ (sum_mem fun k _ => Subring.mul_mem _
      (Formalism.L2.Pj.LocAlg.C_mem_intPoly (hW _)) (Formalism.L2.Pj.LocAlg.X_mem_intPoly _))

theorem aeval_subst {F : Type} [Field F] [Algebra Ω F] (x : Fin N → Ω) (j0 : Fin N) (hx : x j0 ≠ 0)
    (u : Fin (D + 1) × Fin N → F) (hrel : ∀ i : Fin D, ∑ k, u (i.succ, k) * algebraMap Ω F (x k) = 0)
    (p : Fin (D + 1) × Fin N) : aeval (fun s : Free D N j0 => u s.1) (subst x j0 p) = u p := by
  classical
  unfold subst
  split_ifs with h
  · simp
  · obtain ⟨i, k⟩ := p
    simp only [not_or, ne_eq, not_not] at h
    obtain ⟨h1, rfl⟩ := h
    obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 h1
    have hr := hrel i'
    rw [Fintype.sum_eq_add_sum_subtype_ne _ k] at hr
    have hx' : algebraMap Ω F (x k) ≠ 0 := (map_ne_zero _).2 hx
    simp only [map_neg, map_sum, map_mul, aeval_C, aeval_X, map_div₀]
    apply mul_right_cancel₀ hx'
    rw [neg_mul, Finset.sum_mul, eq_comm, ← add_eq_zero_iff_eq_neg, ← hr]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    field_simp

end Subst

section Gauss

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {Ω : Type} [Field Ω] [Algebra K Ω]
  {D N : ℕ}

set_option maxHeartbeats 1000000 in

theorem free_indep (htr : Algebra.trdeg K Ω = D) (x : Fin N → Ω) (j0 : Fin N) (hx : x j0 ≠ 0)
    {F : Type} [Field F] [Algebra Ω F] (w : AddValuation F (WithTop ℤ)) (u : Fin (D + 1) × Fin N → F)
    (hu : ∀ p, u p ∈ vRing w)
    (h0 : ∀ P : MvPolynomial (Fin (D + 1) × Fin N) (𝓞 K),
      0 < w (eval₂ ((algebraMap Ω F).comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) u P) ↔
        ∀ α, P.coeff α ∈ la.asIdeal)
    (h1 : ∀ a : 𝓞 K, 0 ≤ w (((algebraMap Ω F).comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) a))
    (hrel : ∀ i : Fin D, ∑ k, u (i.succ, k) * algebraMap Ω F (x k) = 0)
    (hint : ∀ k, x k / x j0 ∈ ((vRing w).comap (algebraMap Ω F)).toSubring) :
    letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω F)
    AlgebraicIndependent (ResidueField ((vRing w).comap (algebraMap Ω F)))
      (fun s : Free D N j0 => residue (vRing w) ⟨u s.1, hu s.1⟩) :=
  (ReciprocityTheory.MultiplicativeHeights.Closed.residueTrdeg K Ω F D htr (Free D N j0) (fun s => u s.1) (vRing w)
    (fun s => hu s.1) (Fin (D + 1) × Fin N) (fun p => ⟨u p, hu p⟩) (subst x j0)
    (fun p α => subst_mem x j0 hint p α)
    (card_free j0) (aeval_subst x j0 hx u hrel) (ValuationResidueLemmas.indep_u (K := K) (Ω := Ω) w la (fun p => ⟨u p, hu p⟩) h0 h1)).2.2

set_option maxHeartbeats 1000000 in

theorem gauss_one (htr : Algebra.trdeg K Ω = D) (x : Fin N → Ω) (j0 : Fin N) (hx : x j0 ≠ 0)
    {F : Type} [Field F] (w : AddValuation F (WithTop ℤ)) (ι : Ω →+* F) (u : Fin (D + 1) × Fin N → F)
    (h0 : ∀ P : MvPolynomial (Fin (D + 1) × Fin N) (𝓞 K),
      0 < w (eval₂ (ι.comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) u P) ↔ ∀ α, P.coeff α ∈ la.asIdeal)
    (h1 : ∀ P : MvPolynomial (Fin (D + 1) × Fin N) (𝓞 K),
      0 ≤ w (eval₂ (ι.comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) u P))
    (hrel : ∀ i : Fin D, ∑ k, u (i.succ, k) * ι (x k) = 0) (hint : ∀ k, 0 ≤ w (ι (x k / x j0)))
    (P : MvPolynomial (Fin (D + 1) × Fin N) Ω) :
    (aeval (subst x j0) P = 0 → eval₂ ι u P = 0) ∧
    ∀ α ∈ (aeval (subst x j0) P).support,
      (∀ β ∈ (aeval (subst x j0) P).support,
        w (ι ((aeval (subst x j0) P).coeff α)) ≤ w (ι ((aeval (subst x j0) P).coeff β))) →
      w (eval₂ ι u P) = w (ι ((aeval (subst x j0) P).coeff α)) := by
  letI : Algebra Ω F := ι.toAlgebra
  have hu : ∀ p, u p ∈ vRing w := fun p => by
    have := h1 (X p)
    rw [eval₂_X] at this
    exact this
  have hs := aeval_subst x j0 hx u hrel
  have hP : eval₂ ι u P = aeval (fun s : Free D N j0 => u s.1) (aeval (subst x j0) P) := by
    have h : (aeval (fun s : Free D N j0 => u s.1)).comp (aeval (subst x j0)) = aeval (R := Ω) u :=
      algHom_ext fun p => by rw [AlgHom.comp_apply, aeval_X, aeval_X, hs]
    have h2 := DFunLike.congr_fun h P
    rw [AlgHom.comp_apply] at h2
    rw [h2, aeval_def]
    rfl
  have RT := free_indep la htr x j0 hx w u hu h0 (fun a => by
    have := h1 (C a)
    rw [eval₂_C] at this
    exact this) hrel (fun k => hint k)
  refine ⟨fun h => by rw [hP, h, map_zero], fun α hα hmin => ?_⟩
  rw [hP]
  exact GlobalTheory.PlaceRestrict.val_aeval_eq_coeff (Ω := Ω) w (fun s : Free D N j0 => u s.1) (fun s => hu s.1) RT
    (aeval (subst x j0) P) α hα hmin

end Gauss

section Pair

variable {Ω F F' : Type} [Field Ω] [Field F] [Field F'] (w : AddValuation F (WithTop ℤ))
  (w' : AddValuation F' (WithTop ℤ)) (ι : Ω →+* F) (ι' : Ω →+* F')

def Att (z : F × F') : Prop := ∃ a : Ω, w z.1 = w (ι a) ∧ w' z.2 = w' (ι' a)

theorem le_mul_of {a b : ℤ} {x y : F} (hx : (a : WithTop ℤ) ≤ w x) (hy : (b : WithTop ℤ) ≤ w y) {c : ℤ}
    (hc : c ≤ a + b) : (c : WithTop ℤ) ≤ w (x * y) := by
  rw [AddValuation.map_mul]
  exact (by exact_mod_cast hc : (c : WithTop ℤ) ≤ (a : WithTop ℤ) + b).trans (add_le_add hx hy)

theorem exists_lower (x : F) : ∃ m : ℕ, ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ w x := by
  induction h : w x using WithTop.recTopCoe with
  | top => exact ⟨0, le_top⟩
  | coe a => exact ⟨a.natAbs, by exact_mod_cast (by omega : -(a.natAbs : ℤ) ≤ a)⟩

theorem approx_mul {r s a b : F} {m : ℕ} {n : ℤ} (hr : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ w r)
    (hs : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ w s) (ha : (((n.natAbs + m : ℕ) : ℤ) : WithTop ℤ) ≤ w (r - a))
    (hb : (((n.natAbs + m : ℕ) : ℤ) : WithTop ℤ) ≤ w (s - b)) : (n : WithTop ℤ) ≤ w (r * s - a * b) := by
  have e : r * s - a * b = r * (s - b) + (r - a) * s - (r - a) * (s - b) := by ring
  rw [e]
  refine w.map_le_sub (w.map_le_add ?_ ?_) ?_
  · exact le_mul_of w hr hb (by omega)
  · exact le_mul_of w ha hs (by omega)
  · exact le_mul_of w ha hb (by omega)

def lim (A : Subring (F × F')) : Subring (F × F') where
  carrier := {z | ∀ n : ℤ, ∃ a ∈ A, (n : WithTop ℤ) ≤ w (z.1 - a.1) ∧ (n : WithTop ℤ) ≤ w' (z.2 - a.2)}
  one_mem' n := ⟨1, A.one_mem, by simp, by simp⟩
  zero_mem' n := ⟨0, A.zero_mem, by simp, by simp⟩
  add_mem' := by
    intro y z hy hz n
    obtain ⟨a, ha, h1, h2⟩ := hy n
    obtain ⟨b, hb, h3, h4⟩ := hz n
    refine ⟨a + b, A.add_mem ha hb, ?_, ?_⟩
    · rw [Prod.fst_add, Prod.fst_add, add_sub_add_comm]; exact w.map_le_add h1 h3
    · rw [Prod.snd_add, Prod.snd_add, add_sub_add_comm]; exact w'.map_le_add h2 h4
  neg_mem' := by
    intro y hy n
    obtain ⟨a, ha, h1, h2⟩ := hy n
    refine ⟨-a, A.neg_mem ha, ?_, ?_⟩
    · rw [Prod.fst_neg, Prod.fst_neg, neg_sub_neg, AddValuation.map_sub_swap]; exact h1
    · rw [Prod.snd_neg, Prod.snd_neg, neg_sub_neg, AddValuation.map_sub_swap]; exact h2
  mul_mem' := by
    intro y z hy hz n
    obtain ⟨m1, hm1⟩ := exists_lower w y.1
    obtain ⟨m2, hm2⟩ := exists_lower w z.1
    obtain ⟨m3, hm3⟩ := exists_lower w' y.2
    obtain ⟨m4, hm4⟩ := exists_lower w' z.2
    have hle : ∀ k : ℕ, k ≤ m1 + m2 + m3 + m4 →
        ((-((m1 + m2 + m3 + m4 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤ ((-(k : ℤ) : ℤ) : WithTop ℤ) := fun k hk =>
      WithTop.coe_le_coe.2 (by omega)
    obtain ⟨a, ha, h1, h2⟩ := hy ((n.natAbs + (m1 + m2 + m3 + m4) : ℕ) : ℤ)
    obtain ⟨b, hb, h3, h4⟩ := hz ((n.natAbs + (m1 + m2 + m3 + m4) : ℕ) : ℤ)
    exact ⟨a * b, A.mul_mem ha hb,
      approx_mul w ((hle _ (by omega)).trans hm1) ((hle _ (by omega)).trans hm2) h1 h3,
      approx_mul w' ((hle _ (by omega)).trans hm3) ((hle _ (by omega)).trans hm4) h2 h4⟩

theorem le_lim (A : Subring (F × F')) : A ≤ lim w w' A := fun z hz _ => ⟨z, hz, by simp, by simp⟩

theorem val_eq_of_close {r a : F} {n : ℤ} (h : ((n + 1 : ℤ) : WithTop ℤ) ≤ w (r - a)) :
    w r = n ↔ w a = n := by
  have hlt : (n : WithTop ℤ) < w (r - a) := lt_of_lt_of_le (WithTop.coe_lt_coe.2 (by omega)) h
  constructor
  · intro hr
    have : a = r + -(r - a) := by ring
    rw [this, AddValuation.map_add_eq_of_lt_left _ (by rw [AddValuation.map_neg, hr]; exact hlt), hr]
  · intro ha
    have : r = a + (r - a) := by ring
    rw [this, AddValuation.map_add_eq_of_lt_left _ (by rw [ha]; exact hlt), ha]

theorem att_lim (heq : ∀ a, w (ι a) = w' (ι' a)) {A : Subring (F × F')} (hA : ∀ z ∈ A, Att w w' ι ι' z) :
    ∀ z ∈ lim w w' A, Att w w' ι ι' z := by
  intro z hz
  induction h : w z.1 using WithTop.recTopCoe with
  | top =>
    induction h' : w' z.2 using WithTop.recTopCoe with
    | top => exact ⟨0, by simp [h], by simp [h']⟩
    | coe n =>
      obtain ⟨a, ha, h1, h2⟩ := hz (n + 1)
      obtain ⟨b, hb1, hb2⟩ := hA a ha
      have e2 := (val_eq_of_close w' h2).1 h'
      have e1 := (val_eq_of_close w h1).2 (by rw [hb1, heq, ← hb2, e2])
      rw [h] at e1
      exact absurd e1 WithTop.top_ne_coe
  | coe n =>
    obtain ⟨a, ha, h1, h2⟩ := hz (n + 1)
    obtain ⟨b, hb1, hb2⟩ := hA a ha
    have e1 := (val_eq_of_close w h1).1 h
    have e2 := (val_eq_of_close w' h2).2 (by rw [hb2, ← heq, ← hb1, e1])
    exact ⟨b, by rw [h, ← hb1, e1], by rw [e2, ← heq, ← hb1, e1]⟩

def frc (A : Subring (F × F')) : Subring (F × F') where
  carrier := {z | ∃ d ∈ A, d.1 ≠ 0 ∧ d.2 ≠ 0 ∧ d * z ∈ A}
  one_mem' := ⟨1, A.one_mem, one_ne_zero, one_ne_zero, by simpa using A.one_mem⟩
  zero_mem' := ⟨1, A.one_mem, one_ne_zero, one_ne_zero, by simpa using A.zero_mem⟩
  add_mem' := by
    rintro y z ⟨d, hd, d1, d2, hy⟩ ⟨e, he, e1, e2, hz⟩
    refine ⟨d * e, A.mul_mem hd he, mul_ne_zero d1 e1, mul_ne_zero d2 e2, ?_⟩
    have : d * e * (y + z) = e * (d * y) + d * (e * z) := by ring
    rw [this]
    exact A.add_mem (A.mul_mem he hy) (A.mul_mem hd hz)
  neg_mem' := by
    rintro y ⟨d, hd, d1, d2, hy⟩
    exact ⟨d, hd, d1, d2, by rw [mul_neg]; exact A.neg_mem hy⟩
  mul_mem' := by
    rintro y z ⟨d, hd, d1, d2, hy⟩ ⟨e, he, e1, e2, hz⟩
    refine ⟨d * e, A.mul_mem hd he, mul_ne_zero d1 e1, mul_ne_zero d2 e2, ?_⟩
    rw [mul_mul_mul_comm]
    exact A.mul_mem hy hz

theorem le_frc (A : Subring (F × F')) : A ≤ frc A := fun z hz =>
  ⟨1, A.one_mem, one_ne_zero, one_ne_zero, by rwa [one_mul]⟩

theorem inv_mem_frc (A : Subring (F × F')) {y : F} {y' : F'} (h : (y, y') ∈ frc A) (hy : y ≠ 0) (hy' : y' ≠ 0) :
    (y⁻¹, y'⁻¹) ∈ frc A := by
  obtain ⟨d, hd, d1, d2, hz⟩ := h
  refine ⟨d * (y, y'), hz, mul_ne_zero d1 hy, mul_ne_zero d2 hy', ?_⟩
  have : d * (y, y') * (y⁻¹, y'⁻¹) = d := by
    ext <;> simp [hy, hy']
  rwa [this]

theorem att_frc {A : Subring (F × F')} (hA : ∀ z ∈ A, Att w w' ι ι' z) :
    ∀ z ∈ frc A, Att w w' ι ι' z := by
  rintro z ⟨d, hd, d1, d2, hz⟩
  obtain ⟨a, ha1, ha2⟩ := hA d hd
  obtain ⟨b, hb1, hb2⟩ := hA _ hz
  refine ⟨b * a⁻¹, ?_, ?_⟩
  · have : z.1 = (d * z).1 * d.1⁻¹ := by rw [Prod.fst_mul]; field_simp
    rw [this, map_mul ι, map_inv₀ ι, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_inv,
      AddValuation.map_inv, ha1, hb1]
  · have : z.2 = (d * z).2 * d.2⁻¹ := by rw [Prod.snd_mul]; field_simp
    rw [this, map_mul ι', map_inv₀ ι', AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_inv,
      AddValuation.map_inv, ha2, hb2]

end Pair

section Both

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {Ω : Type} [Field Ω] [Algebra K Ω]
  {D N : ℕ}

theorem exists_adapted (x : Fin N → Ω) (hx : ∃ k, x k ≠ 0) (v : AddValuation Ω (WithTop ℤ)) :
    ∃ j0, x j0 ≠ 0 ∧ ∀ k, 0 ≤ v (x k / x j0) := by
  obtain ⟨k0, hk0⟩ := hx
  haveI : Nonempty (Fin N) := ⟨k0⟩
  obtain ⟨j0, -, hj⟩ := Finset.univ.exists_min_image (fun k => v (x k)) Finset.univ_nonempty
  have hne : x j0 ≠ 0 := by
    intro h
    have := hj k0 (Finset.mem_univ _)
    rw [h, AddValuation.map_zero, top_le_iff, AddValuation.top_iff] at this
    exact hk0 this
  refine ⟨j0, hne, fun k => ValuationResidueLemmas.wt_nonneg_of_add (b := v (x j0)) (c := v (x k)) ?_ ?_ (hj k (Finset.mem_univ _))⟩
  · rw [Ne, AddValuation.top_iff]; exact hne
  · rw [← AddValuation.map_mul, div_mul_cancel₀ _ hne]

theorem exists_approx (c : la.adicCompletion K) (ϖ : la.adicCompletionIntegers K) (hϖ : ϖ ≠ 0) :
    ∃ (a : K) (o : la.adicCompletionIntegers K),
      c - algebraMap K (la.adicCompletion K) a = (ϖ : la.adicCompletion K) * o := by
  have hϖ' : (ϖ : la.adicCompletion K) ≠ 0 := fun h => hϖ (Subtype.ext h)
  have hU : IsOpen {z : la.adicCompletion K | (c - z) * (ϖ : la.adicCompletion K)⁻¹ ∈ la.adicCompletionIntegers K} :=
    (Valued.isOpen_valuationSubring (la.adicCompletion K)).preimage ((continuous_const.sub continuous_id).mul continuous_const)
  obtain ⟨a, ha⟩ := (HeightOneSpectrum.denseRange_algebraMap K la).exists_mem_open hU ⟨c, by simp⟩
  refine ⟨a, ⟨_, ha⟩, ?_⟩
  field_simp

theorem algebraMap_mem_max (a : 𝓞 K) :
    algebraMap (𝓞 K) (la.adicCompletionIntegers K) a ∈ maximalIdeal (la.adicCompletionIntegers K) ↔
      a ∈ la.asIdeal := by
  rw [mem_maximalIdeal, mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
    HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_eq_one_iff_notMem, not_not]

variable {K' : Type} [Field K'] (φ : MvPolynomial (Fin (D + 1) × Fin N) (la.adicCompletionIntegers K) →+* K')
  (κ : la.adicCompletion K →+* K') (x : Fin N → Ω)

def OverGauss {F : Type} [Field F] (w : AddValuation F (WithTop ℤ)) (ι : Ω →+* F) (e : K' →+* F) : Prop :=
  (∀ P, 0 ≤ w (e (φ P))) ∧ (∀ P, 0 < w (e (φ P)) ↔ ∀ α, P.coeff α ∈ maximalIdeal (la.adicCompletionIntegers K)) ∧
  (∀ a : K, ι (algebraMap K Ω a) = e (κ (algebraMap K (la.adicCompletion K) a))) ∧
  ∀ i : Fin D, ∑ k, e (φ (X (i.succ, k))) * ι (x k) = 0

variable {la φ κ x}

theorem OverGauss.eval_eq (hκ : ∀ o : la.adicCompletionIntegers K, κ o = φ (C o))
    {F : Type} [Field F] {w : AddValuation F (WithTop ℤ)} {ι : Ω →+* F} {e : K' →+* F}
    (h : OverGauss la φ κ x w ι e) (P : MvPolynomial (Fin (D + 1) × Fin N) (𝓞 K)) :
    eval₂ (ι.comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) (fun p => e (φ (X p))) P =
      e (φ (MvPolynomial.map (algebraMap (𝓞 K) (la.adicCompletionIntegers K)) P)) := by
  have : eval₂Hom (ι.comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) (fun p => e (φ (X p))) =
      e.comp (φ.comp (MvPolynomial.map (algebraMap (𝓞 K) (la.adicCompletionIntegers K)))) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => by simp)
    simp only [coe_eval₂Hom, eval₂_C, RingHom.comp_apply, map_C, h.2.2.1, ← hκ]
    rfl
  exact DFunLike.congr_fun this P

theorem OverGauss.gauss (hκ : ∀ o : la.adicCompletionIntegers K, κ o = φ (C o)) (htr : Algebra.trdeg K Ω = D)
    {F : Type} [Field F] {w : AddValuation F (WithTop ℤ)} {ι : Ω →+* F} {e : K' →+* F}
    (h : OverGauss la φ κ x w ι e) (j0 : Fin N) (hx : x j0 ≠ 0) (hint : ∀ k, 0 ≤ w (ι (x k / x j0)))
    (P : MvPolynomial (Fin (D + 1) × Fin N) Ω) :
    (aeval (subst x j0) P = 0 → eval₂ ι (fun p => e (φ (X p))) P = 0) ∧
    ∀ α ∈ (aeval (subst x j0) P).support,
      (∀ β ∈ (aeval (subst x j0) P).support,
        w (ι ((aeval (subst x j0) P).coeff α)) ≤ w (ι ((aeval (subst x j0) P).coeff β))) →
      w (eval₂ ι (fun p => e (φ (X p))) P) = w (ι ((aeval (subst x j0) P).coeff α)) := by
  refine gauss_one la htr x j0 hx w ι _ (fun Q => ?_) (fun Q => ?_) h.2.2.2 hint P
  · rw [h.eval_eq hκ, h.2.1]
    simp only [coeff_map, algebraMap_mem_max]
  · rw [h.eval_eq hκ]
    exact h.1 _

theorem OverGauss.approx (hκ : ∀ o : la.adicCompletionIntegers K, κ o = φ (C o))
    {F : Type} [Field F] {w : AddValuation F (WithTop ℤ)} {ι : Ω →+* F} {e : K' →+* F}
    (h : OverGauss la φ κ x w ι e) {ϖ : la.adicCompletionIntegers K}
    (hϖ : ϖ ∈ maximalIdeal (la.adicCompletionIntegers K)) (n : ℤ) {c : la.adicCompletion K} {a : K}
    {o : la.adicCompletionIntegers K}
    (hc : c - algebraMap K (la.adicCompletion K) a = ((ϖ ^ n.natAbs : la.adicCompletionIntegers K) : la.adicCompletion K) * o) :
    (n : WithTop ℤ) ≤ w (e (κ c) - ι (algebraMap K Ω a)) := by
  classical
  rw [h.2.2.1, ← map_sub, ← map_sub, hc, map_mul, map_mul, hκ, hκ]
  have h1 : ((1 : ℤ) : WithTop ℤ) ≤ w (e (φ (C ϖ))) := by
    have : 0 < w (e (φ (C ϖ))) := (h.2.1 _).2 fun α => by
      rw [coeff_C]; split_ifs
      · exact hϖ
      · exact Ideal.zero_mem _
    induction hh : w (e (φ (C ϖ))) using WithTop.recTopCoe with
    | top => exact le_top
    | coe m =>
      rw [hh] at this
      have : (0 : ℤ) < m := by exact_mod_cast this
      exact WithTop.coe_le_coe.2 (by omega)
  have h2 : ∀ m : ℕ, ((m : ℤ) : WithTop ℤ) ≤ w (e (φ (C (ϖ ^ m)))) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, map_mul, map_mul, map_mul]
      exact le_mul_of w ih h1 (by push_cast; omega)
  exact le_mul_of w (b := 0) (h2 _) (h.1 _) (by omega)

theorem exists_att (hκ : ∀ o : la.adicCompletionIntegers K, κ o = φ (C o))
    (hφ : ∀ c : K', ∃ a b, φ b ≠ 0 ∧ φ b * c = φ a) (htr : Algebra.trdeg K Ω = D) (hx : ∃ k, x k ≠ 0)
    {F F' : Type} [Field F] [Field F'] {w : AddValuation F (WithTop ℤ)} {ι : Ω →+* F} {e : K' →+* F}
    {w' : AddValuation F' (WithTop ℤ)} {ι' : Ω →+* F'} {e' : K' →+* F'}
    (h : OverGauss la φ κ x w ι e) (h' : OverGauss la φ κ x w' ι' e') (heq : ∀ a, w (ι a) = w' (ι' a)) :
    ∃ A : Subring (F × F'), (∀ z ∈ A, Att w w' ι ι' z) ∧ (∀ a, (ι a, ι' a) ∈ A) ∧ (∀ c, (e c, e' c) ∈ A) ∧
      ∀ y y', (y, y') ∈ A → y ≠ 0 → y' ≠ 0 → (y⁻¹, y'⁻¹) ∈ A := by
  classical
  obtain ⟨j0, hj0, hint⟩ := exists_adapted x hx (w.comap ι)
  have hint1 : ∀ k, 0 ≤ w (ι (x k / x j0)) := hint
  have hint2 : ∀ k, 0 ≤ w' (ι' (x k / x j0)) := fun k => heq _ ▸ hint1 k
  let A₀ : Subring (F × F') :=
    ((eval₂Hom ι (fun p => e (φ (X p)))).prod (eval₂Hom ι' (fun p => e' (φ (X p))))).range
  have hA₀ : ∀ z ∈ A₀, Att w w' ι ι' z := by
    rintro _ ⟨P, rfl⟩
    obtain ⟨g1, g2⟩ := h.gauss hκ htr j0 hj0 hint1 P
    obtain ⟨g3, g4⟩ := h'.gauss hκ htr j0 hj0 hint2 P
    by_cases hQ : aeval (subst x j0) P = 0
    · exact ⟨0, by simp [g1 hQ], by simp [g3 hQ]⟩
    · obtain ⟨α, hα, hmin⟩ := (aeval (subst x j0) P).support.exists_min_image
        (fun β => w (ι ((aeval (subst x j0) P).coeff β))) (MvPolynomial.support_nonempty.2 hQ)
      exact ⟨_, g2 α hα hmin, g4 α hα (fun β hβ => by rw [← heq, ← heq]; exact hmin β hβ)⟩
  have hΩ : ∀ a, (ι a, ι' a) ∈ A₀ := fun a => ⟨C a, by simp⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (la.adicCompletionIntegers K)
  have hϖm : ϖ ∈ maximalIdeal (la.adicCompletionIntegers K) := hϖ.not_isUnit
  have hP : ∀ P, (e (φ P), e' (φ P)) ∈ lim w w' A₀ := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C o =>
      intro n
      obtain ⟨a, o', hc⟩ := exists_approx la (o : la.adicCompletion K) (ϖ ^ n.natAbs) (pow_ne_zero _ hϖ.ne_zero)
      refine ⟨_, hΩ (algebraMap K Ω a), ?_, ?_⟩
      · rw [← hκ]; exact h.approx hκ hϖm n hc
      · rw [← hκ]; exact h'.approx hκ hϖm n hc
    | add p q hp hq =>
      have := Subring.add_mem _ hp hq
      simpa only [map_add, Prod.mk_add_mk] using this
    | mul_X p s hp =>
      have := Subring.mul_mem _ hp (le_lim w w' A₀ (⟨X s, by simp⟩ : (e (φ (X s)), e' (φ (X s))) ∈ A₀))
      simpa only [map_mul, Prod.mk_mul_mk] using this
  refine ⟨frc (lim w w' A₀), att_frc w w' ι ι' (att_lim w w' ι ι' heq hA₀),
    fun a => le_frc _ (le_lim w w' A₀ (hΩ a)), fun c => ?_, fun y y' => inv_mem_frc _⟩
  obtain ⟨a, b, hb, hc⟩ := hφ c
  refine ⟨_, hP b, (map_ne_zero e).2 hb, (map_ne_zero e').2 hb, ?_⟩
  rw [Prod.mk_mul_mk, ← map_mul, ← map_mul, hc]
  exact hP a

theorem exists_sep (v v' : AddValuation Ω (WithTop ℤ)) (h : ∃ a, v a = 1) (h' : ∃ a, v' a = 1) (hne : v ≠ v') :
    ∃ a, 0 < v a ∧ 0 < v' (a - 1) := by
  obtain ⟨s, hs⟩ := weak_approx_orders ![v, v'] (fun i a ha => by rw [Ne, AddValuation.top_iff]; exact ha)
    (fun i => by fin_cases i; exacts [h, h'])
    (fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all [hne.symm]) ![1, -1]
  have s1 : v s = ((1 : ℤ) : WithTop ℤ) := hs 0
  have s2 : v' s = ((-1 : ℤ) : WithTop ℤ) := hs 1
  have t1 : v (1 + s) = ((0 : ℤ) : WithTop ℤ) := by
    rw [AddValuation.map_add_eq_of_lt_left _ (by
      rw [AddValuation.map_one, s1]; exact_mod_cast (zero_lt_one : (0 : ℤ) < 1)),
      AddValuation.map_one, WithTop.coe_zero]
  have t2 : v' (1 + s) = ((-1 : ℤ) : WithTop ℤ) := by
    rw [AddValuation.map_add_eq_of_lt_right _ (by
      rw [AddValuation.map_one, s2]; exact_mod_cast (by omega : (-1 : ℤ) < 0)), s2]
  have h0 : 1 + s ≠ 0 := wa_ne_zero_of_coe _ t1
  refine ⟨s / (1 + s), ?_, ?_⟩
  · rw [wa_div _ s1 t1]; exact_mod_cast (by omega : (0 : ℤ) < 1 - 0)
  · have : s / (1 + s) - 1 = -(1 + s)⁻¹ := by field_simp; ring
    rw [this, AddValuation.map_neg, wa_inv _ t2]; exact_mod_cast (by omega : (0 : ℤ) < - -1)

end Both

end GlobalTheory.GenSep
