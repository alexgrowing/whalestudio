import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.ShortIsot
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower

open Matrix NumberField Topology
open scoped ComplexConjugate

noncomputable section

namespace CompanionTheory.D.gk.RF.PE

open Formalism.MainNotions.S

variable (I : AutInst)

def emb (p : InfinitePlace I.F × Bool) : I.E →+* ℂ := if p.2 then (starRingEnd ℂ).comp (I.φ p.1) else I.φ p.1

theorem emb_over (p : InfinitePlace I.F × Bool) (a : I.F) : emb I p (algebraMap I.F I.E a) = p.1.embedding a := by
  have := I.cm.totReal
  obtain ⟨v, b⟩ := p
  cases b
  · exact I.φ_over v a
  · show conj (I.φ v _) = _
    rw [I.φ_over]
    exact RingHom.congr_fun (IsTotallyReal.complexEmbedding_isReal v.embedding) a

theorem emb_inj (hs : ∀ v (a : I.E), I.φ v (star a) = star (I.φ v a)) : Function.Injective (emb I) := by
  have key : ∀ v, (starRingEnd ℂ).comp (I.φ v) ≠ I.φ v := fun v h => by
    have h1 : ∀ a : I.E, star a = a := fun a => (I.φ v).injective (by rw [hs]; exact RingHom.congr_fun h a)
    have h2 : Function.Bijective (algebraMap I.F I.E) :=
      ⟨(algebraMap I.F I.E).injective, fun a => (I.cm.fixed a).1 (h1 a)⟩
    have h3 := (LinearEquiv.ofBijective (Algebra.linearMap I.F I.E) h2).finrank_eq
    rw [I.cm.deg2, Module.finrank_self] at h3
    exact absurd h3 (by norm_num)
  rintro ⟨v, b⟩ ⟨w, c⟩ h
  have hvw : v = w := by
    rw [← v.mk_embedding, ← w.mk_embedding]
    congr 1
    ext a
    rw [← emb_over I (v, b), h, emb_over I (w, c)]
  subst hvw
  cases b <;> cases c
  · rfl
  · exact absurd h.symm (key v)
  · exact absurd h (key v)
  · rfl

theorem emb_bij (hs : ∀ v (a : I.E), I.φ v (star a) = star (I.φ v a)) : Function.Bijective (emb I) := by
  classical
  have := I.cm.totReal
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨emb_inj I hs, ?_⟩
  rw [Embeddings.card, ← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2, Fintype.card_prod, Fintype.card_bool,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero,
    IsTotallyReal.finrank, add_zero]

theorem finite_bdd (hs : ∀ v (a : I.E), I.φ v (star a) = star (I.φ v a)) (B : ℝ) :
    {x : I.E | IsIntegral ℤ x ∧ ∀ v, ‖I.φ v x‖ ≤ B}.Finite := by
  refine (Embeddings.finite_of_norm_le I.E ℂ B).subset fun x hx => ⟨hx.1, fun ψ => ?_⟩
  obtain ⟨⟨v, b⟩, rfl⟩ := (emb_bij I hs).2 ψ
  cases b
  · exact hx.2 v
  · show ‖conj (I.φ v x)‖ ≤ B
    rw [Complex.norm_conj]; exact hx.2 v

theorem trace_eq (hs : ∀ v (a : I.E), I.φ v (star a) = star (I.φ v a)) (x : I.E) :
    ((Algebra.trace ℚ I.E x : ℚ) : ℝ) = ∑ v, 2 * (I.φ v x).re := by
  classical
  have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := I.E) (x := x)
  rw [← (RingHom.equivRatAlgHom (R := I.E) (S := ℂ)).sum_comp, ← (Equiv.ofBijective _ (emb_bij I hs)).sum_comp,
    Fintype.sum_prod_type] at h
  have h2 := congrArg Complex.re h
  rw [eq_ratCast, Complex.ratCast_re, Complex.re_sum] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_bool]
  show (conj (I.φ v x) + I.φ v x).re = _
  simp [two_mul]

theorem exists_den {E ι : Type} [Field E] [NumberField E] [Finite ι] (f : ι → E) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ i, IsIntegral ℤ ((c : E) * f i) := by
  classical
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (Set.finite_range f).toFinset
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i => ?_⟩
  have := h (f i) (by simp)
  rw [zsmul_eq_mul] at this
  rcases Int.natAbs_eq y with e | e
  · rwa [e, Int.cast_natCast] at this
  · rw [e, Int.cast_neg, Int.cast_natCast, neg_mul] at this
    simpa using this.neg

theorem isIntegral_star {E : Type} [Field E] [StarRing E] {x : E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  map_isIntegral_int (starRingEnd E) hx

def IntM {E : Type} [Field E] {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : Prop := ∀ i j, IsIntegral ℤ (A i j)

theorem IntM.mul {E : Type} [Field E] {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : IntM A) (hB : IntM B) :
    IntM (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact IsIntegral.sum _ fun k _ => (hA i k).mul (hB k j)

theorem IntM.conjT {E : Type} [Field E] [StarRing E] {n : ℕ} {A : Matrix (Fin n) (Fin n) E} (hA : IntM A) :
    IntM Aᴴ := fun i j => isIntegral_star (hA j i)

theorem uMat_mul_inv {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 :=
  (g : (Matrix (Fin n) (Fin n) ℂ)ˣ).mul_inv

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : uMat g⁻¹ * uMat g = 1 :=
  (g : (Matrix (Fin n) (Fin n) ℂ)ˣ).inv_mul

theorem hf_uMat {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (a b : Fin n → ℂ) :
    hf (Formalism.REAL.Jm ε) (uMat g *ᵥ a) (uMat g *ᵥ b) = hf (Formalism.REAL.Jm ε) a b := by
  have h : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  unfold hf
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h]

theorem norm_hf_le {n : ℕ} (ε : Fin n → Bool) {a b : Fin n → ℂ} {s : ℝ} (ha : ∀ i, ‖a i‖ ≤ s) (hb : ∀ i, ‖b i‖ ≤ s) :
    ‖hf (Formalism.REAL.Jm ε) a b‖ ≤ n * (s * s) := by
  unfold hf dotProduct
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (s * s) fun i _ => ?_).trans (by simp))
  rw [Formalism.REAL.Jm, mulVec_diagonal, norm_mul, norm_mul, Pi.star_apply, norm_star]
  have : ‖(if ε i = true then (1 : ℂ) else -1)‖ = 1 := by split_ifs <;> simp
  rw [this, one_mul]
  exact mul_le_mul (ha i) (hb i) (norm_nonneg _) ((norm_nonneg _).trans (ha i))

theorem isCompact_inv_bdd (K : ℝ) : IsCompact {x : I.Ginf | ∀ v i j, ‖uMat (x v)⁻¹ i j‖ ≤ K} := by
  have h1 : ∀ v, IsCompact {g : Formalism.REAL.UJ (I.ε v) | ∀ i j, ‖uMat g⁻¹ i j‖ ≤ K} := fun v => by
    have h2 : IsCompact {A : Matrix (Fin I.n) (Fin I.n) ℂ | ∀ i j, ‖A i j‖ ≤ K} := by
      have := isCompact_univ_pi fun _ : Fin I.n => isCompact_univ_pi fun _ : Fin I.n =>
        isCompact_closedBall (0 : ℂ) K
      refine IsCompact.of_isClosed_subset (s := (Set.univ.pi fun _ : Fin I.n => Set.univ.pi fun _ : Fin I.n =>
        Metric.closedBall (0 : ℂ) K : Set (Matrix (Fin I.n) (Fin I.n) ℂ))) this ?_ fun A hA i _ j _ =>
          mem_closedBall_zero_iff.2 (hA i j)
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_le (continuous_id.matrix_elem i j).norm continuous_const
    exact ((Formalism.REAL.isClosedEmbeddingMatrix I.n (I.ε v)).1.isCompact_preimage h2).inv
  convert isCompact_univ_pi h1 using 1
  ext x
  simp [Set.mem_pi]

end CompanionTheory.D.gk.RF.PE

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S PE

theorem mahler_compactness_of : Transp → GamSub → Mahler := by
  classical
  intro hT _ I M hM R
  obtain ⟨hJ, hs, hh, -, -, -, -, hG⟩ := hT I
  obtain ⟨c, hc, hcJ⟩ := exists_den fun p : Fin I.n × Fin I.n => I.J p.1 p.2
  have hcJ' : IntM ((c : I.E) • I.J) := fun i j => hcJ (i, j)
  have hc0 : (c : I.E) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
  set T : ℝ := I.n * |R| + |R| + 1 with hTd
  have hT0 : 0 ≤ T := by positivity
  set s : ℝ := T + |R|

  have hfin : {G : Matrix (Fin I.n) (Fin I.n) I.E | ∀ i j, IsIntegral ℤ ((c : I.E) * G i j) ∧
      ∀ v, ‖I.φ v ((c : I.E) * G i j)‖ ≤ c * (I.n * (s * s))}.Finite := by
    have h1 := Set.Finite.pi' fun _ : Fin I.n => Set.Finite.pi' fun _ : Fin I.n =>
      (finite_bdd I hs (c * (I.n * (s * s)))).preimage (f := fun x : I.E => (c : I.E) * x)
        (mul_right_injective₀ hc0).injOn
    exact h1.subset fun G hG' i j => hG' i j
  have := hfin.to_subtype
  obtain ⟨D, hD, hDG⟩ := exists_den fun p : {G // G ∈ _} × Fin I.n × Fin I.n =>
    ((p.1 : {G // G ∈ {G : Matrix (Fin I.n) (Fin I.n) I.E | ∀ i j, IsIntegral ℤ ((c : I.E) * G i j) ∧
      ∀ v, ‖I.φ v ((c : I.E) * G i j)‖ ≤ c * (I.n * (s * s))}}) : Matrix (Fin I.n) (Fin I.n) I.E)⁻¹ p.2.1 p.2.2
  set k : ℕ := M * D * c with hk
  have hk0 : (k : 𝓞 I.E) ≠ 0 := by
    have : k ≠ 0 := by positivity
    exact_mod_cast this
  have := Ideal.finiteQuotientOfFreeOfNeBot (Ideal.span {(k : 𝓞 I.E)}) (by simpa using hk0)
  let 𝔅 : Set (Matrix (Fin I.n) (Fin I.n) (𝓞 I.E)) := {B | IsUnit (B.map (algebraMap (𝓞 I.E) I.E)).det ∧
    ∀ i j, IsIntegral ℤ ((c : I.E) * ((B.map (algebraMap (𝓞 I.E) I.E))ᴴ * I.J * B.map (algebraMap (𝓞 I.E) I.E)) i j) ∧
      ∀ v, ‖I.φ v ((c : I.E) * ((B.map (algebraMap (𝓞 I.E) I.E))ᴴ * I.J * B.map (algebraMap (𝓞 I.E) I.E)) i j)‖ ≤
        c * (I.n * (s * s))}
  let κ : Matrix (Fin I.n) (Fin I.n) (𝓞 I.E) → Matrix (Fin I.n) (Fin I.n) I.E ×
      (Fin I.n → Fin I.n → 𝓞 I.E ⧸ Ideal.span {(k : 𝓞 I.E)}) := fun B =>
    ((B.map (algebraMap (𝓞 I.E) I.E))ᴴ * I.J * B.map (algebraMap (𝓞 I.E) I.E), fun i j => Ideal.Quotient.mk _ (B i j))
  have hκ : (κ '' 𝔅).Finite := (hfin.prod Set.finite_univ).subset (by
    rintro _ ⟨B, hB, rfl⟩
    exact ⟨hB.2, trivial⟩)
  have := hκ.to_subtype
  choose rp hrp hrpκ using fun z : κ '' 𝔅 => z.2
  obtain ⟨K, hK⟩ := (Set.finite_range fun p : (κ '' 𝔅) × InfinitePlace I.F × Fin I.n × Fin I.n =>
    ‖((((rp p.1).map (algebraMap (𝓞 I.E) I.E))⁻¹).map (I.φ p.2.1) * I.P p.2.1) p.2.2.1 p.2.2.2‖).bddAbove
  refine ⟨_, isCompact_inv_bdd I (I.n * (s * K)), fun y hy => ?_⟩
  have hW : ∀ v, Wv I ⊤ v = ⊤ := fun v => by
    have h1 := (hT I).2.2.2.1 v ⊥
    have e1 : perp I.J ⊥ = ⊤ := eq_top_iff.2 fun z _ w hw => by rw [(Submodule.mem_bot _).1 hw]; simp [hf]
    have e2 : Wv I ⊥ v = ⊥ := by
      refine Submodule.span_eq_bot.2 ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [(Submodule.mem_bot _).1 hu]
      funext i; simp [atV, mulVec, dotProduct]
    rw [e1, e2] at h1
    rw [h1]
    exact eq_top_iff.2 fun z _ w hw => by rw [(Submodule.mem_bot _).1 hw]; simp [hf]
  choose b hbI _ hbR using fun i : Fin I.n =>
    hy (fun v => uMat (y v) *ᵥ Pi.single i (T : ℂ)) fun v => by rw [hW]; trivial
  let B : Matrix (Fin I.n) (Fin I.n) (𝓞 I.E) := fun j i => ⟨b i j, hbI i j⟩
  set B' : Matrix (Fin I.n) (Fin I.n) I.E := B.map (algebraMap (𝓞 I.E) I.E) with hB'
  let Q : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ := fun v => uMat (y v)⁻¹ * (I.P v)⁻¹ * B'.map (I.φ v)
  have hQ : ∀ v j i, Q v j i = vecAt I y (b i) v j := fun v j i => by
    simp only [Q, vecAt, atV, mulVec_mulVec]
    rfl
  have hQR : ∀ v j i, ‖(Pi.single i (T : ℂ) : Fin I.n → ℂ) j - Q v j i‖ ≤ |R| := fun v j i => by
    have h1 := (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ v).trans ((hbR i).trans (le_abs_self R)))
    rw [hQ]
    simpa only [Pi.sub_apply, mulVec_mulVec, uMat_inv_mul, one_mulVec] using h1
  have hQs : ∀ v j i, ‖Q v j i‖ ≤ s := fun v j i => by
    have h1 := hQR v j i
    have h2 : ‖(Pi.single i (T : ℂ) : Fin I.n → ℂ) j‖ ≤ T := by
      by_cases h : j = i
      · subst h; simp [abs_of_nonneg hT0]
      · simp [Pi.single_eq_of_ne h, hT0]
    have := norm_sub_norm_le (Q v j i) ((Pi.single i (T : ℂ) : Fin I.n → ℂ) j)
    rw [norm_sub_rev] at this
    linarith
  have hBu : IsUnit B'.det := by
    obtain ⟨v⟩ : Nonempty (InfinitePlace I.F) := inferInstance
    have h1 : (Q v).det ≠ 0 := det_ne_zero_of_sum_row_lt_diag fun j => by
      have h2 := hQR v j j
      rw [Pi.single_eq_same] at h2
      have h3 := norm_sub_norm_le (T : ℂ) (Q v j j)
      rw [Complex.norm_real, Real.norm_of_nonneg hT0] at h3
      have h4 : ∑ i ∈ Finset.univ.erase j, ‖Q v j i‖ ≤ I.n * |R| := by
        refine (Finset.sum_le_card_nsmul _ _ |R| fun i hi => ?_).trans ?_
        · have := hQR v j i
          rwa [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hi).symm, zero_sub, norm_neg] at this
        · rw [nsmul_eq_mul]
          gcongr
          exact_mod_cast (Finset.card_le_univ _).trans (by simp)
      linarith
    refine (Ne.isUnit fun h0 => h1 ?_)
    simp only [Q, det_mul]
    rw [show (B'.map (I.φ v)).det = I.φ v B'.det from ((I.φ v).map_det B').symm, h0, map_zero, mul_zero]
  have hBint : ∀ A : Matrix (Fin I.n) (Fin I.n) (𝓞 I.E), IntM (A.map (algebraMap (𝓞 I.E) I.E)) :=
    fun A i j => (A i j).2
  have hB𝔅 : B ∈ 𝔅 := ⟨hBu, fun i j => ⟨by
      have := ((hBint B).conjT.mul hcJ').mul (hBint B) i j
      rwa [Matrix.mul_smul, Matrix.smul_mul] at this, fun v => by
      have e : (B'ᴴ * I.J * B') i j = hf I.J (b i) (b j) := by
        rw [Matrix.mul_assoc]; rfl
      rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast, e, ← hh, ← hf_uMat (y v)⁻¹]
      exact mul_le_mul_of_nonneg_left (norm_hf_le _ (fun l => (congrArg norm (hQ v l i)).ge.trans (hQs v l i))
        fun l => (congrArg norm (hQ v l j)).ge.trans (hQs v l j))
        (Nat.cast_nonneg c)⟩⟩
  let z : κ '' 𝔅 := ⟨κ B, B, hB𝔅, rfl⟩
  set B₀ : Matrix (Fin I.n) (Fin I.n) I.E := (rp z).map (algebraMap (𝓞 I.E) I.E) with hB₀
  have hB₀u : IsUnit B₀.det := (hrp z).1
  have hGr : B₀ᴴ * I.J * B₀ = B'ᴴ * I.J * B' := congrArg Prod.fst (hrpκ z)
  have hJu : IsUnit I.J.det := I.J_det.isUnit
  have hcong : ∃ A : Matrix (Fin I.n) (Fin I.n) I.E, IntM A ∧ B₀ - B' = (k : I.E) • A := by
    have : ∀ i j, ∃ a : 𝓞 I.E, a * k = rp z i j - B i j := fun i j =>
      Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (congrFun (congrFun (congrArg Prod.snd (hrpκ z)) i) j))
    choose a ha using this
    refine ⟨fun i j => a i j, fun i j => (a i j).2, Matrix.ext fun i j => ?_⟩
    have := congrArg (algebraMap (𝓞 I.E) I.E) (ha i j)
    rw [map_mul, map_natCast, map_sub] at this
    exact this.symm.trans (mul_comm _ _)
  obtain ⟨A, hA, hAe⟩ := hcong
  have hDi : IntM ((D : I.E) • (B'ᴴ * I.J * B')⁻¹) := fun i j => hDG (⟨_, hB𝔅.2⟩, i, j)
  have key : ∀ C : Matrix (Fin I.n) (Fin I.n) I.E, IntM C → IsUnit C.det → Cᴴ * I.J * C = B'ᴴ * I.J * B' →
      IntM (((D * c : ℕ) : I.E) • C⁻¹) := fun C hC hCu e => by
    have hCh : IsUnit Cᴴ.det := by rw [det_conjTranspose]; exact hCu.star
    have e2 : (B'ᴴ * I.J * B')⁻¹ * Cᴴ * I.J = C⁻¹ := by
      rw [← e, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_assoc,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hCh, Matrix.nonsing_inv_mul _ hJu, Matrix.mul_one]
    have := (hDi.mul hC.conjT).mul hcJ'
    rwa [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, e2, smul_smul, mul_comm, ← Nat.cast_mul] at this
  have cong : ∀ C C' A' : Matrix (Fin I.n) (Fin I.n) I.E, IntM A' → C' - C = (k : I.E) • A' → IsUnit C.det →
      IntM (((D * c : ℕ) : I.E) • C⁻¹) → Cong I M (C' * C⁻¹) := fun C C' A' hA' e hu hi i j => by
    refine ⟨_, hA'.mul hi i j, ?_⟩
    have : C' * C⁻¹ - 1 = (M : I.E) • (A' * (((D * c : ℕ) : I.E) • C⁻¹)) := by
      rw [← Matrix.mul_nonsing_inv _ hu, ← Matrix.sub_mul, e, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hk]
      push_cast
      rw [mul_assoc]
    rw [this]; rfl
  let γ : GL (Fin I.n) I.E := ⟨B₀ * B'⁻¹, B' * B₀⁻¹,
    by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hBu, Matrix.mul_nonsing_inv _ hB₀u],
    by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hB₀u, Matrix.mul_nonsing_inv _ hBu]⟩
  have hγU : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := by
    show (B₀ * B'⁻¹)ᴴ * I.J * (B₀ * B'⁻¹) = I.J
    have hBh : IsUnit B'ᴴ.det := by rw [det_conjTranspose]; exact hBu.star
    calc (B₀ * B'⁻¹)ᴴ * I.J * (B₀ * B'⁻¹) = B'ᴴ⁻¹ * (B₀ᴴ * I.J * B₀) * B'⁻¹ := by
          rw [conjTranspose_mul, conjTranspose_nonsing_inv]; simp only [Matrix.mul_assoc]
      _ = I.J := by
          rw [hGr, Matrix.mul_assoc B'ᴴ, Matrix.nonsing_inv_mul_cancel_left _ _ hBh,
            Matrix.mul_nonsing_inv_cancel_right _ _ hBu]
  obtain ⟨g, hg⟩ := hG γ hγU
  refine ⟨g, ⟨γ, ⟨hγU, cong B' B₀ A hA hAe hBu (key B' (hBint B) hBu rfl),
    cong B₀ B' (-A) (fun i j => (hA i j).neg) (by rw [smul_neg, ← hAe, neg_sub]) hB₀u
      (key B₀ (hBint _) hB₀u hGr)⟩, hg⟩, fun v i j => ?_⟩
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have e : uMat ((g * y) v)⁻¹ = Q v * (B₀⁻¹.map (I.φ v) * I.P v) := by
    have e1 : uMat ((g * y) v) = atM I v (B₀ * B'⁻¹) * uMat (y v) := by
      rw [← show uMat (g v) = _ from hg v]; rfl
    have e2 : Q v * (B₀⁻¹.map (I.φ v) * I.P v) * uMat ((g * y) v) = 1 := by
      have e3 : B'.map (I.φ v) * B₀⁻¹.map (I.φ v) * (B₀ * B'⁻¹).map (I.φ v) = 1 := by
        rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hB₀u,
          Matrix.mul_nonsing_inv _ hBu, Matrix.map_one _ (map_zero _) (map_one _)]
      calc _ = uMat (y v)⁻¹ * ((I.P v)⁻¹ * ((B'.map (I.φ v) * B₀⁻¹.map (I.φ v) * (I.P v * (I.P v)⁻¹) *
            (B₀ * B'⁻¹).map (I.φ v)) * I.P v)) * uMat (y v) := by
            rw [e1]; simp only [Q, atM, Matrix.mul_assoc]
        _ = 1 := by
            rw [Matrix.mul_nonsing_inv _ hP, Matrix.mul_one, e3, Matrix.one_mul, Matrix.nonsing_inv_mul _ hP,
              Matrix.mul_one, uMat_inv_mul]
    rw [← Matrix.one_mul (uMat ((g * y) v)⁻¹), ← e2, Matrix.mul_assoc, uMat_mul_inv, Matrix.mul_one]
  rw [e, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (s * K) fun l _ => ?_).trans (by simp))
  rw [norm_mul]
  exact mul_le_mul (hQs v i l) (hK ⟨(z, v, l, j), rfl⟩) (norm_nonneg _) ((norm_nonneg _).trans (hQs v i l))

end CompanionTheory.D.gk.RF
