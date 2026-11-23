import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CastAddNeNatAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SacSuccAbove

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial MeasureTheory

theorem countable_numberField (K : Type) [Field K] [NumberField K] : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem ST_scale (c : ι) (sg : K →+* ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ) (y : Fin (d.N + 1 + d.D) → ℂ)
    (hy : ∀ i, y (Fin.natAdd (d.N + 1) i) ≠ 0) :
    d.ST c sg (fun i j => NPB.gpt (fun q => t q.1 q.2) y (i.succ, j)) = d.ST c sg t := by
  ext P
  simp only [ST, Set.mem_setOf_eq, NPB.gpt, Fin.cases_succ]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, mul_eq_zero]
  simp [hy i]

theorem gpt_one (t : Fin d.D → Fin (d.N + 1) → ℂ) (t0 : Fin (d.N + 1) → ℂ) :
    NPB.gpt (fun q => t q.1 q.2) (Fin.addCases t0 (fun _ => (1 : ℂ))) =
      fun v : TVar d.D d.N => Fin.cases (motive := fun _ => ℂ) (t0 v.2) (fun i => t i v.2) v.1 := by
  funext v
  rcases v with ⟨a, j⟩
  refine Fin.cases ?_ (fun i => ?_) a <;> simp [NPB.gpt]

theorem fib (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ)
    (y : Fin (d.N + 1 + d.D) → ℂ)
    (hpt : ∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 →
      eval₂ sg (NPB.gpt (fun q => t q.1 q.2) y) q ≠ 0) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    (d.ST c sg t).Finite ∧ (d.ST c sg t).ncard = d.delc c ∧
      (∀ g : Ω c, tauPev sg _ hpt (Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g))
        = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), P g) ∧
      tauPev sg _ hpt (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)) =
        ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t),
          ∑ j, y (Fin.castAdd d.D j) * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) := by
  letI iA : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI iB : Algebra (KTf K d.D d.N) ℂ := (tauPev sg _ hpt).toAlgebra
  obtain ⟨hfd, hrank⟩ := d.omS_finite hd h c
  haveI := hfd
  haveI : CharZero (KTf K d.D d.N) := inferInstance
  haveI : Algebra.IsIntegral (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := Algebra.IsSeparable.of_integral _ _
  have hy : ∀ i, y (Fin.natAdd (d.N + 1) i) ≠ 0 := by
    intro i h0
    apply hpt (MvPolynomial.X (i.succ, 0)) (MvPolynomial.X_ne_zero _)
    simp [NPB.gpt, h0]
  have hST : d.ST c sg (fun i j => NPB.gpt (fun q => t q.1 q.2) y (i.succ, j)) = d.ST c sg t :=
    d.ST_scale c sg t y hy
  obtain ⟨hinj, hrange⟩ := d.fibre_core (hd := hd) (h := h) (c := c) (sg := sg)
    (pt := NPB.gpt (fun q => t q.1 q.2) y) (hpt := hpt)
  rw [hST] at hrange
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hrange]
    exact Set.finite_range _
  · rw [← hrange, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, AlgHom.card, hrank]
  · intro g
    have h1 := Algebra.norm_eq_prod_embeddings (KTf K d.D d.N) ℂ
      (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g)
    rw [← hrange, finprod_mem_range hinj, finprod_eq_prod_of_fintype]
    exact h1
  · have h1 := Algebra.norm_eq_prod_embeddings (KTf K d.D d.N) ℂ (d.rationalBaseRow c)
    rw [← hrange, finprod_mem_range hinj, finprod_eq_prod_of_fintype]
    refine h1.trans (Finset.prod_congr rfl fun σ _ => ?_)
    have hσ : (σ : OmS (Ω c) d.D d.N →+* ℂ).comp (d.KTtoS h c) = tauPev sg _ hpt :=
      RingHom.ext fun x => σ.commutes x
    simp only [rationalBaseRow, map_sum, map_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have he := d.emb_sH (h := h) (c := c) (sg := sg)
      (pt := NPB.gpt (fun q => t q.1 q.2) y) (hpt := hpt) (σ : OmS (Ω c) d.D d.N →+* ℂ) hσ
      (MvPolynomial.X (0, j))
    simp only [AlgHom.coe_toRingHom] at he
    rw [he]
    simp [NPB.gpt]

theorem norm_at_sg_B (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      (d.ST c sg (d.tOf z)).Finite ∧ (d.ST c sg (d.tOf z)).ncard = d.delc c ∧
      (∀ (g : Ω c) (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), g ≠ 0 → b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) *
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), P g) ∧
      (∀ (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
          ∑ j, t0 j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  have := countable_numberField K
  filter_upwards [NPB.ae_gen (K := K) (D := d.D) (N := d.N) sg] with z hz
  have hG : ∀ (a : Fin d.D → ℕ) (p : MvPolynomial (Fin d.D × Fin (d.N + 1)) K),
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a p → p ≠ 0 →
        eval₂ sg (fun q => d.tOf z q.1 q.2) p ≠ 0 := hz
  obtain ⟨y1, -, hpt1⟩ := NPB.exists_gen sg (fun q => d.tOf z q.1 q.2) hG 1 one_ne_zero
  obtain ⟨hfin, hcard, -, -⟩ := d.fib hd h c sg (d.tOf z) y1 hpt1
  refine ⟨hfin, hcard, ?_, ?_⟩
  · intro g a b t0 _ _ hab hbt
    have hQ : NPB.psi sg (fun q => d.tOf z q.1 q.2) a -
        C (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), P g) *
          NPB.psi sg (fun q => d.tOf z q.1 q.2) b = 0 := by
      by_contra hQ
      obtain ⟨y, hy, hpt⟩ := NPB.exists_gen sg _ hG _ hQ
      obtain ⟨-, -, hn, -⟩ := d.fib hd h c sg (d.tOf z) y hpt
      apply hy
      have h1 := congrArg (tauPev sg _ hpt) hab
      rw [map_mul, hn g, tauPev_apply, tauPev_apply] at h1
      rw [map_sub, map_mul, eval_C, NPB.eval_psi, NPB.eval_psi, ← h1, sub_self]
    have h2 := congrArg (eval (Fin.addCases t0 (fun _ => (1 : ℂ)))) hQ
    rw [map_sub, map_mul, eval_C, NPB.eval_psi, NPB.eval_psi, d.gpt_one, map_zero, sub_eq_zero] at h2
    rw [div_eq_iff hbt]
    exact h2
  · intro a b t0 _ hab hbt
    let cX : MvPolynomial (Fin (d.N + 1 + d.D)) ℂ := ∏ P ∈ hfin.toFinset,
      ∑ j, X (Fin.castAdd d.D j) * C (P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)))
    have hcX : ∀ y, eval y cX = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
        ∑ j, y (Fin.castAdd d.D j) * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) := by
      intro y
      rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
      simp only [cX, map_prod, map_sum, map_mul, eval_X, eval_C]
    have hQ : NPB.psi sg (fun q => d.tOf z q.1 q.2) a - cX * NPB.psi sg (fun q => d.tOf z q.1 q.2) b = 0 := by
      by_contra hQ
      obtain ⟨y, hy, hpt⟩ := NPB.exists_gen sg _ hG _ hQ
      obtain ⟨-, -, -, hn⟩ := d.fib hd h c sg (d.tOf z) y hpt
      apply hy
      have h1 := congrArg (tauPev sg _ hpt) hab
      rw [map_mul, hn, tauPev_apply, tauPev_apply] at h1
      rw [map_sub, map_mul, hcX, NPB.eval_psi, NPB.eval_psi, ← h1, sub_self]
    have h2 := congrArg (eval (Fin.addCases t0 (fun _ => (1 : ℂ)))) hQ
    rw [map_sub, map_mul, hcX, NPB.eval_psi, NPB.eval_psi, d.gpt_one, map_zero, sub_eq_zero] at h2
    simp only [Fin.addCases_left] at h2
    rw [div_eq_iff hbt]
    exact h2

end Data

end ReciprocityTheory.ChartRestriction.G.T0
