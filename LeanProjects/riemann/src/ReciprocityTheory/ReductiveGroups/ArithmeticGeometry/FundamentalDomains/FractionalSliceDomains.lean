import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MinimumGrowthBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMeanContinuity
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MajorantConjugateTransfer TwoSidedBoostBounds
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace FractionalSliceDomains

variable {r : ℕ} (X : Data E r)

noncomputable def hfun (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r) {n : ℕ}
    (ω : Module.Basis (Fin n) ℝ (X.Ψ → ℝ)) (t : Fin n → ℂ) : ℂ :=
  P (X.flow ξ (fun τ => ∑ j, t j * (ω j τ : ℂ)) x)

def Om (ξ : Fin r → E) (x : Frame X.Ψ r) {n : ℕ} (ω : Module.Basis (Fin n) ℝ (X.Ψ → ℝ)) :
    Set (Fin n → ℝ) :=
  {b | (fun τ => ∑ j, b j * ω j τ) ∈ AdmissibleHermitianColumns.admissibleImaginary X ξ x}

variable {ξ : Fin r → E} {x : Frame X.Ψ r} {n : ℕ} (ω : Module.Basis (Fin n) ℝ (X.Ψ → ℝ))

theorem Om_open_conn (hx : x ∈ X.dom) : IsOpen (Om X ξ x ω) ∧ IsPreconnected (Om X ξ x ω) := by
  obtain ⟨ho, hc⟩ := AdmissibleHermitianColumns.admissibleImaginary_open_convex (X := X) (ξ := ξ) x hx
  have hcont : Continuous (fun b : Fin n → ℝ => fun τ : X.Ψ => ∑ j, b j * ω j τ) := by
    refine continuous_pi fun τ => ?_
    exact continuous_finset_sum _ fun j _ => (continuous_apply j).mul continuous_const
  refine ⟨ho.preimage hcont, ?_⟩
  have hconv : Convex ℝ (Om X ξ x ω) := by
    intro a ha b hb s t hs ht hst
    show (fun τ => ∑ j, (s • a + t • b) j * ω j τ) ∈ AdmissibleHermitianColumns.admissibleImaginary X ξ x
    have e : (fun τ => ∑ j, (s • a + t • b) j * ω j τ) =
        s • (fun τ => ∑ j, a j * ω j τ) + t • (fun τ => ∑ j, b j * ω j τ) := by
      funext τ
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact hc ha hb hs ht hst
  exact hconv.isPreconnected

theorem mem_admissibleImaginary_iff (hx : x ∈ X.dom) (hξ : X.IsIso ξ) (y : X.Ψ → ℝ) :
    y ∈ AdmissibleHermitianColumns.admissibleImaginary X ξ x ↔ ∀ τ, 0 < 1 + X.c τ * y τ * X.maj x τ (Data.emb τ.1 ξ) := by
  have he : X.IsIsoV (fun τ => Data.emb τ.1 ξ) := fun τ =>
    ⟨by rw [ReciprocityTheory.ChartRestriction.G.FD.hermC_emb, hξ.2.1, map_zero], ReciprocityTheory.ChartRestriction.G.FD.emb_ne_zero τ.1 hξ.2.2⟩
  have h1 := AdmissibleHermitianColumns.flow_mem_dom_iff (X := X) hξ.2.1 x hx (fun τ => (y τ : ℂ) * I)
  have h1' : X.flow ξ (fun τ => (y τ : ℂ) * I) x ∈ X.dom ↔ y ∈ AdmissibleHermitianColumns.admissibleImaginary X ξ x := by
    rw [h1]
    apply iff_of_eq
    congr 1
    funext τ
    simp
  have h2 := ((flowDomainCriterion_holds (E := E)) r X (fun τ => Data.emb τ.1 ξ) he x hx
    (fun τ => (y τ : ℂ) * I)).1
  have hfl : X.flow ξ (fun τ => (y τ : ℂ) * I) x =
      X.flowV (fun τ => Data.emb τ.1 ξ) (fun τ => (y τ : ℂ) * I) x := rfl
  rw [← h1', hfl, h2]
  refine forall_congr' fun τ => ?_
  simp only [Data.ttV, Complex.mul_I_im, Complex.ofReal_re]
  rw [div_div_eq_mul_div, div_one]
  have e : y τ * (X.c τ * X.maj x τ (Data.emb τ.1 ξ)) = X.c τ * y τ * X.maj x τ (Data.emb τ.1 ξ) := by
    ring
  rw [e]

theorem zero_mem_Om (hx : x ∈ X.dom) (hξ : X.IsIso ξ) : (0 : Fin n → ℝ) ∈ Om X ξ x ω := by
  show (fun τ => ∑ j, (0 : Fin n → ℝ) j * ω j τ) ∈ AdmissibleHermitianColumns.admissibleImaginary X ξ x
  simp only [AdmissibleHermitianColumns.admissibleImaginary, Set.mem_setOf_eq]
  intro τ i
  have h := (hx τ).2 i
  simpa [dmin] using h

theorem tube_dom (hx : x ∈ X.dom) (hξ : X.IsIso ξ) {u : Fin n → ℂ}
    (hu : u ∈ ReciprocityTheory.L2DbarEstimates.Y.tube n (Om X ξ x ω)) :
    X.flow ξ (fun τ => ∑ j, u j * (ω j τ : ℂ)) x ∈ X.dom := by
  refine (AdmissibleHermitianColumns.flow_mem_dom_iff (X := X) hξ.2.1 x hx (fun τ => ∑ j, u j * (ω j τ : ℂ))).2 ?_
  have e : (fun τ => (∑ j, u j * (ω j τ : ℂ)).im) = fun τ => ∑ j, (u j).im * ω j τ := by
    funext τ
    simp [Complex.im_sum, Complex.mul_im]
  rw [e]
  exact hu

theorem hfun_diff (P : Frame X.Ψ r → ℂ) (la : Wt X.Ψ r) (hP : X.IsSec la P) (hx : x ∈ X.dom)
    (hξ : X.IsIso ξ) :
    DifferentiableOn ℂ (hfun X P ξ x ω) (ReciprocityTheory.L2DbarEstimates.Y.tube n (Om X ξ x ω)) := by
  have hL : Differentiable ℂ (fun t : Fin n → ℂ => fun τ : X.Ψ => ∑ j, t j * (ω j τ : ℂ)) := by
    refine differentiable_pi.2 fun τ => ?_
    exact Differentiable.fun_sum fun j _ => (differentiable_apply j).mul (differentiable_const _)
  have hF : Differentiable ℂ (fun t : Fin n → ℂ => X.flow ξ (fun τ => ∑ j, t j * (ω j τ : ℂ)) x) :=
    (FlowMeanContinuity.flow_differentiable X ξ x).comp hL
  exact hP.1.comp hF.differentiableOn (fun t ht => tube_dom X ω hx hξ ht)

theorem hfun_periodic (P : Frame X.Ψ r → ℂ) (la : Wt X.Ψ r) (hP : X.IsSec la P) (hx : x ∈ X.dom)
    (hξ : X.IsIso ξ) (hω : Submodule.span ℤ (Set.range ω) = RealEmbeddingCharacters.perL X la) :
    ∀ s ∈ ReciprocityTheory.L2DbarEstimates.Y.tube n (Om X ξ x ω), ∀ m : Fin n → ℤ,
      hfun X P ξ x ω (s + fun k => (m k : ℂ)) = hfun X P ξ x ω s := by
  intro s hs m
  have hS := tube_dom X ω hx hξ hs
  have hp : (fun τ => ∑ j, (m j : ℝ) * ω j τ) ∈ X.periods la := by
    have h1 : (fun τ => ∑ j, (m j : ℝ) * ω j τ) ∈ RealEmbeddingCharacters.perL X la := by
      rw [← hω]
      have e : (fun τ => ∑ j, (m j : ℝ) * ω j τ) = ∑ j, (m j) • ω j := by
        funext τ
        simp [Finset.sum_apply, zsmul_eq_mul]
      rw [e]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    first
      | exact h1
      | exact (AddSubgroup.mem_toIntSubmodule _).mp h1
  have hsum : (fun τ => ∑ j, (s + fun k => (m k : ℂ)) j * (ω j τ : ℂ)) =
      TransvectionPeriodicity.cR X (fun τ => ∑ j, (m j : ℝ) * ω j τ) + fun τ => ∑ j, s j * (ω j τ : ℂ) := by
    funext τ
    simp only [Pi.add_apply, TransvectionPeriodicity.cR]
    push_cast
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  show P (X.flow ξ (fun τ => ∑ j, (s + fun k => (m k : ℂ)) j * (ω j τ : ℂ)) x) =
    P (X.flow ξ (fun τ => ∑ j, s j * (ω j τ : ℂ)) x)
  first
    | rw [hsum, ← EmbeddingHermitianPairs.flow_flow (X := X) hξ.2.1]
    | rw [hsum, ← AdmissibleHermitianColumns.flow_flow (X := X) hξ.2.1]
  exact TransvectionPeriodicity.sec_periodic X la P hP hξ.1 hξ.2.1 hp _ hS

theorem slice_fract (P : Frame X.Ψ r → ℂ) (la : Wt X.Ψ r) (hP : X.IsSec la P) (hx : x ∈ X.dom)
    (hξ : X.IsIso ξ) (hω : Submodule.span ℤ (Set.range ω) = RealEmbeddingCharacters.perL X la)
    {b : Fin n → ℝ} (hb : b ∈ Om X ξ x ω) (y : Fin n → ℝ) :
    hfun X P ξ x ω (fun k => (y k : ℂ) + (b k : ℂ) * I) =
      hfun X P ξ x ω (fun k => ((Int.fract (y k) : ℝ) : ℂ) + (b k : ℂ) * I) := by
  have hmem : (fun k => (y k : ℂ) + (b k : ℂ) * I) ∈ ReciprocityTheory.L2DbarEstimates.Y.tube n (Om X ξ x ω) := by
    show (fun k => ((y k : ℂ) + (b k : ℂ) * I).im) ∈ Om X ξ x ω
    simpa using hb
  have h := hfun_periodic X ω P la hP hx hξ hω _ hmem (fun k => -⌊y k⌋)
  rw [← h]
  congr 1
  funext k
  simp only [Pi.add_apply, Int.fract, Complex.ofReal_sub, Complex.ofReal_intCast, Int.cast_neg]
  ring

noncomputable def Bω : ℝ := ∑ τ : X.Ψ, ∑ j, |ω j τ|

theorem re_bound (u : Fin n → ℝ) (hu : ∀ j, 0 ≤ u j ∧ u j ≤ 1) (τ : X.Ψ) :
    |∑ j, u j * ω j τ| ≤ Bω X ω := by
  unfold Bω
  calc |∑ j, u j * ω j τ| ≤ ∑ j, |u j * ω j τ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |ω j τ| := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (hu j).1]
        exact mul_le_of_le_one_left (abs_nonneg _) (hu j).2
    _ ≤ ∑ τ' : X.Ψ, ∑ j, |ω j τ'| :=
        Finset.single_le_sum (f := fun τ' => ∑ j, |ω j τ'|)
          (fun τ' _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ τ)

theorem Bω_nonneg : 0 ≤ Bω X ω := by
  unfold Bω
  exact Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun j _ => abs_nonneg _

end FractionalSliceDomains

end ReciprocityTheory.ChartRestriction.G.FD
