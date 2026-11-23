import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCubicalStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0 dflat herm flat flatOf FlatFormProps)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

namespace GlobalTheory.HorizontalChange

theorem eventually_eq_of_rat {E J K : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J] [Fintype K]
    (F : E × (J → ℝ) → (K → ℝ)) (v₀ : E) (x₀ : J → ℝ)
    (h : ∀ᶠ Q in 𝓝 (v₀, x₀), ContinuousAt F Q ∧
      ((∀ i, ∃ r : ℚ, Q.2 i = r) → ∀ i, ∃ r : ℚ, F Q i = r)) :
    ∀ᶠ v in 𝓝 v₀, F (v, x₀) = F (v₀, x₀) := by
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.1 h
  have hm {v : E} {x : J → ℝ} (hv : v ∈ Metric.ball v₀ ε) (hx : x ∈ Metric.ball x₀ ε) :
      (v, x) ∈ Metric.ball (v₀, x₀) ε := by
    rw [← ball_prod_same]; exact ⟨hv, hx⟩
  filter_upwards [Metric.ball_mem_nhds v₀ hε] with v hv
  have h0 := Metric.mem_ball_self (x := v₀) hε
  have hx0 := Metric.mem_ball_self (x := x₀) hε
  have hd : DenseRange (Pi.map fun (_ : J) (r : ℚ) => (r : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  have hf : ∃ᶠ x in 𝓝 x₀, F (v, x) = F (v₀, x) := by
    refine ((mem_closure_iff_frequently.1 (hd x₀)).and_eventually (Metric.ball_mem_nhds x₀ hε)).mono ?_
    rintro x ⟨⟨r, hr⟩, hx⟩
    funext i
    have hc : ContinuousOn (fun t : E => F (t, x) i) (Metric.ball v₀ ε) := fun t ht =>
      ((continuous_apply i).continuousAt.comp
        ((hb _ (hm ht hx)).1.comp (f := fun t : E => (t, x)) (by fun_prop))).continuousWithinAt
    have hs := (countable_range (Rat.cast : ℚ → ℝ)).isTotallyDisconnected _
      (by
        rintro _ ⟨t, ht, rfl⟩
        obtain ⟨q, hq⟩ := (hb _ (hm ht hx)).2 (fun j => ⟨r j, by rw [← hr]; rfl⟩) i
        exact ⟨q, hq.symm⟩)
      ((convex_ball v₀ ε).isPreconnected.image _ hc)
    exact hs (mem_image_of_mem _ hv) (mem_image_of_mem _ h0)
  exact tendsto_nhds_unique_of_frequently_eq
    ((hb _ (hm hv hx0)).1.comp (f := fun x : J → ℝ => (v, x)) (by fun_prop))
    ((hb _ (hm h0 hx0)).1.comp (f := fun x : J → ℝ => (v₀, x)) (by fun_prop)) hf

theorem rat_iff {J : Type} [Fintype J] (x : J → ℝ) :
    (∀ i, ∃ r : ℚ, x i = r) ↔ ∃ N : ℕ, 0 < N ∧ ∀ i, ∃ n : ℤ, (N • x) i = n := by
  constructor
  · intro h
    choose r hr using h
    refine ⟨∏ i, (r i).den, Finset.prod_pos fun i _ => (r i).pos, fun i => ?_⟩
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun i => (r i).den) (Finset.mem_univ i)
    refine ⟨(r i).num * m, ?_⟩
    have := congrArg (Rat.cast : ℚ → ℝ) (Rat.mul_den_eq_num (r i))
    push_cast at this
    rw [hm, Pi.smul_apply, hr, nsmul_eq_mul]
    push_cast
    rw [← this]
    ring
  · rintro ⟨N, hN, h⟩ i
    obtain ⟨n, hn⟩ := h i
    refine ⟨n / N, ?_⟩
    have : (N : ℝ) ≠ 0 := by positivity
    rw [Pi.smul_apply, nsmul_eq_mul] at hn
    push_cast
    rw [← hn]
    field_simp

theorem per_nsmul {g : ℕ} (t : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) (x : Fl g) : per t (N • x) = N • per t x := by
  ext i
  simp [per, vecMul, dotProduct, mul_add, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _

theorem mem_stdLat_iff {g : ℕ} {x : Fl g} : x ∈ stdLat g ↔ ∀ i, ∃ n : ℤ, x i = n := by
  rw [stdLat, Module.Basis.mem_span_iff_repr_mem]
  exact forall_congr' fun i => ⟨fun ⟨n, hn⟩ => ⟨n, by simpa using hn.symm⟩,
    fun ⟨n, hn⟩ => ⟨n, by simpa using hn.symm⟩⟩

theorem props {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ} (h : IsPeriodMap B τ) : FlatFormProps B τ :=
  ((GlobalTheory.FlatCubicalProof.flatCubical g).1 E B τ h).1

theorem torsion_iff {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {σ : k →+* ℂ} {A : Over S}
    [GrpObj A] {g D : ℕ} {w : VMetric p (omega A) g} {c : AlgChart p σ D}
    {τ : V D → Matrix (Fin g) (Fin g) ℂ} {ex : Pt (V D) g → CxPts (A.hom ≫ p) σ}
    (H : IsPeriodChart w c τ ex) {Q : Pt (V D) g} (hQ : Q ∈ cov c.e.target g)
    (X : Over.mk ((ex Q).1 ≫ A.hom) ⟶ A) (hX : X.left = (ex Q).1) :
    (∀ i, ∃ r : ℚ, flat τ Q i = r) ↔ ∃ N : ℕ, 0 < N ∧ X ^ N = 1 := by
  obtain ⟨v, z⟩ := Q
  have hv : v ∈ c.e.target := hQ.1
  obtain ⟨h₁, h₂, -, h₄, -⟩ := H.2.2 v hv
  obtain ⟨f₁, f₂⟩ := (props H.1).1 v hv
  revert X
  rw [h₁ z]
  intro X hX
  have e₁ : (1 : Over.mk (c.e.symm v).1 ⟶ A).left = (c.e.symm v).1 ≫ unitSec A := by
    rw [Hom.one_def]
    simp
    rfl
  have hp (N : ℕ) : (X ^ N).left = (ex (v, N • z)).1 := by
    induction N with
    | zero =>
      rw [pow_zero, e₁, zero_smul]
      refine ((h₄ 0).2 ⟨0, zero_mem _, ?_⟩).symm
      simpa using (per_nsmul (τ v) 0 0).symm
    | succ n ih => rw [pow_succ, h₂ _ _ _ _ ih hX, succ_nsmul]
  rw [rat_iff]
  refine exists_congr fun N => and_congr_right fun _ => ?_
  rw [← mem_stdLat_iff]
  have e : N • z = per (τ v) (N • flat τ (v, z)) := by
    rw [per_nsmul]; exact congrArg _ (f₂ z).symm
  refine ⟨fun h => Over.OverMorphism.ext ?_, fun h => ?_⟩
  · rw [hp, e₁]
    exact (h₄ _).2 ⟨_, h, e⟩
  · obtain ⟨l, hl, el⟩ := (h₄ _).1 ((hp N).symm.trans ((congrArg (·.left) h).trans e₁))
    have := congrArg (flatOf (τ v)) (e.symm.trans el)
    rw [f₁, f₁] at this
    exact this ▸ hl

theorem dflat_eq_zero_of_rat {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ}
    {B B' : Set E} {τ τ' : E → Matrix (Fin g) (Fin g) ℂ} (h : IsPeriodMap B τ) (h' : IsPeriodMap B' τ')
    {P : Pt E g} (hP : P ∈ cov B g) {ψ : Pt E g → Pt E g} (hψ : DifferentiableAt ℂ ψ P)
    (hc : ∀ᶠ Q in 𝓝 P, ContinuousAt ψ Q ∧ ψ Q ∈ cov B' g ∧
      ((∀ i, ∃ r : ℚ, flat τ Q i = r) → ∀ i, ∃ r : ℚ, flat τ' (ψ Q) i = r))
    (u : Pt E g) (hu : dflat τ P u = 0) : dflat τ' (ψ P) (fderiv ℂ ψ P u) = 0 := by
  have f := props h
  have f' := props h'
  have hP1 : P.1 ∈ B := hP.1
  set x₀ := flat τ P with hx₀
  let t : E × Fl g → Pt E g := fun Q => (Q.1, per (τ Q.1) Q.2)
  have ht (Q : E × Fl g) (hQ : Q.1 ∈ B) : AnalyticAt ℝ t Q :=
    analyticAt_fst.prod (f.2.2.1 Q ⟨hQ, trivial⟩)
  have hft (Q : E × Fl g) (hQ : Q.1 ∈ B) : flat τ (t Q) = Q.2 := (f.1 _ hQ).1 _
  have ht0 : t (P.1, x₀) = P := Prod.ext rfl ((f.1 _ hP1).2 _)
  have hB : ∀ᶠ v in 𝓝 P.1, v ∈ B := h.1.mem_nhds hP1
  have hconst : ∀ᶠ v in 𝓝 P.1, flat τ' (ψ (t (v, x₀))) = flat τ' (ψ (t (P.1, x₀))) := by
    refine eventually_eq_of_rat (fun Q => flat τ' (ψ (t Q))) P.1 x₀ ?_
    have a := (ht (P.1, x₀) hP1).continuousAt
    rw [ContinuousAt, ht0] at a
    filter_upwards [a.eventually hc, (continuousAt_fst (p := (P.1, x₀))).eventually hB] with Q hQ hQB
    refine ⟨((f'.2.1 _ hQ.2.1).continuousAt.comp hQ.1).comp (ht Q hQB).continuousAt, fun hr => hQ.2.2 ?_⟩
    rwa [hft Q hQB]
  have hs : DifferentiableAt ℝ (fun v => t (v, x₀)) P.1 :=
    (ht (P.1, x₀) hP1).differentiableAt.comp (f := fun v => (v, x₀)) _ (by fun_prop)
  set L := fderiv ℝ (fun v => t (v, x₀)) P.1 with hL
  have hsL : HasFDerivAt (fun v => t (v, x₀)) L P.1 := hs.hasFDerivAt
  have hL1 (a : E) : (L a).1 = a :=
    congrArg (· a) (hsL.fst.unique (hasFDerivAt_id P.1))
  have hL2 (a : E) : dflat τ P (L a) = 0 := by
    have d : HasFDerivAt (flat τ) (dflat τ P) (t (P.1, x₀)) :=
      ht0.symm ▸ (f.2.1 P hP).differentiableAt.hasFDerivAt
    have d₀ : HasFDerivAt (flat τ ∘ fun v => t (v, x₀)) (0 : E →L[ℝ] Fl g) P.1 :=
      (hasFDerivAt_const x₀ P.1).congr_of_eventuallyEq (hB.mono fun v hv => hft (v, x₀) hv)
    have e := (d.comp P.1 hsL).unique d₀
    exact congrArg (· a) e
  have hua : u = L u.1 := by
    refine Prod.ext (hL1 _).symm (((f.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 P hP).2 u.1).unique hu ?_)
    have := hL2 u.1
    rwa [← Prod.mk.eta (p := L u.1), hL1] at this
  have dψ : HasFDerivAt ψ ((fderiv ℂ ψ P).restrictScalars ℝ) (t (P.1, x₀)) :=
    ht0.symm ▸ hψ.hasFDerivAt.restrictScalars ℝ
  have d' : HasFDerivAt (flat τ') (dflat τ' (ψ P)) (ψ (t (P.1, x₀))) :=
    ht0.symm ▸ (f'.2.1 _ hc.self_of_nhds.2.1).differentiableAt.hasFDerivAt
  have d₀ : HasFDerivAt (flat τ' ∘ ψ ∘ fun v => t (v, x₀)) (0 : E →L[ℝ] Fl g) P.1 :=
    (hasFDerivAt_const _ P.1).congr_of_eventuallyEq hconst
  have e := (d'.comp P.1 (dψ.comp P.1 hsL)).unique d₀
  rw [hua]
  exact congrArg (· u.1) e

theorem dflat_change_eq_zero : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (A : Over S) [GrpObj A]
    (g : ℕ) (w : VMetric p (omega A) g) (σ : k →+* ℂ) (D : ℕ) (c c' : AlgChart p σ D)
    (τ τ' : V D → Matrix (Fin g) (Fin g) ℂ) (ex ex' : Pt (V D) g → CxPts (A.hom ≫ p) σ),
    IsPeriodChart w c τ ex → IsPeriodChart w c' τ' ex' → ∀ P ∈ cov c.e.target g,
    ∀ ψ : Pt (V D) g → Pt (V D) g, DifferentiableAt ℂ ψ P →
    (∀ᶠ Q in 𝓝 P, ContinuousAt ψ Q ∧ ψ Q ∈ cov c'.e.target g ∧ ex' (ψ Q) = ex Q) →
    ∀ u : Pt (V D) g, dflat τ P u = 0 → dflat τ' (ψ P) (fderiv ℂ ψ P u) = 0 := by
  intro k _ S p A _ g w σ D c c' τ τ' ex ex' H H' P hP ψ hψ hc u hu
  refine dflat_eq_zero_of_rat H.1 H'.1 hP hψ ?_ u hu
  have ho : IsOpen (cov c.e.target g) := H.1.1.prod isOpen_univ
  filter_upwards [hc, ho.mem_nhds hP] with Q hQ hQc
  refine ⟨hQ.1, hQ.2.1, fun hr => ?_⟩
  rw [torsion_iff H' hQ.2.1 (Over.homMk (ex' (ψ Q)).1 rfl) rfl, hQ.2.2]
  exact (torsion_iff H hQc _ rfl).1 hr

end GlobalTheory.HorizontalChange
