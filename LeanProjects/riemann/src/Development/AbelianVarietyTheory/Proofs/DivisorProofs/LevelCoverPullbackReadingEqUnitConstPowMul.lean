import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenScal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSecOfMoveInv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExistsBorelOrthonormalMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevRead

theorem eq_const_mul_of_norm_one {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type*} (U : Set V)
    (hU : IsOpen U) (hc : IsPreconnected U) (P₂ P : ι → V → ℂ) (g : V → ℂ)
    (hP₂ : ∀ i, DifferentiableOn ℂ (P₂ i) U) (hP : ∀ i, DifferentiableOn ℂ (P i) U) (hg1 : ∀ x ∈ U, ‖g x‖ = 1)
    (hg : ∀ i, ∀ x ∈ U, P₂ i x = g x * P i x) : ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ i, ∀ x ∈ U, P₂ i x = u * P i x := by
  by_cases h : ∃ i, ∃ x ∈ U, P i x ≠ 0
  swap
  · push_neg at h
    refine ⟨1, by simp, fun i x hx => ?_⟩
    rw [hg i x hx, h i x hx]
    simp
  obtain ⟨i₀, x₀, hx₀, hne⟩ := h
  have hcont : ContinuousAt (P i₀) x₀ := (hP i₀).continuousOn.continuousAt (hU.mem_nhds hx₀)
  have hnb : ∀ᶠ y in nhds x₀, y ∈ U ∧ P i₀ y ≠ 0 := (hU.eventually_mem hx₀).and (hcont.eventually_ne hne)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnb
  have hx₀b : x₀ ∈ Metric.ball x₀ ε := Metric.mem_ball_self hε
  let q : V → ℂ := fun y => P₂ i₀ y * (P i₀ y)⁻¹
  have hqd : DifferentiableOn ℂ q (Metric.ball x₀ ε) :=
    ((hP₂ i₀).mono (fun y hy => (hball y hy).1)).mul (((hP i₀).mono (fun y hy => (hball y hy).1)).inv
      (fun y hy => (hball y hy).2))
  have hqg : ∀ y ∈ Metric.ball x₀ ε, q y = g y := fun y hy => by
    simp only [q]
    rw [hg i₀ y (hball y hy).1, mul_assoc, mul_inv_cancel₀ (hball y hy).2, mul_one]
  have hmax : IsMaxOn (norm ∘ q) (Metric.ball x₀ ε) x₀ := fun y hy => by
    simp only [Set.mem_setOf_eq, Function.comp_apply]
    rw [hqg y hy, hqg x₀ hx₀b, hg1 _ (hball y hy).1, hg1 _ (hball x₀ hx₀b).1]
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball x₀ ε).isPreconnected
    Metric.isOpen_ball hqd hx₀b hmax
  refine ⟨g x₀, hg1 x₀ hx₀, fun i => ?_⟩
  have hzero : ∀ y ∈ U, (fun y => P₂ i y - g x₀ * P i y) y = 0 := by
    refine ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_eventually hU hc ((hP₂ i).sub ((hP i).const_mul (g x₀))) hx₀ ?_
    filter_upwards [Metric.ball_mem_nhds x₀ hε] with y hy
    have e : g y = g x₀ := by
      rw [← hqg y hy, ← hqg x₀ hx₀b]
      exact heq hy
    simp only [Pi.zero_apply]
    rw [hg i y (hball y hy).1, e]
    ring
  intro x hx
  have := hzero x hx
  simp only at this
  exact sub_eq_zero.1 this

theorem exists_open_ne_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type*} (U : Set V)
    (hU : IsOpen U) (hc : IsPreconnected U) (hne : U.Nonempty) (P : ι → V → ℂ)
    (hP : ∀ i, DifferentiableOn ℂ (P i) U) (s : Finset ι) :
    ∃ W : Set V, IsOpen W ∧ W ⊆ U ∧ W.Nonempty ∧ ∀ i ∈ s, (∃ x ∈ U, P i x ≠ 0) → ∀ x ∈ W, P i x ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨U, hU, subset_rfl, hne, by simp⟩
  | insert i s _ ih =>
    obtain ⟨W, hWo, hWU, hWn, hW⟩ := ih
    by_cases h : ∃ x ∈ U, P i x ≠ 0
    · have hw : ∃ w ∈ W, P i w ≠ 0 := by
        by_contra hno
        push_neg at hno
        obtain ⟨x₀, hx₀⟩ := hWn
        have hz := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_eventually hU hc (hP i) (hWU hx₀)
          (Filter.eventuallyEq_of_mem (hWo.mem_nhds hx₀) (fun y hy => hno y hy))
        obtain ⟨x, hx, hx0⟩ := h
        exact hx0 (hz x hx)
      obtain ⟨w, hwW, hw0⟩ := hw
      refine ⟨W ∩ P i ⁻¹' {0}ᶜ, ((hP i).continuousOn.mono hWU).isOpen_inter_preimage hWo isOpen_compl_singleton,
        Set.inter_subset_left.trans hWU, ⟨w, hwW, hw0⟩, fun i' hi' hex x hx => ?_⟩
      rcases Finset.mem_insert.1 hi' with rfl | hi'
      · exact hx.2
      · exact hW i' hi' hex x hx.1
    · refine ⟨W, hWo, hWU, hWn, fun i' hi' hex x hx => ?_⟩
      rcases Finset.mem_insert.1 hi' with rfl | hi'
      · exact absurd hex h
      · exact hW i' hi' hex x hx

theorem eq_pow_mul_of_norm_one {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type*} (U : Set V)
    (hU : IsOpen U) (hc : IsPreconnected U) (m : ι → ℕ) (P₂ P : ι → V → ℂ) (g : V → ℂ)
    (hP₂ : ∀ i, DifferentiableOn ℂ (P₂ i) U) (hP : ∀ i, DifferentiableOn ℂ (P i) U) (hg1 : ∀ x ∈ U, ‖g x‖ = 1)
    (hg : ∀ i, ∀ x ∈ U, P₂ i x = g x ^ m i * P i x) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ i, ∀ x ∈ U, P₂ i x = u ^ m i * P i x := by
  by_cases hne : U.Nonempty
  swap
  · exact ⟨1, by simp, fun i x hx => absurd ⟨x, hx⟩ hne⟩
  have hone : ∀ i, ∃ u : ℂ, ∀ x ∈ U, P₂ i x = u * P i x := fun i => by
    obtain ⟨u, -, hu⟩ := eq_const_mul_of_norm_one (ι := Unit) U hU hc (fun _ => P₂ i) (fun _ => P i)
      (fun x => g x ^ m i) (fun _ => hP₂ i) (fun _ => hP i)
      (fun x hx => by rw [norm_pow, hg1 x hx, one_pow]) (fun _ => hg i)
    exact ⟨u, hu ()⟩
  let C : ι → Set ℂ := fun i => ⋂ x ∈ U, {t : ℂ | P₂ i x = t ^ m i * P i x}
  have hC : ∀ i, IsClosed (C i) := fun i => isClosed_biInter fun x _ =>
    isClosed_eq continuous_const ((continuous_pow _).mul continuous_const)
  have hfin : ∀ s : Finset ι, (Metric.sphere (0 : ℂ) 1 ∩ ⋂ i ∈ s, C i).Nonempty := by
    intro s
    obtain ⟨W, -, hWU, ⟨x₀, hx₀⟩, hW⟩ := exists_open_ne_zero U hU hc hne P hP s
    refine ⟨g x₀, by simpa using hg1 x₀ (hWU hx₀), Set.mem_iInter₂.2 fun i hi => Set.mem_iInter₂.2 fun x hx => ?_⟩
    show P₂ i x = g x₀ ^ m i * P i x
    by_cases h : ∃ x ∈ U, P i x ≠ 0
    · obtain ⟨u, hu⟩ := hone i
      have hnz := hW i hi h x₀ hx₀
      have e : u = g x₀ ^ m i := mul_right_cancel₀ hnz ((hu x₀ (hWU hx₀)).symm.trans (hg i x₀ (hWU hx₀)))
      rw [hu x hx, e]
    · push_neg at h
      rw [hg i x hx, h x hx]
      simp
  obtain ⟨u, hu1, hu⟩ := (isCompact_sphere (0 : ℂ) 1).inter_iInter_nonempty C hC hfin
  refine ⟨u, by simpa using hu1, fun i x hx => ?_⟩
  exact Set.mem_iInter₂.1 (Set.mem_iInter.1 hu i) x hx

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

@[reducible] def fieldAt {K : Type} [Field K] (σ : K →+* ℂ) : Field (CAt σ) :=
  { (inferInstance : CommRing (CAt σ)), (inferInstanceAs (Field ℂ) : Field (CAt σ)) with }

theorem algClosedAt {K : Type} [Field K] (σ : K →+* ℂ) : @IsAlgClosed (CAt σ) (fieldAt σ) :=
  inferInstanceAs (IsAlgClosed ℂ)

theorem exists_pow_of_pointwise (X₂ X : Data E r) (δ : GL (Fin r) E) (hΨ : ∀ τ : E →+* ℂ, τ ∈ X₂.Ψ ↔ τ ∈ X.Ψ) {ι : Type}
    (m : ι → ℕ) (la₂ : ι → Wt X₂.Ψ r) (la : ι → Wt X.Ψ r)
    (hla : ∀ i (τ : E →+* ℂ) (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ) (a : Fin r), la₂ i ⟨τ, h₂⟩ a = la i ⟨τ, h₁⟩ a)
    (Q₂ : ι → Frame X₂.Ψ r → ℂ) (Q : ι → Frame X.Ψ r → ℂ)
    (hQ₂ : ∀ i, X₂.IsSec (la₂ i) (Q₂ i)) (hQ : ∀ i, X.IsSec (la i) (Q i))
    (hdom : ∀ x ∈ X₂.dom, ∀ x', GlobalTheory.LevModel.Moved X₂ X δ x x' → x' ∈ X.dom)
    (hpt : ∀ x ∈ X₂.dom, ∀ x', GlobalTheory.LevModel.Moved X₂ X δ x x' →
      ∃ t : ℂ, ((∀ τ i, ‖dmin X₂.Gm x τ i‖ = 1) → ‖t‖ = 1) ∧ ∀ i, Q₂ i x = t ^ m i * Q i x') :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ i, ∀ x ∈ X₂.dom, ∀ x', GlobalTheory.LevModel.Moved X₂ X δ x x' → Q₂ i x = u ^ m i * Q i x' := by
  let G : Frame X₂.Ψ r → Frame X.Ψ r := fun x τ =>
    ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩ : Matrix (Fin r) (Fin r) ℂ)
  have hGrel : ∀ x, GlobalTheory.LevModel.Moved X₂ X δ x (G x) := fun x τ h₂ h₁ => rfl
  have hGdom : ∀ x ∈ X₂.dom, G x ∈ X.dom := fun x hx => hdom x hx (G x) (hGrel x)
  have hGdiff : Differentiable ℂ G := by
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
    simp only [G, mat, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]
    fun_prop
  have hPd : ∀ i, DifferentiableOn ℂ (fun x => Q i (G x)) X₂.dom := fun i =>
    (hQ i).1.comp hGdiff.differentiableOn hGdom
  have hg : ∀ x ∈ X₂.dom, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i : ι, Q₂ i x = c ^ m i * Q i (G x) := by
    intro x hxd
    obtain ⟨b, hb, hyd, hyo⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_borel_orthonormal_move X₂ hxd
    obtain ⟨t, hmod, hrd⟩ := hpt (rmul x b) hyd (G (rmul x b)) (hGrel _)
    have ht1 : ‖t‖ = 1 := hmod (fun τ i => ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_diagonal_minor_one _ hyo τ i)
    refine ⟨t, ht1, fun i => ?_⟩
    let b₁ : Frame X.Ψ r := fun τ => b ⟨τ.1, (hΨ τ.1).2 τ.2⟩
    have hb₁ : b₁ ∈ Bor X.Ψ r := fun τ => hb ⟨τ.1, (hΨ τ.1).2 τ.2⟩
    have e1 := hrd i
    have e2 : Q₂ i (rmul x b) = bchar (la₂ i) b * Q₂ i x := (hQ₂ i).2.1 x hxd b hb
    have e3 : G (rmul x b) = rmul (G x) b₁ := by
      funext τ
      simp only [G, rmul, b₁, mat]
      exact (Matrix.mul_assoc ((δ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩) (mat b ⟨τ.1, (hΨ τ.1).2 τ.2⟩)).symm
    have e4 : Q i (rmul (G x) b₁) = bchar (la i) b₁ * Q i (G x) := (hQ i).2.1 (G x) (hGdom x hxd) b₁ hb₁
    have e5 : bchar (la₂ i) b = bchar (la i) b₁ := by
      unfold bchar
      refine Fintype.prod_equiv (Equiv.subtypeEquivRight (fun τ => hΨ τ)) _ _ (fun τ => ?_)
      refine Finset.prod_congr rfl (fun a _ => ?_)
      rw [hla i τ.1 τ.2 ((hΨ τ.1).1 τ.2) a]
      rfl
    have e6 : bchar (la₂ i) b ≠ 0 := by
      unfold bchar
      refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun a _ => zpow_ne_zero _ ?_
      have hdet : (mat b τ).det ≠ 0 := (hb τ).1
      rw [Matrix.det_of_upperTriangular (M := mat b τ) (fun a c h => (hb τ).2 a c h)] at hdet
      simpa [mat] using Finset.prod_ne_zero_iff.1 hdet a (Finset.mem_univ _)
    apply mul_left_cancel₀ e6
    rw [← e2, e1, e3, e4, ← e5]
    ring
  classical
  let g : Frame X₂.Ψ r → ℂ := fun x => if h : x ∈ X₂.dom then (hg x h).choose else 1
  have hg1 : ∀ x ∈ X₂.dom, ‖g x‖ = 1 := fun x h => by
    simp only [g, dif_pos h]; exact (hg x h).choose_spec.1
  have hgr : ∀ i : ι, ∀ x ∈ X₂.dom, Q₂ i x = g x ^ m i * Q i (G x) := fun i x h => by
    simp only [g, dif_pos h]; exact (hg x h).choose_spec.2 i
  obtain ⟨u, hu1, hu⟩ := eq_pow_mul_of_norm_one X₂.dom (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom _)
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X₂).isPreconnected m Q₂ (fun i x => Q i (G x)) g
    (fun i => (hQ₂ i).1) hPd hg1 hgr
  refine ⟨u, hu1, fun i x hxd x' hm => ?_⟩
  have hx' : x' = G x := by
    funext τ
    exact hm τ.1 ((hΨ τ.1).2 τ.2) τ.2
  rw [hx']
  exact hu i x hxd

end Flag

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem wchar_genScal {S : Type} [CommRing S] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t : Sˣ) :
    wchar (ex Dw a n) (GlobalTheory.LevModel.genScal (Dw := Dw) t) = (t : S) ^ n := by
  classical
  unfold wchar
  rw [Fintype.prod_option]
  have h1 : ∀ i : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), ((GlobalTheory.LevModel.genScal (Dw := Dw) t (some i) : Sˣ) : S) = 1 := by
    intro i
    simp [GlobalTheory.LevModel.genScal]
  have h2 : ((GlobalTheory.LevModel.genScal (Dw := Dw) t none : Sˣ) : S) = t := by
    simp [GlobalTheory.LevModel.genScal]
  simp only [h1, h2, one_pow, Finset.prod_const_one, mul_one]
  rfl

theorem evR_pull_genScal {k : Type} [Field k] [IsAlgClosed k] [Algebra c.F k] (d : DeltaDat Xo c 0) [Algebra d.c₂.F k]
    (hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) {g : Rul d.Xo₂ d.c₂} (hP : Pull d f g) (t : kˣ) {y₀ y : FrPt Xo c k} {y₂ : FrPt d.Xo₂ d.c₂ k}
    (hb : FrBor (GlobalTheory.LevModel.genScal (Dw := Dw) t) y₀ y) (hov : FrOver d y₂ y) :
    evR d.Xo₂ d.c₂ g y₂ = (t : k) ^ n * evR Xo c f y₀ := by
  rw [hP k hk y₂ y hov, GlobalTheory.ThetaSumDescent.evR_frBor hf hb, wchar_genScal]

theorem laU_eq {l₂ : Level H} {Xo₂ : Moduli Dw l₂} {c₂ : Coeff l₂} {σ₂ : c₂.F →+* ℂ} {σ : c.F →+* ℂ}
    (U₂ : Unf Xo₂ c₂ σ₂ r) (U : Unf Xo c σ r) (k₂ : U₂.Comp) (k : U.Comp) (hp : (U₂.X k₂).p0 = (U.X k).p0)
    (hrel : relab c₂ σ₂ = relab c σ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : E →+* ℂ) (h₂ : τ ∈ (U₂.X k₂).Ψ)
    (h₁ : τ ∈ (U.X k).Ψ) (i : Fin r) : laU U₂ a n k₂ ⟨τ, h₂⟩ i = laU U a n k ⟨τ, h₁⟩ i := by
  unfold laU
  rw [hp, hrel]

theorem read_pointwise (d : DeltaDat Xo c 0) (σ₂ : d.c₂.F →+* ℂ) (U : Unf Xo c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) r)
    (U₂ : Unf d.Xo₂ d.c₂ σ₂ r) (k₂ : U₂.Comp) (k : U.Comp) (δ : GL (Fin r) E)
    (hOver : GlobalTheory.LevModel.Over d σ₂ U U₂ k₂ k δ) (x : Frame (U₂.X k₂).Ψ r) (hx : x ∈ (U₂.X k₂).dom)
    (x' : Frame (U.X k).Ψ r) (hm : GlobalTheory.LevModel.Moved (U₂.X k₂) (U.X k) δ x x') :
    ∃ t : ℂ, ((∀ τ i, ‖dmin (U₂.X k₂).Gm x τ i‖ = 1) → ‖t‖ = 1) ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ g : Rul d.Xo₂ d.c₂, Pull d f g →
        rdU U₂ g k₂ x = t ^ n * rdU U f k x' := by
  obtain ⟨hx', t, hmod, hy⟩ := hOver x hx x' hm
  letI a₁ : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  obtain ⟨y, hb, hov⟩ := hy
  refine ⟨t, hmod, fun a n f hf g hP => ?_⟩
  have r2 : rdU U₂ g k₂ x = toC (evR d.Xo₂ d.c₂ g (U₂.un k₂ ⟨x, hx⟩)) := dif_pos hx
  have r1 : rdU U f k x' = toC (evR Xo c f (U.un k ⟨x', hx'⟩)) := dif_pos hx'
  rw [r2, r1]
  exact @evR_pull_genScal E _ _ _ H Dw l Xo c ℂ _ _ a₁ d (inferInstanceAs (Algebra d.c₂.F (CAt σ₂))) (fun _ => rfl)
    a n f hf g hP t _ _ _ hb hov

end Point

theorem reading_pull : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d f g → ∀ (x : Frame ((U₂ σ₂).X k₂).Ψ D.R.r) (x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r), x ∈ ((U₂ σ₂).X k₂).dom → GlobalTheory.LevModel.Moved ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ x x' → Even n → rdU (U₂ σ₂) g k₂ x = t ^ n * rdU (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) f k x' := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ _ σ₂ hσ₂ k₂ k δ _ _ hOver
  have hσ : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := hσ₂
  have hU₂ : IsUnf (U₂ σ₂) := hL₂.unf σ₂ hσ₂
  have hU₁ : IsUnf (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) := hL.unf _ hσ
  have hrel : relab d.c₂ σ₂ = relab c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := by
    funext τ
    ext x
    rfl
  have hΨ : ∀ τ : D.host.E →+* ℂ, τ ∈ ((U₂ σ₂).X k₂).Ψ ↔ τ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ :=
    fun τ => by rw [(hU₂.2.1 k₂).2 τ, (hU₁.2.1 k).2 τ]
  let ι := {p : ((D.host.E →+* ℂ) × ℕ → ℕ) × ℕ × Rul Xo c × Rul d.Xo₂ d.c₂ //
    Dom p.1 p.2.1 ∧ p.2.2.1 ∈ sec Xo c p.1 p.2.1 ∧ p.2.2.2 ∈ sec d.Xo₂ d.c₂ p.1 p.2.1 ∧ Pull d p.2.2.1 p.2.2.2}
  obtain ⟨u, hu1, hu⟩ := exists_pow_of_pointwise ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ hΨ (ι := ι)
    (fun i => i.1.2.1) (fun i => laU (U₂ σ₂) i.1.1 i.1.2.1 k₂) (fun i => laU (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) i.1.1 i.1.2.1 k)
    (fun i τ h₂ h₁ a => laU_eq (U₂ σ₂) (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) k₂ k ((hU₂.2.1 k₂).1.trans (hU₁.2.1 k).1.symm) hrel _ _ τ h₂ h₁ a)
    (fun i => rdU (U₂ σ₂) i.1.2.2.2 k₂) (fun i => rdU (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) i.1.2.2.1 k)
    (fun i => hU₂.2.2.2.2.1 i.1.1 i.1.2.1 i.2.1 i.1.2.2.2 i.2.2.2.1 k₂)
    (fun i => hU₁.2.2.2.2.1 i.1.1 i.1.2.1 i.2.1 i.1.2.2.1 i.2.2.1 k)
    (fun x hx x' hm => (hOver x hx x' hm).1)
    (fun x hx x' hm => by
      obtain ⟨t, hmod, ht⟩ := read_pointwise d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ hOver x hx x' hm
      exact ⟨t, hmod, fun i => ht i.1.1 i.1.2.1 i.1.2.2.1 i.2.2.1 i.1.2.2.2 i.2.2.2.2⟩)
  refine ⟨u, hu1, fun a n hDom f hf g hg hP x x' hxd hm _ => ?_⟩
  exact hu ⟨(a, n, f, g), hDom, hf, hg, hP⟩ x hxd x' hm

end GlobalTheory.LevRead
