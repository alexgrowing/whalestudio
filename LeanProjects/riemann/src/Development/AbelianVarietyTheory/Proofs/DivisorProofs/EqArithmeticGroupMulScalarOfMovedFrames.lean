import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenScal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelGamS

noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

namespace GlobalTheory.LevModel

theorem orbit_open_scalar {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (τ₀ : Ψ) (G : Subgroup (GL (Fin r) E)) (h : GL (Fin r) E) {O : Set (Frame Ψ r)} (hO : IsOpen O)
    (hne : O.Nonempty) (hdet : ∀ y ∈ O, (mat y τ₀).det ≠ 0)
    (H1 : ∀ y ∈ O, ∃ γ ∈ G, ∃ b ∈ Bor Ψ r, lact h y = rmul (lact γ y) b) :
    ∃ γ ∈ G, ∃ ζ : E, (h : Matrix (Fin r) (Fin r) E) = (γ : Matrix (Fin r) (Fin r) E) * Matrix.scalar (Fin r) ζ := by
  classical
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hO _ hy₀
  set B₀ := Metric.ball y₀ ρ with hB₀
  let f : Option G → Set (Frame Ψ r) := fun o => match o with
    | none => B₀ᶜ
    | some γ' => ReciprocityTheory.ChartRestriction.G.PullbackSections.TSet Ψ ((γ'.1⁻¹ * h : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
  have hc : ∀ o, IsClosed (f o) := by
    rintro (_ | γ')
    · exact Metric.isOpen_ball.isClosed_compl
    · exact ReciprocityTheory.ChartRestriction.G.PullbackSections.isClosed_TSet _ _
  have hU : ⋃ o, f o = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    by_cases hx : x ∈ B₀
    · obtain ⟨γ', hγ', b, hb, e⟩ := H1 x (hball hx)
      exact ⟨some ⟨γ', hγ'⟩, ReciprocityTheory.ChartRestriction.G.PullbackSections.mem_TSet Ψ h γ' hb e⟩
    · exact ⟨none, hx⟩
  have hd := dense_iUnion_interior_of_closed hc hU
  obtain ⟨y, hyB, hyU⟩ := hd.inter_open_nonempty B₀ Metric.isOpen_ball ⟨_, Metric.mem_ball_self hρ⟩
  obtain ⟨o, ho⟩ := Set.mem_iUnion.1 hyU
  cases o with
  | none => exact absurd hyB (interior_subset ho)
  | some γ' =>
    set g : Matrix (Fin r) (Fin r) E := ((γ'.1⁻¹ * h : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hg
    obtain ⟨κ, hκ⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.scalar_step τ₀ g
      (W := interior (f (some γ')) ∩ B₀) (isOpen_interior.inter Metric.isOpen_ball)
      (fun x hx => interior_subset hx.1) (y := y) ⟨ho, hyB⟩ (hdet y (hball hyB))
    have hent : ∀ a b, τ₀.1 (g a b) = if a = b then κ else 0 := by
      intro a b
      have := congrFun (congrFun hκ a) b
      simpa [Matrix.one_apply] using this
    have hh : (h : Matrix (Fin r) (Fin r) E) = (γ'.1 : Matrix (Fin r) (Fin r) E) * g := by
      rw [hg, ← Units.val_mul, mul_inv_cancel_left]
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      exact ⟨γ'.1, γ'.2, 0, by ext a; exact Fin.elim0 a⟩
    · refine ⟨γ'.1, γ'.2, g ⟨0, hr⟩ ⟨0, hr⟩, ?_⟩
      rw [hh]
      congr 1
      ext a b
      apply τ₀.1.injective
      rw [hent a b, Matrix.scalar_apply, Matrix.diagonal_apply]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos hab, hent, if_pos rfl]
      · rw [if_neg hab, if_neg hab, map_zero]

theorem eq_mul_scalar_of_moved {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X₂ X : Data E r) (δ h : GL (Fin r) E) (hΨ : X₂.Ψ = X.Ψ)
    (H : ∀ x ∈ X₂.dom, ∀ x' : Frame X.Ψ r, GlobalTheory.LevModel.Moved X₂ X δ x x' → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact h x' = rmul (lact γ x') b) :
    ∃ γ ∈ X.Γ, ∃ ζ : E, (h : Matrix (Fin r) (Fin r) E) = (γ : Matrix (Fin r) (Fin r) E) * Matrix.scalar (Fin r) ζ := by
  classical

  obtain ⟨τ₁⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ, τ ∈ X.Ψ := by
    by_cases hτ : τ₁ ∈ X.Ψ
    · exact ⟨τ₁, hτ⟩
    · refine ⟨ComplexEmbedding.conjugate τ₁, ?_⟩
      by_contra hc
      exact hτ ((X.cmType τ₁).2 hc)
  have hmem : ∀ τ : X₂.Ψ, τ.1 ∈ X.Ψ := fun τ => hΨ ▸ τ.2
  have hmem' : ∀ τ : X.Ψ, τ.1 ∈ X₂.Ψ := fun τ => hΨ.symm ▸ τ.2

  let back : Frame X.Ψ r → Frame X₂.Ψ r := fun y τ =>
    (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y ⟨τ.1, hmem τ⟩ : Matrix (Fin r) (Fin r) ℂ)
  let fwd : Frame X₂.Ψ r → Frame X.Ψ r := fun x τ =>
    ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, hmem' τ⟩ : Matrix (Fin r) (Fin r) ℂ)
  have hback : Continuous back := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    have hm : Continuous fun y : Frame X.Ψ r => mat y ⟨τ.1, hmem τ⟩ := continuous_apply _
    exact (continuous_const.matrix_mul hm).matrix_elem a b
  have hbf : ∀ x, back (fwd x) = x := by
    intro x
    funext τ
    show (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) : Matrix (Fin r) (Fin r) ℂ) = mat x τ
    rw [← Matrix.mul_assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.map_gl_inv_mul, Matrix.one_mul]
  have hmoved : ∀ y, GlobalTheory.LevModel.Moved X₂ X δ (back y) y := by
    intro y τ h₂ h₁
    show mat y ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ *
      (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ * mat y ⟨τ, h₁⟩)
    rw [← Matrix.mul_assoc]
    have := ReciprocityTheory.ChartRestriction.G.PullbackSections.map_gl_inv_mul τ (δ⁻¹ : GL (Fin r) E)
    rw [inv_inv] at this
    rw [this, Matrix.one_mul]
  have hdom : (X₂.dom).Nonempty := ⟨_, ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.dom_of_orth X₂ (ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.chosenFrame_isOrthogonal X₂)⟩
  obtain ⟨x₀, hx₀⟩ := hdom
  refine orbit_open_scalar ⟨τ₀, hτ₀⟩ X.Γ h (O := back ⁻¹' X₂.dom)
    ((ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X₂).preimage hback) ⟨fwd x₀, by rw [Set.mem_preimage, hbf]; exact hx₀⟩ ?_
    (fun y hy => H _ hy y (hmoved y))
  intro y hy
  have h1 := (hy ⟨τ₀, hmem' ⟨τ₀, hτ₀⟩⟩).1
  have h2 : mat (back y) ⟨τ₀, hmem' ⟨τ₀, hτ₀⟩⟩ =
      ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ₀ * mat y ⟨τ₀, hτ₀⟩ := rfl
  rw [h2, Matrix.det_mul] at h1
  exact right_ne_zero_of_mul h1

end GlobalTheory.LevModel
