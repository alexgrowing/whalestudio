import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramSchmidtFlagDomainOrthonormalFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameUnitCorrespondenceStatement

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.Descent

theorem lact_mul {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ γ' : GL (Fin r) E) (x : Frame Ψ r) :
    lact (γ * γ') x = lact γ (lact γ' x) := by
  funext τ
  show ((γ * γ' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
    (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((γ' : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem lact_rmul {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ : GL (Fin r) E) (x b : Frame Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) =
    ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) * mat b τ
  rw [Matrix.mul_assoc]

theorem archM_mul {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    archM V θ (a * b) = archM V θ a * archM V θ b := by
  simp only [archM, map_mul, Units.val_mul, Matrix.map_mul]

theorem isUnit_of_negFirst {D : D7} {V : HSp D} {q : ℕ} {x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : NegFirst V q x) (ρ : D.what₂.Tau) : IsUnit (x ρ) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  have h1 := congrArg Matrix.det (h ρ)
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at h1
  refine (Finset.prod_ne_zero_iff.2 fun c _ => ?_) h1.symm
  split_ifs <;> simp

theorem archM_eq_of_frIs {D : D7} {θ : InfFam D} {V : HSp D} {r : ℕ} {hr : V.rank = r} {X : Data D.host.E r}
    {x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hM : ModelOf V hr X) (hx : NegFirst V X.p0 x)
    {u u' : GA D V} {y : Frame X.Ψ r} (h : FrIs θ V hr X x u y) (h' : FrIs θ V hr X x u' y) (ρ : D.what₂.Tau) :
    archM V (θ ρ) u = archM V (θ ρ) u' := by
  have e := (h ρ ⟨tauE D ρ, (hM.1 _).2 ⟨ρ, rfl⟩⟩ rfl).symm.trans (h' ρ ⟨tauE D ρ, (hM.1 _).2 ⟨ρ, rfl⟩⟩ rfl)
  exact (isUnit_of_negFirst hx ρ).mul_right_cancel ((Matrix.reindex _ _).injective e)

theorem descent : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → Data D.host.E r) (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V)) (x₀ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (ψ : GA D V → ℂ), IsInfFam θ → BaseDict θ V hr X dict Kf x₀ → (∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) → (∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) → (∀ k ∈ Kf, ∀ g, ψ (g * k) = ψ g) → (∀ (k : Comp) (g : GA D V), ∃ Q : Frame (X k).Ψ r → ℂ, DifferentiableOn ℂ Q (X k).dom ∧ (∀ y ∈ (X k).dom, ∀ b ∈ Bor (X k).Ψ r, Q (rmul y b) = bchar (la k) b * Q y) ∧ ∀ u ∈ GinfC V, ∀ y, FrIs θ V hr (X k) x₀ u y → Q y = ψ (g * u)) → ∃ P : FDSec X, (∀ k, (X k).IsSec (la k) (P k)) ∧ (∀ g, ψ g = P (dict g).1 (dict g).2) ∧ ∀ C : ℝ, (∀ g, ‖ψ g‖ ≤ C) → ∀ k, ∀ y ∈ (X k).dom, (X k).pnorm (la k) (P k) y ≤ C := by
  intro D θ V r hr Comp X dict Kf x₀ la ψ hθ hB hχ hL hR hQ
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have hF : ∀ (k : Comp) (h h' : GA D V) (z : Frame (X k).Ψ r), ∀ γ ∈ (X k).Γ,
      dict h = ⟨k, z⟩ → dict h' = ⟨k, lact γ z⟩ → ψ h' = ψ h := by
    intro k h h' z γ hγ e e'
    have key : ∀ p : Σ k, Frame (X k).Ψ r, p = ⟨k, z⟩ →
        ∃ γ' ∈ (X p.1).Γ, dict h' = ⟨p.1, lact γ' p.2⟩ := by
      rintro p rfl
      exact ⟨γ, hγ, e'⟩
    obtain ⟨δ, hδ, κ, hκ, rfl⟩ := hB3 h h' (key _ e)
    rw [hR κ hκ, hL δ hδ]
  have hK : ∀ k : Comp, ∃ Q : Frame (X k).Ψ r → ℂ, DifferentiableOn ℂ Q (X k).dom ∧
      (∀ y ∈ (X k).dom, ∀ b ∈ Bor (X k).Ψ r, Q (rmul y b) = bchar (la k) b * Q y) ∧
      ∀ y, IsUnitFr (X k) y → ∃ h, ∃ γ ∈ (X k).Γ, dict h = ⟨k, lact γ y⟩ ∧ Q y = ψ h := by
    intro k
    obtain ⟨hM, hN, g, rfl⟩ := hB1 k
    obtain ⟨U1, U2, -, U4, -⟩ := GlobalTheory.T.frame_unit_correspondence D θ V r hr (X (dict g).1) x₀ hθ hM hN
    obtain ⟨γ, hγ, hfr, hu⟩ := hB2 g
    obtain ⟨a, ha, hfa⟩ := U2 _ (U1 _ _ hfr)
    have ea := archM_eq_of_frIs hM hN hfr hfa
    obtain ⟨Q, hQ1, hQ2, hQ3⟩ := hQ (dict g).1 (γ * g * a⁻¹)
    refine ⟨Q, hQ1, hQ2, fun y hy => ?_⟩
    obtain ⟨v, hv, hfv⟩ := U2 y hy
    obtain ⟨γ', hγ', y', hd, hfy'⟩ := hu (a⁻¹ * v) (mul_mem (inv_mem ha) hv)
    have hfy : FrIs θ V hr (X (dict g).1) x₀ v y' := by
      intro ρ τ hτ
      rw [hfy' ρ τ hτ, archM_mul V _ (γ * g), ea ρ, ← archM_mul, mul_inv_cancel_left]
    obtain rfl : y' = y := U4 v _ _ hfy hfv
    refine ⟨_, γ', hγ', hd, ?_⟩
    rw [hQ3 v hv _ hfv, ← hL γ hγ (g * (a⁻¹ * v))]
    simp only [mul_assoc]
  choose P hP1 hP2 hP3 using hK
  refine ⟨P, fun k => ⟨hP1 k, hP2 k, fun γ hγ x hx => ?_⟩, fun g => ?_, fun C hC k x hx => ?_⟩
  · obtain ⟨G1, G2, -, -, G5, -⟩ := GlobalTheory.T.gramSchmidt_flagDomain_orthonormalFrames D.host.E r (X k)
    obtain ⟨y, hy, b, hb, rfl⟩ := G2 x hx
    have hy' := G5 y hy γ hγ
    obtain ⟨h, γ₁, hγ₁, hd, he⟩ := hP3 k y hy
    obtain ⟨h', γ₂, hγ₂, hd', he'⟩ := hP3 k _ hy'
    have e : ψ h' = ψ h := by
      refine hF k h h' _ (γ₂ * γ * γ₁⁻¹) (mul_mem (mul_mem hγ₂ hγ) (inv_mem hγ₁)) hd ?_
      rw [hd', ← lact_mul, ← lact_mul, inv_mul_cancel_right]
    rw [hχ k γ hγ, one_mul, lact_rmul, hP2 k _ (G1 _ hy') b hb, hP2 k _ (G1 _ hy) b hb, he, he', e]
  · obtain ⟨hM, hN, -⟩ := hB1 (dict g).1
    obtain ⟨U1, -⟩ := GlobalTheory.T.frame_unit_correspondence D θ V r hr (X (dict g).1) x₀ hθ hM hN
    obtain ⟨γ, -, hfr, -⟩ := hB2 g
    obtain ⟨h, γ₁, hγ₁, hd, he⟩ := hP3 _ _ (U1 _ _ hfr)
    rw [he]
    exact (hF _ g h _ γ₁ hγ₁ rfl hd).symm
  · obtain ⟨G1, G2, -, -, -, -, G7⟩ := GlobalTheory.T.gramSchmidt_flagDomain_orthonormalFrames D.host.E r (X k)
    obtain ⟨y, hy, b, hb, rfl⟩ := G2 x hx
    rw [G7 (la k) (P k) y hy b hb (hP2 k y (G1 y hy) b hb)]
    obtain ⟨h, -, -, -, he⟩ := hP3 k y hy
    rw [he]
    exact hC h

end GlobalTheory.HolRead.Descent
