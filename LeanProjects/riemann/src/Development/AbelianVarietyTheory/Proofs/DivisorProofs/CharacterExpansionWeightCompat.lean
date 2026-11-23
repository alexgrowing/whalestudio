import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFormFrameExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedSectionInSpanOfGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicExpansionInDictionaryStatement

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.ToHol

theorem det_ne_of_frame {n : ℕ} (q : ℕ) (G x : Matrix (Fin n) (Fin n) ℂ)
    (h : xᴴ * G * x = diagonal fun c : Fin n => if (c : ℕ) < q then (-1 : ℂ) else 1) : x.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [det_mul, h0, mul_zero, det_diagonal] at this
  refine (Finset.prod_ne_zero_iff.2 fun c _ => ?_) this.symm
  split_ifs <;> norm_num

theorem unitary_of_frames {n : ℕ} (G x x₀ : Matrix (Fin n) (Fin n) ℂ) (hx : x.det ≠ 0)
    (h : x₀ᴴ * G * x₀ = xᴴ * G * x) : (x₀ * x⁻¹)ᴴ * G * (x₀ * x⁻¹) = G := by
  have hu : IsUnit x.det := hx.isUnit
  have h1 : x * x⁻¹ = 1 := mul_nonsing_inv x hu
  calc (x₀ * x⁻¹)ᴴ * G * (x₀ * x⁻¹) = x⁻¹ᴴ * (x₀ᴴ * G * x₀) * x⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (x * x⁻¹)ᴴ * G * (x * x⁻¹) := by
        rw [h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h1]; simp

theorem differentiable_det {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (τ : Ψ) :
    Differentiable ℂ fun y : Frame Ψ r => (mat y τ).det := by
  simp only [det_apply', mat, of_apply]
  fun_prop

theorem bchar_shift {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (la : ReciprocityTheory.ChartRestriction.G.FD.Wt Ψ r) (e : Ψ → ℤ)
    (b : Frame Ψ r) (hb : b ∈ Bor Ψ r) :
    bchar la b = bchar (fun τ i => la τ i - e τ) b * ∏ τ, (mat b τ).det ^ e τ := by
  unfold bchar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hd : (mat b τ).det = ∏ i, b τ i i :=
    det_of_upperTriangular (M := mat b τ) fun a c h => (hb τ).2 a c h
  have hne : ∀ i, b τ i i ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.1 (fun h => (hb τ).1 (hd.trans h)) i (Finset.mem_univ _)
  rw [hd, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_add₀ (hne i), sub_add_cancel]

theorem archM_mul' {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    archM V θ (a * b) = archM V θ a * archM V θ b := by
  unfold archM
  rw [map_mul, Units.val_mul, Matrix.map_mul]

theorem exists_holCusp : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → Data D.host.E r) (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V)) (x₀ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (q : ℕ) (w : D.what₂.Tau → Fin V.rank → ℤ) (e : D.what₂.Tau → ℤ) (mu : GA D V → ℂ), IsInfFam θ → BaseDict θ V hr X dict Kf x₀ → Kf ≤ GfC V → (∀ k, (X k).p0 = q) → NegFirst V q x → (∀ g g', mu (g * g') = mu g * mu g') → (∀ g, ‖mu g‖ = 1) → (∀ γ ∈ GQ V, mu γ = 1) → (∀ k ∈ Kf, mu k = 1) → (∀ u ∈ GinfC V, mu u = ∏ ρ, (archM V (θ ρ) u).det ^ (-(e ρ))) → (∀ k (ρ : D.what₂.Tau) (τ : (X k).Ψ), τ.1 = tauE D ρ → ∀ c : Fin V.rank, la k τ (Fin.cast hr c) = w ρ c + e ρ) → (∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) → (∀ k (τ : (X k).Ψ) (a b : Fin r), (a : ℕ) < q → q ≤ (b : ℕ) → la k τ a < la k τ b) → ∃ a : GA D V, ∀ φ : GA D V → ℂ, IsHolFor θ V x w φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → (∀ k ∈ Kf, ∀ g, φ (g * k) = φ g) → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → ∃ P : FDSec X, IsHolCusp X la P ∧ ∀ g, φ (g * a) = mu g * P (dict g).1 (dict g).2 := by
  intro D θ V r hr Comp X dict Kf x₀ la x q w e mu hθ hB hKf hq hx hmul hnorm hQ hK hinf hla hχ hsep
  have hx₀ : NegFirst V q x₀ := hq (dict 1).1 ▸ (hB.1 (dict 1).1).2.1
  have hdx : ∀ ρ, (x ρ).det ≠ 0 := fun ρ => det_ne_of_frame q _ _ (hx ρ)
  have hdx₀ : ∀ ρ, (x₀ ρ).det ≠ 0 := fun ρ => det_ne_of_frame q _ _ (hx₀ ρ)
  obtain ⟨a, ha, haM⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ V).2 (fun ρ => x₀ ρ * (x ρ)⁻¹)
    (fun ρ => unitary_of_frames _ _ _ (hdx ρ) ((hx₀ ρ).trans (hx ρ).symm))
  have haM' : ∀ ρ, archM V (θ ρ) a * x ρ = x₀ ρ := fun ρ => by
    have : archM V (θ ρ) a = x₀ ρ * (x ρ)⁻¹ := haM ρ
    rw [this, Matrix.mul_assoc, nonsing_inv_mul _ (hdx ρ).isUnit, Matrix.mul_one]
  have hcomm := (GlobalTheory.UnitarySplit.real_finite_split D V).2.1
  have hmu0 : ∀ g, mu g ≠ 0 := fun g h => by simpa [h] using hnorm g
  refine ⟨a, fun φ hφ hl hk ⟨C, hC⟩ => ?_⟩
  obtain ⟨P, hP, hPe, hPb⟩ := GlobalTheory.T.automorphic_expansion_in_dictionary D θ V r hr Comp X dict Kf x₀ la (fun g => φ (g * a) / mu g) hθ hB hχ
    (fun γ hγ g => by simp only [mul_assoc, hl γ hγ, hmul, hQ γ hγ, one_mul])
    (fun k hk' g => by
      simp only [hmul, hK k hk', mul_one]
      rw [mul_assoc, ← hcomm a ha k (hKf hk'), ← mul_assoc, hk k hk'])
    (fun k g => by
      have hM := (hB.1 k).1
      choose s hs using fun τ : (X k).Ψ => (hM.1 τ.1).1 τ.2
      have hsρ : ∀ (ρ : D.what₂.Tau) (τ : (X k).Ψ), τ.1 = tauE D ρ → s τ = ρ := fun ρ τ h =>
        GlobalTheory.SmoothForms.RealPts.tauE_injective D ((hs τ).symm.trans h)
      have hsb : Function.Bijective s := by
        refine ⟨fun τ τ' h => Subtype.ext (by rw [hs τ, hs τ', h]), fun ρ => ?_⟩
        exact ⟨⟨tauE D ρ, (hM.1 _).2 ⟨ρ, rfl⟩⟩, hsρ ρ _ rfl⟩
      obtain ⟨Q, hQd, hQb, hQe⟩ := GlobalTheory.T.holomorphic_form_frame_expansion D θ V r hr (X k) x w (fun τ i => la k τ i - e (s τ)) φ hθ hM
        ((hq k).symm ▸ hx) (fun ρ τ h c => by simp only [hla k ρ τ h c, hsρ ρ τ h, add_sub_cancel_right]) hφ g
      refine ⟨fun y => Q y * (∏ τ, (mat y τ).det ^ e (s τ)) * ((mu g)⁻¹ * ∏ τ, (x₀ (s τ)).det ^ (-e (s τ))), ?_, ?_, ?_⟩
      · refine DifferentiableOn.mul_const (hQd.mul ?_) _
        intro y hy
        refine DifferentiableAt.differentiableWithinAt ?_
        exact (HasFDerivAt.finset_prod (u := Finset.univ) (g := fun τ (y : Frame (X k).Ψ r) => (mat y τ).det ^ e (s τ))
          fun τ _ => (((differentiable_det τ) y).zpow (Or.inl (hy τ).1)).hasFDerivAt).differentiableAt
      · intro y hy b hb
        have hm : ∀ τ, mat (rmul y b) τ = mat y τ * mat b τ := fun τ => rfl
        simp only [hQb y hy b hb, hm, det_mul, mul_zpow, Finset.prod_mul_distrib]
        rw [bchar_shift (la k) (fun τ => e (s τ)) b hb]
        ring
      · intro u hu y hy
        have hy' : FrIs θ V hr (X k) x (u * a) y := fun ρ τ h => by
          rw [hy ρ τ h, archM_mul', Matrix.mul_assoc, haM']
        have hd : ∀ τ, (mat y τ).det = (archM V (θ (s τ)) u).det * (x₀ (s τ)).det := fun τ => by
          rw [hy (s τ) τ (hs τ), det_reindex_self, det_mul]
        have hu' : mu u = ∏ τ, (archM V (θ (s τ)) u).det ^ (-(e (s τ))) := by
          rw [hinf u hu]
          exact (hsb.prod_comp fun ρ => (archM V (θ ρ) u).det ^ (-(e ρ))).symm
        have h1 : (∏ τ, (x₀ (s τ)).det ^ e (s τ)) * ∏ τ, (x₀ (s τ)).det ^ (-e (s τ)) = 1 := by
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_eq_one fun τ _ => by rw [← zpow_add₀ (hdx₀ _), add_neg_cancel, zpow_zero]
        have h2 : (∏ τ, (archM V (θ (s τ)) u).det ^ e (s τ)) = (mu u)⁻¹ := by
          rw [hu', ← Finset.prod_inv_distrib]
          exact Finset.prod_congr rfl fun τ _ => by rw [_root_.zpow_neg, inv_inv]
        simp only [hQe (u * a) (mul_mem hu ha) y hy', hd, mul_zpow, Finset.prod_mul_distrib, h2, hmul, mul_assoc g u a]
        rw [div_eq_mul_inv, mul_inv]
        linear_combination (φ (g * (u * a)) * (mu u)⁻¹ * (mu g)⁻¹) * h1)
  refine ⟨P, fun k => ?_, fun g => ?_⟩
  · refine GlobalTheory.T.bounded_section_in_span_of_gap _ r (X k) (la k) (P k) ⟨hP k, C, hPb C (fun g => ?_) k⟩ ?_
    · simpa only [norm_div, hnorm, div_one] using hC _
    · intro τ a b h1 h2
      rw [hq k] at h1 h2
      exact hsep k τ a b h1 h2
  · rw [← hPe g]
    field_simp [hmu0 g]

end GlobalTheory.HolRead.ToHol
