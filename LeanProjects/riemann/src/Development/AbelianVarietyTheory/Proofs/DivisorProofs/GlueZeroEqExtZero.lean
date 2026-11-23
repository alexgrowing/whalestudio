import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacBox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneTransformRationalPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeInvariantPlaneTransformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOneLatticePlaneTransformStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneCo

theorem GlobalTheory.ThK.PlaneCo.isVac_vacGlue : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (M₁ : Model σ X₁ W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∀ (eq : Fin n × Fin d ≃ Kc F E d₁ n₁ ⊕ Fin n₁ × Fin d₁)
      (T : Matrix (Fin n) (Fin d) (AE F E) ≃ₗ[AF F] ((Kc F E d₁ n₁ → AF F) × (Kc F E d₁ n₁ → AF F)) × Matrix (Fin n₁) (Fin d₁) (AE F E))
      (hT : ∀ u, T u = planeT σ X W H H' u)
      (hf : ∀ w w', symp (cA σ) (-1) (incM F X.J) (incM F W.J) w w' =
        (T w).1.1 ⬝ᵥ (T w').1.2 - (T w').1.1 ⬝ᵥ (T w).1.2 + symp (cA σ) (-1) (incM F X₁.J) (incM F W₁.J) (T w).2 (T w').2)
      (μ : Measure (UA σ X.J)) (D : Set (UA σ X.J)) (v : Pl F),
      Model.IsVac (Model.mk (glueDarboux M₁.co eq T hf) (fun v => vacGlue eq (vacS σ X W H H' v) (M₁.vac v)) μ D) B.ψ v
        (vacGlue eq (vacS σ X W H H' v) (M₁.vac v)) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M₁ hB hX hW hH hH' hM₁ eq T hT hf μ D v
  classical
  set Ma : Model σ X W := Model.mk (glueDarboux M₁.co eq T hf) (fun v => vacGlue eq (vacS σ X W H H' v) (M₁.vac v)) μ D
    with hMa
  have hco : ∀ z, Ma.co.e z = (GlobalTheory.ThK.Adapt.glue eq (T z).1.1 (M₁.co.e (T z).2).1,
      GlobalTheory.ThK.Adapt.glue eq (T z).1.2 (M₁.co.e (T z).2).2) := fun z => by
    show (glueDarboux M₁.co eq T hf).e z = _
    rw [glueDarboux_e]; rfl
  have hrat : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      Ma.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
    intro x
    obtain ⟨⟨y, z, hyz⟩, x₁, hx₁⟩ := GlobalTheory.T.plane_transform_rational_points σ X W H H' x
    obtain ⟨y₁, z₁, h₁⟩ := hM₁.rat x₁
    refine ⟨glue eq y y₁, glue eq z z₁, ?_⟩
    rw [hco, hT, hyz, hx₁, h₁]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
      simp only [GlobalTheory.ThK.Adapt.glue, glue] <;> cases eq i <;> rfl
  have hdec := GlobalTheory.T.lattice_invariant_plane_transform σ B X W X₁ W₁ H H' hB hX hW hH hH' v
  have hpq : ∀ γ ∈ latAtV X W v, ∀ γ' ∈ latAtV X W v, B.ψ ((T γ').1.1 ⬝ᵥ (T γ).1.2) = 1 := by
    intro γ hγ γ' hγ'
    obtain ⟨-, ⟨b, hb, hbT⟩, -⟩ := hdec γ' hγ'
    have h1 := GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W r s r' s' hB hX hW v (-1) 1
      (by rw [map_one]; exact one_mem _) b hb γ hγ
    have h2 := hf b γ
    rw [hT b, hbT] at h2
    have hm : inclR (F := F) (AF F) (((-1 : 𝓞 E) : E)) = -1 := by simp
    rw [one_mul, hm, h2] at h1
    have h0 : symp (cA σ) (-1) (incM F X₁.J) (incM F W₁.J) (0 : Matrix (Fin n₁) (Fin d₁) (AE F E)) (T γ).2 = 0 := by
      simp [symp, hTens]
    rw [h0] at h1
    simpa [hT] using h1
  have hθ : ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ γ ∈ latAtV X W v,
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) =
        B.ψ (⅟(2 : AF F) * ((T γ).1.1 ⬝ᵥ (T γ).1.2)) *
          B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X₁.J) (incM F W₁.J) (T γ).2 (T γ).2) := by
    intro θ hθ γ hγ
    obtain ⟨⟨a, ha, haT⟩, ⟨b, hb, hbT⟩, -⟩ := hdec γ hγ
    have e := GlobalTheory.T.trace_one_lattice_plane_transform σ B X W X₁ W₁ H H' hB hX hW hH hH' (θ : E) hθ γ a b haT hbT
    have h1 := GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W r s r' s' hB hX hW v θ 1
      (by rw [map_one]; exact one_mem _) b hb a ha
    rw [one_mul] at h1
    simp only [hT]
    rw [e, ← AddChar.map_add_eq_mul]
    have h3 : (⅟(2 : AF F)) * 2 = 1 := invOf_mul_self _
    generalize symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) b a = S at h1 ⊢
    generalize (planeT σ X W H H' γ).1.1 ⬝ᵥ (planeT σ X W H H' γ).1.2 = P
    generalize symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X₁.J) (incM F W₁.J) (planeT σ X W H H' γ).2
      (planeT σ X W H H' γ).2 = Q
    have : ⅟(2 : AF F) * (P + 2 * S + Q) = (⅟(2 : AF F) * P + ⅟(2 : AF F) * Q) + S := by
      linear_combination S * h3
    rw [this, AddChar.map_add_eq_mul, h1, mul_one]
  have hΛ : ∀ y, y ∈ latS σ X W H H' v ↔ ∃ γ ∈ latAtV X W v, (fun k => evFin F v ((T γ).1.1 k)) = y := by
    intro y
    simp only [latS, Set.mem_setOf_eq, hT]
    constructor
    · rintro ⟨γ, hγ, h⟩; exact ⟨γ, hγ, funext fun k => (h k).symm⟩
    · rintro ⟨γ, hγ, rfl⟩; exact ⟨γ, hγ, fun k => rfl⟩
  exact GlobalTheory.ThK.AdaptVac.isVac_box eq hX hW Ma M₁ hrat (fun z => (T z).1.1) (fun z => (T z).1.2) (fun z => (T z).2) hco v
    (fun γ hγ => by rw [hT]; exact (hdec γ hγ).2.2) hpq hθ (hM₁.vac v) _ hΛ
