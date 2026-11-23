import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSchwartzSpaceUnitaryStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEvaluationIntertwinesThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEvaluationThetaEquivariantStatement
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB

noncomputable section

namespace GlobalTheory.ConeSoB

theorem dbl_mem {κ Z A B : Type} [MeasurableSpace A] [MeasurableSpace B] (μA : Measure A) (μB : Measure B)
    (V : Submodule ℂ (κ → ℂ)) [FiniteDimensional ℂ V] (g : A → B → κ → ℂ) (hg : ∀ a b, g a b ∈ V)
    (hint : ∀ y, (∀ a, Integrable (fun b => g a b y) μB) ∧ Integrable (fun a => ∫ b, g a b y ∂μB) μA) :
    (fun y => ∫ a, ∫ b, g a b y ∂μB ∂μA) ∈ V ∧
      ∀ (T : (κ → ℂ) →ₗ[ℂ] (Z → ℂ)) (Y : Z), (∀ a b, T (g a b) Y = 0) → T (fun y => ∫ a, ∫ b, g a b y ∂μB ∂μA) Y = 0 := by
  classical
  set I : κ → ℂ := fun y => ∫ a, ∫ b, g a b y ∂μB ∂μA with hI

  let ε : κ → Module.Dual ℂ V := fun y => (LinearMap.proj y).comp V.subtype
  have hspan : Submodule.span ℂ (Set.range ε) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range ε)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro f hf
      rw [Submodule.mem_dualCoannihilator] at hf
      rw [Submodule.mem_bot]
      exact Subtype.ext (funext fun y => hf (ε y) (Submodule.subset_span ⟨y, rfl⟩))
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ε)), h0,
      Submodule.dualAnnihilator_bot]
  have hcomb : ∀ ℓ : Module.Dual ℂ V, ∃ c : κ →₀ ℂ, ∀ f : V, ℓ f = ∑ y ∈ c.support, c y * (f : κ → ℂ) y := by
    intro ℓ
    have hℓ : ℓ ∈ Submodule.span ℂ (Set.range ε) := by rw [hspan]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hℓ
    refine ⟨c, fun f => ?_⟩
    rw [← hc, Finsupp.sum, LinearMap.sum_apply]
    rfl

  have lin : ∀ {J : Type} (t : Finset J) (c : J → ℂ) (p : J → κ),
      ∫ a, ∫ b, ∑ j ∈ t, c j * g a b (p j) ∂μB ∂μA = ∑ j ∈ t, c j * I (p j) := by
    intro J t c p
    have inner : ∀ a, ∫ b, ∑ j ∈ t, c j * g a b (p j) ∂μB = ∑ j ∈ t, c j * ∫ b, g a b (p j) ∂μB := fun a => by
      rw [integral_finset_sum _ fun j _ => ((hint (p j)).1 a).const_mul (c j)]
      simp only [integral_const_mul]
    simp only [inner]
    rw [integral_finset_sum _ fun j _ => (hint (p j)).2.const_mul (c j)]
    simp only [integral_const_mul, hI]

  have hmem : I ∈ V := by
    let bV := Module.finBasis ℂ V
    choose c hc using fun i => hcomb (bV.coord i)
    have key : I = ∑ i, (∑ y ∈ (c i).support, c i y * I y) • ((bV i : V) : κ → ℂ) := by
      funext y₀
      have hg' : ∀ a b, g a b y₀ = ∑ i, (∑ y ∈ (c i).support, c i y * g a b y) * ((bV i : V) : κ → ℂ) y₀ := by
        intro a b
        have h := congrArg (fun f : V => (f : κ → ℂ) y₀) (bV.sum_repr ⟨g a b, hg a b⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
        rw [← h]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hc i ⟨g a b, hg a b⟩]
        rfl
      have h2 : ∀ a b, g a b y₀ = ∑ x ∈ Finset.univ.sigma fun i => (c i).support,
          (c x.1 x.2 * ((bV x.1 : V) : κ → ℂ) y₀) * g a b x.2 := by
        intro a b
        rw [hg' a b, Finset.sum_sigma]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun y _ => by ring
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have h3 : I y₀ = ∫ a, ∫ b, ∑ x ∈ Finset.univ.sigma fun i => (c i).support,
          (c x.1 x.2 * ((bV x.1 : V) : κ → ℂ) y₀) * g a b x.2 ∂μB ∂μA := by
        simp only [hI, ← h2]
      rw [h3, lin, Finset.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [key]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bV i).2
  refine ⟨hmem, fun T Y hT => ?_⟩
  obtain ⟨c, hc⟩ := hcomb ((LinearMap.proj Y).comp (T.comp V.subtype))
  have h1 := hc ⟨I, hmem⟩
  have h2 : ∀ a b, ∑ y ∈ c.support, c y * g a b y = 0 := fun a b => by
    rw [← hc ⟨g a b, hg a b⟩]; exact hT a b
  change T I Y = _ at h1
  rw [h1, ← lin]
  simp only [h2, integral_zero]

theorem coneFin_mem_soLoc : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)), IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (μK₁ : Measure (KAt K (evFin F B.v₁))) (μ₁ : Measure (idelesAt E (evFin F B.v₁))),
    IsNormK K (evFin F B.v₁) μK₁ → IsNormE E B.v₁ μ₁ →
    ∀ φ ∈ G.M'.SoLoc B.ψ B.τ₁,
      coneFin B G.M' om' B.v₁ (ev B.v₁) K μK₁ μ₁ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ ∈ G₁.M'.SoLoc B.ψ B.τ₁ := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC e' hE K hK X om om' om₁ om₁' hT hT₁ ei ev hei hvac hfac μK₁ μ₁ hμK hμ φ hφ
  obtain ⟨ι₁, hι₁, hsupp⟩ := GlobalTheory.T.config_b_evaluation_intertwines_theta B G G₁ H H' hC e' hE X om om' om₁ om₁' hT hT₁ ei ev hei hvac hfac
  obtain ⟨V, hVf, hVSB, hVmem, hint⟩ :=
    GlobalTheory.T.config_b_evaluation_theta_equivariant B G G₁ H H' hC e' hE X om om' om₁ om₁' hT hT₁ ei ev hei hvac hfac K hK μK₁ μ₁ hμK hμ φ hφ.1
  have hloc : ∀ k : KAt K (evFin F B.v₁), locOp B.v₁ (om' (k.1, 1)) φ ∈ G.M'.SoLoc B.ψ B.τ₁ := by
    intro k
    by_cases h : ∃ φ₁, φ₁ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁) ∧ Acts (evFin F B.v₁) (om' (k.1, 1)) φ φ₁
    · exact GlobalTheory.T.local_schwartz_space_unitary_stable B G X om om' hT k.1 (mem_KAt.1 k.2).2 φ hφ _ (locOp_mem _ _ _) (acts_locOp h)
    · obtain ⟨-, ι, hι, -⟩ := hφ
      rw [locOp, dif_neg h]
      exact ⟨zero_mem _, ι, hι, fun Y _ => by simp⟩
  haveI := hVf
  obtain ⟨hmem, hT0⟩ := dbl_mem μK₁ μ₁ V _ hVmem hint
  refine ⟨hVSB hmem, ι₁, hι₁, fun Y hY => hT0 ι₁ Y fun k l => ?_⟩
  have e : (fun y => coneFinInt B G.M' om' B.v₁ (ev B.v₁) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ k.1 l.1 y) =
      ((X.ν l.1 : ℂ) * ((GlobalTheory.Doubling.absE F E l.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) •
        ev B.v₁ (locOp B.v₁ (G.M'.co.rho B.ψ (partFin B.v₁ (shiftB σ H H' l.1))) (locOp B.v₁ (om' (k.1, 1)) φ)) := by
    funext y
    simp only [coneFinInt, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, map_smul, Pi.smul_apply, hsupp _ (hloc k) l.1 Y hY, smul_zero]

end GlobalTheory.ConeSoB
