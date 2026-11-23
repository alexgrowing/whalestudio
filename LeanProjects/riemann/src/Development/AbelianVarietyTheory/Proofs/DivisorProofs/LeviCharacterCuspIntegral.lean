import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegralBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentHaarFundamentalDomainExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryCountableDiscrete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermLeftUnipotentInvariant
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

noncomputable section

namespace GlobalTheory.CTFirst

open GlobalTheory.UnipCT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem levi_conj_mem_unip {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} (H : Plane E n n₁) (t : (AE F E)ˣ)
    (m : UA σ W.J) (hm : IsLevi (W₁ := W₁) H t 1 m) (u : UA σ W.J) (hu : u ∈ unip σ W H) :
    m * u * m⁻¹ ∈ unip σ W H := by
  obtain ⟨hx, -, hι⟩ := hm
  have hι1 : mat m * incM F H.ι = incM F H.ι := by
    rw [hι]; show incM F H.ι * (1 : Matrix (Fin n₁) (Fin n₁) (AE F E)) = _; rw [Matrix.mul_one]
  have hx' : mat m⁻¹ *ᵥ incV F H.x = (t⁻¹).1 • incV F H.x := by
    have e : mat m⁻¹ *ᵥ (mat m *ᵥ incV F H.x) = incV F H.x := by
      rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
    rw [hx, Matrix.mulVec_smul] at e
    conv_rhs => rw [← e]
    rw [smul_smul]
    simp
  have hι' : mat m⁻¹ * incM F H.ι = incM F H.ι := by
    conv_lhs => rw [← hι1]
    rw [← Matrix.mul_assoc, mat_inv_mul', Matrix.one_mul]
  rw [unip_eq] at hu ⊢
  obtain ⟨h1, h2⟩ := hu
  refine ⟨?_, fun z => ?_⟩
  · rw [mat_mul', mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx', Matrix.mulVec_smul,
      Matrix.mulVec_smul, h1, hx, smul_smul]
    simp
  · obtain ⟨a, ha⟩ := h2 z
    refine ⟨a * t.1, ?_⟩
    have e1 : mat m⁻¹ *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := by
      rw [Matrix.mulVec_mulVec, hι']
    have e2 : mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := by
      rw [Matrix.mulVec_mulVec, hι1]
    rw [mat_mul', mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, ha, Matrix.mulVec_add,
      Matrix.mulVec_smul, e2, hx, smul_smul]

theorem ct_first_linear : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (α β : Chr F E) (za zb : ℝ),
    (∃ K : Set (unip σ W H), IsCompact K ∧ ∀ u : unip σ W H, ∃ γ ∈ (ratU σ W.J).subgroupOf (unip σ W H), γ * u ∈ K) →
    ∀ (t₀ : (AE F E)ˣ) (m₀ : UA σ W.J), IsLevi (W₁ := W₁) H t₀ 1 m₀ →
    (α t₀ : ℂ) * (((GlobalTheory.Doubling.absE F E t₀ : ℝ) ^ za : ℝ) : ℂ) ≠ (β t₀ : ℂ) * (((GlobalTheory.Doubling.absE F E t₀ : ℝ) ^ zb : ℝ) : ℂ) →
    ∃ (D : Submodule ℂ (UA σ W.J → ℂ)) (Λ : (UA σ W.J → ℂ) →ₗ[ℂ] (UA σ W.J → ℂ)),
      (∀ f fa fb : UA σ W.J → ℂ, Continuous f → (∀ γ ∈ ratU σ W.J, ∀ z, f (γ * z) = f z) →
        SplitZ W₁ H α β za zb f fa fb → f ∈ D ∧ Λ f = fa) ∧
      (∀ f ∈ D, ∀ y : UA σ W.J, (fun z => f (z * y)) ∈ D ∧ Λ (fun z => f (z * y)) = fun z => Λ f (z * y)) ∧
      ∀ f ∈ D, HasLaw W₁ H α za (Λ f) ∧ ∀ u ∈ unip σ W H, ∀ z, Λ f (u * z) = Λ f z := by
  intro F E _ _ _ _ _ σ n n₁ W W₁ H α β za zb ⟨K, hK, hcov⟩ t₀ m₀ hm₀ hab
  obtain ⟨i1, i2, i3, i4⟩ := topFacts (F := F) σ W.J
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unip σ W H) :=
    (isClosed_unip σ W H).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ W H) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := countable_ratU (σ := σ) W.J
  haveI := GlobalTheory.RatUDisc.discrete_ratU F E σ n W.J
  have hinj : Function.Injective fun γ : (ratU σ W.J).subgroupOf (unip σ W H) => (⟨γ.1.1, γ.2⟩ : ratU σ W.J) :=
    fun x y h => Subtype.ext (Subtype.ext (congrArg (fun t : ratU σ W.J => (t : UA σ W.J)) h))
  haveI : Countable ((ratU σ W.J).subgroupOf (unip σ W H)) := hinj.countable
  haveI : DiscreteTopology ((ratU σ W.J).subgroupOf (unip σ W H)) :=
    DiscreteTopology.of_continuous_injective ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hinj
  have hcov' : ∀ u, ∃ γ ∈ (ratU σ W.J).subgroupOf (unip σ W H), ∃ k ∈ K, u = γ * k := fun u => by
    obtain ⟨γ, hγ, hk⟩ := hcov u
    exact ⟨γ⁻¹, inv_mem hγ, γ * u, hk, by group⟩
  obtain ⟨μ₀, 𝓕₀, hμ₀, h𝓕₀, h1⟩ := GlobalTheory.Per.UnitN.exists_unit_of_cocompact _ hK hcov'
  have hex : ∃ (μ : Measure (unip σ W H)) (𝓕 : Set (unip σ W H)), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H)) 𝓕 μ ∧ μ 𝓕 = 1 := ⟨μ₀, 𝓕₀, hμ₀, h𝓕₀, h1⟩

  let V : Submodule ℂ (UA σ W.J → ℂ) :=
    { carrier := {f | ∀ h, IntegrableOn (fun u : unip σ W H => f (u.1 * h)) 𝓕₀ μ₀}
      add_mem' := fun {f g} hf hg h => (hf h).add (hg h)
      zero_mem' := fun h => by simpa using (integrableOn_zero : IntegrableOn (fun _ : unip σ W H => (0 : ℂ)) 𝓕₀ μ₀)
      smul_mem' := fun c f hf h => (hf h).smul c }
  let L₀ : V →ₗ[ℂ] (UA σ W.J → ℂ) :=
    { toFun := fun f h => ((∫ u in 𝓕₀, (f : UA σ W.J → ℂ) (u.1 * (m₀ * h)) ∂μ₀) -
          (β t₀ : ℂ) * (((GlobalTheory.Doubling.absE F E t₀ : ℝ) ^ zb : ℝ) : ℂ) * ∫ u in 𝓕₀, (f : UA σ W.J → ℂ) (u.1 * h) ∂μ₀) /
          ((α t₀ : ℂ) * (((GlobalTheory.Doubling.absE F E t₀ : ℝ) ^ za : ℝ) : ℂ) -
            (β t₀ : ℂ) * (((GlobalTheory.Doubling.absE F E t₀ : ℝ) ^ zb : ℝ) : ℂ))
      map_add' := fun f g => by
        have hf : ∀ h, IntegrableOn (fun u : unip σ W H => (f : UA σ W.J → ℂ) (u.1 * h)) 𝓕₀ μ₀ := f.2
        have hg : ∀ h, IntegrableOn (fun u : unip σ W H => (g : UA σ W.J → ℂ) (u.1 * h)) 𝓕₀ μ₀ := g.2
        funext h
        simp only [Submodule.coe_add, Pi.add_apply]
        rw [integral_add (hf _) (hg _), integral_add (hf _) (hg _)]
        ring
      map_smul' := fun c f => by
        funext h
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [integral_const_mul, integral_const_mul]
        ring }
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend L₀
  have hΛV : ∀ f ∈ V, Λ f = fun h => ((∫ u in 𝓕₀, f (u.1 * (m₀ * h)) ∂μ₀) -
          (β t₀ : ℂ) * (((GlobalTheory.Doubling.absE F E t₀ : ℝ) ^ zb : ℝ) : ℂ) * ∫ u in 𝓕₀, f (u.1 * h) ∂μ₀) /
          ((α t₀ : ℂ) * (((GlobalTheory.Doubling.absE F E t₀ : ℝ) ^ za : ℝ) : ℂ) -
            (β t₀ : ℂ) * (((GlobalTheory.Doubling.absE F E t₀ : ℝ) ^ zb : ℝ) : ℂ)) :=
    fun f hf => LinearMap.congr_fun hΛ ⟨f, hf⟩

  have hfa : ∀ f fa fb, f ∈ V → SplitZ W₁ H α β za zb f fa fb → Λ f = fa := by
    intro f fa fb hV hs
    rw [hΛV f hV]
    funext h
    have hc : ∀ h, ∫ u in 𝓕₀, f (u.1 * h) ∂μ₀ = fa h + fb h := fun h => (hs.1 μ₀ 𝓕₀ hμ₀ h𝓕₀ h1 h).symm
    rw [hc, hc, hs.2.1 t₀ m₀ hm₀ h, hs.2.2 t₀ m₀ hm₀ h, div_eq_iff (sub_ne_zero.2 hab)]
    ring
  let S0 : Set (UA σ W.J → ℂ) := {f | Continuous f ∧ (∀ γ ∈ ratU σ W.J, ∀ z, f (γ * z) = f z) ∧
    ∃ fa fb, SplitZ W₁ H α β za zb f fa fb}
  have hS0V : S0 ⊆ V := by
    rintro f ⟨hc, hinv, -⟩ h
    have hg : Continuous fun u : unip σ W H => f (u.1 * h) := hc.comp (continuous_subtype_val.mul continuous_const)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
    have hb : ∀ u : unip σ W H, ‖f (u.1 * h)‖ ≤ C := fun u => by
      obtain ⟨γ, hγ, hγK⟩ := hcov u
      have e : f ((γ * u).1 * h) = f (u.1 * h) := by
        rw [Subgroup.coe_mul, mul_assoc]; exact hinv _ (Subgroup.mem_subgroupOf.1 hγ) _
      rw [← e]; exact hC _ hγK
    exact Measure.integrableOn_of_bounded (by rw [h1]; exact ENNReal.one_ne_top) hg.aestronglyMeasurable
      (Eventually.of_forall hb)
  have hRS0 : ∀ y, ∀ f ∈ S0, (fun z => f (z * y)) ∈ S0 := by
    rintro y f ⟨hc, hinv, fa, fb, hct, hla, hlb⟩
    refine ⟨hc.comp (continuous_id.mul continuous_const), fun γ hγ z => ?_, fun z => fa (z * y),
      fun z => fb (z * y), ?_, ?_, ?_⟩
    · show f (γ * z * y) = f (z * y)
      rw [mul_assoc]; exact hinv γ hγ _
    · intro μ 𝓕 hμ h𝓕 h1' h
      have e := hct μ 𝓕 hμ h𝓕 h1' (h * y)
      simp only [Pi.add_apply, mul_assoc] at e ⊢
      exact e
    · intro t m hm h
      show fa (m * h * y) = _ * fa (h * y)
      rw [mul_assoc]; exact hla t m hm (h * y)
    · intro t m hm h
      show fb (m * h * y) = _ * fb (h * y)
      rw [mul_assoc]; exact hlb t m hm (h * y)
  let D : Submodule ℂ (UA σ W.J → ℂ) := Submodule.span ℂ S0
  have hDV : D ≤ V := Submodule.span_le.2 hS0V
  have hDR : ∀ y, ∀ f ∈ D, (fun z => f (z * y)) ∈ D := by
    intro y f hf
    have hle : D.map (LinearMap.funLeft ℂ ℂ (fun z : UA σ W.J => z * y)) ≤ D := by
      rw [Submodule.map_span_le]
      intro g hg; exact Submodule.subset_span (hRS0 y g hg)
    exact hle (Submodule.mem_map_of_mem hf)
  let P : Submodule ℂ (UA σ W.J → ℂ) :=
    { carrier := {f | HasLaw W₁ H α za (Λ f) ∧ ∀ u ∈ unip σ W H, ∀ z, Λ f (u * z) = Λ f z}
      add_mem' := by
        rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
        refine ⟨?_, fun u hu z => ?_⟩
        · intro t m hm h
          simp only [map_add, Pi.add_apply, hf1 t m hm h, hg1 t m hm h]; ring
        · simp only [map_add, Pi.add_apply, hf2 u hu z, hg2 u hu z]
      zero_mem' := by
        refine ⟨?_, fun u hu z => ?_⟩
        · intro t m hm h; simp
        · simp
      smul_mem' := by
        rintro c f ⟨hf1, hf2⟩
        refine ⟨?_, fun u hu z => ?_⟩
        · intro t m hm h
          simp only [map_smul, Pi.smul_apply, smul_eq_mul, hf1 t m hm h]; ring
        · simp only [map_smul, Pi.smul_apply, smul_eq_mul, hf2 u hu z] }
  have hDP : D ≤ P := by
    refine Submodule.span_le.2 fun f hf => ?_
    obtain ⟨hc, hinv, fa, fb, hs⟩ := hf
    have hV : f ∈ V := hS0V ⟨hc, hinv, fa, fb, hs⟩
    have hΛf : Λ f = fa := hfa f fa fb hV hs
    refine ⟨hΛf ▸ hs.2.1, fun u hu z => ?_⟩
    have hinvc : ∀ v ∈ unip σ W H, ∀ h, fa (v * h) + fb (v * h) = fa h + fb h :=
      fun v hv h => GlobalTheory.ThK.UnipInv.isCT_unip_mul hex hs.1 v hv h
    have hc : ∀ h, ∫ u in 𝓕₀, f (u.1 * h) ∂μ₀ = fa h + fb h := fun h => (hs.1 μ₀ 𝓕₀ hμ₀ h𝓕₀ h1 h).symm
    have e1 : fa (m₀ * (u * z)) + fb (m₀ * (u * z)) = fa (m₀ * z) + fb (m₀ * z) := by
      have e := hinvc _ (GlobalTheory.CTFirst.levi_conj_mem_unip H t₀ m₀ hm₀ u hu) (m₀ * z)
      rwa [show m₀ * u * m₀⁻¹ * (m₀ * z) = m₀ * (u * z) by group] at e
    rw [hΛV f hV]
    simp only [hc]
    rw [e1, hinvc u hu z]
  refine ⟨D, Λ, fun f fa fb hc hinv hs => ⟨Submodule.subset_span ⟨hc, hinv, fa, fb, hs⟩,
    hfa f fa fb (hS0V ⟨hc, hinv, fa, fb, hs⟩) hs⟩, fun f hf y => ⟨hDR y f hf, ?_⟩, fun f hf => hDP hf⟩
  rw [hΛV _ (hDV (hDR y f hf)), hΛV f (hDV hf)]
  funext z
  simp only [mul_assoc]

end GlobalTheory.CTFirst

end
