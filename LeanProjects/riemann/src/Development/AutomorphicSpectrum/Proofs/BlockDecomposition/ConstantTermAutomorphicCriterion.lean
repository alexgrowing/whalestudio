import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual

noncomputable section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Topology

namespace GlobalTheory.CompanionTheory.CTFin.Central

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_unip_mul {r : ℕ} {φ : Sm E a} (hφ : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    Continuous fun x : BlockIx a r → Ad E => φ.1 (unip x * g) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  set f₀ := JointCont.finPart g x₀
  have hc : Continuous (fun x : BlockIx a r → Ad E => f₀⁻¹ * JointCont.finPart g x) :=
    continuous_const.mul (JointCont.continuous_finPart g)
  have h1 : finRep E a (f₀⁻¹ * f₀) φ = φ := by rw [inv_mul_cancel]; simp
  have hev : ∀ᶠ x in 𝓝 x₀, chart φ.1 (finGL E a f₀) (toL (JointCont.infPart g x).val) = φ.1 (unip x * g) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hφ.mem_nhds h1)] with x hx
    have hx' : finRep E a (f₀⁻¹ * JointCont.finPart g x) φ = φ := hx
    have e : unip x * g = finGL E a f₀ * infGL E a (JointCont.infPart g x) * finGL E a (f₀⁻¹ * JointCont.finPart g x) := by
      rw [JointCont.unip_mul_eq, mul_assoc, infGL_comm, ← mul_assoc, ← map_mul (finGL E a), mul_inv_cancel_left]
    rw [chart_val, e]
    exact (congrArg (fun ψ : Sm E a => ψ.1 (finGL E a f₀ * infGL E a (JointCont.infPart g x))) hx').symm
  have hA : ContinuousAt (fun x : BlockIx a r → Ad E => chart φ.1 (finGL E a f₀) (toL (JointCont.infPart g x).val)) x₀ :=
    ContinuousAt.comp (g := chart φ.1 (finGL E a f₀))
      ((φ.2 _).continuousOn.continuousAt (isOpen_invSet.mem_nhds (val_mem_invSet _)))
      (JointCont.continuous_infPart g).continuousAt
  exact hA.congr hev

theorem exists_bound_unip_mul {r : ℕ} {φ : Sm E a} (hl : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g)
    (hφ : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    ∃ C, ∀ x : BlockIx a r → Ad E, ‖φ.1 (unip x * g)‖ ≤ C := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have hKc : IsCompact (Set.univ.pi fun _ : BlockIx a r => K) := isCompact_univ_pi fun _ => hK
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (continuous_unip_mul (r := r) hφ g).continuousOn
  refine ⟨C, fun x => ?_⟩
  choose q hq using fun p => hcov (x p)
  have hx : x = (fun p => algebraMap E (Ad E) (q p)) + fun p => x p - algebraMap E (Ad E) (q p) := by
    funext p
    show x p = algebraMap E (Ad E) (q p) + (x p - algebraMap E (Ad E) (q p))
    exact (add_sub_cancel _ _).symm
  have hper : φ.1 (unip x * g) = φ.1 (unip (fun p => x p - algebraMap E (Ad E) (q p)) * g) := by
    conv_lhs => rw [hx]
    rw [unip_add, unip_algebraMap, mul_assoc, hl]
  rw [hper]
  exact hC _ fun p _ => hq p

theorem integrable_unip_mul {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (μ : Measure (BlockIx a r → Ad E)) [μ.IsAddHaarMeasure] (𝓕 : Set (BlockIx a r → Ad E))
    (h𝓕 : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) {φ : Sm E a} (hl : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g)
    (hφ : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    Integrable (fun x => φ.1 (unip x * g)) (μ.restrict 𝓕) := by
  have hfin := covol_lt_top μ 𝓕 h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C, hC⟩ := exists_bound_unip_mul (r := r) hl hφ g
  exact Integrable.of_bound (continuous_unip_mul hφ g).aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem ct_Zalg : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → (∀ φ F : Sm E a, (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → ∀ (X : Lie E a) (g : GA E a), (lie E a X F).1 g = ∫ x in 𝓕, (lie E a X φ).1 (unip x * g) ∂μ) → ∀ φ F : Sm E a, (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → ∀ z ∈ Zalg E a, ∀ g, (z F).1 g = ∫ x in 𝓕, (z φ).1 (unip x * g) ∂μ := by
  intro E _ _ _ a r _ _ μ 𝓕 hμ h𝓕 hlie
  haveI := hμ
  let P : Sm E a → Prop := fun φ =>
    (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) ∧ IsOpen {k | finRep E a k φ = φ}
  have hadd : ∀ φ ψ : Sm E a, P φ → P ψ → P (φ + ψ) := fun φ ψ h1 h2 =>
    ⟨fun γ g => by
      change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
      rw [h1.1, h2.1],
     (GlobalTheory.PRep.smoothPart (finRep E a)).add_mem (show φ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from h1.2)
       (show ψ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from h2.2)⟩
  have hsmul : ∀ (c : ℂ) (φ : Sm E a), P φ → P (c • φ) := fun c φ h1 =>
    ⟨fun γ g => by
      change c • φ.1 _ = c • φ.1 _
      rw [h1.1],
     (GlobalTheory.PRep.smoothPart (finRep E a)).smul_mem c (show φ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from h1.2)⟩
  have hint : ∀ ψ : Sm E a, P ψ → ∀ g, Integrable (fun x => ψ.1 (unip x * g)) (μ.restrict 𝓕) :=
    fun ψ h g => integrable_unip_mul μ 𝓕 h𝓕 h.1 h.2 g
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {T | ∀ φ, P φ → P (T φ) ∧ ∀ F : Sm E a, (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) →
          ∀ g, (T F).1 g = ∫ x in 𝓕, (T φ).1 (unip x * g) ∂μ}
      mul_mem' := fun {T₁ T₂} hT₁ hT₂ φ hφ => by
        obtain ⟨h1, e1⟩ := hT₂ φ hφ
        obtain ⟨h2, e2⟩ := hT₁ _ h1
        exact ⟨h2, fun F hF g => e2 (T₂ F) (e1 F hF) g⟩
      add_mem' := fun {T₁ T₂} hT₁ hT₂ φ hφ => by
        obtain ⟨h1, e1⟩ := hT₁ φ hφ
        obtain ⟨h2, e2⟩ := hT₂ φ hφ
        refine ⟨hadd _ _ h1 h2, fun F hF g => ?_⟩
        change (T₁ F).1 g + (T₂ F).1 g = ∫ x in 𝓕, ((T₁ φ).1 (unip x * g) + (T₂ φ).1 (unip x * g)) ∂μ
        rw [integral_add (hint _ h1 g) (hint _ h2 g), e1 F hF g, e2 F hF g]
      algebraMap_mem' := fun c φ hφ => by
        refine ⟨by rw [Module.algebraMap_end_apply]; exact hsmul c φ hφ, fun F hF g => ?_⟩
        rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
        change c • F.1 g = ∫ x in 𝓕, c • φ.1 (unip x * g) ∂μ
        rw [integral_smul, hF g] }
  have hL : ∀ X, lie E a X ∈ S := fun X φ hφ =>
    ⟨⟨fun γ g => GlobalTheory.SpehInfChar.lie_leftInv (ratGL E a).range X
        (fun u hu g' => by obtain ⟨γ', rfl⟩ := MonoidHom.mem_range.1 hu; exact hφ.1 γ' g') _ ⟨γ, rfl⟩ g,
      GlobalTheory.SpehInfChar.lie_mem_smoothPart X (show φ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from hφ.2)⟩,
     fun F hF g => hlie φ F hφ.1 hφ.2 hF X g⟩
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hL _) (S.smul_mem (hL _) _)) _
  intro φ F hl hlev hF z hz g
  have hzS : z ∈ S := by
    refine (Algebra.adjoin_le (S := S) ?_) hz
    rintro _ ⟨τ, u, rfl⟩
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact (hzS φ ⟨hl, hlev⟩).2 F hF g

end GlobalTheory.CompanionTheory.CTFin.Central
