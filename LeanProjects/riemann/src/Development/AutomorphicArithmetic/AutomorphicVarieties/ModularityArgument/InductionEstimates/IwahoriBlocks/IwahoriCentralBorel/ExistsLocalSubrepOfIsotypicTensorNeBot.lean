import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.TensLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ExistsNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.OccUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LocDat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem dS_single {K : Type} [Field K] [NumberField K] {r : ℕ} (w : Fin r → Pl K) (i : Fin r) (p : PW (w i)) :
    dS w (Pi.mulSingle i p) = dl (w i) p := by
  unfold dS
  rw [MonoidHom.finset_prod_apply, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.mulSingle_eq_of_ne hj]
  · simp

private theorem blocks_single {K : Type} [Field K] [NumberField K] {r : ℕ} {w : Fin r → Pl K} (ι : GS 2 w →* FA K 2)
    (i : Fin r) (p : PW (w i)) :
    blocks ι (Pi.mulSingle i p) =
      (MultiplicityOne.finProj K 2 (ι (Pi.mulSingle i (lev₂ (w i) p).1)),
        MultiplicityOne.finProj K 2 (ι (Pi.mulSingle i (lev₂ (w i) p).2))) := by
  have h1 : (fun j => (lev₂ (w j) ((Pi.mulSingle i p : ∀ j, PW (w j)) j)).1) = Pi.mulSingle i (lev₂ (w i) p).1 := by
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Pi.mulSingle_eq_of_ne h]
  have h2 : (fun j => (lev₂ (w j) ((Pi.mulSingle i p : ∀ j, PW (w j)) j)).2) = Pi.mulSingle i (lev₂ (w i) p).2 := by
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Pi.mulSingle_eq_of_ne h]
  refine Prod.ext ?_ ?_
  · change MultiplicityOne.finProj K 2 (ι (fun j => (lev₂ (w j) ((Pi.mulSingle i p : ∀ j, PW (w j)) j)).1)) = _
    rw [h1]
  · change MultiplicityOne.finProj K 2 (ι (fun j => (lev₂ (w j) ((Pi.mulSingle i p : ∀ j, PW (w j)) j)).2)) = _
    rw [h2]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.exists_local_subrep_of_isotypic_tensor_ne_bot :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ)) (κ : Measure (archCompact K 2)) (p₁ p₂ : archCompact K 2 → ℂ),
      CuspIrr μ τ₁ → CuspIrr μ τ₂ → IdemA κ p₁ → IdemA κ p₂ → ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS 2 w →* FA K 2), Function.Injective w → IsEmb w ι →
      tensFn (Xs μ τ₁ κ p₁ (im w)) (Xs μ τ₂ κ p₂ (im w)) ≠ ⊥ → ∀ i,
      ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (PW (w i)) V) (f : V →ₗ[ℂ] (G1 K 2 × G1 K 2 → ℂ)), LocOk (PW (w i)) ρ ∧ f ≠ 0 ∧
        (∀ v, f v ∈ tensFn (Xs μ τ₁ κ p₁ (im w)) (Xs μ τ₂ κ p₂ (im w))) ∧ ∀ p v, f (ρ p v) = xS ι (Pi.mulSingle i p) (f v) := by
  intro K _ _ _ μ _ τ₁ τ₂ κ p₁ p₂ h₁ h₂ e₁ e₂ r w ι hw hι hne i
  have hX₁ : Xs μ τ₁ κ p₁ (im w) ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff, tensFn, Submodule.span_le]
    rintro _ ⟨φ, hφ, ψ, _, rfl⟩
    rw [h, Submodule.mem_bot] at hφ
    subst hφ
    simp only [Submodule.bot_coe, Set.mem_singleton_iff]
    funext x
    simp
  have hX₂ : Xs μ τ₂ κ p₂ (im w) ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff, tensFn, Submodule.span_le]
    rintro _ ⟨φ, _, ψ, hψ, rfl⟩
    rw [h, Submodule.mem_bot] at hψ
    subst hψ
    simp only [Submodule.bot_coe, Set.mem_singleton_iff]
    funext x
    simp
  obtain ⟨σ₁, f₁, o₁, n₁, m₁, q₁⟩ := xOcc μ τ₁ κ p₁ h₁ e₁ w ι hw hι hX₁ i
  obtain ⟨σ₂, f₂, o₂, n₂, m₂, q₂⟩ := xOcc μ τ₂ κ p₂ h₂ e₂ w ι hw hι hX₂ i
  let f : σ₁.V ⊗[ℂ] σ₂.V →ₗ[ℂ] (G1 K 2 × G1 K 2 → ℂ) :=
    TensorProduct.lift (LinearMap.mk₂ ℂ (fun a b x => f₁ a x.1 * f₂ b x.2)
      (fun _ _ _ => by funext x; simp [add_mul]) (fun _ _ _ => by funext x; simp [mul_assoc])
      (fun _ _ _ => by funext x; simp [mul_add]) (fun _ _ _ => by funext x; simp [mul_left_comm]))
  have hf : ∀ a b, f (a ⊗ₜ b) = fun x => f₁ a x.1 * f₂ b x.2 := by
    intro a b
    simp only [f, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
  refine ⟨σ₁.V ⊗[ℂ] σ₂.V, inferInstance, inferInstance, rhoW (w i) σ₁ σ₂, f,
    locDat (w i) σ₁ σ₂ (occUnit 2 μ τ₁ (w i) σ₁ o₁) (occUnit 2 μ τ₂ (w i) σ₂ o₂), ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ : ∃ a, f₁ a ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact n₁ (LinearMap.ext hc)
    obtain ⟨b, hb⟩ : ∃ b, f₂ b ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact n₂ (LinearMap.ext hc)
    obtain ⟨x, hx⟩ := Function.ne_iff.1 ha
    obtain ⟨y, hy⟩ := Function.ne_iff.1 hb
    intro h0
    have := congrFun (hf a b) (x, y)
    rw [h0] at this
    exact mul_ne_zero hx hy this.symm
  · intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hf]
      exact Submodule.subset_span ⟨_, m₁ a, _, m₂ b, rfl⟩
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  · intro p v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      have hL : rhoW (w i) σ₁ σ₂ p (a ⊗ₜ b) =
          ((dl (w i) p : ℂˣ) : ℂ) • (σ₁.ρ (lev₂ (w i) p).1 a ⊗ₜ σ₂.ρ (lev₂ (w i) p).2 b) := by
        simp only [rhoW, twist_apply, MonoidHom.comp_apply, extTensor_tmul]
      rw [hL, map_smul, hf, hf, q₁, q₂]
      simp only [xS, twist_apply, MonoidHom.comp_apply, dS_single, blocks_single]
      congr 1
