import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.UnitaryBC GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.infinite_matrix_rational {D : D7} {V : HSp D}
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (h : GA D V) (γ₀ : GL (Fin V.rank) D.host.E)
    (e : matHom V h = Matrix.GeneralLinearGroup.map (incA D) γ₀) (τ : D.what₂.Tau) :
    Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) h =
      (Matrix.GeneralLinearGroup.map (tauE D τ) γ₀ : GL (Fin V.rank) ℂ).val := by
  have e' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat _ D.sp.cm.sig V.gram h = Matrix.GeneralLinearGroup.map (incA D) γ₀ := e
  unfold Formalism.MainNotions.StandardLattice.infMat
  rw [e']
  ext a b
  change θ τ (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ⊗ₜ[D.host.F] γ₀.val a b)) = tauE D τ (γ₀.val a b)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  exact (hθ τ).1 _

private theorem UpperTheory.exists_conjugate_embedding {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (σ ε : E →+* ℂ)
    (hε : ε = σ ∨ ε = ComplexEmbedding.conjugate σ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    ∃ B : GL (Fin n) ℂ, ∀ (x : UA E n) (γ₀ : GL (Fin n) E),
      (Matrix.GeneralLinearGroup.map σ γ₀ : GL (Fin n) ℂ).val = A * (cEmb σ x : Matrix (Fin n) (Fin n) ℂ) * A⁻¹ →
      Matrix.GeneralLinearGroup.map ε γ₀ = B * cEmb ε x * B⁻¹ := by
  obtain ⟨B, rfl⟩ := hA
  have key : ∀ (x : UA E n) (γ₀ : GL (Fin n) E),
      (Matrix.GeneralLinearGroup.map σ γ₀ : GL (Fin n) ℂ).val =
        B.val * (cEmb σ x : Matrix (Fin n) (Fin n) ℂ) * (B.val)⁻¹ →
      Matrix.GeneralLinearGroup.map σ γ₀ = B * cEmb σ x * B⁻¹ := fun x γ₀ h => by
    apply Units.ext
    rw [h, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  rcases hε with rfl | rfl
  · exact ⟨B, key⟩
  · refine ⟨Matrix.GeneralLinearGroup.map (starRingEnd ℂ) B, fun x γ₀ h => ?_⟩
    have h1 := congrArg (Matrix.GeneralLinearGroup.map (starRingEnd ℂ)) (key x γ₀ h)
    rw [map_mul, map_mul, map_inv] at h1
    have h2 : Matrix.GeneralLinearGroup.map (starRingEnd ℂ) (cEmb σ x) = cEmb (ComplexEmbedding.conjugate σ) x := by
      ext a b
      exact (GlobalTheory.DefiniteBC.coord_conjugate σ _).symm
    rw [h2] at h1
    rw [← h1]
    ext a b
    rfl

private theorem UpperTheory.weight_operator_conjugate {n : ℕ} {ι : Type} [Fintype ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ)
    (B C G : ι → GL (Fin n) ℂ) (h : G = B * C * B⁻¹) (u : NablaT ℂ n mu) :
    wtOp ℂ n mu sh B⁻¹ (wtOp ℂ n mu sh G u) = wtOp ℂ n mu sh C (wtOp ℂ n mu sh B⁻¹ u) := by
  classical
  rw [h, ← Module.End.mul_apply, ← wtOp_mul, ← mul_assoc, inv_mul_cancel_left, wtOp_mul]
  rfl

private theorem UpperTheory.monoidHom_kernel_invariance {G H K : Type} [Monoid G] [Monoid H] [Monoid K] (j : G →* H) (φ : H →* K)
    (g x : G) (h : H) (hx : φ (j x) = 1) : φ (j (g * x) * h) = φ (j g * h) := by
  simp only [map_mul, hx, mul_one]

theorem UpperTheory.vectorValued_autForm_equivariant_infinite_component :
    ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
        (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V), IsInfFam θ → GlobalTheory.DefTransfer.IsTransfer V θ j h₀ →
        ∀ (emb : D.what₂.Tau → (D.host.E →+* ℂ)), (∀ τ, emb τ = tauE D τ ∨ emb τ = ComplexEmbedding.conjugate (tauE D τ)) →
        ∀ (mu : D.what₂.Tau → ℕ → ℕ) (sh : D.what₂.Tau → ℤ) (Fm : Bridge.Gf V → NablaT ℂ V.rank mu), Fm ≠ 0 →
        (∀ (γ : GQ V) (γ₀ : GL (Fin V.rank) D.host.E), matHom V γ = Matrix.GeneralLinearGroup.map (incA D) γ₀ → ∀ g,
          Fm (Bridge.ratF V γ * g) = wtOp ℂ V.rank mu sh (fun τ => Matrix.GeneralLinearGroup.map (emb τ) γ₀) (Fm g)) →
        (∀ᶠ κ in nhds (1 : GA D V), ∀ g, Fm (g * (finHom V).rangeRestrict κ) = Fm g) →
        ∃ F1 : UA D.host.E V.rank → NablaT ℂ V.rank mu, F1 ≠ 0 ∧
          (∀ γ ∈ ratU D.host.E V.rank, ∀ g, F1 (γ * g) = wtOp ℂ V.rank mu sh (fun τ => cEmb (emb τ) γ) (F1 g)) ∧
          (∀ x ∈ infU D.host.E V.rank, ∀ g, F1 (g * x) = F1 g) ∧ (∀ᶠ y in nhds (1 : UA D.host.E V.rank), ∀ g, F1 (g * y) = F1 g) ∧
          ∃ A : Module.End ℂ (NablaT ℂ V.rank mu), ∀ x, F1 x = A (Fm ((finHom V).rangeRestrict (j x * h₀))) := by
  intro D _ V θ j h₀ hθ hT emb hemb mu sh Fm hF hrat hlev
  classical
  obtain ⟨-, hQ, -, hI, ⟨A, hA, hAe⟩, -⟩ := hT
  choose B hB using fun τ => UpperTheory.exists_conjugate_embedding (tauE D τ) (emb τ) (hemb τ) (A τ) (hA τ)
  refine ⟨fun x => wtOp ℂ V.rank mu sh B⁻¹ (Fm ((finHom V).rangeRestrict (j x * h₀))), ?_, ?_, ?_, ?_, _, fun _ => rfl⟩
  · intro h0
    apply hF
    funext g
    obtain ⟨k, rfl⟩ := (finHom V).rangeRestrict_surjective g
    have h1 := congrArg (wtOp ℂ V.rank mu sh B) (congrFun h0 (j.symm (k * h₀⁻¹)))
    simp only [ContinuousMulEquiv.apply_symm_apply, inv_mul_cancel_right, Pi.zero_apply, map_zero] at h1
    rw [← Module.End.mul_apply, ← wtOp_mul, mul_inv_cancel, wtOp_one] at h1
    exact h1
  · intro γ hγ g
    have hj : j γ ∈ GQ V := (hQ γ).1 hγ
    obtain ⟨γ₀, -, e⟩ := id hj
    have e' : matHom V (j γ) = Matrix.GeneralLinearGroup.map (incA D) γ₀ := e.symm
    have h1 := hrat ⟨j γ, hj⟩ γ₀ e' ((finHom V).rangeRestrict (j g * h₀))
    have h2 : (finHom V).rangeRestrict (j (γ * g) * h₀) =
        Bridge.ratF V ⟨j γ, hj⟩ * (finHom V).rangeRestrict (j g * h₀) := by
      have h4 : j (γ * g) * h₀ = j γ * (j g * h₀) := by rw [map_mul, mul_assoc]
      exact (congrArg (finHom V).rangeRestrict h4).trans (map_mul (finHom V).rangeRestrict _ _)
    have h3 : (fun τ => Matrix.GeneralLinearGroup.map (emb τ) γ₀) = B * (fun τ => cEmb (emb τ) γ) * B⁻¹ := by
      funext τ
      exact hB τ γ γ₀ ((UpperTheory.infinite_matrix_rational θ hθ _ γ₀ e' τ).symm.trans (hAe τ γ))
    exact (congrArg (wtOp ℂ V.rank mu sh B⁻¹) ((congrArg Fm h2).trans h1)).trans
      (UpperTheory.weight_operator_conjugate mu sh B _ _ h3 _)
  · intro x hx g
    have hj : finHom V (j x) = 1 := (hI x).1 hx
    have h1 : (finHom V).rangeRestrict (j x) = 1 := Subtype.ext hj
    exact congrArg (fun z => wtOp ℂ V.rank mu sh B⁻¹ (Fm z))
      (UpperTheory.monoidHom_kernel_invariance j.toMulEquiv.toMonoidHom (finHom V).rangeRestrict g x h₀ h1)
  · have hc : Continuous fun y : UA D.host.E V.rank => h₀⁻¹ * j y * h₀ :=
      (continuous_const.mul j.continuous).mul continuous_const
    have ht : Filter.Tendsto (fun y : UA D.host.E V.rank => h₀⁻¹ * j y * h₀) (nhds 1) (nhds 1) := by
      exact hc.tendsto' 1 1 (by simp only [map_one, mul_one, inv_mul_cancel])
    filter_upwards [ht.eventually hlev] with y hy g
    have h1 : j (g * y) * h₀ = j g * h₀ * (h₀⁻¹ * j y * h₀) := by
      rw [map_mul]
      group
    exact congrArg (wtOp ℂ V.rank mu sh B⁻¹) ((congrArg Fm ((congrArg (finHom V).rangeRestrict h1).trans
      (map_mul (finHom V).rangeRestrict _ _))).trans (hy _))
