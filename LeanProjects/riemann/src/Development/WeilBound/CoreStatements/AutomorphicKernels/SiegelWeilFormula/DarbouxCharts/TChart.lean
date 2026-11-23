import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.THeis
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.JjMulJj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinateChangeRealisedWithDoubleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZeroStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.RatWeilOp

namespace PositivityTheory.SiegelWeilFormula.Tunit

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open PositivityTheory.SiegelWeilFormula.TBij PositivityTheory.SiegelWeilFormula.TBij.Adp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_chart (d : SD σ) : ∃ (τ : d.κ ≃ Ix d)
    (d' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))) d.κ),
    GlobalTheory.TowU.IsRat d' ∧ ∀ w, d'.e w = c0 d τ w := by
  classical
  have hD := d.ok.dbl
  let τ : d.κ ≃ Ix d := Fintype.equivOfCardEq (card_ix d)
  obtain ⟨a, ha, hact⟩ := exists_symp d.dd.e (c0 d τ) (fun w w' => by rw [symplecticForm_coordinates, sy_eq]) (by
    rintro w ⟨y, z, h⟩
    obtain ⟨x, hx⟩ := rat_surj d.bs d.dd.e (fun x => hD.rat x) y z
    obtain rfl : w = incM F x := d.dd.e.injective (h.trans hx.symm)
    exact coordinates_rational d τ x)
  set J := jj d.κ F with hJ
  set b := -(J * aᵀ * J) with hb
  have hba : b * a = 1 := by
    rw [hb, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc aᵀ, ha, jj_mul_jj, neg_neg]
  have hab : a * b = 1 := mul_eq_one_comm.1 hba
  have hinv : ∀ w, act (b.map (algebraMap F (AF F))) (c0 d τ w) = d.dd.e w := fun w => by
    rw [hact w, ← act_mul, ← Matrix.map_mul, hba, Matrix.map_one _ (map_zero _) (map_one _), act_one']
  have hright : ∀ u, c0 d τ (d.dd.e.symm (act (b.map (algebraMap F (AF F))) u)) = u := fun u => by
    rw [hact, LinearEquiv.apply_symm_apply, ← act_mul, ← Matrix.map_mul, hab,
      Matrix.map_one _ (map_zero _) (map_one _), act_one']
  let e' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) ≃ₗ[AF F] (d.κ → AF F) × (d.κ → AF F) :=
    { c0 d τ with
      invFun := fun u => d.dd.e.symm (act (b.map (algebraMap F (AF F))) u)
      left_inv := fun w => by
        show d.dd.e.symm (act (b.map (algebraMap F (AF F))) (c0 d τ w)) = w
        rw [hinv, LinearEquiv.symm_apply_apply]
      right_inv := hright }
  refine ⟨τ, ⟨e', fun w w' => ?_⟩, fun x => ?_, fun w => rfl⟩
  · rw [d.dd.form]
    show om (d.dd.e w) (d.dd.e w') = om (c0 d τ w) (c0 d τ w')
    rw [symplecticForm_coordinates, sy_eq]
  · obtain ⟨y, z, h⟩ := coordinates_rational d τ x
    exact ⟨y, z, h⟩

theorem T_chart (d : SD σ) : ∃ (τ : d.κ ≃ Ix d) (S0 : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ((d.κ → AF F) → ℂ))
    (S0' : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ((d.κ → AF F) → ℂ)) (C : ℂ),
    GlobalTheory.TowU.IsOp d.B.ψ (fun w => c0 d τ (d.dd.e.symm w)) S0 S0' ∧
    ∀ Φ ∈ d.sch, ∀ X, d.T Φ X = C * S0 Φ (fun k => d.crd X (τ k)) := by
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨τ, d', hrat, he'⟩ := exists_chart d
  obtain ⟨S0, S0', hS⟩ := GlobalTheory.T.darbouxCoordinateChange_realised_with_double F E σ d.ok.good.cm d.B.ψ hψ (Fin d.m) (Fin d.n ⊕ Fin d.n) d.κ d.κ _ d.dd d'
    (by exact d.ok.dbl.rat) hrat
  have hop := hS.1
  have hs : (fun w => d'.e (d.dd.e.symm w)) = fun w => c0 d τ (d.dd.e.symm w) := funext fun w => he' _
  rw [hs] at hop
  have rhoS : ∀ w, ∀ φ ∈ schA F d.κ, S0 (d.dd.rho d.B.ψ w φ) = schr d.B.ψ (c0 d τ w) (S0 φ) := by
    intro w φ hφ
    simp only [Darboux.rho]
    rw [hop.Heisenberg₂ _ _ hφ, LinearEquiv.symm_apply_apply]
  have rhoS' : ∀ w, ∀ φ ∈ schA F d.κ, S0' (schr d.B.ψ (c0 d τ w) φ) = d.dd.rho d.B.ψ w (S0' φ) := by
    intro w φ hφ
    have h1 := rhoS w (S0' φ) (hop.pres' φ hφ)
    rw [hop.right φ hφ] at h1
    have hm : d.dd.rho d.B.ψ w (S0' φ) ∈ schA F d.κ :=
      GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ _ _ (hop.pres' φ hφ)
    rw [← h1, hop.left _ hm]
  set l' : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ℂ := d.l ∘ₗ S0' with hl'
  have hadm : l' ∈ (adeleClass F).adm d.κ := hop.adm' d.l d.ok.dbl.adm
  have hinv : ∀ (y : d.κ → AF F), ∀ φ ∈ schA F d.κ, l' (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l' φ := by
    intro y φ hφ
    obtain ⟨w, hw⟩ : ∃ w, c0 d τ w = (0, y) := ⟨d'.e.symm (0, y), by rw [← he', LinearEquiv.apply_symm_apply]⟩
    obtain ⟨Z, rfl⟩ := coordinates_fst_eq_zero d τ w (by rw [hw])
    have e1 : (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = schr d.B.ψ (c0 d τ (Z * (dg d)ᵀ)) φ := by
      rw [hw]; funext x; simp [schr]
    rw [e1, hl', LinearMap.comp_apply, rhoS' _ φ hφ, LinearMap.comp_apply]
    exact d.ok.dbl.kill Z _ (hop.pres' φ hφ)
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F d.B.ψ hψ d.κ l' hadm hinv
  refine ⟨τ, S0, S0', c, hop, fun Φ hΦ X => ?_⟩
  have hΨ : d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ ∈ schA F d.κ :=
    GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ _ _ hΦ
  have e0 : c0 d τ (X * (incM F d.b.1.toCols₂)ᵀ) = (fun k => d.crd X (τ k), 0) := coordinates_frame d τ X
  have e1 : d.T Φ X = l' (S0 (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ)) := by
    rw [hl', LinearMap.comp_apply, hop.left _ hΨ]
    rfl
  rw [e1, hc _ (hop.pres _ hΨ), rhoS _ _ hΦ, e0]
  simp [schr]

end PositivityTheory.SiegelWeilFormula.Tunit

end
