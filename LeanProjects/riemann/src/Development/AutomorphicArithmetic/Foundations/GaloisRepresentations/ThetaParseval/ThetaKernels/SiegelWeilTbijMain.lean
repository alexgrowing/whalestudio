import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.JjMulJj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTbijChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTbijFrame

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.RatWeilOp
namespace PositivityTheory.SiegelWeilFormula.TBij
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace Adp
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.card_ix (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Fintype.card d.κ = Fintype.card (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) := by
  rw [card_eq d.bs d.dd.e, Fintype.card_prod, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin]
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.core (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ (τ : d.κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (e : ((d.κ → AF F) → ℂ) →ₗ[ℂ] d.Fn) (C : ℂ), C ≠ 0 ∧
    Set.BijOn e (schA F d.κ : Set _) (schA F d.κ : Set _) ∧
    (∀ l ∈ (adeleClass F).adm d.κ, l ∘ₗ e ∈ (adeleClass F).adm d.κ) ∧
    ∀ Ψ ∈ schA F d.κ, ∀ X, d.T (e Ψ) X = C * Ψ (fun k => d.crd X (τ k)) := by
  classical
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hF : IsTotallyReal F := d.ok.good.cm.1
  have hD := d.ok.dbl
  let τ : d.κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d := Fintype.equivOfCardEq (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.card_ix d)
  obtain ⟨a, ha, hact⟩ := exists_symp d.dd.e (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ) (fun w w' => by rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.symplecticForm_coordinates, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq]) (by
    rintro w ⟨y, z, h⟩
    obtain ⟨x, hx⟩ := rat_surj d.bs d.dd.e (fun x => hD.rat x) y z
    obtain rfl : w = incM F x := d.dd.e.injective (h.trans hx.symm)
    exact _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_rational d τ x)
  set J := jj d.κ F with hJ
  set b := -(J * aᵀ * J) with hb
  have hba : b * a = 1 := by
    rw [hb, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc aᵀ, ha, jj_mul_jj, neg_neg]
  have hab : a * b = 1 := mul_eq_one_comm.1 hba
  have hbs : bᵀ * J * b = J := by
    calc bᵀ * J * b = bᵀ * (aᵀ * J * a) * b := by rw [ha]
      _ = (a * b)ᵀ * J * (a * b) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = J := by rw [hab, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨e, c, ei, ev, h⟩ := hasOp_of_symplectic hF hψ b hbs
  have hinv : ∀ w, act (b.map (algebraMap F (AF F))) (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) = d.dd.e w := fun w => by
    rw [hact w, ← act_mul, ← Matrix.map_mul, hba, Matrix.map_one _ (map_zero _) (map_one _), act_one']
  have hsurj : ∀ u, ∃ w, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w = u := fun u => ⟨d.dd.e.symm (act (b.map (algebraMap F (AF F))) u), by
    rw [hact, LinearEquiv.apply_symm_apply, ← act_mul, ← Matrix.map_mul, hab,
      Matrix.map_one _ (map_zero _) (map_one _), act_one']⟩
  have hheis : ∀ w, ∀ Ψ ∈ schA F d.κ, e (schr d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) Ψ) = d.dd.rho d.B.ψ w (e Ψ) := fun w Ψ hΨ => by
    rw [h.Heisenberg₂ _ Ψ hΨ, hinv]
    rfl
  have hadm := isOp_adm h d.l hD.adm
  obtain ⟨C, hC⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F d.B.ψ hψ d.κ (d.l ∘ₗ e) hadm (fun y φ hφ => by
    obtain ⟨w, hw⟩ := hsurj (0, y)
    obtain ⟨Z, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_fst_eq_zero d τ w (by rw [hw])
    have e1 : (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = schr d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ)) φ := by
      rw [hw]; funext x; simp [schr]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, hheis _ φ hφ]
    exact hD.kill Z _ (h.maps φ hφ))
  have hT : ∀ Ψ ∈ schA F d.κ, ∀ X, d.T (e Ψ) X = C * Ψ (fun k => d.crd X (τ k)) := fun Ψ hΨ X => by
    have h1 := hC _ (GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (X * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ)) Ψ hΨ)
    rw [LinearMap.comp_apply, hheis _ Ψ hΨ, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_frame] at h1
    rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, h1]
    simp [schr]
  refine ⟨τ, e, C, fun hC0 => ?_, h.bijOn hψ, fun l hl => isOp_adm h l hl, hT⟩
  obtain ⟨Φ, hΦ, hθ⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F d.κ
  obtain ⟨Ψ, hΨ, rfl⟩ := (h.bijOn hψ).surjOn hΦ
  have h0 : ∀ y : Matrix (Fin d.m) (Fin d.n) E,
      d.l (d.dd.rho d.B.ψ (incM F (Matrix.fromCols y (-y))) (e Ψ)) = 0 := fun y => by
    rw [← hheis _ Ψ hΨ]
    have := hC _ (GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (incM F (Matrix.fromCols y (-y)))) Ψ hΨ)
    rw [LinearMap.comp_apply] at this
    rw [this, hC0, zero_mul]
  have h2 := hD.theta (e Ψ) hΦ
  simp only [h0] at h2
  exact hθ (h2.unique hasSum_zero)
end Adp
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij : _root_.PositivityTheory.SiegelWeilFormula.TBij_k := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨τ, e, C, hC, hbij, -, hT⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.core d
  have hcomp : ∀ Ψ ∈ schA F d.κ, (fun c => d.T (e Ψ) (d.cmb c)) = C • fun x : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F => Ψ (x ∘ τ) :=
    fun Ψ hΨ => by
      funext c
      rw [hT Ψ hΨ, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb]
      rfl
  refine ⟨fun Φ hΦ => ?_, fun f hf => ?_, fun Φ hΦ h0 => ?_⟩
  · obtain ⟨Ψ, hΨ, rfl⟩ := hbij.surjOn hΦ
    show (fun c => d.T (e Ψ) (d.cmb c)) ∈ schA F (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d)
    rw [hcomp Ψ hΨ]
    exact Submodule.smul_mem _ C (comp_schA τ hΨ)
  · have hg : (fun c => f (d.cmb c)) ∈ schA F (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) := hf
    have hΨ : C⁻¹ • (fun x : d.κ → AF F => f (d.cmb (x ∘ τ.symm))) ∈ schA F d.κ :=
      Submodule.smul_mem _ _ (comp_schA τ.symm hg)
    refine ⟨e _, hbij.mapsTo hΨ, funext fun X => ?_⟩
    rw [hT _ hΨ]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hC, one_mul]
    congr 1
    conv_rhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d X]
    congr 1
    funext k
    simp
  · obtain ⟨Ψ, hΨ, rfl⟩ := hbij.surjOn hΦ
    have hz : Ψ = 0 := by
      funext v
      have := congrFun h0 (d.cmb (v ∘ τ.symm))
      rw [hT Ψ hΨ, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb] at this
      simpa [hC] using this
    rw [hz, map_zero]
end PositivityTheory.SiegelWeilFormula.TBij
end
end
