import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePlaceVacuumAnyDarbouxCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSchwartzSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveGoodModel
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox

noncomputable section

namespace GlobalTheory.TwoModels

open scoped Classical in

theorem exists_two_models : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n d r s r₁ s₁ : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r₁ s₁ →
    ∀ (χX χW : Chr F E), IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d →
    ∀ cb co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      cb.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ (Mb M₁ : Model σ X W) (omb om₁ : Rep σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d) (c₀ : ℂ),
      Mb.co = cb ∧ M₁.co = co ∧ IsPair B Mb χX χW omb r s r₁ s₁ ∧ IsPair B M₁ χX χW om₁ r s r₁ s₁ ∧
      Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) ∧
      (∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d)) ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e Φ) = c₀ * thetaSum F Φ ∧ (∀ x, e (omb x Φ) = om₁ x (e Φ)) ∧
        ∀ u, e (cb.rho B.ψ u Φ) = co.rho B.ψ u (e Φ) := by
  intro hKP F E _ _ _ _ _ σ B hB n d r s r₁ s₁ X W hX hW χX χW hχX hχW hrX hrW cb co hcb hco

  obtain ⟨μ, 𝓕, hμ, h𝓕⟩ := GlobalTheory.ModelEx.exists_haar_fundDom F E σ n X.J
  have hI := GlobalTheory.VacIndic.eventually_isVac_indicator B hB X W _ _ _ _ hX hW cb hcb
  let M₀ : Model σ X W := ⟨cb, fun _ => 0, 0, ∅⟩
  let ind : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let vac : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    if M₀.IsVac B.ψ v (ind v) then ind v else (GlobalTheory.T.exists_finitePlace_vacuum_any_darboux_coordinates B hB X W _ _ _ _ hX hW cb v).choose
  let Mb : Model σ X W := ⟨cb, vac, μ, 𝓕⟩
  have hMb : Mb.IsGood B.ψ := by
    refine ⟨hcb, fun v => ?_, ?_, hμ, h𝓕⟩
    · show M₀.IsVac B.ψ v (vac v)
      by_cases h : M₀.IsVac B.ψ v (ind v)
      · simp only [vac, if_pos h]; exact h
      · simp only [vac, if_neg h]; exact (GlobalTheory.T.exists_finitePlace_vacuum_any_darboux_coordinates B hB X W _ _ _ _ hX hW cb v).choose_spec
    · filter_upwards [hI] with v hv
      show vac v = ind v
      exact if_pos hv
  obtain ⟨omb, homb⟩ := GlobalTheory.WeilExGen.exists_isWeil hKP.base F E σ B hB n d X W r s r₁ s₁ hX hW Mb hMb χX χW
    hχX hχW hrX hrW
  have hpair : IsPair B Mb χX χW omb r s r₁ s₁ := ⟨hB, hX, hW, hMb, hχX, hχW, hrX, hrW, homb⟩

  obtain ⟨e, ei, ev, hei, hmaps, hheis, hSB, hvac, hstd, hpure, hbij⟩ :=
    GlobalTheory.SympChangeBij.change_of_coordinates_bij F E σ B n d X W Mb r s r₁ s₁ hB hX hW hMb co hco
  let M₁ : Model σ X W := ⟨co, fun v => ev v (Mb.vac v), Mb.μ, Mb.dom⟩
  have hM₁ : M₁.IsGood B.ψ := ⟨hco, hvac, hstd, hMb.haar, hMb.dom⟩
  have hne : ∃ f : SInf F (Fin n × Fin d), f ≠ 0 := by
    by_contra hall
    push_neg at hall
    obtain ⟨φ, hφ, hθ⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin n × Fin d)
    have hle : schA F (Fin n × Fin d) ≤ ⊥ := by
      refine Submodule.span_le.2 ?_
      rintro Φ ⟨f, g, -, rfl⟩
      rw [hall f]
      show pureA F 0 g = 0
      funext x
      simp [pureA]
    have h0 : φ = 0 := (Submodule.mem_bot ℂ).1 (hle hφ)
    exact hθ (by rw [h0]; simp [thetaSum])
  have hev : IsEv B Mb M₁ 1 1 ∅ e := by
    refine ⟨hmaps, fun z Φ hΦ => ?_, fun u hu => hu.elim, ei, ev, ?_, fun v => ⟨rfl, hSB v⟩, hpure⟩
    · have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
      exact hheis z Φ hΦ
    · obtain ⟨f, hf⟩ := hne
      obtain ⟨g, rfl⟩ := hei f
      intro h
      exact hf (by rw [h]; rfl)
  obtain ⟨om₁, hW₁, hint⟩ := GlobalTheory.ModelTr.exists_isWeil_trans_of_bijOn F E σ B n d X W Mb χX χW omb r s r₁ s₁ hpair
    M₁ hM₁ e hev hbij
  obtain ⟨c₀, -, hth⟩ := GlobalTheory.ThetaChange.main F E σ B n d X W Mb χX χW omb r s r₁ s₁ hpair M₁ hM₁ e hev hbij
  refine ⟨Mb, M₁, omb, om₁, e, c₀, rfl, rfl, hpair, ⟨hB, hX, hW, hM₁, hχX, hχW, hrX, hrW, hW₁⟩, hbij,
    fun l hl => (GlobalTheory.ModelAdmUnconditional.model_admissible_iff_evaluation F E σ B n d X W Mb χX χW omb r s r₁ s₁ hpair M₁ hM₁ e hev hbij l).1 hl,
    fun Φ hΦ => ⟨hth Φ hΦ, fun x => hint x Φ hΦ, fun u => hheis u Φ hΦ⟩⟩

end GlobalTheory.TwoModels

end
