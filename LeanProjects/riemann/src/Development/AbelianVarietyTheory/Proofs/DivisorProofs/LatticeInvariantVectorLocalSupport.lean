import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
namespace GlobalTheory.LatSelfDualCo

theorem latAtV_selfDual_locCo : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d)) (v : Pl F)
      (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)),
      (∀ γ ∈ latAtV X W v, GlobalTheory.LatVac.psiAt B.ψ v ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2) = 1) →
      w ∈ (latAtV X W v).map (GlobalTheory.LatVac.locCo co v) := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW co v w hw
  set p : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)) with hp
  set z := co.e.symm p with hz
  have hez : co.e z = p := by rw [hz]; exact co.e.apply_symm_apply p
  have hzat : At (evFin F v) z := by
    intro u hu
    have hpu : u • p = 0 := by
      ext k
      · exact GlobalTheory.LatVac.at_liftV v (w.1 k) u hu
      · exact GlobalTheory.LatVac.at_liftV v (w.2 k) u hu
    rw [hz, ← LinearEquiv.map_smul, hpu, map_zero]
  have hloc : GlobalTheory.LatVac.locCo co v z = w := by
    ext k
    · simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hez, hp, GlobalTheory.LatVac.evFin_liftV]
    · simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hez, hp, GlobalTheory.LatVac.evFin_liftV]
  refine ⟨z, ?_, hloc⟩
  refine (GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X W r s r' s' hB hX hW v z hzat).2 ?_
  intro γ hγ
  have hat : At (evFin F v) (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z γ) := by
    intro u hu
    have := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) u 1 z γ
    rw [hzat u hu, one_smul, mul_one, GlobalTheory.LatVacArith.symp_zero_left] at this
    exact this.symm
  rw [GlobalTheory.VacIndic.psi_of_at _ hat, co.form, hez]
  have h := hw (-γ) (neg_mem hγ)
  rw [GlobalTheory.LatVac.psiAt_apply] at h
  convert h using 2
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hp, dotProduct, map_sub, map_sum, map_mul,
    GlobalTheory.LatVac.evFin_liftV, map_neg, Pi.neg_apply, Prod.fst_neg, Prod.snd_neg]
  simp only [neg_mul, mul_neg, Finset.sum_neg_distrib]
  ring_nf

end GlobalTheory.LatSelfDualCo
