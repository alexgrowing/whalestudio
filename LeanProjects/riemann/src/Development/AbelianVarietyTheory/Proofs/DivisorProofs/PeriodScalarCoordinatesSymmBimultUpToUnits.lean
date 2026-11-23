import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEvenCubicalValuesNotMemMaximalIdealPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositive
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitValEqMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInIffScalarMem
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiScalarsRelationsUpToBaseUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitsK
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

noncomputable section

namespace GlobalTheory.Mum.TensPolRel

theorem tauCoord_rel : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (k : Q.X → Q.X → (FractionRing R)ˣ), (∀ a b, Q.TauCoord a b (k a b)) → (∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b) ∧ ∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b) := by
  intro R _ _ _ Q k hk
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  haveI := Q.isAb.proper
  obtain ⟨J, hJ, iJ⟩ := GlobalTheory.Mum.TensPol.exists_int Q.B Q.M.L Q.M.isLB z
  let E : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ := Units.map (ev z).toMonoidHom
  have hE : Function.Injective E := Units.map_injective (ev_inj z)
  have hτ : ∀ a b, ∃ v ∈ unitsS z, val (Q.tau a b) (𝟙 _) z J = E (k a b) * v := fun a b => by
    obtain ⟨u, -, hu⟩ := hk a b
    refine ⟨_, GlobalTheory.Mum.TensPol.val_mem z iJ _ (fun i => ?_) _ u, (hu z J hJ).trans (congrArg (· * _) (gm_unitOn z _))⟩
    fin_cases i <;> exact Over.w _
  choose v hv ev' using hτ
  refine ⟨fun a b => ?_, fun a a' b => ?_⟩
  · refine ⟨k b a * (k a b)⁻¹, mem_unitsK z ?_, by rw [inv_mul_cancel_right]⟩
    have e := Q.tau_symm a b z J hJ
    rw [ev', ev'] at e
    have : E (k b a * (k a b)⁻¹) = v a b * (v b a)⁻¹ := by
      rw [map_mul, map_inv]
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul e
      simp only [ofMul_mul, ofMul_inv] at e' ⊢
      linear_combination (norm := abel) -e'
    exact this ▸ mul_mem (hv a b) (inv_mem (hv b a))
  · refine ⟨k (a + a') b * (k a b * k a' b)⁻¹, mem_unitsK z ?_, by rw [inv_mul_cancel_right]⟩
    have e := Q.tau_add a a' b z J hJ
    have hc : cubV Q.cub z J (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c a') (toUnit (TK R) ≫ Q.c b) ∈ unitsS z := by
      rw [← val_cub Q.cub (toUnit (TK R)) hJ]
      refine GlobalTheory.Mum.TensPol.val_mem z iJ _ (fun i => ?_) _ _
      exact Over.w (lift (Q.c a) (lift (Q.c a') (Q.c b)) ≫ psum Q.B (x3 Q.B) i.down)
    rw [ev', ev', ev'] at e
    generalize cubV Q.cub z J (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c a') (toUnit (TK R) ≫ Q.c b) = w at e hc
    have : E (k (a + a') b * (k a b * k a' b)⁻¹) = v a b * v a' b * (v (a + a') b)⁻¹ * w⁻¹ := by
      rw [map_mul, map_inv, map_mul]
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul e
      simp only [ofMul_mul, ofMul_inv] at e' ⊢
      linear_combination (norm := abel) e'
    exact this ▸ mul_mem (mul_mem (mul_mem (hv a b) (hv a' b)) (inv_mem (hv _ b))) (inv_mem hc)

end GlobalTheory.Mum.TensPolRel
