import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSkewIdealCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchroedingerEigenvectorCompactCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLocalIdealMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLocalIdealNotMemStatement
open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)
open scoped Classical
open scoped GlobalTheory.VacAny
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

noncomputable section

namespace GlobalTheory.ThK.UnrSuppB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem hTens_self_zero {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E) {x : Fin n → E}
    (hx : form σ JA x x = 0) (z : Fin d → AE F E) :
    hTens (cA σ) (incM F JA) (incM F JB) (Matrix.vecMulVec (incV F x) z) (Matrix.vecMulVec (incV F x) z) = 0 := by
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun _ => rfl
  have hg : ∑ i, ∑ k, incV F x i * incM F JA i k * cA σ (incV F x k) = 0 := by
    have e : ∑ i, ∑ k, incV F x i * incM F JA i k * cA σ (incV F x k) = inclR (F := F) (AF F) (form σ JA x x) := by
      simp only [form, dotProduct, Matrix.mulVec, incV, incM, Matrix.map_apply, hc, map_sum, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    rw [e, hx, map_zero]
  unfold hTens
  have : ∀ i j k l, Matrix.vecMulVec (incV F x) z i j * incM F JA i k * incM F JB j l *
      cA σ (Matrix.vecMulVec (incV F x) z k l) =
      (incV F x i * incM F JA i k * cA σ (incV F x k)) * (z j * incM F JB j l * cA σ (z l)) := by
    intro i j k l
    simp only [Matrix.vecMulVec_apply, map_mul]
    ring
  simp only [this]
  have e2 : ∑ i, ∑ j, ∑ k, ∑ l, (incV F x i * incM F JA i k * cA σ (incV F x k)) * (z j * incM F JB j l * cA σ (z l)) =
      (∑ i, ∑ k, incV F x i * incM F JA i k * cA σ (incV F x k)) * (∑ j, ∑ l, z j * incM F JB j l * cA σ (z l)) := by
    symm
    simp_rw [Finset.sum_mul_sum]
  rw [e2, hg, zero_mul]

theorem schr_comm_vac {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F)
    (hvac : M.IsVac ψ v (M.vac v)) (γ : Matrix (Fin n) (Fin d) (AE F E)) (hat : At (evFin F v) γ)
    (hlat : γ ∈ latAtV X W v) (h0 : hTens (cA σ) (incM F X.J) (incM F W.J) γ γ = 0)
    (u : Matrix (Fin n) (Fin d) (AE F E)) :
    schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v γ) (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v u) (M.vac v)) =
      GlobalTheory.LatVac.psiAt ψ v (evFin F v (symp (cA σ) (-1) (incM F X.J) (incM F W.J) γ u)) •
        schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v u) (M.vac v) := by
  obtain ⟨hSB, -, θ, -, hact⟩ := hvac
  have hfix : schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v γ) (M.vac v) = M.vac v := by
    apply GlobalTheory.TensUniq.eq_of_tens_eq v (M.vac v) _ _ hSB
    intro r hr
    rw [← GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v _ hat _ r hr, hact _ hlat r hr]
    simp only [GlobalTheory.WeilM.symp, h0, mul_zero, map_zero, AddChar.map_zero_eq_one, one_smul]
  rw [GlobalTheory.VacLoc.schr_comm, hfix]
  congr 2
  rw [M.co.form]
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, dotProduct, map_sub, map_sum, map_mul]

theorem evShift_vac : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {a b : ℕ} (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), B.IsGood σ → G.IsGood B → G₁.IsGood B → CfgB B G G₁ H H' →
    ∀ e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b), IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (ei' : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev' : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
      ei' ≠ 0 →
      (∀ v, ev' v (G.M'.vac v) = G₁.M'.vac v ∧
        (SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)).map (ev' v) = SB (Fin b × Fin (a + b) → Fv F v)) →
      (∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ),
        (∀ v, φ v ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
        e' (pure f φ) = pure (ei' f) fun v => ev' v (φ v)) →
      ∀ (v : Pl F) (l : (AE F E)ˣ), l ∈ idelesAt E (evFin F v) →
        ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) (G.M'.vac v)) =
          if compFin F E v (l : AE F E) ∈ locId v (H.𝔟⁻¹ * conjI σ H'.𝔟) then G₁.M'.vac v else 0 := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hB hG hG₁ hC e' he' ei' ev' hei hev hpure v l hl
  have hψ : Continuous B.ψ := hB.std.1
  have hvac : G.M'.vac v ∈ SB _ := (hG.hM'.vac v).1
  rw [(locOp_rho G.M'.co hψ v (shiftB σ H H' l) hvac).2]
  split_ifs with hin
  · rw [GlobalTheory.T.schrodinger_local_ideal_mem σ B G G₁ H H' hB hG hC v l hl hin, (hev v).1]
  · obtain ⟨γ, hγv, ⟨z, hz⟩, hγL, hne⟩ := GlobalTheory.T.schrodinger_local_ideal_not_mem σ B G G₁ H H' hB hG hC v l hl hin
    have hsb : schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (shiftB σ H H' l)) (G.M'.vac v) ∈ SB _ :=
      GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ v _ _ hvac
    have h1 := GlobalTheory.ThK.EvLocInv.ev_schr_of_mem B G.M' G₁.M' H.ι H'.ι (isoB H H') e' he' hψ hG.hM' hG₁.hM' ei' ev' hei
      hev hpure v γ (Or.inl ⟨z, hz⟩) hγv _ hsb
    have h00 : hTens (cA σ) (incM F G.V'.J) (incM F G.W.J) γ γ = 0 := by
      rw [hz]; exact hTens_self_zero _ _ hC.hH.xx z
    rw [schr_comm_vac G.M' B.ψ v (hG.hM'.vac v) γ hγv hγL h00, map_smul] at h1
    have h2 : (GlobalTheory.LatVac.psiAt B.ψ v (evFin F v (symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) γ (shiftB σ H H' l))) - 1) •
        ev' v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (shiftB σ H H' l)) (G.M'.vac v)) = 0 := by
      rw [sub_smul, one_smul, h1, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.ThK.UnrSuppB
