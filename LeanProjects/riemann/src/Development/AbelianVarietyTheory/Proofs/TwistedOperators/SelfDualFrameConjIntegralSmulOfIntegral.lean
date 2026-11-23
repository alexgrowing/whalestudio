import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameIntegralGramMatrix
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjIntegral

theorem mul_int {R : Type} [CommRing R] (S : Subring R) {n : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) (i j : Fin n) : (A * B) i j ∈ S := by
  rw [Matrix.mul_apply]
  exact S.sum_mem fun k _ => S.mul_mem (hA i k) (hB k j)

theorem conj_int {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n : ℕ}
    (G Gi γ γi : Matrix (Fin n) (Fin n) R) (hG : ∀ i j, G i j ∈ S) (hGi : ∀ i j, Gi i j ∈ S) (hGG : Gi * G = 1)
    (hγ : γ * γi = 1) (hu : (γ.map σ)ᵀ * G * γ = G) (a : R) (ha : ∀ i j, (a • γ) i j ∈ S) :
    ∀ i j, (σ a • γi) i j ∈ S := by
  have e1 : γi = Gi * (γ.map σ)ᵀ * G := by
    calc γi = Gi * G * γi := by rw [hGG, Matrix.one_mul]
      _ = Gi * ((γ.map σ)ᵀ * G * γ) * γi := by rw [hu]
      _ = Gi * (γ.map σ)ᵀ * G * (γ * γi) := by simp only [Matrix.mul_assoc]
      _ = Gi * (γ.map σ)ᵀ * G := by rw [hγ, Matrix.mul_one]
  have e2 : σ a • γi = Gi * ((a • γ).map σ)ᵀ * G := by
    have : (a • γ).map σ = σ a • γ.map σ := by
      ext i j; simp [Matrix.map_apply, Matrix.smul_apply, map_mul]
    rw [this, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, e1]
  have hc : ∀ i j, ((a • γ).map σ)ᵀ i j ∈ S := fun i j => hσ _ (ha j i)
  rw [e2]
  exact mul_int S (mul_int S hGi hc) hG

theorem conj_int_both {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n : ℕ}
    (G Gi γ γi : Matrix (Fin n) (Fin n) R) (hG : ∀ i j, G i j ∈ S) (hGi : ∀ i j, Gi i j ∈ S) (hGG : Gi * G = 1)
    (hγ : γ * γi = 1) (hγ' : γi * γ = 1) (hu : (γ.map σ)ᵀ * G * γ = G) (a : R)
    (ha : ∀ i j, (a • γ) i j ∈ S) (ha' : ∀ i j, (a • γi) i j ∈ S) :
    (∀ i j, (σ a • γ) i j ∈ S) ∧ (∀ i j, (σ a • γi) i j ∈ S) := by
  have hu' : (γi.map σ)ᵀ * G * γi = G := by
    have h1 : (γi.map σ)ᵀ * (γ.map σ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hγ, Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
    calc (γi.map σ)ᵀ * G * γi = (γi.map σ)ᵀ * ((γ.map σ)ᵀ * G * γ) * γi := by rw [hu]
      _ = ((γi.map σ)ᵀ * (γ.map σ)ᵀ) * G * (γ * γi) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, hγ, Matrix.one_mul, Matrix.mul_one]
  exact ⟨conj_int S σ hσ G Gi γi γ hG hGi hGG hγ' hu' a ha', conj_int S σ hσ G Gi γ γi hG hGi hGG hγ hu a ha⟩

theorem unit_conj {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (B Bi H J : Matrix (Fin n) (Fin n) R)
    (hB : Bi * B = 1) (hB' : B * Bi = 1) (hH : Formalism.UG.cT σ H * J * H = J) :
    ((Bi * H * B).map σ)ᵀ * (Formalism.UG.cT σ B * J * B) * (Bi * H * B) = Formalism.UG.cT σ B * J * B := by
  have hcT : ∀ A C : Matrix (Fin n) (Fin n) R, Formalism.UG.cT σ (A * C) = Formalism.UG.cT σ C * Formalism.UG.cT σ A := by
    intro A C; simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have e : Formalism.UG.cT σ Bi * Formalism.UG.cT σ B = 1 := by
    rw [← hcT, hB']
    simp only [Formalism.UG.cT, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  change Formalism.UG.cT σ (Bi * H * B) * _ * _ = _
  rw [hcT, hcT]
  calc Formalism.UG.cT σ B * (Formalism.UG.cT σ H * Formalism.UG.cT σ Bi) * (Formalism.UG.cT σ B * J * B) * (Bi * H * B)
      = Formalism.UG.cT σ B * (Formalism.UG.cT σ H * (Formalism.UG.cT σ Bi * Formalism.UG.cT σ B) * J * (B * Bi) * H) * B := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ B * J * B := by rw [e, hB', Matrix.mul_one, Matrix.mul_one, hH]

end GlobalTheory.ConjIntegral

namespace GlobalTheory.ConjIntegral

set_option maxHeartbeats 800000 in

theorem conj_smul_isIntM : ∀ {D : D7} (T : HSp D) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC T ΛT → IsFrame βT ΛT → ∀ (h : GL (Fin T.rank) (EAf D)), h ∈ UA D.sp.cm T.gram → ∀ (γ : GL (Fin T.rank) (EAf D)), γ = βT⁻¹ * h * βT → ∀ (a : AE D), IsIntM (toEAf D a • γ.1) → IsIntM (toEAf D a • (γ⁻¹ : GL (Fin T.rank) (EAf D)).1) → IsIntM (toEAf D (cA D a) • γ.1) ∧ IsIntM (toEAf D (cA D a) • (γ⁻¹ : GL (Fin T.rank) (EAf D)).1) := by
  intro D T ΛT βT hsd hβ h hh γ hγ a h1 h2
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D T ΛT hsd
  obtain ⟨G, hG⟩ := GlobalTheory.FrameGram.exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (fun _ => GlobalTheory.LevSplit.sigR_int) (fun _ => rfl) T.gram βT ΛT hβ (fun y hy => (hsd.2 y).1 hy) s s' hs hd
  have hσ : ∀ x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun _ hx => GlobalTheory.LevSplit.sigR_int hx
  have hGm : ∀ i j, (intGL D.host.F D.host.E T.rank G).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun i j => (G.1 i j).2
  have hGi : ∀ i j, (intGL D.host.F D.host.E T.rank G⁻¹).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun i j => ((G⁻¹).1 i j).2
  have hGG : (intGL D.host.F D.host.E T.rank G⁻¹).1 * (intGL D.host.F D.host.E T.rank G).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

  have hhu : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) h.1 * T.gram.map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F)) * h.1 =
      T.gram.map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F)) := hh
  have hγ1 : γ.1 = (βT⁻¹).1 * h.1 * βT.1 := by rw [hγ]; rfl
  have hu := unit_conj (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) βT.1 (βT⁻¹).1 h.1 _
    (Units.inv_mul βT) (Units.mul_inv βT) hhu
  rw [← hγ1, ← hG] at hu
  have key := conj_int_both _ _ hσ _ _ γ.1 (γ⁻¹).1 hGm hGi hGG (Units.mul_inv γ) (Units.inv_mul γ) hu (toEAf D a) h1 h2
  rw [GlobalTheory.AdelicLatMove.toEAf_cA a]
  exact key

end GlobalTheory.ConjIntegral
