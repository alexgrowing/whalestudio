import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.LiftPlane

section Ring

variable {R : Type} [CommRing R] {M : ℕ}

private theorem hform_eq_dotProduct_mulVec (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a z : Fin M → R) :
    (fun j => ∑ i, c (a i) * Jm i j) ⬝ᵥ z = Formalism.UG.hform c Jm a z := by
  simp only [Formalism.UG.hform, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm

private theorem smul_vecMulVec_left (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) (k : R) :
    k • Matrix.vecMulVec a (fun j => ∑ i, c (a i) * Jm i j) =
      Matrix.vecMulVec (k • a) (fun j => ∑ i, c (a i) * Jm i j) := by
  ext i j
  simp [Matrix.vecMulVec_apply, mul_assoc]

theorem det_qr (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) (k : R) :
    (qr c Jm a k).det = 1 + k * Formalism.UG.hform c Jm a a := by
  rw [qr, smul_vecMulVec_left, Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow,
    dotProduct_smul, smul_eq_mul, hform_eq_dotProduct_mulVec]

theorem qr_mulVec (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a z : Fin M → R) (k : R) :
    (qr c Jm a k).mulVec z = z + (k * Formalism.UG.hform c Jm a z) • a := by
  rw [qr, Matrix.add_mulVec, Matrix.one_mulVec, smul_vecMulVec_left, Matrix.vecMulVec_mulVec, hform_eq_dotProduct_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul]
  ring

end Ring

section Lift

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

theorem iB_mul_one_tmul (P : PlaceMap F K) (y : K ⊗[F] E) (s : E) :
    iB P y * ((1 : AF F) ⊗ₜ[F] s) = iB P (y * inclR K s) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul k e =>
    simp [iB, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.tmul_mul_tmul]
  | add y₁ y₂ h₁ h₂ => rw [map_add, add_mul, h₁, h₂, add_mul, map_add]

theorem sigR_incl (σ : E →ₐ[F] E) (e : E) : sigR K σ (inclR K e) = inclR K (σ e) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem hform_incV (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a t : Fin M → E) :
    Formalism.UG.hform (sigR K σ) (JR K J) (incV K a) (incV K t) = inclR K (hf σ J a t) := by
  simp only [Formalism.UG.hform, incV, JR, Sa2.hf, Matrix.map_apply, sigR_incl, map_sum, map_mul]

end Lift

theorem lift_plane : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → (∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1)) → ∀ (a b : Fin M → E) (x : HA K σ J), IsQPairOf (sigR K σ) (JR K J) (incV K a) (incV K b) ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) → L x ∈ PlaneSupp σ J (P.inj 1) a b := by
  intro F E _ _ _ _ _ σ _ M J _ K _ _ P L hL hSU a b x hx
  obtain ⟨l, ka, kb, -, -, hl, hka, hkb, hX⟩ := hx
  have hdet : ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 := by
    rw [hX, Matrix.det_mul, det_qr, det_qr, hka, hkb]
    simpa using hl
  refine ⟨hSU x hdet, ?_⟩
  intro v hav hbv
  have hfix : ∀ (c : Fin M → E) (k : K ⊗[F] E), hf σ J c v = 0 →
      (qr (sigR K σ) (JR K J) (incV K c) k).mulVec (incV K v) = incV K v := by
    intro c k hc
    rw [qr_mulVec, hform_incV, hc, map_zero, mul_zero, zero_smul, add_zero]
  have hXv : ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).mulVec (incV K v) = incV K v := by
    rw [hX, ← Matrix.mulVec_mulVec, hfix b kb hbv, hfix a ka hav]
  have hsub : (((HA.mat (AF F) σ J (L x)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1).mulVec (vA v) = 0 := by
    funext i
    have hterm : ∀ j, (((HA.mat (AF F) σ J (L x)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j * vA v j =
        iB P ((((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) - 1) i j * inclR K (v j)) := by
      intro j
      rw [hL x i j, ← iB_mul_one_tmul]
      rfl
    have hsum : ∑ j, (((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) - 1) i j * inclR K (v j) =
        ((((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) - 1).mulVec (incV K v)) i := rfl
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← map_sum]
    have h0 : ((((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) - 1).mulVec (incV K v)) = 0 := by
      rw [Matrix.sub_mulVec, hXv, Matrix.one_mulVec, sub_self]
    rw [hsum, h0, Pi.zero_apply, map_zero]
  calc ((HA.mat (AF F) σ J (L x)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).mulVec (vA v)
      = (((HA.mat (AF F) σ J (L x)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1).mulVec (vA v) +
          (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).mulVec (vA v) := by
        rw [← Matrix.add_mulVec, sub_add_cancel]
    _ = vA v := by rw [hsub, Matrix.one_mulVec, zero_add]

end GlobalTheory.CompanionTheory.SaGen.LiftPlane

end
