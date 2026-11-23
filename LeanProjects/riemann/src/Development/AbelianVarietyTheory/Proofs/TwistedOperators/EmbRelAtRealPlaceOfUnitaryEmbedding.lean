import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.EmbAtPlace

variable {D : D7}

theorem mat_ext {m n : Type*} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) {M N : Matrix m n (Formalism.L2.Theta.AE D)}
    (h1 : M.map (Formalism.L2.Theta.finPart D) = N.map (Formalism.L2.Theta.finPart D))
    (h2 : ∀ τ, M.map (fun z => θ τ (Formalism.L2.Theta.infPart D z)) = N.map (fun z => θ τ (Formalism.L2.Theta.infPart D z))) :
    M = N := by
  ext i j
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j
  · rw [RingHom.map_sub, RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun (h2 τ) i) j

theorem vec_ext {n : Type*} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) {v w : n → Formalism.L2.Theta.AE D}
    (h1 : ∀ i, Formalism.L2.Theta.finPart D (v i) = Formalism.L2.Theta.finPart D (w i))
    (h2 : ∀ τ i, θ τ (Formalism.L2.Theta.infPart D (v i)) = θ τ (Formalism.L2.Theta.infPart D (w i))) : v = w := by
  funext i
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · rw [RingHom.map_sub, sub_eq_zero]; exact h1 i
  · rw [RingHom.map_sub, RingHom.map_sub, sub_eq_zero]; exact h2 τ i

theorem theta_incA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : D.host.E) :
    θ τ (Formalism.L2.Theta.infPart D (incA D e)) = tauE D τ e := by
  have : Formalism.L2.Theta.infPart D (incA D e) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] e := by
    simp [Formalism.L2.Theta.infPart, incA, inclR]
  rw [this]; exact (hθ τ).1 e

end GlobalTheory.EmbAtPlace

namespace GlobalTheory.EmbAtPlace

theorem embRel_atTau : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (τ : D.what₂.Tau)
    (h : Matrix (Fin A.rank) (Fin A.rank) ℂ) (g : Matrix (Fin B.rank) (Fin B.rank) ℂ), h ∈ Formalism.QuantumDeterminants.UH (gramAt D A τ) →
    g ∈ Formalism.QuantumDeterminants.UH (gramAt D B τ) → GlobalTheory.RealBessel.IsEmb (gramAt D B τ) ((frameMat B A ι).map (tauE D τ)) g h →
    EmbRel B A ι (atTau θ B τ g) (atTau θ A τ h) := by
  classical
  intro D θ hθ A B ι τ h g hh hg hE
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hX := GlobalTheory.PointAtPlaceHom.atTau_spec hθ B τ hg
  have hY := GlobalTheory.PointAtPlaceHom.atTau_spec hθ A τ hh
  have fX : (matHom B (atTau θ B τ g)).1.map (Formalism.L2.Theta.finPart D) = 1 :=
    (congrArg (fun k : GL (Fin B.rank) (Af D.host.F ⊗[D.host.F] D.host.E) => k.val) (MonoidHom.mem_ker.1 hX.1)).trans Units.val_one
  have fY : (matHom A (atTau θ A τ h)).1.map (Formalism.L2.Theta.finPart D) = 1 :=
    (congrArg (fun k : GL (Fin A.rank) (Af D.host.F ⊗[D.host.F] D.host.E) => k.val) (MonoidHom.mem_ker.1 hY.1)).trans Units.val_one
  have iX : ∀ τ', (matHom B (atTau θ B τ g)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) =
      if τ' = τ then g else 1 := fun τ' => by
    split_ifs with e
    · subst e; exact hX.2.1
    · exact hX.2.2 τ' e
  have iY : ∀ τ', (matHom A (atTau θ A τ h)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) =
      if τ' = τ then h else 1 := fun τ' => by
    split_ifs with e
    · subst e; exact hY.2.1
    · exact hY.2.2 τ' e
  have iF : ∀ τ', ((frameMat B A ι).map (incA D)).map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) =
      (frameMat B A ι).map (tauE D τ') := fun τ' => by
    rw [Matrix.map_map]; congr 1; funext e; exact GlobalTheory.EmbAtPlace.theta_incA hθ τ' e
  refine ⟨?_, fun x hx => ?_⟩
  · refine GlobalTheory.EmbAtPlace.mat_ext hσ ?_ fun τ' => ?_
    · rw [Matrix.map_mul, Matrix.map_mul, fX, fY, Matrix.one_mul, Matrix.mul_one]
    · let φ : Formalism.L2.Theta.AE D →+* ℂ := (θ τ').comp (Formalism.L2.Theta.infPart D)
      change Matrix.map (_ * _) ⇑φ = Matrix.map (_ * _) ⇑φ
      rw [Matrix.map_mul, Matrix.map_mul]
      change (matHom B (atTau θ B τ g)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) *
          ((frameMat B A ι).map (incA D)).map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) =
        ((frameMat B A ι).map (incA D)).map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) *
          (matHom A (atTau θ A τ h)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z))
      rw [iX, iY, iF]
      split_ifs with e
      · subst e; exact hE.1
      · rw [Matrix.one_mul, Matrix.mul_one]
  · refine GlobalTheory.EmbAtPlace.vec_ext hσ (fun i => ?_) fun τ' i => ?_
    · rw [RingHom.map_mulVec, fX, Matrix.one_mulVec]; rfl
    · let φ : Formalism.L2.Theta.AE D →+* ℂ := (θ τ').comp (Formalism.L2.Theta.infPart D)
      change φ _ = φ _
      rw [RingHom.map_mulVec]
      change ((matHom B (atTau θ B τ g)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) *ᵥ
        fun j => θ τ' (Formalism.L2.Theta.infPart D (incA D (x j)))) i = θ τ' (Formalism.L2.Theta.infPart D (incA D (x i)))
      simp only [GlobalTheory.EmbAtPlace.theta_incA hθ]
      rw [iX]
      split_ifs with e
      · subst e
        have h0 : (((frameMat B A ι).map (tauE D τ'))ᴴ * gramAt D B τ') *ᵥ (fun j => tauE D τ' (x j)) = 0 := by
          have hm : ((frameMat B A ι).map (tauE D τ'))ᴴ * gramAt D B τ' =
              (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram).map (tauE D τ') := by
            rw [Matrix.map_mul]
            congr 1
            ext a b
            simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply]
            exact (Formalism.IndefR.Eqv.tauE_star D τ' _).symm
          rw [hm]
          funext i
          have := RingHom.map_mulVec (tauE D τ') (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram) x i
          simp only [Function.comp_def] at this
          rw [← this, hx]
          simp
        exact congrFun (hE.2 _ h0) i
      · rw [Matrix.one_mulVec]

end GlobalTheory.EmbAtPlace
