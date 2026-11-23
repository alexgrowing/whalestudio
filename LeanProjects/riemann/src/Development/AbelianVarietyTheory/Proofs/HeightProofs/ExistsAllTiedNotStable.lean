import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.BlattnerShiftsSignedParameters
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.IsTypeAtCentral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.TypeAtCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem card_eq_of_congr {n p q : ℕ} {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hs : Formalism.UG.HasSignature G p q) :
    (Finset.univ.filter fun a => ε a = true).card = p ∧ (Finset.univ.filter fun a => ε a = false).card = q := by
  classical
  obtain ⟨hc, Q, hQ⟩ := Formalism.UG.P.sig_data G p q hs
  set p' := (Finset.univ.filter fun a => ε a = true).card with hp'
  set q' := (Finset.univ.filter fun a => ε a = false).card with hq'
  let e1 : Fin p' ≃ {a // ε a = true} := (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype])).symm
  let e2 : Fin q' ≃ {a // ¬ ε a = true} :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype]; simp [hq'])).symm
  let e : Fin p' ⊕ Fin q' ≃ Fin n := (Equiv.sumCongr e1 e2).trans (Equiv.sumCompl _)
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hJ : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    rw [← h]
    calc (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  have hQ' : (P⁻¹.submatrix id e)ᴴ * G * P⁻¹.submatrix id e = Formalism.UG.Jpq p' q' := by
    have : (P⁻¹.submatrix id e)ᴴ * G * P⁻¹.submatrix id e = ((P⁻¹)ᴴ * G * P⁻¹).submatrix e e := by
      ext i j; simp [Matrix.mul_apply]
    rw [this, hJ]
    have h1 : ∀ a, ε (e (Sum.inl a)) = true := fun a => (e1 a).2
    have h2 : ∀ a, ¬ ε (e (Sum.inr a)) = true := fun a => (e2 a).2
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Formalism.REAL.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, h1, h2]
    split_ifs <;> simp
  have hn : n = p' + q' := by
    have := Fintype.card_congr e
    simpa using this.symm
  have h1 := Formalism.UG.P.sig_dim G Q hQ _ hQ'
  have h2 := Formalism.UG.P.sig_dim G _ hQ' Q hQ
  simp only [Fintype.card_fin] at h1 h2 hc
  omega

theorem conj_mem {n : ℕ} {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) :
    P * g * P⁻¹ ∈ UJset ε := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hg' : gᴴ * G * g = G := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        rw [h, hg', ← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

theorem exp_mem {n : ℕ} {G X : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G) (hX : Xᴴ * G + G * X = 0) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH G := by
  have hd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have h1 : (t • X)ᴴ = G * (-(t • X)) * G⁻¹ := by
    have h2 : Xᴴ = G * (-X) * G⁻¹ := by
      rw [Matrix.mul_neg, ← eq_neg_of_add_eq_zero_left hX, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
        Matrix.mul_one]
    rw [conjTranspose_smul, h2]
    simp
  show (NormedSpace.exp (t • X))ᴴ * G * NormedSpace.exp (t • X) = G
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hG, Matrix.exp_neg]
  have hu : IsUnit (NormedSpace.exp (t • X)).det := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _)
  rw [Matrix.mul_assoc (G * _), Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

section Pred

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)

abbrev GoodAt (S : SPar) : Prop := GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 S

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {S : SPar}
  {σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)} {lam : Fin V.rank → ℝ} {ε : Fin V.rank → Bool}
  {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}

end Pred

variable {D : D7} {X : ThetaX D}

def Good (V : HSp D) (S : D.what₂.Tau → SPar) : Prop := ∀ τ, GoodAt V τ (S τ)

def VanishOffGood (X : ThetaX D) : Prop := ∀ V : HSp D, V.SigOK → ∀ S, ¬ Good V S → X.typ V S = ⊥

def Agree (T : ThetaTied D X) : Prop :=
  ∀ θ, IsInfFam (D := D) θ → ∀ V : HSp D, V.SigOK → ∀ S, Good V S → ∀ F : X.AF V,
    (∀ τ, IsTypeAt θ V τ (S τ) (T.ev V F)) ↔ ∀ τ, HasTypeAt θ V τ (S τ) (T.ev V F)

def TypAll (T : ThetaTied D X) : Prop :=
  AllSome (IsInfFam (D := D)) fun θ => ∀ V : HSp D, V.SigOK → ∀ S, Good V S →
    ∀ F, F ∈ X.typ V S ↔ ∀ τ, IsTypeAt θ V τ (S τ) (T.ev V F)

def ThetaDatumGood (T : ThetaTied D X) : Prop :=
  AllSome (IsInfFam (D := D)) fun θ => ∀ V : HSp D, V.SigOK → ∀ S, Good V S →
    ∀ F, F ∈ X.typ V S ↔ ∀ τ, HasTypeAt θ V τ (S τ) (T.ev V F)

open Classical in

def retype (X : ThetaX D) (J : ∀ V, Submodule ℂ (X.AF V)) : ThetaX D :=
  { X with typ := fun V S => if Good V S then X.typ V S else J V }

def allThetaData_retype {A : TH.ProvA} (h : AllTied D X A) (J : ∀ V, Submodule ℂ (X.AF V)) : AllTied D (retype X J) A where
  T := { h.T with }
  sm := h.sm
  ty := ⟨h.ty.1, fun θ hθ V hV S hS => by
    have e : (retype X J).typ V S = X.typ V S := if_pos hS
    rw [e]
    exact h.ty.2 θ hθ V hV S hS⟩
  W := { h.W with om_tw := { h.W.om_tw with } }
  unr := h.unr
  kf := { h.kf with }
  phiUp := h.phiUp
  B := { h.B with }
  real := h.real
  prov := h.prov

def thirdPar (D : D7) (t : ℕ) (ht : Odd t) (ht' : D.R.r + 5 ≤ t) : TPar D where
  t := t
  t_odd := ht
  t_ge := ht'
  u := fun _ _ => 1 / 3
  v := fun _ _ => 1 / 3
  b := fun _ _ => 1 / 3
  e := fun _ _ => 1 / 3
  eta := fun _ => 1 / 2
  eta_half := fun _ => Or.inl rfl

def StableGood (X : ThetaX D) : Prop :=
  ∀ (P : TPar D) (j : ℕ), j ≤ D.R.m → Good (X.Ys P.t j) (P.Dpar j) →
    (∀ g F, Formalism.MainNotions.CayleySignature.IsDv X P j F → Formalism.MainNotions.CayleySignature.IsDv X P j (X.actF _ g F)) ∧
    ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D (X.Ys P.t j) τ), ∀ F, Formalism.MainNotions.CayleySignature.IsDv X P j F →
      Formalism.MainNotions.CayleySignature.IsDv X P j (X.actR _ τ h F)

def Hypotheses₂ : Prop :=
  GlobalTheory.Published.DiscreteSeriesUpqExists ∧ GlobalTheory.Published.DiscreteSeriesUpqUnique ∧ GlobalTheory.Published.HarishChandraModules ∧
    GlobalTheory.Published.CasselmanWallach

end GlobalTheory.TypeAtCompare

end
