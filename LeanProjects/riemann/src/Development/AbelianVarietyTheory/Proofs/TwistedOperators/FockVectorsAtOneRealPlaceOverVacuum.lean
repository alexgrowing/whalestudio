import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockOfThetaSquareIntegrable

noncomputable section

namespace GlobalTheory.OnePlaceFock

section Laws

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix Complex
open GlobalTheory.Chain GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars GlobalTheory.VacuumFockLaws
open GlobalTheory.Ker (ipO)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.ArchRec (IsFrameOf Mn)
open scoped Classical ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fockIp_eq {ι : Type} (P Q : MvPolynomial ι ℂ) :
    fockIp P Q = ∑ k ∈ Q.support, P.coeff k * conj (Q.coeff k) * (multiFact k : ℂ) := by
  classical
  have hP : ∀ k ∉ P.support, P.coeff k = 0 := fun k hk => by
    simpa only [MvPolynomial.mem_support_iff, not_not] using hk
  have hQ : ∀ k ∉ Q.support, Q.coeff k = 0 := fun k hk => by
    simpa only [MvPolynomial.mem_support_iff, not_not] using hk
  change ∑ k ∈ P.support, P.coeff k * conj (Q.coeff k) * (multiFact k : ℂ) = _
  have hL : ∑ k ∈ P.support, P.coeff k * conj (Q.coeff k) * (multiFact k : ℂ) =
      ∑ k ∈ P.support ∪ Q.support, P.coeff k * conj (Q.coeff k) * (multiFact k : ℂ) := by
    apply Finset.sum_subset Finset.subset_union_left
    intro k _ hk
    rw [hP k hk, zero_mul, zero_mul]
  have hR : ∑ k ∈ Q.support, P.coeff k * conj (Q.coeff k) * (multiFact k : ℂ) =
      ∑ k ∈ P.support ∪ Q.support, P.coeff k * conj (Q.coeff k) * (multiFact k : ℂ) := by
    apply Finset.sum_subset Finset.subset_union_right
    intro k _ hk
    rw [hQ k hk, map_zero, mul_zero, zero_mul]
  rw [hL, hR]

def sgn {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : ℝ := if ε a then 1 else -1

theorem sgn_cases {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : sgn ε a = 1 ∨ sgn ε a = -1 := by
  unfold sgn
  by_cases h : ε a
  · left; simp [h]
  · right; simp [h]

theorem Jm_eq_sgn {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε = diagonal fun a => (sgn ε a : ℂ) := by
  unfold Formalism.REAL.Jm
  congr 1
  funext a
  unfold sgn
  by_cases h : ε a <;> simp [h]

theorem frame_inv {n : ℕ} {G s fr : Mn n} {ε : Fin n → Bool} (h : IsFrameOf G s ε fr) :
    IsUnit (fr⁻¹).det ∧ s * fr⁻¹ = fr⁻¹ * diagonal (fun a => (sgn ε a : ℂ)) ∧
      (fr⁻¹)ᴴ * G * fr⁻¹ = diagonal fun a => (sgn ε a : ℂ) := by
  obtain ⟨hu, hG, hs⟩ := h
  have hd : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det fr).mp hu
  refine ⟨Matrix.isUnit_nonsing_inv_det fr hd, ?_, ?_⟩
  · rw [hs, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Jm_eq_sgn]
  · have e1 : (fr⁻¹)ᴴ * frᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
    rw [← hG]
    calc (fr⁻¹)ᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * fr⁻¹
        = ((fr⁻¹)ᴴ * frᴴ) * Formalism.REAL.Jm ε * (fr * fr⁻¹) := by simp only [Matrix.mul_assoc]
      _ = diagonal fun a => (sgn ε a : ℂ) := by
        rw [e1, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one, Jm_eq_sgn]

private theorem cplxO_unitMap_eq_I_mul_sign_smul {m n : ℕ} {s B : Matrix (Fin n) (Fin n) ℂ} {s' B' : Matrix (Fin m) (Fin m) ℂ}
    {ε : Fin n → ℝ} {ε' : Fin m → ℝ} (hB : IsUnit B.det) (hs : s * B = B * diagonal fun a => (ε a : ℂ))
    (hs' : s' * B' = B' * diagonal fun a => (ε' a : ℂ)) (i : Fin m) (j : Fin n) :
    cplxO s s' (unitMap B B' i j) = (Complex.I * ((ε' i * ε j : ℝ) : ℂ)) • unitMap B B' i j := by
  have hBi : B⁻¹ * s = (diagonal fun a => (ε a : ℂ)) * B⁻¹ := by
    calc B⁻¹ * s = B⁻¹ * s * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
      _ = B⁻¹ * (s * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (diagonal fun a => (ε a : ℂ)) * B⁻¹ := by
        rw [hs, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.one_mul]
  have hd : (diagonal fun a => (ε' a : ℂ)) * single i j (1 : ℂ) * (diagonal fun a => (ε a : ℂ)) =
      ((ε' i * ε j : ℝ) : ℂ) • single i j (1 : ℂ) := by
    ext a b
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases ha : i = a
    · by_cases hb : j = b
      · subst ha hb; simp
      · simp [hb]
    · simp [ha]
  calc cplxO s s' (unitMap B B' i j)
      = Complex.I • (B' * ((diagonal fun a => (ε' a : ℂ)) * (single i j (1 : ℂ) : Matrix (Fin m) (Fin n) ℂ) *
          (diagonal fun a => (ε a : ℂ))) * B⁻¹) := by
        unfold Formalism.IndefR.Datum.cplxO Formalism.IndefR.Datum.unitMap
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← hBi, ← Matrix.mul_assoc s' B', hs', Matrix.mul_assoc]
    _ = (Complex.I * ((ε' i * ε j : ℝ) : ℂ)) • unitMap B B' i j := by
        rw [hd, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
        rfl

private theorem inv_eq_mul_diagonal_sign_mul_conjTranspose {n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} {ε : Fin n → ℝ}
    (hε : ∀ a, ε a = 1 ∨ ε a = -1) (hB : IsUnit B.det) (hG : Bᴴ * G * B = diagonal fun a => (ε a : ℂ)) :
    G⁻¹ = B * (diagonal fun a => (ε a : ℂ)) * Bᴴ := by
  have hdd : (diagonal fun a => (ε a : ℂ)) * (diagonal fun a => (ε a : ℂ)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with h | h <;> simp [h]
  have e : Bᴴ * G = (diagonal fun a => (ε a : ℂ)) * B⁻¹ := by
    calc Bᴴ * G = Bᴴ * G * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
      _ = Bᴴ * G * B * B⁻¹ := by rw [← Matrix.mul_assoc]
      _ = _ := by rw [hG]
  apply Matrix.inv_eq_left_inv
  calc B * (diagonal fun a => (ε a : ℂ)) * Bᴴ * G = B * (diagonal fun a => (ε a : ℂ)) * (Bᴴ * G) :=
        Matrix.mul_assoc _ _ _
    _ = B * ((diagonal fun a => (ε a : ℂ)) * (diagonal fun a => (ε a : ℂ))) * B⁻¹ := by
        rw [e]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hdd, Matrix.mul_one, Matrix.mul_nonsing_inv _ hB]

private theorem trace_inv_gram_conjTranspose_conj_eq_sign_trace {m n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} {G' B' : Matrix (Fin m) (Fin m) ℂ}
    {ε : Fin n → ℝ} {ε' : Fin m → ℝ} (hε : ∀ a, ε a = 1 ∨ ε a = -1) (hB : IsUnit B.det)
    (hG : Bᴴ * G * B = diagonal fun a => (ε a : ℂ)) (hG' : B'ᴴ * G' * B' = diagonal fun a => (ε' a : ℂ))
    (X Y : Matrix (Fin m) (Fin n) ℂ) :
    (G⁻¹ * (B' * Y * B⁻¹)ᴴ * G' * (B' * X * B⁻¹)).trace =
      ((diagonal fun a => (ε a : ℂ)) * Yᴴ * (diagonal fun a => (ε' a : ℂ)) * X).trace := by
  have h1 : Bᴴ * (B⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hB, Matrix.conjTranspose_one]
  rw [inv_eq_mul_diagonal_sign_mul_conjTranspose hε hB hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have step : B * (diagonal fun a => (ε a : ℂ)) * Bᴴ * ((B⁻¹)ᴴ * (Yᴴ * B'ᴴ)) * G' * (B' * X * B⁻¹) =
      B * ((diagonal fun a => (ε a : ℂ)) * Yᴴ * (B'ᴴ * G' * B') * X) * B⁻¹ := by
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (B * (diagonal fun a => (ε a : ℂ))) Bᴴ (B⁻¹)ᴴ, h1, Matrix.mul_one]
  rw [step, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.one_mul, hG']

private theorem trace_diagonal_single_conjTranspose_single {m n : ℕ} (ε : Fin n → ℝ) (ε' : Fin m → ℝ) (i i' : Fin m) (j j' : Fin n) :
    ((diagonal fun a => (ε a : ℂ)) * (single i' j' (1 : ℂ) : Matrix (Fin m) (Fin n) ℂ)ᴴ *
      (diagonal fun a => (ε' a : ℂ)) * (single i j (1 : ℂ) : Matrix (Fin m) (Fin n) ℂ)).trace =
      if (i, j) = (i', j') then ((ε' i * ε j : ℝ) : ℂ) else 0 := by
  have hY : (single i' j' (1 : ℂ) : Matrix (Fin m) (Fin n) ℂ)ᴴ = single j' i' 1 := by
    ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
    by_cases h1 : j' = a <;> by_cases h2 : i' = b <;> simp [h1, h2]
  have hD : (diagonal fun a => (ε a : ℂ)) * (single j' i' (1 : ℂ) : Matrix (Fin n) (Fin m) ℂ) *
      (diagonal fun a => (ε' a : ℂ)) = single j' i' ((ε j' : ℂ) * ε' i') := by
    ext a b
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
    by_cases h1 : j' = a <;> by_cases h2 : i' = b <;> simp [h1, h2]
  rw [hY, hD, Matrix.trace_single_mul, Matrix.single_apply, smul_eq_mul]
  by_cases h : i = i' ∧ j = j'
  · obtain ⟨rfl, rfl⟩ := h
    simp [mul_comm]
  · have h' : ¬ (i, j) = (i', j') := fun e => h ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩
    simp [h, h']

private theorem trace_inv_gram_single_conj_eq_ite_sign {m n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} {G' B' : Matrix (Fin m) (Fin m) ℂ}
    {ε : Fin n → ℝ} {ε' : Fin m → ℝ} (hε : ∀ a, ε a = 1 ∨ ε a = -1) (hB : IsUnit B.det)
    (hG : Bᴴ * G * B = diagonal fun a => (ε a : ℂ)) (hG' : B'ᴴ * G' * B' = diagonal fun a => (ε' a : ℂ))
    (k l : Fin m × Fin n) :
    (G⁻¹ * (B' * (single l.1 l.2 (1 : ℂ) : Matrix (Fin m) (Fin n) ℂ) * B⁻¹)ᴴ * G' *
      (B' * (single k.1 k.2 (1 : ℂ) : Matrix (Fin m) (Fin n) ℂ) * B⁻¹)).trace =
      if k = l then ((ε' k.1 * ε k.2 : ℝ) : ℂ) else 0 := by
  rw [trace_inv_gram_conjTranspose_conj_eq_sign_trace hε hB hG hG', trace_diagonal_single_conjTranspose_single]

private theorem exists_end_coe_eq_of_linear_on_submodule {X : Type*} (M : Submodule ℂ (X → ℂ)) (T : (X → ℂ) → (X → ℂ))
    (hmem : ∀ g ∈ M, T g ∈ M) (hadd : ∀ g ∈ M, ∀ h ∈ M, T (g + h) = T g + T h)
    (hsmul : ∀ (c : ℂ), ∀ g ∈ M, T (c • g) = c • T g) :
    ∃ a : Module.End ℂ M, ∀ g : M, (a g : X → ℂ) = T g :=
  ⟨{ toFun := fun g => ⟨T g, hmem g g.2⟩
     map_add' := fun g h => Subtype.ext (hadd g g.2 h h.2)
     map_smul' := fun c g => Subtype.ext (hsmul c g g.2) }, fun _ => rfl⟩

set_option maxHeartbeats 4000000 in
private theorem laws_lemma_7 {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (τ : D.what₂.Tau) {s B : Mn V.rank} {s' B' : Mn W.rank} {ε : Fin V.rank → ℝ} {ε' : Fin W.rank → ℝ}
    (hε : ∀ a, ε a = 1 ∨ ε a = -1) (hε' : ∀ a, ε' a = 1 ∨ ε' a = -1) (hB : IsUnit B.det)
    (hs : s * B = B * diagonal fun a => (ε a : ℂ)) (hs' : s' * B' = B' * diagonal fun a => (ε' a : ℂ))
    (hG : Bᴴ * gramAt D V τ * B = diagonal fun a => (ε a : ℂ))
    (hG' : B'ᴴ * gramAt D W τ * B' = diagonal fun a => (ε' a : ℂ)) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hvac : IsFockVacAt (heisO ψ V W) θ τ (cplxO s s') f) :
    (∀ P, IsThetaFunO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f P)) ∧
      (f ≠ 0 → Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f)) ∧
      ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
        ∀ P Q, ipO μ 𝓕 (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f P) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f Q) =
          ipO μ 𝓕 f f * fockIp P Q := by
  classical
  have hsk := GlobalTheory.ThetaSquare.derSkew (V := V) (W := W) hψ hθ
  have hco := GlobalTheory.ThetaSquare.derComm (V := V) (W := W) hψ hθ
  have hsq := GlobalTheory.VacuumFockLaws.fockScale_sq (D := D) τ
  have hc0 := GlobalTheory.VacuumFockLaws.fockScale_ne (D := D) τ
  have hcinv : (fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ)⁻¹ * (8 * Real.pi * ((tauE D τ D.host.xi0).im : ℂ)) = 1 := by
    rw [← hsq]
    field_simp
  have hconj : (starRingEnd ℂ) (fockScale D τ : ℂ)⁻¹ = (fockScale D τ : ℂ)⁻¹ := by rw [map_inv₀, Complex.conj_ofReal]
  have hconjE : (starRingEnd ℂ) (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) = -(-((fockScale D τ : ℂ)⁻¹ * Complex.I)) := by
    rw [map_neg, map_mul, hconj, Complex.conj_I]
    ring
  have Dth : ∀ z g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z g) := fun z g hg => (hsk τ z).2.1 g hg
  have Dlin : ∀ z (α β : ℂ) F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G →
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (α • F + β • G) = α • Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z F + β • Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z G := by
    intro z α β F G hF hG
    rw [GlobalTheory.Size.dRho_add hψ hθ τ z (GlobalTheory.OrientedHeis.theta_smul α hF) (GlobalTheory.OrientedHeis.theta_smul β hG),
      GlobalTheory.Size.dRho_smul, GlobalTheory.Size.dRho_smul]
  have Cm : ∀ z w g, IsThetaFunO ψ V W g → ∀ x,
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ w g) x = Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ w (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z g) x + GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.commScalar V W τ τ z w * g x := by
    intro z w g hg x
    have e := congrFun ((hco τ τ z w).2 g hg) x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    linear_combination e
  have hJ : ∀ k : Fin W.rank × Fin V.rank, cplxO s s' (unitMap B B' k.1 k.2) = ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) :=
    fun k => cplxO_unitMap_eq_I_mul_sign_smul hB hs hs' k.1 k.2
  have hσ : ∀ k : Fin W.rank × Fin V.rank, (ε' k.1 * ε k.2) * (ε' k.1 * ε k.2) = 1 := by
    intro k
    rcases hε k.2 with h | h <;> rcases hε' k.1 with h' | h' <;> rw [h, h'] <;> norm_num
  have htr : ∀ (α β : ℂ) (k l : Fin W.rank × Fin V.rank),
      ((gramAt D V τ)⁻¹ * (β • unitMap B B' l.1 l.2)ᴴ * gramAt D W τ * (α • unitMap B B' k.1 k.2)).trace =
        α * ((starRingEnd ℂ) β * (if k = l then ((ε' k.1 * ε k.2 : ℝ) : ℂ) else 0)) := by
    intro α β k l
    rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, ← trace_inv_gram_single_conj_eq_ite_sign hε hB hG hG' k l]
    rfl
  have kap : ∀ (α β : ℂ) (k l : Fin W.rank × Fin V.rank),
      GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.commScalar V W τ τ (α • unitMap B B' k.1 k.2) (β • unitMap B B' l.1 l.2) =
        -(2 * Real.pi * Complex.I) * (((2 * (tauE D τ D.host.xi0 * (α * ((starRingEnd ℂ) β *
          (if k = l then ((ε' k.1 * ε k.2 : ℝ) : ℂ) else 0)))).re : ℝ)) : ℂ) := by
    intro α β k l
    unfold GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.commScalar GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt
    rw [if_pos rfl, htr]
  have kap0 : ∀ (α β : ℂ) (k l : Fin W.rank × Fin V.rank), k ≠ l →
      GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.commScalar V W τ τ (α • unitMap B B' k.1 k.2) (β • unitMap B B' l.1 l.2) = 0 := by
    intro α β k l hkl
    rw [kap, if_neg hkl]
    simp
  have kapI : ∀ k : Fin W.rank × Fin V.rank,
      GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.commScalar V W τ τ (unitMap B B' k.1 k.2) ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) =
        -(4 * Real.pi * Complex.I) * ((tauE D τ D.host.xi0).im : ℂ) := by
    intro k
    have e := kap 1 (Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) k k
    rw [one_smul] at e
    rw [e, if_pos rfl]
    have h2 : (tauE D τ D.host.xi0 * (1 * ((starRingEnd ℂ) (Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) * ((ε' k.1 * ε k.2 : ℝ) : ℂ)))).re =
        (tauE D τ D.host.xi0).im := by
      have e2 : (1 : ℂ) * ((starRingEnd ℂ) (Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) =
          -Complex.I * (((ε' k.1 * ε k.2) * (ε' k.1 * ε k.2) : ℝ) : ℂ) := by
        rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
        push_cast
        ring
      rw [e2, hσ k]
      simp [Complex.mul_re]
    rw [h2]
    push_cast
    ring
  have hA : ∀ (k : Fin W.rank × Fin V.rank) h, Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) h = (fockScale D τ : ℂ)⁻¹ • Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (unitMap B B' k.1 k.2) h + (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) • Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) h := by
    intro k h
    unfold Formalism.IndefR.Datum.aPlus Formalism.IndefR.Datum.crea
    rw [hJ k]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hBo : ∀ (k : Fin W.rank × Fin V.rank) h, ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) h) = (-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (unitMap B B' k.1 k.2) h + (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) • Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) h := by
    intro k h
    unfold Formalism.IndefR.Datum.annih
    rw [hJ k]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have Ath : ∀ (k : Fin W.rank × Fin V.rank) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g) := by
    intro k g hg
    rw [hA]
    exact GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (Dth _ _ hg)) (GlobalTheory.OrientedHeis.theta_smul _ (Dth _ _ hg))
  have Bth : ∀ (k : Fin W.rank × Fin V.rank) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g) := by
    intro k g hg
    rw [hBo]
    exact GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (Dth _ _ hg)) (GlobalTheory.OrientedHeis.theta_smul _ (Dth _ _ hg))
  have Aadd : ∀ (k : Fin W.rank × Fin V.rank) g h, IsThetaFunO ψ V W g → IsThetaFunO ψ V W h → Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) (g + h) = Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g + Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) h := by
    intro k g h hg hh
    simp only [hA]
    rw [GlobalTheory.Size.dRho_add hψ hθ τ _ hg hh, GlobalTheory.Size.dRho_add hψ hθ τ _ hg hh]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have Badd : ∀ (k : Fin W.rank × Fin V.rank) g h, IsThetaFunO ψ V W g → IsThetaFunO ψ V W h → ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) (g + h)) = ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g) + ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) h) := by
    intro k g h hg hh
    simp only [hBo]
    rw [GlobalTheory.Size.dRho_add hψ hθ τ _ hg hh, GlobalTheory.Size.dRho_add hψ hθ τ _ hg hh]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have Asmul : ∀ (k : Fin W.rank × Fin V.rank) (c : ℂ) g, Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) (c • g) = c • Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g := by
    intro k c g
    simp only [hA]
    rw [GlobalTheory.Size.dRho_smul, GlobalTheory.Size.dRho_smul]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have Bsmul : ∀ (k : Fin W.rank × Fin V.rank) (c : ℂ) g, ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) (c • g)) = c • ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g) := by
    intro k c g
    simp only [hBo]
    rw [GlobalTheory.Size.dRho_smul, GlobalTheory.Size.dRho_smul]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have ccr1 : ∀ (k l : Fin W.rank × Fin V.rank) g, IsThetaFunO ψ V W g → Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) (Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' l.1 l.2) g) = Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' l.1 l.2) (Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g) := by
    intro k l g hg
    by_cases hkl : k = l
    · rw [hkl]
    · have L := fun z z1 z2 (α β : ℂ) => Dlin z α β (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z1 g) (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z2 g) (Dth z1 g hg) (Dth z2 g hg)
      simp only [hA, L]
      funext x
      have k1 := kap0 1 1 k l hkl
      rw [one_smul, one_smul] at k1
      have k2 := kap0 1 (Complex.I * ((ε' l.1 * ε l.2 : ℝ) : ℂ)) k l hkl
      rw [one_smul] at k2
      have k3 := kap0 (Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) 1 k l hkl
      rw [one_smul] at k3
      have k4 := kap0 (Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) (Complex.I * ((ε' l.1 * ε l.2 : ℝ) : ℂ)) k l hkl
      have e1 := Cm (unitMap B B' k.1 k.2) (unitMap B B' l.1 l.2) g hg x
      have e2 := Cm (unitMap B B' k.1 k.2) ((Complex.I * ((ε' l.1 * ε l.2 : ℝ) : ℂ)) • unitMap B B' l.1 l.2) g hg x
      have e3 := Cm ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) (unitMap B B' l.1 l.2) g hg x
      have e4 := Cm ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) ((Complex.I * ((ε' l.1 * ε l.2 : ℝ) : ℂ)) • unitMap B B' l.1 l.2) g hg x
      rw [k1] at e1
      rw [k2] at e2
      rw [k3] at e3
      rw [k4] at e4
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ)⁻¹ * e1 + (fockScale D τ : ℂ)⁻¹ * (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * e2 + (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * (fockScale D τ : ℂ)⁻¹ * e3 + (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * e4
  have ccr2 : ∀ (k l : Fin W.rank × Fin V.rank) g, IsThetaFunO ψ V W g →
      ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) (Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' l.1 l.2) g)) = Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' l.1 l.2) ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g) + (@ite ℂ (k = l) (Classical.propDecidable (k = l)) 1 0) • g := by
    intro k l g hg
    have L := fun z z1 z2 (α β : ℂ) => Dlin z α β (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z1 g) (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z2 g) (Dth z1 g hg) (Dth z2 g hg)
    simp only [hA, hBo, L]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl]
      funext x
      have e2 := Cm (unitMap B B' k.1 k.2) ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) g hg x
      rw [kapI k] at e2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination ((-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * (-(fockScale D τ : ℂ)⁻¹ - (fockScale D τ : ℂ)⁻¹)) * e2 + (g x) * hcinv +
        (-(8 * Real.pi) * (fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ)⁻¹ * ((tauE D τ D.host.xi0).im : ℂ) * g x) * Complex.I_mul_I
    · rw [if_neg hkl]
      funext x
      have k1 := kap0 1 1 k l hkl
      rw [one_smul, one_smul] at k1
      have k2 := kap0 1 (Complex.I * ((ε' l.1 * ε l.2 : ℝ) : ℂ)) k l hkl
      rw [one_smul] at k2
      have k3 := kap0 (Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) 1 k l hkl
      rw [one_smul] at k3
      have k4 := kap0 (Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) (Complex.I * ((ε' l.1 * ε l.2 : ℝ) : ℂ)) k l hkl
      have e1 := Cm (unitMap B B' k.1 k.2) (unitMap B B' l.1 l.2) g hg x
      have e2 := Cm (unitMap B B' k.1 k.2) ((Complex.I * ((ε' l.1 * ε l.2 : ℝ) : ℂ)) • unitMap B B' l.1 l.2) g hg x
      have e3 := Cm ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) (unitMap B B' l.1 l.2) g hg x
      have e4 := Cm ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) ((Complex.I * ((ε' l.1 * ε l.2 : ℝ) : ℂ)) • unitMap B B' l.1 l.2) g hg x
      rw [k1] at e1
      rw [k2] at e2
      rw [k3] at e3
      rw [k4] at e4
      simp only [ Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(fockScale D τ : ℂ)⁻¹) * (fockScale D τ : ℂ)⁻¹ * e1 + (-(fockScale D τ : ℂ)⁻¹) * (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * e2 + (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * (fockScale D τ : ℂ)⁻¹ * e3 + (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * e4
  have hex : ∀ T : (WO V W → ℂ) → (WO V W → ℂ), (∀ g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (T g)) →
      (∀ g h, IsThetaFunO ψ V W g → IsThetaFunO ψ V W h → T (g + h) = T g + T h) → (∀ (c : ℂ) g, T (c • g) = c • T g) →
      ∃ e : Module.End ℂ (GlobalTheory.VacuumFockLaws.thetaSub V W ψ), ∀ g : GlobalTheory.VacuumFockLaws.thetaSub V W ψ, (e g : WO V W → ℂ) = T g :=
    fun T h1 h2 h3 => exists_end_coe_eq_of_linear_on_submodule _ T (fun g hg => h1 g hg) (fun g hg h hh => h2 g h hg hh) (fun c g _ => h3 c g)
  choose a ha using fun k : Fin W.rank × Fin V.rank => hex (fun g => Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g) (Ath k) (Aadd k) (Asmul k)
  choose b hb using fun k : Fin W.rank × Fin V.rank => hex (fun g => ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g)) (Bth k) (Badd k) (Bsmul k)
  have ha' : ∀ (k : Fin W.rank × Fin V.rank) (g : GlobalTheory.VacuumFockLaws.thetaSub V W ψ), (a k g : WO V W → ℂ) = Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) (g : WO V W → ℂ) := fun k g => ha k g
  have hb' : ∀ (k : Fin W.rank × Fin V.rank) (g : GlobalTheory.VacuumFockLaws.thetaSub V W ψ), (b k g : WO V W → ℂ) = ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) (g : WO V W → ℂ)) := fun k g => hb k g
  have haa : ∀ i j (g : GlobalTheory.VacuumFockLaws.thetaSub V W ψ), a i (a j g) = a j (a i g) := by
    intro i j g
    apply Subtype.ext
    simp only [ha']
    exact ccr1 i j g g.2
  have hba : ∀ i j (g : GlobalTheory.VacuumFockLaws.thetaSub V W ψ), b i (a j g) = a j (b i g) + (@ite ℂ (i = j) (Classical.propDecidable (i = j)) 1 0) • g := by
    intro i j g
    apply Subtype.ext
    simp only [ha', hb', Submodule.coe_add, Submodule.coe_smul]
    exact ccr2 i j g g.2
  have hv : ∀ z, Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') z f = 0 := hvac
  have hfb : ∀ i, b i ⟨f, hf⟩ = 0 := by
    intro i
    apply Subtype.ext
    rw [hb']
    simp [hv]
  have R := GlobalTheory.VacuumFockLaws.fock_of_ccr (ι := Fin W.rank × Fin V.rank) (X := WO V W) (GlobalTheory.VacuumFockLaws.thetaSub V W ψ) (fun (k : Fin W.rank × Fin V.rank) (h : WO V W → ℂ) => Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) h) a b
    (fun k g => (ha' k g).symm) haa hba ⟨f, hf⟩ hfb
  have thP : ∀ P, IsThetaFunO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f P) := fun P => R.1 P
  have IPkey : ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratL W V) 𝓕 μ → ∀ (β : Fin W.rank × Fin V.rank →₀ ℕ)
        (Q : MvPolynomial (Fin W.rank × Fin V.rank) ℂ),
        ipO μ 𝓕 (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f Q) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f (MvPolynomial.monomial β 1)) = Q.coeff β * ((multiFact β : ℂ) * ipO μ 𝓕 f f) := by
    intro μ 𝓕 hμ h𝓕
    have ipL : ∀ (α β : ℂ) F G H, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → IsThetaFunO ψ V W H →
        ipO μ 𝓕 (α • F + β • G) H = α * ipO μ 𝓕 F H + β * ipO μ 𝓕 G H := by
      intro α β F G H hF hG hH
      rw [GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 (GlobalTheory.OrientedHeis.theta_smul α hF) (GlobalTheory.OrientedHeis.theta_smul β hG) hH,
        GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_left]
    have ipR : ∀ (α β : ℂ) F G H, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → IsThetaFunO ψ V W H →
        ipO μ 𝓕 H (α • F + β • G) = (starRingEnd ℂ) α * ipO μ 𝓕 H F + (starRingEnd ℂ) β * ipO μ 𝓕 H G := by
      intro α β F G H hF hG hH
      rw [GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 hH (GlobalTheory.OrientedHeis.theta_smul α hF) (GlobalTheory.OrientedHeis.theta_smul β hG),
        GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_right]
    have sk : ∀ z F H, IsThetaFunO ψ V W F → IsThetaFunO ψ V W H → ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z F) H = -ipO μ 𝓕 F (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z H) :=
      fun z F H hF hH => (hsk τ z).2.2 μ 𝓕 hμ h𝓕 F H hF hH
    apply R.2 (ipO μ 𝓕)
    · intro x y z
      exact GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 x.2 y.2 z.2
    · intro c x z
      exact GlobalTheory.Size.ipO_smul_left (μ := μ) (𝓕 := 𝓕) c x z
    · intro x
      have e := GlobalTheory.Size.ipO_smul_right (μ := μ) (𝓕 := 𝓕) (0 : ℂ) x 0
      simpa using e
    · intro i x y
      have hx : IsThetaFunO ψ V W (x : WO V W → ℂ) := x.2
      have hy : IsThetaFunO ψ V W (y : WO V W → ℂ) := y.2
      simp only [ha', hb', hA, hBo]
      rw [ipL _ _ _ _ _ (Dth _ _ hx) (Dth _ _ hx) hy, ipR _ _ _ _ _ (Dth _ _ hy) (Dth _ _ hy) hx,
        sk _ _ _ hx hy, sk _ _ _ hx hy, map_neg, hconj, hconjE]
      ring
    · intro i x y
      have hx : IsThetaFunO ψ V W (x : WO V W → ℂ) := x.2
      have hy : IsThetaFunO ψ V W (y : WO V W → ℂ) := y.2
      simp only [ha', hb', hA, hBo]
      rw [ipR _ _ _ _ _ (Dth _ _ hy) (Dth _ _ hy) hx, ipL _ _ _ _ _ (Dth _ _ hx) (Dth _ _ hx) hy,
        sk _ _ _ hx hy, sk _ _ _ hx hy, hconj, hconjE]
      ring
  refine ⟨thP, fun hne => ?_, fun μ 𝓕 hμ h𝓕 P Q => ?_⟩
  · intro P Q hPQ
    obtain ⟨μ, 𝓕, hcov⟩ := GlobalTheory.Size.exists_isCovolOne (D := D) V W
    obtain ⟨hμ, h𝓕, -⟩ := hcov
    have key := IPkey μ 𝓕 hμ h𝓕
    have hff : ipO μ 𝓕 f f ≠ 0 := fun h0 => hne ((GlobalTheory.Size.ipO_self_eq_zero_iff hψ hμ h𝓕 hf).mp h0)
    ext β
    have e1 := key β P
    have e2 := key β Q
    rw [hPQ] at e1
    have hm : (multiFact β : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      unfold multiFact
      rw [Finsupp.prod]
      exact Finset.prod_ne_zero_iff.mpr fun a _ => Nat.factorial_ne_zero _
    exact mul_right_cancel₀ (mul_ne_zero hm hff) (e1.symm.trans e2)
  · have key := IPkey μ 𝓕 hμ h𝓕
    have lin : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f Q = ∑ β ∈ Q.support, Q.coeff β • GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f (MvPolynomial.monomial β 1) := by
      conv_lhs => rw [Q.as_sum]
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt Formalism.IndefR.Datum.pureTensorL
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro β _
      rw [← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have thsum : ∀ (t : Finset (Fin W.rank × Fin V.rank →₀ ℕ)) (cf : (Fin W.rank × Fin V.rank →₀ ℕ) → ℂ),
        IsThetaFunO ψ V W (∑ β ∈ t, cf β • GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f (MvPolynomial.monomial β 1)) := by
      intro t cf
      refine Finset.induction_on t ?_ ?_
      · rw [Finset.sum_empty]
        exact GlobalTheory.OrientedHeis.theta_zero
      · intro β t hβ ih
        rw [Finset.sum_insert hβ]
        exact GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (thP _)) ih
    have ipRs : ∀ (t : Finset (Fin W.rank × Fin V.rank →₀ ℕ)) (cf : (Fin W.rank × Fin V.rank →₀ ℕ) → ℂ),
        ipO μ 𝓕 (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f P) (∑ β ∈ t, cf β • GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f (MvPolynomial.monomial β 1)) =
          ∑ β ∈ t, (starRingEnd ℂ) (cf β) * ipO μ 𝓕 (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f P) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f (MvPolynomial.monomial β 1)) := by
      intro t cf
      refine Finset.induction_on t ?_ ?_
      · rw [Finset.sum_empty, Finset.sum_empty]
        have e := GlobalTheory.Size.ipO_smul_right (μ := μ) (𝓕 := 𝓕) (0 : ℂ) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f P) 0
        simpa using e
      · intro β t hβ ih
        rw [Finset.sum_insert hβ, Finset.sum_insert hβ,
          GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 (thP P) (GlobalTheory.OrientedHeis.theta_smul _ (thP _)) (thsum t cf),
          GlobalTheory.Size.ipO_smul_right, ih]
    rw [lin, ipRs, fockIp_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    rw [key β P]
    ring

variable {D : D7} {V W : HSp D}

theorem laws {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (τ : D.what₂.Tau) {s B : Mn V.rank} {s' B' : Mn W.rank} {ε : Fin V.rank → ℝ} {ε' : Fin W.rank → ℝ}
    (hε : ∀ a, ε a = 1 ∨ ε a = -1) (hε' : ∀ a, ε' a = 1 ∨ ε' a = -1) (hB : IsUnit B.det)
    (hs : s * B = B * diagonal fun a => (ε a : ℂ)) (hs' : s' * B' = B' * diagonal fun a => (ε' a : ℂ))
    (hG : Bᴴ * gramAt D V τ * B = diagonal fun a => (ε a : ℂ))
    (hG' : B'ᴴ * gramAt D W τ * B' = diagonal fun a => (ε' a : ℂ)) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hvac : IsFockVacAt (heisO ψ V W) θ τ (cplxO s s') f) :
    (∀ P, IsThetaFunO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f P)) ∧
      (f ≠ 0 → Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f)) ∧
      ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
        ∀ P Q, ipO μ 𝓕 (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f P) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f Q) =
          ipO μ 𝓕 f f * fockIp P Q :=
  laws_lemma_7 hψ hθ τ hε hε' hB hs hs' hG hG' hf hvac

end Laws

section Main

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

theorem fock_at_one_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → (∀ P, IsThetaFunO ψ S T (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f P)) ∧ (f ≠ 0 → Function.Injective (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ N, Fischer (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f) (ipTh μ 𝓕) (LinearEquiv.refl ℂ _) N) := by
  intro D ψ θ S T τ hψ hθ sS frS εS sT frT εT hS hT f hf hvac
  obtain ⟨hdS, hsS, hGS⟩ := frame_inv hS
  obtain ⟨hdT, hsT, hGT⟩ := frame_inv hT
  have L := laws (D := D) (V := S) (W := T) hψ hθ τ (ε := fun a => sgn εS a) (ε' := fun a => sgn εT a)
    (fun a => sgn_cases εS a) (fun a => sgn_cases εT a) hdS hsS hsT hGS hGT hf hvac
  refine ⟨L.1, fun hne => ⟨L.2.1 hne, ?_⟩⟩
  intro μ 𝓕 hμ h𝓕
  have hne0 : GlobalTheory.Ker.ipO μ 𝓕 f f ≠ 0 := fun h0 =>
    hne ((GlobalTheory.Size.ipO_self_eq_zero_iff hψ hμ h𝓕 hf).mp h0)
  have hre : GlobalTheory.Ker.ipO μ 𝓕 f f = (((GlobalTheory.Ker.ipO μ 𝓕 f f).re : ℝ) : ℂ) := by
    have hc : (starRingEnd ℂ) (GlobalTheory.Ker.ipO μ 𝓕 f f) = GlobalTheory.Ker.ipO μ 𝓕 f f :=
      GlobalTheory.Size.ipO_conj (μ := μ) (𝓕 := 𝓕) f f
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · have him := congrArg Complex.im hc
      rw [Complex.conj_im] at him
      simp only [Complex.ofReal_im]
      linarith
  have hnn : 0 ≤ (GlobalTheory.Ker.ipO μ 𝓕 f f).re := by
    have hI := GlobalTheory.Size.integrableOn_mul_conj hψ hμ h𝓕 hf hf
    unfold GlobalTheory.Ker.ipO
    have key : (∫ w in 𝓕, f w * (starRingEnd ℂ) (f w) ∂μ).re =
        ∫ w in 𝓕, (f w * (starRingEnd ℂ) (f w)).re ∂μ := (integral_re hI).symm
    rw [key]
    exact MeasureTheory.integral_nonneg fun w => by
      simp only [Complex.mul_conj, Complex.ofReal_re]
      exact Complex.normSq_nonneg _
  have hpos : 0 < (GlobalTheory.Ker.ipO μ 𝓕 f f).re := by
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [hre, ← h, Complex.ofReal_zero]) hne0
  refine ⟨(GlobalTheory.Ker.ipO μ 𝓕 f f).re, ?_⟩
  unfold GlobalTheory.ArchRec.Fischer
  refine ⟨hpos, fun P Q => ?_⟩
  rw [LinearEquiv.refl_apply, LinearEquiv.refl_apply, ← hre, ← L.2.2 μ 𝓕 hμ h𝓕 P Q]
  rfl

end Main

end GlobalTheory.OnePlaceFock

end
