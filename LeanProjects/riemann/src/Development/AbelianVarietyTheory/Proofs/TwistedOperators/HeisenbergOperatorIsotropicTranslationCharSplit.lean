import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.HeisFlip

theorem schr_schr {K : Type} [CommRing K] [Invertible (2 : K)] (ψ' : AddChar K ℂ) {κ : Type} [Fintype κ]
    (a b : (κ → K) × (κ → K)) (φ : (κ → K) → ℂ) (h : ψ' (⅟(2 : K) * (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)) = 1) :
    GlobalTheory.WeilM.schr ψ' a (GlobalTheory.WeilM.schr ψ' b φ) = GlobalTheory.WeilM.schr ψ' (a + b) φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr]
  have h2 : (⅟(2 : K)) * 2 = 1 := invOf_mul_self 2
  have e : (x ⬝ᵥ a.2 + ⅟(2 : K) * (a.1 ⬝ᵥ a.2)) + ((x + a.1) ⬝ᵥ b.2 + ⅟(2 : K) * (b.1 ⬝ᵥ b.2)) =
      (x ⬝ᵥ (a + b).2 + ⅟(2 : K) * ((a + b).1 ⬝ᵥ (a + b).2)) + ⅟(2 : K) * (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2) := by
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    linear_combination (-(a.1 ⬝ᵥ b.2)) * h2
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, e, AddChar.map_add_eq_mul, h, mul_one, Prod.fst_add, add_assoc]

theorem pairM_eq_trace {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (X Y : Matrix A C k) :
    pairM X Y = (X * Yᵀ).trace := by
  simp [pairM, Matrix.trace, Matrix.mul_apply]

theorem pairM_comm {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (X Y : Matrix A C k) :
    pairM X Y = pairM Y X := by
  unfold pairM
  simp only [mul_comm]

theorem pairM_mul {k A C : Type} [CommRing k] [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]
    (P : Matrix A A k) (Q : Matrix A C k) (R : Matrix C C k) (S : Matrix A C k) :
    pairM (P * Q * R) S = pairM Q (Pᵀ * S * Rᵀ) := by
  rw [pairM_eq_trace, pairM_eq_trace, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem pairM_smul_left {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (s : k) (X Y : Matrix A C k) :
    pairM (s • X) Y = s * pairM X Y := by
  simp only [pairM, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem pairM_neg_left {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (X Y : Matrix A C k) :
    pairM (-X) Y = -pairM X Y := by
  simp only [pairM, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]

end GlobalTheory.HeisFlip

namespace GlobalTheory.HeisFlip

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE cA incM)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_neg_hTens {σ : E →ₐ[F] E} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E)
    (JB : Matrix (Fin n) (Fin n) E) (x u : Matrix (Fin m) (Fin n) (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) ((-1 : AE F E) * GlobalTheory.WeilM.hTens (cA σ) (incM F JA) (incM F JB) x u) := by
  intro r hr
  have h : ∀ i j, r • x i j = 0 := fun i j => by
    have := congrFun (congrFun (hx r hr) i) j
    simpa using this
  rw [← mul_smul_comm]
  unfold GlobalTheory.WeilM.hTens
  simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]

theorem symp_bar {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d)
    (hX : ∀ r s, σ (X.J s r) = X.J r s) (hY : ∀ r s, σ (Y.J s r) = -Y.J r s) (ψ : AddChar (AF F) ℂ)
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (x u : Matrix (Fin n) (Fin d) (AE F E)) (hx : At (evFin F v) x) (hx0 : x.map (piW t) = 0)
    (hu1 : u.map (piW (t.comp σ)) = 0) :
    ψ (GlobalTheory.WeilM.symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J) x u) =
      psiLoc ψ v (-pairM (coY σ X Y t b c x) (coX t b c u)) := by
  unfold GlobalTheory.WeilM.symp
  rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ (at_neg_hTens _ _ x u hx)]
  rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add,
    GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm t X.J Y.J hX hY x u hx0 hu1]
  show psiLoc ψ v _ = psiLoc ψ v _
  congr 1
  congr 1
  have e : coY σ X Y t b c x = b.1ᵀ * (-(X.J.map t * x.map (piW (t.comp σ)) * (Y.J.map t)ᵀ)) * c.1 := by
    simp only [coY, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rw [e, pairM_mul, Matrix.transpose_transpose]
  have e2 : b.1 * coX t b c u * c.1ᵀ = u.map (piW t) := by
    simp only [coX, ← Matrix.mul_assoc]
    rw [show b.1 * (b⁻¹).1 = 1 by simp, Matrix.one_mul, Matrix.mul_assoc,
      show (c⁻¹).1ᵀ * c.1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp, Matrix.mul_one]
  rw [e2]
  rfl

theorem symp_lin {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d)
    (hX : ∀ r s, σ (X.J s r) = X.J r s) (hY : ∀ r s, σ (Y.J s r) = -Y.J r s) (ψ : AddChar (AF F) ℂ)
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (x u : Matrix (Fin n) (Fin d) (AE F E)) (hx : At (evFin F v) x) (hx0 : x.map (piW (t.comp σ)) = 0)
    (hu1 : u.map (piW t) = 0) :
    ψ (GlobalTheory.WeilM.symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J) x u) =
      psiLoc ψ v (pairM (coX t b c x) (coY σ X Y t b c u)) := by
  have hss : (t.comp σ).comp σ = t := comp_conj_conj hcm t
  unfold GlobalTheory.WeilM.symp
  rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v (t.comp σ) _ (at_neg_hTens _ _ x u hx)]
  rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add,
    GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm (t.comp σ) X.J Y.J hX hY x u hx0 (by rw [hss]; exact hu1), hss]
  show psiLoc ψ v _ = psiLoc ψ v _
  congr 1
  have hA : (X.J.map (t.comp σ))ᵀ = X.J.map t := by
    ext i k
    simp only [Matrix.transpose_apply, Matrix.map_apply, AlgHom.comp_apply, hX]
  have hB : Y.J.map (t.comp σ) = -(Y.J.map t)ᵀ := by
    ext j l
    simp only [Matrix.map_apply, AlgHom.comp_apply, Matrix.neg_apply, Matrix.transpose_apply, hY, map_neg]
  have e1 : ∑ k, ∑ l, (-(X.J.map (t.comp σ) * x.map (piW t) * (Y.J.map (t.comp σ))ᵀ)) k l *
      u.map (piW (t.comp σ)) k l =
      -pairM (x.map (piW t)) (-(X.J.map t * u.map (piW (t.comp σ)) * (Y.J.map t)ᵀ)) := by
    change pairM _ _ = _
    rw [pairM_neg_left, pairM_mul, Matrix.transpose_transpose, hA, hB]
    simp only [Matrix.mul_neg]
  rw [e1, neg_neg]
  have e : coY σ X Y t b c u = b.1ᵀ * (-(X.J.map t * u.map (piW (t.comp σ)) * (Y.J.map t)ᵀ)) * c.1 := by
    simp only [coY, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rw [e, pairM_comm (coX t b c x), pairM_mul, Matrix.transpose_transpose, pairM_comm]
  congr 1
  simp only [coX, ← Matrix.mul_assoc]
  rw [show b.1 * (b⁻¹).1 = 1 by simp, Matrix.one_mul, Matrix.mul_assoc,
    show (c⁻¹).1ᵀ * c.1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp, Matrix.mul_one]

end GlobalTheory.HeisFlip

namespace GlobalTheory.HeisFlip

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE cA incM)

theorem heis_trans_char : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d), (∀ r s, σ (X.J s r) = X.J r s) → (∀ r s, σ (Y.J s r) = -Y.J r s) → X.J.det ≠ 0 → Y.J.det ≠ 0 → ∀ (M : Model σ X Y) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), At (evFin F v) u → pairM (coX t b c u) (coY σ X Y t b c u) = 0 →
    ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (M.co.rho ψ u) φ φ₁ →
      (∀ ι, M.IsLinW ψ t b c ι → ∀ Z, ι φ₁ Z = psiLoc ψ v (pairM Z (coY σ X Y t b c u)) * ι φ (Z + coX t b c u)) ∧
      ∀ ι, M.IsLinBar ψ t b c ι → ∀ Z, ι φ₁ Z = psiLoc ψ v (-pairM Z (coX t b c u)) * ι φ (Z + coY σ X Y t b c u) := by
  intro F E _ _ _ _ _ σ hcm n d X Y hX hY hdX hdY M ψ hψ v t b c u hu hpair φ hφ φ₁ hφ₁ hact
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin n) (Fin d) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁

  set u₁ := U (u.map (piW t)) 0 with hu₁def
  set u₂ := u - u₁ with hu₂def
  have hu₁at : At (evFin F v) u₁ := hUat _ _
  have hu₁t : u₁.map (piW t) = u.map (piW t) := hU0 _ _
  have hu₁s : u₁.map (piW (t.comp σ)) = 0 := hU1 _ _
  have hu₂at : At (evFin F v) u₂ := fun r hr => by rw [hu₂def, smul_sub, hu r hr, hu₁at r hr, sub_zero]
  have hu₂t : u₂.map (piW t) = 0 := by
    ext i j
    rw [Matrix.map_apply, hu₂def, Matrix.sub_apply, map_sub, ← Matrix.map_apply (f := piW t) (M := u₁), hu₁t,
      Matrix.map_apply, sub_self, Matrix.zero_apply]
  have hu₂s : u₂.map (piW (t.comp σ)) = u.map (piW (t.comp σ)) := by
    ext i j
    rw [Matrix.map_apply, hu₂def, Matrix.sub_apply, map_sub, ← Matrix.map_apply (f := piW (t.comp σ)) (M := u₁), hu₁s,
      Matrix.zero_apply, sub_zero, Matrix.map_apply]
  have hsum : u₁ + u₂ = u := by rw [hu₂def, add_sub_cancel]
  have hcoXu₁ : coX t b c u₁ = coX t b c u := by simp only [coX, hu₁t]
  have hcoYu₁ : coY σ X Y t b c u₁ = 0 := by simp only [coY, hu₁s, Matrix.mul_zero, Matrix.zero_mul, neg_zero]
  have hcoXu₂ : coX t b c u₂ = 0 := by simp only [coX, hu₂t, Matrix.mul_zero, Matrix.zero_mul]
  have hcoYu₂ : coY σ X Y t b c u₂ = coY σ X Y t b c u := by simp only [coY, hu₂s]

  set ψv := GlobalTheory.LatVac.psiAt ψ v with hψv
  have hsb : ∀ (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) (f : (Fin n × Fin d → Fv F v) → ℂ),
      f ∈ GlobalTheory.WeilM.SB _ → GlobalTheory.WeilM.schr ψv w f ∈ GlobalTheory.WeilM.SB _ :=
    fun w f hf => GlobalTheory.SchrSB.schr_mem_SB ψ hψ.1 v w f hf
  have hbr := fun (γ : Matrix (Fin n) (Fin d) (AE F E)) (hγ : At (evFin F v) γ) (f : (Fin n × Fin d → Fv F v) → ℂ) =>
    GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v γ hγ f
  have hφ₁eq : φ₁ = GlobalTheory.WeilM.schr ψv (GlobalTheory.LatVac.locCo M.co v u) φ :=
    GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr => (hact r hr).symm.trans (hbr u hu φ r hr)

  have hat2 : At (evFin F v) ((⅟(2 : AF F)) • u₂) := fun r hr => by rw [smul_comm, hu₂at r hr, smul_zero]
  have hmap2 : ∀ τ : E →ₐ[F] Fv F v, ((⅟(2 : AF F)) • u₂).map (piW τ) =
      piW τ (algebraMap (AF F) (AE F E) (⅟(2 : AF F))) • u₂.map (piW τ) := by
    intro τ
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, Algebra.smul_def, map_mul, smul_eq_mul]
  have hz : ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J) u₂ u₁) = 1 := by
    have e := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F Y.J) (-1) (⅟(2 : AF F)) 1 u₂ u₁
    rw [one_smul, mul_one] at e
    rw [← e, symp_bar hcm X Y hX hY ψ t b c _ u₁ hat2 (by rw [hmap2, hu₂t, smul_zero]) hu₁s]
    have e2 : coY σ X Y t b c ((⅟(2 : AF F)) • u₂) =
        piW (t.comp σ) (algebraMap (AF F) (AE F E) (⅟(2 : AF F))) • coY σ X Y t b c u := by
      rw [← hcoYu₂]
      simp only [coY, hmap2, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
    rw [e2, pairM_smul_left, hcoXu₁, pairM_comm, hpair, mul_zero, neg_zero]
    show psiLoc ψ v 0 = 1
    rw [← GlobalTheory.LatVac.psiAt_apply, AddChar.map_zero_eq_one]
  have hsympAt : At (evFin F v) (GlobalTheory.WeilM.symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J) u₂ u₁) := by
    intro r hr
    unfold GlobalTheory.WeilM.symp
    rw [smul_eq_mul, ← smul_eq_mul, ← LinearMap.map_smul, at_neg_hTens (σ := σ) X.J Y.J u₂ u₁ hu₂at r hr, map_zero]
  have hphase : ψv (⅟(2 : Fv F v) * ((GlobalTheory.LatVac.locCo M.co v u₂).1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u₁).2 -
      (GlobalTheory.LatVac.locCo M.co v u₁).1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u₂).2)) = 1 := by
    have hat' : At (evFin F v) (⅟(2 : AF F) * GlobalTheory.WeilM.symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J) u₂ u₁) :=
      fun r hr => by rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul r, hsympAt r hr, mul_zero]
    rw [GlobalTheory.StdVacuum.psi_eq_psiLoc ψ v _ hat', M.co.form u₂ u₁] at hz
    rw [← hz, hψv, GlobalTheory.LatVac.psiAt_apply]
    congr 1
    simp only [map_mul, map_sub, dotProduct, map_sum, GlobalTheory.VacAny.evFin_invOf_two]
    rfl
  have hphase' : ψv (⅟(2 : Fv F v) * ((GlobalTheory.LatVac.locCo M.co v u₁).1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u₂).2 -
      (GlobalTheory.LatVac.locCo M.co v u₂).1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u₁).2)) = 1 := by
    rw [← neg_sub, mul_neg, AddChar.map_neg_eq_inv, hphase, inv_one]
  have h21 : φ₁ = GlobalTheory.WeilM.schr ψv (GlobalTheory.LatVac.locCo M.co v u₂) (GlobalTheory.WeilM.schr ψv (GlobalTheory.LatVac.locCo M.co v u₁) φ) := by
    rw [schr_schr _ _ _ _ hphase, ← map_add, add_comm, hsum, hφ₁eq]
  have h12 : φ₁ = GlobalTheory.WeilM.schr ψv (GlobalTheory.LatVac.locCo M.co v u₁) (GlobalTheory.WeilM.schr ψv (GlobalTheory.LatVac.locCo M.co v u₂) φ) := by
    rw [schr_schr _ _ _ _ hphase', ← map_add, hsum, hφ₁eq]

  have hA : IsUnit (X.J.map t).det := by
    rw [show (X.J.map t).det = (t : E →+* Fv F v) X.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdX ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  have hB : IsUnit (Y.J.map t)ᵀ.det := by
    rw [Matrix.det_transpose, show (Y.J.map t).det = (t : E →+* Fv F v) Y.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdY ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  constructor
  · intro ι hι Z
    have hL : M.IsLin ψ (piW t) (piW (t.comp σ)) (fun u => (b⁻¹).1 * u.map (piW t) * (c⁻¹).1ᵀ) ι := hι
    set φ' := GlobalTheory.WeilM.schr ψv (GlobalTheory.LatVac.locCo M.co v u₁) φ with hφ'
    have hφ'sb : φ' ∈ GlobalTheory.WeilM.SB _ := hsb _ φ hφ
    have htr := hL.trans u₁ hu₁at hu₁s φ hφ φ' hφ'sb (hbr u₁ hu₁at φ)
    set x := U (b.1 * Z * c.1ᵀ) 0 with hxdef
    have hcoX : coX t b c x = Z := by
      simp only [coX, hxdef, hU0, ← Matrix.mul_assoc]
      rw [show (b⁻¹).1 * b.1 = 1 by simp, Matrix.one_mul, Matrix.mul_assoc,
        show c.1ᵀ * (c⁻¹).1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp, Matrix.mul_one]
    have hm := hL.mult u₂ hu₂at hu₂t φ' hφ'sb _ (hsb _ _ hφ'sb) (hbr u₂ hu₂at φ') x (hUat _ _) (hU1 _ _)
    change ι _ (coX t b c x) = _ * ι φ' (coX t b c x) at hm
    rw [hcoX] at hm
    rw [h21, hm, symp_lin hcm X Y hX hY ψ t b c x u₂ (hUat _ _) (hU1 _ _) hu₂t, hcoX, hcoYu₂, htr Z]
    rw [show (b⁻¹).1 * u₁.map (piW t) * (c⁻¹).1ᵀ = coX t b c u₁ from rfl, hcoXu₁]
  · intro ι hι Z
    have hL : M.IsLin ψ (piW (t.comp σ)) (piW t)
        (fun u => -(b.1ᵀ * X.J.map t * u.map (piW (t.comp σ)) * (Y.J.map t)ᵀ * c.1)) ι := hι
    set φ' := GlobalTheory.WeilM.schr ψv (GlobalTheory.LatVac.locCo M.co v u₂) φ with hφ'
    have hφ'sb : φ' ∈ GlobalTheory.WeilM.SB _ := hsb _ φ hφ
    have htr := hL.trans u₂ hu₂at hu₂t φ hφ φ' hφ'sb (hbr u₂ hu₂at φ)
    set x := U 0 (-((X.J.map t)⁻¹ * (b⁻¹).1ᵀ * Z * (c⁻¹).1 * ((Y.J.map t)ᵀ)⁻¹)) with hxdef
    have hcoY : coY σ X Y t b c x = Z := by
      simp only [coY, hxdef, hU1, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ hA, Matrix.nonsing_inv_mul_cancel_left _ _ hB,
        ← Matrix.mul_assoc (b.1ᵀ), show b.1ᵀ * (b⁻¹).1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp, Matrix.one_mul,
        show (c⁻¹).1 * c.1 = 1 by simp, Matrix.mul_one]
    have hm := hL.mult u₁ hu₁at hu₁s φ' hφ'sb _ (hsb _ _ hφ'sb) (hbr u₁ hu₁at φ') x (hUat _ _) (hU0 _ _)
    change ι _ (coY σ X Y t b c x) = _ * ι φ' (coY σ X Y t b c x) at hm
    rw [hcoY] at hm
    rw [h12, hm, symp_bar hcm X Y hX hY ψ t b c x u₁ (hUat _ _) (hU0 _ _) hu₁s, hcoY, hcoXu₁, htr Z]
    rw [show -(b.1ᵀ * X.J.map t * u₂.map (piW (t.comp σ)) * (Y.J.map t)ᵀ * c.1) = coY σ X Y t b c u₂ from rfl, hcoYu₂]

end GlobalTheory.HeisFlip
