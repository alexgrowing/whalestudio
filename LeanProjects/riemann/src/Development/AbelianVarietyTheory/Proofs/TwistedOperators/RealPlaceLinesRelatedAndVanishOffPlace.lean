import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalDarboux
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchrodingerThetaDatumAddAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanPreimageRealPlaceLineStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergDerivativeArchimedeanDirectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.PlaceLines

variable {D : D7}

theorem cart_herm {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) :
    (A.cart τ)ᴴ * gramAt D V τ = gramAt D V τ * A.cart τ := by
  have hJ : (Formalism.REAL.Jm (A.ε τ))ᴴ = Formalism.REAL.Jm (A.ε τ) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1; funext a; by_cases h : A.ε τ a = true <;> simp [h]
  have hJJ : Formalism.REAL.Jm (A.ε τ) * Formalism.REAL.Jm (A.ε τ) = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> norm_num
  have hdet : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  have h1 : A.fr τ * (A.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h2 : ((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have k1 : ∀ M : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((A.fr τ)⁻¹)ᴴ * ((A.fr τ)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have k2 : ∀ M : Matrix (Fin V.rank) (Fin V.rank) ℂ, A.fr τ * ((A.fr τ)⁻¹ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have k3 : ∀ M : Matrix (Fin V.rank) (Fin V.rank) ℂ, Formalism.REAL.Jm (A.ε τ) * (Formalism.REAL.Jm (A.ε τ) * M) = M :=
    fun M => by rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  rw [← A.fr_gram τ]
  simp only [Fr.cart, Matrix.conjTranspose_mul, hJ, Matrix.mul_assoc, k1, k2, k3]

theorem cart_herm_conj {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) :
    (A.cart τ)ᵀ * (gramAt D V τ).map (starRingEnd ℂ) = (gramAt D V τ).map (starRingEnd ℂ) * (A.cart τ).map (starRingEnd ℂ) := by
  have h := congrArg (fun M => Matrix.map M (starRingEnd ℂ)) (cart_herm A τ)
  simp only [Matrix.map_mul] at h
  rw [← h]
  congr 1
  ext i j
  simp [Matrix.conjTranspose_apply]

theorem cart_frSgn' (ε : Bool) {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) :
    (frSgn ε A).cart τ = (if ε then -1 else 1 : ℂ) • A.cart τ := by
  cases ε
  · simp [Fr.cart, frSgn]
  · have h : Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) = -Formalism.REAL.Jm (A.ε τ) := by
      ext a b
      by_cases hab : a = b
      · subst hab; cases h : A.ε τ a <;> simp [Formalism.REAL.Jm, h]
      · simp [Formalism.REAL.Jm, hab]
    show (A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) * A.fr τ = _
    rw [h, Matrix.mul_neg, Matrix.neg_mul]
    simp [Fr.cart]

theorem det_ne (ε : Bool) (S : HSp D) (τ : D.what₂.Tau) :
    IsUnit (((if ε then -1 else 1 : D.host.E) • S.gram).map ((starRingEnd ℂ).comp (tauE D τ))).det := by
  have hm := RingHom.map_det ((starRingEnd ℂ).comp (tauE D τ)) ((if ε then -1 else 1 : D.host.E) • S.gram)
  simp only [RingHom.mapMatrix_apply] at hm
  rw [← hm]
  refine Ne.isUnit ?_
  rw [Ne, map_eq_zero_iff _ (RingHom.injective _), Matrix.det_smul]
  refine mul_ne_zero (pow_ne_zero _ ?_) (gram_det_ne S)
  split_ifs <;> norm_num

open Classical in

theorem read_line (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X)
    (hcS : ∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D)))
    (τ τ' : D.what₂.Tau) (φ : AE D →+* ℂ) (hφ : ∀ y, φ y = starRingEnd ℂ (θ τ' (infPart D y)))
    (z : Matrix (Fin X.rank) (Fin S.rank) ℂ) :
    ((cS.symm (lineAt θ τ z 1)).map φ)ᵀ.submatrix e id *
        (((if ε then -1 else 1 : D.host.E) • S.gram).map ((starRingEnd ℂ).comp (tauE D τ'))) =
      if τ' = τ then z.map (starRingEnd ℂ) else 0 := by
  have hy := cS.apply_symm_apply (lineAt θ τ z 1)
  rw [hcS] at hy
  have hinc : ∀ x : D.host.E, φ (inclR (AF D.host.F) x) = starRingEnd ℂ (tauE D τ' x) := by
    intro x
    rw [hφ]
    congr 1
    rw [← (hθ τ').1 x]
    congr 1
  have hR : (lineAt θ τ z 1).map φ = if τ' = τ then z.map (starRingEnd ℂ) else 0 := by
    have hL := (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z).2.2 1 τ'
    ext i j
    have h3 := congrFun (congrFun hL i) j
    simp only [compAt, Matrix.map_apply] at h3
    rw [Matrix.map_apply, hφ, h3]
    split_ifs <;> simp
  rw [← hR]
  conv_rhs => rw [← hy]
  rw [Matrix.map_mul]
  congr 1
  ext i j
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hinc]

theorem zero_off (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X)
    (hcS : ∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D)))
    (τ τ' : D.what₂.Tau) (hne : τ' ≠ τ) (φ : AE D →+* ℂ) (hφ : ∀ y, φ y = starRingEnd ℂ (θ τ' (infPart D y)))
    (z : Matrix (Fin X.rank) (Fin S.rank) ℂ) :
    (cS.symm (lineAt θ τ z 1)).map φ = 0 := by
  have h := read_line θ hθ ε S X e cS hcS τ τ' φ hφ z
  rw [if_neg hne] at h
  have h0 : ((cS.symm (lineAt θ τ z 1)).map φ)ᵀ.submatrix e id = 0 := by
    calc _ = ((cS.symm (lineAt θ τ z 1)).map φ)ᵀ.submatrix e id *
          (((if ε then -1 else 1 : D.host.E) • S.gram).map ((starRingEnd ℂ).comp (tauE D τ'))) *
          (((if ε then -1 else 1 : D.host.E) • S.gram).map ((starRingEnd ℂ).comp (tauE D τ')))⁻¹ :=
          (Matrix.mul_nonsing_inv_cancel_right _ _ (det_ne ε S τ')).symm
      _ = 0 := by rw [h, Matrix.zero_mul]
  ext i j
  have h4 := congrFun (congrFun h0 (e.symm j)) i
  simpa using h4

theorem submatrix_triple_mul_of_triangular {n d k : ℕ} (e : Fin k ≃ Fin d) (V : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin d) ℂ)
    (b : Matrix (Fin k) (Fin k) ℂ) :
    (V * U * (reindex e e b)ᵀ)ᵀ.submatrix e id = b * (Uᵀ.submatrix e id) * Vᵀ := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.mul_apply, reindex_apply, id,
    Equiv.symm_apply_apply, Finset.sum_mul]
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => ?_
  ring

open Classical in

theorem at_place (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ}
    (e : Fin X.rank ≃ Fin d) (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X)
    (hcS : ∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D)))
    (τ : D.what₂.Tau) (φ : AE D →+* ℂ) (hφ : ∀ y, φ y = starRingEnd ℂ (θ τ (infPart D y)))
    (z : Matrix (Fin X.rank) (Fin S.rank) ℂ) :
    (cS.symm (lineAt θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) 1)).map φ =
      Complex.I • ((if ε then 1 else -1 : ℂ) • A.cart τ * (cS.symm (lineAt θ τ z 1)).map φ *
        ((reindex e e (B.cart τ)).map (starRingEnd ℂ))ᵀ) := by
  set G := ((if ε then -1 else 1 : D.host.E) • S.gram).map ((starRingEnd ℂ).comp (tauE D τ)) with hGdef
  have hdet : IsUnit G.det := det_ne ε S τ
  have h1 : ((cS.symm (lineAt θ τ z 1)).map φ)ᵀ.submatrix e id * G = z.map (starRingEnd ℂ) := by
    have h := read_line θ hθ ε S X e cS hcS τ τ φ hφ z
    rw [if_pos rfl] at h
    exact h
  have h2 : ((cS.symm (lineAt θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) 1)).map φ)ᵀ.submatrix e id * G =
      (cplxO ((frSgn ε A).cart τ) (B.cart τ) z).map (starRingEnd ℂ) := by
    have h := read_line θ hθ ε S X e cS hcS τ τ φ hφ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z)
    rw [if_pos rfl] at h
    exact h
  have hP : ∀ M N : Matrix (Fin S.rank) (Fin d) ℂ, Mᵀ.submatrix e id = Nᵀ.submatrix e id → M = N := by
    intro M N h; ext i j; have h5 := congrFun (congrFun h (e.symm j)) i; simpa using h5
  have hC : ∀ M N : Matrix (Fin X.rank) (Fin S.rank) ℂ, M * G = N * G → M = N := by
    intro M N h
    rw [← Matrix.mul_nonsing_inv_cancel_right G M hdet, h, Matrix.mul_nonsing_inv_cancel_right G N hdet]
  have hG : G = (if ε then -1 else 1 : ℂ) • (gramAt D S τ).map (starRingEnd ℂ) := by
    rw [hGdef]; ext i j; cases ε <;> simp [gramAt]
  have hkey : ((if ε then 1 else -1 : ℂ) • A.cart τ)ᵀ * G =
      -(G * ((frSgn ε A).cart τ).map (starRingEnd ℂ)) := by
    rw [hG, cart_frSgn']
    have hh := cart_herm_conj A τ
    have hn : ((-1 : ℂ) • A.cart τ).map (starRingEnd ℂ) = -(A.cart τ).map (starRingEnd ℂ) := by
      ext i j; simp
    cases ε
    · simp only [Bool.false_eq_true, if_false, one_smul, neg_smul, Matrix.transpose_neg, Matrix.neg_mul, hh]
    · simp only [if_true, one_smul, hn, neg_smul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, hh]
      have hn2 : (-A.cart τ).map (starRingEnd ℂ) = -(A.cart τ).map (starRingEnd ℂ) := by ext i j; simp
      rw [hn2, Matrix.mul_neg]
  have hm : ∀ M : Matrix (Fin X.rank) (Fin S.rank) ℂ,
      (Complex.I • M).map (starRingEnd ℂ) = -(Complex.I • M.map (starRingEnd ℂ)) := fun M => by
    ext i j; simp
  have hb : (reindex e e (B.cart τ)).map (starRingEnd ℂ) = reindex e e ((B.cart τ).map (starRingEnd ℂ)) := rfl
  have hs : ∀ M : Matrix (Fin S.rank) (Fin d) ℂ,
      (Complex.I • M)ᵀ.submatrix e id = Complex.I • (Mᵀ.submatrix e id) := fun M => by ext; simp
  apply hP
  apply hC
  rw [h2, hb, hs, submatrix_triple_mul_of_triangular, Matrix.smul_mul, Matrix.mul_assoc, hkey,
    Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ G, h1, cplxO, hm, Matrix.map_mul, Matrix.map_mul, smul_neg]

theorem lines_at_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
      ∃ w, (∀ w', w' ≠ w →
          (cS.symm (lineAt θ τ z 1)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w')) = 0 ∧
          (cS.symm (lineAt θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) 1)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w')) = 0) ∧
        (cS.symm (lineAt θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) 1)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
          Complex.I • (Vs.θ w * (cS.symm (lineAt θ τ z 1)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Ws.θ w)ᵀ) := by
  intro D θ hθ ε S X A B d e Bs hBs Vs Ws r s r' s' hJ hJW hV hW hemb cS hcS τ z
  classical
  choose τf hτf hθV hθW using hemb
  have hpi : ∀ w y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w) y = starRingEnd ℂ (θ (τf w) (infPart D y)) := by
    intro w y
    have h1 : (Bs.emb w).1 = (starRingEnd ℂ).comp (tauE D (τf w)) := RingHom.ext (hτf w)
    have h2 : ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding := by
      rw [← h1]; exact (Bs.emb w).2
    have h3 : Bs.emb w = ⟨(starRingEnd ℂ).comp (tauE D (τf w)), h2⟩ := Subtype.ext h1
    rw [h3]
    exact GlobalTheory.ConjInfExp.piInf_eq θ hθ (τf w) w h2 y
  have hinj : ∀ w w', τf w = τf w' → w = w' := by
    intro w w' h
    have h1 : (Bs.emb w).1 = (starRingEnd ℂ).comp (tauE D (τf w)) := RingHom.ext (hτf w)
    have h1' : (Bs.emb w').1 = (starRingEnd ℂ).comp (tauE D (τf w')) := RingHom.ext (hτf w')
    have e1 : w.embedding = w'.embedding := by
      rw [← (Bs.emb w).2, ← (Bs.emb w').2, h1, h1', h]
    rw [← NumberField.InfinitePlace.mk_embedding w, ← NumberField.InfinitePlace.mk_embedding w', e1]
  have hz : ∀ w', τf w' ≠ τ → ∀ z₀ : Matrix (Fin X.rank) (Fin S.rank) ℂ,
      (cS.symm (lineAt θ τ z₀ 1)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w')) = 0 := fun w' hne z₀ =>
    GlobalTheory.PlaceLines.zero_off θ hθ ε S X e cS hcS τ (τf w') hne _ (hpi w') z₀
  by_cases hex : ∃ w, τf w = τ
  · obtain ⟨w, hw⟩ := hex
    refine ⟨w, fun w' hw' => ?_, ?_⟩
    · have hne : τf w' ≠ τ := fun h => hw' (hinj w' w (h.trans hw.symm))
      exact ⟨hz w' hne z, hz w' hne _⟩
    · rw [hθV w, hθW w]
      subst hw
      exact GlobalTheory.PlaceLines.at_place θ hθ ε S X A B e cS hcS (τf w) _ (hpi w) z
  · obtain ⟨w0⟩ : Nonempty (NumberField.InfinitePlace D.host.F) := inferInstance
    have hne : ∀ w', τf w' ≠ τ := fun w' h => hex ⟨w', h⟩
    refine ⟨w0, fun w' _ => ⟨hz w' (hne w') z, hz w' (hne w') _⟩, ?_⟩
    rw [hz w0 (hne w0) z, hz w0 (hne w0) _]
    simp

end GlobalTheory.PlaceLines
