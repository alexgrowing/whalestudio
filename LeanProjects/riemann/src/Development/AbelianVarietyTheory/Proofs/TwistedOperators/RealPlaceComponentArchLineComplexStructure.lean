import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGaussEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchLineApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergOpArchimedeanSumRealPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer
noncomputable section

namespace GlobalTheory.CartanLinTransfer

variable {D : D7}

theorem phi_smul_realAd {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (a : AE D) :
    θ τ (infPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 1 • a)) = θ τ (infPart D a) := by
  rw [GlobalTheory.ArchLineSum.infPart_smul, map_mul, GlobalTheory.ArchLineSum.theta_realAd hθ, Complex.ofReal_one, one_mul]

theorem phi_incM {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : Type} (J : Matrix m n D.host.E) :
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J).map ((θ τ).comp (infPart D)) = J.map (tauE D τ) := by
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, ← (hθ τ).1]
  rfl

theorem cartH_gram {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) :
    (A.cart τ)ᴴ * gramAt D V τ = gramAt D V τ * A.cart τ := by
  have hu : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  have hJ : (Formalism.REAL.Jm (A.ε τ))ᴴ = Formalism.REAL.Jm (A.ε τ) := by
    ext a b; by_cases h : a = b
    · subst h; simp [Formalism.REAL.Jm, Matrix.conjTranspose_apply]; split_ifs <;> simp
    · simp [Formalism.REAL.Jm, Matrix.conjTranspose_apply, h, Ne.symm h]
  have hJJ : Formalism.REAL.Jm (A.ε τ) * Formalism.REAL.Jm (A.ε τ) = 1 := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext a; split_ifs <;> simp
  rw [← A.fr_gram τ, Fr.cart, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_nonsing_inv]
  have h1 : ((A.fr τ)ᴴ)⁻¹ * (A.fr τ)ᴴ = 1 := Matrix.nonsing_inv_mul _ (by rw [Matrix.det_conjTranspose]; exact hu.star)
  have h2 : A.fr τ * (A.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  calc _ = (A.fr τ)ᴴ * (Formalism.REAL.Jm (A.ε τ) * (((A.fr τ)ᴴ)⁻¹ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
        simp only [Matrix.mul_assoc]
    _ = (A.fr τ)ᴴ * (Formalism.REAL.Jm (A.ε τ) * ((A.fr τ * (A.fr τ)⁻¹) * Formalism.REAL.Jm (A.ε τ))) * A.fr τ := by
        rw [h1, h2, Matrix.mul_one, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]

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
    rw [h, Matrix.mul_neg, Matrix.neg_mul]; simp [Fr.cart]

end GlobalTheory.CartanLinTransfer

namespace GlobalTheory.CartanLinTransfer

theorem map_conj_conj {m n : Type} (M : Matrix m n ℂ) : (M.map (starRingEnd ℂ)).map (starRingEnd ℂ) = M := by
  ext i j; simp

theorem map_conj_smul {m n : Type} (c : ℂ) (M : Matrix m n ℂ) :
    (c • M).map (starRingEnd ℂ) = (starRingEnd ℂ c) • M.map (starRingEnd ℂ) := by
  ext i j; simp

theorem map_conj_transpose {m n : Type} (M : Matrix m n ℂ) : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := by
  ext i j; simp [Matrix.conjTranspose_apply]

theorem alg_step {m n k : ℕ} (e : Fin m ≃ Fin k) (Ac G : Matrix (Fin n) (Fin n) ℂ) (Bc : Matrix (Fin m) (Fin m) ℂ)
    (P P' : Matrix (Fin n) (Fin k) ℂ) (s : ℂ) (hs : starRingEnd ℂ s = s) (hAG : Acᴴ * G = G * Ac)
    (h : P'.map (starRingEnd ℂ) =
      Complex.I • ((-s) • Ac * P.map (starRingEnd ℂ) * ((Matrix.reindex e e Bc).map (starRingEnd ℂ))ᵀ)) :
    P'ᵀ.submatrix e id * (s • G) = Complex.I • (Bc * (Pᵀ.submatrix e id * (s • G)) * (s • Ac)) := by
  have h2 := congrArg (fun M => M.map (starRingEnd ℂ)) h
  simp only [map_conj_conj, map_conj_smul, Matrix.map_mul, Matrix.transpose_map, Complex.conj_I, map_neg, hs] at h2
  rw [h2]
  have hsub : (Matrix.reindex e e Bc).submatrix e e = Bc := by
    ext i j; simp [Matrix.reindex_apply]
  have hprod : ∀ K : Matrix (Fin n) (Fin n) ℂ,
      (Matrix.reindex e e Bc * (Pᵀ * K)).submatrix e id = Bc * (Pᵀ.submatrix e id * K) := by
    intro K
    rw [← Matrix.submatrix_mul_equiv (Matrix.reindex e e Bc) (Pᵀ * K) e e id, hsub]
    congr 1
  rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_smul, map_conj_transpose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.submatrix_smul, Pi.smul_apply, smul_smul]
  rw [hprod]
  simp only [Matrix.mul_assoc, hAG]
  congr 1
  ring

end GlobalTheory.CartanLinTransfer

open GlobalTheory.CartanLinTransfer in

theorem GlobalTheory.CartanLinTransfer.compAt_archLine_cplxO : ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d),
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ u u' : Matrix (Fin S.rank) (Fin d) (AE D),
      (∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
        Complex.I • (Vs.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Ws.θ w)ᵀ)) →
    ∀ τ, compAt θ τ (GlobalTheory.VacTransfer.archLine cS u' 1) =
      cplxO ((frSgn ε A).cart τ) (B.cart τ) (compAt θ τ (GlobalTheory.VacTransfer.archLine cS u 1)) := by
  intro D θ hθ ε S X A B d e Bs Vs Ws hBs cS hcS u u' hu τ
  obtain ⟨τw, hemb, hV, hW⟩ := hBs (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
  set w : InfinitePlace D.host.F := InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)) with hw
  have hembR : (Bs.emb w).1 = (starRingEnd ℂ).comp (tauE D τw) := RingHom.ext hemb
  have hτ : τw = τ := by
    apply (GlobalTheory.CMTypePlaces.places_bijective D).1
    have h2 := (Bs.emb w).2
    rw [hembR] at h2
    have h3 := congrArg InfinitePlace.mk h2
    have hc : (starRingEnd ℂ).comp ((tauE D τw).comp (algebraMap D.host.F D.host.E)) =
        ComplexEmbedding.conjugate ((tauE D τw).comp (algebraMap D.host.F D.host.E)) :=
      RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
    rw [InfinitePlace.mk_embedding, RingHom.comp_assoc, hc, InfinitePlace.mk_conjugate_eq] at h3
    exact h3
  rw [hτ] at hembR hV hW
  have hcomp : ((starRingEnd ℂ).comp (tauE D τ)).comp (algebraMap D.host.F D.host.E) = w.embedding := by
    rw [← hembR]; exact (Bs.emb w).2
  have hE : Bs.emb w = ⟨(starRingEnd ℂ).comp (tauE D τ), hcomp⟩ := Subtype.ext hembR
  have hpi : ∀ y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w) y = starRingEnd ℂ (((θ τ).comp (infPart D)) y) := by
    intro y; rw [hE]; exact GlobalTheory.ConjInfExp.piInf_eq θ hθ τ w hcomp y
  have hmap : ∀ v : Matrix (Fin S.rank) (Fin d) (AE D),
      v.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) = (v.map ((θ τ).comp (infPart D))).map (starRingEnd ℂ) := by
    intro v; ext i j; simp only [Matrix.map_apply, hpi]
  have hu1 := hu w
  rw [hmap, hmap, hV, hW] at hu1
  have hz : ∀ v : Matrix (Fin S.rank) (Fin d) (AE D), compAt θ τ (GlobalTheory.VacTransfer.archLine cS v 1) =
      (v.map ((θ τ).comp (infPart D)))ᵀ.submatrix e id * ((if ε then -1 else 1 : ℂ) • gramAt D S τ) := by
    intro v
    show (cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 1 • v)).map ((θ τ).comp (infPart D)) = _
    rw [hcS, Matrix.map_mul, phi_incM hθ]
    congr 1
    · ext i j
      simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, id,
        RingHom.comp_apply, phi_smul_realAd hθ]
    · ext i j
      cases ε <;> simp [gramAt, Matrix.smul_apply]
  have hsgn : (if ε then 1 else -1 : ℂ) = -(if ε then -1 else 1 : ℂ) := by cases ε <;> simp
  have hs : starRingEnd ℂ (if ε then -1 else 1 : ℂ) = (if ε then -1 else 1 : ℂ) := by cases ε <;> simp
  rw [hsgn] at hu1
  rw [hz, hz, cart_frSgn', cplxO]
  exact alg_step e (A.cart τ) (gramAt D S τ) (B.cart τ) _ _ _ hs (cartH_gram A τ) hu1
