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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzEqZeroOfWrongSignGaussianRelationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergLineDerivativeEqDirectionalAddPhaseStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeZeroOrEmptyEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceLinesRelatedAndVanishOffPlaceStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section
open scoped Classical

namespace GlobalTheory.GaussCancel

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem actsD_zero_of_neg {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (r s r' s' : ℕ)
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (M : Model σ X W)
    (g : SInf F (Fin n × Fin d)) (ε' : InfinitePlace F → ℤˣ)
    (hε' : ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
      (∀ w, u'.map (piInf (B.emb w)) = (((ε' w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) →
      ∀ f f' : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) g f → ActsD (evI F) (M.heisLine B.ψ u') g f' →
        f' = Complex.I • f)
    (w : InfinitePlace F) (hw : ε' w = -1) (v : Matrix (Fin n) (Fin d) (AE F E)) (h : SInf F (Fin n × Fin d))
    (hD : ActsD (evI F) (M.heisLine B.ψ v) g h) : h = 0 := by
  by_cases hκ : n = 0 ∨ d = 0
  · refine GlobalTheory.T.heisenbergDerivative_zero_or_empty_eq_zero M B.ψ g h v hD (Or.inr ?_)
    rcases hκ with hκ | hκ
    · subst hκ; exact ⟨fun p => p.1.elim0⟩
    · subst hκ; exact ⟨fun p => p.2.elim0⟩
  push_neg at hκ
  obtain ⟨u, u', hu, hu', hrel, hneg⟩ :=
    GlobalTheory.T.exists_archimedean_pair_negative_symplectic_pairing B X W r s r' s' hB hX hW (Nat.pos_of_ne_zero hκ.1) (Nat.pos_of_ne_zero hκ.2) ε' w hw
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_heisenberg_derivative_archimedean_direction M B.ψ hB.std g u hu
  obtain ⟨f', hf'⟩ := GlobalTheory.T.exists_heisenberg_derivative_archimedean_direction M B.ψ hB.std g u' hu'
  have hff := hε' u u' hu hu' hrel f f' hf hf'
  let ell : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → (Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
    fun b =>
    { toFun := fun y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ b)
      map_add' := fun x y => by simp only [add_dotProduct, map_add]
      map_smul' := fun c x => by simp only [smul_dotProduct, map_smul, smul_eq_mul, RingHom.id_apply] }
  set a₁ : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).1 i)
  set a₂ : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u').1 i)
  set b₁ : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).2 i)
  set b₂ : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u').2 i)
  have hg0 : g = 0 := by
    refine GlobalTheory.T.schwartz_eq_zero_of_wrong_sign_gaussian_relation g a₁ a₂ (ell b₁) (ell b₂) (fun y => ?_) ?_
    · have e1 := GlobalTheory.T.heisenbergLineDerivative_eq_directional_add_phase M B.ψ hB.std g f u hu hf y
      have e2 := GlobalTheory.T.heisenbergLineDerivative_eq_directional_add_phase M B.ψ hB.std g f' u' hu' hf' y
      have e3 : f' y = Complex.I * f y := by rw [hff]; rfl
      rw [e1, e2] at e3
      exact e3
    · have hform := M.co.form u u'
      have hev : evI F (GlobalTheory.WeilM.symp (cA σ) (-1) (incM F X.J) (incM F W.J) u u') = a₁ ⬝ᵥ b₂ - a₂ ⬝ᵥ b₁ := by
        let evH : AF F →+* mixedEmbedding.mixedSpace F :=
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
            (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
        have hevH : ∀ a : AF F, evI F a = evH a := fun a => rfl
        rw [hform, hevH]
        simp only [dotProduct, map_sub, map_sum, map_mul, a₁, a₂, b₁, b₂, hevH]
      rw [hev, map_sub] at hneg
      have c1 : (ell b₂) a₁ = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (a₁ ⬝ᵥ b₂) := rfl
      have c2 : (ell b₁) a₂ = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (a₂ ⬝ᵥ b₁) := rfl
      rw [c1, c2]
      exact hneg
  exact GlobalTheory.T.heisenbergDerivative_zero_or_empty_eq_zero M B.ψ g h v hD (Or.inl hg0)

end GlobalTheory.GaussCancel

theorem GlobalTheory.GaussCancel.heis_cancel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ), M.IsGauss Bs.ψ Bs.emb g →
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ) (g₁ g₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ (cS.symm (lineAt θ τ z 1))) g g₁ →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F)
            (M.heisLine Bs.ψ (cS.symm (lineAt θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) 1))) g g₁' →
          g₁ + Complex.I • g₁' = 0 := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS g φ hg hφ hvac τ z g₁ g₁' h₁ h₁'
  obtain ⟨ε', hε'⟩ := hg
  obtain ⟨w, hoff, hon⟩ :=
    GlobalTheory.T.realPlaceLines_related_and_vanish_off_place D θ hθ ε S X A B e Bs hBs Vs Ws r s r' s' hJ hJW hV hW hemb cS hcS τ z
  have hu := GlobalTheory.T.archimedean_preimage_realPlace_line D θ hθ ε S X e cS hcS τ z
  have hu' := GlobalTheory.T.archimedean_preimage_realPlace_line D θ hθ ε S X e cS hcS τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z)
  rcases Int.units_eq_one_or (ε' w) with h1 | h1
  · have key := hε' _ _ hu hu' (fun w' => by
      by_cases hw : w' = w
      · subst hw; rw [hon, h1]; simp
      · rw [(hoff w' hw).1, (hoff w' hw).2]; simp) g₁ g₁' h₁ h₁'
    rw [key, smul_smul, Complex.I_mul_I, neg_one_smul, add_neg_cancel]
  · rw [GlobalTheory.GaussCancel.actsD_zero_of_neg Bs r s r' s' hBs hV hW M g ε' hε' w h1 _ g₁ h₁,
      GlobalTheory.GaussCancel.actsD_zero_of_neg Bs r s r' s' hBs hV hW M g ε' hε' w h1 _ g₁' h₁', smul_zero, add_zero]
