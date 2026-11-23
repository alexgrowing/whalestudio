import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {σ : Type*}

instance isPrime_ker_eval_point (w : σ → ℂ) : (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)).IsPrime :=
  RingHom.ker_isPrime _

def pointLocalRing (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) : Type _ :=
  Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) ⧸
    I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))))

instance (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) : CommRing (pointLocalRing I w) :=
  inferInstanceAs (CommRing (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) ⧸
    I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))))))

instance (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) : Algebra (MvPolynomial σ ℂ) (pointLocalRing I w) :=
  inferInstanceAs (Algebra (MvPolynomial σ ℂ) (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) ⧸
    I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))))))

theorem isUnit_algebraMap_pointLocalRing (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (f : MvPolynomial σ ℂ)
    (hf : eval w f ≠ 0) : IsUnit (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) f) := by
  have hu : IsUnit (algebraMap (MvPolynomial σ ℂ)
      (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))) f) :=
    IsLocalization.map_units _
      (⟨f, fun h ↦ hf (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)).primeCompl)
  exact hu.map (Ideal.Quotient.mk _)

theorem pointLocalRing_nontrivial (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ)
    (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) : Nontrivial (pointLocalRing I w) := by
  unfold pointLocalRing
  rw [Ideal.Quotient.nontrivial_iff]
  intro htop
  have hle : I.map (algebraMap (MvPolynomial σ ℂ)
      (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)))) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))) := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ g).2 (RingHom.mem_ker.2 (hw g hg))
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (htop ▸ hle))

theorem pointLocalRing_subsingleton (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ)
    (hw : w ∉ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) : Subsingleton (pointLocalRing I w) := by
  simp only [IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn, Set.mem_ofPred_eq, not_forall] at hw
  obtain ⟨g, hg, hgw⟩ := hw
  unfold pointLocalRing
  rw [Ideal.Quotient.subsingleton_iff]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hg)
    (IsLocalization.map_units _
      (⟨g, fun h ↦ hgw (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)).primeCompl))

def NormalModelPlace.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal → IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q →
      ∃ P : MaximalSpectrum (curveNormalisation J q), ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation J q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f))) =
          Ring.ord (pointLocalRing M.ideal w)
            (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (pointLocalRing M.ideal w) (rename Sum.inl f))

theorem NormalModelPlace.hypotheses_inhabited :
    (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)).IsPrime ∧
      (fun _ ↦ 0 : Fin 1 ⊕ Fin IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalModel.m → ℂ) ∈
        IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalModel.ideal ∧
      IndefiniteRowSideFullHecke.ComplexSets.firstCoords (fun _ ↦ 0 : Fin 1 ⊕ Fin IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalModel.m → ℂ) = 0 :=
  ⟨Ideal.isPrime_bot, IndefiniteRowSideFullHecke.ComplexSets.const_mem_zeroSetIn_lineDiagonal 0, rfl⟩

theorem NormalModelPlace.pointLocalRing_inhabitant_nontrivial :
    Nontrivial (pointLocalRing IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalModel.ideal
      (fun _ ↦ 0 : Fin 1 ⊕ Fin IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalModel.m → ℂ)) :=
  pointLocalRing_nontrivial _ _ NormalModelPlace.hypotheses_inhabited.2.1

end

end GroundTheory.Heights₂.Heights
