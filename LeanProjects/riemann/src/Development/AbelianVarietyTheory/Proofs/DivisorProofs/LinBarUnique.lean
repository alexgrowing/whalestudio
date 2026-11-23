import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbeddingAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

open GlobalTheory.WeilM GlobalTheory.LFun
open scoped GlobalTheory.VacAny

namespace GlobalTheory.LinModelUniq

theorem linBar_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ ι₀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι₀ → G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι →
      ∃ l : ℂ, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), ι φ = l • ι₀ φ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT ι₀ ι hι₀ hι
  have hcm : IsCMExt F E σ := hT.base.cm
  have hstd := hT.base.std
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  set A := G.V'.J.map B.τ₁ with hAdef
  set Bm := G.W.J.map B.τ₁ with hBdef
  have hA : IsUnit A.det := GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V'.J B.τ₁ (B.emb w).1 1 one_ne_zero (G.V'.θ w)
    (by rw [one_smul]; exact hT.geo.hV'.cartan w)
  have hBm : IsUnit Bm.det := GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.W.J B.τ₁ (B.emb w).1 Complex.I Complex.I_ne_zero
    (G.W.θ w) (hT.geo.hW.cartan w)
  have hB : IsUnit Bmᵀ.det := by rw [Matrix.det_transpose]; exact hBm
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁)) =>
    GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm B.v₁ B.τ₁ P₀ P₁
  let Pm : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁) → Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁) :=
    fun C => -(A⁻¹ * C * (Bmᵀ)⁻¹)
  let Lm : (Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁) →ₗ[Fv F B.v₁] Fv F B.v₁) →
      Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁) := fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  have hcoP : ∀ C, -(A * (U 0 (Pm C)).map (piW (B.τ₁.comp σ)) * Bmᵀ) = C := by
    intro C
    rw [hU1]
    simp only [Pm, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  have hsymp : ∀ x u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F B.v₁) x → x.map (piW B.τ₁) = 0 →
      u.map (piW (B.τ₁.comp σ)) = 0 →
      B.ψ (symp (R := AF F) (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) x u) =
        GlobalTheory.LatVac.psiAt B.ψ B.v₁
          (-(∑ k, ∑ j, (-(A * x.map (piW (B.τ₁.comp σ)) * Bmᵀ)) k j * u.map (piW B.τ₁) k j)) := by
    intro x u hx hx0 hu1
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm B.v₁ B.τ₁ _ (GlobalTheory.WeilTransferW.atHTens _ _ x u hx)]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add,
      GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm B.τ₁ G.V'.J G.W.J hT.geo.hV'.herm hT.geo.hW.skew x u hx0 hu1]
    rfl
  have hbr := fun (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)) hγ (φ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) =>
    GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ B.v₁ γ hγ φ
  have hsb := fun (w : (Fin a' × Fin (a + a') → Fv F B.v₁) × (Fin a' × Fin (a + a') → Fv F B.v₁))
    (φ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB _) => GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 B.v₁ w φ hφ
  have c12 : ∀ ι' : ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁) → ℂ),
      G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι' →
      (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        ι' (schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ (U 0 (Pm C))) φ) = fun Y => ι' φ (Y + C)) ∧
      (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        ι' (schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ (U (-Lm l) 0)) φ) =
          fun Y => GlobalTheory.LatVac.psiAt B.ψ B.v₁ (l Y) * ι' φ Y) := by
    intro ι' hι'
    have hL := hι'
    unfold Model.IsLinBar at hL
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
    have htr := hL.trans
    have hmu := hL.mult
    refine ⟨fun C φ hφ => ?_, fun l φ hφ => ?_⟩
    · funext Y
      rw [htr (U 0 (Pm C)) (hUat 0 (Pm C)) (hU0 0 (Pm C)) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat 0 (Pm C)) φ) Y, hcoP]
    · funext Y
      have hm := hmu (U (-Lm l) 0) (hUat (-Lm l) 0) (hU1 (-Lm l) 0) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat (-Lm l) 0) φ)
        (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))
      rw [hcoP] at hm
      rw [hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) (hU1 (-Lm l) 0), hcoP, hU0, GlobalTheory.WeilTransferW.sumLinForm l Y]
      congr 2
      simp [Lm, Finset.sum_neg_distrib]
  obtain ⟨c1₀, c2₀⟩ := c12 ι₀ hι₀
  obtain ⟨c1, c2⟩ := c12 ι hι
  obtain ⟨l, hl⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁)) (GlobalTheory.LatVac.psiAt B.ψ B.v₁)
    (GlobalTheory.SchrSB.continuous_psiAt B.ψ hstd.1 B.v₁) (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hstd B.v₁) ι₀ ι hι₀.bij
    (fun x _ y _ c => by rw [map_add, map_smul])
    (fun C => schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ (U 0 (Pm C))))
    (fun l => schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ (U (-Lm l) 0)))
    (fun C x hx => ⟨hsb _ x hx, c1₀ C x hx, c1 C x hx⟩)
    (fun l x hx => ⟨hsb _ x hx, c2₀ l x hx, c2 l x hx⟩)
  exact ⟨l, hl⟩

end GlobalTheory.LinModelUniq
