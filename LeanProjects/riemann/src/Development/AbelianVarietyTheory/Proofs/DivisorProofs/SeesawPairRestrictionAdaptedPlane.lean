import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryCharacterTrivialOfSiegelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfIsSkew
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeviElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProductSchwartzAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneRestrictionPairFourth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairRestrictToSubspaceLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromColsMulBlockDiagTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairRestrictToSubspaceRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryBlockConjugateStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixWCharP

open GlobalTheory.DblCompare (extL proj_mem_adm vecMulVec_mul_transpose fromCols_vecMulVec_zero fromCols_zero_vecMulVec)
open GlobalTheory.MixWChar (exists_dbl_left boxFun_ne_zero eq_one_of_boxFun)

open scoped Classical in

theorem dblEv_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (dd₁ : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W₁.J))) (Fin n × Fin d₁ ⊕ Fin n × Fin d₁)),
        IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd → IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W₁.J) M₁.co dd₁ →
      ∀ (Ed S : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ)),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ∈ schA F (Fin n × Fin d₁ ⊕ Fin n × Fin d₁)) →
        (∀ (z : Matrix (Fin n) (Fin d₁ ⊕ Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ) = dd₁.rho B.ψ z (Ed Φ)) →
        (∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y (incV F H'.x)) 0) Φ) = Ed Φ ∧
          Ed (dd.rho B.ψ (Matrix.fromCols 0 (Matrix.vecMulVec y (incV F H'.x))) Φ) = Ed Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁ ⊕ Fin n × Fin d₁), l ∘ₗ Ed ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
        (∃ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ≠ 0) →
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), S Φ ∈ schA F (Fin n × Fin d₁ ⊕ Fin n × Fin d₁)) →
        (∀ (z : Matrix (Fin n) (Fin d₁ ⊕ Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          S (dd.rho B.ψ (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ) = dd₁.rho B.ψ z (S Φ)) →
        (∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          S (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y (incV F H'.x)) 0) Φ) = S Φ ∧
          S (dd.rho B.ψ (Matrix.fromCols 0 (Matrix.vecMulVec y (incV F H'.x))) Φ) = S Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁ ⊕ Fin n × Fin d₁), l ∘ₗ S ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
        ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), S Φ = c • Ed Φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH' hP₁ dd dd₁ hdd hdd₁
    Ed S hEd hEdH hEdI hEdA hEdne _hS hSH hSI hSA
  have hstd : IsStd B.ψ := hP.base.std
  obtain ⟨L, hiso, hrank, hL⟩ := GlobalTheory.EvZeroUniqDbl.dblLagr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH' hP₁
    dd dd₁ hdd hdd₁
  let δ : ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj 0
  have hδ : δ ∈ (adeleClass F).adm (Fin n × Fin d₁ ⊕ Fin n × Fin d₁) := GlobalTheory.EvZeroUniqDbl.proj_zero_mem_adm F _
  have hρ : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), dd.rho B.ψ u Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) :=
    fun u Φ hΦ => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd _ Φ hΦ
  have hδe : ∀ (f : (Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ) x, f x = δ (dd₁.rho B.ψ (dd₁.e.symm (x, 0)) f) :=
    fun f x => by simp [δ, Darboux.rho, schr]
  have hfix : ∀ z, (dd₁.e z).1 = 0 → ∀ f : (Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ,
      δ (dd₁.rho B.ψ z f) = δ f :=
    fun z hz f => by simp [δ, Darboux.rho, schr, hz]
  have key : ∀ T : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ),
      (∀ (z : Matrix (Fin n) (Fin d₁ ⊕ Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          T (dd.rho B.ψ (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ) = dd₁.rho B.ψ z (T Φ)) →
      (∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          T (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y (incV F H'.x)) 0) Φ) = T Φ ∧
          T (dd.rho B.ψ (Matrix.fromCols 0 (Matrix.vecMulVec y (incV F H'.x))) Φ) = T Φ) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
        (δ ∘ₗ T) (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) =
          (δ ∘ₗ T) φ := by
    intro T hH hI t w hw φ hφ
    obtain ⟨y, y', z, hz, heq⟩ := hL t w hw
    simp only [LinearMap.comp_apply]
    rw [heq, (hI y _ (hρ _ _ (hρ _ _ hφ))).1, (hI y' _ (hρ _ _ hφ)).2, hH z φ hφ, hfix z hz]
  obtain ⟨Φ₀, hΦ₀, hne⟩ := hEdne
  obtain ⟨x₀, hx₀⟩ : ∃ x, Ed Φ₀ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨c, hc⟩ := GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F B.ψ hstd (Fin n × Fin d ⊕ Fin n × Fin d) L hiso hrank (δ ∘ₗ S) (hSA δ hδ)
    (δ ∘ₗ Ed) (hEdA δ hδ) (key S hSH hSI) (key Ed hEdH hEdI)
    ⟨_, hρ ((dd₁.e.symm (x₀, 0)) * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ₀ hΦ₀, by
      simp only [LinearMap.comp_apply]
      rw [hEdH _ Φ₀ hΦ₀, ← hδe]
      exact hx₀⟩
  refine ⟨c, fun Φ hΦ => funext fun x => ?_⟩
  have h1 := hc _ (hρ ((dd₁.e.symm (x, 0)) * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ hΦ)
  simp only [LinearMap.comp_apply] at h1
  rw [hSH _ Φ hΦ, hEdH _ Φ hΦ, ← hδe, ← hδe] at h1
  simpa using h1

open GlobalTheory.DblSiegel in

theorem dblEv_siegel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (omd : UG (cA σ) (dbl (incM F W.J)) →* Module.End ℂ ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ)),
        IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
        IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d)) omd →
      ∀ (dd₁ : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W₁.J))) (Fin n × Fin d₁ ⊕ Fin n × Fin d₁))
        (omd₁ : UG (cA σ) (dbl (incM F W₁.J)) →* Module.End ℂ ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ)),
        IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W₁.J) M₁.co dd₁ →
        IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W₁.J)) dd₁ χX (diagCols (Fin d₁)) omd₁ →
      ∀ (Ed : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ)),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ∈ schA F (Fin n × Fin d₁ ⊕ Fin n × Fin d₁)) →
        (∀ (z : Matrix (Fin n) (Fin d₁ ⊕ Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ) = dd₁.rho B.ψ z (Ed Φ)) →
        (∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y (incV F H'.x)) 0) Φ) = Ed Φ ∧
          Ed (dd.rho B.ψ (Matrix.fromCols 0 (Matrix.vecMulVec y (incV F H'.x))) Φ) = Ed Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁ ⊕ Fin n × Fin d₁), l ∘ₗ Ed ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
        (∃ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ≠ 0) →
      ∀ (p₁ : UG (cA σ) (dbl (incM F W₁.J))) (t₁ : GL (Fin d₁) (AE F E)),
        (p₁.1.1 : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) * diagCols (Fin d₁) = diagCols (Fin d₁) * t₁.1 →
      ∀ g : UG (cA σ) (dbl (incM F W.J)), ((g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι) =
          Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι) * (p₁.1.1 : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (incV F H'.x) (0 : Fin d → AE F E) = Sum.elim (incV F H'.x) (0 : Fin d → AE F E) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.x) = Sum.elim (0 : Fin d → AE F E) (incV F H'.x) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (incV F H'.y) (0 : Fin d → AE F E) = Sum.elim (incV F H'.y) (0 : Fin d → AE F E) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.y) = Sum.elim (0 : Fin d → AE F E) (incV F H'.y)) →
      ∀ a : ℂ, (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed (omd g Φ) = a • omd₁ p₁ (Ed Φ)) → a = 1 := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ dd omd hdd homd dd₁ omd₁
    hdd₁ homd₁ Ed hmaps hheis hinv hadm hne p₁ t₁ hp₁ g hg a ha
  obtain ⟨hg1, hgx0, hg0x, -, -⟩ := hg
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨Φ₀, hΦ₀, hΦ₀ne⟩ := hne
  obtain ⟨l₁, hl₁adm, hl₁inv, w, hw⟩ := GlobalTheory.T.doubled_darboux_coords_compat F E σ (Fin n) (Fin d₁) (Fin n × Fin d₁) B.ψ (incM F X.J) (incM F W₁.J)
    M₁.co dd₁ hψ hdd₁ (Ed Φ₀) (hmaps Φ₀ hΦ₀) hΦ₀ne
  set Φ₁ := dd.rho B.ψ (w * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ₀ with hΦ₁def
  have hΦ₁ : Φ₁ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) := GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ _ Φ₀ hΦ₀
  have hL0 : l₁ (Ed Φ₁) ≠ 0 := by rw [hΦ₁def, hheis w Φ₀ hΦ₀]; exact hw
  obtain ⟨γ, S, S', hγ, hSS', hS'S⟩ := GlobalTheory.T.doubled_unitary_block_conjugate F E σ B hP.base d d₁ W W₁ H' i₀ i₁ r' s' r₁ s₁ hP.skew hP₁.skew hH
  have hSR := siegelRule_transport (AF F) (AE F E) (cA σ) (adeleClass F) B.ψ (-1) (Fin n) (Fin d ⊕ Fin d) (Fin n × Fin d ⊕ Fin n × Fin d)
    (Fin d) (Fin 2 ⊕ Fin d₁) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d))
    (lagCols (incV F H'.x) (incM F H'.ι)) omd homd.2.1.toIsSplitting homd.2.2 γ S S' hγ hSS' hS'S
  let T : GL (Fin 2 ⊕ Fin d₁) (AE F E) := ⟨Matrix.fromBlocks 1 0 0 t₁.1, Matrix.fromBlocks 1 0 0 (t₁⁻¹).1,
    by simp [Matrix.fromBlocks_multiply], by simp [Matrix.fromBlocks_multiply]⟩
  have hT : Matrix.GeneralLinearGroup.det T = Matrix.GeneralLinearGroup.det t₁ := by
    ext
    simp [T, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fromBlocks_zero₂₁]
  have hgA : (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *
      (Matrix.of fun r k => ![Sum.elim (incV F H'.x) (0 : Fin d → AE F E), Sum.elim (0 : Fin d → AE F E) (incV F H'.x)] k r) =
      Matrix.of fun r k => ![Sum.elim (incV F H'.x) (0 : Fin d → AE F E), Sum.elim (0 : Fin d → AE F E) (incV F H'.x)] k r := by
    ext r k
    fin_cases k
    · exact congrFun hgx0 r
    · exact congrFun hg0x r
  have hgD : (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * Matrix.fromRows (incM F H'.ι) (incM F H'.ι) =
      Matrix.fromRows (incM F H'.ι) (incM F H'.ι) * t₁.1 := by
    rw [← blk_diagCols, ← Matrix.mul_assoc, hg1, Matrix.mul_assoc]
    erw [hp₁]
    exact (Matrix.mul_assoc _ _ _).symm
  have hgT : (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * lagCols (incV F H'.x) (incM F H'.ι) =
      lagCols (incV F H'.x) (incM F H'.ι) * (T : Matrix (Fin 2 ⊕ Fin d₁) (Fin 2 ⊕ Fin d₁) (AE F E)) := by
    simp only [lagCols, T, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, hgA, hgD]
    simp
  have hL := hSR (l₁ ∘ₗ Ed) (hadm l₁ hl₁adm)
    (fun z φ hφ => inv_lagCols hH hψ dd dd₁ Ed hheis hinv hmaps l₁ hl₁inv z φ hφ) g T hgT Φ₁ hΦ₁
  have h1 := homd₁.2.2 l₁ hl₁adm hl₁inv p₁ t₁ hp₁ (Ed Φ₁) (hmaps Φ₁ hΦ₁)
  have h2 := congrArg l₁ (ha Φ₁ hΦ₁)
  rw [hT] at hL
  simp only [LinearMap.comp_apply] at hL
  rw [map_smul, smul_eq_mul, h1, hL] at h2
  have hK : (χX (Matrix.GeneralLinearGroup.det t₁) : ℂ) *
      ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t₁)) : ℝ) ^
        ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ) * l₁ (Ed Φ₁) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Circle.coe_ne_zero _) (modu_pow_ne_zero _ _ _)) hL0
  have := mul_right_cancel₀ hK (h2.symm.trans (one_mul _).symm)
  exact this

theorem dblEv_intertwine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (omd : UG (cA σ) (dbl (incM F W.J)) →* Module.End ℂ ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ)),
        IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
        IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d)) omd →
      ∀ (dd₁ : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W₁.J))) (Fin n × Fin d₁ ⊕ Fin n × Fin d₁))
        (omd₁ : UG (cA σ) (dbl (incM F W₁.J)) →* Module.End ℂ ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ)),
        IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W₁.J) M₁.co dd₁ →
        IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W₁.J)) dd₁ χX (diagCols (Fin d₁)) omd₁ →
      ∀ (Ed : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ)),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ∈ schA F (Fin n × Fin d₁ ⊕ Fin n × Fin d₁)) →
        (∀ (z : Matrix (Fin n) (Fin d₁ ⊕ Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ) = dd₁.rho B.ψ z (Ed Φ)) →
        (∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y (incV F H'.x)) 0) Φ) = Ed Φ ∧
          Ed (dd.rho B.ψ (Matrix.fromCols 0 (Matrix.vecMulVec y (incV F H'.x))) Φ) = Ed Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁ ⊕ Fin n × Fin d₁), l ∘ₗ Ed ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
        (∃ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ≠ 0) →
      ∀ (g₁ : UG (cA σ) (dbl (incM F W₁.J))) (g : UG (cA σ) (dbl (incM F W.J))),
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι) =
          Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι) * (g₁.1.1 : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) →
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (incV F H'.x) (0 : Fin d → AE F E) = Sum.elim (incV F H'.x) (0 : Fin d → AE F E) →
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.x) = Sum.elim (0 : Fin d → AE F E) (incV F H'.x) →
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (incV F H'.y) (0 : Fin d → AE F E) = Sum.elim (incV F H'.y) (0 : Fin d → AE F E) →
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.y) = Sum.elim (0 : Fin d → AE F E) (incV F H'.y) →
        ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed (omd g Φ) = omd₁ g₁ (Ed Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁
    dd omd hdd homd dd₁ omd₁ hdd₁ homd₁ Ed hEpres hEheis hEinv hEadm hEnz g₁ g hg1 hg2 hg3 hg4 hg5
  obtain ⟨ext, hextc, hext⟩ := extL F E σ B hP.base d d₁ W W₁ H' i₀ i₁ r' s' r₁ s₁ hP.skew hP₁.skew hH
  have hc := fun h₁ => (hext h₁ (ext h₁)).2 rfl
  have hsplit := homd.2.1
  have hsplit₁ := homd₁.2.1

  have hinv : ∀ h₁ : UG (cA σ) (dbl (incM F W₁.J)),
      ((h₁⁻¹).1.1 : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) * h₁.1.1 = 1 := fun h₁ =>
    Units.inv_mul h₁.1
  have hS : ∀ h₁, ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
      (omd₁ h₁⁻¹ ∘ₗ Ed ∘ₗ omd (ext h₁)) Φ = c • Ed Φ := by
    intro h₁
    obtain ⟨e1, e2, e3, e4, e5⟩ := hc h₁
    refine dblEv_unique F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ dd dd₁ hdd hdd₁
      Ed _ hEpres hEheis hEinv hEadm hEnz ?_ ?_ ?_ ?_
    · intro Φ hΦ
      exact hsplit₁.pres _ _ (hEpres _ (hsplit.pres _ _ hΦ))
    · intro z Φ hΦ
      simp only [LinearMap.comp_apply]
      rw [hsplit.impl _ _ _ hΦ]
      have ha : actB (cA σ) (ext h₁) (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) =
          (z * (h₁.1.1 : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E))ᵀ) *
            (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ := by
        simp only [actB, Matrix.mul_assoc, ← Matrix.transpose_mul]
        congr 2
      rw [ha, hEheis _ _ (hsplit.pres _ _ hΦ), hsplit₁.impl _ _ _ (hEpres _ (hsplit.pres _ _ hΦ))]
      congr 1
      simp only [actB, Matrix.mul_assoc, ← Matrix.transpose_mul]
      show z * ((h₁⁻¹).1.1 * h₁.1.1)ᵀ = z
      rw [hinv, Matrix.transpose_one, Matrix.mul_one]
    · intro y Φ hΦ
      simp only [LinearMap.comp_apply]
      rw [hsplit.impl _ _ _ hΦ, hsplit.impl _ _ _ hΦ]
      have ha : ∀ v : Fin d ⊕ Fin d → AE F E, ((ext h₁).1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ v = v →
          actB (cA σ) (ext h₁) (Matrix.vecMulVec y v) = Matrix.vecMulVec y v := fun v hv => by
        simp only [actB]
        rw [vecMulVec_mul_transpose, hv]
      rw [fromCols_vecMulVec_zero, fromCols_zero_vecMulVec, ha _ e2, ha _ e3, ← fromCols_vecMulVec_zero,
        ← fromCols_zero_vecMulVec, (hEinv y _ (hsplit.pres _ _ hΦ)).1, (hEinv y _ (hsplit.pres _ _ hΦ)).2]
      exact ⟨rfl, rfl⟩
    · intro l hl
      exact hsplit.adm _ _ (hEadm _ (hsplit₁.adm _ _ hl))

  choose c hcS using hS
  have hkey : ∀ h₁ (Φ : (Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ), Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) →
      Ed (omd (ext h₁) Φ) = c h₁ • omd₁ h₁ (Ed Φ) := by
    intro h₁ Φ hΦ
    have h1 := congrArg (omd₁ h₁) (hcS h₁ Φ hΦ)
    simp only [LinearMap.comp_apply, map_smul] at h1
    rw [← h1, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨Φ₀, hΦ₀, hne⟩ := hEnz
  have huniq : ∀ (h₁ : UG (cA σ) (dbl (incM F W₁.J))) (a b : ℂ),
      a • omd₁ h₁ (Ed Φ₀) = b • omd₁ h₁ (Ed Φ₀) → a = b := by
    intro h₁ a b hab
    have h1 := congrArg (omd₁ h₁⁻¹) hab
    simp only [map_smul] at h1
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h1
    have h2 : (a - b) • Ed Φ₀ = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hne)
  have hext_mul : ∀ a b, ext (a * b) = ext a * ext b := by
    intro a b
    obtain ⟨a1, a2, a3, a4, a5⟩ := hc a
    obtain ⟨b1, b2, b3, b4, b5⟩ := hc b
    refine ((hext (a * b) (ext a * ext b)).1 ⟨?_, ?_, ?_, ?_, ?_⟩).symm
    · show ((ext a).1.1 * (ext b).1.1) * _ = _ * ((a.1.1) * (b.1.1))
      rw [Matrix.mul_assoc, b1, ← Matrix.mul_assoc, a1, Matrix.mul_assoc]
    · show ((ext a).1.1 * (ext b).1.1) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, b2, a2]
    · show ((ext a).1.1 * (ext b).1.1) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, b3, a3]
    · show ((ext a).1.1 * (ext b).1.1) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, b4, a4]
    · show ((ext a).1.1 * (ext b).1.1) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, b5, a5]
  have hext_one : ext 1 = 1 := by
    refine ((hext 1 1).1 ⟨?_, ?_, ?_, ?_, ?_⟩).symm
    · show (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * _ = _ * 1
      rw [Matrix.one_mul, Matrix.mul_one]
    all_goals exact Matrix.one_mulVec _
  have hc_one : c 1 = 1 := by
    refine huniq 1 _ _ ?_
    rw [← hkey 1 Φ₀ hΦ₀, hext_one, map_one, map_one, Module.End.one_apply, Module.End.one_apply, one_smul]
  have hc_mul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    refine huniq (a * b) _ _ ?_
    rw [← hkey _ Φ₀ hΦ₀, hext_mul, map_mul, Module.End.mul_apply, hkey a _ (hsplit.pres _ _ hΦ₀), hkey b _ hΦ₀,
      map_smul, smul_smul, map_mul, Module.End.mul_apply]
  have hc_ne : ∀ a, c a ≠ 0 := fun a h0 => by
    have := hc_mul a a⁻¹
    rw [mul_inv_cancel, hc_one, h0, zero_mul] at this
    exact one_ne_zero this
  let cM : UG (cA σ) (dbl (incM F W₁.J)) →* ℂ := ⟨⟨c, hc_one⟩, hc_mul⟩
  let cU := cM.toHomUnits
  have hcU : ∀ a, (cU a : ℂ) = c a := fun a => rfl

  obtain ⟨x₀, hx₀⟩ : ∃ x, Ed Φ₀ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  set l : ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj x₀ with hl_def
  have hl : l ∈ (adeleClass F).adm (Fin n × Fin d₁ ⊕ Fin n × Fin d₁) := proj_mem_adm F _ x₀
  have hcont : Continuous fun a : UG (cA σ) (dbl (incM F W₁.J)) => c a := by
    rw [continuous_iff_continuousAt]
    intro a₀
    have hΦ' : omd (ext a₀⁻¹) Φ₀ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) := hsplit.pres _ _ hΦ₀
    have hfc : Continuous fun a => l (omd₁ a (Ed (omd (ext a₀⁻¹) Φ₀))) :=
      hsplit₁.cont l hl _ (hEpres _ hΦ')
    have hhc : Continuous fun a => (l ∘ₗ Ed) (omd (ext a) (omd (ext a₀⁻¹) Φ₀)) :=
      (hsplit.cont (l ∘ₗ Ed) (hEadm l hl) _ hΦ').comp hextc
    have heq : ∀ a, c a * l (omd₁ a (Ed (omd (ext a₀⁻¹) Φ₀))) = (l ∘ₗ Ed) (omd (ext a) (omd (ext a₀⁻¹) Φ₀)) := by
      intro a
      rw [LinearMap.comp_apply, hkey a _ hΦ', map_smul, smul_eq_mul]
    have hf0 : l (omd₁ a₀ (Ed (omd (ext a₀⁻¹) Φ₀))) ≠ 0 := by
      rw [hkey _ _ hΦ₀, map_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
        map_smul, smul_eq_mul]
      exact mul_ne_zero (hc_ne _) hx₀
    refine ((hhc.continuousAt).div (hfc.continuousAt) hf0).congr ?_
    filter_upwards [hfc.continuousAt.eventually_ne hf0] with a ha
    rw [Pi.div_apply, ← heq a]
    field_simp
  have hcUc : Continuous cU := by
    have h2 : Continuous fun a => (((cU a)⁻¹ : ℂˣ) : ℂ) := by
      have : (fun a => (((cU a)⁻¹ : ℂˣ) : ℂ)) = fun a => (c a)⁻¹ :=
        funext fun a => by rw [Units.val_inv_eq_inv_val, hcU]
      rw [this]
      exact hcont.inv₀ hc_ne
    exact Units.continuous_iff.2 ⟨hcont, h2⟩
  have hskew : ∀ i j, σ (W₁.J j i) = (((-1 : ℤˣ) : ℤ) : E) * W₁.J i j := by
    intro i j
    rw [hP₁.skew.skew]
    simp
  have htriv := GlobalTheory.T.doubledUnitary_character_trivial_of_siegel F E σ hP.base.cm d₁ W₁.J (-1) hskew
    (GlobalTheory.ThK.TorusCentre.det_ne_zero_of_isSkew hP₁.skew) cU hcUc (by
      intro p t hpt
      refine Units.ext ?_
      rw [hcU]
      exact dblEv_siegel F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁
        dd omd hdd homd dd₁ omd₁ hdd₁ homd₁ Ed hEpres hEheis hEinv hEadm ⟨Φ₀, hΦ₀, hne⟩ p t hpt (ext p) (hc p) (c p)
        (fun Φ hΦ => hkey p Φ hΦ))
  have hg : g = ext g₁ := (hext g₁ g).1 ⟨hg1, hg2, hg3, hg4, hg5⟩
  have hc1 : c g₁ = 1 := by
    rw [← hcU, htriv]
    rfl
  intro Φ hΦ
  rw [hg, hkey g₁ Φ hΦ, hc1, one_smul]

theorem char_eq_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ c : UA σ W₁.J →* ℂˣ, Continuous c →
      (∀ h₁ m, IsLevi H' 1 h₁ m → ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, m) Φ) = (c h₁ : ℂ) • om₁ (1, h₁) (e Φ)) → c = 1 := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he c _hc hce
  obtain ⟨hUS, dd, omd, hDC, hSpl, hbox⟩ := hP.weil.1
  obtain ⟨-, dd₁, omd₁, hDC₁, hSpl₁, hbox₁⟩ := hP₁.weil.1
  obtain ⟨Ed, e₂, hEa, hEb, hEc, hEd, hEe, he₂s, Φ₂, hΦ₂, he₂Φ⟩ :=
    GlobalTheory.MixWCharP.Ev.exists_dblEv F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he dd dd₁ hDC hDC₁
  obtain ⟨Φ₁, hΦ₁, heΦ⟩ := GlobalTheory.EvSchANe.exists_mem_schA_ne_zero F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he
  have hEne : ∃ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ≠ 0 :=
    ⟨boxFun Φ₁ Φ₂, GlobalTheory.BoxSchwartz.boxFun_mem_schA_adelic F _ _ Φ₁ Φ₂ hΦ₁ hΦ₂, by rw [hEe Φ₁ hΦ₁ Φ₂ hΦ₂]; exact boxFun_ne_zero heΦ he₂Φ⟩
  have key := dblEv_intertwine F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ dd omd hDC hSpl
    dd₁ omd₁ hDC₁ hSpl₁ Ed hEa hEb hEc hEd hEne
  ext h₁
  obtain ⟨m, hm, -⟩ := GlobalTheory.PlaneLeviExt.levi_existsUnique F E σ B d d₁ W W₁ H' i₀ i₁ r' s' r₁ s₁ (GlobalTheory.AdelicU.cm_conj_conj hP.base.cm) hP.skew hP₁.skew hH h₁
  obtain ⟨md, hmd⟩ := exists_dbl_left (cA σ) (incM F W.J) m
  obtain ⟨hd, hhd⟩ := exists_dbl_left (cA σ) (incM F W₁.J) h₁
  obtain ⟨hmx, hmy, hmι⟩ := hm
  have hmx' : mat m *ᵥ incV F H'.x = incV F H'.x := by rw [hmx, Units.val_one, one_smul]
  have hmy' : mat m *ᵥ incV F H'.y = incV F H'.y := by rw [hmy, inv_one, Units.val_one, map_one, one_smul]
  have hmd' : (md.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) = Matrix.fromBlocks (mat m) 0 0 1 := hmd
  have hhd' : (hd.1.1 : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) = Matrix.fromBlocks (mat h₁) 0 0 1 := hhd
  have k := key hd md
    (by
      rw [hmd', hhd', Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp [hmι])
    (by rw [hmd', Matrix.fromBlocks_mulVec]; simp [hmx'])
    (by rw [hmd', Matrix.fromBlocks_mulVec]; simp)
    (by rw [hmd', Matrix.fromBlocks_mulVec]; simp [hmy'])
    (by rw [hmd', Matrix.fromBlocks_mulVec]; simp)
    (boxFun Φ₁ Φ₂) (GlobalTheory.BoxSchwartz.boxFun_mem_schA_adelic F _ _ Φ₁ Φ₂ hΦ₁ hΦ₂)
  have hpres : om (1, m) Φ₁ ∈ schA F (Fin n × Fin d) := by
    have := hUS.toIsSplitting.pres m Φ₁ hΦ₁
    exact this
  rw [hbox m md hmd Φ₁ hΦ₁ Φ₂ hΦ₂] at k
  rw [show (om.comp (MonoidHom.inr _ _)) m Φ₁ = om (1, m) Φ₁ from rfl, hEe _ hpres Φ₂ hΦ₂, hEe Φ₁ hΦ₁ Φ₂ hΦ₂,
    hbox₁ h₁ hd hhd (e Φ₁) (he.maps Φ₁ hΦ₁) (e₂ Φ₂) (he₂s Φ₂ hΦ₂), hce h₁ m ⟨hmx, hmy, hmι⟩ Φ₁ hΦ₁] at k
  have hA : om₁ (1, h₁) (e Φ₁) ≠ 0 := by
    intro h0
    apply heΦ
    have : om₁ (1, h₁⁻¹) (om₁ (1, h₁) (e Φ₁)) = e Φ₁ := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, inv_mul_cancel, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    rw [← this, h0, map_zero]
  rw [MonoidHom.one_apply, Units.val_one]
  exact eq_one_of_boxFun hA he₂Φ k

end GlobalTheory.MixWCharP
