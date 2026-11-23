import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairRestrictsAdaptedPlaneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedPlaneInductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedRestrictionCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedRestrictionCompatAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompGlInvHaarStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.MixWSiegel

theorem rho_diagCols {a b : ℕ} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {JA : Matrix (Fin a) (Fin a) E} {JB : Matrix (Fin b) (Fin b) E} {κ : Type}
    [Fintype κ] {d : Darboux (symp (cA σ) (-1) (incM F JA) (incM F JB)) κ}
    {dd : Darboux (symp (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ)}
    (h : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd) (ψ : AddChar (AF F) ℂ)
    (z : Matrix (Fin a) (Fin b) (AE F E)) :
    dd.rho ψ (z * (diagCols (Fin b))ᵀ) =
      schr ψ (Sum.elim (d.e z).1 (d.e z).1, Sum.elim (d.e z).2 (-(d.e z).2)) := by
  unfold Darboux.rho
  rw [← h]
  congr 2
  ext i j
  rcases j with j | j <;> erw [Matrix.mul_apply] <;> simp [diagCols, Matrix.one_apply]

theorem haar_exists (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    ∃ μ : @Measure (Fin n → AE F E) (borel _), GlobalTheory.SiegelAvg.IsHaarB μ := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  letI : MeasurableSpace (Fin n → AE F E) := borel _
  haveI : BorelSpace (Fin n → AE F E) := ⟨rfl⟩
  exact ⟨Measure.addHaar, by unfold GlobalTheory.SiegelAvg.IsHaarB; infer_instance⟩

theorem actB_vecMulVec_diag {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n a : ℕ} {J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)} (p : UG (cA σ) J)
    (t : GL (Fin n) (AE F E))
    (hpt : ((p : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * diagCols (Fin n) =
      diagCols (Fin n) * (t : Matrix (Fin n) (Fin n) (AE F E))) (u : Fin a → AE F E) (y : Fin n → AE F E) :
    actB (cA σ) p (Matrix.vecMulVec u (Sum.elim ((((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))) *ᵥ y)
      ((((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))) *ᵥ y))) = Matrix.vecMulVec u (Sum.elim y y) := by
  have hd : ∀ z : Fin n → AE F E, Sum.elim z z = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) *ᵥ z :=
    fun z => by rw [diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]
  have ht : (t : Matrix (Fin n) (Fin n) (AE F E)) * ((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hpt' : ((p : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (t : Matrix (Fin n) (Fin n) (AE F E)) := hpt
  have h1 : ((p : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *ᵥ
      Sum.elim ((((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))) *ᵥ y)
        ((((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))) *ᵥ y) = Sum.elim y y := by
    rw [hd, Matrix.mulVec_mulVec, hpt', ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec y (t : Matrix (Fin n) (Fin n) (AE F E)),
      ht, Matrix.one_mulVec, ← hd]
  unfold actB
  rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose, h1]

theorem avg_exists : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
        (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
      ∀ (d₁' : Darboux (symp (cA σ) (-1) (incM F W₁.J) (incM F X.J)) (Fin n × Fin d₁)),
        (∀ x : Matrix (Fin n) (Fin d₁) (AE F E), d₁'.e xᵀ = M₁.co.e x) →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
        IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd →
      ∀ (dd₁ : Darboux (symp (cA σ) (-1) (incM F W₁.J) (dbl (incM F X.J))) ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))),
        IsDblCoord (cA σ) (-1) (incM F W₁.J) (incM F X.J) d₁' dd₁ →
      ∀ (omd : UG (cA σ) (dbl (incM F X.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ)),
        IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F W.J) (dbl (incM F X.J)) dd χW (diagCols (Fin n)) omd →
      ∀ (omd₁ : UG (cA σ) (dbl (incM F X.J)) →* Module.End ℂ (((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → AF F) → ℂ)),
        IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F W₁.J) (dbl (incM F X.J)) dd₁ χW (diagCols (Fin n)) omd₁ →
      ∀ ed : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] (((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → AF F) → ℂ),
        (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ed Φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))) →
        (∀ (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ed (dd.rho B.ψ (incM F H'.ι * z) Φ) = dd₁.rho B.ψ z (ed Φ)) →
        (∀ (y : Fin n ⊕ Fin n → AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) y) Φ) = ed Φ) →
        (∀ l ∈ (adeleClass F).adm ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)), l ∘ₗ ed ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d))) →
        (∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ed Φ ≠ 0) →
      ∀ l₁ : (((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → AF F) → ℂ) →ₗ[ℂ] ℂ, l₁ ∈ (adeleClass F).adm ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)) →
        (∀ (z : Matrix (Fin d₁) (Fin n) (AE F E)), ∀ φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)),
          l₁ (dd₁.rho B.ψ (z * (diagCols (Fin n))ᵀ) φ) = l₁ φ) →
        (∃ φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)), l₁ φ ≠ 0) →
      ∃ L : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ℂ, L ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ∧
        (∀ (z : Matrix (Fin d) (Fin n) (AE F E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          L (dd.rho B.ψ (z * (diagCols (Fin n))ᵀ) Φ) = L Φ) ∧
        (∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), L Φ ≠ 0) ∧
        ∀ (p : UG (cA σ) (dbl (incM F X.J))) (t : GL (Fin n) (AE F E)),
          ((p : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 →
          ∀ k : ℂ, (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), l₁ (ed (omd p Φ)) = k * l₁ (ed Φ)) →
          ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
            L (omd p Φ) = k * (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) : ℂ) * L Φ := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁' hd₁' dd hdd
    dd₁ hdd₁ omd hWS omd₁ hWS₁ ed hmap hheis hinv hadm hnz l₁ hl₁ hl₁inv hl₁0
  obtain ⟨μ, hμ⟩ := haar_exists F E n
  have hψ : IsStd B.ψ := hP.base.std
  have hconv := GlobalTheory.T.pair_restricts_adapted_plane hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁' hd₁' dd hdd dd₁ hdd₁ ed hmap hheis hinv hadm hnz l₁ hl₁ hl₁inv μ hμ
  have hA := GlobalTheory.T.pair_adapted_plane_induction hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁' hd₁' dd hdd dd₁ hdd₁ ed hmap hheis hinv hadm hnz l₁ hl₁ hl₁inv μ hμ
  have hN := GlobalTheory.T.pair_adapted_restriction_compat hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁' hd₁' dd hdd dd₁ hdd₁ ed hmap hheis hinv hadm hnz l₁ hl₁ hl₁inv hl₁0 μ hμ
  have hV := GlobalTheory.T.pair_adapted_restriction_compat_alt hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁' hd₁' dd hdd dd₁ hdd₁ ed hmap hheis hinv hadm hnz l₁ hl₁ hl₁inv μ hμ
  refine ⟨_, hA, hV, hN, ?_⟩
  intro p t hpt k hk Φ hΦ
  obtain ⟨-, hS, -⟩ := hWS
  have hΦ' := hS.pres p Φ hΦ
  letI : MeasurableSpace (Fin n → AE F E) := borel _
  rw [GlobalTheory.SiegelAvg.avgForm_apply _ _ _ (hconv _ hΦ'), GlobalTheory.SiegelAvg.avgForm_apply _ _ _ (hconv _ hΦ)]
  have hpw : ∀ y, (l₁ ∘ₗ ed) (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y (omd p Φ)) =
      k * (l₁ ∘ₗ ed) (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y)
        ((((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))) *ᵥ y) Φ) := fun y => by
    simp only [LinearMap.comp_apply, GlobalTheory.SiegelAvg.starFam_apply]
    rw [← actB_vecMulVec_diag p t hpt (incV F H'.y) y, ← hS.impl p _ Φ hΦ]
    exact hk _ (GlobalTheory.SchrKeepsSchA.schr_mem_schA F B.ψ hψ _ _ Φ hΦ)
  simp_rw [hpw]
  rw [integral_const_mul, GlobalTheory.T.integral_comp_gl_inv_haar F E n μ hμ t _ (hconv _ hΦ)]
  ring

theorem siegel_scalar_eq_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
        (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
      ∀ (d₁' : Darboux (symp (cA σ) (-1) (incM F W₁.J) (incM F X.J)) (Fin n × Fin d₁)),
        (∀ x : Matrix (Fin n) (Fin d₁) (AE F E), d₁'.e xᵀ = M₁.co.e x) →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
        IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd →
      ∀ (dd₁ : Darboux (symp (cA σ) (-1) (incM F W₁.J) (dbl (incM F X.J))) ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))),
        IsDblCoord (cA σ) (-1) (incM F W₁.J) (incM F X.J) d₁' dd₁ →
      ∀ (omd : UG (cA σ) (dbl (incM F X.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ)),
        IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F W.J) (dbl (incM F X.J)) dd χW (diagCols (Fin n)) omd →
      ∀ (omd₁ : UG (cA σ) (dbl (incM F X.J)) →* Module.End ℂ (((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → AF F) → ℂ)),
        IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F W₁.J) (dbl (incM F X.J)) dd₁ χW (diagCols (Fin n)) omd₁ →
      ∀ ed : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] (((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → AF F) → ℂ),
        (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ed Φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))) →
        (∀ (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ed (dd.rho B.ψ (incM F H'.ι * z) Φ) = dd₁.rho B.ψ z (ed Φ)) →
        (∀ (y : Fin n ⊕ Fin n → AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) y) Φ) = ed Φ) →
        (∀ l ∈ (adeleClass F).adm ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)), l ∘ₗ ed ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d))) →
        (∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ed Φ ≠ 0) →
      ∀ cd : UG (cA σ) (dbl (incM F X.J)) → ℂ,
        (∀ p, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ed (omd p Φ) = cd p • omd₁ p (ed Φ)) →
      ∀ (p : UG (cA σ) (dbl (incM F X.J))) (t : GL (Fin n) (AE F E)),
        ((p : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 →
        cd p = 1 := by

  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁' hd₁' dd hdd
    dd₁ hdd₁ omd hWS omd₁ hWS₁ ed hmap hheis hinv hadm hnz cd hcd p t hpt
  obtain ⟨l₁, hl₁, hl₁inv, φ₀, hφ₀, hl₁0⟩ := GlobalTheory.T.exists_diagonalLagrangian_invariant_form F B.ψ (Fin n × Fin d₁)
  have hl₁' : ∀ (z : Matrix (Fin d₁) (Fin n) (AE F E)), ∀ φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)),
      l₁ (dd₁.rho B.ψ (z * (diagCols (Fin n))ᵀ) φ) = l₁ φ := fun z φ hφ => by
    rw [rho_diagCols hdd₁ B.ψ z]; exact hl₁inv _ _ φ hφ
  obtain ⟨L, hL, hLinv, ⟨Φ₀, hΦ₀, hL0⟩, hLtr⟩ := avg_exists hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁
    r₁ s₁ hH hP₁ d' hd' d₁' hd₁' dd hdd dd₁ hdd₁ omd hWS omd₁ hWS₁ ed hmap hheis hinv hadm hnz l₁ hl₁ hl₁' ⟨φ₀, hφ₀, hl₁0⟩
  obtain ⟨-, -, hR⟩ := hWS
  obtain ⟨-, -, hR₁⟩ := hWS₁
  set m : ℝ≥0 := (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) with hm
  set χt : ℂ := ((χW (Matrix.GeneralLinearGroup.det t) : Circle) : ℂ) with hχt
  have hk : ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), l₁ (ed (omd p Φ)) =
      (cd p * (χt * (((m : ℝ) ^ ((d₁ : ℝ) / 2) : ℝ) : ℂ))) * l₁ (ed Φ) := fun Φ hΦ => by
    rw [hcd p Φ hΦ, map_smul, hR₁ l₁ hl₁ hl₁' p t hpt _ (hmap Φ hΦ), smul_eq_mul]
    simp only [Fintype.card_fin, hχt, hm]
    ring
  have e1 := hLtr p t hpt _ hk Φ₀ hΦ₀
  have e2 := hR L hL hLinv p t hpt Φ₀ hΦ₀
  rw [e1] at e2
  simp only [Fintype.card_fin] at e2
  have hm0 : (m : ℝ) ≠ 0 := by
    intro h0
    have h1 := map_mul (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t))
      (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t))⁻¹
    rw [mul_inv_cancel, map_one, ← hm] at h1
    have : (m : ℝ) * ((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t))⁻¹ : ℝ) = 1 := by
      exact_mod_cast h1.symm
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hmpos : (0 : ℝ) < m := lt_of_le_of_ne m.2 (Ne.symm hm0)
  have hd : (d : ℝ) / 2 = (d₁ : ℝ) / 2 + 1 := by rw [hH.rank]; push_cast; ring
  rw [hd, Real.rpow_add hmpos, Real.rpow_one] at e2
  have hχ0 : χt ≠ 0 := by rw [hχt]; exact Circle.coe_ne_zero _
  have hp0 : (((m : ℝ) ^ ((d₁ : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hmpos _).ne'
  have hm0' : ((m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm0
  have key : (cd p - 1) * (χt * (((m : ℝ) ^ ((d₁ : ℝ) / 2) : ℝ) : ℂ) * ((m : ℝ) : ℂ) * L Φ₀) = 0 := by
    push_cast at e2 ⊢
    linear_combination e2
  rcases mul_eq_zero.mp key with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hχ0 hp0) hm0') hL0) h

end GlobalTheory.MixWSiegel
end
