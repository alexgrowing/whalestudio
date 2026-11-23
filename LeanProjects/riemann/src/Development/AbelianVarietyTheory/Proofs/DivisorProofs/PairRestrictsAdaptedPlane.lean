import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIncMLagP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelHaarIntegrableBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxModelCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedMatrixPhaseIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedModelRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLagrangianVecMulVecCoordsStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.SiegelConv

theorem schrSchr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]
  congr 2
  have h : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h

theorem avg_conv : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
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
      ∀ μ : @Measure (Fin n → AE F E) (borel _), GlobalTheory.SiegelAvg.IsHaarB μ →
        ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), GlobalTheory.SiegelAvg.Conv μ (l₁ ∘ₗ ed) (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y)) Φ := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hpair₁
    d' hd' d₁' hd₁' dd hdd dd₁ hdd₁ ed hed_mem hed_heis hed_inv hed_adm hed_ne l₁ hl₁ hl₁_inv μ hμ Φ hΦ
  classical
  have hψ : IsStd B.ψ := hpair.base.std
  haveI : Nontrivial (AF F) := (inferInstance : Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  obtain ⟨D, hDinj, hD⟩ := GlobalTheory.T.darboux_model_coordinates F E σ B n d X W M χX χW om r s r' s' hpair d' hd' dd hdd
  obtain ⟨hPinj, hPy⟩ := GlobalTheory.T.pair_adapted_model_restriction F E σ B n d X W M χX χW om r s r' s' hpair d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hpair₁
  let κ := (Fin n × Fin d) ⊕ (Fin n × Fin d)
  let P := GlobalTheory.SiegelConv.lagP n H'.ι H'.x
  let L : Submodule F ((κ → F) × (κ → F)) := ((LinearMap.range P).restrictScalars F).map D
  let l := l₁ ∘ₗ ed
  have hmem : ∀ w, ∀ φ ∈ schA F κ, dd.rho B.ψ w φ ∈ schA F κ := fun w φ hφ =>
    GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ (dd.e w) φ hφ

  have hinvZ : ∀ (Z : Matrix (Fin d₁) (Fin n) (AE F E)) (Y : Fin n ⊕ Fin n → AE F E), ∀ φ ∈ schA F κ,
      l (dd.rho B.ψ (incM F H'.ι * (Z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) + Matrix.vecMulVec (incV F H'.x) Y) φ) = l φ := by
    intro Z Y φ hφ
    have hiso := GlobalTheory.T.pair_adapted_matrix_phase_identity F E σ B n d X W M χX χW om r s r' s' hpair d₁ W₁ H' i₀ i₁ hH Z 0 0 Y
    have h0 : Matrix.vecMulVec (incV F H'.x) (0 : Fin n ⊕ Fin n → AE F E) = 0 := by
      ext i j; simp [Matrix.vecMulVec_apply]
    have h0' : incM F H'.ι * ((0 : Matrix (Fin d₁) (Fin n) (AE F E)) * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) = 0 := by
      rw [Matrix.zero_mul, Matrix.mul_zero]
    rw [h0, h0', add_zero, zero_add] at hiso
    have hform := dd.form (incM F H'.ι * (Z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ)) (Matrix.vecMulVec (incV F H'.x) Y)
    rw [hiso] at hform
    have hss := schrSchr B.ψ (dd.e (incM F H'.ι * (Z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ))) (dd.e (Matrix.vecMulVec (incV F H'.x) Y)) φ
    rw [← hform, mul_zero, AddChar.map_zero_eq_one, one_smul, ← map_add] at hss
    have hb' : dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) Y) φ ∈ schA F κ := hmem _ φ hφ
    show l₁ (ed (schr B.ψ (dd.e (incM F H'.ι * (Z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) + Matrix.vecMulVec (incV F H'.x) Y)) φ)) = l₁ (ed φ)
    rw [← hss]
    show l₁ (ed (dd.rho B.ψ (incM F H'.ι * (Z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ)) (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) Y) φ))) = l₁ (ed φ)
    rw [hed_heis _ _ hb']
    exact (hl₁_inv Z _ (hed_mem _ hb')).trans (congrArg l₁ (hed_inv Y φ hφ))

  have hL_iso : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2 := by
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩ _ ⟨_, ⟨q, rfl⟩, rfl⟩
    have hp := GlobalTheory.SiegelConv.smul_incM_lagP (F := F) (n := n) H'.ι H'.x (1 : AF F) p
    have hq := GlobalTheory.SiegelConv.smul_incM_lagP (F := F) (n := n) H'.ι H'.x (1 : AF F) q
    simp only [one_smul] at hp hq
    have hiso := GlobalTheory.T.pair_adapted_matrix_phase_identity F E σ B n d X W M χX χW om r s r' s' hpair d₁ W₁ H' i₀ i₁ hH (incM F p.1) (incM F q.1)
      (fun i => inclR (F := F) (AF F) (p.2 i)) (fun i => inclR (F := F) (AF F) (q.2 i))
    rw [← hp, ← hq] at hiso
    have hform := dd.form (incM F (P p)) (incM F (P q))
    rw [hiso, hD, hD] at hform
    simp only [GlobalTheory.SiegelConv.ratP, GlobalTheory.SiegelConv.ratDot, ← map_sub] at hform
    exact sub_eq_zero.mp ((algebraMap F (AF F)).injective (hform.symm.trans (map_zero _).symm))
  have hL_dim : Module.finrank F L = Fintype.card κ := by
    have h1 : Module.finrank F L = Module.finrank F ((LinearMap.range P).restrictScalars F) :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective D hDinj _)).symm
    have h2 : Module.finrank F ((LinearMap.range P).restrictScalars F) =
        Module.finrank F E * Module.finrank E (LinearMap.range P) :=
      (Module.finrank_mul_finrank F E (LinearMap.range P)).symm
    have h3 : Module.finrank E (LinearMap.range P) = d₁ * n + (n + n) := by
      rw [LinearMap.finrank_range_of_inj hPinj, Module.finrank_prod, Module.finrank_matrix,
        Module.finrank_fintype_fun_eq_card]
      simp
    have hE : Module.finrank F E = 2 := hpair.base.cm.2.2.1
    have hd : d = d₁ + 2 := hH.rank
    rw [h1, h2, h3, hE]
    simp only [κ, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hd]
    ring
  have hL_inv : ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ, l (schr B.ψ (t • GlobalTheory.SiegelConv.ratP w) φ) = l φ := by
    rintro t _ ⟨_, ⟨p, rfl⟩, rfl⟩ φ hφ
    have e : t • GlobalTheory.SiegelConv.ratP (D (P p)) = dd.e (t • incM F (P p)) := by rw [map_smul, hD]
    rw [e, GlobalTheory.SiegelConv.smul_incM_lagP]
    exact hinvZ _ _ φ hφ
  let A := D ∘ₗ GlobalTheory.SiegelConv.vvMap F (n := n) H'.y
  have hA : ∀ s', A s' ∈ L → s' = 0 := by
    rintro s' ⟨_, ⟨p, rfl⟩, hu⟩
    have h1 : P p = GlobalTheory.SiegelConv.vvMap F (n := n) H'.y s' := hDinj hu
    have h2 := hPy (GlobalTheory.SiegelConv.vecOf F s') ⟨p, h1⟩
    funext ji
    obtain ⟨j, i⟩ := ji
    have h3 : ∑ i, s' (j, i) • Module.finBasis F E i = 0 := congrFun h2 j
    exact Fintype.linearIndependent_iff.mp (Module.finBasis F E).linearIndependent (fun i => s' (j, i)) h3 i
  have hl_adm : l ∈ (adeleClass F).adm κ := hed_adm l₁ hl₁
  show (letI : MeasurableSpace (Fin n → AE F E) := borel _;
    Integrable (fun y => l (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y Φ)) μ)
  refine GlobalTheory.T.siegel_haar_integrable_basis F E n _ μ hμ (fun ν hν => ?_)
  have key := GlobalTheory.T.lagrangian_invariant_functional F B.ψ hψ κ L hL_iso hL_dim l hl_adm hL_inv (Fin n × Fin (Module.finrank F E)) A hA ν hν Φ hΦ
  have e : (fun t => l (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) (GlobalTheory.SiegelConv.basisMap F E n t) Φ)) =
      fun t => l (schr B.ψ (GlobalTheory.SiegelConv.extA A t) Φ) := by
    funext t
    rw [GlobalTheory.SiegelAvg.starFam_apply]
    show l (schr B.ψ (dd.e _) Φ) = _
    rw [show dd.e _ = GlobalTheory.SiegelConv.extA A t from GlobalTheory.T.siegel_lagrangian_vecMulVec_coords F E n d κ dd.e.toLinearMap D hD H'.y t]
  rw [e]
  exact key

end GlobalTheory.SiegelConv

end
