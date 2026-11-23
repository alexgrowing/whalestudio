import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaGlobal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

private theorem symp_dual {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hcm : IsCMExt F E σ) {n d n₁ d₁ : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E}
    (hJ : ∀ i j, σ (JW j i) = -JW i j) (H : Plane E n n₁) (H' : Plane E d d₁) (hH : form σ JX H.x H.y = 1)
    (hH' : form σ JW H'.x H'.y = 1) (c t : E) :
    symp (cA σ) (-1) (incM F JX) (incM F JW)
      (inclR (F := F) (AF F) c • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
      (inclR (F := F) (AF F) (σ t) • Matrix.vecMulVec (incV F H.y) (incV F H'.x)) =
      Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) t * inclR (F := F) (AF F) c) := by
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  rw [symp, GlobalTheory.XTermSupp.hTens_vv, GlobalTheory.XTermSupp.form_inc, GlobalTheory.XTermSupp.form_inc, hH,
    GlobalTheory.XTermSupp.form_skew hcm hJ, hH', hc, GlobalTheory.XTermSupp.invol hcm]
  congr 1
  simp [mul_comm]

open GlobalTheory.XTermDecay GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.DiffDecay in
theorem UpperTheory.theta_geometry_triple_vanishing :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
        (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
        ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
        ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
        ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), ∀ C : Set (UA σ G.V'.J × UA σ G.W.J), IsCompact C →
        ∀ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U → ∀ (c : Fin b × Fin (a + b) → Af F) (N k : ℕ),
        ∃ D : ℝ, ∀ p ∈ C, ∀ l : (AE F E)ˣ, (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U →
          ∃ f : SInf F (Fin b × Fin (a + b)), (∀ y, f y = e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' p Ψ))
              (fun q => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y q), c q))) ∧
            GlobalTheory.ThKSoDecay.semK (Fin b × Fin (a + b)) k f ≤
              D * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) := by
  classical
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC e he X om om' om₁ om₁' hT _ Ψ hΨ C hCc U hU c N k
  have hw := hT.weil'
  obtain ⟨m, g, f, hg, hdec, hf⟩ := exists_decomp (fun p : C => om' p.1 Ψ)
    (fun p => (IsUWeilPair.isUSplitting hw).pres p.1 Ψ hΨ) fun l hl => by
      have hc := hw.2.2 l hl Ψ hΨ
      obtain ⟨D, hD⟩ := hCc.exists_bound_of_continuousOn hc.continuousOn
      exact ⟨D, fun p => hD p.1 p.2⟩
  choose t ht using GlobalTheory.XTermSupp.trace_mul_dual (F := F) (E := E)
  let S := fun j => G.M'.co.e (inclR (F := F) (AF F) (σ (Module.finBasis F E j)) •
    Matrix.vecMulVec (incV F H.y) (incV F H'.x))
  let U' := fun i => G.M'.co.e (inclR (F := F) (AF F) (-(t i)) • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
  have hp : Continuous ⇑(Finset.sup (Finset.Iic (k, k))
      (schwartzSeminormFamily ℂ (Fin b × Fin (a + b) → mixedEmbedding.mixedSpace F) ℂ)) :=
    Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm i
  have hSU : ∀ i j, (S j).1 ⬝ᵥ (U' i).2 - (U' i).1 ⬝ᵥ (S j).2 = if i = j then 1 else 0 := fun i j => by
    have h1 := symp_dual hT.base.cm hT.geo.hW.skew H H' hC.hH.xy hC.hH'.xy (-(t i)) (Module.finBasis F E j)
    rw [G.M'.co.form, map_neg, mul_neg, map_neg, ht] at h1
    have h2 : GlobalTheory.XTermMaj.crd F E (inclR (F := F) (AF F) (Module.finBasis F E j)) i = if i = j then 1 else 0 := by
      have h3 : inclR (F := F) (AF F) (Module.finBasis F E j) =
          Algebra.TensorProduct.basis (AF F) (Module.finBasis F E) j := by
        rw [Algebra.TensorProduct.basis_apply]
        rfl
      rw [h3]
      change (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun _ i = _
      rw [Module.Basis.equivFun_self]
      simp only [eq_comm]
    rw [← h2, ← neg_sub]
    simp only [S, U', map_neg]
    rw [h1, neg_neg]
  choose D₀ hCb using fun j => slice_decay B.ψ hT.base.std S U' (fun i j => by convert hSU i j)
    (sliceL c ∘ₗ e) (exists_slice_clm hT.geo.hM' he c) (fun i a Ψ hΨ => by
      have := he.inv (a • inclR (F := F) (AF F) (-(t i)) • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
        (Or.inl ⟨a • inclR (F := F) (AF F) (-(t i)) • incV F H'.y, by
          rw [Matrix.vecMulVec_smul, Matrix.vecMulVec_smul]⟩) Ψ hΨ
      rw [Darboux.rho, map_smul] at this
      exact congrArg (sliceL c) this) (hg j) (f j) (hf j) hU _ hp N
  refine ⟨∑ j, D₀ j, fun p hp l hl => ?_⟩
  choose f₁ hf₁ hb₁ using fun j => hCb j ⟨p, hp⟩ (GlobalTheory.XTermMaj.crd F E (l : AE F E)) hl
  have hS : G.M'.co.e (shiftB σ H H' l) = ∑ i, GlobalTheory.XTermMaj.crd F E (l : AE F E) i • S i := by
    simp only [S, ← map_smul, ← map_sum, ← smul_assoc, ← Finset.sum_smul]
    congr 1
    rw [shiftB]
    congr 1
    refine (congrArg (cA σ)
      ((Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).sum_equivFun (l : AE F E)).symm).trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.TensorProduct.basis_apply]
    rfl
  refine ⟨∑ j, f₁ j, fun y => ?_, ?_⟩
  · have h1 := hdec ⟨p, hp⟩
    simp only at h1
    rw [h1, Darboux.rho, hS]
    change coeL (∑ j, f₁ j) y = (sliceL c ∘ₗ e) (schrL B.ψ _ _) y
    rw [map_sum, map_sum, map_sum]
    exact congrFun (Finset.sum_congr rfl fun j _ => hf₁ j) y
  · rw [Finset.sum_mul]
    exact (Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _).trans (Finset.sum_le_sum fun j _ => hb₁ j)
