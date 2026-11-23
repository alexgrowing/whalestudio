import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaFinite

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ConeFinSlices

open GlobalTheory.XTermFinParts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem symp_dual_eq_zero {B : Base F E} {n n₁ d : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ : ℕ}
    (hH : H.IsAdapted σ B X X₁ i₀ i₁) (JB : Matrix (Fin d) (Fin d) (AE F E)) (z : Matrix (Fin n₁) (Fin d) (AE F E))
    (l : AE F E) (y : Fin d → AE F E) :
    symp (R := AF F) (cA σ) (-1) (incM F X.J) JB (incM F H.ι * z) (l • Matrix.vecMulVec (incV F H.y) y) = 0 := by
  have h0 : ∀ a, ∑ i, ∑ k, incM F H.ι i a * incM F X.J i k * cA σ (incV F H.y k) = 0 := fun a => by
    have h := congrArg (inclR (F := F) (AF F)) (hH.orth (Pi.single a 1)).2
    rw [map_zero, Matrix.mulVec_single_one] at h
    rw [← h]
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, mul_assoc]
    rfl
  have h1 : hTens (cA σ) (incM F X.J) JB (incM F H.ι * z) (l • Matrix.vecMulVec (incV F H.y) y) =
      ∑ a, ∑ j, ∑ m, (∑ i, ∑ k, incM F H.ι i a * incM F X.J i k * cA σ (incV F H.y k)) *
        (z a j * JB j m * cA σ l * cA σ (y m)) := by
    simp only [hTens, Matrix.mul_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, map_mul, Finset.sum_mul]
    simp only [← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv ⟨fun p => (p.2.2.2.2, p.2.1, p.2.2.2.1, p.1, p.2.2.1),
      fun p => (p.2.2.2.1, p.2.1, p.2.2.2.2, p.2.2.1, p.1), fun _ => rfl, fun _ => rfl⟩ _ _ fun p => ?_
    simp only [Equiv.coe_fn_mk]
    ring
  rw [symp, h1]
  simp [h0]

end GlobalTheory.ConeFinSlices

namespace GlobalTheory.ConeFinSlices

open GlobalTheory.XTermFinParts

theorem finite_slices : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h,
      ∃ (r : ℕ) (g : Fin r → (Fin b × Fin (a + b) → FiniteAdeleRing (𝓞 F) F) → ℂ),
        (∀ j, g j ∈ SB (Fin b × Fin (a + b) → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ (k : K) (l : (AE F E)ˣ) (s : Fin b × Fin (a + b) → InfiniteAdeleRing F),
          (fun z : Fin b × Fin (a + b) → FiniteAdeleRing (𝓞 F) F =>
            e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ')) (fun i => ((s i, z i) : AdeleRing (𝓞 F) F))) ∈ Submodule.span ℂ (Set.range g) := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' hC e he K _ _ hK _ _ X om om' _ _ hT _ Φ hΦ h
  have hψ := hT.base.std
  have hΦ' : Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) := by
    refine (Submodule.span_le.2 ?_ : PolData B G.M' ≤ _) hΦ.1
    rintro _ ⟨f, -, φ, hφ, hv, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hφ ((hv.and hT.geo.hM'.std).mono fun v h => h.1.trans h.2)
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have hs : Continuous (G₁.M'.co.e.symm : _ → Matrix (Fin b) (Fin (a + b)) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap G₁.M'.co.e.symm.toLinearMap
  have c : Continuous fun w => incM F H.ι * G₁.M'.co.e.symm w * (incM F H'.ι)ᵀ :=
    (continuous_const.matrix_mul hs).matrix_mul continuous_const
  have hN := (c.tendsto' 0 0 (by simp)).eventually (eventually_rho_om_eq hT.base hT.geo.hV' hK G.M' hT.weil' hΦ' h)
  obtain ⟨m, c, φ, hφ, hD⟩ := exists_parts hψ hN
  refine ⟨m, φ, hφ, fun k l s => ?_⟩
  have key := hD (e (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ))) fun w hw h0 => by
    have hΨ : om' (k.1, h) Φ ∈ schA F _ := (IsUWeilPair.isUSplitting hT.weil').pres (k.1, h) Φ hΦ'
    have h1 := hw (by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← map_smul, h0, map_zero, Matrix.mul_zero, Matrix.zero_mul]) k.1 k.2
    have h2 := he.Heisenberg₂ (G₁.M'.co.e.symm w) _ (GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hψ (shiftB σ H H' l) _ hΨ)
    rw [rho_comm G.M'.co B.ψ (by rw [Matrix.mul_assoc]; exact symp_dual_eq_zero hC.hH _ _ _ _), h1,
      show G₁.M'.co.rho B.ψ (G₁.M'.co.e.symm w) = schr B.ψ w from
        congrArg (schr B.ψ) (G₁.M'.co.e.apply_symm_apply w)] at h2
    exact h2.symm
  refine (Submodule.mem_span_range_iff_exists_fun ℂ).2
    ⟨fun j => e (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ)) (fun q => ((s q, c j q) : AdeleRing (𝓞 F) F)), ?_⟩
  funext z
  rw [Finset.sum_apply]
  exact (key fun i => ((s i, z i) : AdeleRing (𝓞 F) F)).symm

end GlobalTheory.ConeFinSlices

end
