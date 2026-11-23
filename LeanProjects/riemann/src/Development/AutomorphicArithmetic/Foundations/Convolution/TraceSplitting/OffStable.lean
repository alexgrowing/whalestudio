import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.FinSplit
import GroundTheory.GlobalFields.SemilocalAlgebras.Galois

open NumberField IsDedekindDomain ValuativeRel
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.T

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem val_gal (v : HeightOneSpectrum (𝓞 F)) (σ : E ≃ₐ[F] E) (w u : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver v.asIdeal] (h : u = σ • w) (y : w.adicCompletion E) :
    Valued.v (galEquiv v σ w u h y) = Valued.v y := by
  have hK : ∀ x : E, Valued.v (galEquiv v σ w u h (algebraMap E (w.adicCompletion E) x)) =
      Valued.v (algebraMap E (w.adicCompletion E) x) := by
    intro x
    have hx := valuation_smul σ w x
    rw [← h] at hx
    rw [galEquiv_algebraMap, HeightOneSpectrum.algebraMap_adicCompletion,
      HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa using hx
  have hclosed : IsClosed {y : w.adicCompletion E | Valued.v (galEquiv v σ w u h y) = Valued.v y} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y0 hy0
    have h0 : y0 ≠ 0 := by
      rintro rfl
      simp at hy0
    have h1 : Valued.v y0 ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have h2 : Valued.v (galEquiv v σ w u h y0) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 ((map_ne_zero _).2 h0)
    filter_upwards [Valued.locally_const h1,
      (continuous_galEquiv v σ w u h).continuousAt.preimage_mem_nhds (Valued.locally_const h2)]
      with y hy hy'
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff] at hy hy' hy0 ⊢
    rwa [hy, hy']
  exact (HeightOneSpectrum.denseRange_algebraMap E w).induction_on y hclosed hK

private theorem galFin_apply (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (y : CompletionsOver E v)
    (u : PlacesOver E v) :
    galFin σ v y u = galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u) (y (σ⁻¹ • u)) := by
  obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
  have h1 : galFin σ v (tensorEquiv' E v t) =
      tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F (v.adicCompletion F)) t) := by
    simp [galFin, galOf]
  rw [h1]
  clear h1
  induction t with
  | zero => simp
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  | tmul x a =>
    rw [Algebra.TensorProduct.map_tmul, tensorEquiv'_tmul, tensorEquiv'_tmul, Pi.mul_apply, Pi.mul_apply, map_mul]
    congr 1
    · exact (galEquiv_algebraMap v σ _ _ _ x).symm
    · exact ((galEquiv v σ _ _ (eq_smul_inv_smul v σ u)).commutes a).symm

variable {w u : HeightOneSpectrum (𝓞 E)} (φ : w.adicCompletion E →+* u.adicCompletion E)

private theorem le_of_val (hφ : ∀ y, Valued.v (φ y) = Valued.v y) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y ≤ 1) : valuation (u.adicCompletion E) (φ y) ≤ 1 := by
  rw [(ValuativeRel.isEquiv (valuation (u.adicCompletion E)) Valued.v).le_one_iff_le_one, hφ]
  exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).le_one_iff_le_one.1 hy

private theorem lt_of_val (hφ : ∀ y, Valued.v (φ y) = Valued.v y) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y < 1) : valuation (u.adicCompletion E) (φ y) < 1 := by
  rw [(ValuativeRel.isEquiv (valuation (u.adicCompletion E)) Valued.v).lt_one_iff_lt_one, hφ]
  exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).lt_one_iff_lt_one.1 hy

private theorem eq_of_val (hφ : ∀ y, Valued.v (φ y) = Valued.v y) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y = 1) : valuation (u.adicCompletion E) (φ y) = 1 := by
  rw [(ValuativeRel.isEquiv (valuation (u.adicCompletion E)) Valued.v).eq_one_iff_eq_one, hφ]
  exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).eq_one_iff_eq_one.1 hy

private theorem integral_map (n : ℕ) (hφ : ∀ y, Valued.v (φ y) = Valued.v y)
    {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GLnLocal.integralGL (w.adicCompletion E) n) :
    mapGL n φ g ∈ GLnLocal.integralGL (u.adicCompletion E) n := by
  rw [GLnLocal.mem_integralGL_iff] at hg ⊢
  rw [← map_inv]
  simp only [Valuation.mem_integer_iff] at hg ⊢
  exact ⟨fun i j => le_of_val φ hφ (hg.1 i j), fun i j => le_of_val φ hφ (hg.2 i j)⟩

private theorem iwahori_map (n : ℕ) (hφ : ∀ y, Valued.v (φ y) = Valued.v y)
    {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GLnLocal.iwahori (w.adicCompletion E) n) :
    mapGL n φ g ∈ GLnLocal.iwahori (u.adicCompletion E) n := by
  rw [GLnLocal.mem_iwahori_iff] at hg ⊢
  exact ⟨fun i j => le_of_val φ hφ (hg.1 i j), fun i j h => lt_of_val φ hφ (hg.2.1 i j h),
    fun i => eq_of_val φ hφ (hg.2.2 i)⟩

end

end UpperTheory.ConvolutionTheory.T

theorem UpperTheory.ConvolutionTheory.T.offStable :
    UpperTheory.ConvolutionTheory.T.OffStable := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ v
  have hv : ∀ (u : PlacesOver E v) y,
      Valued.v ((galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u)).toRingEquiv.toRingHom y) = Valued.v y :=
    fun u y => UpperTheory.ConvolutionTheory.T.val_gal v σ _ _ _ y
  have hc : ∀ (x : GL (Fin n) (CompletionsOver E v)) (u : PlacesOver E v),
      GM.cmp u (mapGL n (galFin σ v) x) =
        mapGL n (galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u)).toRingEquiv.toRingHom (GM.cmp (σ⁻¹ • u) x) :=
    fun x u => Units.ext (Matrix.ext fun a b => UpperTheory.ConvolutionTheory.T.galFin_apply σ v _ u)
  refine ⟨fun x hx u => ?_, fun x hx u => ?_,
    ⟨⨅ u : PlacesOver E v, (GLnLocal.integralGL (u.1.adicCompletion E) n).comap (GM.cmp u), ?_⟩,
    ⟨⨅ u : PlacesOver E v, (GLnLocal.iwahori (u.1.adicCompletion E) n).comap (GM.cmp u),
      fun g => by simp [Subgroup.mem_iInf]⟩,
    fun w => ⟨And.intro (GLnLocal.isCompact_integralGL _ n) (GLnLocal.isOpen_integralGL _ n),
      And.intro (GLnLocal.isCompact_iwahori _ n) (GLnLocal.isOpen_iwahori _ n),
      GLnLocal.iwahori_le_integralGL _ n⟩⟩
  · rw [hc]
    exact UpperTheory.ConvolutionTheory.T.integral_map _ n (hv u) (hx _)
  · rw [hc]
    exact UpperTheory.ConvolutionTheory.T.iwahori_map _ n (hv u) (hx _)
  · ext g
    simp [Subgroup.mem_iInf, unitSet, GM.cmp]
