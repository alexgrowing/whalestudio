import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundUnitaryAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAtOfPiInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanCoordsMovedStaySupportedAndRecovered
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.MovSize

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

abbrev Zs (F : Type) [Field F] [NumberField F] (n d : ℕ) : Type :=
  (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)

theorem infAd_add (a b : mixedEmbedding.mixedSpace F) : infAd F (a + b) = infAd F a + infAd F b := by
  unfold infAd
  rw [map_add, map_add]
  rfl

theorem infAd_smul (t : ℝ) (a : mixedEmbedding.mixedSpace F) : infAd F (t • a) = realAd F t * infAd F a := by
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • a) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a
    rw [← map_mul, Algebra.smul_def]
  · show (0 : FiniteAdeleRing (𝓞 F) F) = 0 * 0
    rw [mul_zero]

theorem liftI_add (M : Model σ X W) (ζ ζ' : Zs F n d) : liftI M (ζ + ζ') = liftI M ζ + liftI M ζ' := by
  unfold liftI
  rw [← map_add]
  congr 1
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [infAd_add]

theorem liftI_smul (M : Model σ X W) (t : ℝ) (ζ : Zs F n d) : liftI M (t • ζ) = realAd F t • liftI M ζ := by
  unfold liftI
  rw [← LinearEquiv.map_smul]
  congr 1
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [infAd_smul]

theorem arch_e_liftI (M : Model σ X W) (ζ : Zs F n d) :
    (arch F (M.co.e (liftI M ζ)).1, arch F (M.co.e (liftI M ζ)).2) = ζ := by
  unfold liftI arch
  rw [LinearEquiv.apply_symm_apply]
  refine Prod.ext ?_ ?_ <;> funext i <;>
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

variable (τ : ∀ w : InfinitePlace F, EmbOver E w)

def readC (M : Model σ X W) : Zs F n d →ₗ[ℝ] (InfinitePlace F → Fin n → Fin d → ℂ) where
  toFun ζ w i j := piInf (τ w) (liftI M ζ i j)
  map_add' ζ ζ' := by funext w i j; simp [liftI_add, map_add]
  map_smul' t ζ := by
    funext w i j
    simp only [liftI_smul, Matrix.smul_apply, RingHom.id_apply, Pi.smul_apply]
    rw [GlobalTheory.RealScalar.piInf_realAd_smul, Complex.real_smul]

theorem readC_injective (hCM : IsCMExt F E σ) (M : Model σ X W) : Function.Injective (readC τ M) := by
  rw [injective_iff_map_eq_zero]
  intro ζ hζ
  have hA := (liftI_at_movI F E σ n d X W M 1 ζ).1
  have h0 : liftI M ζ = 0 := by
    ext i j
    refine GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hCM τ _ ?_ ?_
    · intro a ha
      have := congrFun (congrFun (hA a ha) i) j
      simpa [Matrix.smul_apply] using this
    · intro w
      exact congrFun (congrFun (congrFun hζ w) i) j
  rw [← arch_e_liftI M ζ, h0, map_zero]
  refine Prod.ext ?_ ?_ <;> funext i <;> exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem norm_piInf_eq (hCM : IsCMExt F E σ) {w : InfinitePlace F} (τ₀ τ' : EmbOver E w) (z : AE F E) :
    ‖piInf τ' z‖ = ‖piInf τ₀ z‖ := by
  unfold piInf
  rcases infEmb_eq_or_conj hCM τ₀ τ' with e | e
  · rw [RingHom.comp_apply, RingHom.comp_apply, e]
  · rw [RingHom.comp_apply, RingHom.comp_apply, e, RingHom.comp_apply, Complex.norm_conj]

end GlobalTheory.ArchDecay.MovSize

open GlobalTheory.ArchDecay.MovSize in

theorem GlobalTheory.ArchDecay.movI_size : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∃ (C : ℝ) (k : ℕ), ∀ (g : UA σ X.J) (h : UA σ W.J) (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)), ‖movI M (g, h) ζ‖ ≤ C * ((ht g : ℝ) * ht h) ^ k * ‖ζ‖ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hCM : IsCMExt F E σ := hP.base.cm
  set L := readC B.emb M with hL
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith (LinearMap.ker_eq_bot.2 (readC_injective B.emb hCM M))
  set Lc := LinearMap.toContinuousLinearMap L with hLc
  refine ⟨K * (n * d) * ‖Lc‖, 1, fun g h ζ => ?_⟩
  have h1 : ‖movI M (g, h) ζ‖ ≤ K * ‖L (movI M (g, h) ζ)‖ := by
    have := hK.le_mul_dist (movI M (g, h) ζ) 0
    simpa [dist_eq_norm] using this
  have hB : ∀ (w : InfinitePlace F) (τ' : EmbOver E w) k l, ‖piInf τ' (liftI M ζ k l)‖ ≤ ‖L ζ‖ := by
    intro w τ' k l
    rw [norm_piInf_eq hCM (B.emb w) τ']
    exact (norm_le_pi_norm (L ζ w k) l).trans ((norm_le_pi_norm (L ζ w) k).trans (norm_le_pi_norm (L ζ) w))
  have hg : (ht (((g, h)⁻¹ : UA σ X.J × UA σ W.J)).1 : ℝ) = ht g := by
    show ((heightGL F ((g⁻¹ : UA σ X.J) : GL (Fin n) (AE F E))) : ℝ) = heightGL F (g : GL (Fin n) (AE F E))
    rw [Subgroup.coe_inv, heightGL_inv]
  have hh : (ht (((g, h)⁻¹ : UA σ X.J × UA σ W.J)).2 : ℝ) = ht h := by
    show ((heightGL F ((h⁻¹ : UA σ W.J) : GL (Fin d) (AE F E))) : ℝ) = heightGL F (h : GL (Fin d) (AE F E))
    rw [Subgroup.coe_inv, heightGL_inv]
  have hgh : (0 : ℝ) ≤ n * d * ((ht g : ℝ) * ht h) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))
  have hpos : (0 : ℝ) ≤ n * d * ((ht g : ℝ) * ht h) * ‖L ζ‖ := mul_nonneg hgh (norm_nonneg _)
  have h2 : ‖L (movI M (g, h) ζ)‖ ≤ n * d * ((ht g : ℝ) * ht h) * ‖L ζ‖ := by
    refine (pi_norm_le_iff_of_nonneg hpos).2 fun w => ?_
    refine (pi_norm_le_iff_of_nonneg hpos).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg hpos).2 fun j => ?_
    show ‖piInf (B.emb w) (liftI M (movI M (g, h) ζ) i j)‖ ≤ _
    rw [(liftI_at_movI F E σ n d X W M (g, h) ζ).2]
    have := GlobalTheory.WeilDirBound.norm_piInf_actAB_le σ n d X.J W.J (g, h)⁻¹ (liftI M ζ) ‖L ζ‖ (norm_nonneg _) hB w
      (B.emb w) i j
    rwa [hg, hh] at this
  have h3 : ‖L ζ‖ ≤ ‖Lc‖ * ‖ζ‖ := Lc.le_opNorm ζ
  have hK0 : (0 : ℝ) ≤ K := K.2
  calc ‖movI M (g, h) ζ‖ ≤ K * (n * d * ((ht g : ℝ) * ht h) * (‖Lc‖ * ‖ζ‖)) :=
        h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hgh)) hK0)
    _ = K * (n * d) * ‖Lc‖ * ((ht g : ℝ) * ht h) ^ 1 * ‖ζ‖ := by ring
