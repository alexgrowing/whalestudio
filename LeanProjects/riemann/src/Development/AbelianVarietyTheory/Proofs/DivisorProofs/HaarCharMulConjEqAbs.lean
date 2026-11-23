import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCA
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharProdCongr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LeviModulus
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ImaginaryModulus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_anti {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases hx : ∃ x, σ x ≠ x
  · obtain ⟨x, hx⟩ := hx
    refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
    rw [map_sub, sig_sig h]; ring
  · push_neg at hx
    exfalso
    have hr : ComplexEmbedding.IsReal τ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq]
      have := h.2.2.2 τ x
      rw [hx x] at this
      exact this.symm
    exact InfinitePlace.isComplex_mk_iff.1 (h.2.1.isComplex _) hr

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem cA_eq_sigR (σ : E →ₐ[F] E) (z : AE F E) : cA σ z = sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => simp [cA, sigR]

section Iso

variable (σ : E →ₐ[F] E) [IsTopologicalRing (AE F E)]

def splitIm (hσ : ∀ x, σ (σ x) = x) (δ : E) (hδ0 : δ ≠ 0) (hδ : σ δ = -δ) : (imA σ × imA σ) ≃ₜ+ AE F E where
  toFun p := (p.1 : AE F E) + inclR (F := F) (AF F) δ * p.2
  invFun z := (⟨inclR (F := F) (AF F) (2⁻¹ : E) * (z - cA σ z), by
      rw [mem_imA, map_mul, map_sub, cA_inclR, cA_cA σ hσ, map_inv₀ σ 2, map_ofNat σ 2]; ring⟩,
    ⟨inclR (F := F) (AF F) (2⁻¹ : E) * inclR (F := F) (AF F) δ⁻¹ * (z + cA σ z), by
      rw [mem_imA, map_mul, map_mul, map_add, cA_inclR, cA_inclR, cA_cA σ hσ, map_inv₀ σ 2, map_inv₀ σ δ,
        map_ofNat σ 2, hδ, inv_neg, map_neg]; ring⟩)
  left_inv p := by
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
    have hh : inclR (F := F) (AF F) (2⁻¹ : E) * 2 = 1 := by
      rw [show (2 : AE F E) = inclR (F := F) (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul,
        inv_mul_cancel₀ (two_ne_zero), map_one]
    have hc : inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ0, map_one]
    have hz : cA σ (x + inclR (F := F) (AF F) δ * y) = -x + inclR (F := F) (AF F) δ * y := by
      rw [map_add, map_mul, hx, hy, cA_inclR, hδ, map_neg]; ring
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show inclR (F := F) (AF F) (2⁻¹ : E) * ((x + inclR (F := F) (AF F) δ * y) - cA σ (x + inclR (F := F) (AF F) δ * y)) = x
      rw [hz]; linear_combination x * hh
    · show inclR (F := F) (AF F) (2⁻¹ : E) * inclR (F := F) (AF F) δ⁻¹ *
        ((x + inclR (F := F) (AF F) δ * y) + cA σ (x + inclR (F := F) (AF F) δ * y)) = y
      rw [hz]
      linear_combination (y * inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹) * hh + y * hc
  right_inv z := by
    have hh : inclR (F := F) (AF F) (2⁻¹ : E) * 2 = 1 := by
      rw [show (2 : AE F E) = inclR (F := F) (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul,
        inv_mul_cancel₀ (two_ne_zero), map_one]
    have hc : inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ0, map_one]
    show inclR (F := F) (AF F) (2⁻¹ : E) * (z - cA σ z) + inclR (F := F) (AF F) δ *
      (inclR (F := F) (AF F) (2⁻¹ : E) * inclR (F := F) (AF F) δ⁻¹ * (z + cA σ z)) = z
    linear_combination z * hh + inclR (F := F) (AF F) (2⁻¹ : E) * (z + cA σ z) * hc
  map_add' p q := by
    show ((p.1 + q.1 : imA σ) : AE F E) + _ * ((p.2 + q.2 : imA σ) : AE F E) = _
    push_cast; ring
  continuous_toFun := by
    exact (continuous_subtype_val.comp continuous_fst).add
      (continuous_const.mul (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := by
    have hc := continuous_cA σ
    exact (Continuous.subtype_mk (continuous_const.mul (continuous_id.sub hc)) _).prodMk
      (Continuous.subtype_mk (continuous_const.mul (continuous_id.add hc)) _)

theorem splitIm_apply (hσ : ∀ x, σ (σ x) = x) (δ : E) (hδ0 : δ ≠ 0) (hδ : σ δ = -δ) (p : imA σ × imA σ) :
    splitIm σ hσ δ hδ0 hδ p = (p.1 : AE F E) + inclR (F := F) (AF F) δ * p.2 := rfl

end Iso

variable (F E) in

def scal [IsTopologicalRing (AE F E)] : AE F E ≃ₜ+ Matrix (Fin 1) (Fin 1) (AE F E) where
  toFun z := Matrix.of fun _ _ => z
  invFun M := M 0 0
  left_inv z := rfl
  right_inv M := by
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    rfl
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun _ => continuous_pi fun _ => continuous_id
  continuous_invFun := (continuous_apply 0).comp (continuous_apply 0)

theorem addEquivAddHaarChar_imA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ →
    ∀ [IsTopologicalRing (AE F E)] [LocallyCompactSpace (imA σ)] [MeasurableSpace (imA σ)] [BorelSpace (imA σ)]
      (l : (AE F E)ˣ) (L : imA σ ≃ₜ+ imA σ), (∀ b, (L b : AE F E) = l * cA σ l * b) → addEquivAddHaarChar L = absE F E l := by
  intro F E _ _ _ _ _ σ B hB _ _ _ _ l L hL
  have hcm := hB.cm
  haveI : IsTotallyReal F := hcm.1
  have hσ := sig_sig hcm
  obtain ⟨δ, hδ0, hδ⟩ := exists_anti hcm
  obtain ⟨-, hlc, hsc, ht2⟩ := topAE F E
  letI : MeasurableSpace (AE F E) := borel _
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin 1) (Fin 1) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 1 → Fin 1 → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin 1) (Fin 1) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin 1 → Fin 1 → AE F E))
  letI : MeasurableSpace (Matrix (Fin 1) (Fin 1) (AE F E)) := borel _
  haveI : BorelSpace (Matrix (Fin 1) (Fin 1) (AE F E)) := ⟨rfl⟩
  set Φ := splitIm σ hσ δ hδ0 hδ
  set M : AE F E ≃ₜ+ AE F E := (Φ.symm.trans (GlobalTheory.ModuLR.prodCE L L)).trans Φ
  set a : (AE F E)ˣ := l * GlobalTheory.Doubling.conjUnit σ l
  have ha : (a : AE F E) = l * cA σ l := by
    show (l : AE F E) * sigR (AF F) σ l = _
    rw [cA_eq_sigR]
  have hM : ∀ z, M z = a * z := by
    intro z
    obtain ⟨p, rfl⟩ := Φ.surjective z
    show Φ (GlobalTheory.ModuLR.prodCE L L (Φ.symm (Φ p))) = a * Φ p
    rw [ContinuousAddEquiv.symm_apply_apply, GlobalTheory.ModuLR.prodCE_apply, splitIm_apply, splitIm_apply, hL, hL, ha]
    ring
  set g : GL (Fin 1) (AE F E) := Units.map (Matrix.scalar (Fin 1) : AE F E →+* _).toMonoidHom a
  have hg : Matrix.GeneralLinearGroup.det g = a := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    rfl
  have hT : ((scal F E).symm.trans M).trans (scal F E) = GlobalTheory.ModuLR.lrCE g 1 := by
    ext u i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    show M (u 0 0) = (((g : Matrix (Fin 1) (Fin 1) (AE F E)) * u * 1 : Matrix (Fin 1) (Fin 1) (AE F E)) 0 0)
    rw [hM, Matrix.mul_one, Matrix.mul_apply, Fin.sum_univ_one]
    rfl
  have h1 : addEquivAddHaarChar M = absE F E a := by
    have := GlobalTheory.ModuLR.addEquivAddHaarChar_transport (scal F E) M
    rw [← this, hT]
    rw [GlobalTheory.ModuLR.chi_lr F E 1 1 g 1, hg, map_one, map_one]
    simp
  haveI : SecondCountableTopology (imA σ) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : T2Space (imA σ) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (imA σ × imA σ) := Prod.borelSpace
  have h2 : addEquivAddHaarChar M = addEquivAddHaarChar L * addEquivAddHaarChar L := by
    rw [GlobalTheory.ModuLR.addEquivAddHaarChar_transport Φ, GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE]
  have h3 : absE F E a = absE F E l * absE F E l := by
    rw [map_mul, GlobalTheory.Doubling.absE_conjUnit]
  exact (mul_self_inj (by positivity) (by positivity)).1 (h2.symm.trans (h1.trans h3))

end GlobalTheory.ImaginaryModulus
