import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFirstColumnPositive
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open IsDedekindDomain

noncomputable section
namespace GlobalTheory.EisMidHt
open GlobalTheory.Doubling (absEv absEw unitFin unitInf)

theorem ht_iwasawa_anyDim : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → IsHermND σ J → IsWittFrame σ J X Y →
    GlobalTheory.EisLine.IsAdapted σ J X Y L a → IsIwaHtG σ J (col0 X) L a h →
      0 < GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) ∧
      ∀ g : GAd σ J, h g * GlobalTheory.EisMidHt.ht L a ((matHom _ σ J g⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) =
        GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hCM _ hJ hW hA hI
  have hx0 : firstColumn X ≠ 0 := by
    intro e
    have h1 := congrFun (congrFun hW.xy 0) 0
    have h2 : (Formalism.UG.cT (σ : E →+* E) X * J * Y) 0 0 = 0 := by
      simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Finset.sum_eq_zero fun i _ => by rw [show X i 0 = 0 from congrFun e i, map_zero, zero_mul], zero_mul]
    rw [h2] at h1
    simp at h1
  obtain ⟨hfin, hpos⟩ := normFin_first_column_finite_pos σ J X Y L a hCM hJ hW hA
  set u := adVec F (firstColumn X) with hu
  have hfinR : (Function.mulSupport fun v => (normFin F L v (fun i => compFin F E v (u i)) : ℝ)).Finite :=
    hfin.subset (fun v hv => fun e => hv (by simp [e]))
  refine ⟨mul_pos ?_ (Finset.prod_pos fun w _ => normInf_adVec_pos σ hCM a w _ hx0), fun g => ?_⟩
  · rw [finprod_eq_prod _ hfinR]
    exact Finset.prod_pos fun v _ => by exact_mod_cast hpos v
  · obtain ⟨p, l, hpl, k, hk, rfl⟩ := hI.1 g
    rw [hI.2 p l hpl k hk]
    have hpv : (matHom _ σ J p).1 *ᵥ u = l.1 • u := by
      funext i
      have := congrFun (congrFun hpl i) 0
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hu, adVec, firstColumn, col0] using this
    have hpinv : (matHom _ σ J p⁻¹).1 *ᵥ u = (l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u := by
      have e1 : (matHom _ σ J p⁻¹).1 *ᵥ ((matHom _ σ J p).1 *ᵥ u) = u := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
          Matrix.one_mulVec]
      rw [hpv, Matrix.mulVec_smul] at e1
      calc _ = (l⁻¹ : (AF F ⊗[F] E)ˣ).1 • (l.1 • (matHom _ σ J p⁻¹).1 *ᵥ u) := by
            rw [smul_smul, Units.inv_mul, one_smul]
        _ = _ := by rw [e1]
    have hg : (matHom _ σ J (p * k)⁻¹).1 *ᵥ u = (matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u) := by
      rw [mul_inv_rev, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hpinv]
    rw [hg]
    have hk' := mem_levelAll.1 (inv_mem hk)
    have hfv : ∀ v, normFin F L v (fun i => compFin F E v (((matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u)) i)) =
        absEv F E v (unitFin F E v l⁻¹) * normFin F L v (fun i => compFin F E v (u i)) := by
      intro v
      have e : (fun i => compFin F E v (((matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u)) i)) =
          (matHom _ σ J (proj σ J v k⁻¹)).1 *ᵥ ((unitFin F E v l⁻¹ : Fv F v ⊗[F] E) • fun i => compFin F E v (u i)) := by
        funext i
        rw [RingHom.map_mulVec, matHom_proj]
        congr 1
        funext j
        simp [GlobalTheory.Doubling.unitFin]
      rw [e, normFin_stab σ J L v _ (hk'.1 v), normFin_unit_smul]
    have hiw : ∀ w, normInf a w (fun i => compInf F E w (((matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u)) i)) =
        absEw F E w (unitInf F E w l⁻¹) * normInf a w (fun i => compInf F E w (u i)) := by
      intro w
      have e : (fun i => compInf F E w (((matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u)) i)) =
          (matHom _ σ J (projArch σ J w k⁻¹)).1 *ᵥ ((unitInf F E w l⁻¹ : w.Completion ⊗[F] E) • fun i => compInf F E w (u i)) := by
        funext i
        rw [RingHom.map_mulVec, matHom_projArch]
        congr 1
        funext j
        simp [GlobalTheory.Doubling.unitInf]
      rw [e, normInf_stab σ J hCM a w _ (hk'.2 w), normInf_unit_smul]
    unfold ht
    simp only [hfv, hiw, NNReal.coe_mul]
    have hA1 : (Function.mulSupport fun v => ((absEv F E v (unitFin F E v l⁻¹) : ℝ≥0) : ℝ)).Finite :=
      (GlobalTheory.Doubling.finite_mulSupport_absEv l⁻¹).subset (fun v hv => by
        simp only [Function.mem_mulSupport, ne_eq, NNReal.coe_eq_one] at hv ⊢; exact hv)
    rw [finprod_mul_distrib hA1 hfinR, Finset.prod_mul_distrib]
    have hl : (absE F E l : ℝ) * ((∏ w, (absEw F E w (unitInf F E w l⁻¹) : ℝ)) *
        ∏ᶠ v, (absEv F E v (unitFin F E v l⁻¹) : ℝ)) = 1 := by
      have h1 : (absE F E l : ℝ) * (absE F E l⁻¹ : ℝ) = 1 := by
        rw [← NNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, NNReal.coe_one]
      have h2 := NNReal.toRealHom.toMonoidHom.map_finprod (GlobalTheory.Doubling.finite_mulSupport_absEv l⁻¹)
      have e2 : (absE F E l⁻¹ : ℝ) = (∏ w, (absEw F E w (unitInf F E w l⁻¹) : ℝ)) *
          ∏ᶠ v, (absEv F E v (unitFin F E v l⁻¹) : ℝ) := by
        rw [GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]
        congr 1
      rw [← e2]
      exact h1
    calc _ = ((absE F E l : ℝ) * ((∏ w, (absEw F E w (unitInf F E w l⁻¹) : ℝ)) *
          ∏ᶠ v, (absEv F E v (unitFin F E v l⁻¹) : ℝ))) *
          ((∏ᶠ v, (normFin F L v (fun i => compFin F E v (u i)) : ℝ)) *
            ∏ w, normInf a w (fun i => compInf F E w (u i))) := by ring
      _ = _ := by rw [hl, one_mul]
end GlobalTheory.EisMidHt

end
