import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaHeightAdaptedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinHeightSmulInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLatticeAdaptedBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaHeightAdaptedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLineCosetRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicLineCosetRepresentativesStatement
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EisMidHt

theorem midLines_sum_rpow_lt_top : GlobalTheory.Published.EisensteinIsotropicLine → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
      ∀ Yr : Set (Fin n → E), GlobalTheory.EisMidHt.IsLineReps σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn Y) Yr →
      ∀ s : ℝ, (n : ℝ) - 3 < s → ∑' y : Yr, ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F y.1) ^ (-s)) < ⊤ := by
  intro hP F E _ _ _ _ _ σ n J r X Y L a h hS Yr hY s hs
  have hS' := hS
  obtain ⟨hCM, hUn, hND, hn4, hW, hA, hI⟩ := hS
  have hnn : ∀ {k : ℕ} (L' : Submodule (𝓞 E) (Fin k → E)) (a' : GL (Fin k) (AF F ⊗[F] E)) u,
      0 ≤ GlobalTheory.EisMidHt.ht L' a' u := fun L' a' u =>
    mul_nonneg (finprod_nonneg fun _ => NNReal.coe_nonneg _)
      (Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)
  have hinj : ∀ {k : ℕ}, Function.Injective (GlobalTheory.EisMidHt.adVec F : (Fin k → E) → Fin k → AF F ⊗[F] E) := by
    intro k u v huv
    funext i
    exact Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F) (congrFun huv i)
  cases r with
  | zero =>
    have hE0 : Yr = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hy
      obtain ⟨h0, hyy, hx, hyv⟩ := hY.1 y hy
      apply h0
      refine hW.aniso y ?_ ?_ hyy
      · funext i
        fin_cases i
        simp [hE, Formalism.UG.hform, Matrix.mulVec, dotProduct, Matrix.mul_apply, Formalism.UG.cT, Finset.sum_mul,
          GlobalTheory.EisMidHt.firstColumn] at hx ⊢
        rw [Finset.sum_comm]; exact hx
      · funext i
        fin_cases i
        simp [hE, Formalism.UG.hform, Matrix.mulVec, dotProduct, Matrix.mul_apply, Formalism.UG.cT, Finset.sum_mul,
          GlobalTheory.EisMidHt.firstColumn] at hyv ⊢
        rw [Finset.sum_comm]; exact hyv
    subst hE0
    simp
  | succ r =>
    obtain ⟨m, ι, J₀, X₀, Y₀, L₀, a₀, hm, hND₀, hW₀, hA₀, hh, hsurj, hht⟩ :=
      GlobalTheory.T.wittFrame_lattice_adapted_basis F E σ n J r X Y L a hCM hUn hND hW hA
    obtain ⟨h₀, hI₀⟩ := GlobalTheory.T.iwasawa_height_adapted_lattice F E σ m J₀ r X₀ Y₀ L₀ a₀ hCM hUn hND₀ hW₀ hA₀
    obtain ⟨T, hT⟩ := GlobalTheory.T.exists_coset_representatives_adelic_line_stabilizer F E σ m J₀ (col0 X₀)
    obtain ⟨hpos, hid⟩ := GlobalTheory.T.iwasawa_height_adapted F E σ m J₀ r X₀ Y₀ L₀ a₀ h₀ hCM hUn hND₀ hW₀ hA₀ hI₀
    obtain ⟨Eis, c, h1, -⟩ :=
      hP F E σ hCM hUn m J₀ hND₀ r X₀ Y₀ hW₀ (col0 X₀) (col0 Y₀) rfl rfl L₀ a₀ hA₀ h₀ hI₀.1 hI₀.2
    have hmR : (m : ℝ) + 2 = n := by exact_mod_cast hm
    have hsum := h1 T hT ((s : ℂ) - ((m : ℂ) - 1) / 2) (by
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.div_re, Complex.natCast_re, Complex.one_re,
        Complex.natCast_im, Complex.one_im, Complex.sub_im]
      norm_num
      linarith) 1
    simp only [mul_one, sub_add_cancel] at hsum
    set H₀ := GlobalTheory.EisMidHt.ht L₀ a₀ (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X₀))
    have hpos0 : ∀ g : GAd σ J₀, 0 < h₀ g := fun g => by
      have e := hid g
      have h2 := hnn L₀ a₀ ((matHom _ σ J₀ g⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X₀))
      by_contra hc
      push_neg at hc
      have : h₀ g * GlobalTheory.EisMidHt.ht L₀ a₀ ((matHom _ σ J₀ g⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X₀)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc h2
      linarith
    have hsR : Summable (fun t : T => h₀ t.1.1 ^ s) := by
      have e : (fun t : T => ((h₀ t.1.1 : ℂ) ^ (s : ℂ))) = fun t => ((h₀ t.1.1 ^ s : ℝ) : ℂ) :=
        funext fun t => (Complex.ofReal_cpow (hpos0 _).le _).symm
      rw [e] at hsum
      exact Complex.summable_ofReal.1 hsum.summable
    have key : ∀ y : Yr, ∃ t : T, GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F y.1) * h₀ t.1.1 = H₀ ∧
        ∃ c : E, c ≠ 0 ∧ ∃ u, ι u = y.1 ∧
          (matHom _ σ J₀ (t.1 : GAd σ J₀)⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X₀) =
            GlobalTheory.EisMidHt.adVec F (c • u) := by
      intro y
      obtain ⟨h0, hyy, hx, hyv⟩ := hY.1 y.1 y.2
      obtain ⟨u, hu⟩ := hsurj y.1 hx hyv
      have hu0 : u ≠ 0 := by rintro rfl; exact h0 (by rw [← hu, map_zero])
      have huu : hE σ J₀ u u = 0 := by rw [hh, hu]; exact hyy
      obtain ⟨t, htT, c, hc, he⟩ := GlobalTheory.T.wittFrame_line_coset_representatives F E σ m J₀ r X₀ Y₀ hCM hND₀ hW₀ T hT u hu0 huu
      refine ⟨⟨t, htT⟩, ?_, c, hc, u, hu, he⟩
      have e1 := hid t.1
      rw [he, hht, map_smul, hu, GlobalTheory.T.eisenstein_height_smul_invariant F E σ n J (r + 1) X Y L a h hS' c hc] at e1
      rw [mul_comm]; exact e1
    choose f hf1 hf2 using key
    have hfinj : Function.Injective f := by
      intro y y' hyy'
      obtain ⟨c, hc, u, hu, he⟩ := hf2 y
      obtain ⟨c', hc', u', hu', he'⟩ := hf2 y'
      rw [hyy', he'] at he
      have e2 := congrArg ι (hinj he)
      rw [map_smul, map_smul, hu, hu'] at e2
      apply Subtype.ext
      refine hY.2.1 y.1 y.2 y'.1 y'.2 (c⁻¹ * c') ?_
      rw [mul_smul, e2, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hterm : ∀ y : Yr, ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F y.1) ^ (-s)) =
        ENNReal.ofReal (H₀ ^ (-s)) * ENNReal.ofReal (h₀ (f y).1.1 ^ s) := by
      intro y
      have hp := hpos0 (f y).1.1
      have e : GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F y.1) = H₀ / h₀ (f y).1.1 := by
        rw [eq_div_iff hp.ne']; exact hf1 y
      rw [e, Real.div_rpow hpos.le hp.le, Real.rpow_neg hp.le, div_eq_mul_inv, inv_inv,
        ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _)]
    calc ∑' y : Yr, ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F y.1) ^ (-s))
        = ∑' y : Yr, ENNReal.ofReal (H₀ ^ (-s)) * (fun t : T => ENNReal.ofReal (h₀ t.1.1 ^ s)) (f y) :=
          tsum_congr hterm
      _ = ENNReal.ofReal (H₀ ^ (-s)) * ∑' y : Yr, (fun t : T => ENNReal.ofReal (h₀ t.1.1 ^ s)) (f y) :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (H₀ ^ (-s)) * ∑' t : T, ENNReal.ofReal (h₀ t.1.1 ^ s) := by
          gcongr; exact ENNReal.tsum_comp_le_tsum_of_injective hfinj _
      _ < ⊤ := by
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => Real.rpow_nonneg (hpos0 _).le _) hsR]
          exact ENNReal.ofReal_lt_top

end GlobalTheory.EisMidHt

end
