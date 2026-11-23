import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximumHolds

namespace ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma span_le_of_upper (p : ℕ) (hp : p ≤ r) (M N : Matrix (Fin r) (Fin r) ℂ) (hN : N.BlockTriangular id) :
    Submodule.span ℂ (Set.range fun a : Fin p => col (M * N) (Fin.castLE hp a)) ≤
      Submodule.span ℂ (Set.range fun a : Fin p => col M (Fin.castLE hp a)) := by
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have hcol : col (M * N) (Fin.castLE hp a) = ∑ j : Fin r, N j (Fin.castLE hp a) • col M j := by
    funext i
    simp only [col, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  show col (M * N) (Fin.castLE hp a) ∈ Submodule.span ℂ (Set.range fun a : Fin p => col M (Fin.castLE hp a))
  rw [hcol]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  by_cases hj : (j : ℕ) < p
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, congrArg (col M) (Fin.ext rfl)⟩)
  · have hlt : Fin.castLE hp a < j := Fin.lt_iff_val_lt_val.mpr (by show (a : ℕ) < j; omega)
    have h0 : N j (Fin.castLE hp a) = 0 := hN hlt
    rw [h0, zero_smul]
    exact Submodule.zero_mem _

variable (X : Data E r)

lemma sameFlag_rmul (z : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : X.SameFlag z (rmul z b) := by
  unfold Data.SameFlag
  unfold Bor at hb
  rw [Set.mem_setOf_eq] at hb
  intro τ
  obtain ⟨hdet, htri⟩ := hb τ
  have hmul : mat (rmul z b) τ = mat z τ * mat b τ := by
    first
    | rfl
    | (unfold rmul mat; rfl)
    | (ext i j; simp [rmul, mat, Matrix.mul_apply])
  have hT : (mat b τ).BlockTriangular id := fun a c h => by
    first
    | exact htri a c h
    | (simp only [mat]; exact htri a c h)
  haveI : Invertible (mat b τ).det := invertibleOfNonzero hdet
  haveI : Invertible (mat b τ) := Matrix.invertibleOfDetInvertible _
  apply le_antisymm
  · have hinv : mat z τ = mat (rmul z b) τ * (mat b τ)⁻¹ := by
      rw [hmul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one]
    rw [hinv]
    exact span_le_of_upper _ _ _ _ (Matrix.blockTriangular_inv_of_blockTriangular hT)
  · rw [hmul]
    exact span_le_of_upper _ _ _ _ hT

lemma maj_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) : 0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · subst hv
    simp [Data.maj, Data.posPart, hermC]
  · exact (X.maj_pos hx τ hv).le

lemma rho_pos {w : ℝ} (hw1 : 1 ≤ w) (hr : 0 < r) : 0 < frameRadius w r ∧ frameRadius w r ≤ 1 / 10 := by
  unfold frameRadius
  have hwr : 1 ≤ w * (r : ℝ) := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  have hs : 1 ≤ √(w * r) := by
    first
    | exact Real.one_le_sqrt.mpr hwr
    | exact (Real.sqrt_one).symm ▸ Real.sqrt_le_sqrt hwr
  constructor
  · apply div_pos one_pos
    linarith
  · exact one_div_le_one_div_of_le (by norm_num) (by linarith)

end

end ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem frameAtMaximum_of_lower_bound (h41a : LatticeBoundAtMaximum (E := E)) (h6p1 : OrthonormalChartNormControl (E := E)) :
    FrameAtMaximum (E := E) := by
  intro r X la P z0 laStar w hP hz0 hmax hpos hw hw1 hr hl0 hl1 hMAX
  obtain ⟨b, hb, ho⟩ := (orthonormalFlagTranslate_holds r X.toData).1 z0 hz0
  have hx0 := OrthogonalFrameDomain.rmul_mem_dom X.toData hz0 hb
  have hsf : X.SameFlag z0 (rmul z0 b) := FlagSpanBounds.sameFlag_rmul X.toData z0 hb
  obtain ⟨hρ0, hρ10⟩ := FlagSpanBounds.rho_pos (r := r) hw1 hr
  obtain ⟨lam, Z, hZ, hlam⟩ :=
    h41a r X z0 (rmul z0 b) laStar (frameRadius w r) hz0 hx0 ho hsf hl0 hl1 hρ0 (by linarith) hMAX
  have hZρ : X.zN Z ≤ frameRadius w r := by linarith
  refine ⟨X.xZ (rmul z0 b) Z, lam, OrthonormalChartBounds.xZ_mem_dom X.toData hx0 ho (by linarith), hlam,
    nonvanishingNearMaximum_holds r X.toData la P z0 (rmul z0 b) w hP hz0 ho ⟨b, hb, rfl⟩ hmax hpos hw hw1 hr Z hZ,
    fun τ v => ?_⟩
  have hm := (((h6p1 r X.toData (rmul z0 b) hx0 ho (frameRadius w r) hρ0 hρ10).1 Z hZρ).2.2 τ v).2
  have hmeq := ((orthonormalFlagTranslate_holds r X.toData).2.2 z0 hz0 _ hx0 hsf).2
  rw [← hmeq] at hm
  have hnn := FlagSpanBounds.maj_nonneg X.toData hz0 τ v
  have hq : (1 + frameRadius w r) / (1 - frameRadius w r) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  exact hm.trans (mul_le_mul_of_nonneg_right hq hnn)

end ReciprocityTheory.ChartRestriction.G.FD
