import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetRationalProductOfLocalLevels

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem eq_one_of_cong {L : Type} [Field L] [NumberField L] [IsCMField L] (m : ℕ) (hm : 3 ≤ m) (δ : L)
    (hδ : δ * IsCMField.complexConj L δ = 1)
    (h : ∀ w : HeightOneSpectrum (𝓞 L), ∃ a ∈ w.adicCompletionIntegers L,
      algebraMap L (w.adicCompletion L) δ - 1 = (m : w.adicCompletion L) * a) : δ = 1 := by
  have hm0 : (m : L) ≠ 0 := by
    have : m ≠ 0 := by omega
    exact_mod_cast this
  have hx : ∀ v : HeightOneSpectrum (𝓞 L), v.valuation L ((δ - 1) / m) ≤ 1 := by
    intro v
    obtain ⟨a, ha, e⟩ := h v
    have hma : (m : v.adicCompletion L) = algebraMap L (v.adicCompletion L) (m : L) := by simp
    have hm0' : (m : v.adicCompletion L) ≠ 0 := by
      rw [hma]
      exact (map_ne_zero _).2 hm0
    have hxa : algebraMap L (v.adicCompletion L) ((δ - 1) / m) = a := by
      rw [map_div₀, map_sub, map_one, e, ← hma]
      field_simp
    have hval : Valued.v (algebraMap L (v.adicCompletion L) ((δ - 1) / m)) = v.valuation L ((δ - 1) / m) :=
      v.valuedAdicCompletion_eq_valuation' _
    rw [← hval, hxa]
    exact ha
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one L _ hx
  by_contra hne
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    have : δ - 1 = 0 := by
      have := hy.symm
      rwa [div_eq_zero_iff, or_iff_left hm0] at this
    exact hne (sub_eq_zero.1 this)
  have hlt : ∀ z : InfinitePlace L, z ((y : 𝓞 L) : L) < 1 := by
    intro z
    have hyx : ((y : 𝓞 L) : L) = (δ - 1) / m := hy
    have hn : ‖z.embedding δ‖ = 1 := by
      have e1 : z.embedding δ * (starRingEnd ℂ) (z.embedding δ) = 1 := by
        rw [← IsCMField.complexEmbedding_complexConj, ← map_mul, hδ, map_one]
      have e2 := congrArg norm e1
      rw [norm_mul, Complex.norm_conj, norm_one] at e2
      nlinarith [norm_nonneg (z.embedding δ)]
    rw [← InfinitePlace.norm_embedding_eq, hyx, map_div₀, map_sub, map_one, map_natCast, norm_div,
      Complex.norm_natCast]
    have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    rw [div_lt_one (by linarith)]
    have := norm_sub_le (z.embedding δ) 1
    rw [hn, norm_one] at this
    linarith
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace L) := inferInstance
  have := InfinitePlace.one_le_of_lt_one (w := w₀) hy0 (fun z _ => hlt z)
  linarith [hlt w₀]

private theorem det_cong {L : Type} [Field L] [NumberField L] [IsCMField L] {m : ℕ} {w : HeightOneSpectrum (𝓞 L)}
    (M : Matrix (Fin 2) (Fin 2) (w.adicCompletion L))
    (h : ∀ i j, ∃ a ∈ w.adicCompletionIntegers L, (M - 1) i j = (m : w.adicCompletion L) * a) :
    ∃ a ∈ w.adicCompletionIntegers L, M.det - 1 = (m : w.adicCompletion L) * a := by
  obtain ⟨a, ha, ea⟩ := h 0 0
  obtain ⟨b, hb, eb⟩ := h 0 1
  obtain ⟨c, hc, ec⟩ := h 1 0
  obtain ⟨d, hd, ed⟩ := h 1 1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at ea eb ec ed
  have hmO : (m : w.adicCompletion L) ∈ w.adicCompletionIntegers L := natCast_mem _ m
  refine ⟨a + d + m * (a * d - b * c), add_mem (add_mem ha hd) (mul_mem hmO (sub_mem (mul_mem ha hd) (mul_mem hb hc))), ?_⟩
  have e0 : M 0 0 = 1 + m * a := by rw [← ea]; ring
  have e3 : M 1 1 = 1 + m * d := by rw [← ed]; ring
  rw [Matrix.det_fin_two, e0, e3, eb, ec]
  ring

theorem UpperTheory.V.Z.Sym.So.detRoot :
    UpperTheory.V.Z.Sym.So.DetRoot := by
  intro L _ _ _ m hm U hU f hf k hk hr u hu hfu
  obtain ⟨γ₀, hγ₀'⟩ := hr
  have hγ₀ : ratGL L 2 γ₀ = ((f * k : UA L 2) : GA L 2) := hγ₀'
  have hg : Formalism.UG.cT (conjAd L) ((f * k : UA L 2) : GA L 2).val * 1 * ((f * k : UA L 2) : GA L 2).val = 1 := (f * k).2
  rw [← hγ₀, mul_one] at hg
  have hv : (ratGL L 2 γ₀).val = γ₀.val.map (algebraMap L (Ad L)) := rfl
  rw [hv, GlobalTheory.DefU.ClassFin.cT_map (algebraMap L (Ad L)) (IsCMField.complexConj L).toRingEquiv.toRingHom (conjAd L)
    (fun y => (conjAd_algebraMap y).symm), ← Matrix.map_mul] at hg
  haveI hnt : Nontrivial (Ad L) := show Nontrivial (InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L) from inferInstance
  have hUL : Formalism.UG.cT (IsCMField.complexConj L).toRingEquiv.toRingHom γ₀.val * γ₀.val = 1 := by
    ext i j
    have := congrFun₂ hg i j
    rw [Matrix.map_apply, Matrix.one_apply] at this
    rw [Matrix.one_apply]
    apply (algebraMap L (Ad L)).injective
    rw [this]
    split_ifs <;> simp
  have hδ : γ₀.val.det * IsCMField.complexConj L γ₀.val.det = 1 := by
    have := congrArg Matrix.det hUL
    rw [Matrix.det_mul, Matrix.det_one] at this
    have hc : (Formalism.UG.cT (IsCMField.complexConj L).toRingEquiv.toRingHom γ₀.val).det = IsCMField.complexConj L γ₀.val.det := by
      simp only [Formalism.UG.cT, Matrix.det_transpose]
      exact (RingHom.map_det (IsCMField.complexConj L).toRingEquiv.toRingHom γ₀.val).symm
    rw [hc] at this
    rw [mul_comm]
    exact this
  have hD : (f : GA L 2).val.det * (k : GA L 2).val.det = algebraMap L (Ad L) γ₀.val.det := by
    rw [RingHom.map_det]
    have h2 : (γ₀.val.map (algebraMap L (Ad L))) = ((f * k : UA L 2) : GA L 2).val := by rw [← hv, hγ₀]
    change _ = (γ₀.val.map (algebraMap L (Ad L))).det
    rw [h2, ← Matrix.det_mul]
    rfl
  have hkF : pFin L (k : GA L 2).val.det = 1 := by
    have hk' : Matrix.GeneralLinearGroup.map (pFin L) (k : GA L 2) = 1 := hk
    rw [RingHom.map_det]
    have := congrArg (fun g : GL (Fin 2) (Af L) => g.val.det) hk'
    simpa using this
  have hfI : pInf L (f : GA L 2).val.det = 1 := by
    have hf' : Matrix.GeneralLinearGroup.map (pInf L) (f : GA L 2) = 1 := hf
    rw [RingHom.map_det]
    have := congrArg (fun g : GL (Fin 2) (Cinf L) => g.val.det) hf'
    simpa using this
  have hdu : (f : GA L 2).val.det * (u : GA L 2).val.det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det ((f * u : UA L 2) : GA L 2) = 1 := hfu
    have := congrArg Units.val h1
    simpa using this
  have huv : (u : GA L 2).val.det * ((u⁻¹ : UA L 2) : GA L 2).val.det = 1 := by
    rw [← Matrix.det_mul]
    have : (u : GA L 2).val * ((u⁻¹ : UA L 2) : GA L 2).val = 1 := by
      have := congrArg (fun x : UA L 2 => (x : GA L 2).val) (mul_inv_cancel u)
      simpa using this
    rw [this, Matrix.det_one]
  have hfv : (f : GA L 2).val.det = ((u⁻¹ : UA L 2) : GA L 2).val.det := by
    calc _ = (f : GA L 2).val.det * ((u : GA L 2).val.det * ((u⁻¹ : UA L 2) : GA L 2).val.det) := by rw [huv, mul_one]
      _ = _ := by rw [← mul_assoc, hdu, one_mul]
  have hcong : ∀ w : HeightOneSpectrum (𝓞 L), ∃ a ∈ w.adicCompletionIntegers L,
      algebraMap L (w.adicCompletion L) γ₀.val.det - 1 = (m : w.adicCompletion L) * a := by
    intro w
    have hmem := ((hU (u⁻¹)).1 (U.inv_mem hu)).2 w
    obtain ⟨a, ha, e⟩ := det_cong (mL w (u⁻¹ : UA L 2)) hmem
    refine ⟨a, ha, ?_⟩
    rw [← e]
    have e1 : (mL w (u⁻¹ : UA L 2)).det = pLoc L w (pFin L ((u⁻¹ : UA L 2) : GA L 2).val.det) := by
      rw [← RingHom.comp_apply, RingHom.map_det]
      rfl
    have e2 : algebraMap L (w.adicCompletion L) γ₀.val.det = pLoc L w (pFin L (algebraMap L (Ad L) γ₀.val.det)) := rfl
    rw [e1, e2, ← hD, hfv, map_mul, hkF, mul_one]
  have h1 : γ₀.val.det = 1 := eq_one_of_cong m hm _ hδ hcong
  rw [h1, map_one] at hD
  have hfF : pFin L (f : GA L 2).val.det = 1 := by
    have := congrArg (pFin L) hD
    rwa [map_mul, hkF, mul_one, map_one] at this
  have hf1 : (f : GA L 2).val.det = 1 := by
    refine Prod.ext ?_ hfF
    apply (infEq L).symm.injective
    have e : (infEq L).symm ((1 : Ad L).1) = 1 := map_one _
    exact hfI.trans e.symm
  have hk1 : (k : GA L 2).val.det = 1 := by rwa [hf1, one_mul] at hD
  refine ⟨?_, ?_⟩
  · refine MonoidHom.mem_ker.2 (Units.ext ?_)
    exact hf1
  · refine MonoidHom.mem_ker.2 (Units.ext ?_)
    exact hk1

end
