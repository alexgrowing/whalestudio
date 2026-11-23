import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace ColumnBlockEquiv

section Ring

variable {R : Type} [CommRing R] {a : ℕ}

theorem pm_col (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (i k : Fin a) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y i k =
      if hik : (i : ℕ) < m ∧ (k : ℕ) = m then y ⟨(i, k), hik.1, hik.2.ge, hik.2.le⟩ else 0 := by
  rw [posM, Matrix.sum_apply]
  split_ifs with hik
  · rw [Finset.sum_eq_single ⟨(i, k), hik.1, hik.2.ge, hik.2.le⟩]
    · simp
    · intro b _ hb
      rw [Matrix.single_apply, if_neg]
      rintro ⟨h1, h2⟩
      exact hb (Subtype.ext (Prod.ext h1 h2))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [Matrix.single_apply, if_neg]
    rintro ⟨h1, h2⟩
    apply hik
    have := t.2
    rw [← h1, ← h2]
    omega

theorem pm_mul_apply {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) (y : ι → R)
    (M : Matrix (Fin a) (Fin a) R) (i k : Fin a) :
    (posM p y * M) i k = ∑ s, if (p s).1 = i then y s * M (p s).2 k else 0 := by
  simp only [posM, Matrix.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : (p s).1 = i
  · subst h
    simp [Matrix.single_mul_apply_same]
  · rw [if_neg h, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply, if_neg (fun e => h e.1), zero_mul]

theorem mul_pm_apply {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) (y : ι → R)
    (M : Matrix (Fin a) (Fin a) R) (i k : Fin a) :
    (M * posM p y) i k = ∑ s, if (p s).2 = k then M i (p s).1 * y s else 0 := by
  simp only [posM, Matrix.mul_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : (p s).2 = k
  · subst h
    simp [Matrix.mul_single_apply_same]
  · rw [if_neg h, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply, if_neg (fun e => h e.2), mul_zero]

theorem pm_mul_row (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ j k : Fin a, (j : ℕ) = m → M j k = (1 : Matrix (Fin a) (Fin a) R) j k) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y * M = posM Subtype.val y := by
  ext i k
  have e := pm_mul_apply (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y 1 i k
  rw [Matrix.mul_one] at e
  rw [e, pm_mul_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hM s.1.2 k (by have := s.2; omega)]

theorem mul_posM_blockColumn (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (h : GL (Fin a) R) (hB : GlobalTheory m h) :
    h.val * posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y =
      posM Subtype.val (fun t : UnipotentBlockColumnIndex a m m => ∑ s, h.val t.1.1 s.1.1 * y s) := by
  ext i k
  rw [mul_pm_apply, pm_col]
  split_ifs with hc
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [if_pos (Fin.ext (by have := s.2; omega))]
  · refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs with hs
    · have h2 := s.2
      have hk : (k : ℕ) = m := by rw [← hs]; omega
      have hi : m ≤ (i : ℕ) := by
        by_contra hh
        exact hc ⟨by omega, hk⟩
      rw [hB i s.1.1 (Or.inl hi), Matrix.one_apply_ne, zero_mul]
      intro e
      rw [← e] at h2
      omega
    · rfl

theorem conj_blkU (m : ℕ) (h : GL (Fin a) R) (hB : GlobalTheory m h) (y : UnipotentBlockColumnIndex a m m → R) :
    h * blkU y * h⁻¹ = blkU (fun t : UnipotentBlockColumnIndex a m m => ∑ s, h.val t.1.1 s.1.1 * y s) := by
  have e : h * blkU y = blkU (fun t : UnipotentBlockColumnIndex a m m => ∑ s, h.val t.1.1 s.1.1 * y s) * h := by
    apply Units.ext
    show h.val * (1 + posM Subtype.val y) = (1 + posM Subtype.val _) * h.val
    rw [mul_add, add_mul, mul_one, one_mul,
      pm_mul_row m _ h.val (fun j k hj => hB j k (Or.inl hj.ge)), mul_posM_blockColumn m y h hB]
  rw [e, mul_inv_cancel_right]

end Ring

def colEquiv (k j : ℕ) (hj : j < k) : UnipotentBlockColumnIndex k j j ≃ Fin j where
  toFun t := ⟨t.1.1.val, t.2.1⟩
  invFun i := ⟨(⟨i.val, i.2.trans hj⟩, ⟨j, hj⟩), i.2, le_rfl, le_rfl⟩
  left_inv t := Subtype.ext (Prod.ext rfl (Fin.ext (by
    have := t.2.2
    change j = (t.1.2 : ℕ)
    omega)))
  right_inv i := Fin.ext rfl

end ColumnBlockEquiv

theorem algebraic_modulus_one_of_finiteOrder_char : AdelicLinearChange → CornerEmbedding → ColumnConjugationMeasure := by
  intro hM hK E _ _ _ k j hj g hg F hF
  have hK' := hK E k j hj.le
  obtain ⟨ι, hι⟩ := hK'.1 (Ad E)
  have hK2 := hK'.2 ι hι
  obtain ⟨g', rfl⟩ := hK2.2.2.1 g hg
  have hDt : Dt (ι g') = Dt g' := hK2.2.2.2.1 g'
  let e : UnipotentBlockColumnIndex k j j ≃ Fin j := ColumnBlockEquiv.colEquiv k j hj
  let Φ := MeasurableEquiv.piCongrLeft (fun _ : Fin j => Ad E) e
  have hΦ : MeasurePreserving Φ (vecMeasure E (UnipotentBlockColumnIndex k j j)) (vecMeasure E (Fin j)) :=
    measurePreserving_piCongrLeft (fun _ : Fin j => GroundTheory.Global.adeleMeasure E) e
  have key : ∀ H : (UnipotentBlockColumnIndex k j j → Ad E) → ℝ≥0∞,
      ∫⁻ y, H y ∂vecMeasure E (UnipotentBlockColumnIndex k j j) = ∫⁻ v, H (Φ.symm v) ∂vecMeasure E (Fin j) := by
    intro H
    have h1 := hΦ.lintegral_comp_emb Φ.measurableEmbedding (fun v => H (Φ.symm v))
    simp only [MeasurableEquiv.symm_apply_apply] at h1
    exact h1
  have hsymm : ∀ (v : Fin j → Ad E) (t : UnipotentBlockColumnIndex k j j), Φ.symm v t = v (e t) := by
    intro v t
    rfl
  have hent : ∀ t s : UnipotentBlockColumnIndex k j j, (ι g').val t.1.1 s.1.1 = g'.val (e t) (e s) := by
    intro t s
    rw [hι g']
    exact dif_pos ⟨t.2.1, s.2.1⟩
  have hpt : ∀ v : Fin j → Ad E, ι g' * blkU (Φ.symm v) * (ι g')⁻¹ =
      blkU (fun t : UnipotentBlockColumnIndex k j j => (g'.val *ᵥ v) (e t)) := by
    intro v
    rw [PositivityTheory.AdelicQuotientData.ColumnBlockEquiv.conj_blkU j (ι g') hg]
    refine congrArg blkU (funext fun t => ?_)
    rw [show (g'.val *ᵥ v) (e t) = ∑ b, g'.val (e t) b * v b from rfl, ← e.sum_comp]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hsymm, hent t s]
  have hc : Continuous (fun v : Fin j → Ad E => (blkU (fun t : UnipotentBlockColumnIndex k j j => v (e t)) : GA E k)) :=
    (continuous_posU (isNil_blk k j j)).comp (continuous_pi fun t => continuous_apply (e t))
  have hG : Measurable (fun v : Fin j → Ad E => F (blkU (fun t : UnipotentBlockColumnIndex k j j => v (e t)))) :=
    hF.comp hc.measurable
  calc ∫⁻ x, F (ι g' * blkU x * (ι g')⁻¹) ∂vecMeasure E (UnipotentBlockColumnIndex k j j)
      = ∫⁻ v, F (ι g' * blkU (Φ.symm v) * (ι g')⁻¹) ∂vecMeasure E (Fin j) :=
        key (fun x => F (ι g' * blkU x * (ι g')⁻¹))
    _ = ∫⁻ v, F (blkU (fun t : UnipotentBlockColumnIndex k j j => (g'.val *ᵥ v) (e t))) ∂vecMeasure E (Fin j) :=
        lintegral_congr fun v => by rw [hpt v]
    _ = ENNReal.ofReal (Dt g')⁻¹ *
          ∫⁻ v, F (blkU (fun t : UnipotentBlockColumnIndex k j j => v (e t))) ∂vecMeasure E (Fin j) :=
        (hM E j g' _ hG).1
    _ = ENNReal.ofReal (Dt (ι g'))⁻¹ * ∫⁻ x, F (blkU x) ∂vecMeasure E (UnipotentBlockColumnIndex k j j) := by
        rw [hDt, key (fun x => F (blkU x))]
        congr 1

end PositivityTheory.AdelicQuotientData

end
