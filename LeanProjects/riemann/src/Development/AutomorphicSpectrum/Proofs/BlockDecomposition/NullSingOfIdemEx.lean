import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingMultiplicative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFieldIdemOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureUnitImage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureComplementImageEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointEqTranslate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PieceMeasureLtTop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDependentColumn
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GUEqOneAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGlGD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompInfSingleInfSelf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFrameLeftInvGram
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

theorem scale_image {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] (ν : Measure Z) (φ : Z ≃ₜ Z) (s : ℝ≥0)
    (h : ν.map φ = s • ν) (B : Set Z) : (s : ℝ≥0∞) * ν (φ '' B) = ν B := by
  have h1 : (ν.map φ) (φ '' B) = ν B := by
    have h2 := φ.toMeasurableEquiv.map_apply (μ := ν) (φ '' B)
    have h3 : (φ.toMeasurableEquiv : Z → Z) ⁻¹' (φ '' B) = B := by
      ext x; simp
    rw [h3] at h2
    exact h2
  rw [h] at h1
  rw [← h1, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

section
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {a r t : ℕ}

def colH (g : GL (Fin t) A) : (Fx A a r × Fx A a t) ≃ₜ (Fx A a r × Fx A a t) where
  toFun z := (z.1, z.2 * g.1)
  invFun z := (z.1, z.2 * (g⁻¹).1)
  left_inv z := by
    have : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp [Matrix.mul_assoc, this]
  right_inv z := by
    have : (g⁻¹).1 * g.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp [Matrix.mul_assoc, this]
  continuous_toFun := continuous_fst.prodMk (continuous_snd.matrix_mul continuous_const)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.matrix_mul continuous_const)

def shH (y : Fx A r t) : (Fx A a r × Fx A a t) ≃ₜ (Fx A a r × Fx A a t) where
  toFun z := (z.1, z.2 + z.1 * y)
  invFun z := (z.1, z.2 - z.1 * y)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (continuous_fst.matrix_mul continuous_const))

end

section
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {a r t : ℕ}
  [MeasurableSpace (Fx A a r)] [MeasurableSpace (Fx A a t)] [BorelSpace (Fx A a r × Fx A a t)]

theorem exists_strictHenselian_absolutely_closed_local_ring (md : Aˣ →* ℝ≥0) (e : A) (ν : Measure (Fx A a r × Fx A a t))
    (invS : ∀ y : Fx A r t, e • y = y → ν.map (fun z : Fx A a r × Fx A a t => (z.1, z.2 + z.1 * y)) = ν)
    (cov : ∀ g : GL (Fin t) A, e • (g.1 - 1) = g.1 - 1 → ν.map (fun z : Fx A a r × Fx A a t => (z.1, z.2 * g.1)) =
      ((md (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (r + t) : ℝ≥0) • ν) (i : Fin t) (c₀ : Fin t → A) (y₀ : Fin r → A)
    (hc₀ : c₀ i = 0) (hce : ∀ k, e * c₀ k = c₀ k) (hye : ∀ l, e * y₀ l = y₀ l) :
    ∃ φ : (Fx A a r × Fx A a t) ≃ₜ (Fx A a r × Fx A a t), ν.map φ = ν ∧
      ∀ w, φ w = (w.1, w.2 * gU i c₀ + w.1 * yU i y₀) := by
  obtain ⟨g, hg, hdet⟩ := GlobalTheory.CompanionTheory.NullFr.exists_GL_gU i c₀ hc₀
  have h1 : e • (g.1 - 1) = g.1 - 1 := by
    rw [hg]
    ext k j
    simp only [gU, add_sub_cancel_left, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    split_ifs <;> simp [hce]
  have h2 : e • yU i y₀ = (yU i y₀ : Fx A r t) := by
    ext l j
    simp only [yU, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    split_ifs <;> simp [hye]
  have c1 : ν.map (colH (a := a) (r := r) g) = ν := by
    have := cov g h1
    rw [hdet, map_one, inv_one, one_pow, one_smul] at this
    exact this
  have c2 : ν.map (shH (a := a) (yU i y₀ : Fx A r t)) = ν := invS _ h2
  refine ⟨(colH g).trans (shH (yU i y₀)), ?_, fun w => ?_⟩
  · have m1 : Measurable (colH (a := a) (r := r) g) := (colH g).continuous.measurable
    have m2 : Measurable (shH (a := a) (yU i y₀ : Fx A r t)) := (shH _).continuous.measurable
    have : (((colH (a := a) (r := r) g).trans (shH (yU i y₀)) : _ ≃ₜ _) : _ → _) = shH (yU i y₀) ∘ colH g := rfl
    rw [this, ← Measure.map_map m2 m1, c1, c2]
  · show (w.1, w.2 * g.1 + w.1 * yU i y₀) = _
    rw [hg]
end

section
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A] [T2Space A]
  [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] {a r t : ℕ}
  [MeasurableSpace (Fx A a r)] [MeasurableSpace (Fx A a t)] [BorelSpace (Fx A a r × Fx A a t)]

theorem piece_null (md : Aˣ →* ℝ≥0) (hmd : IsHaarMod md) (e f : A) (he : e * e = e) (hfe : f * e = f) (hf : IsFieldIdem f)
    (hnd : NonDiscreteAt f) (P : Fx A a r → Fx A r a) (ν : Measure (Fx A a r × Fx A a t)) (hfin : IsFiniteMeasureOnCompacts ν)
    (invS : ∀ y : Fx A r t, e • y = y → ν.map (fun z : Fx A a r × Fx A a t => (z.1, z.2 + z.1 * y)) = ν)
    (cov : ∀ g : GL (Fin t) A, e • (g.1 - 1) = g.1 - 1 → ν.map (fun z : Fx A a r × Fx A a t => (z.1, z.2 * g.1)) =
      ((md (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (r + t) : ℝ≥0) • ν) (i : Fin t) (C : Set A) (hC : IsCompact C)
    (hC0 : C ∈ 𝓝 (0 : A)) : ν (Piece e f P i C) = 0 := by
  classical
  have h0C : (0 : A) ∈ C := mem_of_mem_nhds hC0
  set B := Piece e f P i C with hB
  have hBfin : ν B < ∞ := GlobalTheory.CompanionTheory.NullFr.piece_measure_lt_top e f P i C hC h0C ν hfin
  let C₂ : Set A := (fun q : A × (Fin t → A) × (Fin t → A) => q.1 - ∑ k, q.2.1 k * q.2.2 k) ''
    (C ×ˢ (Set.pi Set.univ fun _ => C) ×ˢ (Set.pi Set.univ fun _ => C))
  have hC₂ : IsCompact C₂ :=
    (hC.prod ((isCompact_univ_pi fun _ => hC).prod (isCompact_univ_pi fun _ => hC))).image (by fun_prop)
  obtain ⟨κ₁, V₁, hV₁, hn₁⟩ := GlobalTheory.CompanionTheory.NullFr.Packing.net md hmd f hf.idem C C hC hC0
  obtain ⟨κ₂, V₂, hV₂, hn₂⟩ := GlobalTheory.CompanionTheory.NullFr.Packing.net md hmd f hf.idem C₂ C hC₂ hC0
  let Ti := {k : Fin t // k ≠ i}
  have hT : Fintype.card Ti + 1 = t := by
    have := Fintype.card_subtype_compl (fun k : Fin t => k = i)
    have h1 : Fintype.card {k : Fin t // k = i} = 1 := by simp
    have h2 : 0 < t := i.pos
    simp only [Fintype.card_fin, h1] at this
    change Fintype.card {k : Fin t // ¬ k = i} + 1 = t
    omega
  let κ : ℝ≥0 := κ₁ ^ Fintype.card Ti * κ₂ ^ r
  obtain ⟨u, hu, huV, hε⟩ := GlobalTheory.CompanionTheory.NullFr.exists_unit_small_module md hmd f hf hnd (1 / (κ + 1)) (by positivity) (V₁ ∩ V₂) (Filter.inter_mem hV₁ hV₂)
  obtain ⟨N₁, hN₁, hcard₁, hcov₁⟩ := hn₁ u hu huV.1
  obtain ⟨N₂, hN₂, hcard₂, hcov₂⟩ := hn₂ u hu huV.2
  let ext : (Ti → A) → Fin t → A := fun c' k => if h : k ≠ i then c' ⟨k, h⟩ else 0
  have ext_i : ∀ c', ext c' i = 0 := fun c' => by simp [ext]
  have ext_ne : ∀ c' (k : Ti), ext c' k.1 = c' k := fun c' k => by simp [ext, k.2]
  have eq_of_f : ∀ p : A, f * p = p → e * p = p := fun p hp => by
    rw [← hp, ← mul_assoc, mul_comm e f, hfe]
  let Q : Finset ((Ti → A) × (Fin r → A)) :=
    Fintype.piFinset (fun _ => N₁) ×ˢ Fintype.piFinset (fun _ => N₂)
  have hTq : ∀ q ∈ Q, ∃ φ : (Fx A a r × Fx A a t) ≃ₜ (Fx A a r × Fx A a t), ν.map φ = ν ∧
      ∀ w, φ w = (w.1, w.2 * gU i (ext q.1) + w.1 * yU i q.2) := by
    intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hq
    rw [Fintype.mem_piFinset] at h1 h2
    refine exists_strictHenselian_absolutely_closed_local_ring md e ν invS cov i _ _ (ext_i _) (fun k => ?_) (fun l => eq_of_f _ (hN₂ _ (h2 l)).1)
    by_cases h : k = i
    · subst h; simp [ext_i]
    · have := ext_ne q.1 ⟨k, h⟩
      simp only at this
      rw [this]
      exact eq_of_f _ (hN₁ _ (h1 _)).1
  haveI : Nonempty ((Fx A a r × Fx A a t) ≃ₜ (Fx A a r × Fx A a t)) := ⟨Homeomorph.refl _⟩
  choose! T hT1 hT2 using hTq
  obtain ⟨gd, hgd, hdetd⟩ := GlobalTheory.CompanionTheory.NullFr.exists_gl_gD i u
  have hue : e * ((u : A) - 1) = (u : A) - 1 := by
    have h1 : (u : A) - 1 = f * u - f := by linear_combination hu
    rw [h1]
    have h2 : e * (f * u - f) = (f * e) * u - f * e := by ring
    rw [h2, hfe]
  have hgde : e • (gd.1 - 1) = gd.1 - 1 := by
    rw [hgd]
    ext k j
    simp only [gD, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hkj : k = j
    · subst hkj
      by_cases hki : k = i
      · subst hki; simpa using hue
      · simp [hki]
    · simp [hkj]
  let Dh : (Fx A a r × Fx A a t) ≃ₜ (Fx A a r × Fx A a t) := colH gd
  have hmapD : ν.map Dh = ((md u)⁻¹ ^ (r + t) : ℝ≥0) • ν := by
    have := cov gd hgde
    rw [hdetd] at this
    exact this
  have hDB := scale_image ν Dh _ hmapD B
  have hcover : B ⊆ ⋃ q ∈ Q, T q '' (Dh '' B) := by
    rintro z ⟨hadm, hx, hy, hv, hv', c, hci, hc, hcv⟩
    have hpick : ∀ k : Ti, ∃ p ∈ N₁, ∃ w ∈ C, f * w = w ∧ c k.1 = p + u * w := fun k =>
      hcov₁ (c k.1) (hc k.1).2 (hc k.1).1
    choose p hpN w hwC hwf hpw using hpick
    have hc₀f : ∀ k, f * ext p k = ext p k := fun k => by
      by_cases h : k = i
      · subst h; simp [ext_i]
      · have := ext_ne p ⟨k, h⟩
        simp only at this
        rw [this]; exact (hN₁ _ (hpN _)).1
    have hc₀C : ∀ k, ext p k ∈ C := fun k => by
      by_cases h : k = i
      · subst h; simpa [ext_i] using h0C
      · have := ext_ne p ⟨k, h⟩
        simp only at this
        rw [this]; exact (hN₁ _ (hpN _)).2
    have hc₁ : ∀ k, f * ext w k = ext w k ∧ ext w k ∈ C := fun k => by
      by_cases h : k = i
      · subst h; simpa [ext_i] using h0C
      · have := ext_ne w ⟨k, h⟩
        simp only at this
        rw [this]; exact ⟨hwf _, hwC _⟩
    have hcc : ∀ k, c k = ext p k + u * ext w k := fun k => by
      by_cases h : k = i
      · subst h; simp [ext_i, hci]
      · have h1 := ext_ne w ⟨k, h⟩
        have h2 := ext_ne p ⟨k, h⟩
        simp only at h1 h2
        rw [h1, h2]; exact hpw ⟨k, h⟩
    have hterm : ∀ l, f * yc P z l i - ∑ k, ext p k * yc P z l k ∈ C₂ := fun l => by
      refine ⟨(f * yc P z l i, ext p, fun k => f * yc P z l k), ⟨(hy l i).1, fun k _ => hc₀C k, fun k _ => (hy l k).1⟩, ?_⟩
      simp only
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, mul_comm (ext p k) f, hc₀f]
    have hfterm : ∀ l, f * (f * yc P z l i - ∑ k, ext p k * yc P z l k) = f * yc P z l i - ∑ k, ext p k * yc P z l k := fun l => by
      rw [mul_sub, ← mul_assoc, hf.idem, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, hc₀f]
    have hpick2 : ∀ l, ∃ q ∈ N₂, ∃ w ∈ C, f * w = w ∧ f * yc P z l i - ∑ k, ext p k * yc P z l k = q + u * w := fun l =>
      hcov₂ _ (hterm l) (hfterm l)
    choose y₀ hyN y₁ hy₁C hy₁f hyy using hpick2
    obtain ⟨w', hw', hz'⟩ := GlobalTheory.CompanionTheory.NullFr.CoverStep.point_eq_translate e f he hfe hf.idem P i C z hadm hx hy hv hv' c hci (fun k => (hc k).1) hcv u hu (ext p) (ext w)
      (ext_i _) hc₀f (ext_i _) hc₁ hcc y₀ y₁ (fun l => (hN₂ _ (hyN l)).1) (fun l => ⟨hy₁f l, hy₁C l⟩) hyy
    have hq : (p, y₀) ∈ Q := Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 hpN, Fintype.mem_piFinset.2 hyN⟩
    refine Set.mem_biUnion hq ⟨Dh w', ⟨w', hw', rfl⟩, ?_⟩
    rw [hT2 _ hq, hz']
    show ((w'.1, (w'.2 * gd.1) * gU i (ext p) + w'.1 * yU i y₀) : Fx A a r × Fx A a t) = _
    rw [hgd]
  set m : ℝ≥0 := md u with hm
  have hm0 : m ≠ 0 := by
    intro h
    have h1 : md u * md u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [← hm, h, zero_mul] at h1
    exact zero_ne_one h1
  have hDval : ν (Dh '' B) = ((m ^ (r + t) : ℝ≥0) : ℝ≥0∞) * ν B := by
    rw [← hDB, ← mul_assoc, ← ENNReal.coe_mul, ← mul_pow, mul_inv_cancel₀ hm0, one_pow, ENNReal.coe_one, one_mul]
  have hTval : ∀ q ∈ Q, ν (T q '' (Dh '' B)) = ν (Dh '' B) := fun q hq => by
    have := scale_image ν (T q) 1 (by rw [hT1 q hq, one_smul]) (Dh '' B)
    simpa using this
  have hle : ν B ≤ (Q.card : ℝ≥0∞) * ν (Dh '' B) := by
    calc ν B ≤ ν (⋃ q ∈ Q, T q '' (Dh '' B)) := measure_mono hcover
      _ ≤ ∑ q ∈ Q, ν (T q '' (Dh '' B)) := measure_biUnion_finset_le _ _
      _ = ∑ q ∈ Q, ν (Dh '' B) := Finset.sum_congr rfl hTval
      _ = _ := by simp
  have hcardQ : (Q.card : ℝ≥0) = (N₁.card : ℝ≥0) ^ Fintype.card Ti * (N₂.card : ℝ≥0) ^ r := by
    simp [Q, Finset.card_product, Fintype.card_piFinset]
  have hρ : (Q.card : ℝ≥0) * m ^ (r + t) ≤ κ * m := by
    have h1 : r + t = Fintype.card Ti + r + 1 := by omega
    rw [hcardQ, h1, pow_succ, pow_add]
    calc _ = ((N₁.card : ℝ≥0) * m) ^ Fintype.card Ti * (((N₂.card : ℝ≥0) * m) ^ r) * m := by
          rw [mul_pow, mul_pow]; ring
      _ ≤ κ * m := by
          refine mul_le_mul_left ?_ m
          exact mul_le_mul' (pow_le_pow_left' hcard₁ _) (pow_le_pow_left' hcard₂ _)
  have hlt : κ * m < 1 := by
    have h1 : m * (κ + 1) < 1 := by
      have := (lt_div_iff₀ (by positivity : 0 < κ + 1)).1 hε
      simpa using this
    calc κ * m ≤ m * (κ + 1) := by rw [mul_add, mul_one, mul_comm]; exact le_self_add
      _ < 1 := h1
  set ρ : ℝ≥0 := (Q.card : ℝ≥0) * m ^ (r + t) with hρdef
  have hρ1 : ρ < 1 := lt_of_le_of_lt hρ hlt
  have hle2 : ν B ≤ (ρ : ℝ≥0∞) * ν B := by
    calc ν B ≤ (Q.card : ℝ≥0∞) * ν (Dh '' B) := hle
      _ = (ρ : ℝ≥0∞) * ν B := by
          rw [hDval, ← mul_assoc, hρdef, ENNReal.coe_mul, ENNReal.coe_natCast]
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, (b : ℝ≥0∞) = ν B := ⟨(ν B).toNNReal, ENNReal.coe_toNNReal hBfin.ne⟩
  rw [← hb] at hle2 ⊢
  have hb2 : b ≤ ρ * b := by exact_mod_cast hle2
  by_contra h0
  have hb0 : 0 < b := pos_iff_ne_zero.2 fun h => h0 (by simp [h])
  exact absurd hb2 (not_le.2 (mul_lt_of_lt_one_left hb0 hρ1))
end

section
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A] [T2Space A]
  [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] {a r t : ℕ}
  [MeasurableSpace (Fx A a r)] [MeasurableSpace (Fx A a t)] [BorelSpace (Fx A a r × Fx A a t)]

theorem frames_null {ι : Type} [Fintype ι] (md : Aˣ →* ℝ≥0) (hmd : IsHaarMod md) (e : A) (f : ι → A) (hd : IsFieldDec e f)
    (hnd : ∀ j, NonDiscreteAt (f j)) (P : Fx A a r → Fx A r a) (ν : Measure (Fx A a r × Fx A a t))
    (hfin : IsFiniteMeasureOnCompacts ν)
    (invS : ∀ y : Fx A r t, e • y = y → ν.map (fun z : Fx A a r × Fx A a t => (z.1, z.2 + z.1 * y)) = ν)
    (cov : ∀ g : GL (Fin t) A, e • (g.1 - 1) = g.1 - 1 → ν.map (fun z : Fx A a r × Fx A a t => (z.1, z.2 * g.1)) =
      ((md (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (r + t) : ℝ≥0) • ν)
    (supp : ν (admitted e P)ᶜ = 0) : ν {z | ¬ ∃ M : Fx A t a, M * vc P z = e • (1 : Fx A t t)} = 0 := by
  classical
  have hfe : ∀ j, f j * e = f j := fun j => by
    rw [← hd.sum, Finset.mul_sum, Finset.sum_eq_single j (fun b _ hb => hd.orth j b hb.symm) (by simp), (hd.field j).idem]
  have he : e * e = e := by
    nth_rw 1 [← hd.sum]
    rw [Finset.sum_mul, Finset.sum_congr rfl fun j _ => hfe j, hd.sum]
  let K : CompactExhaustion A := default
  obtain ⟨n₀, hn₀⟩ := K.exists_mem_nhds (0 : A)
  have ev : ∀ x : A, ∀ᶠ n in atTop, x ∈ K (n + n₀) := fun x => by
    obtain ⟨m, hm⟩ := K.exists_mem x
    exact eventually_atTop.2 ⟨m, fun n hn => K.subset (by omega) hm⟩
  have hsub : {z | ¬ ∃ M : Fx A t a, M * vc P z = e • (1 : Fx A t t)} ⊆
      (admitted e P)ᶜ ∪ ⋃ j, ⋃ i, ⋃ n, Piece e (f j) P i (K (n + n₀)) := by
    intro z hz
    by_cases hadm : z ∈ admitted e P
    · right
      obtain ⟨j, i, c, hci, hcf, hcv⟩ := GlobalTheory.CompanionTheory.NullFr.Coeff.exists_dependent_column e f hd (vc P z) hz
      have hall : ∀ᶠ n in atTop, (∀ p q, z.1 p q ∈ K (n + n₀)) ∧
          (∀ l k, f j * yc P z l k ∈ K (n + n₀) ∧ (1 - f j) * yc P z l k ∈ K (n + n₀)) ∧
          (∀ p k, vc P z p k ∈ K (n + n₀)) ∧ (∀ p, (1 - f j) * vc P z p i ∈ K (n + n₀)) ∧ ∀ k, c k ∈ K (n + n₀) := by
        refine (eventually_all.2 fun p => eventually_all.2 fun q => ev _).and
          ((eventually_all.2 fun l => eventually_all.2 fun k => (ev _).and (ev _)).and
          ((eventually_all.2 fun p => eventually_all.2 fun k => ev _).and
          ((eventually_all.2 fun p => ev _).and (eventually_all.2 fun k => ev _))))
      obtain ⟨n, h1, h2, h3, h4, h5⟩ := hall.exists
      simp only [Set.mem_union, Set.mem_iUnion]
      exact ⟨j, i, n, hadm, h1, h2, fun p k _ => h3 p k, h4, c, hci, fun k => ⟨hcf k, h5 k⟩, hcv⟩
    · exact Or.inl hadm
  refine measure_mono_null hsub (measure_union_null supp ?_)
  refine measure_iUnion_null fun j => measure_iUnion_null fun i => measure_iUnion_null fun n => ?_
  exact piece_null md hmd e (f j) he (hfe j) (hd.field j) (hnd j) P ν hfin invS cov i _ (K.isCompact _)
    (Filter.mem_of_superset hn₀ (K.subset (by omega)))
end

end GlobalTheory.CompanionTheory.NullFr

section
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.NullFr

set_option maxHeartbeats 1600000 in

theorem nullSing_of_idemEx : IdemEx → NullSing := by
  intro hI D r t V b₀ hb S e he ν hν
  haveI : IsTopologicalRing (AE D) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele D.host.F
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  haveI : LocallyCompactSpace (AE D) := eh.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE D) := eh.secondCountableTopology
  haveI : T2Space (AE D) := eh.isEmbedding.t2Space
  haveI : BorelSpace (AE D) := ⟨rfl⟩
  haveI b1 : BorelSpace (Mx D V.rank r) := @BorelSpace.mk _ _ (measMx _ _) rfl
  haveI b2 : BorelSpace (Mx D V.rank t) := @BorelSpace.mk _ _ (measMx _ _) rfl
  haveI s1 : SecondCountableTopology (Mx D V.rank r) := inferInstanceAs (SecondCountableTopology (Fin V.rank → Fin r → AE D))
  haveI s2 : SecondCountableTopology (Mx D V.rank t) := inferInstanceAs (SecondCountableTopology (Fin V.rank → Fin t → AE D))
  haveI b3 : BorelSpace (Mx D V.rank r × Mx D V.rank t) := Prod.borelSpace
  obtain ⟨ι, _, f, hd, hnd⟩ := GlobalTheory.CompanionTheory.NullFr.FieldDec.exists_isFieldDec D S e he
  have hmd : IsHaarMod (absA D) := fun h hh u =>
    GlobalTheory.AdeleUnitModule.map_mul_eq_absE_inv_smul _ _ D.sp.cm.sig (isCMExt_host D) h hh u
  let P : Mx D V.rank r → Mx D r V.rank := fun x => mm (rat b₀.1⁻¹) (mm (adj x) (gA V))
  have hyv : ∀ z : Mx D V.rank r × Mx D V.rank t, yc P z = yv V b₀ z := fun z => by
    simp only [yc, P, yv, ip, mm, Matrix.mul_assoc]
  have hinv : mm (rat b₀.1⁻¹) (rat b₀.1) = (1 : Mx D r r) := by
    have h1 : b₀.1⁻¹ * b₀.1 = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hb)
    have h2 : (b₀.1⁻¹ * b₀.1).map (incA D) = (rat b₀.1⁻¹ : Mx D r r) * rat b₀.1 := Matrix.map_mul
    have h3 : ((1 : Matrix (Fin r) (Fin r) D.host.E)).map (incA D) = (1 : Mx D r r) := Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1, h3] at h2
    exact h2.symm
  have hsupp : ν (admitted e P)ᶜ = 0 := by
    refine measure_mono_null ?_ hν.supp
    rintro z hz ⟨g1, g2, g3, -⟩
    refine hz ⟨g1, g2, ?_⟩
    show mm (mm (rat b₀.1⁻¹) (mm (adj z.1) (gA V))) z.1 = _
    have h4 : mm (mm (rat b₀.1⁻¹) (mm (adj z.1) (gA V))) z.1 = mm (rat b₀.1⁻¹) (ip V z.1 z.1) := by
      simp only [ip, mm, Matrix.mul_assoc]
    rw [h4, g3]
    simp only [mm, Matrix.mul_smul] at hinv ⊢
    rw [hinv]
  have key := frames_null (absA D) hmd e f hd hnd P ν hν.fin hν.invS hν.cov hsupp
  refine measure_mono_null ?_ (measure_union_null hν.supp key)
  intro z hz
  by_cases hg : e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0
  · right
    rintro ⟨M, hM⟩
    refine hz (GlobalTheory.CompanionTheory.NullFr.free_of_leftInv_orth V b₀ hb e z hg.1 hg.2.1 hg.2.2.1 M ?_)
    rw [← hyv]
    exact hM
  · exact Or.inl hg

end GlobalTheory.CompanionTheory.NullFr
end
