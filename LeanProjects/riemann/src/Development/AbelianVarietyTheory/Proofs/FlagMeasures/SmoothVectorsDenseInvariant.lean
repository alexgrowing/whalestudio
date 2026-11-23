import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SgInfDD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mat k r → (H →L[ℂ] H)}

theorem gg_mul {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r :=
  Formalism.MainNotions.LowestKTypeMultiplicity.UH_mul ha hb

theorem gg_one : (1 : Mat k r) ∈ GG k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_one k r

theorem hasDeriv_dsig (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    {Y : Mat k r} (hY : InLieHpk k r Y) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) v) (dsig σ Y v) 0 :=
  Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hσ hv [] (by simp) hY

theorem smooth_dsig (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    {Y : Mat k r} (hY : InLieHpk k r Y) : IsSmoothVec (k := k) (r := r) σ (dsig σ Y v) := by
  have h2 := Formalism.MainNotions.LowestKTypeMultiplicity.psiD_smooth hσ hv [Y] (by simpa using hY)
  intro g₀ hg₀
  obtain ⟨U, F, hU, hp, hF, hE⟩ := h2 ((1 : Mat k r), g₀) (gg_one) hg₀
  have hc : ContDiff ℝ ∞ (fun g : Mat k r => (((1 : Mat k r), g) : Mat k r × Mat k r)) :=
    contDiff_const.prodMk contDiff_id
  refine ⟨(fun g : Mat k r => (((1 : Mat k r), g) : Mat k r × Mat k r)) ⁻¹' U, fun g => F ((1 : Mat k r), g),
    hU.preimage hc.continuous, hp, hF.comp hc.contDiffOn (fun x hx => hx), ?_⟩
  intro g hgU hgH
  have := hE ((1 : Mat k r), g) hgU gg_one hgH
  simp only [hσ.1.1, ContinuousLinearMap.one_apply] at this
  exact this

theorem lie_conj {g Y : Mat k r} (hg : g ∈ GG k r) (hY : InLieHpk k r Y) :
    InLieHpk k r (g * Y * g⁻¹) := by
  have hd : IsUnit g.det := Formalism.MainNotions.LowestKTypeMultiplicity.UH_det hg
  have hM : g⁻¹ ∈ GG k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_inv hg
  have hgM : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hd
  have hMg : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hd
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hM' : (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r := hM
  have e1 : gᴴ * Hpk k r = Hpk k r * g⁻¹ := by
    calc gᴴ * Hpk k r = gᴴ * Hpk k r * (g * g⁻¹) := by rw [hgM, Matrix.mul_one]
      _ = (gᴴ * Hpk k r * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * g⁻¹ := by rw [hg']
  have e2 : Hpk k r * g = (g⁻¹)ᴴ * Hpk k r := by
    calc Hpk k r * g = ((g⁻¹)ᴴ * Hpk k r * g⁻¹) * g := by rw [hM']
      _ = (g⁻¹)ᴴ * Hpk k r * (g⁻¹ * g) := by simp only [Matrix.mul_assoc]
      _ = (g⁻¹)ᴴ * Hpk k r := by rw [hMg, Matrix.mul_one]
  have hY' : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY
  show (g * Y * g⁻¹)ᴴ * Hpk k r + Hpk k r * (g * Y * g⁻¹) = 0
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc (g⁻¹)ᴴ * (Yᴴ * gᴴ) * Hpk k r + Hpk k r * (g * Y * g⁻¹)
      = (g⁻¹)ᴴ * Yᴴ * (gᴴ * Hpk k r) + (Hpk k r * g) * Y * g⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (g⁻¹)ᴴ * Yᴴ * (Hpk k r * g⁻¹) + ((g⁻¹)ᴴ * Hpk k r) * Y * g⁻¹ := by rw [e1, e2]
    _ = (g⁻¹)ᴴ * (Yᴴ * Hpk k r + Hpk k r * Y) * g⁻¹ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hY', Matrix.mul_zero, Matrix.zero_mul]

theorem dsig_conj (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    {Y : Mat k r} (hY : InLieHpk k r Y) {g : Mat k r} (hg : g ∈ GG k r) :
    σ g (dsig σ Y v) = dsig σ (g * Y * g⁻¹) (σ g v) := by
  have hd : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (Formalism.MainNotions.LowestKTypeMultiplicity.UH_det hg)
  have hM : g⁻¹ ∈ GG k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_inv hg
  have hMg : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g ((Matrix.isUnit_iff_isUnit_det g).1 hd)
  have h1 := hasDeriv_dsig hσ hv hY
  have h2 := ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have e : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (g * Y * g⁻¹))) (σ g v)) =
      (⇑((σ g).restrictScalars ℝ) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) v) := by
    funext t
    have hx := Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hY t
    have hs : (t : ℂ) • (g * Y * g⁻¹) = g * ((t : ℂ) • Y) * g⁻¹ := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [hs, Matrix.exp_conj _ _ hd]
    simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars']
    have hc : g * NormedSpace.exp ((t : ℂ) • Y) ∈ GG k r := gg_mul hg hx
    rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ (gg_mul hc hM) g hg,
      ← ContinuousLinearMap.comp_apply, ← hσ.1.2 g hg _ hx]
    congr 2
    rw [Matrix.mul_assoc, hMg, Matrix.mul_one]
  show _ = deriv _ 0
  rw [e, h2.deriv]
  rfl

theorem smooth_dsigW (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v) :
    ∀ Ys : List (Mat k r), (∀ Y ∈ Ys, InLieHpk k r Y) → IsSmoothVec (k := k) (r := r) σ (dsigW σ Ys v) := by
  intro Ys
  induction Ys with
  | nil => intro _; exact hv
  | cons Y Ys ih =>
    intro h
    exact smooth_dsig hσ (ih fun X hX => h X (List.mem_cons_of_mem _ hX)) (h Y List.mem_cons_self)

theorem dsigW_conj (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    {g : Mat k r} (hg : g ∈ GG k r) :
    ∀ Ys : List (Mat k r), (∀ Y ∈ Ys, InLieHpk k r Y) →
      σ g (dsigW σ Ys v) = dsigW σ (Ys.map fun Y => g * Y * g⁻¹) (σ g v) := by
  intro Ys
  induction Ys with
  | nil => intro _; rfl
  | cons Y Ys ih =>
    intro h
    have h' : ∀ X ∈ Ys, InLieHpk k r X := fun X hX => h X (List.mem_cons_of_mem _ hX)
    show σ g (dsig σ Y (dsigW σ Ys v)) = dsig σ (g * Y * g⁻¹) (dsigW σ (Ys.map fun Y => g * Y * g⁻¹) (σ g v))
    rw [dsig_conj hσ (smooth_dsigW hσ hv Ys h') (h Y List.mem_cons_self) hg, ih h']

theorem dsig_zero (Y : Mat k r) : dsig σ Y (0 : H) = 0 := by
  simp [dsig]

theorem dsig_add (hσ : IsURepOn (GG k r) σ) {a b : H} (ha : IsSmoothVec (k := k) (r := r) σ a)
    (hb : IsSmoothVec (k := k) (r := r) σ b) {Y : Mat k r} (hY : InLieHpk k r Y) :
    dsig σ Y (a + b) = dsig σ Y a + dsig σ Y b := by
  have h := (hasDeriv_dsig hσ ha hY).add (hasDeriv_dsig hσ hb hY)
  show deriv _ 0 = _
  simp only [map_add]
  exact h.deriv

theorem dsig_smul (hσ : IsURepOn (GG k r) σ) {a : H} (ha : IsSmoothVec (k := k) (r := r) σ a)
    (c : ℂ) {Y : Mat k r} (hY : InLieHpk k r Y) :
    dsig σ Y (c • a) = c • dsig σ Y a := by
  have h := (hasDeriv_dsig hσ ha hY).const_smul c
  show deriv _ 0 = _
  simp only [map_smul]
  exact h.deriv

theorem DD_stable (hσ : IsURepOn (GG k r) σ) (w : H) {g : Mat k r} (hg : g ∈ GG k r) :
    DD σ w ≤ (DD σ w).comap (σ g : H →ₗ[ℂ] H) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨h, hh, rfl⟩
  show σ g (σ h w) ∈ DD σ w
  rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 g hg h hh]
  exact mem_DD σ w (gg_mul hg hh)

theorem mem_DD_self (hσ : IsURepOn (GG k r) σ) (w : H) : w ∈ DD σ w := by
  have := mem_DD σ w (gg_one (k := k) (r := r))
  rwa [hσ.1.1, ContinuousLinearMap.one_apply] at this

theorem DD_dense (hσ : IsURepOn (GG k r) σ) (hirr : IsIrredOn (GG k r) σ) {w : H} (hw : w ≠ 0) :
    Dense (DD σ w : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  have hst : ∀ g ∈ GG k r, ∀ v ∈ (DD σ w).topologicalClosure, σ g v ∈ (DD σ w).topologicalClosure := by
    intro g hg v hv
    have hle : (DD σ w).topologicalClosure ≤ ((DD σ w).topologicalClosure).comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.topologicalClosure_minimal _ ?_ ?_
      · exact (DD_stable hσ w hg).trans (Submodule.comap_mono (DD σ w).le_topologicalClosure)
      · exact (DD σ w).isClosed_topologicalClosure.preimage (σ g).continuous
    exact hle hv
  rcases hirr (DD σ w).topologicalClosure (DD σ w).isClosed_topologicalClosure hst with h | h
  · exfalso
    have h1 : w ∈ (DD σ w).topologicalClosure := (DD σ w).le_topologicalClosure (mem_DD_self hσ w)
    rw [h, Submodule.mem_bot] at h1
    exact hw h1
  · exact h

theorem DD_le_Vinf (w : H) : DD σ w ≤ Vinf σ w := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, rfl⟩
  exact Submodule.subset_span ⟨[], g, by simp, hg, rfl⟩

theorem Vinf_smooth (hσ : IsURepOn (GG k r) σ) {w : H} (hw : IsSmoothVec (k := k) (r := r) σ w) :
    ∀ v ∈ Vinf σ w, IsSmoothVec (k := k) (r := r) σ v := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Ys, g, hYs, hg, rfl⟩ := hx
    exact smooth_dsigW hσ (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hw hg) Ys hYs
  | zero => exact Formalism.MainNotions.LowestKTypeMultiplicity.smooth_zero
  | add x y _ _ hx hy => exact Formalism.MainNotions.LowestKTypeMultiplicity.smooth_add hx hy
  | smul a x _ hx => exact Formalism.MainNotions.LowestKTypeMultiplicity.smooth_smul a hx

theorem Vinf_stable (hσ : IsURepOn (GG k r) σ) {w : H} (hw : IsSmoothVec (k := k) (r := r) σ w)
    {g : Mat k r} (hg : g ∈ GG k r) : Vinf σ w ≤ (Vinf σ w).comap (σ g : H →ₗ[ℂ] H) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨Ys, h, hYs, hh, rfl⟩
  show σ g (dsigW σ Ys (σ h w)) ∈ Vinf σ w
  rw [dsigW_conj hσ (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hw hh) hg Ys hYs,
    ← ContinuousLinearMap.comp_apply, ← hσ.1.2 g hg h hh]
  refine Submodule.subset_span ⟨Ys.map fun Y => g * Y * g⁻¹, g * h, ?_, gg_mul hg hh, rfl⟩
  intro Y hY
  obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
  exact lie_conj hg (hYs X hX)

theorem Vinf_dsig (hσ : IsURepOn (GG k r) σ) {w : H} (hw : IsSmoothVec (k := k) (r := r) σ w)
    {Y : Mat k r} (hY : InLieHpk k r Y) : ∀ v ∈ Vinf σ w, dsig σ Y v ∈ Vinf σ w := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Ys, g, hYs, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨Y :: Ys, g, ?_, hg, rfl⟩
    intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · exact hY
    · exact hYs X hX
  | zero => rw [dsig_zero]; exact (Vinf σ w).zero_mem
  | add x y hx hy ihx ihy =>
    rw [dsig_add hσ (Vinf_smooth hσ hw x hx) (Vinf_smooth hσ hw y hy) hY]
    exact (Vinf σ w).add_mem ihx ihy
  | smul a x hx ihx =>
    rw [dsig_smul hσ (Vinf_smooth hσ hw x hx) a hY]
    exact (Vinf σ w).smul_mem a ihx

theorem DD_stable_dense : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H), IsURepOn (GG k r) σ →
    (∀ g ∈ GG k r, ∀ v ∈ DD σ w, σ g v ∈ DD σ w) ∧
    (IsIrredOn (GG k r) σ → w ≠ 0 → Dense (DD σ w : Set H)) ∧ DD σ w ≤ Vinf σ w ∧
    (∀ v, IsSmoothVec σ v → (∀ g ∈ GG k r, IsSmoothVec σ (σ g v)) ∧
      ∀ Y, InLieHpk k r Y → IsSmoothVec σ (dsig σ Y v) ∧
        ∀ g ∈ GG k r, InLieHpk k r (g * Y * g⁻¹) ∧ σ g (dsig σ Y v) = dsig σ (g * Y * g⁻¹) (σ g v)) ∧
    (IsSmoothVec σ w → (∀ v ∈ Vinf σ w, IsSmoothVec σ v) ∧ (∀ g ∈ GG k r, ∀ v ∈ Vinf σ w, σ g v ∈ Vinf σ w) ∧
      ∀ Y, InLieHpk k r Y → ∀ v ∈ Vinf σ w, dsig σ Y v ∈ Vinf σ w) := by
  intro k r H _ _ _ σ w hσ
  refine ⟨fun g hg v hv => DD_stable hσ w hg hv, fun hirr hw => DD_dense hσ hirr hw, DD_le_Vinf w,
    fun v hv => ⟨fun g hg => Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv hg, fun Y hY =>
      ⟨smooth_dsig hσ hv hY, fun g hg => ⟨lie_conj hg hY, dsig_conj hσ hv hY hg⟩⟩⟩,
    fun hw => ⟨Vinf_smooth hσ hw, fun g hg v hv => Vinf_stable hσ hw hg hv, fun Y hY => Vinf_dsig hσ hw hY⟩⟩

end GlobalTheory.SgInfDD
