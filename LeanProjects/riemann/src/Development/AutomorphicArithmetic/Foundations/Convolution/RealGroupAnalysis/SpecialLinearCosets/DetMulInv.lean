import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IntegrableSB
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.TranslateMemSB
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.CosetSpan
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IsCompactBoxSet

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] {v : P F}

private lemma det_inv_mul (y : GLv v) : ((y⁻¹).val).det * (y.val).det = 1 := by
  rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]

private lemma det_mul_inv (y : GLv v) : (y.val).det * ((y⁻¹).val).det = 1 := by
  rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]

private noncomputable def tw (y h : GLv v) (e : (y.val).det = (h.val).det) : SL v ≃ₜ SL v where
  toFun m := ⟨(y⁻¹).val * m.1 * h.val, by
    rw [Matrix.det_mul, Matrix.det_mul, m.2, mul_one, ← e, det_inv_mul]⟩
  invFun m := ⟨y.val * m.1 * (h⁻¹).val, by
    rw [Matrix.det_mul, Matrix.det_mul, m.2, mul_one, e, det_mul_inv]⟩
  left_inv m := by
    apply Subtype.ext
    have hy : y.val * (y⁻¹).val = 1 := Units.mul_inv y
    have hh : h.val * (h⁻¹).val = 1 := Units.mul_inv h
    change y.val * ((y⁻¹).val * m.1 * h.val) * (h⁻¹).val = m.1
    calc y.val * ((y⁻¹).val * m.1 * h.val) * (h⁻¹).val
        = (y.val * (y⁻¹).val) * m.1 * (h.val * (h⁻¹).val) := by simp only [Matrix.mul_assoc]
      _ = m.1 := by rw [hy, hh, Matrix.one_mul, Matrix.mul_one]
  right_inv m := by
    apply Subtype.ext
    have hy : (y⁻¹).val * y.val = 1 := Units.inv_mul y
    have hh : (h⁻¹).val * h.val = 1 := Units.inv_mul h
    change (y⁻¹).val * (y.val * m.1 * (h⁻¹).val) * h.val = m.1
    calc (y⁻¹).val * (y.val * m.1 * (h⁻¹).val) * h.val
        = ((y⁻¹).val * y.val) * m.1 * ((h⁻¹).val * h.val) := by simp only [Matrix.mul_assoc]
      _ = m.1 := by rw [hy, hh, Matrix.one_mul, Matrix.mul_one]
  continuous_toFun := by
    refine Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.continuous_iff.2 ?_
    exact (continuous_const.matrix_mul Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous).matrix_mul continuous_const
  continuous_invFun := by
    refine Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.continuous_iff.2 ?_
    exact (continuous_const.matrix_mul Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous).matrix_mul continuous_const

private noncomputable def cj (w : GLv v) : SL v →* SL v where
  toFun := tw w w rfl
  map_one' := by
    apply Subtype.ext
    have hw : (w⁻¹).val * w.val = 1 := Units.inv_mul w
    change (w⁻¹).val * (1 : M2 v) * w.val = 1
    rw [Matrix.mul_one, hw]
  map_mul' m n := by
    apply Subtype.ext
    have hw : w.val * (w⁻¹).val = 1 := Units.mul_inv w
    change (w⁻¹).val * (m.1 * n.1) * w.val = ((w⁻¹).val * m.1 * w.val) * ((w⁻¹).val * n.1 * w.val)
    calc (w⁻¹).val * (m.1 * n.1) * w.val
        = (w⁻¹).val * m.1 * (1 : M2 v) * n.1 * w.val := by
          rw [Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = ((w⁻¹).val * m.1 * w.val) * ((w⁻¹).val * n.1 * w.val) := by
          rw [← hw]; simp only [Matrix.mul_assoc]

private lemma sb_comp {X : Type} [TopologicalSpace X] (e : X ≃ₜ X) {b : X → ℂ} (hb : b ∈ SB X) :
    b ∘ e ∈ SB X :=
  ⟨hb.1.comp_continuous e.continuous, hb.2.comp_homeomorph e⟩

private lemma ind_mem {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {U : Subgroup G} (hUo : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G)) : ind U ∈ SB G := by
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_,
    HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ (U : Set G)
  · exact ⟨U, hUo, hx, fun y hy => by
      simp only [ind]; rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨(U : Set G)ᶜ, (U.isClosed_of_isOpen hUo).isOpen_compl, hx, fun y hy => by
      simp only [ind]; rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

private lemma one_term {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLv v) V)
    (β : V →ₗ[ℂ] SB (SL v) →ₗ[ℂ] ℂ)
    (hβ : ∀ (g : SL v) f (a a' : SB (SL v)), (∀ m, a'.1 m = a.1 (m * g)) →
      β (ρ (Matrix.SpecialLinearGroup.toGL g) f) a' = β f a)
    (I : SB (SL v) →ₗ[ℂ] ℂ) (hI : InvI I) (Λ : V →ₗ[ℂ] ℂ)
    (hΛ : ∀ f (U : Subgroup (SL v)) (a : SB (SL v)), IsOpen (U : Set (SL v)) → a.1 = ind U →
      (∀ g ∈ U, ρ (Matrix.SpecialLinearGroup.toGL g) f = f) → β f a = I a * Λ f)
    (U : Subgroup (SL v)) (hUo : IsOpen (U : Set (SL v))) (a0 : SB (SL v)) (ha0 : a0.1 = ind U)
    (f : V) (hfix : ∀ u ∈ U, ρ (Matrix.SpecialLinearGroup.toGL u) f = f)
    (w d : GLv v) (e : (w.val).det = (d.val).det) (b : SB (SL v))
    (hb : ∀ m, b.1 m = ind U (tw w d e m)) :
    β (ρ d f) b = I a0 * Λ (ρ w f) := by
  have hdi : (d⁻¹).val * d.val = 1 := Units.inv_mul d
  have hwi : w.val * (w⁻¹).val = 1 := Units.mul_inv w
  let g' : SL v := ⟨w.val * (d⁻¹).val, by rw [Matrix.det_mul, e, det_mul_inv]⟩
  have hg' : Matrix.SpecialLinearGroup.toGL g' * d = w := by
    apply Units.ext
    change w.val * (d⁻¹).val * d.val = w.val
    rw [Matrix.mul_assoc, hdi, Matrix.mul_one]
  let Uc : Subgroup (SL v) := U.comap (cj w)
  have hUco : IsOpen (Uc : Set (SL v)) := hUo.preimage (tw w w rfl).continuous
  have hU0 : ind U ∈ SB (SL v) := ha0 ▸ a0.2
  let a1 : SB (SL v) := ⟨ind U ∘ (tw w w rfl), sb_comp _ hU0⟩
  have h1 : a1.1 = ind Uc := by
    funext m
    change ind U (tw w w rfl m) = ind Uc m
    unfold ind
    by_cases h : tw w w rfl m ∈ U
    · rw [Set.indicator_of_mem (show _ ∈ (U : Set (SL v)) from h),
        Set.indicator_of_mem (show m ∈ (Uc : Set (SL v)) from h)]
    · rw [Set.indicator_of_notMem (show _ ∉ (U : Set (SL v)) from h),
        Set.indicator_of_notMem (show m ∉ (Uc : Set (SL v)) from h)]
  have h2 : β (ρ (Matrix.SpecialLinearGroup.toGL g') (ρ d f)) a1 = β (ρ d f) b :=
    hβ g' (ρ d f) b a1 fun m => by
      rw [hb]
      change ind U (tw w w rfl m) = ind U (tw w d e (m * g'))
      congr 1
      apply Subtype.ext
      change (w⁻¹).val * m.1 * w.val = (w⁻¹).val * (m.1 * (w.val * (d⁻¹).val)) * d.val
      simp only [Matrix.mul_assoc]
      rw [hdi, Matrix.mul_one]
  have h3 : ρ (Matrix.SpecialLinearGroup.toGL g') (ρ d f) = ρ w f := by
    rw [← Module.End.mul_apply, ← map_mul, hg']
  have h4 : ∀ u ∈ Uc, ρ (Matrix.SpecialLinearGroup.toGL u) (ρ w f) = ρ w f := by
    intro u hu
    have hw : Matrix.SpecialLinearGroup.toGL u * w = w * Matrix.SpecialLinearGroup.toGL (tw w w rfl u) := by
      apply Units.ext
      change u.1 * w.val = w.val * ((w⁻¹).val * u.1 * w.val)
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hwi, Matrix.one_mul]
    have h5 : ρ (Matrix.SpecialLinearGroup.toGL (tw w w rfl u)) f = f := hfix _ hu
    calc ρ (Matrix.SpecialLinearGroup.toGL u) (ρ w f)
        = ρ (Matrix.SpecialLinearGroup.toGL u * w) f := by rw [map_mul, Module.End.mul_apply]
      _ = ρ w (ρ (Matrix.SpecialLinearGroup.toGL (tw w w rfl u)) f) := by
          rw [hw, map_mul, Module.End.mul_apply]
      _ = ρ w f := by rw [h5]
  have h6 : I a1 = I a0 := hI.conj w a0 a1 fun m m' h => by
    have : m' = tw w w rfl m := Subtype.ext h
    rw [this, ha0]
    rfl
  rw [← h2, h3, hΛ (ρ w f) Uc a1 hUco h1 h4, h6]

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.I.absS :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLv v) V), (∀ f, IsOpen {g | ρ g f = f}) →
      ∀ β : V →ₗ[ℂ] SB (SL v) →ₗ[ℂ] ℂ,
      (∀ (g : SL v) f (a a' : SB (SL v)), (∀ m, a'.1 m = a.1 (m * g)) → β (ρ (Matrix.SpecialLinearGroup.toGL g) f) a' = β f a) →
      ∀ f (a : SB (SL v)) (aa : GLv v → SB (SL v)),
        (∀ x (m m' : SL v), m'.1 = (x⁻¹).val * m.1 * (dd x).val → (aa x).1 m = a.1 m') → (fun x => β (ρ (dd x) f) (aa x)) ∈ MC ρ := by
  intro F _ _ v V _ _ ρ hsm β hβ f a aa haa
  obtain ⟨I, hI⟩ := UpperTheory.ConvolutionTheory.R2.I.invI F v
  obtain ⟨Λ, hΛ⟩ := UpperTheory.ConvolutionTheory.R2.I.lamEx F v V ρ hsm I hI β hβ
  have hN : (Matrix.SpecialLinearGroup.toGL : SL v → GLv v) ⁻¹' {g | ρ g f = f} ∈ 𝓝 (1 : SL v) :=
    ((hsm f).preimage Matrix.SpecialLinearGroup.continuous_toGL).mem_nhds (by simp)
  obtain ⟨U, s, c, hUo, hUc, hUN, hsum⟩ :=
    UpperTheory.ConvolutionTheory.R2.I.cosetSpan (SL v) (UpperTheory.ConvolutionTheory.R2.I.lgrp F v).1 a.1 a.2 _ hN
  let a0 : SB (SL v) := ⟨ind U, ind_mem hUo hUc⟩
  have hfix : ∀ u ∈ U, ρ (Matrix.SpecialLinearGroup.toGL u) f = f := fun u hu => hUN hu
  have hdet0 : ∀ x : GLv v, (x.val).det = ((dd x).val).det := by
    intro x
    change _ = (!![(((1 : (Kv v)ˣ)) : Kv v), 0; 0, ((Matrix.GeneralLinearGroup.det x : (Kv v)ˣ) : Kv v)]).det
    simp [Matrix.det_fin_two_of]
  have hdet : ∀ (x : GLv v) (g : SL v),
      ((x * Matrix.SpecialLinearGroup.toGL g).val).det = ((dd x).val).det := by
    intro x g
    rw [← hdet0 x, Units.val_mul, Matrix.det_mul]
    have : ((Matrix.SpecialLinearGroup.toGL g).val).det = 1 := g.2
    rw [this, mul_one]
  have hval : ∀ x, β (ρ (dd x) f) (aa x) =
      ∑ g ∈ s, (c g * I a0) * Λ (ρ x (ρ (Matrix.SpecialLinearGroup.toGL g) f)) := by
    intro x
    let B : SL v → SB (SL v) := fun g =>
      ⟨ind U ∘ tw (x * Matrix.SpecialLinearGroup.toGL g) (dd x) (hdet x g), sb_comp _ a0.2⟩
    have hs : aa x = ∑ g ∈ s, c g • B g := by
      apply Subtype.ext
      funext m
      rw [haa x m (tw x (dd x) (hdet0 x) m) rfl, hsum]
      simp only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, Submodule.coe_smul,
        Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      congr 1
      change ind U _ = ind U (tw (x * Matrix.SpecialLinearGroup.toGL g) (dd x) (hdet x g) m)
      congr 1
      apply Subtype.ext
      have hinv : ((x * Matrix.SpecialLinearGroup.toGL g)⁻¹).val = (g⁻¹).1 * (x⁻¹).val := by
        rw [_root_.mul_inv_rev, ← map_inv, Units.val_mul]
        rfl
      change (g⁻¹).1 * ((x⁻¹).val * m.1 * (dd x).val) =
        ((x * Matrix.SpecialLinearGroup.toGL g)⁻¹).val * m.1 * (dd x).val
      rw [hinv]
      simp only [Matrix.mul_assoc]
    rw [hs, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, smul_eq_mul,
      one_term ρ β hβ I hI Λ hΛ U hUo a0 rfl f hfix (x * Matrix.SpecialLinearGroup.toGL g) (dd x)
        (hdet x g) (B g) (fun m => rfl), map_mul, Module.End.mul_apply, mul_assoc]
  have hfun : (fun x => β (ρ (dd x) f) (aa x)) =
      ∑ g ∈ s, (c g * I a0) • (fun x => Λ (ρ x (ρ (Matrix.SpecialLinearGroup.toGL g) f))) := by
    funext x
    rw [hval x]
    simp [Finset.sum_apply]
  rw [hfun]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Λ, _, rfl⟩)
