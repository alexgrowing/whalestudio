import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ThickFrames
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LactTens
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LactCv
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PositionOf
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmoothAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.CvPowers
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.CvBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.JUnique
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LactLaws

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Geo
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.L1

section One

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem conv_apply (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β γ : TI K n) (g : archGroup K n) :
    GM.conv ν β γ g = cv ν β γ g := by
  have hb := cvBasic (archGroup K n) ν β γ γ β.continuous β.hasCompactSupport γ.continuous γ.hasCompactSupport
    γ.continuous γ.hasCompactSupport
  have hex : ∃ δ : TI K n, ∀ g, δ g = ∫ x, β x * γ (x⁻¹ * g) ∂ν := ⟨⟨⟨cv ν β γ, hb.1⟩, hb.2.1⟩, fun _ => rfl⟩
  unfold GM.conv
  rw [dif_pos hex]
  exact hex.choose_spec g

variable [IsTotallyComplex K]

private theorem lact_step (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (α β γ : TI K n) (hα : SmoothT α)
    (hβ : SmoothT β) (h : ∀ g, γ g = cv ν α β g) (y z : UC K n) (hz : z ∈ Subalgebra.center ℂ (UC K n))
    (g : archGroup K n) : lact (y * z) γ g = cv ν (lact y α) (lact z β) g := by
  obtain ⟨hγ, -, -, h4⟩ := lactCv K n ν α β γ hα h
  have hl := lactLaws K n γ hγ
  rw [hl.2.2.1 y z]
  have h5 : ∀ g, lact z γ g = cv ν α (lact z β) g := h4 hβ z hz
  exact (lactCv K n ν α (lact z β) (lact z γ) hα h5).2.2.1 y g

private theorem cvAll_ex (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] :
    ∀ (m : ℕ) (φ : Fin (m + 1) → TI K n), (∀ i, SmoothT (φ i)) →
      ∃ γ : TI K n, SmoothT γ ∧ ∀ g, γ g = cvAll ν m (fun i => φ i) g := by
  intro m
  induction m with
  | zero => exact fun φ h => ⟨φ 0, h 0, fun _ => rfl⟩
  | succ m ih =>
    intro φ h
    obtain ⟨γ', h1, h2⟩ := ih (fun i => φ i.succ) fun i => h _
    have h3 : (γ' : archGroup K n → ℂ) = cvAll ν m (fun i => φ i.succ) := funext h2
    refine ⟨GM.conv ν (φ 0) γ', (lactCv K n ν (φ 0) γ' _ (h 0) (conv_apply ν _ _)).1, fun g => ?_⟩
    rw [conv_apply, h3]
    rfl

private theorem cvAll_lact (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] :
    ∀ (m : ℕ) (φ : Fin (m + 1) → TI K n) (z : Fin (m + 1) → Subalgebra.center ℂ (UC K n)) (γ : TI K n),
      (∀ i, SmoothT (φ i)) → (∀ g, γ g = cvAll ν m (fun i => φ i) g) →
      ∀ g, lact ((∏ i, z i : Subalgebra.center ℂ (UC K n)) : UC K n) γ g = cvAll ν m (fun i => lact (z i) (φ i)) g := by
  intro m
  induction m with
  | zero =>
    intro φ z γ _ h g
    have : γ = φ 0 := DFunLike.ext _ _ h
    subst this
    simp [cvAll]
  | succ m ih =>
    intro φ z γ h hγ g
    obtain ⟨γ', h1, h2⟩ := cvAll_ex ν m (fun i => φ i.succ) fun i => h _
    have h3 : (γ' : archGroup K n → ℂ) = cvAll ν m (fun i => φ i.succ) := funext h2
    have h4 : ∀ g, γ g = cv ν (φ 0) γ' g := fun g => by
      rw [hγ, h3]
      rfl
    have h5 := ih (fun i => φ i.succ) (fun i => z i.succ) γ' (fun i => h _) h2
    rw [Fin.prod_univ_succ, Subalgebra.coe_mul,
      lact_step ν (φ 0) γ' γ (h 0) h1 h4 _ _ (Subtype.property _) g, funext h5]
    rfl

private theorem pow_word (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (α : TI K n) (hα : SmoothT α) (k : ℕ) :
    SmoothT (GM.word ν α (List.replicate k none)) ∧ ∀ g, GM.word ν α (List.replicate k none) g = cvPow ν α k g := by
  induction k with
  | zero => exact ⟨hα, fun _ => rfl⟩
  | succ k ih =>
    refine ⟨(lactCv K n ν α (GM.word ν α (List.replicate k none)) _ hα (conv_apply ν _ _)).1, fun g => ?_⟩
    have h : GM.word ν α (List.replicate (k + 1) none) = GM.conv ν α (GM.word ν α (List.replicate k none)) := rfl
    rw [h, conv_apply, funext ih.2]
    rfl

end One

section Two

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {m : ℕ} {D : InfD σ m} {n : ℕ} {νE : Measure (archGroup E n)} [νE.IsHaarMeasure]
  {νF : Measure (archGroup F n)} [νF.IsHaarMeasure] {b a : TI F n} {aE : TI E n} {aF : TI F n}

private theorem conv_tens (hm : νE = Measure.map (glueA D n) (Measure.pi fun _ => νF))
    {ψ φ : Fin (m + 1) → TI F n} {β₁ β₂ : TI E n} (h1 : IsTens D ψ β₁) (h2 : IsTens D φ β₂) :
    IsTens D (fun i => GM.conv νF (ψ i) (φ i)) (GM.conv νE β₁ β₂) := by
  intro g
  obtain ⟨hc, -, -, hgc, -⟩ := archBasic F E σ m D n
  have h3 := (cvPowers (archGroup F n) νF m (ψ 0) (ψ 0) (ψ 0).continuous (ψ 0).hasCompactSupport
    (ψ 0).continuous (ψ 0).hasCompactSupport 0).2.2 (fun i => ψ i) (fun i => φ i)
    (fun i => ⟨(ψ i).continuous, (ψ i).hasCompactSupport⟩) (fun i => ⟨(φ i).continuous, (φ i).hasCompactSupport⟩)
  have h4 := congrFun h3 (fun i => compA D n i g)
  simp only [conv_apply]
  refine Eq.trans ?_ h4
  unfold cv
  rw [hm, integral_map hgc.aemeasurable]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [h1 _, h2 _, hc, map_mul, map_inv, Pi.mul_apply, Pi.inv_apply]
  · have : Continuous fun x : archGroup E n => β₁ x * β₂ (x⁻¹ * g) := by
      have := β₁.continuous
      have := β₂.continuous
      fun_prop
    exact this.aestronglyMeasurable

variable [IsTotallyComplex F] [IsTotallyComplex E]

private theorem a_smooth (hs : ArchSlot D νE νF b a aE aF) : SmoothT a := by
  have hc : Continuous fun x : archGroup F n => conj (b x⁻¹) := by
    have := b.continuous
    fun_prop
  have hk : HasCompactSupport fun x : archGroup F n => conj (b x⁻¹) :=
    (b.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)).comp_left (g := starRingEnd ℂ) (map_zero _)
  exact (lactCv F n νF b ⟨⟨_, hc⟩, hk⟩ a hs.smooth hs.sq).1

private theorem aF_smooth (hs : ArchSlot D νE νF b a aE aF) : SmoothT aF := by
  obtain ⟨γ, h1, h2⟩ := cvAll_ex νF m (fun _ => a) fun _ => a_smooth hs
  have : γ = aF := DFunLike.ext _ _ fun g => by rw [h2, hs.pow]; rfl
  exact this ▸ h1

private theorem letter_tens (hs : ArchSlot D νE νF b a aE aF) (x : Option (Ix E n)) :
    ∃ y : Fin (m + 1) → Subalgebra.center ℂ (UC F n), IsTens D (fun i => lact (y i) a) (GM.letter aE x) ∧
      GM.letter aF (GM.resIx F x) = lact ((∏ i, y i : Subalgebra.center ℂ (UC F n)) : UC F n) aF := by
  have ha := a_smooth hs
  cases x with
  | none =>
    refine ⟨1, fun g => ?_, ?_⟩
    · simp only [Pi.one_apply, OneMemClass.coe_one, (lactLaws F n a ha).2.1]
      exact hs.tens g
    · simp only [Pi.one_apply, Finset.prod_const_one, OneMemClass.coe_one, (lactLaws F n aF (aF_smooth hs)).2.1]
      rfl
  | some x =>
    obtain ⟨τ, i⟩ := x
    obtain ⟨k, hk⟩ := (positionOf F E σ m D).1 τ
    let c : Subalgebra.center ℂ (UC F n) := ⟨zc (τ.comp (algebraMap F E)) i, (jUnique F n _).2 i⟩
    refine ⟨Function.update 1 k c, fun g => ?_, ?_⟩
    · have h := lactTens F E σ m D n τ k hk (fun _ => a) aE (fun _ => ha) hs.tens i g
      refine h.trans (Finset.prod_congr rfl fun j _ => ?_)
      by_cases hj : j = k
      · subst hj
        simp [c]
      · simp [Function.update_of_ne hj, (lactLaws F n a ha).2.1]
    · have : (∏ i, (Function.update 1 k c : Fin (m + 1) → Subalgebra.center ℂ (UC F n)) i) = c := by
        rw [Finset.prod_update_of_mem (Finset.mem_univ k)]
        simp
      rw [this]
      rfl

private theorem word_main (hs : ArchSlot D νE νF b a aE aF) (w : List (Option (Ix E n))) :
    ∃ z : Fin (m + 1) → Subalgebra.center ℂ (UC F n),
      IsTens D (fun i => lact (z i) (GM.word νF a (List.replicate w.length none))) (GM.word νE aE w) ∧
      GM.word νF aF (w.map (GM.resIx F)) =
        lact ((∏ i, z i : Subalgebra.center ℂ (UC F n)) : UC F n) (GM.word νF aF (List.replicate w.length none)) := by
  have ha := a_smooth hs
  have hA := aF_smooth hs
  induction w with
  | nil =>
    refine ⟨1, fun g => ?_, ?_⟩
    · simp only [Pi.one_apply, OneMemClass.coe_one, List.length_nil, List.replicate_zero]
      simp only [GM.word, (lactLaws F n a ha).2.1]
      exact hs.tens g
    · simp only [Pi.one_apply, Finset.prod_const_one, OneMemClass.coe_one, List.length_nil, List.replicate_zero,
        List.map_nil, GM.word, (lactLaws F n aF hA).2.1]
  | cons x w ih =>
    obtain ⟨y, hy1, hy2⟩ := letter_tens hs x
    obtain ⟨z, hz1, hz2⟩ := ih
    refine ⟨fun i => y i * z i, fun g => ?_, ?_⟩
    · have ht := conv_tens hs.meas hy1 hz1 g
      refine ht.trans (Finset.prod_congr rfl fun i _ => ?_)
      rw [conv_apply]
      exact (lact_step νF a _ (GM.word νF a (List.replicate (w.length + 1) none)) ha (pow_word νF a ha _).1
        (conv_apply νF _ _) (y i) (z i) (z i).2 _).symm
    · have h : GM.word νF aF ((x :: w).map (GM.resIx F)) =
          GM.conv νF (GM.letter aF (GM.resIx F x)) (GM.word νF aF (w.map (GM.resIx F))) := rfl
      rw [h, hy2, hz2]
      refine DFunLike.ext _ _ fun g => ?_
      rw [conv_apply, Finset.prod_mul_distrib]
      exact (lact_step νF aF _ (GM.word νF aF (List.replicate (w.length + 1) none)) hA (pow_word νF aF hA _).1
        (conv_apply νF _ _) _ _ (Subtype.property _) _).symm

end Two

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.wordTens :
    UpperTheory.ConvolutionTheory.L1.WordTens := by
  intro F E _ _ _ _ _ _ _ σ m D n νE _ νF _ b a aE aF hs w
  obtain ⟨z, h1, h2⟩ := word_main hs w
  have ha := a_smooth hs
  have hA := aF_smooth hs
  obtain ⟨p1, p2⟩ := pow_word νF a ha w.length
  obtain ⟨q1, q2⟩ := pow_word νF aF hA w.length
  refine ⟨fun i => lact (z i) (GM.word νF a (List.replicate w.length none)), h1, fun g => ?_⟩
  rw [h2]
  refine cvAll_lact νF m (fun _ => GM.word νF a (List.replicate w.length none)) z _ (fun _ => p1) (fun g => ?_) g
  have h3 := (cvPowers (archGroup F n) νF m a a a.continuous a.hasCompactSupport a.continuous a.hasCompactSupport
    w.length).1
  have h4 : (aF : archGroup F n → ℂ) = cvPow νF a m := funext hs.pow
  rw [q2, funext p2, h4, ← h3]
