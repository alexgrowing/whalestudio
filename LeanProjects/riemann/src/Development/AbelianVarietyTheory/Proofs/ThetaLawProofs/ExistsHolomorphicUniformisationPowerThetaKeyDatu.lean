import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowUnif

def IsHolFamily {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Z : Scheme.{0}} (c : E → (Sp ℂ ⟶ Z)) : Prop :=
  ∀ (U : Z.Opens) (f : Γ(Z, U)), IsOpen {z | ⊤ ≤ c z ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun z => valAt' (c z) U f) {z | ⊤ ≤ c z ⁻¹ᵁ U}

section Hol

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem IsHolFamily.comp {Z Z' : Scheme.{0}} {c : E → (Sp ℂ ⟶ Z)} (h : IsHolFamily c) (φ : Z ⟶ Z') :
    IsHolFamily (fun z => c z ≫ φ) := fun U f => by
  have := h (φ ⁻¹ᵁ U) ((φ.app U).hom f)
  simp only [valAt'_comp, ← top_le_preimage_comp] at this
  exact this

theorem IsHolFamily.precomp {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {Z : Scheme.{0}}
    {c : E → (Sp ℂ ⟶ Z)} (h : IsHolFamily c) {T : E' → E} (hT : Differentiable ℂ T) :
    IsHolFamily (fun z => c (T z)) := fun U f =>
  ⟨(h U f).1.preimage hT.continuous, (h U f).2.comp hT.differentiableOn fun _ hz => hz⟩

theorem isHolFamily_const {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) : IsHolFamily (fun _ : E => x) := fun U f =>
  ⟨isOpen_const, differentiableOn_const _⟩

theorem isHolFamily_tensor (X Y : Over (Sp ℂ)) (c : E → (𝟙_ (Over (Sp ℂ)) ⟶ X ⊗ Y))
    (h0 : IsHolFamily (Z := X.left) (fun z => (c z ≫ fst _ _).left))
    (h1 : IsHolFamily (Z := Y.left) (fun z => (c z ≫ snd _ _).left)) :
    IsHolFamily (Z := (X ⊗ Y).left) (fun z => (c z).left) := by
  intro U f
  have := holFamily_lift valAt'_rules E Set.univ X Y (fun z => c z ≫ fst _ _)
    (fun z => c z ≫ snd _ _) (fun U f => by simpa only [Set.mem_univ, true_and] using h0 U f)
    (fun U f => by simpa only [Set.mem_univ, true_and] using h1 U f) U f
  simpa only [Set.mem_univ, true_and, ← comp_lift, lift_fst_snd, Category.comp_id] using this

theorem isHolFamily_powObj (G : Over (Sp ℂ)) : ∀ (n : ℕ) (c : E → (𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj G n)),
    (∀ i, IsHolFamily (Z := G.left) (fun z => (c z ≫ Out.powPr G i).left)) →
    IsHolFamily (Z := (Out.powObj G n).left) (fun z => (c z).left)
  | 0, c, _ => by
    have : c = fun _ => 𝟙 _ := funext fun z => toUnit_unique _ _
    subst this
    exact isHolFamily_const _
  | n + 1, c, h => by
    refine isHolFamily_tensor G (Out.powObj G n) c (h 0) (isHolFamily_powObj G n (fun z => c z ≫ snd _ _) fun i => ?_)
    have h1 : (fun z => ((c z ≫ snd G (Out.powObj G n)) ≫ Out.powPr G i).left) =
        fun z => (c z ≫ Out.powPr G i.succ).left := funext fun z => congrArg _ (Category.assoc _ _ _)
    exact h1 ▸ h i.succ

theorem isHolFamily_pow {G' G : Over (Sp ℂ)} [GrpObj G'] [GrpObj G] {j : ℕ} (p : Out.IsPowGrp G' G j)
    (c : E → (𝟙_ (Over (Sp ℂ)) ⟶ G'))
    (h : ∀ i, IsHolFamily (Z := G.left) (fun z => (c z ≫ p.pr i).left)) :
    IsHolFamily (Z := G'.left) (fun z => (c z).left) := by
  let φ : G' ⟶ Out.powObj G j := (Out.powIsLimit G j).lift (Fan.mk _ p.pr)
  let ψ : Out.powObj G j ⟶ G' := p.lim.lift (Fan.mk _ (Out.powPr G))
  have hφ : ∀ i, φ ≫ Out.powPr G i = p.pr i := fun i => (Out.powIsLimit G j).fac (Fan.mk _ p.pr) ⟨i⟩
  have hψ : ∀ i, ψ ≫ p.pr i = Out.powPr G i := fun i => p.lim.fac (Fan.mk _ (Out.powPr G)) ⟨i⟩
  have hφψ : φ ≫ ψ = 𝟙 _ := p.lim.hom_ext fun ⟨i⟩ => by
    change (φ ≫ ψ) ≫ p.pr i = 𝟙 _ ≫ p.pr i
    rw [Category.assoc, hψ, hφ, Category.id_comp]
  have h1 := (isHolFamily_powObj G j (fun z => c z ≫ φ) (fun i => by
    simpa only [Category.assoc, hφ] using h i)).comp ψ.left
  have h2 : ∀ z, (c z ≫ φ).left ≫ ψ.left = (c z).left := fun z => by
    rw [← Over.comp_left, Category.assoc, hφψ, Category.comp_id]
  have h3 : (fun z => (c z ≫ φ).left ≫ ψ.left) = fun z => (c z).left := funext h2
  exact h3 ▸ h1

end Hol

section Val

variable {X Y : Scheme.{0}}

theorem val_res (x : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U) (s : Γ(X, U)ˣ) (hV : ⊤ ≤ x ⁻¹ᵁ V) :
    valAt' x V (res h s).val = valAt' x U s.val :=
  valAt'_map x (homOfLE h).op s.val hV

theorem val_res_pull (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) {V : X.Opens} (h : V ≤ φ ⁻¹ᵁ U) (s : Γ(Y, U)ˣ)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) : valAt' x V (res h (pullU φ U s)).val = valAt' (x ≫ φ) U s.val :=
  (val_res x h _ hV).trans (valAt'_comp x φ U s.val)

theorem le_wchart_iff (x : Sp ℂ ⟶ Y) (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (jj : K → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ jj ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (jj k) := by
  simp only [top_le_preimage_iff_mem]
  exact Set.mem_iInter

theorem exists_chart {L : LB X} (hL : L.IsLB) (x : Sp ℂ ⟶ X) : ∃ i, ⊤ ≤ x ⁻¹ᵁ L.U i := by
  have : x (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact ⟨i, (top_le_preimage_iff_mem x _).2 hi⟩

theorem val_g_self {L : LB X} (hL : L.IsLB) (x : Sp ℂ ⟶ X) (i : L.ι) (h : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    valAt' x (L.U i ⊓ L.U i) (L.g i i).val = 1 := by
  rw [← val_res x (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) _ h, hL.g_self, Units.val_one, valAt'_one x h]

theorem val_gen {L : LB X} {t : L.Gen} (ht : t.IsGen) (x : Sp ℂ ⟶ X) (i k : L.ι) (h : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U k)) :
    valAt' x (L.U i) (t.s i).val = valAt' x (L.U i ⊓ L.U k) (L.g i k).val * valAt' x (L.U k) (t.s k).val := by
  rw [← val_res x (inf_le_left : L.U i ⊓ L.U k ≤ _) _ h, ht i k, Units.val_mul, valAt'_mul, val_res x _ _ h]

theorem val_div_g (M L : LB X) (x : Sp ℂ ⟶ X) (a a' : M.ι) (b b' : L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ (M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b'))) :
    valAt' x (M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b')) ((LB.div M L).g (a, b) (a', b')).val =
      valAt' x (M.U a ⊓ M.U a') (M.g a a').val * (valAt' x (L.U b ⊓ L.U b') (L.g b b').val)⁻¹ := by
  rw [← val_res x (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) (M.g a a') h,
    ← val_res x (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) (L.g b b') h,
    ← valAt'_units_inv x h, ← valAt'_mul]
  rfl

theorem val_linComb_g (x : Sp ℂ ⟶ Y) (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (jj jj' : K → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ jj ⊓ LB.wchart L φ jj')) :
    valAt' x (LB.wchart L φ jj ⊓ LB.wchart L φ jj') ((LB.LinComb L φ (fun _ => 1)).g jj jj').val =
      ∏ k, valAt' (x ≫ φ k) (L.U (jj k) ⊓ L.U (jj' k)) (L.g (jj k) (jj' k)).val := by
  refine (valAt'_units_prod x h Finset.univ _).trans (Finset.prod_congr rfl fun k _ => ?_)
  rw [zpow_one]
  exact val_res_pull x (φ k) (L.U (jj k) ⊓ L.U (jj' k)) _ _ h

theorem val_iso (x : Sp ℂ ⟶ Y) (L : LB X) (L' : LB Y) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (w : LB.Iso L' (LB.LinComb L φ (fun _ => 1))) (hw : w.IsGen) (jj jj' : K → L.ι) (b b' : L'.ι)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ jj) (h₂ : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ jj')
    (h₃ : ⊤ ≤ x ⁻¹ᵁ L'.U b) (h₄ : ⊤ ≤ x ⁻¹ᵁ L'.U b') :
    valAt' x (LB.wchart L φ jj ⊓ L'.U b) (w.s (jj, b)).val =
      (∏ k, valAt' (x ≫ φ k) (L.U (jj k) ⊓ L.U (jj' k)) (L.g (jj k) (jj' k)).val) *
        (valAt' x (L'.U b ⊓ L'.U b') (L'.g b b').val)⁻¹ *
        valAt' x (LB.wchart L φ jj' ⊓ L'.U b') (w.s (jj', b')).val := by
  have hV : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ jj ⊓ L'.U b ⊓ (LB.wchart L φ jj' ⊓ L'.U b')) := by
    simp only [top_le_preimage_inf]; exact ⟨⟨h₁, h₃⟩, h₂, h₄⟩
  have h12 : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ jj ⊓ LB.wchart L φ jj') := (top_le_preimage_inf _ _ _).2 ⟨h₁, h₂⟩
  rw [← val_linComb_g x L φ jj jj' h12]
  exact (val_gen hw x (jj, b) (jj', b') hV).trans
    (congrArg (· * _) (val_div_g (LB.LinComb L φ (fun _ => 1)) L' x jj jj' b b' hV))

end Val

theorem exists_frame {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {X Y : Scheme.{0}} {c : E → (Sp ℂ ⟶ Y)}
    (hc : IsHolFamily c) {L : LB X} (hL : L.IsLB) {L' : LB Y} (hL' : L'.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (w : LB.Iso L' (LB.LinComb L φ (fun _ => 1))) (hw : w.IsGen) (fr : K → L.ι → E → ℂ)
    (hhol : ∀ k i, DifferentiableOn ℂ (fr k i) {z | ⊤ ≤ (c z ≫ φ k) ⁻¹ᵁ L.U i})
    (hne : ∀ k i z, ⊤ ≤ (c z ≫ φ k) ⁻¹ᵁ L.U i → fr k i z ≠ 0)
    (hco : ∀ k i i' z, ⊤ ≤ (c z ≫ φ k) ⁻¹ᵁ (L.U i ⊓ L.U i') →
      fr k i z = valAt' (c z ≫ φ k) (L.U i ⊓ L.U i') (L.g i i').val * fr k i' z) :
    ∃ fr' : L'.ι → E → ℂ, (∀ b, DifferentiableOn ℂ (fr' b) {z | ⊤ ≤ c z ⁻¹ᵁ L'.U b}) ∧
      (∀ b z, ⊤ ≤ c z ⁻¹ᵁ L'.U b → fr' b z ≠ 0) ∧
      (∀ b b' z, ⊤ ≤ c z ⁻¹ᵁ (L'.U b ⊓ L'.U b') →
        fr' b z = valAt' (c z) (L'.U b ⊓ L'.U b') (L'.g b b').val * fr' b' z) ∧
      ∀ jj b z, ⊤ ≤ c z ⁻¹ᵁ LB.wchart L φ jj → ⊤ ≤ c z ⁻¹ᵁ L'.U b →
        ∏ k, fr k (jj k) z = valAt' (c z) (LB.wchart L φ jj ⊓ L'.U b) (w.s (jj, b)).val * fr' b z := by
  choose j₀ hj₀ using fun z k => exists_chart hL (c z ≫ φ k)
  have hj : ∀ z, ⊤ ≤ c z ⁻¹ᵁ LB.wchart L φ (j₀ z) := fun z => (le_wchart_iff _ L φ _).2 (hj₀ z)
  let ω : (K → L.ι) → L'.ι → E → ℂ := fun jj b z => valAt' (c z) (LB.wchart L φ jj ⊓ L'.U b) (w.s (jj, b)).val
  let G : (K → L.ι) → L'.ι → E → ℂ := fun jj b z => (∏ k, fr k (jj k) z) / ω jj b z
  have hω : ∀ jj b z, ⊤ ≤ c z ⁻¹ᵁ LB.wchart L φ jj → ⊤ ≤ c z ⁻¹ᵁ L'.U b → ω jj b z ≠ 0 := fun jj b z h₁ h₂ =>
    valAt'_unit_ne_zero (c z) ((top_le_preimage_inf _ _ _).2 ⟨h₁, h₂⟩) (w.s (jj, b))
  have hG : ∀ jj jj' b b' z, ⊤ ≤ c z ⁻¹ᵁ LB.wchart L φ jj → ⊤ ≤ c z ⁻¹ᵁ LB.wchart L φ jj' →
      ⊤ ≤ c z ⁻¹ᵁ L'.U b → ⊤ ≤ c z ⁻¹ᵁ L'.U b' →
      G jj b z = valAt' (c z) (L'.U b ⊓ L'.U b') (L'.g b b').val * G jj' b' z := by
    intro jj jj' b b' z h₁ h₂ h₃ h₄
    have hk : ∀ k, ⊤ ≤ (c z ≫ φ k) ⁻¹ᵁ (L.U (jj k) ⊓ L.U (jj' k)) := fun k => (top_le_preimage_inf _ _ _).2
      ⟨(le_wchart_iff _ L φ _).1 h₁ k, (le_wchart_iff _ L φ _).1 h₂ k⟩
    have e₁ : ω jj b z = _ * _ * ω jj' b' z := val_iso (c z) L L' φ w hw jj jj' b b' h₁ h₂ h₃ h₄
    have e₂ : ∏ k, fr k (jj k) z = (∏ k, valAt' (c z ≫ φ k) (L.U (jj k) ⊓ L.U (jj' k)) (L.g (jj k) (jj' k)).val) *
        ∏ k, fr k (jj' k) z := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => hco k _ _ z (hk k)
    have n₁ : (∏ k, valAt' (c z ≫ φ k) (L.U (jj k) ⊓ L.U (jj' k)) (L.g (jj k) (jj' k)).val) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => valAt'_unit_ne_zero _ (hk k) _
    have n₂ := valAt'_unit_ne_zero (c z) ((top_le_preimage_inf _ _ _).2 ⟨h₃, h₄⟩) (L'.g b b')
    have n₃ := hω jj' b' z h₂ h₄
    simp only [G]
    rw [e₁, e₂]
    field_simp
  have hG' : ∀ jj b z, ⊤ ≤ c z ⁻¹ᵁ LB.wchart L φ jj → ⊤ ≤ c z ⁻¹ᵁ L'.U b → G (j₀ z) b z = G jj b z := by
    intro jj b z h₁ h₂
    rw [hG (j₀ z) jj b b z (hj z) h₁ h₂ h₂, val_g_self hL' _ _ h₂, _root_.one_mul]
  refine ⟨fun b z => G (j₀ z) b z, fun b z₀ hz₀ => ?_, fun b z hz => ?_, fun b b' z hz => ?_, fun jj b z h₁ h₂ => ?_⟩
  · have hS := (hc (LB.wchart L φ (j₀ z₀) ⊓ L'.U b) (w.s (j₀ z₀, b)).val)
    have hS₀ := hS.1.mem_nhds ((top_le_preimage_inf _ _ _).2 ⟨hj z₀, hz₀⟩)
    have hd : DifferentiableAt ℂ (G (j₀ z₀) b) z₀ := by
      simp only [G, div_eq_mul_inv]
      classical
      refine DifferentiableAt.mul
        (HasFDerivAt.finsetProd fun k _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
        ((hS.2.differentiableAt hS₀).inv (hω _ _ _ (hj z₀) hz₀))
      exact (hhol k _).differentiableAt (((hc.comp (φ k)) _ 0).1.mem_nhds (hj₀ z₀ k))
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hS₀] with z hz
    exact hG' _ _ _ ((top_le_preimage_inf _ _ _).1 hz).1 ((top_le_preimage_inf _ _ _).1 hz).2
  · exact div_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => hne k _ z (hj₀ z k)) (hω _ _ _ (hj z) hz)
  · exact hG _ _ _ _ z (hj z) (hj z) ((top_le_preimage_inf _ _ _).1 hz).1 ((top_le_preimage_inf _ _ _).1 hz).2
  · beta_reduce
    rw [hG' jj b z h₁ h₂]
    exact (mul_div_cancel₀ _ (hω jj b z h₁ h₂)).symm

section Blocks

variable {j g n : ℕ} (e : Fin j × Fin g ≃ Fin n)

def blockPr (i : Fin j) : (Fin n → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (e (i, k))

def blockIn (i : Fin j) : (Fin g → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun q => if i = (e.symm q).1 then ContinuousLinearMap.proj (e.symm q).2 else 0

theorem blockPr_apply (i : Fin j) (z : Fin n → ℂ) : blockPr e i z = fun k => z (e (i, k)) := rfl

theorem blockIn_apply (i : Fin j) (z : Fin g → ℂ) :
    blockIn e i z = fun q => if i = (e.symm q).1 then z (e.symm q).2 else 0 := by
  funext q
  simp only [blockIn, ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

theorem blockPr_blockIn (i i' : Fin j) (z : Fin g → ℂ) :
    blockPr e i' (blockIn e i z) = if i = i' then z else 0 := by
  rw [blockPr_apply, blockIn_apply]
  split_ifs with h <;> funext k <;> simp [h]

theorem sum_blockIn_blockPr (z : Fin n → ℂ) : ∑ i, blockIn e i (blockPr e i z) = z := by
  funext q
  simp only [Finset.sum_apply, blockIn_apply, blockPr_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Prod.mk.eta, Equiv.apply_symm_apply]

def blockLat (Λ : Submodule ℤ (Fin g → ℂ)) : Submodule ℤ (Fin n → ℂ) where
  carrier := {z | ∀ i, blockPr e i z ∈ Λ}
  add_mem' := fun ha hb i => by rw [map_add]; exact Λ.add_mem (ha i) (hb i)
  zero_mem' := fun i => by rw [map_zero]; exact Λ.zero_mem
  smul_mem' := fun c z hz i => by rw [map_zsmul]; exact Λ.smul_mem c (hz i)

theorem blockLat_discrete (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] : DiscreteTopology (blockLat e Λ) := by
  refine DiscreteTopology.of_continuous_injective (β := Fin j → Λ)
    (f := fun z i => ⟨blockPr e i z.1, z.2 i⟩)
    (continuous_pi fun i => ((blockPr e i).continuous.comp continuous_subtype_val).subtype_mk _) fun z z' h => ?_
  refine Subtype.ext ?_
  rw [← sum_blockIn_blockPr e z.1, ← sum_blockIn_blockPr e z'.1]
  exact Finset.sum_congr rfl fun i _ => congrArg _ (congrArg Subtype.val (congrFun h i))

theorem blockLat_full (Λ : Submodule ℤ (Fin g → ℂ)) (h : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    Submodule.span ℝ (blockLat e Λ : Set (Fin n → ℂ)) = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  rw [← sum_blockIn_blockPr e z]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hz : blockPr e i z ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := h ▸ Submodule.mem_top
  generalize blockPr e i z = a at hz
  induction hz using Submodule.span_induction with
  | mem a ha =>
    refine Submodule.subset_span fun i' => ?_
    rw [blockPr_blockIn]
    split_ifs
    exacts [ha, Λ.zero_mem]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [ContinuousLinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ r ha

end Blocks

section Pow

variable {G' G : Over (Sp ℂ)} [GrpObj G'] [GrpObj G] {j : ℕ} (p : Out.IsPowGrp G' G j)

theorem pow_hom_ext {T : Over (Sp ℂ)} {a b : T ⟶ G'} (h : ∀ i, a ≫ p.pr i = b ≫ p.pr i) : a = b :=
  p.lim.hom_ext fun ⟨i⟩ => h i

def powLift {T : Over (Sp ℂ)} (a : Fin j → (T ⟶ G)) : T ⟶ G' := p.lim.lift (Fan.mk _ a)

theorem powLift_pr {T : Over (Sp ℂ)} (a : Fin j → (T ⟶ G)) (i : Fin j) : powLift p a ≫ p.pr i = a i :=
  p.lim.fac (Fan.mk _ a) ⟨i⟩

variable {L : LB G.left} {g : ℕ} (u : HolUnif G L g)

theorem ex_zero : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem

theorem one_left : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G).left = eSec G := by
  rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  rfl

theorem exists_powUnif (hL : L.IsLB) {L' : LB G'.left} (hL' : L'.IsLB) (w : LB.Iso L' (Out.boxLB L p.pr))
    (hw : w.IsGen) {n : ℕ} (e : Fin j × Fin g ≃ Fin n) :
    ∃ u' : HolUnif G' L' n, (∀ z, z ∈ u'.Λ ↔ ∀ i, blockPr e i z ∈ u.Λ) ∧
      (∀ z i, u'.ex z ≫ p.pr i = u.ex (blockPr e i z)) ∧
      ∀ jj b z, ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (Out.boxLB L p.pr).U jj → ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U b →
        ∏ i, u.fr (jj i) (blockPr e i z) =
          valAt' (u'.ex z).left ((Out.boxLB L p.pr).U jj ⊓ L'.U b) (w.s (jj, b)).val * u'.fr b z := by
  let ex : (Fin n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ G') := fun z => powLift p fun i => u.ex (blockPr e i z)
  have hex : ∀ z i, ex z ≫ p.pr i = u.ex (blockPr e i z) := fun z i => powLift_pr p _ i
  let c : (Fin n → ℂ) → (Sp ℂ ⟶ G'.left) := fun z => (ex z).left
  let d : (Fin g → ℂ) → (Sp ℂ ⟶ G.left) := fun z => (u.ex z).left
  have hcd : ∀ z i, c z ≫ (p.pr i).left = d (blockPr e i z) := fun z i => congrArg (·.left) (hex z i)
  have hd : IsHolFamily d := u.hol
  have hc : IsHolFamily c := isHolFamily_pow p ex fun i => by
    simp only [hex]
    exact hd.precomp (blockPr e i).differentiable
  obtain ⟨fr', h₁, h₂, h₃, h₄⟩ := exists_frame hc hL hL' (fun i => (p.pr i).left) w hw
    (fun i a z => u.fr a (blockPr e i z))
    (fun i a => by
      simp only [hcd]
      exact (u.fr_hol a).comp (blockPr e i).differentiable.differentiableOn fun _ hz => hz)
    (fun i a z hz => u.fr_ne a _ (by rw [hcd] at hz; exact hz))
    (fun i a a' z hz => by
      rw [hcd] at hz ⊢
      exact u.fr_compat a a' _ hz)
  have := u.discrete
  refine ⟨⟨ex, fun z z' => pow_hom_ext p fun i => ?_, fun a => ?_, blockLat e u.Λ, fun z => ?_,
    blockLat_discrete e u.Λ, blockLat_full e u.Λ u.full, hc, fr', h₁, h₂, h₃⟩, fun z => Iff.rfl, hex, h₄⟩
  · have := p.hom i
    rw [MonObj.mul_comp, hex, hex, hex, map_add, u.ex_add]
  · choose z hz using fun i => u.ex_onto (a ≫ p.pr i)
    refine ⟨∑ i, blockIn e i (z i), pow_hom_ext p fun i => ?_⟩
    rw [hex, ← hz, map_sum]
    simp only [blockPr_blockIn, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · constructor
    · intro h i
      have := p.hom i
      rw [← u.ker, ← hex, h, MonObj.one_comp]
    · intro h
      refine pow_hom_ext p fun i => ?_
      have := p.hom i
      rw [hex, MonObj.one_comp, (u.ker _).2 (h i)]

variable {L' : LB G'.left} {n : ℕ} (u' : HolUnif G' L' n)

theorem isDiff_map (φ : G ⟶ G') (T : (Fin g → ℂ) →L[ℂ] (Fin n → ℂ)) (hT : ∀ z, u'.ex (T z) = u.ex z ≫ φ)
    {a : Fin g → ℂ} {v : epsR ℂ ⟶ G} (ht : IsTangent (v ≫ φ)) (h : u.IsDiff a v) : u'.IsDiff (T a) (v ≫ φ) := by
  intro U hU f
  have h0 : ⊤ ≤ (u'.ex 0).left ⁻¹ᵁ U := by
    rw [ex_zero, one_left]
    intro x hx
    have h1 : (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (v ≫ φ).left) x ∈ U := hU (Set.mem_univ _)
    rw [ht] at h1
    exact h1
  have hF : DifferentiableAt ℂ (fun z => valAt' (u'.ex z).left U f) (T 0) := by
    rw [map_zero]
    exact (u'.hol U f).2.differentiableAt ((u'.hol U f).1.mem_nhds h0)
  have h1 := h (φ.left ⁻¹ᵁ U) hU ((φ.left.app U).hom f)
  have h2 : (fun z => valAt' (u.ex z).left (φ.left ⁻¹ᵁ U) ((φ.left.app U).hom f)) =
      (fun z => valAt' (u'.ex z).left U f) ∘ T := funext fun z => by
    refine (valAt'_comp _ _ _ _).trans ?_
    rw [Function.comp_apply, hT]
    rfl
  rw [h2, fderiv_comp _ hF T.differentiableAt, T.fderiv, map_zero] at h1
  refine Eq.trans ?_ h1
  have h3 : (v ≫ φ).left.appLE U ⊤ hU = φ.left.app U ≫ v.left.appLE (φ.left ⁻¹ᵁ U) ⊤ hU :=
    Scheme.Hom.comp_appLE v.left φ.left U ⊤ hU
  rw [h3]
  rfl

end Pow

theorem val_boxRig {G' G : Over (Sp ℂ)} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] {j : ℕ}
    (p : Out.IsPowGrp G' G j) {L : LB G.left} {L' : LB G'.left} (w : LB.Iso L' (Out.boxLB L p.pr))
    (r : LB.Gen (L.pull (eSec G))) (r' : LB.Gen (L'.pull (eSec G')))
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) r' (Out.boxRig p L r))
    (a : L.ι) (b : (L'.pull (eSec G')).ι) (ha : ⊤ ≤ eSec G' ⁻¹ᵁ (Out.boxLB L p.pr).U fun _ => a)
    (hb : ⊤ ≤ (L'.pull (eSec G')).U b) :
    ∏ _i : Fin j, valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec G)).U fun _ => a) (r.s fun _ => a).val =
      valAt' (eSec G') ((Out.boxLB L p.pr).U (fun _ => a) ⊓ L'.U (b PUnit.unit)) (w.s (fun _ => a, b PUnit.unit)).val *
        valAt' (𝟙 (Sp ℂ)) ((L'.pull (eSec G')).U b) (r'.s b).val := by
  have ha' : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ ((Out.boxLB L p.pr).pull (eSec G')).U fun _ _ => a :=
    fun x hx => Set.mem_iInter.2 fun _ => ha hx
  have hV : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ (((Out.boxLB L p.pr).pull (eSec G')).U (fun _ _ => a) ⊓ (L'.pull (eSec G')).U b) :=
    (top_le_preimage_inf _ _ _).2 ⟨ha', hb⟩
  have h1 := (val_res (𝟙 (Sp ℂ)) _ _ hV).symm.trans
    ((congrArg (fun s => valAt' (𝟙 (Sp ℂ)) _ (Units.val s)) (h (fun _ _ => a, b))).trans (valAt'_mul _ _ _ _))
  refine Eq.trans ?_ (h1.trans (congrArg₂ (· * ·) ?_ (val_res _ _ _ hV)))
  · refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) (valAt'_units_prod (κ := Fin j) _ ha' Finset.univ _).symm
    have hi : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ LB.wchart (L.pull (p.pr i).left) (fun _ : PUnit => eSec G') (fun _ _ => a) :=
      top_le_preimage_mono _ (Out.GeneratorPullback.box_le L (fun i => (p.pr i).left) (fun _ : PUnit => eSec G') (fun _ _ => a) i) ha'
    refine Eq.trans ?_ (val_res _ _ _ ha').symm
    exact (val_res_pull (𝟙 (Sp ℂ)) (𝟙 (Sp ℂ)) _ _ _ hi).symm
  · refine (valAt'_units_prod (κ := PUnit) _ hV Finset.univ _).trans ?_
    rw [Fintype.prod_unique, zpow_one]
    exact val_res_pull (𝟙 (Sp ℂ)) (eSec G') ((Out.boxLB L p.pr).U (fun _ => a) ⊓ L'.U (b PUnit.unit)) _ _ hV

theorem exists_holUnif_pow : ∀ (x y : KeyIn ℂ) (j : ℕ) (u : HolUnif x.P.A x.P.L x.P.g) (θ : (Fin x.P.g → ℂ) → ℂ) (W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ), GlobalTheory.KeyPow.IsKeyPow y x j → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) → ∃ (e : Fin j × Fin x.P.g ≃ Fin y.P.g) (u' : HolUnif y.P.A y.P.L y.P.g), (∀ z, z ∈ u'.Λ ↔ ∀ i, (fun k => z (e (i, k))) ∈ u.Λ) ∧ u'.IsRig y.rig ∧ u'.IsFn y.th (fun z => ∏ i, θ (fun k => z (e (i, k)))) ∧ ∀ p, u'.IsDiff (fun q => if (e.symm p).1 = (e.symm q).1 then W (e.symm p).2 (e.symm q).2 else 0) (y.v p) := by
  rintro x y j u θ W ⟨p, hg, hr, ht, hv⟩ hrig hfn hdiff
  let e : Fin j × Fin x.P.g ≃ Fin y.P.g := finProdFinEquiv.trans (finCongr hg)
  obtain ⟨u', hΛ, hex, hfr⟩ := exists_powUnif p.toIsPowGrp u x.P.isLB y.P.isLB p.w p.w_gen e
  let c : (Fin y.P.g → ℂ) → (Sp ℂ ⟶ y.P.A.left) := fun z => (u'.ex z).left
  let d : (Fin x.P.g → ℂ) → (Sp ℂ ⟶ x.P.A.left) := fun z => (u.ex z).left
  have hcd : ∀ z i, c z ≫ (p.pr i).left = d (blockPr e i z) := fun z i => congrArg (·.left) (hex z i)
  refine ⟨e, u', hΛ, fun b hb => ?_, fun b z hb => ?_, fun q => ?_⟩
  · have := y.P.isAb.comm
    have := x.P.isAb.comm
    obtain ⟨a, ha⟩ := exists_chart x.P.isLB (d 0)
    have hc0 : c 0 = eSec y.P.A := (congrArg (·.left) (ex_zero u')).trans one_left
    have hd0 : d 0 = eSec x.P.A := (congrArg (·.left) (ex_zero u)).trans one_left
    have h₁ : ⊤ ≤ c 0 ⁻¹ᵁ (Out.boxLB x.P.L p.pr).U fun _ => a :=
      (le_wchart_iff _ _ _ _).2 fun i => by rw [hcd, map_zero]; exact ha
    have h₂ : ⊤ ≤ c 0 ⁻¹ᵁ y.P.L.U (b PUnit.unit) := by
      rw [hc0]
      exact hb.trans (LB.wchart_le y.P.L (fun _ : PUnit => eSec y.P.A) b PUnit.unit)
    have h₃ : ⊤ ≤ (x.P.L.pull (eSec x.P.A)).U fun _ => a := by
      rw [hd0] at ha
      exact fun s hs => Set.mem_iInter.2 fun _ => ha hs
    have e₁ : _ = valAt' (c 0) _ _ * _ := hfr _ _ 0 h₁ h₂
    have hne := valAt'_unit_ne_zero (c 0) ((top_le_preimage_inf _ _ _).2 ⟨h₁, h₂⟩) (p.w.s (fun _ => a, b PUnit.unit))
    have e₂ := val_boxRig p.toIsPowGrp p.w x.rig y.rig hr a b (hc0 ▸ h₁) hb
    rw [hc0] at e₁ hne
    refine mul_left_cancel₀ hne (e₁.symm.trans (Eq.trans (Finset.prod_congr rfl fun i _ => ?_) e₂))
    rw [map_zero]
    exact hrig _ h₃
  · choose jj hjj using fun i => exists_chart x.P.isLB (d (blockPr e i z))
    have h₁ : ⊤ ≤ c z ⁻¹ᵁ (Out.boxLB x.P.L p.pr).U jj :=
      (le_wchart_iff _ _ _ _).2 fun i => by rw [hcd]; exact hjj i
    have hV : ⊤ ≤ c z ⁻¹ᵁ ((Out.boxLB x.P.L p.pr).U jj ⊓ y.P.L.U b) := (top_le_preimage_inf _ _ _).2 ⟨h₁, hb⟩
    have e₁ : _ = valAt' (c z) _ _ * _ := hfr _ _ z h₁ hb
    have hne := valAt'_unit_ne_zero (c z) hV (p.w.s (jj, b))
    have e₂ := congrArg (valAt' (c z) _) (ht jj b fun i =>
      inf_le_left.trans (LB.wchart_le x.P.L (fun i => (p.pr i).left) jj i))
    rw [valAt'_prod _ hV, valAt'_mul, valAt'_res _ _ _ hV] at e₂
    refine mul_left_cancel₀ hne (e₂.symm.trans ?_)
    rw [mul_left_comm]
    refine Eq.trans ?_ (congrArg (_ * ·) e₁)
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [valAt'_appLE _ _ _ _ _ _ hV, hcd]
    exact hfn _ _ (hjj i)
  · obtain ⟨⟨i, k⟩, rfl⟩ := e.surjective q
    let ι' : x.P.A ⟶ y.P.A := powLift p.toIsPowGrp fun i' => if i = i' then 𝟙 _ else 1
    have hι : ∀ {T : Over (Sp ℂ)} (s : T ⟶ x.P.A) (i' : Fin j),
        (s ≫ ι') ≫ p.pr i' = if i = i' then s else 1 := fun s i' => by
      rw [Category.assoc, powLift_pr]
      split_ifs
      exacts [Category.comp_id _, MonObj.comp_one _]
    have hq : y.v (e (i, k)) = x.v k ≫ ι' := pow_hom_ext p.toIsPowGrp fun i' => (hv i i' k).trans (hι _ i').symm
    have hT : ∀ z, u'.ex (blockIn e i z) = u.ex z ≫ ι' := fun z => pow_hom_ext p.toIsPowGrp fun i' => by
      rw [hex, blockPr_blockIn, hι]
      split_ifs
      exacts [rfl, ex_zero u]
    have := isDiff_map u u' ι' (blockIn e i) hT (hq ▸ y.basis.1 _) (hdiff k)
    rw [blockIn_apply, ← hq] at this
    simpa only [Equiv.symm_apply_apply] using this

end GlobalTheory.PowUnif
end
