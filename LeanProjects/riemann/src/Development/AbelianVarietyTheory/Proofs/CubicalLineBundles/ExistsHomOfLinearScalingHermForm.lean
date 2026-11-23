import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DenseClosedPoints

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory
namespace AnalyticHom
open CubeValues SymmetricSemicharacter ComplexPoints AffinePointValues

section Values

variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)

lemma val_mul {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f f' : Γ(X, U)) :
    valAt' x U (f * f') = valAt' x U f * valAt' x U f' := by
  obtain ⟨e, he⟩ := (valueRules X x).2.1 U h
  simp only [he, map_mul]

lemma val_add {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f f' : Γ(X, U)) :
    valAt' x U (f + f') = valAt' x U f + valAt' x U f' := by
  obtain ⟨e, he⟩ := (valueRules X x).2.1 U h
  simp only [he, map_add]

lemma val_one {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) : valAt' x U 1 = 1 := by
  obtain ⟨e, he⟩ := (valueRules X x).2.1 U h
  simp only [he, map_one]

lemma val_zero {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) : valAt' x U 0 = 0 := by
  obtain ⟨e, he⟩ := (valueRules X x).2.1 U h
  simp only [he, map_zero]

lemma val_resG {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valAt' x V (resG X hVU f) = valAt' x U f :=
  (valueRules X x).2.2.1 U V hVU f h

lemma val_appLE {Y : Scheme.{0}} (φ : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (h : V ≤ φ ⁻¹ᵁ U)
    (f : Γ(Y, U)) (hx : ⊤ ≤ x ⁻¹ᵁ V) :
    valAt' x V ((φ.appLE U V h).hom f) = valAt' (x ≫ φ) U f := by
  rw [← (valueRules X x).2.2.2.1, ← val_resG x h hx]
  rfl

lemma le_preimage_mono {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ U :=
  fun _ hp => hVU (h hp)

lemma val_sec {L : LB X} (s : L.Sec) (i j : L.ι) (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valAt' x (L.U i) (s.f i) =
      valAt' x (L.U i ⊓ L.U j) (L.g i j).val * valAt' x (L.U j) (s.f j) := by
  have hij := (le_preimage_inf x _ _).2 ⟨hi, hj⟩
  rw [← val_resG x inf_le_left hij (s.f i), ← val_resG x inf_le_right hij (s.f j), ← val_mul x hij]
  exact congrArg _ (s.compat i j)

lemma le_preimage_nonzeroLocus {L : LB X} (s : L.Sec) (j : L.ι) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus s ↔ valAt' x (L.U j) (s.f j) ≠ 0 := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (((valueRules X x).1 _).1 h)
    have hi' := ((valueRules X x).1 _).2 hi
    have h1 := ((valueRules X x).2.2.2.2.1 _ _).1 hi'
    rw [val_sec x s i j (le_preimage_mono x (X.basicOpen_le _) hi') hj] at h1
    exact right_ne_zero_of_mul h1
  · intro h
    exact le_preimage_mono x (le_iSup (fun k => X.basicOpen (s.f k)) j)
      (((valueRules X x).2.2.2.2.1 _ _).2 h)

end Values

section Criterion

variable {X Y : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X] {Z : Type}
  (ex : Z → (Sp ℂ ⟶ X)) (ey : Z → (Sp ℂ ⟶ Y))
  (hon : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ z, ex z = x)

include hon in

lemma exists_hom_affine {W : X.Opens} {D : Y.Opens} (hW : IsAffineOpen W) (hD : IsAffineOpen D)
    (hin : ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W → ⊤ ≤ ey w ⁻¹ᵁ D)
    (hfn : ∀ f : Γ(Y, D), ∃ h : Γ(X, W), ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W →
      valAt' (ex w) W h = valAt' (ey w) D f) :
    ∃ g : W.toScheme ⟶ Y, ∀ w (y : Sp ℂ ⟶ W.toScheme), y ≫ W.ι = ex w → y ≫ g = ey w := by
  choose ρ hρ using hfn
  have ext : ∀ a b : Γ(X, W), (∀ w, ⊤ ≤ ex w ⁻¹ᵁ W → valAt' (ex w) W a = valAt' (ex w) W b) →
      a = b := fun a b h => eq_of_valAt'_eq p W a b fun x hx hxW => by
    obtain ⟨w, rfl⟩ := hon x hx
    exact h w hxW
  let ρ' : Γ(Y, D) →+* Γ(X, W) :=
    { toFun := ρ
      map_one' := ext _ _ fun w hw => by rw [hρ _ w hw, val_one _ hw, val_one _ (hin w hw)]
      map_mul' := fun a b => ext _ _ fun w hw => by
        rw [hρ _ w hw, val_mul _ hw, val_mul _ (hin w hw), hρ _ w hw, hρ _ w hw]
      map_zero' := ext _ _ fun w hw => by rw [hρ _ w hw, val_zero _ hw, val_zero _ (hin w hw)]
      map_add' := fun a b => ext _ _ fun w hw => by
        rw [hρ _ w hw, val_add _ hw, val_add _ (hin w hw), hρ _ w hw, hρ _ w hw] }
  refine ⟨hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ρ') ≫ hD.fromSpec, fun w y hy => ?_⟩
  have hw : ⊤ ≤ ex w ⁻¹ᵁ W := by
    rw [← hy]
    intro a _
    exact (y a).2
  have h1 := specMap_appLE_fromSpec hW (R := CommRingCat.of ℂ) (ex w) hw
  have h2 := specMap_appLE_fromSpec hD (R := CommRingCat.of ℂ) (ey w) (hin w hw)
  have h3 : y ≫ hW.isoSpec.hom =
      Spec.map ((ex w).appLE W ⊤ hw ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) := by
    rw [← cancel_mono hW.fromSpec, h1, ← hy, Category.assoc, ← hW.isoSpec_inv_ι,
      Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h3, ← h2, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext f
  have := hρ f w hw
  rw [valAt', valAt', dif_pos hw, dif_pos (hin w hw)] at this
  exact this

include hon in

lemma exists_hom_of_values {S : Scheme.{0}} (q : Y ⟶ S) [IsSeparated q] [IsAffine S]
    (h : ∀ z, ∃ (W : X.Opens) (D : Y.Opens), IsAffineOpen D ∧ ⊤ ≤ ex z ⁻¹ᵁ W ∧
      (∀ w, ⊤ ≤ ex w ⁻¹ᵁ W → ⊤ ≤ ey w ⁻¹ᵁ D) ∧
      ∀ f : Γ(Y, D), ∃ h : Γ(X, W), ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W → valAt' (ex w) W h = valAt' (ey w) D f) :
    ∃ g : X ⟶ Y, ∀ z, ex z ≫ g = ey z := by
  first
  | (rename_i h_3 h_4 h_11 h_12; revert X Y p h_3 h_4 Z ex ey hon S q h_11 h_12 h; exact @_root_.GlobalTheory.SchemeHomsFromPoints.exists_hom)
  | exact @_root_.GlobalTheory.SchemeHomsFromPoints.exists_hom
  | exact _root_.GlobalTheory.SchemeHomsFromPoints.exists_hom
  | (apply _root_.GlobalTheory.SchemeHomsFromPoints.exists_hom <;> assumption)
  | (intros; apply _root_.GlobalTheory.SchemeHomsFromPoints.exists_hom <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SchemeHomsFromPoints.exists_hom <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SchemeHomsFromPoints.exists_hom ..)

end Criterion

section Transport

variable {X Y : Scheme.{0}} (L : LB X) (κ : Y ⟶ X) (σ : X ⟶ Y) (e : σ ≫ κ = 𝟙 X) (N : ℕ)

include e in
lemma chart_le (j : PUnit → L.ι) :
    L.wchart (fun _ : PUnit => 𝟙 X) j ≤
      σ ⁻¹ᵁ L.wchart (fun _ : Fin N => κ) (fun _ => j PUnit.unit) := by
  intro y hy
  have h : κ (σ y) = y := by rw [← Scheme.Hom.comp_apply, e]; rfl
  refine Set.mem_iInter.2 fun _ => ?_
  have := Set.mem_iInter.1 hy PUnit.unit
  show κ (σ y) ∈ L.U (j PUnit.unit)
  rw [h]; exact this

include e in

lemma exists_sec_pow (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    (s : (L.LinComb (K := Fin N) (fun _ => κ) (fun _ => 1)).Sec) :
    ∃ s' : (lbPow L N).Sec, ∀ (x : Sp ℂ ⟶ X) (j : PUnit → L.ι), ⊤ ≤ x ⁻¹ᵁ (lbPow L N).U j →
      valAt' x ((lbPow L N).U j) (s'.f j) =
        valAt' (x ≫ σ) (L.wchart (fun _ : Fin N => κ) (fun _ => j PUnit.unit))
          (s.f fun _ => j PUnit.unit) := by
  let f : ∀ j : PUnit → L.ι, Γ(X, L.wchart (fun _ : PUnit => 𝟙 X) j) := fun j =>
    (σ.appLE _ _ (chart_le L κ σ e N j)).hom (s.f fun _ => j PUnit.unit)
  have hf : ∀ (x : Sp ℂ ⟶ X) (j : PUnit → L.ι), ⊤ ≤ x ⁻¹ᵁ L.wchart (fun _ : PUnit => 𝟙 X) j →
      valAt' x _ (f j) = valAt' (x ≫ σ) (L.wchart (fun _ : Fin N => κ) (fun _ => j PUnit.unit))
        (s.f fun _ => j PUnit.unit) := fun x j hj => val_appLE x σ _ _ _ _ hj
  refine ⟨⟨f, fun i j => eq_of_valAt'_eq p _ _ _ fun x _ hx => ?_⟩, hf⟩
  obtain ⟨hi, hj⟩ := (le_preimage_inf x _ _).1 hx
  have hi' : ⊤ ≤ (x ≫ σ) ⁻¹ᵁ L.wchart (fun _ : Fin N => κ) (fun _ => i PUnit.unit) :=
    le_preimage_mono x (chart_le L κ σ e N i) hi
  have hj' : ⊤ ≤ (x ≫ σ) ⁻¹ᵁ L.wchart (fun _ : Fin N => κ) (fun _ => j PUnit.unit) :=
    le_preimage_mono x (chart_le L κ σ e N j) hj
  refine (val_resG x inf_le_left hx _).trans (Eq.trans ?_ (val_mul x hx _ _).symm)
  refine (hf x i hi).trans ((val_sec (x ≫ σ) s _ _ hi' hj').trans (congrArg₂ (· * ·) ?_ ?_))
  · refine (val_linComb (x ≫ σ) valueRules L _ _ _ _ hi' hj').trans
      (Eq.trans ?_ (val_linComb x valueRules L _ _ _ _ hi hj).symm)
    simp [e]
  · exact ((val_resG x inf_le_right hx _).trans (hf x j hj)).symm

end Transport

section Theta

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
  (u : HolUnif A L g) (u' : HolUnif A' L' g')

lemma isThetaFn_comp {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    {Hm' : Matrix (Fin g') (Fin g') ℂ} {χ' : u'.Λ → ℂ} (hχ : ∀ l, χ l ^ 2 = 1)
    (hχ' : ∀ l, χ' l ^ 2 = 1) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (n : ℕ)
    (hΛ : ∀ l ∈ u.Λ, F l ∈ u'.Λ)
    (hH : ∀ z w, hermForm Hm' (F z) (F w) = (n : ℂ) * hermForm Hm z w) {N : ℕ}
    {θ₁ θ₂ : (Fin g' → ℂ) → ℂ} (h₁ : u'.IsThetaFn Hm' χ' N θ₁) (h₂ : u'.IsThetaFn Hm' χ' N θ₂) :
    u.IsThetaFn Hm χ (2 * (n * N)) fun z => θ₁ (F z) * θ₂ (F z) := by
  have hF : Differentiable ℂ F := F.toContinuousLinearMap.differentiable
  refine ⟨(h₁.1.comp hF).mul (h₂.1.comp hF), fun l z => ?_⟩
  have k₁ := h₁.2 ⟨F l, hΛ l l.2⟩ (F z)
  have k₂ := h₂.2 ⟨F l, hΛ l l.2⟩ (F z)
  simp only [hH] at k₁ k₂
  have e : Complex.exp (Real.pi * (n * hermForm Hm z l) + Real.pi / 2 * (n * hermForm Hm l l)) =
      Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) ^ n := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  simp only [map_add]
  rw [k₁, k₂, e]
  generalize Complex.exp _ = E
  have a₁ : χ l ^ (2 * (n * N)) = 1 := by rw [pow_mul, hχ, one_pow]
  have a₂ : χ' ⟨F l, hΛ l l.2⟩ ^ (2 * N) = 1 := by rw [pow_mul, hχ', one_pow]
  rw [mul_pow (χ l), a₁]
  linear_combination (E ^ (2 * (n * N)) * θ₁ (F z) * θ₂ (F z)) * a₂

lemma le_preimage_lbPow {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (L : LB X) (k : ℕ) (j : PUnit → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ (lbPow L k).U j ↔ ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit) := by
  refine (le_preimage_wchart x L (fun _ : PUnit => 𝟙 X) j).trans ?_
  simp only [Category.comp_id]
  exact ⟨fun h => h _, fun h _ => h⟩

lemma exists_quot [LocallyOfFiniteType A.hom] {k : ℕ} {s t : (lbPow L k).Sec}
    {θ ϑ : (Fin g → ℂ) → ℂ} (hs : u.IsFnPow k s θ) (ht : u.IsFnPow k t ϑ) (j : (lbPow L k).ι) :
    ∃ h : Γ(A.left, A.left.basicOpen (t.f j)), ∀ w,
      ⊤ ≤ (u.ex w).left ⁻¹ᵁ A.left.basicOpen (t.f j) →
        valAt' (u.ex w).left _ h * ϑ w = θ w := by
  have hle := A.left.basicOpen_le (t.f j)
  obtain ⟨v, hv⟩ := isUnit_of_valAt'_ne_zero A.hom _ (resG _ hle (t.f j)) fun x _ hx => by
    rw [val_resG x hle hx]
    exact ((valueRules _ x).2.2.2.2.1 _ _).1 hx
  refine ⟨resG _ hle (s.f j) * (v⁻¹).val, fun w hw => ?_⟩
  have hj := le_preimage_mono _ hle hw
  have h1 : valAt' (u.ex w).left _ (v⁻¹).val * valAt' (u.ex w).left _ v.val = 1 := by
    rw [← val_mul _ hw, Units.inv_mul, val_one _ hw]
  rw [hv, val_resG _ hle hw, ht j w hj] at h1
  rw [val_mul _ hw, val_resG _ hle hw, hs j w hj]
  linear_combination θ w * h1

end Theta

section Main

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
  (u : HolUnif A L g) (u' : HolUnif A' L' g')

lemma isMonHom_of_additive [Smooth A.hom] [IsSeparated A'.hom]
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (f : A ⟶ A') (hf : ∀ z, u'.ex (F z) = u.ex z ≫ f) :
    IsMonHom f where
  one_hom := by
    have h := hf 0
    rw [map_zero, ex_zero, ex_zero, Hom.one_def, Hom.one_def, toUnit_unit, Category.id_comp,
      Category.id_comp] at h
    exact h.symm
  mul_hom := by
    haveI : Smooth (A ⊗ A).hom := by
      change Smooth (pullback.fst A.hom A.hom ≫ A.hom)
      infer_instance
    haveI := isReduced_of_smooth_complex _ (A ⊗ A).hom inferInstance
    refine over_hom_ext_of_complexPoints fun x => ?_
    obtain ⟨z, hz⟩ := u.ex_onto (x ≫ fst A A)
    obtain ⟨w, hw⟩ := u.ex_onto (x ≫ snd A A)
    have hx : x = lift (u.ex z) (u.ex w) := by
      rw [hz, hw, ← comp_lift, lift_fst_snd, Category.comp_id]
    rw [hx, lift_map_assoc, ← Category.assoc, ← Hom.mul_def, ← Hom.mul_def, ← u.ex_add, ← hf, ← hf,
      ← hf, map_add, u'.ex_add]

lemma exists_hom [Smooth A.hom] [Smooth A'.hom] [IsSeparated A'.hom] (hL : L.IsLB) (hL' : L'.IsLB)
    (ha : Out.RelAmple A' L')
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    {Hm' : Matrix (Fin g') (Fin g') ℂ} {χ' : u'.Λ → ℂ} (hχ : ∀ l, χ l ^ 2 = 1)
    (hχ' : ∀ l, χ' l ^ 2 = 1)
    (hs : ∀ (k : ℕ) θ, u.IsThetaFn Hm χ k θ → ∃! s, u.IsFnPow k s θ)
    (hθ : ∀ (k : ℕ) s, ∃! θ, u'.IsThetaFn Hm' χ' k θ ∧ u'.IsFnPow k s θ)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (n : ℕ) (hΛ : ∀ l ∈ u.Λ, F l ∈ u'.Λ)
    (hH : ∀ z w, hermForm Hm' (F z) (F w) = (n : ℂ) * hermForm Hm z w) :
    ∃ f : A.left ⟶ A'.left, ∀ z, (u.ex z).left ≫ f = (u'.ex (F z)).left := by
  haveI := isReduced_of_smooth_complex _ A.hom inferInstance
  haveI := isReduced_of_smooth_complex _ A'.hom inferInstance
  obtain ⟨N, -, M, s, hcov, hD⟩ := ha ⊤ (isAffineOpen_top _)
  have hr : Set.range (𝟙 A'.left : A'.left ⟶ A'.left) ⊆ Set.range (A'.hom ⁻¹ᵁ ⊤).ι := by
    intro x _
    rw [Scheme.Opens.range_ι]
    trivial
  obtain ⟨σ, hσ⟩ : ∃ σ : A'.left ⟶ (A'.hom ⁻¹ᵁ ⊤).toScheme, σ ≫ (A'.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  choose s' hs' using fun i => exists_sec_pow L' _ σ hσ N A'.hom (s i)
  choose θ hθ₁ hθ₂ using fun i => (hθ N (s' i)).exists
  choose t ht using fun i j =>
    (hs _ _ (isThetaFn_comp u u' hχ hχ' F n hΛ hH (hθ₁ i) (hθ₁ j))).exists
  choose ch hch using exists_chart u valueRules hL
  choose ch' hch' using exists_chart u' valueRules hL'
  have hU : ∀ z, ⊤ ≤ ((u'.ex z).left ≫ σ) ⁻¹ᵁ (Out.powOver A' L' ⊤ N).U (fun _ => ch' z) := fun z =>
    le_preimage_mono (u'.ex z).left (chart_le L' _ σ hσ N fun _ => ch' z)
      ((le_preimage_lbPow _ L' N fun _ => ch' z).2 (hch' z))
  have hval : ∀ i z, valAt' ((u'.ex z).left ≫ σ) ((Out.powOver A' L' ⊤ N).U fun _ => ch' z)
      ((s i).f fun _ => ch' z) = θ i z * u'.fr (ch' z) z ^ N := fun i z =>
    have k := (le_preimage_lbPow _ L' N fun _ => ch' z).2 (hch' z)
    (hs' i _ _ k).symm.trans (hθ₂ i _ z k)
  have hfr : ∀ z, u'.fr (ch' z) z ^ N ≠ 0 := fun z => pow_ne_zero _ (u'.fr_ne _ _ (hch' z))
  have hmem : ∀ i z, ⊤ ≤ ((u'.ex z).left ≫ σ) ⁻¹ᵁ Out.nonzeroLocus (s i) ↔ θ i z ≠ 0 := fun i z => by
    rw [le_preimage_nonzeroLocus _ (s i) _ (hU z), hval, mul_ne_zero_iff_right (hfr z)]
  have hon : ∀ x : Sp ℂ ⟶ A.left, x ≫ A.hom = 𝟙 _ → ∃ z, (u.ex z).left = x := fun x hx => by
    obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x hx)
    exact ⟨z, by rw [hz]; rfl⟩
  refine (exists_hom_of_values A.hom (fun z => (u.ex z).left)
    (fun z => (u'.ex (F z)).left ≫ σ) hon ((A'.hom ⁻¹ᵁ ⊤).ι ≫ A'.hom) (fun z => ?_)).elim
    fun G hG => ⟨G ≫ (A'.hom ⁻¹ᵁ ⊤).ι, fun z => by
      rw [← Category.assoc, hG, Category.assoc, hσ, Category.comp_id]⟩
  have hz : ((u'.ex (F z)).left ≫ σ) (default : PrimeSpectrum ℂ) ∈ ⨆ i, Out.nonzeroLocus (s i) := by
    rw [hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  replace hi := (hmem i _).1 (((valueRules _ _).1 _).2 hi)
  obtain ⟨hDi, r, hr, hsurj⟩ := hD i
  have hne : ∀ w, ⊤ ≤ (u.ex w).left ⁻¹ᵁ A.left.basicOpen ((t i i).f fun _ => ch z) →
      θ i (F w) ≠ 0 := fun w hw => by
    have k := ((valueRules _ _).2.2.2.2.1 _ _).1 hw
    rw [ht i i _ w (le_preimage_mono _ (A.left.basicOpen_le _) hw)] at k
    exact left_ne_zero_of_mul (left_ne_zero_of_mul k)
  have hzU := (le_preimage_lbPow _ L (2 * (n * N)) fun _ => ch z).2 (hch z)
  refine ⟨A.left.basicOpen ((t i i).f fun _ => ch z), _, hDi, ?_,
    fun w hw => (hmem i _).2 (hne w hw), fun f => ?_⟩
  · refine ((valueRules _ _).2.2.2.2.1 _ _).2 ?_
    rw [ht i i _ z hzU]
    exact mul_ne_zero (mul_ne_zero hi hi) (pow_ne_zero _ (u.fr_ne _ _ (hch z)))
  obtain ⟨Q, rfl⟩ := hsurj f
  induction Q using MvPolynomial.induction_on with
  | C a =>
    have hc : ∀ w, ((u'.ex w).left ≫ σ) ≫ (A'.hom ∣_ ⊤) = ((u'.ex 0).left ≫ σ) ≫ (A'.hom ∣_ ⊤) := by
      intro w
      rw [← cancel_mono (⊤ : (Sp ℂ).Opens).ι]
      simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hσ, Over.w]
    refine ⟨constFn A.hom _ (valAt' (((u'.ex 0).left ≫ σ) ≫ (A'.hom ∣_ ⊤)) ⊤ a), fun w hw => ?_⟩
    rw [(valueRules _ _).2.2.2.2.2 A.hom (Over.w (u.ex w)) _ _ hw, MvPolynomial.eval₂Hom_C,
      ← hc (F w)]
    exact (val_appLE _ (A'.hom ∣_ ⊤) ⊤ _ _ a ((hmem i _).2 (hne w hw))).symm
  | add Q Q' h h' =>
    obtain ⟨a, ha⟩ := h
    obtain ⟨a', ha'⟩ := h'
    refine ⟨a + a', fun w hw => ?_⟩
    rw [map_add, val_add _ hw, val_add _ ((hmem i _).2 (hne w hw)), ha w hw, ha' w hw]
  | mul_X Q j h =>
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb⟩ := exists_quot u (ht i j) (ht i i) fun _ => ch z
    refine ⟨a * b, fun w hw => ?_⟩
    have hw' := (hmem i _).2 (hne w hw)
    rw [map_mul, val_mul _ hw, val_mul _ hw', ha w hw, MvPolynomial.eval₂Hom_X']
    congr 1
    have k := (le_preimage_inf _ _ _).2 ⟨hw', hU (F w)⟩
    have k₁ := congrArg (valAt' ((u'.ex (F w)).left ≫ σ) _) (hr j fun _ => ch' (F w))
    rw [val_mul _ k, val_resG _ _ k, val_resG _ _ k, val_resG _ _ k, hval, hval, ← _root_.mul_assoc] at k₁
    have k₂ := mul_right_cancel₀ (hfr _) k₁
    have k₃ := hb w hw
    refine mul_right_cancel₀ (mul_ne_zero (hne w hw) (hne w hw)) (k₃.trans ?_)
    linear_combination θ i (F w) * k₂

end Main

end AnalyticHom

open AnalyticHom in

theorem exists_hom_of_linear_scaling_hermForm :
    ∀ (P P' : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (u' : HolUnif P'.A P'.L P'.g)
      (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Hm' : Matrix (Fin P'.g) (Fin P'.g) ℂ)
      (χ' : u'.Λ → ℂ),
    u.IsAH Hm χ → u'.IsAH Hm' χ' →
    (∀ (k : ℕ) θ, u.IsThetaFn Hm χ k θ → ∃! s, u.IsFnPow k s θ) →
    (∀ (k : ℕ) s, ∃! θ, u'.IsThetaFn Hm' χ' k θ ∧ u'.IsFnPow k s θ) →
    ∀ (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)) (n : ℕ), (∀ l ∈ u.Λ, F l ∈ u'.Λ) →
    (∀ z w, hermForm Hm' (F z) (F w) = (n : ℂ) * hermForm Hm z w) →
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  intro P P' u u' Hm χ Hm' χ' h h' hs hθ F n hΛ hH
  haveI := P.isAb.smooth
  haveI := P'.isAb.smooth
  haveI := P'.isAb.proper
  obtain ⟨f, hf⟩ := exists_hom u u' P.isLB P'.isLB P'.ample
    (semicharacter_sq_eq_one_of_symmetric P u Hm χ h)
    (semicharacter_sq_eq_one_of_symmetric P' u' Hm' χ' h') hs hθ F n hΛ hH
  haveI := isReduced_of_smooth_complex _ P.A.hom inferInstance
  have hw : f ≫ P'.A.hom = P.A.hom := by
    refine ComplexPoints.hom_ext_of_points P.A.hom (terminal.from (Sp ℂ)) (terminal.hom_ext _ _)
      fun x hx => ?_
    obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x hx)
    obtain rfl : (u.ex z).left = x := by rw [hz]; rfl
    rw [← Category.assoc, hf, Over.w, Over.w]
  have key : ∀ z, u'.ex (F z) = u.ex z ≫ Over.homMk f hw := fun z =>
    Over.OverMorphism.ext (hf z).symm
  exact ⟨Over.homMk f hw, isMonHom_of_additive u u' F _ key, key⟩

end GlobalTheory
