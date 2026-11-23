import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDualFamilyModSubspace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Kunneth

theorem pushout_functional {K : Type} [Field K] {A B C : CommRingCat.{0}} (f : CommRingCat.of K ⟶ A)
    (g : CommRingCat.of K ⟶ B) (i : A ⟶ C) (j : B ⟶ C) (po : IsPushout f g i j) :
    (∀ (α : A →+ K) (β : B →+ K), (∀ c a, α (f.hom c * a) = c * α a) → (∀ c b, β (g.hom c * b) = c * β b) →
      ∃ F : C →+ K, ∀ a b, F (i.hom a * j.hom b) = α a * β b) ∧
    ∀ G : C →+ K, (∀ a b, G (i.hom a * j.hom b) = 0) → ∀ w, G w = 0 := by
  letI : Algebra K A := f.hom.toAlgebra
  letI : Algebra K B := g.hom.toAlgebra
  have hw : f ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := A) (B := B)) =
      g ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := B)).toRingHom := by
    ext c
    show f.hom c ⊗ₜ[K] (1 : B) = (1 : A) ⊗ₜ[K] g.hom c
    have h1 : f.hom c = c • (1 : A) := by rw [Algebra.smul_def, _root_.mul_one]; rfl
    have h2 : g.hom c = c • (1 : B) := by rw [Algebra.smul_def, _root_.mul_one]; rfl
    rw [h1, h2, TensorProduct.smul_tmul]
  obtain ⟨φ, hφi', hφj'⟩ : ∃ φ : C ⟶ CommRingCat.of (A ⊗[K] B),
      i ≫ φ = CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ∧
      j ≫ φ = CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := B)).toRingHom :=
    ⟨po.desc _ _ hw, po.inl_desc _ _ hw, po.inr_desc _ _ hw⟩
  have hφi : ∀ a, φ.hom (i.hom a) = a ⊗ₜ[K] (1 : B) := fun a => by
    have := congrArg (fun m => m.hom a) hφi'
    exact this
  have hφj : ∀ b, φ.hom (j.hom b) = (1 : A) ⊗ₜ[K] b := fun b => by
    have := congrArg (fun m => m.hom b) hφj'
    exact this
  refine ⟨fun α β hα hβ => ?_, fun G hG w => ?_⟩
  · let α' : A →ₗ[K] K :=
      { toFun := α, map_add' := α.map_add, map_smul' := fun c a => by rw [Algebra.smul_def]; exact hα c a }
    let β' : B →ₗ[K] K :=
      { toFun := β, map_add' := β.map_add, map_smul' := fun c b => by rw [Algebra.smul_def]; exact hβ c b }
    refine ⟨((LinearMap.mul' K K).comp (TensorProduct.map α' β')).toAddMonoidHom.comp φ.hom.toAddMonoidHom,
      fun a b => ?_⟩
    show LinearMap.mul' K K (TensorProduct.map α' β' (φ.hom (i.hom a * j.hom b))) = α a * β b
    rw [map_mul, hφi, hφj, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul, TensorProduct.map_tmul,
      LinearMap.mul'_apply]
    rfl
  · letI : Algebra K C := (f ≫ i).hom.toAlgebra
    let iA : A →ₐ[K] C := { i.hom with commutes' := fun _ => rfl }
    let jA : B →ₐ[K] C :=
      { j.hom with commutes' := fun c => (congrArg (fun m => m.hom c) po.w).symm }
    let ψ := Algebra.TensorProduct.productMap iA jA
    have hψ : φ ≫ CommRingCat.ofHom ψ.toRingHom = 𝟙 C := by
      apply po.hom_ext
      · ext a
        show ψ (φ.hom (i.hom a)) = i.hom a
        rw [hφi, Algebra.TensorProduct.productMap_apply_tmul]
        show i.hom a * j.hom 1 = i.hom a
        rw [map_one, _root_.mul_one]
      · ext b
        show ψ (φ.hom (j.hom b)) = j.hom b
        rw [hφj, Algebra.TensorProduct.productMap_apply_tmul]
        show i.hom 1 * j.hom b = j.hom b
        rw [map_one, _root_.one_mul]
    have hw' : ψ (φ.hom w) = w := congrArg (fun m => m.hom w) hψ
    rw [← hw']
    generalize φ.hom w = t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b =>
      rw [Algebra.TensorProduct.productMap_apply_tmul]
      exact hG a b
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

theorem pbT_of_le {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) {O : Z.Opens}
    (h : O ≤ f ⁻¹ᵁ O₀) : pbT f s O = (f.appLE O₀ O h).hom s := by
  unfold pbT
  rw [dif_pos h]

theorem rsT_of_le {Y : Scheme.{0}} {O₀ : Y.Opens} (s : Γ(Y, O₀)) {O : Y.Opens}
    (h : O ≤ O₀) : rsT s O = resG Y h s := by
  unfold rsT
  rw [dif_pos h]

theorem res_pbT {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ O₁ : Y.Opens} (s : Γ(Y, O₀)) {O O' : Z.Opens}
    (h : O ≤ f ⁻¹ᵁ O₀) (h' : O' ≤ O) (h₁ : O₁ ≤ O₀) (h₂ : O' ≤ f ⁻¹ᵁ O₁) :
    resG Z h' (pbT f s O) = pbT f (rsT s O₁) O' := by
  rw [pbT_of_le f s h, rsT_of_le s h₁, pbT_of_le f _ h₂]
  show (f.appLE O₀ O h ≫ Z.presheaf.map (homOfLE h').op).hom s =
    (Y.presheaf.map (homOfLE h₁).op ≫ f.appLE O₁ O' h₂).hom s
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem rsT_self {Y : Scheme.{0}} {O₀ : Y.Opens} (s : Γ(Y, O₀)) : rsT s O₀ = s := by
  rw [rsT_of_le s le_rfl]
  simp [resG]

noncomputable def cstHom {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) :
    CommRingCat.of K ⟶ Γ(Y, O) :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appLE ⊤ O (fun _ _ => trivial)

theorem cstHom_apply {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (c : K) :
    (cstHom q O).hom c = constFn q O c := rfl

theorem res_constFn {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) {O O' : Y.Opens} (h : O' ≤ O) (c : K) :
    resG Y h (constFn q O c) = constFn q O' c := by
  rw [← cstHom_apply, ← cstHom_apply]
  have e : cstHom q O ≫ Y.presheaf.map (homOfLE h).op = cstHom q O' := by
    unfold cstHom
    rw [Category.assoc]
    congr 1
    exact Scheme.Hom.appLE_map _ _ _
  rw [← e]
  rfl

theorem prod_functional {K : Type} [Field K] {Y Z : Scheme.{0}} {q : Y ⟶ Sp K} {p₁ p₂ : Z ⟶ Y}
    (H : IsPullback p₁ p₂ q q) {O O' : Y.Opens} (hO : IsAffineOpen O) (hO' : IsAffineOpen O') :
    (∀ (α : Γ(Y, O) →+ K) (β : Γ(Y, O') →+ K), (∀ c a, α (constFn q O c * a) = c * α a) →
      (∀ c b, β (constFn q O' c * b) = c * β b) →
      ∃ F : Γ(Z, p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O') →+ K, ∀ a b,
        F (pbT p₁ a (p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O') * pbT p₂ b (p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O')) = α a * β b) ∧
    ∀ G : Γ(Z, p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O') →+ K,
      (∀ (a : Γ(Y, O)) (b : Γ(Y, O')), G (pbT p₁ a (p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O') * pbT p₂ b (p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O')) = 0) →
      ∀ w, G w = 0 := by
  have hO1 : p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O' ≤ p₁ ⁻¹ᵁ O := inf_le_left
  have hO2 : p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O' ≤ p₂ ⁻¹ᵁ O' := inf_le_right
  have hiso := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UX := O) (UT := O')
    (UY := p₁ ⁻¹ᵁ O ⊓ p₂ ⁻¹ᵁ O') (by simp) (by simp) rfl (isAffineOpen_top _) hO' hO
  have po₀ := (isIso_pushoutSection_iff H _ _ _).mp hiso
  have po : IsPushout (cstHom q O) (cstHom q O') (p₁.appLE O _ hO1) (p₂.appLE O' _ hO2) :=
    IsPushout.of_iso po₀ (Scheme.ΓSpecIso (CommRingCat.of K)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [cstHom]) (by simp [cstHom]) (by simp) (by simp)
  obtain ⟨h1, h2⟩ := pushout_functional (cstHom q O) (cstHom q O') _ _ po
  refine ⟨fun α β hα hβ => ?_, fun G hG w => ?_⟩
  · obtain ⟨F, hF⟩ := h1 α β (fun c a => by rw [cstHom_apply]; exact hα c a)
      (fun c b => by rw [cstHom_apply]; exact hβ c b)
    exact ⟨F, fun a b => by rw [pbT_of_le p₁ a hO1, pbT_of_le p₂ b hO2]; exact hF a b⟩
  · refine h2 G (fun a b => ?_) w
    have e := hG a b
    rwa [pbT_of_le p₁ a hO1, pbT_of_le p₂ b hO2] at e

theorem functional_eq_sum {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} [Fintype I] [DecidableEq I]
    {U : I → Y.Opens} (α : C1 U →+ K) (c : C1 U) :
    α c = ∑ i, ∑ j, α (Pi.single i (Pi.single j (c i j))) := by
  have hc : c = ∑ i, ∑ j, (Pi.single i (Pi.single j (c i j)) : C1 U) := by
    conv_lhs => rw [← Finset.univ_sum_single c]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [← Finset.univ_sum_single (c i)]
    exact map_sum (AddMonoidHom.single _ i) _ _
  conv_lhs => rw [hc]
  simp only [map_sum]

theorem functional_cob {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} [Fintype I] [DecidableEq I]
    {U : I → Y.Opens} (α : C1 U →+ K) (h : ∀ c, IsCob U c → α c = 0) (j : I) (b : Γ(Y, U j)) :
    ∑ k, α (Pi.single k (Pi.single j (rsT b (U k ⊓ U j)))) =
      ∑ k, α (Pi.single j (Pi.single k (rsT b (U j ⊓ U k)))) := by
  have hz : ∀ (O₀ O : Y.Opens), rsT (0 : Γ(Y, O₀)) O = 0 := by
    intro O₀ O
    unfold rsT
    split_ifs <;> simp
  have hcob := h (fun i k => rsT ((Pi.single j b : ∀ i, Γ(Y, U i)) k) (U i ⊓ U k) -
      rsT ((Pi.single j b : ∀ i, Γ(Y, U i)) i) (U i ⊓ U k)) ⟨Pi.single j b, fun _ _ => rfl⟩
  rw [functional_eq_sum] at hcob
  simp only [Pi.single_sub, map_sub, Finset.sum_sub_distrib, sub_eq_zero] at hcob
  have e1 : ∀ i, ∑ k, α (Pi.single i (Pi.single k (rsT ((Pi.single j b : ∀ i, Γ(Y, U i)) k) (U i ⊓ U k)))) =
      α (Pi.single i (Pi.single j (rsT b (U i ⊓ U j)))) := by
    intro i
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, hz, Pi.single_zero, Pi.single_zero, map_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have e2 : ∑ i, ∑ k, α (Pi.single i (Pi.single k (rsT ((Pi.single j b : ∀ i, Γ(Y, U i)) i) (U i ⊓ U k)))) =
      ∑ k, α (Pi.single j (Pi.single k (rsT b (U j ⊓ U k)))) := by
    rw [Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same]
    · intro i _ hi
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Pi.single_eq_of_ne hi, hz, Pi.single_zero, Pi.single_zero, map_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [e2] at hcob
  simp only [e1] at hcob
  exact hcob

theorem pair_symm {K : Type} [Field K] {Y Z : Scheme.{0}} {q : Y ⟶ Sp K} {p₁ p₂ : Z ⟶ Y} {I : Type} [Finite I]
    {U : I → Y.Opens} {g : ℕ} (θ φ : Fin g → C1 U) (hq : IsSeparated q) (H : IsPullback p₁ p₂ q q)
    (hU : ∀ i, IsAffineOpen (U i)) (u : ∀ i i' j, Γ(Z, p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j))
    (u' : ∀ i j j', Γ(Z, p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')))
    (hu : ∀ i i' j j', ∑ a, (pbT p₁ (θ a i i') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) * pbT p₂ (φ a j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - pbT p₁ (φ a i i') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) * pbT p₂ (θ a j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) = (rsT (u i i' j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - rsT (u i i' j) (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) + (rsT (u' i' j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - rsT (u' i j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))))
    (α β : C1 U →+ K)
    (hα : ∀ (c : K) (x : C1 U), α (fun i j => constFn q (U i ⊓ U j) c * x i j) = c * α x)
    (hβ : ∀ (c : K) (x : C1 U), β (fun i j => constFn q (U i ⊓ U j) c * x i j) = c * β x)
    (hα0 : ∀ c, IsCob U c → α c = 0) (hβ0 : ∀ c, IsCob U c → β c = 0) :
    ∑ a, α (θ a) * β (φ a) = ∑ a, α (φ a) * β (θ a) := by
  classical
  haveI := Fintype.ofFinite I
  haveI := hq
  have haff : ∀ i i', IsAffineOpen (U i ⊓ U i') := fun i i' =>
    (isAffineHom_diagonal_iff (f := q)).mp inferInstance ⊤ (isAffineOpen_top _) (U i) (by simp) (U i') (by simp)
      (hU i) (hU i')
  let sg : ∀ i i', Γ(Y, U i ⊓ U i') →+ C1 U := fun i i' =>
    (AddMonoidHom.single (fun k => ∀ l, Γ(Y, U k ⊓ U l)) i).comp
      (AddMonoidHom.single (fun l => Γ(Y, U i ⊓ U l)) i')
  have hcs : ∀ (c : K) i i' (x : Γ(Y, U i ⊓ U i')),
      (fun k l => constFn q (U k ⊓ U l) c * (Pi.single i (Pi.single i' x) : C1 U) k l) =
        (Pi.single i (Pi.single i' (constFn q (U i ⊓ U i') c * x)) : C1 U) := by
    intro c i i' x
    funext k l
    by_cases hk : k = i
    · subst hk
      by_cases hl : l = i'
      · subst hl
        simp only [Pi.single_eq_same]
      · simp only [Pi.single_eq_same, Pi.single_eq_of_ne hl, MulZeroClass.mul_zero]
    · simp only [Pi.single_eq_of_ne hk, Pi.zero_apply, MulZeroClass.mul_zero]
  have hαc : ∀ i i' (c : K) (x : Γ(Y, U i ⊓ U i')),
      (α.comp (sg i i')) (constFn q (U i ⊓ U i') c * x) = c * (α.comp (sg i i')) x := by
    intro i i' c x
    show α (Pi.single i (Pi.single i' (constFn q _ c * x))) = c * α (Pi.single i (Pi.single i' x))
    rw [← hcs c i i' x]
    exact hα c _
  have hβc : ∀ i i' (c : K) (x : Γ(Y, U i ⊓ U i')),
      (β.comp (sg i i')) (constFn q (U i ⊓ U i') c * x) = c * (β.comp (sg i i')) x := by
    intro i i' c x
    show β (Pi.single i (Pi.single i' (constFn q _ c * x))) = c * β (Pi.single i (Pi.single i' x))
    rw [← hcs c i i' x]
    exact hβ c _
  have hF0 : ∀ i i' j j', ∃ F : Γ(Z, (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) →+ K, ∀ a b,
      F (pbT p₁ a (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) * pbT p₂ b (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) =
        α (Pi.single i (Pi.single i' a)) * β (Pi.single j (Pi.single j' b)) := fun i i' j j' =>
    (prod_functional H (haff i i') (haff j j')).1 (α.comp (sg i i')) (β.comp (sg j j')) (hαc i i') (hβc j j')
  choose F hF using hF0
  have T1 : ∀ i i', ∑ j, ∑ j', (F i i' j j' (rsT (u i i' j') _) - F i i' j j' (rsT (u i i' j) _)) = 0 := by
    intro i i'
    have hG : ∀ j (w : Γ(Z, p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j)),
        ∑ j', (F i i' j' j (rsT w _) - F i i' j j' (rsT w _)) = 0 := by
      intro j
      have hle1 : ∀ j', (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j' ⊓ U j)) ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j := fun j' => by
        intro x hx
        exact ⟨hx.1, hx.2.2⟩
      have hle2 : ∀ j', (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j := fun j' => by
        intro x hx
        exact ⟨hx.1, hx.2.1⟩
      let G : Γ(Z, p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j) →+ K :=
        ∑ j', ((F i i' j' j).comp (resG Z (hle1 j')).toAddMonoidHom -
          (F i i' j j').comp (resG Z (hle2 j')).toAddMonoidHom)
      have hGw : ∀ w, G w = ∑ j', (F i i' j' j (rsT w _) - F i i' j j' (rsT w _)) := by
        intro w
        simp only [G, AddMonoidHom.finsetSum_apply, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [rsT_of_le w (hle1 j'), rsT_of_le w (hle2 j')]
        rfl
      intro w
      rw [← hGw]
      refine (prod_functional H (haff i i') (hU j)).2 G (fun a b => ?_) w
      rw [hGw]
      have e : ∀ j', F i i' j' j (rsT (pbT p₁ a (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j) *
            pbT p₂ b (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j)) _) -
          F i i' j j' (rsT (pbT p₁ a (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j) *
            pbT p₂ b (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j)) _) =
          α (Pi.single i (Pi.single i' a)) * (β (Pi.single j' (Pi.single j (rsT b (U j' ⊓ U j)))) -
            β (Pi.single j (Pi.single j' (rsT b (U j ⊓ U j'))))) := by
        intro j'
        rw [rsT_of_le _ (hle1 j'), rsT_of_le _ (hle2 j'), map_mul (resG Z (hle1 j')), map_mul (resG Z (hle2 j')),
          res_pbT p₁ a inf_le_left (hle1 j') le_rfl inf_le_left,
          res_pbT p₂ b inf_le_right (hle1 j') inf_le_right inf_le_right,
          res_pbT p₁ a inf_le_left (hle2 j') le_rfl inf_le_left,
          res_pbT p₂ b inf_le_right (hle2 j') inf_le_left inf_le_right,
          rsT_self, hF, hF, mul_sub]
      rw [Finset.sum_congr rfl fun j' _ => e j', ← Finset.mul_sum, Finset.sum_sub_distrib,
        functional_cob β hβ0 j b, sub_self, MulZeroClass.mul_zero]
    calc _ = ∑ j, ∑ j', F i i' j' j (rsT (u i i' j) _) - ∑ j, ∑ j', F i i' j j' (rsT (u i i' j) _) := by
          simp only [Finset.sum_sub_distrib]
          congr 1
          exact Finset.sum_comm
      _ = ∑ j, ∑ j', (F i i' j' j (rsT (u i i' j) _) - F i i' j j' (rsT (u i i' j) _)) := by
          simp only [Finset.sum_sub_distrib]
      _ = 0 := Finset.sum_eq_zero fun j _ => hG j (u i i' j)
  have T2 : ∀ j j', ∑ i, ∑ i', (F i i' j j' (rsT (u' i' j j') _) - F i i' j j' (rsT (u' i j j') _)) = 0 := by
    intro j j'
    have hG : ∀ i (w : Γ(Z, p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))),
        ∑ i', (F i' i j j' (rsT w _) - F i i' j j' (rsT w _)) = 0 := by
      intro i
      have hle1 : ∀ i', (p₁ ⁻¹ᵁ (U i' ⊓ U i) ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) ≤ p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') := fun i' => by
        intro x hx
        exact ⟨hx.1.2, hx.2⟩
      have hle2 : ∀ i', (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) ≤ p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') := fun i' => by
        intro x hx
        exact ⟨hx.1.1, hx.2⟩
      let G : Γ(Z, p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) →+ K :=
        ∑ i', ((F i' i j j').comp (resG Z (hle1 i')).toAddMonoidHom -
          (F i i' j j').comp (resG Z (hle2 i')).toAddMonoidHom)
      have hGw : ∀ w, G w = ∑ i', (F i' i j j' (rsT w _) - F i i' j j' (rsT w _)) := by
        intro w
        simp only [G, AddMonoidHom.finsetSum_apply, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply]
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [rsT_of_le w (hle1 i'), rsT_of_le w (hle2 i')]
        rfl
      intro w
      rw [← hGw]
      refine (prod_functional H (hU i) (haff j j')).2 G (fun a b => ?_) w
      rw [hGw]
      have e : ∀ i', F i' i j j' (rsT (pbT p₁ a (p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) *
            pbT p₂ b (p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) _) -
          F i i' j j' (rsT (pbT p₁ a (p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) *
            pbT p₂ b (p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) _) =
          (α (Pi.single i' (Pi.single i (rsT a (U i' ⊓ U i)))) -
            α (Pi.single i (Pi.single i' (rsT a (U i ⊓ U i'))))) * β (Pi.single j (Pi.single j' b)) := by
        intro i'
        rw [rsT_of_le _ (hle1 i'), rsT_of_le _ (hle2 i'), map_mul (resG Z (hle1 i')), map_mul (resG Z (hle2 i')),
          res_pbT p₁ a inf_le_left (hle1 i') inf_le_right inf_le_left,
          res_pbT p₂ b inf_le_right (hle1 i') le_rfl inf_le_right,
          res_pbT p₁ a inf_le_left (hle2 i') inf_le_left inf_le_left,
          res_pbT p₂ b inf_le_right (hle2 i') le_rfl inf_le_right,
          rsT_self, hF, hF, sub_mul]
      rw [Finset.sum_congr rfl fun i' _ => e i', ← Finset.sum_mul, Finset.sum_sub_distrib,
        functional_cob α hα0 i a, sub_self, MulZeroClass.zero_mul]
    calc _ = ∑ i, ∑ i', F i' i j j' (rsT (u' i j j') _) - ∑ i, ∑ i', F i i' j j' (rsT (u' i j j') _) := by
          simp only [Finset.sum_sub_distrib]
          congr 1
          exact Finset.sum_comm
      _ = ∑ i, ∑ i', (F i' i j j' (rsT (u' i j j') _) - F i i' j j' (rsT (u' i j j') _)) := by
          simp only [Finset.sum_sub_distrib]
      _ = 0 := Finset.sum_eq_zero fun i _ => hG i (u' i j j')
  have key : ∀ i i' j j', ∑ a, (α (Pi.single i (Pi.single i' (θ a i i'))) * β (Pi.single j (Pi.single j' (φ a j j'))) -
      α (Pi.single i (Pi.single i' (φ a i i'))) * β (Pi.single j (Pi.single j' (θ a j j')))) =
      F i i' j j' (rsT (u i i' j') _ - rsT (u i i' j) _ + (rsT (u' i' j j') _ - rsT (u' i j j') _)) := by
    intro i i' j j'
    rw [← hu, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sub, hF, hF]
  have expand : ∀ x y : C1 U, α x * β y = ∑ i, ∑ i', ∑ j, ∑ j',
      α (Pi.single i (Pi.single i' (x i i'))) * β (Pi.single j (Pi.single j' (y j j'))) := by
    intro x y
    rw [functional_eq_sum α x, functional_eq_sum β y, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  have step : ∀ f : Fin g → I → I → I → I → K, ∑ a, ∑ i, ∑ i', ∑ j, ∑ j', f a i i' j j' =
      ∑ i, ∑ i', ∑ j, ∑ j', ∑ a, f a i i' j j' := by
    intro f
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
  have swap : ∀ f : I → I → I → I → K, ∑ i, ∑ i', ∑ j, ∑ j', f i i' j j' = ∑ j, ∑ j', ∑ i, ∑ i', f i i' j j' := by
    intro f
    calc ∑ i, ∑ i', ∑ j, ∑ j', f i i' j j' = ∑ i, ∑ j, ∑ j', ∑ i', f i i' j j' := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ j, ∑ j', ∑ i, ∑ i', f i i' j j' := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
  have hsplit : ∀ i i' j j', F i i' j j' (rsT (u i i' j') _ - rsT (u i i' j) _ + (rsT (u' i' j j') _ - rsT (u' i j j') _)) =
      (F i i' j j' (rsT (u i i' j') _) - F i i' j j' (rsT (u i i' j) _)) +
        (F i i' j j' (rsT (u' i' j j') _) - F i i' j j' (rsT (u' i j j') _)) := by
    intro i i' j j'
    rw [map_add, map_sub, map_sub]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  have e1 : ∀ a, α (θ a) * β (φ a) - α (φ a) * β (θ a) = ∑ i, ∑ i', ∑ j, ∑ j',
      (α (Pi.single i (Pi.single i' (θ a i i'))) * β (Pi.single j (Pi.single j' (φ a j j'))) -
        α (Pi.single i (Pi.single i' (φ a i i'))) * β (Pi.single j (Pi.single j' (θ a j j')))) := by
    intro a
    rw [expand (θ a) (φ a), expand (φ a) (θ a)]
    simp only [← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl fun a _ => e1 a, step]
  simp only [key, hsplit, Finset.sum_add_distrib, T1, _root_.zero_add]
  rw [swap]
  simp only [T2, Finset.sum_const_zero]

theorem kunneth_symm : ∀ (K : Type) [Field K] (Y Z : Scheme.{0}) (q : Y ⟶ Sp K) (p₁ p₂ : Z ⟶ Y) (I : Type) [Finite I] (U : I → Y.Opens) (g : ℕ) (θ φ : Fin g → C1 U), IsSeparated q → IsPullback p₁ p₂ q q → (∀ i, IsAffineOpen (U i)) → (∀ c, IsCob U (lc q c φ) → c = 0) → ∀ (u : ∀ i i' j, Γ(Z, p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j)) (u' : ∀ i j j', Γ(Z, p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))), (∀ i i' j j', ∑ a, (pbT p₁ (θ a i i') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) * pbT p₂ (φ a j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - pbT p₁ (φ a i i') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) * pbT p₂ (θ a j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) = (rsT (u i i' j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - rsT (u i i' j) (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) + (rsT (u' i' j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - rsT (u' i j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')))) → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob U (θ b - lc q (Θ b) φ) := by
  intro K _ Y Z q p₁ p₂ I _ U g θ φ hq H hU hind u u' hu
  letI : ∀ i j : I, Module K Γ(Y, U i ⊓ U j) := fun i j => (cstHom q (U i ⊓ U j)).hom.toModule
  have hsmul : ∀ (c : K) (x : C1 U), c • x = fun i j => constFn q (U i ⊓ U j) c * x i j := by
    intro c x
    funext i j
    rw [← cstHom_apply]
    rfl
  have hrs_add : ∀ {O₀ O : Y.Opens} (s t : Γ(Y, O₀)), rsT (s + t) O = rsT s O + rsT t O := by
    intro O₀ O s t
    unfold rsT
    split_ifs <;> simp
  have hrs_cmul : ∀ {O₀ O : Y.Opens} (c : K) (s : Γ(Y, O₀)), O ≤ O₀ →
      rsT (constFn q O₀ c * s) O = constFn q O c * rsT s O := by
    intro O₀ O c s h
    rw [rsT_of_le _ h, rsT_of_le _ h, map_mul, res_constFn]
  let B : Submodule K (C1 U) :=
    { carrier := {c | IsCob U c}
      add_mem' := by
        rintro x y ⟨b, hb⟩ ⟨b', hb'⟩
        refine ⟨b + b', fun i j => ?_⟩
        show x i j + y i j = _
        rw [hb, hb', Pi.add_apply, Pi.add_apply, hrs_add, hrs_add]
        abel
      zero_mem' := ⟨0, fun i j => by simp [rsT]⟩
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨fun i => constFn q (U i) c * b i, fun i j => ?_⟩
        rw [hsmul]
        show constFn q _ c * x i j = _
        rw [hb, hrs_cmul c _ inf_le_right, hrs_cmul c _ inf_le_left, mul_sub] }
  have hlc : ∀ c : Fin g → K, lc q c φ = ∑ a, c a • φ a := by
    intro c
    funext i j
    simp only [lc, Finset.sum_apply, hsmul]
  have hind' : ∀ c : Fin g → K, ∑ a, c a • φ a ∈ B → c = 0 := by
    intro c hc
    apply hind c
    rw [hlc]
    exact hc
  obtain ⟨Θ, hΘ, hmem⟩ := exists_symm_matrix_mod_subspace K (C1 U) B g θ φ hind'
    (fun α β hα hβ => pair_symm θ φ hq H hU u u' hu α.toAddMonoidHom β.toAddMonoidHom
      (fun c x => by
        have e := hsmul c x
        rw [← e]
        show α (c • x) = c * α x
        rw [map_smul, smul_eq_mul])
      (fun c x => by
        have e := hsmul c x
        rw [← e]
        show β (c • x) = c * β x
        rw [map_smul, smul_eq_mul])
      (fun c hc => LinearMap.mem_ker.mp (hα hc))
      (fun c hc => LinearMap.mem_ker.mp (hβ hc)))
  refine ⟨Θ, hΘ, fun b => ?_⟩
  rw [hlc]
  exact hmem b

end GlobalTheory.KS.Kunneth
