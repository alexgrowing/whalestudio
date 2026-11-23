import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSecOfLocal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaBaseChange

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar

section Bundles

variable {Y Y' X X' N N' : Scheme.{0}} {L : LB X} {L' : LB X'} {M : LB N} {M' : LB N'}

theorem exists_unpull {c₀ : Y ⟶ X} {q : Y ⟶ N} {w : LB.Iso (L.pull c₀) (M.pull q)} (hw : w.IsGen) (n : X ⟶ Y)
    (hn : n ≫ c₀ = 𝟙 X) {P : X ⟶ N} (hP : n ≫ q = P) :
    ∃ u : LB.Iso L (M.pull P), PGen u ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j : M.ι) (i : L.ι),
      P (f z) ∈ M.U j → f z ∈ L.U i → gw u f z j i = isoVal w (f ≫ n) z j i := by
  subst hP
  have hle : ∀ p : (PUnit → M.ι) × L.ι,
      (M.pull (n ≫ q)).U p.1 ⊓ L.U p.2 ≤ n ⁻¹ᵁ ((M.pull q).U p.1 ⊓ (L.pull c₀).U (fun _ => p.2)) := by
    rintro ⟨J, i⟩ x ⟨hx1, hx2⟩
    have hx3 : (n ≫ c₀) x ∈ L.U i := by rw [hn]; exact hx2
    have hx4 := mem_pull.mp hx1
    exact ⟨mem_pull.mpr hx4, mem_pull.mpr hx3⟩
  let u : LB.Iso L (M.pull (n ≫ q)) := ⟨fun p => res (hle p) (pullU n _ (w.s (p.1, fun _ => p.2)))⟩
  have key : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j : M.ι) (i : L.ι), (n ≫ q) (f z) ∈ M.U j → f z ∈ L.U i →
      gw u f z j i = isoVal w (f ≫ n) z j i := by
    intro Z f z j i hj hi
    have hV : f z ∈ (M.pull (n ≫ q)).U (fun _ => j) ⊓ L.U i := ⟨mem_pull.mpr hj, hi⟩
    exact (gm_res f z (hle ((fun _ => j), i)) hV _).trans (gm_pull f n z _ (hle ((fun _ => j), i) hV) _)
  refine ⟨u, ?_, key⟩
  intro Y₀ f y j j' k k' hj hj' hk hk'
  have hfn : (f ≫ n) ≫ c₀ = f := by rw [Category.assoc, hn, Category.comp_id]
  have a₁ : ((f ≫ n) ≫ c₀) y ∈ L.U k := by rw [hfn]; exact hk
  have b₁ : ((f ≫ n) ≫ c₀) y ∈ L.U k' := by rw [hfn]; exact hk'
  rw [key _ f y j k hj hk, key _ f y j' k' hj' hk', isoVal_trans hw (f ≫ n) y hj hj' a₁ b₁, hfn, Category.assoc]

theorem exists_side (hL : L.IsLB) (hL' : L'.IsLB) (hM : M.IsLB) (hM' : M'.IsLB)
    {c₀ : Y ⟶ X} {q : Y ⟶ N} {w : LB.Iso (L.pull c₀) (M.pull q)} (hw : w.IsGen) (n : X ⟶ Y) (hn : n ≫ c₀ = 𝟙 X)
    {c₁ : Y' ⟶ X'} {q' : Y' ⟶ N'} {w' : LB.Iso (L'.pull c₁) (M'.pull q')} (hw' : w'.IsGen)
    {Ψ : N' ⟶ N} {wM : LB.Iso M' (M.pull Ψ)} (hwM : wM.IsGen) (Φ : Y' ⟶ X) (hΦ : Φ ≫ n ≫ q = q' ≫ Ψ) :
    ∃ v : LB.Iso (L'.pull c₁) (L.pull Φ), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y') (z : Z) (j : M.ι) (j' : M'.ι) (i : L.ι) (i' : L'.ι),
        Ψ (q' (f z)) ∈ M.U j → q' (f z) ∈ M'.U j' → Φ (f z) ∈ L.U i → c₁ (f z) ∈ L'.U i' →
        isoVal w (f ≫ Φ ≫ n) z j i * isoVal v f z i i' = gw wM (f ≫ q') z j j' * isoVal w' f z j' i' := by
  obtain ⟨u, hu, hu'⟩ := exists_unpull hw n hn (P := n ≫ q) rfl
  obtain ⟨w₁, T₁⟩ := exists_comp hM' wM w' ((isGen_iff wM).mp hwM) ((isGen_iff w').mp hw') hM (pull_isLB hL' c₁)
  have T₁' : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y') (y : Z) (j : M.ι) (i : M'.ι) (k : PUnit → L'.ι),
      Ψ (q' (f y)) ∈ M.U j → q' (f y) ∈ M'.U i → f y ∈ (L'.pull c₁).U k →
      gw w₁ f y j k = gw wM (f ≫ q') y j i * gw w' f y i k := T₁
  have P₁ := T₁.pgen_comp hM' ((isGen_iff wM).mp hwM) ((isGen_iff w').mp hw')
  clear T₁
  generalize hQ : q' ≫ Ψ = Q at w₁ T₁' P₁
  have hQ' : Φ ≫ n ≫ q = Q := hΦ.trans hQ
  subst hQ'
  obtain ⟨v, T₂⟩ := exists_cancel hM u w₁ hu P₁ hL (pull_isLB hL' c₁)
  refine ⟨v, (isGen_iff v).mpr (T₂.pgen_cancel hM hu P₁), ?_⟩
  intro Z f z j j' i i' hj hj' hi hi'
  have m₁ : (n ≫ q) (Φ (f z)) ∈ M.U j := by
    have m₀ : (Φ ≫ n ≫ q) (f z) ∈ M.U j := by
      rw [hΦ]
      exact hj
    exact m₀
  have e₂ := T₂ Z f z j i (fun _ => i') m₁ hi (mem_pull.mpr hi')
  have e₁ := T₁' Z f z j j' (fun _ => i') hj hj' (mem_pull.mpr hi')
  have e₃ := hu' Z (f ≫ Φ) z j i m₁ hi
  rw [e₃, Category.assoc] at e₂
  exact e₂.symm.trans e₁

theorem exists_gen_up (hL : L.IsLB) (hL' : L'.IsLB) {Φ : X' ⟶ X} {v : LB.Iso L' (L.pull Φ)} (hv : PGen v)
    {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (ω : Y ⟶ Y')
    (hc : ∀ κ, ω ≫ φ' κ ≫ Φ = φ κ) (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good L' z J' →
      val t r z J = (∏ κ, gw v ((r ≫ ω) ≫ φ' κ) z (J (r ≫ φ κ)) (J' ((r ≫ ω) ≫ φ' κ)) ^ ε κ) * val a (r ≫ ω) z J' := by
  obtain ⟨t₀, ht₀, hv₀⟩ := exists_up hv hL hL' a ha
  have hφ : φ = fun κ => ω ≫ φ' κ ≫ Φ := funext fun κ => (hc κ).symm
  subst hφ
  refine ⟨LB.pullGen L (fun k => φ' k ≫ Φ) ε t₀ ω, pullGen_isGen _ _ _ _ ht₀ ω, ?_⟩
  intro Z r z J J' hJ hJ'
  rw [val_pull hJ]
  have h1 := hv₀ Z (r ≫ ω) z _ _ (hJ.mem (fun k => φ' k ≫ Φ) (r ≫ ω)) (hJ'.mem φ' (r ≫ ω))
  unfold val
  rw [h1]
  unfold pw
  simp only [Category.assoc]

end Bundles

section Geometry

variable {S S' W : Scheme.{0}} {g : S' ⟶ S} {t : W ⟶ S} {t' : W ⟶ S'}

theorem exists_cmp (ht : t' ≫ g = t) {A : Over S} {A' : Over S'} {Φ : A'.left ⟶ A.left}
    (w : Φ ≫ A.hom = A'.hom ≫ g) :
    ∃ Ω : (Over.mk t' ⊗ A').left ⟶ (Over.mk t ⊗ A).left, Ω ≫ (fst (Over.mk t) A).left = (fst (Over.mk t') A').left ∧
      Ω ≫ (snd (Over.mk t) A).left = (snd (Over.mk t') A').left ≫ Φ := by
  subst ht
  let U : Over S := Over.mk ((Over.mk t' ⊗ A').hom ≫ g)
  let a : U ⟶ Over.mk (t' ≫ g) := Over.homMk (fst (Over.mk t') A').left (by
    show (fst (Over.mk t') A').left ≫ t' ≫ g = (Over.mk t' ⊗ A').hom ≫ g
    rw [← Category.assoc]
    exact congrArg (· ≫ g) (Over.w (fst (Over.mk t') A')))
  let b : U ⟶ A := Over.homMk ((snd (Over.mk t') A').left ≫ Φ) (by
    rw [Category.assoc, w, ← Category.assoc]
    exact congrArg (· ≫ g) (Over.w (snd (Over.mk t') A')))
  refine ⟨(lift a b).left, ?_, ?_⟩
  · rw [← Over.comp_left, lift_fst]
    rfl
  · rw [← Over.comp_left, lift_snd]
    rfl

theorem cmp_ext {A : Over S} {A' : Over S'} {Φ : A'.left ⟶ A.left} (hp : IsPullback Φ A'.hom A.hom g)
    {Z : Scheme.{0}} {a b : Z ⟶ (Over.mk t' ⊗ A').left}
    (h₁ : a ≫ (fst (Over.mk t') A').left = b ≫ (fst (Over.mk t') A').left)
    (h₂ : a ≫ (snd (Over.mk t') A').left ≫ Φ = b ≫ (snd (Over.mk t') A').left ≫ Φ) : a = b := by
  have hs : a ≫ (snd (Over.mk t') A').left = b ≫ (snd (Over.mk t') A').left := by
    apply hp.hom_ext
    · simpa only [Category.assoc] using h₂
    · calc (a ≫ (snd (Over.mk t') A').left) ≫ A'.hom
          = a ≫ (fst (Over.mk t') A').left ≫ (Over.mk t').hom := by
            rw [Category.assoc, Over.w, Over.w]
        _ = (b ≫ (fst (Over.mk t') A').left) ≫ (Over.mk t').hom := by rw [← Category.assoc, h₁]
        _ = (b ≫ (snd (Over.mk t') A').left) ≫ A'.hom := by
            rw [Category.assoc, Category.assoc, Over.w, Over.w]
  have hb : b ≫ (Over.mk t' ⊗ A').hom = a ≫ (Over.mk t' ⊗ A').hom := by
    rw [← Over.w (fst (Over.mk t') A'), ← Category.assoc, ← Category.assoc, h₁]
  let U : Over S' := Over.mk (a ≫ (Over.mk t' ⊗ A').hom)
  let fa : U ⟶ Over.mk t' ⊗ A' := Over.homMk a rfl
  let fb : U ⟶ Over.mk t' ⊗ A' := Over.homMk b hb
  have hab : fa = fb := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      simpa only [Over.comp_left, Over.homMk_left, fa, fb] using h₁
    · apply Over.OverMorphism.ext
      simpa only [Over.comp_left, Over.homMk_left, fa, fb] using hs
  exact congrArg (fun f => f.left) hab

theorem exists_cmp_inv (ht : t' ≫ g = t) {A : Over S} {A' : Over S'} {Φ : A'.left ⟶ A.left}
    (hp : IsPullback Φ A'.hom A.hom g) :
    ∃ ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t' ⊗ A').left, ω ≫ (fst (Over.mk t') A').left = (fst (Over.mk t) A).left ∧
      ω ≫ (snd (Over.mk t') A').left ≫ Φ = (snd (Over.mk t) A).left := by
  subst ht
  have hsq : (snd (Over.mk (t' ≫ g)) A).left ≫ A.hom = ((fst (Over.mk (t' ≫ g)) A).left ≫ t') ≫ g := by
    rw [Over.w, Category.assoc]
    exact (Over.w (fst (Over.mk (t' ≫ g)) A)).symm
  let c : (Over.mk (t' ≫ g) ⊗ A).left ⟶ A'.left :=
    hp.lift (snd (Over.mk (t' ≫ g)) A).left ((fst (Over.mk (t' ≫ g)) A).left ≫ t') hsq
  let U : Over S' := Over.mk ((fst (Over.mk (t' ≫ g)) A).left ≫ t')
  let a : U ⟶ Over.mk t' := Over.homMk (fst (Over.mk (t' ≫ g)) A).left rfl
  let b : U ⟶ A' := Over.homMk c (hp.lift_snd _ _ _)
  refine ⟨(lift a b).left, ?_, ?_⟩
  · rw [← Over.comp_left, lift_fst]
    rfl
  · rw [← Category.assoc, ← Over.comp_left, lift_snd]
    exact hp.lift_fst _ _ _

variable {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {Φ : A'.left ⟶ A.left}

theorem pow_eq_one_of_push (ht : t' ≫ g = t) (hp : IsGrpPullback A' A g Φ) {x : Over.mk t ⟶ A} {x' : Over.mk t' ⟶ A'}
    (hx : x'.left ≫ Φ = x.left) {k : ℕ} (h : x ^ k = 1) : x' ^ k = 1 := by
  subst ht
  have hψ : ∀ y : Over.mk t' ⟶ A', (y.left ≫ Φ) ≫ A.hom = (Over.mk t').hom ≫ g := fun y => by
    rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w]
  let ψ : (Over.mk t' ⟶ A') → (Over.mk (t' ≫ g) ⟶ A) := fun y => Over.homMk (y.left ≫ Φ) (hψ y)
  have hmul : ∀ y z, ψ (y * z) = ψ y * ψ z := fun y z =>
    Over.OverMorphism.ext (hp.2 (Over.mk t') y z (ψ y) (ψ z) rfl rfl).symm
  let Ψ : (Over.mk t' ⟶ A') →* (Over.mk (t' ≫ g) ⟶ A) := MonoidHom.mk' ψ hmul
  have hinj : Function.Injective ψ := fun y z e => by
    have e' : y.left ≫ Φ = z.left ≫ Φ := congrArg (fun f => f.left) e
    exact Over.OverMorphism.ext (hp.1.hom_ext e' (by rw [Over.w, Over.w]))
  have hx' : ψ x' = x := Over.OverMorphism.ext hx
  apply hinj
  change Ψ (x' ^ k) = Ψ 1
  rw [map_pow, map_one]
  show ψ x' ^ k = 1
  rw [hx', h]

theorem translPt_cmp (ht : t' ≫ g = t) (hp : IsGrpPullback A' A g Φ) {x : Over.mk t ⟶ A} {x' : Over.mk t' ⟶ A'}
    (hx : x'.left ≫ Φ = x.left) {ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t' ⊗ A').left}
    (h₁ : ω ≫ (fst (Over.mk t') A').left = (fst (Over.mk t) A).left)
    (h₂ : ω ≫ (snd (Over.mk t') A').left ≫ Φ = (snd (Over.mk t) A).left) :
    ω ≫ (translPt A' x').left ≫ Φ = (translPt A x).left := by
  subst ht
  unfold translPt
  change ω ≫ ((fst (Over.mk t') A' ≫ x') * snd (Over.mk t') A').left ≫ Φ =
    ((fst (Over.mk (t' ≫ g)) A ≫ x) * snd (Over.mk (t' ≫ g)) A).left
  have he : ω ≫ (Over.mk t' ⊗ A').hom ≫ g = (Over.mk (t' ≫ g) ⊗ A).hom := by
    rw [← Over.w (fst (Over.mk t') A'), ← Over.w (fst (Over.mk (t' ≫ g)) A), ← h₁]
    simp only [Over.mk_hom, Category.assoc]
  let V : Over S := Over.mk ((Over.mk t' ⊗ A').hom ≫ g)
  let e : Over.mk (t' ≫ g) ⊗ A ⟶ V := Over.homMk ω he
  let x₀ : V ⟶ A := Over.homMk ((fst (Over.mk t') A' ≫ x').left ≫ Φ) (by
    show ((fst (Over.mk t') A' ≫ x').left ≫ Φ) ≫ A.hom = (Over.mk t' ⊗ A').hom ≫ g
    rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w])
  let y₀ : V ⟶ A := Over.homMk ((snd (Over.mk t') A').left ≫ Φ) (by
    show ((snd (Over.mk t') A').left ≫ Φ) ≫ A.hom = (Over.mk t' ⊗ A').hom ≫ g
    rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w])
  have hm := hp.2 (Over.mk t' ⊗ A') (fst (Over.mk t') A' ≫ x') (snd (Over.mk t') A') x₀ y₀ rfl rfl
  rw [← hm]
  have h1 : e ≫ x₀ = fst (Over.mk (t' ≫ g)) A ≫ x := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, hx, e, x₀]
    rw [← Category.assoc, h₁]
  have h2 : e ≫ y₀ = snd (Over.mk (t' ≫ g)) A := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.homMk_left, e, y₀]
    exact h₂
  have h3 : e ≫ (x₀ * y₀) = (fst (Over.mk (t' ≫ g)) A ≫ x) * snd (Over.mk (t' ≫ g)) A := by
    rw [← h1, ← h2]
    show e ≫ (lift x₀ y₀ ≫ μ) = lift (e ≫ x₀) (e ≫ y₀) ≫ μ
    rw [← Category.assoc, comp_lift]
  exact congrArg (fun f => f.left) h3

theorem translT_cmp (ht : t' ≫ g = t) (hp : IsGrpPullback A' A g Φ) {x : Over.mk t ⟶ A} {x' : Over.mk t' ⟶ A'}
    (hx : x'.left ≫ Φ = x.left) {ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t' ⊗ A').left}
    (h₁ : ω ≫ (fst (Over.mk t') A').left = (fst (Over.mk t) A).left)
    (h₂ : ω ≫ (snd (Over.mk t') A').left ≫ Φ = (snd (Over.mk t) A).left) :
    (translT A x).left ≫ ω = ω ≫ (translT A' x').left := by
  unfold translT
  have e1 : (lift (fst (Over.mk t) A) (translPt A x)).left ≫ (fst (Over.mk t) A).left = (fst (Over.mk t) A).left := by
    rw [← Over.comp_left, lift_fst]
  have e2 : (lift (fst (Over.mk t') A') (translPt A' x')).left ≫ (fst (Over.mk t') A').left =
      (fst (Over.mk t') A').left := by
    rw [← Over.comp_left, lift_fst]
  have e3 : (lift (fst (Over.mk t) A) (translPt A x)).left ≫ (snd (Over.mk t) A).left = (translPt A x).left := by
    rw [← Over.comp_left, lift_snd]
  have e4 : (lift (fst (Over.mk t') A') (translPt A' x')).left ≫ (snd (Over.mk t') A').left =
      (translPt A' x').left := by
    rw [← Over.comp_left, lift_snd]
  apply cmp_ext hp.1
  · rw [Category.assoc, h₁, e1, Category.assoc, e2, h₁]
  · rw [Category.assoc, h₂, e3, Category.assoc, reassoc_of% e4, translPt_cmp ht hp hx h₁ h₂]

end Geometry

section Theta

theorem actVal_of_isActOf {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}
    {θ : ThetaGrp A L k T} {s s' : LB.Sec (LPow A L k T)} (h : IsActOf A L k θ s s') : ActVal θ s s' := by
  intro Z r z J hJ
  have hJ2 := hJ.mem ![(snd T A).left, (translPt A θ.pt).left] r
  have hJ1 := hJ.mem (fun _ : Fin 1 => (snd T A).left) (r ≫ (translT A θ.pt).left)
  simp only [Category.assoc, translT_snd_left] at hJ1
  have e := congrArg (gs r z _) (h (fun k => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] k)))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
  erw [gs_mul _ _ _ hJ2, gs_res _ _ _ hJ2, gs_res _ _ _ hJ2, gs_unit _ _ _ hJ2,
    gs_pull r (translT A θ.pt).left z _ hJ1] at e
  simp only [secVal, thetaVal, sval, val]
  rw [show ((r ≫ (translT A θ.pt).left) ≫ (snd T A).left) = r ≫ (translPt A θ.pt).left by
    rw [Category.assoc, translT_snd_left]]
  exact e

variable {S S' W : Scheme.{0}} {g : S' ⟶ S} {t : W ⟶ S} {t' : W ⟶ S'}
  {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {Φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}

def Moved (v : LB.Iso L' (L.pull Φ)) (ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t' ⊗ A').left) {k : ℤ}
    (s' : LB.Sec (LPow A' L' k (Over.mk t'))) (s : LB.Sec (LPow A L k (Over.mk t))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk t ⊗ A).left) (z : Z) (i : L.ι) (i' : L'.ι),
    (snd (Over.mk t) A).left (r z) ∈ L.U i → (snd (Over.mk t') A').left (ω (r z)) ∈ L'.U i' →
    powVal (L := L) (g := (snd (Over.mk t) A).left) s r z i =
      (gw v ((r ≫ ω) ≫ (snd (Over.mk t') A').left) z i i' ^ k).val *
        powVal (L := L') (g := (snd (Over.mk t') A').left) s' (r ≫ ω) z i'

theorem exists_theta_moved (hL : L.IsLB) (hL' : L'.IsLB) (ht : t' ≫ g = t) (hp : IsGrpPullback A' A g Φ)
    {v : LB.Iso L' (L.pull Φ)} (hv : PGen v) {ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t' ⊗ A').left}
    (h₁ : ω ≫ (fst (Over.mk t') A').left = (fst (Over.mk t) A).left)
    (h₂ : ω ≫ (snd (Over.mk t') A').left ≫ Φ = (snd (Over.mk t) A).left) {k : ℤ}
    (θ' : ThetaGrp A' L' k (Over.mk t')) {x : Over.mk t ⟶ A} (hx : θ'.pt.left ≫ Φ = x.left) :
    ∃ θ : ThetaGrp A L k (Over.mk t), θ.pt = x ∧ ∀ s' s₂' s s₂, Moved v ω s' s → Moved v ω s₂' s₂ →
      IsActOf A' L' k θ' s' s₂' → IsActOf A L k θ s s₂ := by
  have hc : ∀ κ, ω ≫ (![(snd (Over.mk t') A').left, (translPt A' θ'.pt).left] κ) ≫ Φ =
      ![(snd (Over.mk t) A).left, (translPt A x).left] κ := by
    intro κ
    fin_cases κ
    · exact h₂
    · exact translPt_cmp ht hp hx h₁ h₂
  obtain ⟨t₀, ht₀, hv₀⟩ := exists_gen_up hL hL' hv (ε := ![k, -k]) ω hc θ'.φ θ'.isGen
  refine ⟨⟨x, t₀, ht₀⟩, rfl, fun s' s₂' s s₂ hs hs₂ hact => ActVal.isActOf hL ?_⟩
  have ha := actVal_of_isActOf hact
  intro Z r z J hJ
  obtain ⟨J', hJ', -⟩ := exists_good L' hL' z (fun e : Empty => e.elim) (fun e : Empty => e.elim)
    (fun a _ _ => a.elim) (fun a => a.elim)
  have a1 := hs₂ Z r z (J (r ≫ (snd (Over.mk t) A).left)) (J' ((r ≫ ω) ≫ (snd (Over.mk t') A').left))
    (hJ _) (hJ' ((r ≫ ω) ≫ (snd (Over.mk t') A').left))
  have a2 := ha Z (r ≫ ω) z J' hJ'
  unfold secVal at a2
  erw [sval_eq_powVal, sval_eq_powVal] at a2
  unfold thetaVal at a2
  have a3 := hv₀ Z r z J J' hJ hJ'
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at a3
  have a4 := hs Z (r ≫ (translT A x).left) z (J ((r ≫ (translT A x).left) ≫ (snd (Over.mk t) A).left))
    (J' (((r ≫ (translT A x).left) ≫ ω) ≫ (snd (Over.mk t') A').left)) (hJ _)
    (hJ' (((r ≫ (translT A x).left) ≫ ω) ≫ (snd (Over.mk t') A').left))
  have hT : (r ≫ (translT A x).left) ≫ ω = (r ≫ ω) ≫ (translT A' θ'.pt).left := by
    rw [Category.assoc, translT_cmp ht hp hx h₁ h₂, ← Category.assoc]
  have hS : ((r ≫ ω) ≫ (translT A' θ'.pt).left) ≫ (snd (Over.mk t') A').left = (r ≫ ω) ≫ (translPt A' θ'.pt).left := by
    rw [Category.assoc, translT_snd_left]
  have hS0 : (r ≫ (translT A x).left) ≫ (snd (Over.mk t) A).left = r ≫ (translPt A x).left := by
    rw [Category.assoc, translT_snd_left]
  rw [hT, hS, hS0] at a4
  rw [hS] at a2
  unfold secVal
  erw [sval_eq_powVal, sval_eq_powVal]
  rw [hS0, a1, a2, a4]
  change _ = (val t₀ r z J).val * _
  rw [a3, zpow_neg, Units.val_mul, Units.val_mul]
  have hu := Units.inv_mul (gw v ((r ≫ ω) ≫ (translPt A' θ'.pt).left) z (J (r ≫ (translPt A x).left))
    (J' ((r ≫ ω) ≫ (translPt A' θ'.pt).left)) ^ k)
  linear_combination (-((gw v ((r ≫ ω) ≫ (snd (Over.mk t') A').left) z (J (r ≫ (snd (Over.mk t) A).left))
    (J' ((r ≫ ω) ≫ (snd (Over.mk t') A').left)) ^ k).val * (val θ'.φ (r ≫ ω) z J').val *
    powVal s' ((r ≫ ω) ≫ (translT A' θ'.pt).left) z (J' ((r ≫ ω) ≫ (translPt A' θ'.pt).left)))) * hu

end Theta

section Sections

variable {S S' W : Scheme.{0}} {t : W ⟶ S} {t' : W ⟶ S'}
  {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {Φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
  {ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t' ⊗ A').left} {Y Y' N N' V V' : Scheme.{0}} {M : LB N} {M' : LB N'}

theorem exists_moved (hL : L.IsLB) (hL' : L'.IsLB) (h₂ : ω ≫ (snd (Over.mk t') A').left ≫ Φ = (snd (Over.mk t) A).left)
    {c₁ : Y' ⟶ A'.left} {n₁ : A'.left ⟶ Y'} (hn : n₁ ≫ c₁ = 𝟙 _) {v₂ : LB.Iso (L'.pull c₁) (L.pull (c₁ ≫ Φ))}
    (hv₂ : v₂.IsGen) {v : LB.Iso L' (L.pull Φ)}
    (hv : ∀ (Z : Scheme.{0}) (f : Z ⟶ A'.left) (z : Z) (j : L.ι) (i : L'.ι),
      Φ (f z) ∈ L.U j → f z ∈ L'.U i → gw v f z j i = isoVal v₂ (f ≫ n₁) z j i) {k : ℤ}
    (s' : LB.Sec (LPow A' L' k (Over.mk t'))) : ∃ s : LB.Sec (LPow A L k (Over.mk t)), Moved v ω s' s := by
  have hn' : ∀ {V : Scheme.{0}} (h : A'.left ⟶ V), n₁ ≫ c₁ ≫ h = h := fun h => by
    rw [← Category.assoc, hn, Category.id_comp]
  have e₁ : ω ≫ (snd (Over.mk t') A').left = (ω ≫ (snd (Over.mk t') A').left ≫ n₁) ≫ c₁ := by
    rw [Category.assoc, Category.assoc, hn, Category.comp_id]
  have e₂ : (snd (Over.mk t) A).left = (ω ≫ (snd (Over.mk t') A').left ≫ n₁) ≫ c₁ ≫ Φ := by
    rw [← h₂, Category.assoc, Category.assoc, hn']
  obtain ⟨b, hb⟩ := exists_move hL' hL hv₂ (ω ≫ (snd (Over.mk t') A').left ≫ n₁) k ω e₁ e₂ s'
  refine ⟨b, fun Z r z i i' hi hi' => ?_⟩
  have hΦ : Φ (((r ≫ ω) ≫ (snd (Over.mk t') A').left) z) ∈ L.U i := by
    rw [← h₂] at hi
    exact hi
  have m₂ : (c₁ ≫ Φ) ((ω ≫ (snd (Over.mk t') A').left ≫ n₁) (r z)) ∈ L.U i := by
    rw [e₂] at hi
    exact hi
  have m₁ : (ω ≫ (snd (Over.mk t') A').left) (r z) ∈ L'.U i' := hi'
  rw [e₁] at m₁
  rw [hv _ _ _ _ _ hΦ hi', hb Z r z i i' m₂ m₁]
  simp only [Category.assoc]

theorem moved_sec (hL : L.IsLB) (hL' : L'.IsLB)
    {c₀ : Y ⟶ A.left} {n : A.left ⟶ Y} {q : Y ⟶ N} {w : LB.Iso (L.pull c₀) (M.pull q)}
    {c₁ : Y' ⟶ A'.left} {n₁ : A'.left ⟶ Y'} (hn₁ : c₁ ≫ n₁ = 𝟙 _) {q' : Y' ⟶ N'} {w' : LB.Iso (L'.pull c₁) (M'.pull q')}
    {Ψ : N' ⟶ N} {wM : LB.Iso M' (M.pull Ψ)} (hn : n ≫ c₀ = 𝟙 _) (hΦ : (c₁ ≫ Φ) ≫ n ≫ q = q' ≫ Ψ)
    {v₂ : LB.Iso (L'.pull c₁) (L.pull (c₁ ≫ Φ))}
    (hsq : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y') (z : Z) (j : M.ι) (j' : M'.ι) (i : L.ι) (i' : L'.ι),
        Ψ (q' (f z)) ∈ M.U j → q' (f z) ∈ M'.U j' → (c₁ ≫ Φ) (f z) ∈ L.U i → c₁ (f z) ∈ L'.U i' →
        isoVal w (f ≫ (c₁ ≫ Φ) ≫ n) z j i * isoVal v₂ f z i i' = gw wM (f ≫ q') z j j' * isoVal w' f z j' i')
    {v : LB.Iso L' (L.pull Φ)}
    (hv : ∀ (Z : Scheme.{0}) (f : Z ⟶ A'.left) (z : Z) (j : L.ι) (i : L'.ι),
      Φ (f z) ∈ L.U j → f z ∈ L'.U i → gw v f z j i = isoVal v₂ (f ≫ n₁) z j i)
    {m : V ⟶ Y} {h : V ⟶ (Over.mk t ⊗ A).left} {m' : V' ⟶ Y'} {h' : V' ⟶ (Over.mk t' ⊗ A').left} {Ξ : V' ⟶ V}
    (x₁ : (Ξ ≫ h) ≫ ω = h') (x₂ : Ξ ≫ m = m' ≫ (c₁ ≫ Φ) ≫ n) {k : ℕ}
    {s' : LB.Sec (LPow A' L' k (Over.mk t'))} {s : LB.Sec (LPow A L k (Over.mk t))} (hs : Moved v ω s' s)
    {σ : LB.Sec (LB.LinComb M (K := Fin 1) (fun _ => m ≫ q) (fun _ => (k : ℤ)))}
    {σ' : LB.Sec (LB.LinComb M' (K := Fin 1) (fun _ => m' ≫ q') (fun _ => (k : ℤ)))}
    (H : GeneratorPullback.IsoRelM L M c₀ q w m k (snd (Over.mk t) A).left h s (m ≫ q) (𝟙 _) σ)
    (H' : GeneratorPullback.IsoRelM L' M' c₁ q' w' m' k (snd (Over.mk t') A').left h' s' (m' ≫ q') (𝟙 _) σ')
    (Z : Scheme.{0}) (r : Z ⟶ V') (z : Z) (p : Fin 1 → M.ι) (p' : Fin 1 → M'.ι)
    (hp : ∀ κ, Ψ ((m' ≫ q') (r z)) ∈ M.U (p κ)) (hp' : ∀ κ, (m' ≫ q') (r z) ∈ M'.U (p' κ)) :
    gs (r ≫ Ξ) z (LB.wchart M (fun _ : Fin 1 => m ≫ q) p) (σ.f p) =
      (∏ κ : Fin 1, gw wM (r ≫ m' ≫ q') z (p κ) (p' κ) ^ (k : ℤ)).val *
        gs r z (LB.wchart M' (fun _ : Fin 1 => m' ≫ q') p') (σ'.f p') := by
  have H₀ := H
  have H₀' := H'
  unfold GeneratorPullback.IsoRelM at H₀ H₀'
  have PH := (isoRelM_iff w m k h H₀.1 (𝟙 V) H₀.2.1 s σ).1 H
  have PH' := (isoRelM_iff w' m' k h' H₀'.1 (𝟙 V') H₀'.2.1 s' σ').1 H'
  obtain ⟨i₁, hi₁⟩ := exists_chart hL (c₀ (m (Ξ (r z))))
  obtain ⟨i', hi'⟩ := exists_chart hL' (c₁ (m' (r z)))
  simp only [Category.assoc] at hΦ x₂ x₁
  have eq_q : Ξ ≫ m ≫ q = m' ≫ q' ≫ Ψ := by
    rw [← Category.assoc, x₂]
    simp only [Category.assoc, hΦ]
  have eq_c : Ξ ≫ m ≫ c₀ = m' ≫ c₁ ≫ Φ := by
    rw [← Category.assoc, x₂]
    simp only [Category.assoc, hn, Category.comp_id]
  have eq_h' : h' ≫ (snd (Over.mk t') A').left ≫ n₁ = m' := by
    rw [← Category.assoc, H₀'.1, Category.assoc, hn₁, Category.comp_id]
  have eq_R : ((r ≫ Ξ) ≫ h) ≫ ω = r ≫ h' := by
    simp only [Category.assoc, x₁]
  have m_q : (Ξ ≫ m ≫ q) (r z) ∈ M.U (p 0) := by
    rw [eq_q]
    exact hp 0
  have m_snd : (h ≫ (snd (Over.mk t) A).left) (Ξ (r z)) ∈ L.U i₁ := by
    rw [H₀.1]
    exact hi₁
  have m_h' : (h' ≫ (snd (Over.mk t') A').left) (r z) ∈ L'.U i' := by
    rw [H₀'.1]
    exact hi'
  have m_snd' : ((((r ≫ Ξ) ≫ h) ≫ ω) ≫ (snd (Over.mk t') A').left) z ∈ L'.U i' := by
    rw [eq_R, Category.assoc]
    exact m_h'
  have m_c : (m' ≫ c₁ ≫ Φ) (r z) ∈ L.U i₁ := by
    rw [← eq_c]
    exact hi₁
  have m_v1 : (h' ≫ (snd (Over.mk t') A').left ≫ Φ) (r z) ∈ L.U i₁ := by
    rw [← Category.assoc, H₀'.1, Category.assoc]
    exact m_c
  have E1 := PH Z (r ≫ Ξ) z (p 0) i₁ m_q hi₁
  have E2 := hs Z ((r ≫ Ξ) ≫ h) z i₁ i' m_snd m_snd'
  rw [eq_R] at E2
  have E3 := PH' Z r z (p' 0) i' (hp' 0) hi'
  have E4 := hsq Z (r ≫ m') z (p 0) (p' 0) i₁ i' (hp 0) (hp' 0) m_c hi'
  have E5 := hv Z ((r ≫ h') ≫ (snd (Over.mk t') A').left) z i₁ i' m_v1 m_h'
  have eq_m : ((r ≫ h') ≫ (snd (Over.mk t') A').left) ≫ n₁ = r ≫ m' := by
    simp only [Category.assoc]
    rw [eq_h']
  rw [eq_m] at E5
  have eq_W : (r ≫ m') ≫ (c₁ ≫ Φ) ≫ n = (r ≫ Ξ) ≫ m := by
    simp only [Category.assoc]
    rw [x₂]
  have eq_g : (r ≫ m') ≫ q' = r ≫ m' ≫ q' := Category.assoc _ _ _
  rw [eq_W, eq_g] at E4
  have hp0 : p = fun _ => p 0 := funext fun κ => congrArg p (Subsingleton.elim κ 0)
  have hp0' : p' = fun _ => p' 0 := funext fun κ => congrArg p' (Subsingleton.elim κ 0)
  have L1 : gs (r ≫ Ξ) z (M.wchart (fun _ => m ≫ q) p) (σ.f p) = powVal σ ((r ≫ Ξ) ≫ 𝟙 V) z (p 0) := by
    rw [Category.comp_id, hp0]
    rfl
  have L2 : gs r z (M'.wchart (fun _ => m' ≫ q') p') (σ'.f p') = powVal σ' (r ≫ 𝟙 V') z (p' 0) := by
    rw [Category.comp_id, hp0']
    rfl
  have E6 : isoVal w ((r ≫ Ξ) ≫ m) z (p 0) i₁ ^ (k : ℤ) * isoVal v₂ (r ≫ m') z i₁ i' ^ (k : ℤ) =
      gw wM (r ≫ m' ≫ q') z (p 0) (p' 0) ^ (k : ℤ) * isoVal w' (r ≫ m') z (p' 0) i' ^ (k : ℤ) := by
    rw [← mul_zpow, ← mul_zpow, E4]
  rw [Fin.prod_univ_one, L1, L2, E1, E2, E3, E5, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, E6]

end Sections

end GlobalTheory.ThetaBaseChange
