import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoLinCombSymmBiadditiveSubstitution
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.PowerPullback

theorem biadd_eq_zero {G M : Type*} [CommGroup G] [AddCommGroup M] (D : G → G → M)
    (hB : ∀ x x' y, D (x * x') y = D x y + D x' y) (hs : ∀ x y, D x y = D y x) {n : ℕ}
    (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (hW : (W + W.transpose).det = 1)
    (h : ∀ x : Fin (n + 1) → G, ∑ uv : Fin (n + 1) × Fin (n + 1), W uv.1 uv.2 • D (x uv.1) (x uv.2) = 0)
    (a b : G) : D a b = 0 := by
  have h1 : ∀ y, D 1 y = 0 := fun y => by
    have e := hB 1 1 y
    rw [_root_.mul_one] at e
    exact add_left_cancel (a := D 1 y) (by rw [add_zero]; exact e.symm)
  have h2 : ∀ y, D y 1 = 0 := fun y => by rw [hs]; exact h1 y
  have hB' : ∀ x y y', D x (y * y') = D x y + D x y' := fun x y y' => by
    rw [hs, hB, hs y x, hs y' x]
  have hpol : ∀ y z : Fin (n + 1) → G,
      ∑ uv : Fin (n + 1) × Fin (n + 1), (W + W.transpose) uv.1 uv.2 • D (y uv.1) (z uv.2) = 0 := by
    intro y z
    have e := h (y * z)
    simp only [Pi.mul_apply, hB, hB', smul_add, Finset.sum_add_distrib, h y, h z] at e
    have hswap : ∑ uv : Fin (n + 1) × Fin (n + 1), W uv.2 uv.1 • D (y uv.1) (z uv.2) =
        ∑ uv : Fin (n + 1) × Fin (n + 1), W uv.1 uv.2 • D (z uv.1) (y uv.2) :=
      Fintype.sum_equiv (Equiv.prodComm _ _) _ _ (fun uv => by rw [hs]; rfl)
    simp only [Matrix.add_apply, Matrix.transpose_apply, add_smul, Finset.sum_add_distrib, hswap]
    rw [← e]
    abel
  have hk : ∀ k, (W + W.transpose) k 0 • D a b = 0 := by
    intro k
    have e := hpol (Pi.mulSingle k a) (Pi.mulSingle 0 b)
    rwa [Finset.sum_eq_single (k, 0) ?_ (by simp), Pi.mulSingle_eq_same, Pi.mulSingle_eq_same] at e
    rintro ⟨u, v⟩ _ huv
    by_cases hu : u = k
    · subst hu
      have hv : v ≠ 0 := fun hv => huv (by rw [hv])
      simp [Pi.mulSingle_eq_of_ne hv, h2]
    · simp [Pi.mulSingle_eq_of_ne hu, h1]
  have hadj := congrFun (congrFun (Matrix.adjugate_mul (W + W.transpose)) 0) 0
  rw [hW, Matrix.mul_apply, one_smul, Matrix.one_apply_eq] at hadj
  calc D a b = (1 : ℤ) • D a b := (one_smul _ _).symm
    _ = (∑ k, (W + W.transpose).adjugate 0 k * (W + W.transpose) k 0) • D a b := by rw [hadj]
    _ = 0 := by
      rw [Finset.sum_smul]
      exact Finset.sum_eq_zero fun k _ => by rw [mul_smul, hk k, smul_zero]

theorem isPullback_of {P X Y Z : Scheme.{0}} {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (w : p ≫ f = q ≫ g)
    (ex : ∀ (T : Scheme.{0}) (a : T ⟶ X) (b : T ⟶ Y), a ≫ f = b ≫ g → ∃ l : T ⟶ P, l ≫ p = a ∧ l ≫ q = b)
    (un : ∀ (T : Scheme.{0}) (l l' : T ⟶ P), l ≫ p = l' ≫ p → l ≫ q = l' ≫ q → l = l') : IsPullback p q f g := by
  choose l hl₁ hl₂ using ex
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk w (fun s => l s.pt s.fst s.snd s.condition)
    (fun s => hl₁ _ _ _ _) (fun s => hl₂ _ _ _ _)
    (fun s m h₁ h₂ => un _ _ _ (h₁.trans (hl₁ _ _ _ _).symm) (h₂.trans (hl₂ _ _ _ _).symm)))

section
variable {S : Scheme.{0}} {A C : Over S} {I : Type} {pr : I → (A ⟶ C)}
  (hU : ∀ (T : Over S) (y : I → (T ⟶ C)), ∃! x : T ⟶ A, ∀ u, x ≫ pr u = y u)
include hU

theorem pow_ext {Z : Scheme.{0}} (a b : Z ⟶ A.left) (h₁ : a ≫ A.hom = b ≫ A.hom)
    (h₂ : ∀ u, a ≫ (pr u).left = b ≫ (pr u).left) : a = b := by
  obtain ⟨x, -, hx⟩ := hU (Over.mk (a ≫ A.hom)) (fun u => (Over.homMk a rfl : Over.mk (a ≫ A.hom) ⟶ A) ≫ pr u)
  have ea : (Over.homMk a rfl : Over.mk (a ≫ A.hom) ⟶ A) = x := hx _ (fun u => rfl)
  have eb : (Over.homMk b h₁.symm : Over.mk (a ≫ A.hom) ⟶ A) = x := hx _ (fun u => by
    apply Over.OverMorphism.ext
    simp [h₂])
  simpa using congrArg CommaMorphism.left (ea.trans eb.symm)

theorem pow_exists {Z : Scheme.{0}} (z : Z ⟶ S) (y : I → (Z ⟶ C.left)) (hy : ∀ u, y u ≫ C.hom = z) :
    ∃ x : Z ⟶ A.left, x ≫ A.hom = z ∧ ∀ u, x ≫ (pr u).left = y u := by
  obtain ⟨x, hx, -⟩ := hU (Over.mk z) (fun u => Over.homMk (y u) (hy u))
  refine ⟨x.left, by simpa using Over.w x, fun u => ?_⟩
  simpa using congrArg CommaMorphism.left (hx u)
end

theorem lift_square {S S' : Scheme.{0}} {C : Over S} {C' : Over S'} {ψ : C'.left ⟶ C.left}
    {ψ₂ : (C' ⊗ C').left ⟶ (C ⊗ C).left} (hsq : IsSquare ψ ψ₂) {T : Over S} {T' : Over S'} (φ : T'.left ⟶ T.left)
    {x y : T ⟶ C} {x' y' : T' ⟶ C'} (hx : x'.left ≫ ψ = φ ≫ x.left) (hy : y'.left ≫ ψ = φ ≫ y.left) :
    (lift x' y').left ≫ ψ₂ = φ ≫ (lift x y).left := by
  obtain ⟨h1, h2⟩ := hsq
  have e1 : (lift x' y').left ≫ ψ₂ ≫ (fst C C).left = x'.left ≫ ψ := by
    rw [h1, ← Category.assoc, ← Over.comp_left, lift_fst]
  have e2 : (lift x' y').left ≫ ψ₂ ≫ (snd C C).left = y'.left ≫ ψ := by
    rw [h2, ← Category.assoc, ← Over.comp_left, lift_snd]
  have e3 : φ ≫ (lift x y).left ≫ (fst C C).left = φ ≫ x.left := by
    rw [← Over.comp_left, lift_fst]
  have e4 : φ ≫ (lift x y).left ≫ (snd C C).left = φ ≫ y.left := by
    rw [← Over.comp_left, lift_snd]
  apply Over.tensorObj_ext
  · rw [Category.assoc, Category.assoc]; exact e1.trans (hx.trans e3.symm)
  · rw [Category.assoc, Category.assoc]; exact e2.trans (hy.trans e4.symm)

private theorem exists_monoidHom_points_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) (T : Over S') :
    ∃ M : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G), ∀ x, (M x).left = x.left ≫ φ := by
  refine ⟨MonoidHom.mk' (fun x => (Over.homMk (x.left ≫ φ)
    (by rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w]; rfl) : Over.mk (T.hom ≫ f) ⟶ G))
    (fun x y => ?_), fun x => rfl⟩
  apply Over.OverMorphism.ext
  exact (hφ.2 T x y _ _ rfl rfl).symm

private theorem exists_monoidHom_precomp {S : Scheme.{0}} {X Y G : Over S} [GrpObj G] (h : X ⟶ Y) :
    ∃ N : (Y ⟶ G) →* (X ⟶ G), ∀ g, N g = h ≫ g :=
  ⟨MonoidHom.mk' (fun g => h ≫ g) (fun a b => MonObj.comp_mul h a b), fun _ => rfl⟩

open GlobalTheory.CechPic in

theorem forward {h g : ℕ} {W : Matrix (Fin 8) (Fin 8) ℤ} {J : Type} {a : J → Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} {k : ℕ} {o : Type} [CommRing o] {b : TBase o k}
    {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {c : SiegPre h k (b.ζ : o) s} {c' : SiegPre h k (b.ζ : o) s'}
    {t : TObj g k J b s} {t' : TObj g k J b s'} {f : S' ⟶ S} (H : IsSharp W a bas t c) (H' : IsSharp W a bas t' c')
    (hpb : SiegPB c' c f) : TMap t' t f := by
  obtain ⟨pr, hpr, hU, hL, hact, hpt⟩ := H
  obtain ⟨pr', hpr', hU', hL', hact', hpt'⟩ := H'
  obtain ⟨φ, φ₂, hφ, hsq, hP, hlev⟩ := hpb
  have hw : φ ≫ c.A.hom = c'.A.hom ≫ f := hφ.1.w
  have hb : ∀ X : Scheme.{0}, (Out.baseOver X).hom = 𝟙 X := fun _ => rfl
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ := pow_exists hU (t'.A.hom ≫ f) (fun u => (pr' u).left ≫ φ)
    (fun u => by rw [Category.assoc, hw, ← Category.assoc, Over.w])
  obtain ⟨M, hM⟩ := exists_monoidHom_points_of_isGrpPullback hφ t'.A
  let Φt : Over.mk (t'.A.hom ≫ f) ⟶ t.A := Over.homMk Φ (by rw [hΦ₁]; rfl)
  obtain ⟨N, hN⟩ := exists_monoidHom_precomp (G := c.A) Φt
  have hMN : ∀ u, M (pr' u) = Φt ≫ pr u := fun u => by
    apply Over.OverMorphism.ext
    rw [hM, Over.comp_left]
    exact (hΦ₂ u).symm
  refine ⟨Φ, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · refine isPullback_of hΦ₁ (fun T a b hab => ?_) (fun T l l' h1 h2 => ?_)
    · obtain ⟨l, hl₁, hl₂⟩ := pow_exists hU' b (fun u => hφ.1.lift (a ≫ (pr u).left) b
        (by rw [Category.assoc, Over.w]; exact hab)) (fun u => IsPullback.lift_snd _ _ _ _)
      refine ⟨l, pow_ext hU _ _ ?_ (fun u => ?_), hl₁⟩
      · rw [Category.assoc, hΦ₁, ← Category.assoc, hl₁, hab]
      · rw [Category.assoc, hΦ₂, ← Category.assoc, hl₂ u, IsPullback.lift_fst]
    · refine pow_ext hU' l l' h2 (fun u => hφ.1.hom_ext ?_ ?_)
      · simp only [Category.assoc, ← hΦ₂]
        simp only [← Category.assoc, h1]
      · simp only [Category.assoc, Over.w]
        exact h2
  · intro T x y x₀ y₀ hx hy
    refine pow_ext hU _ _ ?_ (fun u => ?_)
    · simp only [Over.w, Category.assoc, hΦ₁, Over.w_assoc, Over.mk_hom]
    · have := hpr u
      have := hpr' u
      have hx' : (x₀ ≫ pr u).left = (x ≫ pr' u).left ≫ φ := by
        rw [Over.comp_left, hx, Over.comp_left, Category.assoc, Category.assoc, hΦ₂]
      have hy' : (y₀ ≫ pr u).left = (y ≫ pr' u).left ≫ φ := by
        rw [Over.comp_left, hy, Over.comp_left, Category.assoc, Category.assoc, hΦ₂]
      calc (x₀ * y₀).left ≫ (pr u).left = ((x₀ * y₀) ≫ pr u).left := by rw [Over.comp_left]
        _ = ((x₀ ≫ pr u) * (y₀ ≫ pr u)).left := by rw [MonObj.mul_comp]
        _ = ((x ≫ pr' u) * (y ≫ pr' u)).left ≫ φ := hφ.2 T _ _ _ _ hx' hy'
        _ = ((x * y) ≫ pr' u).left ≫ φ := by rw [MonObj.mul_comp]
        _ = ((x * y).left ≫ Φ) ≫ (pr u).left := by rw [Over.comp_left, Category.assoc, Category.assoc, hΦ₂]
  · have hLt' := (cls_eq_iff t'.isLB (LB.isLB_linComb c'.isLB _ _)).2 hL'
    have hLt := (cls_eq_iff t.isLB (LB.isLB_linComb c.isLB _ _)).2 hL
    have hPc := (cls_eq_iff c'.isLB (pull_isLB c.isLB φ₂)).2 hP
    rw [cls_pull c.isLB] at hPc
    refine (cls_eq_iff t'.isLB (pull_isLB t.isLB Φ)).1 ?_
    rw [cls_pull t.isLB, hLt', hLt, cls_linComb c'.isLB, cls_linComb c.isLB, map_sum]
    refine Finset.sum_congr rfl fun uv _ => ?_
    rw [map_zsmul, hPc, ← pull_comp, ← pull_comp, lift_square hsq Φ (hΦ₂ uv.1).symm (hΦ₂ uv.2).symm]
  · intro i
    refine pow_ext hU _ _ ?_ (fun u => ?_)
    · rw [Category.assoc, hΦ₁, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp f).trans (Category.comp_id f).symm
    · rw [Category.assoc, hΦ₂, ← Category.assoc, ← Over.comp_left, hpt' i u, hlev, Category.assoc,
        ← Over.comp_left, hpt i u]
  · intro j
    refine pow_ext hU _ _ ?_ (fun u => ?_)
    · simp only [Category.assoc, hΦ₁, Over.w_assoc, Over.w]
    · have e1 : ((t'.act j).left ≫ Φ) ≫ (pr u).left = (M (t'.act j ≫ pr' u)).left := by
        rw [hM, Category.assoc, hΦ₂, ← Category.assoc, ← Over.comp_left]
      have e2 : (Φ ≫ (t.act j).left) ≫ (pr u).left = (Φt ≫ (t.act j ≫ pr u)).left := by
        simp [Φt]
      rw [e1, e2]
      suffices e : M (t'.act j ≫ pr' u) = Φt ≫ (t.act j ≫ pr u) by rw [e]
      rw [← hN, hact', hact, List.prod_ofFn, List.prod_ofFn, map_prod, map_prod]
      simp only [map_zpow]
      simp only [hMN, hN]

theorem exists_factor {S S' : Scheme.{0}} {A C : Over S} {A' C' : Over S'} [GrpObj A] [GrpObj C] [GrpObj A'] [GrpObj C']
    {I : Type} [DecidableEq I] (z : I) {pr : I → (A ⟶ C)} {pr' : I → (A' ⟶ C')} [∀ u, IsMonHom (pr u)]
    [∀ u, IsMonHom (pr' u)] (hU : ∀ (T : Over S) (y : I → (T ⟶ C)), ∃! x : T ⟶ A, ∀ u, x ≫ pr u = y u)
    (hU' : ∀ (T : Over S') (y : I → (T ⟶ C')), ∃! x : T ⟶ A', ∀ u, x ≫ pr' u = y u) {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (hφ : IsGrpPullback A' A f φ) (p : I → (A ⟶ A)) (p' : I → (A' ⟶ A'))
    (hp : ∀ u, p u ≫ pr z = pr u) (hp' : ∀ u w, p' u ≫ pr' w = if w = z then pr' u else 1)
    (hc : ∀ u, (p' u).left ≫ φ = φ ≫ (p u).left) :
    ∃ ψ : C'.left ⟶ C.left, IsGrpPullback C' C f ψ ∧ ∀ u, (pr' u).left ≫ ψ = φ ≫ (pr u).left := by
  obtain ⟨iz, hι, -⟩ := hU' C' (fun w => if w = z then 𝟙 C' else 1)
  have hιz : iz ≫ pr' z = 𝟙 C' := by rw [hι, if_pos rfl]
  have hp'ι : ∀ u, pr' u ≫ iz = p' u := fun u => by
    obtain ⟨_, -, huniq⟩ := hU' A' (fun w => if w = z then pr' u else 1)
    rw [huniq (pr' u ≫ iz) (fun w => ?_), huniq (p' u) (hp' u)]
    rw [Category.assoc, hι]
    split_ifs
    · exact Category.comp_id _
    · exact MonObj.comp_one _
  have hψ : ∀ u, (pr' u).left ≫ (iz.left ≫ φ ≫ (pr z).left) = φ ≫ (pr u).left := fun u => by
    rw [← Category.assoc, ← Over.comp_left, hp'ι, ← Category.assoc, hc, Category.assoc, ← Over.comp_left, hp]
  have hψw : (iz.left ≫ φ ≫ (pr z).left) ≫ C.hom = C'.hom ≫ f := by
    simp only [Category.assoc, Over.w, hφ.1.w, Over.w_assoc]
  have hιw : ∀ w {X : Scheme.{0}} (g : C'.left ⟶ X),
      iz.left ≫ (pr' w).left ≫ g = (if w = z then 𝟙 C'.left else (1 : C' ⟶ C').left) ≫ g := by
    intro w X g
    rw [← Category.assoc, ← Over.comp_left, hι w]
    split_ifs <;> rfl
  refine ⟨iz.left ≫ φ ≫ (pr z).left, ⟨isPullback_of hψw (fun T a b hab => ?_) (fun T l l' h1 h2 => ?_), ?_⟩, hψ⟩
  · obtain ⟨aA, haA, -⟩ := hU (Over.mk (b ≫ f))
      (fun w => if w = z then (Over.homMk a hab : Over.mk (b ≫ f) ⟶ C) else 1)
    refine ⟨hφ.1.lift aA.left b (by rw [Over.w]; rfl) ≫ (pr' z).left, ?_, ?_⟩
    · rw [Category.assoc, hψ z, ← Category.assoc, IsPullback.lift_fst, ← Over.comp_left, haA, if_pos rfl]
      rfl
    · rw [Category.assoc, Over.w (pr' z), IsPullback.lift_snd]
  · have hone : l ≫ (1 : C' ⟶ C').left = l' ≫ (1 : C' ⟶ C').left := by
      have e : (1 : C' ⟶ C').left = C'.hom ≫ (η[C'] : 𝟙_ (Over S') ⟶ C').left := rfl
      rw [e, ← Category.assoc, h2, Category.assoc]
    have key : l ≫ iz.left = l' ≫ iz.left := by
      apply hφ.1.hom_ext
      · refine pow_ext hU _ _ ?_ (fun w => ?_)
        · simp only [Category.assoc, hφ.1.w, Over.w_assoc]
          simp only [← Category.assoc, h2]
        · simp only [Category.assoc, ← hψ w]
          simp only [hιw]
          split_ifs
          · simpa using h1
          · rw [← Category.assoc, hone, Category.assoc]
      · simp only [Category.assoc, Over.w]
        exact h2
    calc l = l ≫ iz.left ≫ (pr' z).left := by rw [← Over.comp_left, hιz, Over.id_left, Category.comp_id]
      _ = l' ≫ iz.left ≫ (pr' z).left := by rw [← Category.assoc, key, Category.assoc]
      _ = l' := by rw [← Over.comp_left, hιz, Over.id_left, Category.comp_id]
  · intro T x y x₀ y₀ hx hy
    obtain ⟨Mh, hMh⟩ := exists_monoidHom_points_of_isGrpPullback hφ T
    have hιmul : (x * y) ≫ iz = (x ≫ iz) * (y ≫ iz) := by
      obtain ⟨_, -, huniq⟩ := hU' T (fun w => (x ≫ iz * y ≫ iz) ≫ pr' w)
      rw [huniq ((x * y) ≫ iz) (fun w => ?_), huniq _ (fun w => rfl)]
      rw [MonObj.mul_comp (x ≫ iz) (y ≫ iz) (pr' w)]
      simp only [Category.assoc, hι]
      split_ifs
      · simp only [Category.comp_id]
      · simp only [MonObj.comp_one, _root_.mul_one]
    have hx₀ : Mh (x ≫ iz) ≫ pr z = x₀ := by
      apply Over.OverMorphism.ext
      simp only [Over.comp_left, hMh, hx, Category.assoc]
    have hy₀ : Mh (y ≫ iz) ≫ pr z = y₀ := by
      apply Over.OverMorphism.ext
      simp only [Over.comp_left, hMh, hy, Category.assoc]
    subst hx₀ hy₀
    rw [← MonObj.mul_comp, ← map_mul, ← hιmul, Over.comp_left, hMh, Over.comp_left]
    simp only [Category.assoc]

open GlobalTheory.CechPic in

theorem pair_mul (hG : Out.GlobalFnsSt) {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (c : SiegPre h k ζ s) (hc : c.Principal) {T : Over S} (x x' y : T ⟶ c.A) :
    pull (lift (x * x') y).left (cls c.P c.isLB) =
      pull (lift x y).left (cls c.P c.isLB) + pull (lift x' y).left (cls c.P c.isLB) := by
  obtain ⟨hB, -⟩ := GlobalTheory.Biadditive.biadditive_of_triv_axes hG S c.A c.diag c.ab (pull_isLB c.isLB _) hc.1
    c.P c.isLB c.rig₁ c.rig₂ T x x' y
  have h0 := (cls_eq_zero_iff (LB.isLB_linComb c.isLB _ _)).2 hB
  rw [cls_linComb c.isLB] at h0
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, one_smul, neg_smul] at h0
  rw [← sub_eq_zero, ← h0]
  abel

open GlobalTheory.CechPic in

theorem pair_symm {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (c : SiegPre h k ζ s) {T : Over S} (x y : T ⟶ c.A) :
    pull (lift x y).left (cls c.P c.isLB) = pull (lift y x).left (cls c.P c.isLB) := by
  have e : cls c.P c.isLB = pull (lift (snd c.A c.A) (fst c.A c.A)).left (cls c.P c.isLB) := by
    rw [← cls_pull c.isLB _ (pull_isLB c.isLB _)]
    exact (cls_eq_iff c.isLB (pull_isLB c.isLB _)).2 c.symm
  conv_lhs => rw [e]
  rw [← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst]

theorem prod_single {G : Type*} [CommGroup G] (x : Fin 8 → G) (u v w : Fin 8) :
    (List.ofFn fun i => x i ^ (Matrix.single u v (1 : ℤ)) w i).prod = if w = u then x v else 1 := by
  rw [List.prod_ofFn]
  by_cases hw : w = u
  · subst hw
    rw [if_pos rfl, Finset.prod_eq_single v (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
    simp
  · rw [if_neg hw]
    exact Finset.prod_eq_one fun i _ => by simp [Ne.symm hw]

open GlobalTheory.CechPic in

theorem backward (hG : Out.GlobalFnsSt) {h g : ℕ} {W : Matrix (Fin 8) (Fin 8) ℤ} {J : Type}
    {a : J → Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} (hW : IsE8 W) {k : ℕ} {o : Type} [CommRing o]
    {b : TBase o k}
    {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {c : SiegPre h k (b.ζ : o) s} {c' : SiegPre h k (b.ζ : o) s'}
    {t : TObj g k J b s} {t' : TObj g k J b s'} {f : S' ⟶ S} (hc : c.Principal) (hc' : c'.Principal)
    (H : IsSharp W a bas t c) (H' : IsSharp W a bas t' c') (he : ∀ u v, ∃ j, a j = Matrix.single u v 1)
    (hT : TMap t' t f) : SiegPB c' c f := by
  obtain ⟨pr, hpr, hU, hL, hact, hpt⟩ := H
  obtain ⟨pr', hpr', hU', hL', hact', hpt'⟩ := H'
  obtain ⟨Φ, hΦ, hLΦ, hptΦ, hactΦ⟩ := hT
  have : ∀ u, IsMonHom (pr u) := hpr
  have : ∀ u, IsMonHom (pr' u) := hpr'
  choose j hj using he
  have hp : ∀ u, t.act (j 0 u) ≫ pr 0 = pr u := fun u => by
    rw [hact, hj, prod_single, if_pos rfl]
  have hp' : ∀ u w, t'.act (j 0 u) ≫ pr' w = if w = 0 then pr' u else 1 := fun u w => by
    rw [hact', hj, prod_single]
  obtain ⟨ψ, hψ, hψpr⟩ := exists_factor (0 : Fin 8) hU hU' hΦ (fun u => t.act (j 0 u))
    (fun u => t'.act (j 0 u)) hp hp' (fun u => hactΦ (j 0 u))
  let q₁ : Over.mk ((c'.A ⊗ c'.A).hom ≫ f) ⟶ c.A := Over.homMk ((fst c'.A c'.A).left ≫ ψ)
    (by rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w]; rfl)
  let q₂ : Over.mk ((c'.A ⊗ c'.A).hom ≫ f) ⟶ c.A := Over.homMk ((snd c'.A c'.A).left ≫ ψ)
    (by rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w]; rfl)
  obtain ⟨φ₂, hφ₂⟩ : ∃ φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left, φ₂ = (lift q₁ q₂).left := ⟨_, rfl⟩
  have hsq : IsSquare ψ φ₂ :=
    ⟨by rw [hφ₂, ← Over.comp_left, lift_fst] <;> rfl, by rw [hφ₂, ← Over.comp_left, lift_snd] <;> rfl⟩
  refine ⟨ψ, φ₂, hψ, hsq, ?_, ?_⟩
  · have hD0 : ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • pull (lift (pr' uv.1) (pr' uv.2)).left
        (cls c'.P c'.isLB - pull φ₂ (cls c.P c.isLB)) = 0 := by
      have hLt' := (cls_eq_iff t'.isLB (LB.isLB_linComb c'.isLB _ _)).2 hL'
      have hLt := (cls_eq_iff t.isLB (LB.isLB_linComb c.isLB _ _)).2 hL
      have hT2 := (cls_eq_iff t'.isLB (pull_isLB t.isLB Φ)).2 hLΦ
      rw [cls_pull t.isLB, hLt', hLt, cls_linComb c'.isLB, cls_linComb c.isLB, map_sum] at hT2
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hT2
      rw [← hT2]
      refine Finset.sum_congr rfl fun uv _ => ?_
      rw [map_sub, smul_sub, map_zsmul, ← pull_comp, ← pull_comp,
        lift_square hsq Φ (hψpr uv.1) (hψpr uv.2)]
    obtain ⟨Mh, hMh⟩ := exists_monoidHom_points_of_isGrpPullback hψ (c'.A ⊗ c'.A)
    have kT : ∀ x y : c'.A ⊗ c'.A ⟶ c'.A, pull (lift x y).left (pull φ₂ (cls c.P c.isLB)) =
        pull (lift (Mh x) (Mh y)).left (cls c.P c.isLB) := fun x y => by
      rw [← pull_comp, lift_square hsq (T := Over.mk ((c'.A ⊗ c'.A).hom ≫ f)) (𝟙 _) (x := Mh x) (y := Mh y)
        (by rw [hMh, Category.id_comp]) (by rw [hMh, Category.id_comp]), Category.id_comp]
    have h0 := biadd_eq_zero (G := c'.A ⊗ c'.A ⟶ c'.A) (M := Pic (G2 c'.A).left)
      (fun x y => pull (lift x y).left (cls c'.P c'.isLB - pull φ₂ (cls c.P c.isLB)))
      (fun x x' y => by
        simp only [map_sub, kT, map_mul]
        rw [pair_mul hG c' hc' x x' y, pair_mul hG c hc (Mh x) (Mh x') (Mh y)]
        exact add_sub_add_comm _ _ _ _)
      (fun x y => by
        simp only [map_sub, kT]
        rw [pair_symm c' x y, pair_symm c (Mh x) (Mh y)])
      (n := 7) W hW.2 (fun xs => ?_) (fst c'.A c'.A) (snd c'.A c'.A)
    · simp only [lift_fst_snd, Over.id_left, pull_id] at h0
      have e := sub_eq_zero.1 h0
      exact (cls_eq_iff c'.isLB (pull_isLB c.isLB _)).1 (e.trans (cls_pull c.isLB _ _).symm)
    · obtain ⟨X, hX, -⟩ := hU' (c'.A ⊗ c'.A) xs
      have e : ∀ uv : Fin 8 × Fin 8, W uv.1 uv.2 • pull (lift (xs uv.1) (xs uv.2)).left
          (cls c'.P c'.isLB - pull φ₂ (cls c.P c.isLB)) =
          pull X.left (W uv.1 uv.2 • pull (lift (pr' uv.1) (pr' uv.2)).left
          (cls c'.P c'.isLB - pull φ₂ (cls c.P c.isLB))) := fun uv => by
        rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, hX, hX]
      simp only [e]
      rw [← map_sum, hD0, map_zero]
  · obtain ⟨Mh, hMh⟩ := exists_monoidHom_points_of_isGrpPullback hψ (𝟙_ (Over S'))
    let F : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ 𝟙_ (Over S) :=
      Over.homMk f (by show f ≫ 𝟙 S = 𝟙 S' ≫ f; simp)
    let E₁ : (Fin h ⊕ Fin h → ℤ) →+ Additive (Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ c.A) :=
      AddMonoidHom.mk' (fun a => Additive.ofMul (Mh (c'.lev a))) (fun a b => by
        rw [c'.lev_add, map_mul, ofMul_mul])
    let E₂ : (Fin h ⊕ Fin h → ℤ) →+ Additive (Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ c.A) :=
      AddMonoidHom.mk' (fun a => Additive.ofMul (F ≫ c.lev a)) (fun a b => by
        rw [c.lev_add, MonObj.comp_mul, ofMul_mul])
    have hbasis : ∀ i u, E₁ (bas (Pi.single i 1) u) = E₂ (bas (Pi.single i 1) u) := fun i u => by
      show Additive.ofMul (Mh (c'.lev (bas (Pi.single i 1) u))) = Additive.ofMul (F ≫ c.lev (bas (Pi.single i 1) u))
      congr 1
      apply Over.OverMorphism.ext
      rw [hMh, Over.comp_left, ← hpt' i u, Over.comp_left, Category.assoc, hψpr u, ← Category.assoc, hptΦ i,
        Category.assoc, ← Over.comp_left, hpt i u]
      all_goals rfl
    have hE : E₁ = E₂ := by
      refine AddMonoidHom.ext fun a => ?_
      obtain ⟨v, hv0⟩ : ∃ v, v = bas.symm (Pi.single 0 a) := ⟨_, rfl⟩
      have hv : v = ∑ i, v i • (Pi.single i 1 : Fin (2 * g) → ℤ) := by
        ext m
        simp [Finset.sum_apply, Pi.single_apply]
      have ha : a = ∑ i, v i • bas (Pi.single i 1) 0 := by
        have e1 : bas v = Pi.single 0 a := by rw [hv0]; exact bas.apply_symm_apply _
        have e2 := congrFun e1 0
        rw [Pi.single_eq_same] at e2
        rw [← e2]
        conv_lhs => rw [hv]
        rw [map_sum, Finset.sum_apply]
        simp only [map_zsmul, Pi.smul_apply]
      rw [ha, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, map_zsmul, hbasis]
    intro a
    have h3 : Mh (c'.lev a) = F ≫ c.lev a := congrArg Additive.toMul (DFunLike.congr_fun hE a)
    have h4 : (Mh (c'.lev a)).left = (F ≫ c.lev a).left := by rw [h3]
    rw [hMh, Over.comp_left] at h4
    exact h4

theorem main : Out.Laws → Out.Laws2 → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (c : SiegPre h k (b.ζ : o) s) (c' : SiegPre h k (b.ζ : o) s') (t : TObj g k J b s) (t' : TObj g k J b s') (f : S' ⟶ S), c.Principal → c'.Principal → IsSharp W a bas t c → IsSharp W a bas t' c' → (SiegPB c' c f → TMap t' t f) ∧ ((∀ u v, ∃ j, a j = Matrix.single u v 1) → TMap t' t f → SiegPB c' c f) := by
  intro hL _ h g W J a bas hW _ k o _ b S S' s s' c c' t t' f hc hc' H H'
  exact ⟨fun hpb => forward H H' hpb, fun he hT => backward hL.globalFns hW hc hc' H H' he hT⟩

end GlobalTheory.PowerPullback
end
