import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LamRigid

theorem rigid_pw {X X' Y S₀ : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) {K : Type} [Fintype K] (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    {a : LB.Gen (LB.LinComb L' φ' ε)} (ha : a.IsGen) {t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)} (ht : t.IsGen)
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (h0 : ∀ y : S₀, ∃ J J', Good L y J ∧ Good L' y J' ∧
      val t e y J = pw w φ' ε e y (fun k => J (e ≫ φ' k ≫ F)) (fun k => J' (e ≫ φ' k)) * val a e y J')
    (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (hJ : Good L z J)
    (hJ' : Good L' z J') :
    val t r z J = pw w φ' ε r z (fun k => J (r ≫ φ' k ≫ F)) (fun k => J' (r ≫ φ' k)) * val a r z J' := by
  obtain ⟨t₂, ht₂, hv₂⟩ : ∃ t₂ : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε), t₂.IsGen ∧ ∀ (Z : Scheme.{0})
      (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good L' z J' →
      val t₂ r z J = pw w φ' ε r z (fun k => J (r ≫ φ' k ≫ F)) (fun k => J' (r ≫ φ' k)) * val a r z J' := by
    obtain ⟨t₁, ht₁, hv⟩ := exists_up ((isGen_iff w).1 hw) hL hL' a ha
    exact ⟨t₁, ht₁, fun Z r z J J' hJ hJ' => hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)⟩
  refine (gen_unique hL p e he hp ht ht₂ (fun y J hJ => ?_) Z r z J hJ).trans (hv₂ Z r z J J' hJ hJ')
  obtain ⟨J₀, J₀', hJ₀, hJ₀', e₀⟩ := h0 y
  rw [GlobalTheory.UU.val_change ht e hJ hJ₀, GlobalTheory.UU.val_change ht₂ e hJ hJ₀, e₀, hv₂ _ e y J₀ J₀' hJ₀ hJ₀']

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

def ind {L : LB G.left} {Z : Scheme.{0}} (J : (Z ⟶ G.left) → L.ι) :
    (Z ⟶ (G2 G).left) → ULift.{0} (Finset (Fin 2)) → L.ι :=
  fun q I => J (q ≫ (psum G (x2 G) I.down).left)

variable {G}

theorem good_ind {L : LB G.left} {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ G.left) → L.ι} (hJ : Good L z J) :
    Good (abelian₂ G L) z (ind G J) := fun q => hJ.mem _ q

theorem adj_ind {L : LB G.left} (hL : L.IsLB) {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ G.left) → L.ι} (hJ : Good L z J)
    (χ : Z ⟶ (G2 G).left) : GlobalTheory.LamBiext.adj (GlobalTheory.LamBiext.lamφ G) GlobalTheory.LamBiext.lamε z (ind G J) J χ = 1 :=
  trF_self hL _ _ χ z (hJ.mem _ χ)

theorem square_over_hom_ext {X : Scheme.{0}} {a b : X ⟶ (G2 G).left} (h₁ : a ≫ (fst G G).left = b ≫ (fst G G).left)
    (h₂ : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b := pullback.hom_ext h₁ h₂

theorem cartesian_lift_three_comp_projection {T₀ : Over S} (p q r : T₀ ⟶ G) (i : Fin 3) : lift p (lift q r) ≫ x3 G i = ![p, q, r] i := by
  fin_cases i <;> simp [x3]

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

theorem lamVal_eq {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B']
    [IsCommMonObj B'] {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)) {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z)
    (J : (Z ⟶ B.left) → M.ι) (J' : (Z ⟶ B'.left) → M'.ι) :
    lamVal w p z J J' = gw w p z (ind B J (p ≫ β₂)) (ind B' J' p) := by
  have e : ind B J (p ≫ β₂) = fun I => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left) :=
    funext fun I => congrArg J (Category.assoc _ _ _)
  rw [e]; rfl

theorem pw_eq {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B']
    [IsCommMonObj B'] {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)) {Y Z : Scheme.{0}} {K : Type} [Fintype K]
    (φ' : K → (Y ⟶ (G2 B').left)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ B.left) → M.ι) (J' : (Z ⟶ B'.left) → M'.ι) :
    pw w φ' ε r z (fun k => ind B J (r ≫ φ' k ≫ β₂)) (fun k => ind B' J' (r ≫ φ' k)) =
      ∏ k, lamVal w (r ≫ φ' k) z J J' ^ ε k := by
  unfold pw
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [lamVal_eq, Category.assoc]
open GlobalTheory.LamBiext

theorem lam_iso_laws : ∀ (S S' : Scheme.{0}) (B : Over S) (B' : Over S') [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : RigLB B) (M' : RigLB B') (c : CubicalStr B M) (c' : CubicalStr B' M') (f : S' ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M'.L) ((abelian₂ B M.L).pull β₂)) (hβ : IsGrpPullback B' B f β), IsAbelianScheme B' → IsSquare β β₂ → w.IsGen → (∀ (T : Over S') z J J', Good M.L z J → Good M'.L z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (T : Over S') (x x' y : T ⟶ B') z J J', Good M.L z J → Good M'.L z J' → lamVal w (lift x y).left z J J' = lamVal w (lift y x).left z J J' ∧ ∀ (u u' v : Over.mk (T.hom ≫ f) ⟶ B), u.left = x.left ≫ β → u'.left = x'.left ≫ β → v.left = y.left ≫ β → lamVal w (lift (x * x') y).left z J J' * cubV c' z J' x x' y = @id (T.left.presheaf.stalk z)ˣ (cubV (T := Over.mk (T.hom ≫ f)) c z J u u' v) * lamVal w (lift x y).left z J J' * lamVal w (lift x' y).left z J J' := by
  intro S S' B B' _ _ _ _ M M' c c' f β β₂ w hβ hB hsq hw hn T x x' y z J J' hJ hJ'
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B M.L).IsLB := DVR.linComb_isLB _ M.isLB _ _
  have hL' : (abelian₂ B' M'.L).IsLB := DVR.linComb_isLB _ M'.isLB _ _
  have hw₀ : β ≫ B.hom = B'.hom ≫ f := hβ.1.w
  have pt_mul : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'), toBase hw₀ (a * b) = toBase hw₀ a * toBase hw₀ b :=
    fun a b => Over.OverMorphism.ext (hβ.2 _ a b _ _ rfl rfl).symm
  have pt_one : ∀ T₀ : Over S', toBase hw₀ (1 : T₀ ⟶ B') = 1 := fun T₀ =>
    mul_eq_left.1 ((pt_mul 1 1).symm.trans (congrArg (toBase hw₀) (mul_one 1)))
  have β₂_lift : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'),
      (lift a b).left ≫ β₂ = (lift (toBase hw₀ a) (toBase hw₀ b)).left := fun a b => square_over_hom_ext
    (by rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]; rfl)
    (by rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]; rfl)
  have Hlam : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B') {U : Type} [CommGroup U] (h : (T₀.left ⟶ B.left) → U),
      ∏ i, h (((lift a b).left ≫ β₂) ≫ lamφ B i) ^ lamε i =
        h (toBase hw₀ a * toBase hw₀ b).left * (h (toBase hw₀ a).left)⁻¹ * (h (toBase hw₀ b).left)⁻¹ *
          h (1 : Over.mk (T₀.hom ≫ f) ⟶ B).left := fun a b U _ h => by
    rw [β₂_lift]; exact prod_lam (toBase hw₀ a) (toBase hw₀ b) h

  have symm : lamVal w (lift x y).left z J J' = lamVal w (lift y x).left z J J' := by
    let φ2 : Fin 2 → ((G2 B').left ⟶ (G2 B').left) :=
      ![(lift (fst B' B') (snd B' B')).left, (lift (snd B' B') (fst B' B')).left]
    let ε2 : Fin 2 → ℤ := ![1, -1]
    have fe2' : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B') φ2) (flatε lamε ε2) := fun U _ h => by
      rw [prod_flat, Fin.prod_univ_two, Fintype.prod_empty]
      show 1 = (∏ i, h ((lift (fst B' B') (snd B' B')).left ≫ lamφ B' i) ^ lamε i) ^ (1 : ℤ) *
        (∏ i, h ((lift (snd B' B') (fst B' B')).left ≫ lamφ B' i) ^ lamε i) ^ (-1 : ℤ)
      rw [prod_lam, prod_lam, _root_.mul_comm (snd B' B')]
      apply Additive.ofMul.injective
      simp only [zpow_neg, zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
      abel
    have fe2 : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => φ2 k ≫ β₂) (flatε lamε ε2) :=
      fun U _ h => by
        rw [prod_flat, Fin.prod_univ_two, Fintype.prod_empty]
        show 1 = (∏ i, h (((lift (fst B' B') (snd B' B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ) *
          (∏ i, h (((lift (snd B' B') (fst B' B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (-1 : ℤ)
        rw [Hlam, Hlam, _root_.mul_comm (toBase hw₀ (snd B' B'))]
        apply Additive.ofMul.injective
        simp only [zpow_neg, zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
        abel
    obtain ⟨g', hg', hv'⟩ := exists_gen M'.isLB fe2' (LB.oneGen M'.L) (oneGen_isGen _)
    obtain ⟨g, hg, hv⟩ := exists_gen M.isLB fe2 (LB.oneGen M.L) (oneGen_isGen _)
    have Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z₀ : Z) J₀, Good M'.L z₀ J₀ →
        val (L := abelian₂ B' M'.L) (nest M'.L (lamφ B') lamε φ2 ε2 g') r z₀ (ind B' J₀) = 1 := fun r z₀ J₀ hJ₀ => by
      refine (val_nest hg' r (good_ind hJ₀) hJ₀).trans ?_
      simp only [adj_ind M'.isLB hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
      exact (hv' _ r z₀ J₀ hJ₀).trans (val_one r)
    have Ft : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z₀ : Z) J₀, Good M.L z₀ J₀ →
        val (L := abelian₂ B M.L) (nest M.L (lamφ B) lamε (fun k => φ2 k ≫ β₂) ε2 g) r z₀ (ind B J₀) = 1 :=
      fun r z₀ J₀ hJ₀ => by
        refine (val_nest hg r (good_ind hJ₀) hJ₀).trans ?_
        simp only [adj_ind M.isLB hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
        exact (hv _ r z₀ J₀ hJ₀).trans (val_one r)
    have Fp : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B') (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.L.ι)
        (J₀' : (T₀.left ⟶ B'.left) → M'.L.ι),
        pw w φ2 ε2 (lift a b).left z₀ (fun k => ind B J₀ ((lift a b).left ≫ φ2 k ≫ β₂))
          (fun k => ind B' J₀' ((lift a b).left ≫ φ2 k)) =
          lamVal w (lift a b).left z₀ J₀ J₀' * (lamVal w (lift b a).left z₀ J₀ J₀')⁻¹ := by
      intro T₀ a b z₀ J₀ J₀'
      rw [pw_eq, Fin.prod_univ_two]
      show lamVal w (lift a b ≫ lift (fst B' B') (snd B' B')).left z₀ J₀ J₀' ^ (1 : ℤ) *
        lamVal w (lift a b ≫ lift (snd B' B') (fst B' B')).left z₀ J₀ J₀' ^ (-1 : ℤ) = _
      rw [comp_lift, comp_lift, lift_fst, lift_snd, zpow_neg, zpow_one, zpow_one]
    have he2 : (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (snd B' B').left ≫ B'.hom = 𝟙 _ := by
      rw [Over.w]; exact Over.w (lift (1 : 𝟙_ (Over S') ⟶ B') 1)
    have E := rigid_pw w hw hL hL' φ2 ε2 (nest_isGen hg') (nest_isGen hg) _ _ he2
      (surj_comp (surj_snd hG hB _) (hG _ _ hB).2) (fun y₀ => by
        obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt M.isLB y₀
        obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt M'.isLB y₀
        refine ⟨ind B J₁, ind B' J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
        rw [Ft _ y₀ J₁ hJ₁, Fp, Fa _ y₀ J₁' hJ₁', mul_inv_cancel, _root_.mul_one])
      T.left (lift x y).left z (ind B J) (ind B' J') (good_ind hJ) (good_ind hJ')
    rw [Ft _ z J hJ, Fp, Fa _ z J' hJ', _root_.mul_one] at E
    exact mul_inv_eq_one.1 E.symm

  obtain ⟨l₁, l₂, hl₁, hl₂, cl₁, cl₂, vl⟩ := exists_laws M' c'
  let φ3 := law1φ B' (x3 B' 0) (x3 B' 1) (x3 B' 2)
  let β₃ : (G3 B').left ⟶ (G3 B).left :=
    (lift (toBase hw₀ (x3 B' 0)) (lift (toBase hw₀ (x3 B' 1)) (toBase hw₀ (x3 B' 2)))).left
  have fe3 : FormEq (fun I => β₃ ≫ thφ B (x3 B) I) thε (flatφ (lamφ B) (fun k => φ3 k ≫ β₂)) (flatε lamε lawε) :=
    fun U _ h => by
      have a := prod_cub (toBase hw₀ (x3 B' 0)) (toBase hw₀ (x3 B' 1)) (toBase hw₀ (x3 B' 2)) h
      have b := prod_law₁ (x3 B' 0) (x3 B' 1) (x3 B' 2) (fun χ => ∏ i, h ((χ ≫ β₂) ≫ lamφ B i) ^ lamε i)
      rw [id₃] at b
      simp only [Over.id_left, Category.id_comp, Hlam, pt_mul] at b
      rw [a, prod_flat, b]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
  obtain ⟨g₃, hg₃, hv₃⟩ := exists_gen M.isLB fe3 (LB.pullGen M.L (thφ B (x3 B)) thε c.t β₃)
    (DVR.pullGen_isGen _ _ _ _ c.isGen β₃)
  have ht₃ := nest_isGen (L := M.L) (φ := lamφ B) (δ := lamε) hg₃
  have Ft3 : ∀ {T₀ : Over S'} (a a' b : T₀ ⟶ B') (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.L.ι), Good M.L z₀ J₀ →
      val (L := abelian₂ B M.L) (nest M.L (lamφ B) lamε (fun k => φ3 k ≫ β₂) lawε g₃) (lift a (lift a' b)).left z₀ (ind B J₀) =
        cubV (T := Over.mk (T₀.hom ≫ f)) c z₀ J₀ (toBase hw₀ a) (toBase hw₀ a') (toBase hw₀ b) := by
    intro T₀ a a' b z₀ J₀ hJ₀
    show val (L := LB.LinComb M.L (lamφ B) lamε) (nest M.L (lamφ B) lamε (fun k => φ3 k ≫ β₂) lawε g₃) _ z₀ (ind B J₀) = _
    rw [val_nest hg₃ _ (good_ind hJ₀) hJ₀]
    simp only [adj_ind M.isLB hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
    rw [hv₃ _ _ z₀ J₀ hJ₀]
    refine (val_pull hJ₀ _ _ _).trans ?_
    refine congrArg (fun q => val (L := M.L) (φ := thφ B (x3 B)) (ε := thε) c.t q z₀ J₀) ?_
    refine hom_ext_triple B fun i => ?_
    have e1 : β₃ ≫ (x3 B i).left = (x3 B' i).left ≫ β := by
      show (lift _ (lift _ _) ≫ x3 B i).left = _
      rw [cartesian_lift_three_comp_projection]; fin_cases i <;> rfl
    rw [Category.assoc, e1, ← Category.assoc, ← Over.comp_left, cartesian_lift_three_comp_projection, ← Over.comp_left, cartesian_lift_three_comp_projection]
    fin_cases i <;> rfl
  have Fa3 : ∀ {T₀ : Over S'} (a a' b : T₀ ⟶ B') (z₀ : T₀.left) (J₀' : (T₀.left ⟶ B'.left) → M'.L.ι),
      Good M'.L z₀ J₀' → val (L := abelian₂ B' M'.L) l₁ (lift a (lift a' b)).left z₀ (ind B' J₀') = cubV c' z₀ J₀' a a' b := by
    intro T₀ a a' b z₀ J₀' hJ₀'
    show val (L := lamLB M') l₁ _ z₀ (ind B' J₀') = _
    rw [(vl z₀ (ind B' J₀') (good_ind hJ₀') J₀' hJ₀').1 a a' b, adj_ind M'.isLB hJ₀', adj_ind M'.isLB hJ₀',
      adj_ind M'.isLB hJ₀']
    simp
  have Fp3 : ∀ {T₀ : Over S'} (a a' b : T₀ ⟶ B') (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.L.ι)
      (J₀' : (T₀.left ⟶ B'.left) → M'.L.ι),
      pw w φ3 lawε (lift a (lift a' b)).left z₀ (fun k => ind B J₀ ((lift a (lift a' b)).left ≫ φ3 k ≫ β₂))
        (fun k => ind B' J₀' ((lift a (lift a' b)).left ≫ φ3 k)) =
        lamVal w (lift (a * a') b).left z₀ J₀ J₀' * (lamVal w (lift a b).left z₀ J₀ J₀')⁻¹ *
          (lamVal w (lift a' b).left z₀ J₀ J₀')⁻¹ := by
    intro T₀ a a' b z₀ J₀ J₀'
    rw [pw_eq]; exact prod_law₁ a a' b (fun χ => lamVal w χ z₀ J₀ J₀')

  have sj3 : Function.Surjective ((snd B' (B' ⊗ B')).left ≫ (snd B' B').left ≫ B'.hom).appTop.hom :=
    surj_comp (surj_snd hG hB _) (surj_comp (surj_snd hG hB _) (hG _ _ hB).2)
  have he3 : (lift (1 : 𝟙_ (Over S') ⟶ B') (lift 1 1)).left ≫ (snd B' (B' ⊗ B')).left ≫ (snd B' B').left ≫ B'.hom =
      𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w (lift (1 : 𝟙_ (Over S') ⟶ B') (lift 1 1))
  have R3 := rigid_pw w hw hL hL' φ3 lawε hl₁ ht₃ _ _ he3 sj3 (fun y₀ => by
    obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt M.isLB y₀
    obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt M'.isLB y₀
    refine ⟨ind B J₁, ind B' J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
    rw [Ft3 (T₀ := 𝟙_ (Over S')) 1 1 1 y₀ J₁ hJ₁, Fp3, Fa3 1 1 1 y₀ J₁' hJ₁', pt_one, _root_.mul_one,
      (isCub_cubV c (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) hJ₁).face, (isCub_cubV c' hJ₁').face,
      hn (𝟙_ (Over S')) y₀ J₁ J₁' hJ₁ hJ₁']
    simp)
  have E3 := R3 T.left (lift x (lift x' y)).left z (ind B J) (ind B' J') (good_ind hJ) (good_ind hJ')
  rw [Ft3 x x' y z J hJ, Fp3, Fa3 x x' y z J' hJ'] at E3
  refine ⟨symm, fun u u' v hu hu' hv => ?_⟩
  obtain rfl : u = toBase hw₀ x := Over.OverMorphism.ext hu
  obtain rfl : u' = toBase hw₀ x' := Over.OverMorphism.ext hu'
  obtain rfl : v = toBase hw₀ y := Over.OverMorphism.ext hv
  rw [id, E3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.LamRigid
