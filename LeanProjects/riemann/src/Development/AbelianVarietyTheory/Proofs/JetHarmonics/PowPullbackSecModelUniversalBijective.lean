import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.SecTie

section Gen
variable {X Y Z X' X₁ X₂ Y₁ Y₂ B B₀ : Scheme.{0}} {L' : LB X'} {L₁ : LB X₁} {L₂ : LB X₂} {F₁ : X' ⟶ X₁} {F₂ : X' ⟶ X₂}

abbrev PSec (L : LB X) (φ : Y ⟶ X) (q : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (q : ℤ)))

theorem mem_one {L : LB X} {φ : Y ⟶ X} {j : Fin 1 → L.ι} {y : Y} :
    y ∈ LB.wchart L (fun _ : Fin 1 => φ) j ↔ φ y ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem trans_one {L : LB X} {φ : Y ⟶ X} {q : ℕ} (s : PSec L φ q) (r : Z ⟶ Y) (z : Z) {j j' : Fin 1 → L.ι}
    (hj : r z ∈ LB.wchart L (fun _ : Fin 1 => φ) j) (hj' : r z ∈ LB.wchart L (fun _ : Fin 1 => φ) j') :
    gs r z (LB.wchart L (fun _ : Fin 1 => φ) j) (s.f j) =
      (gm (r ≫ φ) z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ q).val *
        gs r z (LB.wchart L (fun _ : Fin 1 => φ) j') (s.f j') := by
  rw [sec_trans s r z hj hj', trF, Fin.prod_univ_one, zpow_natCast]

def ratio (w₁ : LB.Iso L' (L₁.pull F₁)) (w₂ : LB.Iso L' (L₂.pull F₂)) (r : Z ⟶ X') (z : Z) (j₁ : L₁.ι) (j₂ : L₂.ι)
    (k : L'.ι) : (Z.presheaf.stalk z)ˣ := gw w₁ r z j₁ k * (gw w₂ r z j₂ k)⁻¹

theorem ratio_trans {w₁ : LB.Iso L' (L₁.pull F₁)} {w₂ : LB.Iso L' (L₂.pull F₂)} (h₁ : PGen w₁) (h₂ : PGen w₂)
    (r : Z ⟶ X') (z : Z) {j₁ j₁' : L₁.ι} {j₂ j₂' : L₂.ι} {k k' : L'.ι} (a : F₁ (r z) ∈ L₁.U j₁) (a' : F₁ (r z) ∈ L₁.U j₁')
    (b : F₂ (r z) ∈ L₂.U j₂) (b' : F₂ (r z) ∈ L₂.U j₂') (c : r z ∈ L'.U k) (c' : r z ∈ L'.U k') :
    ratio w₁ w₂ r z j₁ j₂ k * gm (r ≫ F₂) z _ (L₂.g j₂ j₂') = gm (r ≫ F₁) z _ (L₁.g j₁ j₁') * ratio w₁ w₂ r z j₁' j₂' k' := by
  rw [ratio, ratio, h₁ _ r z j₁ j₁' k k' a a' c c', h₂ _ r z j₂ j₂' k k' b b' c c']
  generalize gm (r ≫ F₁) z _ (L₁.g j₁ j₁') = A
  generalize gm (r ≫ F₂) z _ (L₂.g j₂ j₂') = A'
  generalize gm r z _ (L'.g k k') = C
  generalize gw w₁ r z j₁' k' = D
  generalize gw w₂ r z j₂' k' = D'
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_transport {w₁ : LB.Iso L' (L₁.pull F₁)} {w₂ : LB.Iso L' (L₂.pull F₂)} (h₁ : PGen w₁) (h₂ : PGen w₂)
    (hL' : L'.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {φ₁ : Y₁ ⟶ X₁} {φ₂ : Y₂ ⟶ X₂} (ρ : Y₁ ⟶ X') (e : Y₁ ⟶ Y₂)
    (e₁ : ρ ≫ F₁ = φ₁) (e₂ : e ≫ φ₂ = ρ ≫ F₂) (q : ℕ) (s₂ : PSec L₂ φ₂ q) :
    ∃ s₁ : PSec L₁ φ₁ q, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₁) (z : Z) (j₁ : Fin 1 → L₁.ι) (j₂ : Fin 1 → L₂.ι) (k : L'.ι),
      r z ∈ LB.wchart L₁ (fun _ : Fin 1 => φ₁) j₁ → e (r z) ∈ LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂ → ρ (r z) ∈ L'.U k →
      gs r z (LB.wchart L₁ (fun _ : Fin 1 => φ₁) j₁) (s₁.f j₁) =
        (ratio w₁ w₂ (r ≫ ρ) z (j₁ 0) (j₂ 0) k ^ q).val *
          gs (r ≫ e) z (LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂) (s₂.f j₂) := by
  subst e₁
  have m₂ : ∀ (y : Y₁) (j₂ : Fin 1 → L₂.ι), e y ∈ LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂ ↔ F₂ (ρ y) ∈ L₂.U (j₂ 0) :=
    fun y j₂ => mem_one.trans (iff_of_eq (congrArg (fun f => f y ∈ L₂.U (j₂ 0)) e₂))
  have m₁ : ∀ (y : Y₁) (j₁ : Fin 1 → L₁.ι), y ∈ LB.wchart L₁ (fun _ : Fin 1 => ρ ≫ F₁) j₁ ↔ F₁ (ρ y) ∈ L₁.U (j₁ 0) :=
    fun y j₁ => mem_one
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₁) (z : Z) (j₁ j₁' : Fin 1 → L₁.ι) (j₂ j₂' : Fin 1 → L₂.ι) (k k' : L'.ι),
      r z ∈ LB.wchart L₁ (fun _ : Fin 1 => ρ ≫ F₁) j₁ → e (r z) ∈ LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂ → ρ (r z) ∈ L'.U k →
      r z ∈ LB.wchart L₁ (fun _ : Fin 1 => ρ ≫ F₁) j₁' → e (r z) ∈ LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂' → ρ (r z) ∈ L'.U k' →
      (ratio w₁ w₂ (r ≫ ρ) z (j₁ 0) (j₂ 0) k ^ q).val *
          gs (r ≫ e) z (LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂) (s₂.f j₂) =
      (gm (r ≫ ρ ≫ F₁) z (L₁.U (j₁ 0) ⊓ L₁.U (j₁' 0)) (L₁.g (j₁ 0) (j₁' 0)) ^ q).val *
        ((ratio w₁ w₂ (r ≫ ρ) z (j₁' 0) (j₂' 0) k' ^ q).val *
          gs (r ≫ e) z (LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂') (s₂.f j₂')) := by
    intro Z r z j₁ j₁' j₂ j₂' k k' a b c a' b' c'
    have t := ratio_trans h₁ h₂ (r ≫ ρ) z ((m₁ _ _).1 a) ((m₁ _ _).1 a') ((m₂ _ _).1 b) ((m₂ _ _).1 b') c c'
    rw [trans_one s₂ (r ≫ e) z b b', Category.assoc, e₂, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
      ← Units.val_mul, ← mul_pow, ← mul_pow]
    rw [Category.assoc, Category.assoc] at t
    rw [t]
  have glue : ∀ j₁ : Fin 1 → L₁.ι, ∃ a : Γ(Y₁, LB.wchart L₁ (fun _ : Fin 1 => ρ ≫ F₁) j₁),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₁) (z : Z) (j₂ : Fin 1 → L₂.ι) (k : L'.ι),
      r z ∈ LB.wchart L₁ (fun _ : Fin 1 => ρ ≫ F₁) j₁ → e (r z) ∈ LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂ → ρ (r z) ∈ L'.U k →
      gs r z (LB.wchart L₁ (fun _ : Fin 1 => ρ ≫ F₁) j₁) a =
        (ratio w₁ w₂ (r ≫ ρ) z (j₁ 0) (j₂ 0) k ^ q).val *
          gs (r ≫ e) z (LB.wchart L₂ (fun _ : Fin 1 => φ₂) j₂) (s₂.f j₂) := by
    intro j₁
    let W : (Fin 1 → L₂.ι) × L'.ι → Y₁.Opens := fun p =>
      LB.wchart L₁ (fun _ : Fin 1 => ρ ≫ F₁) j₁ ⊓ e ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => φ₂) p.1 ⊓ ρ ⁻¹ᵁ L'.U p.2
    have l₁ : ∀ p, W p ≤ ρ ⁻¹ᵁ ((L₁.pull F₁).U (fun _ => j₁ 0) ⊓ L'.U p.2) := fun p y hy =>
      ⟨mem_pull.2 ((m₁ _ _).1 hy.1.1), hy.2⟩
    have l₂ : ∀ p, W p ≤ ρ ⁻¹ᵁ ((L₂.pull F₂).U (fun _ => p.1 0) ⊓ L'.U p.2) := fun p y hy =>
      ⟨mem_pull.2 ((m₂ _ _).1 hy.1.2), hy.2⟩
    have l₃ : ∀ p, W p ≤ e ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => φ₂) p.1 := fun p y hy => hy.1.2
    obtain ⟨u, hu⟩ : ∃ u : ∀ p, Γ(Y₁, W p), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₁) (z : Z) p, r z ∈ W p →
        gs r z (W p) (u p) = (ratio w₁ w₂ (r ≫ ρ) z (j₁ 0) (p.1 0) p.2 ^ q).val *
          gs (r ≫ e) z (LB.wchart L₂ (fun _ : Fin 1 => φ₂) p.1) (s₂.f p.1) :=
      ⟨fun p => ((res (l₁ p) (pullU ρ _ (w₁.s (fun _ => j₁ 0, p.2))) *
          (res (l₂ p) (pullU ρ _ (w₂.s (fun _ => p.1 0, p.2))))⁻¹) ^ q).val *
          (Y₁.presheaf.map (homOfLE (l₃ p)).op).hom ((e.app _).hom (s₂.f p.1)), fun Z r z p hz => by
        refine (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans (congrArg Units.val ?_))
          ((gs_res r z _ hz _).trans (gs_pull r e z _ (l₃ p hz) _)))
        rw [map_pow, map_mul, map_inv, gm_res r z _ hz, gm_res r z _ hz]
        exact congrArg (· ^ q) (congrArg₂ (· * ·)
          (gm_pull r ρ z ((L₁.pull F₁).U (fun _ => j₁ 0) ⊓ L'.U p.2) (l₁ p hz) _)
          (congrArg (·⁻¹) (gm_pull r ρ z ((L₂.pull F₂).U (fun _ => p.1 0) ⊓ L'.U p.2) (l₂ p hz) _)))⟩
    obtain ⟨a, ha, -⟩ := Y₁.sheaf.existsUnique_gluing' W (LB.wchart L₁ (fun _ : Fin 1 => ρ ≫ F₁) j₁)
      (fun p => homOfLE (inf_le_left.trans inf_le_left)) (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL' (ρ y)
        obtain ⟨j, hj⟩ := exists_chart hL₂ (F₂ (ρ y))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => j, k), ⟨hy, (m₂ _ _).2 hj⟩, hk⟩) u
      (fun p p' => fn_ext (V := W p ⊓ W p') fun y hy => by
        refine (gs_res (𝟙 Y₁) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y₁) y inf_le_right hy _).symm)
        rw [hu _ _ y p hy.1, hu _ _ y p' hy.2,
          key _ (𝟙 Y₁) y j₁ j₁ p.1 p'.1 p.2 p'.2 hy.1.1.1 hy.1.1.2 hy.1.2 hy.1.1.1 hy.2.1.2 hy.2.2,
          gm_self hL₁ (𝟙 Y₁ ≫ ρ ≫ F₁) y ((m₁ _ _).1 hy.1.1.1), one_pow, Units.val_one, _root_.one_mul])
    refine ⟨a, fun Z r z j₂ k a₁ a₂ a₃ => ?_⟩
    have hz : r z ∈ W (j₂, k) := ⟨⟨a₁, a₂⟩, a₃⟩
    exact (gs_res r z (inf_le_left.trans inf_le_left) hz a).symm.trans ((congrArg (gs r z (W (j₂, k))) (ha (j₂, k))).trans
      (hu Z r z (j₂, k) hz))
  choose a ha using glue
  refine ⟨⟨a, fun (j j' : Fin 1 → L₁.ι) => fn_ext fun y hy => ?_⟩, fun Z r z j₁ j₂ k => ha j₁ Z r z j₂ k⟩
  obtain ⟨k, hk⟩ := exists_chart hL' (ρ y)
  obtain ⟨i, hi⟩ := exists_chart hL₂ (F₂ (ρ y))
  have hi' := (m₂ y (fun _ => i)).2 hi
  have e₃ := gm_linComb L₁ (fun _ : Fin 1 => ρ ≫ F₁) (fun _ => (q : ℤ)) (𝟙 Y₁) y j j' hy.1 hy.2
  rw [Fin.prod_univ_one, zpow_natCast] at e₃
  have e₄ := ha j _ (𝟙 Y₁) y (fun _ => i) k hy.1 hi' hk
  have e₅ := ha j' _ (𝟙 Y₁) y (fun _ => i) k hy.2 hi' hk
  have e₆ := key _ (𝟙 Y₁) y j j' (fun _ => i) (fun _ => i) k k hy.1 hi' hk hy.2 hi' hk
  rw [← e₄, ← e₅, ← e₃] at e₆
  exact (gs_res (𝟙 Y₁) y _ hy _).trans (e₆.trans ((gs_mul (𝟙 Y₁) y _ hy _ _).trans (congrArg₂ (· * ·)
    (gs_unit (𝟙 Y₁) y _ hy _) (gs_res (𝟙 Y₁) y _ hy _))).symm)

def Comparison₂ (w₁ : LB.Iso L' (L₁.pull F₁)) (w₂ : LB.Iso L' (L₂.pull F₂)) (φ₁ : Y₁ ⟶ X₁) (φ₂ : Y₂ ⟶ X₂) (p₁ : Y₁ ⟶ B)
    (p₂ : Y₂ ⟶ B) (f : B ⟶ B₀) (π : X' ⟶ B₀) (q : ℕ) (s₂ : PSec L₂ φ₂ q) (s₁ : PSec L₁ φ₁ q) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z₂ : Z ⟶ Y₂) (z₁ : Z ⟶ Y₁), z₂ ≫ φ₂ = r ≫ F₂ → z₁ ≫ φ₁ = r ≫ F₁ →
    z₂ ≫ p₂ = z₁ ≫ p₁ → z₁ ≫ p₁ ≫ f = r ≫ π →
    ∀ (z : Z) (J₁ : (Z ⟶ X₁) → L₁.ι) (J₂ : (Z ⟶ X₂) → L₂.ι) (k : L'.ι), Good L₁ z J₁ → Good L₂ z J₂ → r z ∈ L'.U k →
      sval s₂ z₂ z J₂ * ((gw w₁ r z (J₁ (r ≫ F₁)) k).val) ^ q = sval s₁ z₁ z J₁ * ((gw w₂ r z (J₂ (r ≫ F₂)) k).val) ^ q

theorem Comparison₂.symm {w₁ : LB.Iso L' (L₁.pull F₁)} {w₂ : LB.Iso L' (L₂.pull F₂)} {φ₁ : Y₁ ⟶ X₁} {φ₂ : Y₂ ⟶ X₂} {p₁ : Y₁ ⟶ B}
    {p₂ : Y₂ ⟶ B} {f : B ⟶ B₀} {π : X' ⟶ B₀} {q : ℕ} {s₂ : PSec L₂ φ₂ q} {s₁ : PSec L₁ φ₁ q}
    (h : Comparison₂ w₁ w₂ φ₁ φ₂ p₁ p₂ f π q s₂ s₁) : Comparison₂ w₂ w₁ φ₂ φ₁ p₂ p₁ f π q s₁ s₂ :=
  fun Z r z₁ z₂ a b c d z J₂ J₁ k g₂ g₁ hk =>
    (h Z r z₂ z₁ b a c.symm (by rw [← d, ← Category.assoc, c, Category.assoc]) z J₁ J₂ k g₁ g₂ hk).symm

theorem existsUnique_tie {w₁ : LB.Iso L' (L₁.pull F₁)} {w₂ : LB.Iso L' (L₂.pull F₂)} (h₁ : PGen w₁) (h₂ : PGen w₂)
    (hL' : L'.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {φ₁ : Y₁ ⟶ X₁} {φ₂ : Y₂ ⟶ X₂} {p₁ : Y₁ ⟶ B}
    {p₂ : Y₂ ⟶ B} {f : B ⟶ B₀} {π : X' ⟶ B₀} {S₁ S₂ : Scheme.{0}} {π₁ : X₁ ⟶ S₁} {π₂ : X₂ ⟶ S₂} {b₁ : B₀ ⟶ S₁}
    {b₂ : B₀ ⟶ S₂} (c₁ : IsPullback F₁ π π₁ b₁) (c₂ : IsPullback F₂ π π₂ b₂) (d₁ : φ₁ ≫ π₁ = p₁ ≫ f ≫ b₁)
    (d₂ : IsPullback φ₂ p₂ π₂ (f ≫ b₂)) (q : ℕ) (s₂ : PSec L₂ φ₂ q) :
    ∃! s₁ : PSec L₁ φ₁ q, Comparison₂ w₁ w₂ φ₁ φ₂ p₁ p₂ f π q s₂ s₁ := by
  obtain ⟨ρ, r₁, r₂⟩ : ∃ ρ : Y₁ ⟶ X', ρ ≫ F₁ = φ₁ ∧ ρ ≫ π = p₁ ≫ f :=
    ⟨c₁.lift φ₁ (p₁ ≫ f) (by rw [d₁, Category.assoc]), c₁.lift_fst _ _ _, c₁.lift_snd _ _ _⟩
  obtain ⟨e, e₁, e₂⟩ : ∃ e : Y₁ ⟶ Y₂, e ≫ φ₂ = ρ ≫ F₂ ∧ e ≫ p₂ = p₁ :=
    ⟨d₂.lift (ρ ≫ F₂) p₁ (by rw [Category.assoc, c₂.w, ← Category.assoc, r₂, Category.assoc]), d₂.lift_fst _ _ _,
      d₂.lift_snd _ _ _⟩
  obtain ⟨s₁, hs⟩ := exists_transport h₁ h₂ hL' hL₁ hL₂ ρ e r₁ e₁ q s₂
  have T : Comparison₂ w₁ w₂ φ₁ φ₂ p₁ p₂ f π q s₂ s₁ := by
    intro Z r z₂ z₁ a b c d z J₁ J₂ k g₁ g₂ hk
    obtain rfl : r = z₁ ≫ ρ := c₁.hom_ext (by rw [Category.assoc, r₁, b]) (by rw [Category.assoc, r₂, d])
    obtain rfl : z₂ = z₁ ≫ e := d₂.hom_ext (by rw [a, Category.assoc, Category.assoc, e₁])
      (by rw [c, Category.assoc, e₂])
    have := hs Z z₁ z (fun _ => J₁ (z₁ ≫ φ₁)) (fun _ => J₂ ((z₁ ≫ e) ≫ φ₂)) k (g₁.mem (fun _ : Fin 1 => φ₁) z₁)
      (g₂.mem (fun _ : Fin 1 => φ₂) (z₁ ≫ e)) hk
    rw [← a, ← b]
    refine Eq.trans ?_ (congrArg (· * _) this).symm
    rw [ratio, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, mul_right_comm, ← Units.val_mul, ← mul_pow,
      inv_mul_cancel_right, _root_.mul_comm]
    rfl
  refine ⟨s₁, T, fun s₁' T' => ?_⟩
  have hf : ∀ j, s₁'.f j = s₁.f j := sec_ext_val hL₁ fun y J₁ g₁ => by
    choose J₂ g₂ using fun χ : Y₁ ⟶ X₂ => exists_chart hL₂ (χ y)
    obtain ⟨k, hk⟩ := exists_chart hL' (ρ y)
    have a := T Y₁ ρ e (𝟙 _) e₁ (by rw [Category.id_comp, r₁]) (by rw [Category.id_comp, e₂])
      (by rw [Category.id_comp, r₂]) y J₁ J₂ k g₁ g₂ hk
    have a' := T' Y₁ ρ e (𝟙 _) e₁ (by rw [Category.id_comp, r₁]) (by rw [Category.id_comp, e₂])
      (by rw [Category.id_comp, r₂]) y J₁ J₂ k g₁ g₂ hk
    exact ((Units.isUnit _).pow q).mul_right_cancel (a'.symm.trans a)
  obtain ⟨f', _⟩ := s₁'
  obtain ⟨f'', _⟩ := s₁
  obtain rfl : f' = f'' := funext hf
  rfl

theorem sval_scal {L : LB X} {φ : Y ⟶ X} {q : ℕ} {s s' : PSec L φ q} {p : Y ⟶ B} {u : Γ(B, ⊤)}
    (h : ∀ j, s'.f j = resTop _ (p.appTop.hom u) * s.f j) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (g : Good L z J) :
    sval s' r z J = gs (r ≫ p) z ⊤ u * sval s r z J := by
  have m := g.mem (fun _ : Fin 1 => φ) r
  exact (congrArg (gs r z _) (h _)).trans ((gs_mul r z _ m _ _).trans (congrArg (· * _)
    ((gs_res r z _ m _).trans (gs_pull r p z ⊤ trivial u))))

theorem Comparison₂.smul {w₁ : LB.Iso L' (L₁.pull F₁)} {w₂ : LB.Iso L' (L₂.pull F₂)} {φ₁ : Y₁ ⟶ X₁} {φ₂ : Y₂ ⟶ X₂} {p₁ : Y₁ ⟶ B}
    {p₂ : Y₂ ⟶ B} {f : B ⟶ B₀} {π : X' ⟶ B₀} {q : ℕ} {s₂ s₂' : PSec L₂ φ₂ q} {s₁ s₁' : PSec L₁ φ₁ q}
    (h : Comparison₂ w₁ w₂ φ₁ φ₂ p₁ p₂ f π q s₂ s₁) (u : Γ(B, ⊤)) (h₂ : ∀ j, s₂'.f j = resTop _ (p₂.appTop.hom u) * s₂.f j)
    (h₁ : ∀ j, s₁'.f j = resTop _ (p₁.appTop.hom u) * s₁.f j) : Comparison₂ w₁ w₂ φ₁ φ₂ p₁ p₂ f π q s₂' s₁' := by
  intro Z r z₂ z₁ a b c d z J₁ J₂ k g₁ g₂ hk
  rw [sval_scal h₂ z₂ z g₂, sval_scal h₁ z₁ z g₁, c, _root_.mul_assoc, _root_.mul_assoc,
    h Z r z₂ z₁ a b c d z J₁ J₂ k g₁ g₂ hk]

theorem isoCast_isGen {L L₀ : LB X} (h : L = L₀) {M : LB Y} (f : Y ⟶ X) (w : LB.Iso M (L.pull f)) (hw : w.IsGen) :
    (isoCast h f w).IsGen := by
  subst h
  exact hw

end Gen

set_option maxHeartbeats 800000 in

theorem secTie_bijective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∀ q : ℕ, (∀ σ, ∃! hh, SecTieF I P F xF q σ hh) ∧ (∀ hh, ∃! σ, SecTieF I P F xF q σ hh) ∧ ∀ (u : F) (σ σ' : P.U.toUnifPre.SecGF F q) (hh hh' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))), SecTieF I P F xF q σ hh → (∀ jj, σ'.f jj = resTop _ (scal (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left u) * σ.f jj) → (∀ jj, hh'.f jj = liftFun Xo.univ.t.G _ (toΓ F u) * hh.f jj) → SecTieF I P F xF q σ' hh' := by
  intro E _ _ _ H Dw l Xo c T io y I P F _ _ xF hx q
  have h₁ := (isGen_iff I.w1).1 I.rig1.1
  have h₂ := (isGen_iff _).1 (isoCast_isGen (congrArg RigLB.L P.bundle).symm I.m2.φ I.w2 I.rig2.1)
  have d₁ : IsPullback (snd (ptO Xo xF) Xo.univ.t.G).left (fst (ptO Xo xF) Xo.univ.t.G).left Xo.univ.t.G.hom
      (spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x)) := by
    rw [← hx]
    exact (IsPullback.of_hasPullback xF Xo.univ.t.G.hom).flip
  have d₂ : IsPullback (UnifPre.gFK (R := T.V) (G := I.G.G) F)
      (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left I.G.G.hom
      (spMap (algebraMap T.Fr F) ≫ spMap (algebraMap T.V T.Fr)) :=
    (IsPullback.of_hasPullback (jFK (R := T.V) F) (pullback.snd I.G.G.hom (jK T.V))).flip.paste_horiz
      (IsPullback.of_hasPullback I.G.G.hom (jK T.V))
  have key : ∀ σ hh, SecTieF I P F xF q σ hh ↔ Comparison₂ I.w1 (isoCast (congrArg RigLB.L P.bundle).symm I.m2.φ I.w2)
      (snd (ptO Xo xF) Xo.univ.t.G).left (UnifPre.gFK (R := T.V) (G := I.G.G) F) (fst (ptO Xo xF) Xo.univ.t.G).left
      (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left (spMap (algebraMap T.Fr F)) I.t'.G.hom q σ hh :=
    fun σ hh => ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  simp only [key]
  refine ⟨fun σ => ?_, fun hh => ?_, fun u σ σ' hh hh' h a b => ?_⟩
  · exact existsUnique_tie h₁ h₂ I.t'.PP.isLB Xo.univ.t.PP.isLB P.U.LG.isLB I.m1.cart.1 I.m2.cart.1 d₁.w d₂ q σ
  · obtain ⟨σ, a, b⟩ := existsUnique_tie h₂ h₁ I.t'.PP.isLB P.U.LG.isLB Xo.univ.t.PP.isLB I.m2.cart.1 I.m1.cart.1 d₂.w d₁ q hh
    exact ⟨σ, a.symm, fun σ' h => b σ' (Comparison₂.symm h)⟩
  · exact Comparison₂.smul h (toΓ F u) a b

end GlobalTheory.SecTie
