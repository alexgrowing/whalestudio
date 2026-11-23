import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeightGen

abbrev GermFn (Y : Scheme.{0}) := ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z), (Z.presheaf.stalk z)ˣ

section

variable {P G B : Scheme.{0}} (q : G ⟶ B) (a p : P ⟶ G)

def HasGen (N : LB B) (c : GermFn P) : Prop :=
  ∃ s : ∀ j, Γ(G, q ⁻¹ᵁ N.U j)ˣ,
    (∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z) (j j' : N.ι), q (r z) ∈ N.U j → q (r z) ∈ N.U j' →
      gm r z _ (s j') = gm (r ≫ q) z _ (N.g j j') * gm r z _ (s j)) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) (j : N.ι), q (p (r z)) ∈ N.U j →
      gm (r ≫ a) z _ (s j) = c Z r z * gm (r ≫ p) z _ (s j)

variable {q a p}

theorem pt_eq (h : a ≫ q = p ≫ q) (x : P) : q (a x) = q (p x) := congrArg (fun g => g x) h

theorem HasGen.of_local (h : a ≫ q = p ≫ q) {N : LB B} {c : GermFn P} {A : Type} (W : A → B.Opens)
    (hW : ∀ x, ∃ α, x ∈ W α) (F : N.ι → A → GermFn G)
    (rep : ∀ j α, ∃ y : Γ(G, q ⁻¹ᵁ N.U j ⊓ q ⁻¹ᵁ W α)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z),
      q (r z) ∈ N.U j → q (r z) ∈ W α → gm r z _ y = F j α Z r z)
    (tr : ∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z) (j j' : N.ι) (α α' : A), q (r z) ∈ N.U j →
      q (r z) ∈ N.U j' → q (r z) ∈ W α → q (r z) ∈ W α' →
      F j' α' Z r z = gm (r ≫ q) z _ (N.g j j') * F j α Z r z)
    (wt : ∀ (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) (j : N.ι) (α : A), q (p (r z)) ∈ N.U j →
      q (p (r z)) ∈ W α → F j α Z (r ≫ a) z = c Z r z * F j α Z (r ≫ p) z) :
    HasGen q a p N c := by
  choose y hy using rep
  have glue : ∀ j, ∃ s : Γ(G, q ⁻¹ᵁ N.U j)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z) (α : A),
      q (r z) ∈ N.U j → q (r z) ∈ W α → gm r z _ s = F j α Z r z := by
    intro j
    obtain ⟨s, hs⟩ := glue_unit (q ⁻¹ᵁ N.U j) (fun α => q ⁻¹ᵁ N.U j ⊓ q ⁻¹ᵁ W α)
      (fun _ => inf_le_left) (fun x hx => by
        obtain ⟨α, hα⟩ := hW (q x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨α, hx, hα⟩) (y j) (fun α α' x hx => by
        have e₁ := tr _ (𝟙 G) x j j α α' hx.1.1 hx.1.1 hx.1.2 hx.2.2
        have e₂ := tr _ (𝟙 G) x j j α α hx.1.1 hx.1.1 hx.1.2 hx.1.2
        exact (hy j α _ (𝟙 G) x hx.1.1 hx.1.2).trans ((e₂.trans e₁.symm).trans
          (hy j α' _ (𝟙 G) x hx.1.1 hx.2.2).symm))
    refine ⟨s, fun Z r z α h₁ h₂ => ?_⟩
    have hm : r z ∈ q ⁻¹ᵁ N.U j ⊓ q ⁻¹ᵁ W α := ⟨h₁, h₂⟩
    exact (gm_res r z inf_le_left hm s).symm.trans ((congrArg (gm r z _) (hs α)).trans
      (hy j α Z r z h₁ h₂))
  choose s hs using glue
  refine ⟨s, fun Z r z j j' h₁ h₂ => ?_, fun Z r z j h₁ => ?_⟩
  · obtain ⟨α, hα⟩ := hW (q (r z))
    rw [hs j Z r z α h₁ hα, hs j' Z r z α h₂ hα]
    exact tr Z r z j j' α α h₁ h₂ hα hα
  · obtain ⟨α, hα⟩ := hW (q (p (r z)))
    rw [hs j Z (r ≫ p) z α h₁ hα, hs j Z (r ≫ a) z α ((pt_eq h (r z)).symm ▸ h₁ : q (a (r z)) ∈ _)
      ((pt_eq h (r z)).symm ▸ hα : q (a (r z)) ∈ _)]
    exact wt Z r z j α h₁ hα

theorem gm_gen {N : LB B} {t : LB.Gen N} (ht : t.IsGen) {Z : Scheme.{0}} (r : Z ⟶ B) (z : Z)
    {j j' : N.ι} (h : r z ∈ N.U j) (h' : r z ∈ N.U j') :
    gm r z _ (t.s j) = gm r z _ (N.g j j') * gm r z _ (t.s j') := by
  have hm : r z ∈ N.U j ⊓ N.U j' := ⟨h, h'⟩
  exact (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _) (ht j j')).trans ((map_mul _ _ _).trans
    (congrArg _ (gm_res r z _ hm _))))

theorem gm_iso {L M : LB B} {w : LB.Iso L M} (hw : w.IsGen) {Z : Scheme.{0}} (r : Z ⟶ B) (z : Z)
    {j j' : M.ι} {k k' : L.ι} (hj : r z ∈ M.U j) (hj' : r z ∈ M.U j') (hk : r z ∈ L.U k)
    (hk' : r z ∈ L.U k') :
    gm r z (M.U j ⊓ L.U k) (w.s (j, k)) = gm r z _ (M.g j j') * (gm r z _ (L.g k k'))⁻¹ *
      gm r z (M.U j' ⊓ L.U k') (w.s (j', k')) := by
  have := gm_gen hw r z (j := (j, k)) (j' := (j', k')) ⟨hj, hk⟩ ⟨hj', hk'⟩
  exact this.trans (congrArg (· * _) (gm_div L M r z (j, k) (j', k') ⟨⟨hj, hk⟩, hj', hk'⟩))

theorem HasGen.of_gen (h : a ≫ q = p ≫ q) {N : LB B} (t : LB.Gen N) (ht : t.IsGen) :
    HasGen q a p N (fun _ _ _ => 1) := by
  refine ⟨fun j => (pullU q _ (t.s j))⁻¹, fun Z r z j j' h₁ h₂ => ?_, fun Z r z j h₁ => ?_⟩
  · rw [map_inv, map_inv, gm_pull r q z _ h₁, gm_pull r q z _ h₂, gm_gen ht (r ≫ q) z h₁ h₂,
      mul_inv, mul_inv_cancel_left]
  · rw [map_inv, map_inv, gm_pull (r ≫ p) q z _ h₁,
      gm_pull (r ≫ a) q z _ ((pt_eq h (r z)).symm ▸ h₁ : q (a (r z)) ∈ _), _root_.one_mul,
      Category.assoc, Category.assoc, h]

theorem HasGen.div (h : a ≫ q = p ≫ q) {L M : LB B} {c c' : GermFn P} (hM : HasGen q a p M c)
    (hL : HasGen q a p L c') :
    HasGen q a p (LB.div M L) (fun Z r z => c Z r z * (c' Z r z)⁻¹) := by
  obtain ⟨s, s₁, s₂⟩ := hM
  obtain ⟨t, t₁, t₂⟩ := hL
  obtain ⟨u, hu⟩ : ∃ u : ∀ j : M.ι × L.ι, Γ(G, q ⁻¹ᵁ (M.U j.1 ⊓ L.U j.2))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z) j, q (r z) ∈ M.U j.1 ⊓ L.U j.2 →
        gm r z _ (u j) = gm r z _ (s j.1) * (gm r z _ (t j.2))⁻¹ :=
    ⟨fun j => res (q.preimage_mono inf_le_left) (s j.1) * (res (q.preimage_mono inf_le_right) (t j.2))⁻¹,
      fun Z r z j hj => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hj _)
        ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z _ hj _))))⟩
  refine ⟨u, fun Z r z j j' h₁ h₂ => ?_, fun Z r z j h₁ => ?_⟩
  · refine (hu Z r z j' h₂).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (gm_div L M (r ≫ q) z j j' ⟨h₁, h₂⟩) (hu Z r z j h₁)).symm)
    rw [s₁ Z r z _ _ h₁.1 h₂.1, t₁ Z r z _ _ h₁.2 h₂.2, mul_inv, _root_.mul_mul_mul_comm]
  · refine (hu Z (r ≫ a) z j ((pt_eq h (r z)).symm ▸ h₁ : q (a (r z)) ∈ _)).trans
      (Eq.trans ?_ (congrArg _ (hu Z (r ≫ p) z j h₁)).symm)
    rw [s₂ Z r z _ h₁.1, t₂ Z r z _ h₁.2, mul_inv, _root_.mul_mul_mul_comm]

theorem HasGen.iso (h : a ≫ q = p ≫ q) {L M : LB B} {c : GermFn P} (hL : HasGen q a p L c)
    (cov : ∀ x, ∃ k, x ∈ L.U k) (w : LB.Iso L M) (hw : w.IsGen) : HasGen q a p M c := by
  obtain ⟨s, s₁, s₂⟩ := hL
  refine HasGen.of_local h L.U cov
    (fun j k Z r z => gm r z _ (s k) * (gm (r ≫ q) z (M.U j ⊓ L.U k) (w.s (j, k)))⁻¹)
    (fun j k => ⟨res (V := q ⁻¹ᵁ M.U j ⊓ q ⁻¹ᵁ L.U k) inf_le_right (s k) *
      (res (U := q ⁻¹ᵁ (M.U j ⊓ L.U k)) (le_inf inf_le_left inf_le_right)
        (pullU q (M.U j ⊓ L.U k) (w.s (j, k))))⁻¹, fun Z r z h₁ h₂ => ?_⟩)
    (fun Z r z j j' k k' h₁ h₂ h₃ h₄ => ?_) (fun Z r z j k h₁ h₂ => ?_)
  · have hm : r z ∈ q ⁻¹ᵁ M.U j ⊓ q ⁻¹ᵁ L.U k := ⟨h₁, h₂⟩
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _)
      ((map_inv _ _).trans (congrArg (·⁻¹)
        ((gm_res r z _ hm _).trans (gm_pull r q z (M.U j ⊓ L.U k) hm _)))))
  · rw [gm_iso hw (r ≫ q) z h₁ h₂ h₃ h₄, s₁ Z r z k k' h₃ h₄]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · rw [s₂ Z r z k h₂, Category.assoc, Category.assoc, h, _root_.mul_assoc]

theorem HasGen.iso' (h : a ≫ q = p ≫ q) {L M : LB B} {c : GermFn P} (hM : HasGen q a p M c)
    (cov : ∀ x, ∃ k, x ∈ M.U k) (w : LB.Iso L M) (hw : w.IsGen) : HasGen q a p L c := by
  obtain ⟨s, s₁, s₂⟩ := hM
  refine HasGen.of_local h M.U cov
    (fun k j Z r z => gm r z _ (s j) * gm (r ≫ q) z (M.U j ⊓ L.U k) (w.s (j, k)))
    (fun k j => ⟨res (V := q ⁻¹ᵁ L.U k ⊓ q ⁻¹ᵁ M.U j) inf_le_right (s j) *
      res (U := q ⁻¹ᵁ (M.U j ⊓ L.U k)) (le_inf inf_le_right inf_le_left)
      (pullU q (M.U j ⊓ L.U k) (w.s (j, k))), fun Z r z h₁ h₂ => ?_⟩)
    (fun Z r z k k' j j' h₁ h₂ h₃ h₄ => ?_) (fun Z r z j k h₁ h₂ => ?_)
  · have hm : r z ∈ q ⁻¹ᵁ L.U k ⊓ q ⁻¹ᵁ M.U j := ⟨h₁, h₂⟩
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _)
      ((gm_res r z _ hm _).trans (gm_pull r q z (M.U j ⊓ L.U k) ⟨h₂, h₁⟩ _)))
  · rw [gm_iso hw (r ≫ q) z h₃ h₄ h₁ h₂, s₁ Z r z j j' h₃ h₄]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · rw [s₂ Z r z k h₂, Category.assoc, Category.assoc, h, _root_.mul_assoc]

theorem HasGen.exists_gen {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (B ⟶ X)} {ε : K → ℤ} {c : GermFn P} (h : a ≫ q = p ≫ q)
    (H : HasGen q a p (LB.LinComb L φ ε) c) (φ' : K → (G ⟶ X)) (ε' : K → ℤ)
    (hφ : ∀ k, φ' k = q ≫ φ k) (hε : ∀ k, ε' k = -ε k) (hL : L.IsLB) :
    ∃ t : LB.Gen (LB.LinComb L φ' ε'), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) (J),
      Good L z J → val t (r ≫ a) z J = c Z r z * val t (r ≫ p) z J := by
  obtain rfl : φ' = fun k => q ≫ φ k := funext hφ
  obtain rfl : ε' = fun k => -ε k := funext hε
  obtain ⟨s, s₁, s₂⟩ := H
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => q ≫ φ k) j ≤ q ⁻¹ᵁ LB.wchart L φ j :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  refine ⟨⟨fun j => res (le j) (s j)⟩, fun j j' => unit_ext fun y hy => ?_, fun Z r z J hJ => ?_⟩
  · refine ((gm_res _ y _ hy _).trans (gm_res (𝟙 G) y (le j) hy.1 _)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 G) y j j' hy.1 hy.2)
        ((gm_res _ y _ hy _).trans (gm_res (𝟙 G) y (le j') hy.2 _)))).symm)
    have e := (s₁ _ (𝟙 G) y j j' (le j hy.1) (le j' hy.2)).trans (congrArg (· * _)
      (gm_linComb L φ ε (𝟙 G ≫ q) y j j' (le j hy.1) (le j' hy.2)))
    refine (inv_mul_cancel_left _ _).symm.trans (congrArg₂ (· * ·) ?_ e.symm)
    refine (DVR.prod_neg _ _ ?_).symm
    simp only [Category.assoc]
  · have m := hJ.mem (fun k => q ≫ φ k) (r ≫ p)
    have m' := hJ.mem (fun k => q ≫ φ k) (r ≫ a)
    have e : ∀ k, J ((r ≫ a) ≫ q ≫ φ k) = J ((r ≫ p) ≫ q ≫ φ k) := fun k => by
      rw [Category.assoc, Category.assoc, reassoc_of% h]
    rw [funext e] at m'
    rw [val_of _ (r ≫ a) z J _ e]
    exact (gm_res _ z (le _) m' _).trans ((s₂ Z r z _ (le _ m)).trans
      (congrArg _ (gm_res _ z (le _) m _).symm))

end

theorem gm_res_pull_top {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (f : Y ⟶ X) {V : Y.Opens}
    (hz : r z ∈ V) (h : V ≤ f ⁻¹ᵁ ⊤) (c : Γ(X, ⊤)ˣ) :
    gm r z V (res h (pullU f ⊤ c)) = gm (r ≫ f) z ⊤ c :=
  (gm_res r z h hz _).trans (gm_pull r f z ⊤ trivial c)

section Datum

variable {S : Scheme.{0}}

theorem charUnit_add (X : Type) [AddCommGroup X] (χ χ' : X) :
    charUnit S X (χ + χ') = charUnit S X χ * charUnit S X χ' := by
  apply Units.ext
  rw [Units.val_mul, SplitTorus.charUnit_val, SplitTorus.charUnit_val, SplitTorus.charUnit_val]
  exact SplitTorus.val_add (𝟙 _) χ χ'

noncomputable def wt (X : Type) [AddCommGroup X] (G : Over S) (χ : X) :
    GermFn (splitTorus S X ⊗ G).left :=
  fun _ r z => gm (r ≫ (fst (splitTorus S X) G).left) z ⊤ (charUnit S X χ)

theorem wt_add (X : Type) [AddCommGroup X] (G : Over S) (χ χ' : X) (Z : Scheme.{0})
    (r : Z ⟶ (splitTorus S X ⊗ G).left) (z : Z) :
    wt X G (χ + χ') Z r z = wt X G χ Z r z * wt X G χ' Z r z := by
  rw [wt, charUnit_add, map_mul]; rfl

theorem wt_zero (X : Type) [AddCommGroup X] (G : Over S) : wt X G 0 = fun _ _ _ => 1 := by
  funext Z r z
  have := wt_add X G 0 0 Z r z
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

variable {E : SplitExt S} {G : Over S} [GrpObj G] (d : E.GtDatum G)

noncomputable abbrev act : splitTorus S E.X ⊗ G ⟶ G :=
  lift (fst (splitTorus S E.X) G ≫ d.i) (snd (splitTorus S E.X) G) ≫ μ[G]

theorem act_q : act d ≫ d.q = snd _ _ ≫ d.q := by
  have := d.q_hom
  change ((fst (splitTorus S E.X) G ≫ d.i) * snd (splitTorus S E.X) G) ≫ d.q = _
  rw [MonObj.mul_comp, Category.assoc, d.isKernel.w, ← Category.assoc, comp_toUnit]
  exact _root_.one_mul _

theorem act_q_left : (act d).left ≫ d.q.left = (snd (splitTorus S E.X) G).left ≫ d.q.left :=
  congrArg (fun g => g.left) (act_q d)

attribute [local instance] SplitExt.free SplitExt.finite

theorem exists_mem_chart (x : E.B.left) : ∃ j, x ∈ E.chart j := by
  choose j hj using fun k => exists_chart (E.O (E.basis k)).isLB x
  refine ⟨j, ?_⟩
  have : ((E.chart j : E.B.left.Opens) : Set E.B.left) =
      ⋂ k, ((E.O (E.basis k)).L.U (j k) : Set E.B.left) := TopologicalSpace.Opens.coe_iInf _
  exact this.ge (Set.mem_iInter.2 hj)

theorem hasGen_basis (k : Module.Free.ChooseBasisIndex ℤ E.X) :
    HasGen d.q.left (act d).left (snd (splitTorus S E.X) G).left (E.O (E.basis k)).L
      (wt E.X G (E.basis k)) := by
  have hL := (E.O (E.basis k)).isLB
  refine HasGen.of_local (act_q_left d) E.chart exists_mem_chart
    (fun j α Z r z => gm r z _ (d.u α k) * gm (r ≫ d.q.left) z _ ((E.O (E.basis k)).L.g (α k) j))
    (fun j α => ⟨res (V := d.q.left ⁻¹ᵁ (E.O (E.basis k)).L.U j ⊓ d.q.left ⁻¹ᵁ E.chart α)
      inf_le_right (d.u α k) * res (U := d.q.left ⁻¹ᵁ ((E.O (E.basis k)).L.U (α k) ⊓ (E.O (E.basis k)).L.U j))
        (le_inf (inf_le_right.trans (d.q.left.preimage_mono (E.chart_le α k))) inf_le_left)
        (pullU d.q.left _ ((E.O (E.basis k)).L.g (α k) j)), fun Z r z h₁ h₂ => ?_⟩)
    (fun Z r z j j' α α' h₁ h₂ h₃ h₄ => ?_) (fun Z r z j α h₁ h₂ => ?_)
  · have hm : r z ∈ d.q.left ⁻¹ᵁ (E.O (E.basis k)).L.U j ⊓ d.q.left ⁻¹ᵁ E.chart α := ⟨h₁, h₂⟩
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _)
      ((gm_res r z _ hm _).trans (gm_pull r _ z (_ ⊓ _) ⟨E.chart_le α k h₂, h₁⟩ _)))
  · have hm : r z ∈ d.q.left ⁻¹ᵁ (E.chart α ⊓ E.chart α') := ⟨h₃, h₄⟩
    have e := (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _) (d.trans α α' k)).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_pull r _ z _ hm _).trans
        (gm_res (r ≫ d.q.left) z _ hm _)) (gm_res r z _ hm _))))
    have c₁ := gm_cocycle hL (r ≫ d.q.left) z (E.chart_le α k h₃) (E.chart_le α' k h₄) h₂
    have c₂ := gm_cocycle hL (r ≫ d.q.left) z (E.chart_le α k h₃) h₁ h₂
    rw [e, mul_right_comm, c₁, ← c₂]
    ac_rfl
  · have hm : r z ∈ (snd (splitTorus S E.X) G).left ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart α) := h₂
    have e := congrArg (gm r z ((snd (splitTorus S E.X) G).left ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart α)))
      (d.equiv α k)
    rw [map_mul, gm_res r z _ hm,
      gm_pull r (act d).left z (d.q.left ⁻¹ᵁ E.chart α) (d.act_le α hm),
      gm_pull r (snd (splitTorus S E.X) G).left z (d.q.left ⁻¹ᵁ E.chart α) hm] at e
    have e' := e.trans (congrArg (· * _) (gm_res_pull_top r z _ hm _ _))
    rw [e', Category.assoc, Category.assoc, act_q_left, _root_.mul_assoc]
    rfl

theorem hasGen (χ : E.X) :
    HasGen d.q.left (act d).left (snd (splitTorus S E.X) G).left (E.O χ).L (wt E.X G χ) := by
  let Q : E.X → Prop := fun χ =>
    HasGen d.q.left (act d).left (snd (splitTorus S E.X) G).left (E.O χ).L (wt E.X G χ)
  have h0 : Q 0 := by
    obtain ⟨t, ht⟩ := E.zeroTriv
    simp only [Q, wt_zero]
    exact HasGen.of_gen (act_q_left d) t ht
  have hs : ∀ x y, Q (x + y) → Q x → Q y := by
    intro x y h₁ h₂
    obtain ⟨w, hw⟩ := E.addIso x y
    have := (HasGen.div (act_q_left d) h₁ h₂).iso' (act_q_left d) (fun b => by
      obtain ⟨i, hi⟩ := exists_chart (E.O (x + y)).isLB b
      obtain ⟨j, hj⟩ := exists_chart (E.O x).isLB b
      exact ⟨(i, j), hi, hj⟩) w hw
    have e : (fun Z r z => wt E.X G (x + y) Z r z * (wt E.X G x Z r z)⁻¹) = wt E.X G y := by
      funext Z r z
      rw [wt_add, mul_inv_cancel_comm]
    rwa [e] at this
  have hn : ∀ x, Q x → Q (-x) := fun x h => hs x (-x) (by rw [add_neg_cancel]; exact h0) h
  have hχ : χ ∈ AddSubgroup.closure (Set.range E.basis) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, E.basis.span_eq]; trivial
  refine AddSubgroup.closure_induction (p := fun x _ => Q x) ?_ h0 ?_ (fun x _ => hn x) hχ
  · rintro _ ⟨k, rfl⟩
    exact hasGen_basis d k
  · intro x y _ _ hx hy
    exact hs (-x) (x + y) (by rw [neg_add_cancel_left]; exact hy) (hn x hx)

theorem exists_const (hG : GlobalFnsSt) (f : Γ(G.left, ⊤))
    (hf : (act d).left.appTop.hom f = (snd (splitTorus S E.X) G).left.appTop.hom f) :
    ∃ c, G.hom.appTop.hom c = f := by
  have := d.q_affine
  obtain ⟨b, hb⟩ := (invariant_functions_descend S G E.B _ d.q d.i d.q_hom d.i_hom d.q_flat
    d.q_surjective inferInstance d.isKernel ⊤).2.2 f (fun Z t g h₁ h₂ => by
      have e₁ : (t ≫ d.i) * g = lift t g ≫ act d := by
        rw [Hom.mul_def, comp_lift_assoc, lift_fst_assoc, lift_snd]
      have key : ((t ≫ d.i) * g).left.appTop.hom f = g.left.appTop.hom f := by
        rw [e₁, Over.comp_left, FunDescent.comp_appTop_apply, hf, ← FunDescent.comp_appTop_apply,
          ← Over.comp_left, lift_snd]
      rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.app_eq_appLE] at key
      exact key)
  obtain ⟨c, hc⟩ := (hG S E.B E.isAbelian).2 b
  refine ⟨c, ?_⟩
  rw [← Over.w d.q, FunDescent.comp_appTop_apply, hc]
  exact hb

end Datum

theorem gen_unique_of_invariant {X Y P S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type}
    [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (hF : FormEq φ ε φ' ε') (π : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ π = 𝟙 _) (a p : P ⟶ Y)
    (hp : ∀ f : Γ(Y, ⊤), a.appTop.hom f = p.appTop.hom f → ∃ c, π.appTop.hom c = f)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen)
    (hu' : u'.IsGen) (h : ∀ y J, Good M y J → val u e y J = val u' e y J)
    (hw : ∀ y J, Good M y J → val u a y J * (val u' a y J)⁻¹ = val u p y J * (val u' p y J)⁻¹)
    (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (hJ : Good M z J) :
    val u r z J = val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hF U h,
        mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u'))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  have key₀ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ (res le (t.s PEmpty.elim)).val := by
    intro Z r z J hJ
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans (gs_unit r z ⊤ trivial _).symm
  obtain ⟨c, hc⟩ := hp (res le (t.s PEmpty.elim)).val (fn_ext fun y _ => by
    choose I hI using fun χ : P ⟶ X => exists_chart hM (χ y)
    refine (gs_pull (𝟙 P) a y ⊤ trivial _).trans (Eq.trans ?_ (gs_pull (𝟙 P) p y ⊤ trivial _).symm)
    rw [Category.id_comp, Category.id_comp, ← key₀ _ a y I hI, ← key₀ _ p y I hI, hw y I hI])
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs (r ≫ π) z ⊤ c := fun Z r z J hJ =>
    (key₀ Z r z J hJ).trans ((congrArg (gs r z ⊤) hc.symm).trans (gs_pull r π z ⊤ trivial c))
  have a1 : c = 1 := fn_ext fun y _ => by
    choose I hI using fun χ : S₀ ⟶ X => exists_chart hM (χ y)
    have := key _ e y I hI
    rw [h y I hI, mul_inv_cancel, he] at this
    rw [← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
  have := key Z r z J hJ
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

section Coord

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem comp_Oφ {T T' : Over (Spec (CommRingCat.of R))} (h : T' ⟶ T) (p : T ⟶ D.P.A) (χ : D.X)
    (k : Fin 4) : h.left ≫ D.Oφ p χ k = D.Oφ (h ≫ p) χ k := by
  have e0 : h ≫ padd D.P.A p (toUnit T ≫ D.c χ) = padd D.P.A (h ≫ p) (toUnit T' ≫ D.c χ) := by
    simp only [padd]; rw [← Category.assoc, comp_lift, comp_toUnit_assoc]
  have e1 : h ≫ toUnit T ≫ D.c χ = toUnit T' ≫ D.c χ := by simp
  have e3 : h ≫ toUnit T ≫ η[D.P.A] = toUnit T' ≫ η[D.P.A] := by simp
  fin_cases k
  · exact congrArg (fun g => g.left) e0
  · exact congrArg (fun g => g.left) e1
  · rfl
  · exact congrArg (fun g => g.left) e3

theorem prod_Oφ {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type}
    [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k, h (D.Oφ p χ k) ^ Oinvε k = (h (p * (toUnit T ≫ D.c χ)).left)⁻¹ *
      h (toUnit T ≫ D.c χ).left * h p.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  change h (p * (toUnit T ≫ D.c χ)).left ^ (-1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (1 : ℤ) *
    h p.left ^ (1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem exists_normalised {T S₀ P : Over (Spec (CommRingCat.of R))} (q : T ⟶ D.P.A) (π : T ⟶ S₀)
    (e : S₀ ⟶ T) (he : e ≫ π = 𝟙 _) (heq : e ≫ q = 1) (a p : P ⟶ T) (hq : a ≫ q = p ≫ q)
    (hπ : a ≫ π = p ≫ π)
    (hp : ∀ f : Γ(T.left, ⊤), a.left.appTop.hom f = p.left.appTop.hom f →
      ∃ c, π.left.appTop.hom c = f)
    (c : D.X → GermFn P.left)
    (hc : ∀ χ χ' Z r z, c (χ + χ') Z r z = c χ Z r z * c χ' Z r z)
    (H : ∀ χ, ∃ t : LB.Gen (LB.LinComb D.P.L (D.Oφ q χ) Oinvε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ P.left) (z : Z) (J), Good D.P.L z J →
        val t (r ≫ a.left) z J = c χ Z r z * val t (r ≫ p.left) z J) :
    ∃ t : ∀ χ, LB.Gen (LB.LinComb D.P.L (D.Oφ q χ) Oinvε), (∀ χ, (t χ).IsGen) ∧
      (∀ χ χ', LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (t (χ + χ'))
          (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
            (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') q)).left))
        (LB.mulGen D.P.L _ _ _ _ (t χ) (t χ'))) ∧
      (∀ χ y J, Good D.P.L y J → val (t χ) e.left y J = 1) ∧
      ∀ χ (Z : Scheme.{0}) (r : Z ⟶ P.left) (z : Z) (J), Good D.P.L z J →
        val (t χ) (r ≫ a.left) z J = c χ Z r z * val (t χ) (r ≫ p.left) z J := by
  choose t₀ g₀ w₀ using H
  have hL := D.P.isLB
  have norm : ∀ χ, ∃ t : LB.Gen (LB.LinComb D.P.L (D.Oφ q χ) Oinvε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val t r z J = val (t₀ χ) r z J * (val (t₀ χ) (r ≫ (π ≫ e).left) z J)⁻¹ := by
    intro χ
    obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := D.Oφ q χ) (ε' := Oinvε) (fun U _ h => by
        have z : (π ≫ e) ≫ q = 1 := by rw [Category.assoc, heq, MonObj.comp_one]
        have := prod_Oφ D ((π ≫ e) ≫ q) χ h
        refine Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
          (c := ∏ k, h (D.Oφ q χ k) ^ Oinvε k) rfl (DVR.prod_neg _ _
            ((Finset.prod_congr rfl fun k _ =>
              congrArg (fun g => h g ^ Oinvε k) (comp_Oφ D (π ≫ e) q χ k)).trans this))) ?_
        rw [z, _root_.one_mul]
        simp)
      (LB.mulGen D.P.L _ _ _ _ (t₀ χ) (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ (t₀ χ) (π ≫ e).left)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (g₀ χ) (DVR.invGen_isGen _ _ _ _
        (DVR.pullGen_isGen _ _ _ _ (g₀ χ) _)))
    exact ⟨t, ht, fun Z r z J hJ => by rw [hv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ]⟩
  choose t g v using norm
  have unit : ∀ χ y J, Good D.P.L y J → val (t χ) e.left y J = 1 := fun χ y J hJ => by
    rw [v χ _ _ y J hJ, ← Over.comp_left, reassoc_of% he, mul_inv_cancel]
  have wgt : ∀ χ (Z : Scheme.{0}) (r : Z ⟶ P.left) (z : Z) (J), Good D.P.L z J →
      val (t χ) (r ≫ a.left) z J = c χ Z r z * val (t χ) (r ≫ p.left) z J := fun χ Z r z J hJ => by
    have k : a.left ≫ (π ≫ e).left = p.left ≫ (π ≫ e).left :=
      congrArg (fun g => g.left) (show a ≫ π ≫ e = p ≫ π ≫ e by rw [reassoc_of% hπ])
    rw [v χ _ _ z J hJ, v χ _ _ z J hJ, w₀ χ Z r z J hJ, Category.assoc, Category.assoc, k, _root_.mul_assoc]
  refine ⟨t, g, fun χ χ' => corr_of_val hL fun y J hJ => ?_, unit, wgt⟩
  have ev : ∀ {T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) {z : T'.left} {J},
      Good D.P.L z J → val (LB.mulGen D.P.L _ _ _ _ (t (χ + χ'))
          (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
            (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') q)).left)) ρ.left z J =
        val (t (χ + χ')) ρ.left z J *
          cubV D.cub z J (toUnit _ ≫ D.c χ) (toUnit _ ≫ D.c χ') (ρ ≫ q) := fun ρ z J hJ => by
    refine (val_mul hJ _ _ _).trans (congrArg _ ((val_cub D.cub ρ hJ _ _ _).trans ?_))
    rw [comp_toUnit_assoc, comp_toUnit_assoc]
  refine gen_unique_of_invariant hL (u := LB.mulGen D.P.L _ _ _ _ (t (χ + χ'))
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
        (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') q)).left)) (fun U _ h => ?_) π.left e.left
    (congrArg (fun g => g.left) he) a.left p.left hp
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (g _) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (g _) (g _)) (fun y J hJ => ?_) (fun y J hJ => ?_) _ _ y J hJ
  · refine (DVR.prod_sum₂ (K := Fin 4) (K' := thK) (U := U) _ (prod_Oφ D q (χ + χ') h)
      (prod_cub _ _ _ h)).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
        (prod_Oφ D q χ h) (prod_Oφ D q χ' h)).symm)
    have e₁ : toUnit T ≫ D.c (χ + χ') = (toUnit T ≫ D.c χ) * (toUnit T ≫ D.c χ') := by
      rw [D.c_add]; exact MonObj.comp_mul _ _ _
    rw [e₁, mul_comm q, mul_comm q, mul_comm q]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · rw [ev e hJ, val_mul hJ, unit _ y J hJ, unit _ y J hJ, unit _ y J hJ, heq,
      (isCub_cubV D.cub hJ).face₃]
  · have w := fun χ => wgt χ _ (𝟙 _) y J hJ
    simp only [Category.id_comp] at w
    rw [ev a hJ, ev p hJ, val_mul hJ, val_mul hJ, w, w, w, hc, hq]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

end Coord

theorem unit_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A] :
    η[(Over.pullback f).obj A].left ≫ pullback.fst A.hom f = f ≫ η[A].left := by
  have h : η[(Over.pullback f).obj A] =
      Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map η[A] := rfl
  have h₁ : ((Over.pullback f).map η[A]).left ≫ pullback.fst A.hom f =
      pullback.fst (𝟙_ (Over S)).hom f ≫ η[A].left := pullback.lift_fst _ _ _
  rw [h, Over.comp_left, Category.assoc, h₁, ← Category.assoc]
  congr 1
  have h₂ : pullback.fst (𝟙_ (Over S)).hom f = pullback.snd (𝟙_ (Over S)).hom f ≫ f :=
    (Category.comp_id _).symm.trans pullback.condition
  rw [h₂, ← Category.assoc]
  exact (congrArg (· ≫ f) (Over.w (Functor.LaxMonoidal.ε (Over.pullback f)))).trans
    (Category.id_comp _)

theorem val_charGen {S Y Z : Scheme.{0}} (X : Type) [AddCommGroup X] (G : Over S) (L : LB Y) (χ : X)
    (r : Z ⟶ (splitTorus S X ⊗ G).left) (z : Z) (J : (Z ⟶ Y) → L.ι) :
    val (charGen X G L χ) r z J = gm (r ≫ (fst (splitTorus S X) G).left) z ⊤ (charUnit S X χ) :=
  gm_res_pull_top r z (fst (splitTorus S X) G).left
    (V := LB.wchart L (PEmpty.elim : PEmpty → (_ ⟶ Y)) fun k => J (r ≫ k.elim))
    (Set.mem_iInter.2 fun k => k.elim) (fun _ _ => trivial) _

end GlobalTheory.WeightGen

namespace GlobalTheory

open WeightGen

theorem nonempty_gtCoord_of_isGt : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : E.B ≅ thickObj R I e D.P.A) (xe : D.X ≃+ E.X), IsMonHom β.hom → (∀ χ : D.X, ∃ w : LB.Iso (E.O (xe χ)).L (LB.LinComb D.P.L (fun k => ((Over.map (thick R I e)).map β.hom ≫ D.prBe I e).left ≫ D.Oφ (𝟙 _) χ k) Oε), w.IsGen) → E.IsGt (thickObj R I e G) → Nonempty (GtCoord I D e G) := by
  intro hG R _ _ I D e G _ _ E β xe hβ hw ⟨d⟩
  have hL := D.P.isLB
  have := d.q_hom
  have := d.i_hom
  have := d.q_flat
  have := d.q_surjective
  have := d.q_affine
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  let F := Over.map (thick R I e)
  let κ : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ≅ splitTorus _ E.X :=
    { hom := SplitTorus.torusMap _ xe.symm.toAddMonoidHom
      inv := SplitTorus.torusMap _ xe.toAddMonoidHom
      hom_inv_id := by
        rw [← SplitTorus.torusMap_comp, ← SplitTorus.torusMap_id]
        congr 1; ext; simp
      inv_hom_id := by
        rw [← SplitTorus.torusMap_comp, ← SplitTorus.torusMap_id]
        congr 1; ext; simp }
  have : IsMonHom κ.hom := SplitTorus.isMonHom_torusMap _
  have hκ : ∀ χ, pullU κ.hom.left ⊤ (charUnit _ E.X (xe χ)) = charUnit _ D.X χ := fun χ => by
    apply Units.ext
    rw [SplitTorus.charUnit_val]
    refine Eq.trans ?_ ((SplitTorus.torusMap_appTop_chi xe.symm.toAddMonoidHom (xe χ)).trans
      (congrArg _ (xe.symm_apply_apply χ)))
    rw [← SplitTorus.charUnit_val]
    rfl
  have unit_q : F.map η[thickObj R I e G] ≫ F.map (d.q ≫ β.hom) ≫ D.prBe I e = 1 := by
    rw [← F.map_comp_assoc, IsMonHom.one_hom]
    exact Over.OverMorphism.ext (unit_fst (thick R I e) D.P.A)
  obtain ⟨t, g, m, u, w⟩ := exists_normalised D (F.map (d.q ≫ β.hom) ≫ D.prBe I e)
    (F.map (toUnit _)) (F.map η[thickObj R I e G])
    (by rw [← F.map_comp, comp_toUnit, toUnit_unit, F.map_id]) unit_q
    (F.map (act d)) (F.map (snd _ _))
    (by rw [← F.map_comp_assoc, ← F.map_comp_assoc, ← Category.assoc (act d), act_q d,
      Category.assoc])
    (by rw [← F.map_comp, ← F.map_comp, comp_toUnit, comp_toUnit])
    (exists_const d hG) (fun χ => wt E.X (thickObj R I e G) (xe χ))
    (fun χ χ' Z r z => by rw [map_add]; exact wt_add _ _ _ _ Z r z)
    (fun χ => by
      obtain ⟨w, hw⟩ := hw χ
      refine ((hasGen d (xe χ)).iso (act_q_left d) (exists_chart (E.O (xe χ)).isLB) w hw).exists_gen
        (act_q_left d) _ _ (fun k => ?_) (fun k => by fin_cases k <;> rfl) hL
      have := comp_Oφ D (F.map (d.q ≫ β.hom) ≫ D.prBe I e) (𝟙 _) χ k
      rw [Category.comp_id] at this
      refine this.symm.trans ?_
      rw [F.map_comp, Category.assoc, Over.comp_left, Category.assoc]
      rfl)
  refine ⟨{ q := d.q ≫ β.hom
            q_hom := inferInstance
            q_flat := by rw [Over.comp_left]; infer_instance
            q_surj := by rw [Over.comp_left]; infer_instance
            q_affine := by rw [Over.comp_left]; infer_instance
            i := κ.hom ≫ d.i
            i_hom := inferInstance
            isKernel := d.isKernel.of_iso κ.symm (Iso.refl _) (Iso.refl _) β (by simp)
              (toUnit_unique _ _) (by simp) (by simp)
            t := t
            t_gen := g
            t_mul := m
            t_unit := fun χ => corr_of_val hL fun y J hJ => ?_
            t_weight := fun χ => corr_of_val hL fun y J hJ => ?_ }⟩
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [Category.id_comp]
    exact u χ y J hJ
  · have k := w χ _ (κ.hom ▷ thickObj R I e G).left y J hJ
    have k₁ : κ.hom ▷ thickObj R I e G ≫ act d =
        lift (fst _ (thickObj R I e G) ≫ κ.hom ≫ d.i) (snd _ _) ≫ μ[thickObj R I e G] := by
      rw [comp_lift_assoc, whiskerRight_fst_assoc, whiskerRight_snd]
    have k₂ : κ.hom ▷ thickObj R I e G ≫ snd _ _ = snd _ _ := whiskerRight_snd _ _
    have k₃ : (κ.hom ▷ thickObj R I e G).left ≫ (fst _ _ : _ ⟶ splitTorus _ E.X).left =
        (fst _ (thickObj R I e G)).left ≫ κ.hom.left :=
      congrArg (fun g => g.left) (whiskerRight_fst κ.hom (thickObj R I e G))
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_mul hJ _ _ _).trans
      (congrArg _ (val_pull hJ _ _ _))).symm)
    rw [Category.id_comp, Category.id_comp]
    have l₁ : (κ.hom ▷ thickObj R I e G).left ≫ (F.map (act d)).left =
        (lift (fst _ (thickObj R I e G) ≫ κ.hom ≫ d.i) (snd _ _) ≫ μ[thickObj R I e G]).left :=
      congrArg (fun g => g.left) k₁
    have l₂ : (κ.hom ▷ thickObj R I e G).left ≫ (F.map (snd _ _)).left =
        (snd _ (thickObj R I e G)).left := congrArg (fun g => g.left) k₂
    have l₃ : wt E.X (thickObj R I e G) (xe χ) _ (κ.hom ▷ thickObj R I e G).left y =
        val (charGen D.X (thickObj R I e G) D.P.L χ) (𝟙 _) y J := by
      rw [val_charGen, Category.id_comp, ← hκ]
      refine Eq.trans ?_ (gm_pull (fst _ (thickObj R I e G)).left κ.hom.left y ⊤ trivial _).symm
      rw [← k₃]
      rfl
    exact (congrArg (fun g => val (t χ) g y J) l₁).symm.trans (k.trans
      (congrArg₂ (· * ·) l₃ (congrArg (fun g => val (t χ) g y J) l₂)))

end GlobalTheory
