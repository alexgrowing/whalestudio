import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueCharacterOfMul
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.IsoDesc

section Schemes
variable {X Y Z : Scheme.{0}}

def kap (σ : Z ⟶ Y) (z : Z) : (Y.presheaf.stalk (σ z))ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map (σ.stalkMap z).hom.toMonoidHom

theorem kap_gm (σ : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (a : Γ(X, U)ˣ) :
    kap σ z (gm r (σ z) U a) = gm (σ ≫ r) z U a := by
  by_cases h : r (σ z) ∈ U
  · apply Units.ext
    rw [gm_val (σ ≫ r) z U h]
    show (σ.stalkMap z).hom (gm r (σ z) U a).val = _
    rw [gm_val r (σ z) U h]
    exact Scheme.Hom.germ_stalkMap_apply σ (r ⁻¹ᵁ U) z h _
  · have h' : ¬ (σ ≫ r) z ∈ U := h
    rw [gm, gm, dif_neg h, dif_neg h']
    exact map_one _

theorem kap_injective (σ : Z ⟶ Y) [Flat σ] (z : Z) : Function.Injective (kap σ z) := by
  let _ := (σ.stalkMap z).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (σ z)) (Z.presheaf.stalk z) := Flat.stalkMap σ z
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (σ z)) (Z.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (σ.stalkMap z).hom)
  have : Module.FaithfullyFlat (Y.presheaf.stalk (σ z)) (Z.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Units.map_injective (FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (σ z)) (Z.presheaf.stalk z))

theorem exists_good_epi {L : LB X} (hL : L.IsLB) (σ : Z ⟶ Y) [Epi σ] (z : Z) {J} (hJ : Good L (σ z) J) :
    ∃ J', Good L z J' ∧ ∀ ψ, J' (σ ≫ ψ) = J ψ :=
  exists_good L hL z (fun ψ : Y ⟶ X => σ ≫ ψ) J (fun _ _ e => congrArg J ((cancel_epi σ).1 e)) hJ

theorem kap_val {L : LB X} {K : Type} [Fintype K] {W : Scheme.{0}} {φ : K → (W ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (σ : Z ⟶ Y) (z : Z) {J J'} (h : ∀ ψ, J' (σ ≫ ψ) = J ψ) (r : Y ⟶ W) :
    kap σ z (val t r (σ z) J) = val t (σ ≫ r) z J' := by
  rw [val_of t (σ ≫ r) z J' (fun k => J (r ≫ φ k)) (fun k => by rw [Category.assoc, h])]
  exact kap_gm _ _ _ _ _

theorem kap_gw {X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (σ : Z ⟶ Y)
    (z : Z) (r : Y ⟶ X') (j k) : kap σ z (gw w r (σ z) j k) = gw w (σ ≫ r) z j k := kap_gm _ _ _ _ _

theorem appTop_eq_iff (a b : Γ(Z, ⊤)ˣ) : a.val = b.val ↔ ∀ z, gm (𝟙 Z) z ⊤ a = gm (𝟙 Z) z ⊤ b :=
  ⟨fun h z => congrArg _ (Units.ext h), fun h => congrArg Units.val (unit_ext fun z _ => h z)⟩

theorem appLE_eq_of_gm (r r' : Z ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (h' : ⊤ ≤ r' ⁻¹ᵁ U) (a : Γ(Y, U)ˣ)
    (e : ∀ z, gm r z U a = gm r' z U a) : (r.appLE U ⊤ h).hom a.val = (r'.appLE U ⊤ h').hom a.val := by
  have k : ∀ (r : Z ⟶ Y) (h : ⊤ ≤ r ⁻¹ᵁ U) (z : Z), gm (𝟙 Z) z ⊤ (res h (pullU r U a)) = gm r z U a := fun r h z => by
    rw [gm_res (𝟙 Z) z h trivial, gm_pull (𝟙 Z) r z U (h trivial), Category.id_comp]
  exact (appTop_eq_iff (res h (pullU r U a)) (res h' (pullU r' U a))).2 fun z => by rw [k, k, e]

variable {G B' B : Scheme.{0}} {L : LB G} {M' : LB B'} {M : LB B} {q : G ⟶ B'} {β : B' ⟶ B}

abbrev dom (M' : LB B') (M : LB B) (β : B' ⟶ B) (j : M.ι) (i : M'.ι) : B'.Opens :=
  (M.pull β).U (fun _ => j) ⊓ M'.U i

def IsQuot (u : LB.Iso L (M'.pull q)) (w : LB.Iso L (M.pull (q ≫ β)))
    (s : ∀ j i, Γ(G, q ⁻¹ᵁ dom M' M β j i)ˣ) : Prop :=
  ∀ (Y : Scheme.{0}) (f : Y ⟶ G) (y : Y) (j : M.ι) (i : M'.ι) (k : L.ι), β (q (f y)) ∈ M.U j → q (f y) ∈ M'.U i →
    f y ∈ L.U k → gw w f y j k = gm f y _ (s j i) * gw u f y i k

theorem exists_isQuot (hL : L.IsLB) (hM' : M'.IsLB) (hM : M.IsLB) {u : LB.Iso L (M'.pull q)}
    {w : LB.Iso L (M.pull (q ≫ β))} (hu : PGen u) (hw : PGen w) : ∃ s, IsQuot u w s := by
  have glue : ∀ (j : M.ι) (i : M'.ι), ∃ s : Γ(G, q ⁻¹ᵁ dom M' M β j i)ˣ,
      ∀ (Y : Scheme.{0}) (f : Y ⟶ G) (y : Y) (k : L.ι), β (q (f y)) ∈ M.U j → q (f y) ∈ M'.U i → f y ∈ L.U k →
        gm f y _ s = gw w f y j k * (gw u f y i k)⁻¹ := by
    intro j i
    obtain ⟨W, hW⟩ : ∃ W : L.ι → G.Opens, ∀ k x, x ∈ W k ↔ β (q x) ∈ M.U j ∧ q x ∈ M'.U i ∧ x ∈ L.U k :=
      ⟨fun k => q ⁻¹ᵁ (β ⁻¹ᵁ M.U j) ⊓ (q ⁻¹ᵁ M'.U i ⊓ L.U k), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ k, W k ≤ q ⁻¹ᵁ dom M' M β j i := fun k x hx =>
      ⟨mem_pull.2 ((hW k x).1 hx).1, ((hW k x).1 hx).2.1⟩
    have l₁ : ∀ k, W k ≤ (M.pull (q ≫ β)).U (fun _ => j) ⊓ L.U k := fun k x hx =>
      ⟨mem_pull₂.2 ((hW k x).1 hx).1, ((hW k x).1 hx).2.2⟩
    have l₂ : ∀ k, W k ≤ (M'.pull q).U (fun _ => i) ⊓ L.U k := fun k x hx =>
      ⟨mem_pull.2 ((hW k x).1 hx).2.1, ((hW k x).1 hx).2.2⟩
    obtain ⟨a, ha⟩ : ∃ a : ∀ k, Γ(G, W k)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ G) (y : Y) (k : L.ι), f y ∈ W k →
        gm f y (W k) (a k) = gw w f y j k * (gw u f y i k)⁻¹ :=
      ⟨fun k => res (l₁ k) (w.s (fun _ => j, k)) * (res (l₂ k) (u.s (fun _ => i, k)))⁻¹, fun Y f y k hy =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f y (l₁ k) hy _)
          ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res f y (l₂ k) hy _))))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨k, hk⟩ := exists_chart hL x
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (hW k x).2 ⟨mem_pull.1 hx.1, hx.2, hk⟩⟩) a (fun k k' x hx => by
        have h₁ := (hW k x).1 hx.1
        have h₂ := (hW k' x).1 hx.2
        rw [ha _ (𝟙 G) x k hx.1, ha _ (𝟙 G) x k' hx.2, hw _ (𝟙 G) x j j k k' h₁.1 h₁.1 h₁.2.2 h₂.2.2,
          hu _ (𝟙 G) x i i k k' h₁.2.1 h₁.2.1 h₁.2.2 h₂.2.2, gm_self hM (𝟙 G ≫ q ≫ β) x h₁.1,
          gm_self hM' (𝟙 G ≫ q) x h₁.2.1]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
    refine ⟨s, fun Y f y k hj hi hk => ?_⟩
    have hy := (hW k (f y)).2 ⟨hj, hi, hk⟩
    exact (gm_res f y (l₀ k) hy s).symm.trans ((congrArg (gm f y (W k)) (hs k)).trans (ha Y f y k hy))
  choose s hs using glue
  exact ⟨s, fun Y f y j i k hj hi hk => by rw [hs j i Y f y k hj hi hk, inv_mul_cancel_right]⟩

theorem IsQuot.trans (hL : L.IsLB) {u : LB.Iso L (M'.pull q)}
    {w : LB.Iso L (M.pull (q ≫ β))} (hu : PGen u) (hw : PGen w) {s} (hs : IsQuot u w s)
    (f : Y ⟶ G) (y : Y) (j j' : M.ι) (i i' : M'.ι) (hj : β (q (f y)) ∈ M.U j) (hj' : β (q (f y)) ∈ M.U j')
    (hi : q (f y) ∈ M'.U i) (hi' : q (f y) ∈ M'.U i') :
    gm f y _ (s j i) = gm ((f ≫ q) ≫ β) y _ (M.g j j') * (gm (f ≫ q) y _ (M'.g i i'))⁻¹ * gm f y _ (s j' i') := by
  obtain ⟨k, hk⟩ := exists_chart hL (f y)
  have a := hw _ f y j j' k k hj hj' hk hk
  rw [hs _ f y j i k hj hi hk, hs _ f y j' i' k hj' hi' hk, hu _ f y i i' k k hi hi' hk hk, ← Category.assoc] at a
  apply Additive.ofMul.injective
  have a' := congrArg Additive.ofMul a
  simp only [ofMul_mul, ofMul_inv] at a' ⊢
  linear_combination (norm := abel) a'

theorem IsQuot.exists_ratio (hL : L.IsLB) (hM' : M'.IsLB) (hM : M.IsLB) {u : LB.Iso L (M'.pull q)}
    {w : LB.Iso L (M.pull (q ≫ β))} (hu : PGen u) (hw : PGen w) {s} (hs : IsQuot u w s)
    (m p : Y ⟶ G) (e : m ≫ q = p ≫ q) : ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : M.ι) (i : M'.ι),
      q (p (r z)) ∈ dom M' M β j i → gm (r ≫ m) z _ (s j i) = gm r z ⊤ a * gm (r ≫ p) z _ (s j i) := by
  have ept : ∀ y, q (m y) = q (p y) := fun y => congrArg (fun g => g y) e
  let W : M.ι × M'.ι → Y.Opens := fun c => p ⁻¹ᵁ q ⁻¹ᵁ dom M' M β c.1 c.2
  have l : ∀ c, W c ≤ m ⁻¹ᵁ q ⁻¹ᵁ dom M' M β c.1 c.2 := fun c y hy => by
    show q (m y) ∈ dom M' M β c.1 c.2
    rw [ept]; exact hy
  obtain ⟨b, hb⟩ : ∃ b : ∀ c, Γ(Y, W c)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) c, r z ∈ W c →
      gm r z (W c) (b c) = gm (r ≫ m) z _ (s c.1 c.2) * (gm (r ≫ p) z _ (s c.1 c.2))⁻¹ :=
    ⟨fun c => res (l c) (pullU m _ (s c.1 c.2)) * (pullU p _ (s c.1 c.2))⁻¹, fun Z r z c hz =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z (l c) hz _).trans (gm_pull r m z _ (l c hz) _))
        ((map_inv _ _).trans (congrArg (·⁻¹) (gm_pull r p z _ hz _))))⟩
  obtain ⟨a, ha⟩ := glue_unit ⊤ W (fun _ => le_top) (fun y _ => by
      obtain ⟨j, hj⟩ := exists_chart hM (β (q (p y)))
      obtain ⟨i, hi⟩ := exists_chart hM' (q (p y))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, i), mem_pull.2 hj, hi⟩) b (fun c c' y hy => by
      rw [hb _ (𝟙 Y) y c hy.1, hb _ (𝟙 Y) y c' hy.2,
        hs.trans hL hu hw (𝟙 Y ≫ m) y c.1 c'.1 c.2 c'.2 (mem_pull.1 (l c hy.1).1) (mem_pull.1 (l c' hy.2).1)
          (l c hy.1).2 (l c' hy.2).2,
        hs.trans hL hu hw (𝟙 Y ≫ p) y c.1 c'.1 c.2 c'.2 (mem_pull.1 hy.1.1) (mem_pull.1 hy.2.1) hy.1.2 hy.2.2,
        Category.id_comp, Category.id_comp, e]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨a, fun Z r z j i hz => ?_⟩
  have := (gm_res r z le_top (show r z ∈ W (j, i) from hz) a).symm.trans
    ((congrArg (gm r z (W (j, i))) (ha (j, i))).trans (hb Z r z (j, i) hz))
  rw [this, inv_mul_cancel_right]

theorem IsQuot.pgen [Flat q] [Surjective q] (hL : L.IsLB) {u : LB.Iso L (M'.pull q)}
    {w : LB.Iso L (M.pull (q ≫ β))} (hu : PGen u) (hw : PGen w) {s} (hs : IsQuot u w s)
    {v : LB.Iso M' (M.pull β)} (hv : ∀ (Y : Scheme.{0}) (f : Y ⟶ G) (y : Y) j i, q (f y) ∈ dom M' M β j i →
      gw v (f ≫ q) y j i = gm f y _ (s j i)) : PGen v := by
  intro Y f y j j' i i' hj hj' hi hi'
  obtain ⟨z, rfl⟩ := (pullback.fst f q).surjective y
  have e : q (pullback.snd f q z) = f (pullback.fst f q z) :=
    congrArg (fun g => g z) (pullback.condition (f := f) (g := q)).symm
  apply kap_injective _ z
  have a := hs.trans hL hu hw (pullback.snd f q) z j j' i i' (e ▸ hj) (e ▸ hj') (e ▸ hi) (e ▸ hi')
  rw [← hv _ _ _ _ _ ⟨mem_pull.2 (e ▸ hj), e ▸ hi⟩, ← hv _ _ _ _ _ ⟨mem_pull.2 (e ▸ hj'), e ▸ hi'⟩,
    ← pullback.condition, Category.assoc] at a
  simp only [map_mul, map_inv, kap_gm, kap_gw]
  exact a

end Schemes

section Groups
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G B' : Over S'} {B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj B']
  [IsCommMonObj B'] [GrpObj B] [IsCommMonObj B] {P : CP G} {M' : CP B'} {M : CP B} {q : G ⟶ B'}
  {β : B'.left ⟶ B.left} {hβ : β ≫ B.hom = B'.hom ≫ f}

def Eqns (M' : CP B') (M : CP B) (hβ : β ≫ B.hom = B'.hom ≫ f) {T : Over S'} (z : T.left)
    (I : (T.left ⟶ B'.left) → M'.L.L.ι) (J : (T.left ⟶ B.left) → M.L.L.ι) {A : Type} [Group A] (π : A → (T ⟶ B'))
    (V : A → (T.left.presheaf.stalk z)ˣ) : Prop :=
  (val (L := M.L.L) (φ := fun _ : PUnit => eSec B) (ε := fun _ => 1) M.L.rig (T.hom ≫ f) z J =
    V 1 * val (L := M'.L.L) (φ := fun _ : PUnit => eSec B') (ε := fun _ => 1) M'.L.rig T.hom z I) ∧
  (∀ x, val M.sym ((π x).left ≫ β) z J * V x = V x⁻¹ * val M'.sym (π x).left z I) ∧
  ∀ x y u, @id (T.left.presheaf.stalk z)ˣ (cubV M.c (T := Over.mk (T.hom ≫ f)) z J (toBase hβ (π x))
      (toBase hβ (π y)) (toBase hβ (π u))) * V (x * y) * V (x * u) * V (y * u) * V 1 =
    V (x * y * u) * V x * V y * V u * cubV M'.c z I (π x) (π y) (π u)

theorem cubV_toBase_hom {L : RigLB B'} (c : CubicalStr B' L) (h : q.left ≫ B'.hom = G.hom ≫ 𝟙 S') {T : Over S'}
    (z : T.left) (J) (x y u : T ⟶ G) :
    cubV c (T := Over.mk (T.hom ≫ 𝟙 S')) z J (toBase h x) (toBase h y) (toBase h u) =
      cubV c z J (x ≫ q) (y ≫ q) (u ≫ q) := by
  let ρ : Over.mk (T.hom ≫ 𝟙 S') ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e : ∀ a : T ⟶ G, toBase h a = ρ ≫ a ≫ q := fun a => Over.OverMorphism.ext (Category.id_comp _).symm
  have e' : (lift (toBase h x) (lift (toBase h y) (toBase h u))).left =
      (lift (x ≫ q) (lift (y ≫ q) (u ≫ q))).left := by
    rw [e, e, e, ← comp_lift, ← comp_lift]; exact Category.id_comp _
  exact congrArg (fun r => val (L := L.L) (φ := thφ B' (x3 B')) (ε := thε) c.t r z J) e'

theorem eqns_quot {hq : q.left ≫ B'.hom = G.hom ≫ 𝟙 S'} {hw : (q.left ≫ β) ≫ B.hom = G.hom ≫ f} {u w}
    (Hu : IsCPMap P M' (𝟙 S') q.left hq u) (Hw : IsCPMap P M f (q.left ≫ β) hw w) {s} (hs : IsQuot u w s)
    {T : Over S'} {z : T.left} {I J} (hI : Good M'.L.L z I) (hJ : Good M.L.L z J) :
    Eqns M' M hβ z I J (fun x : T ⟶ G => x ≫ q)
      (fun x => gm x.left z _ (s (J ((x ≫ q).left ≫ β)) (I (x ≫ q).left))) := by
  obtain ⟨K, hK⟩ := exists_good_pt P.L.isLB z
  obtain ⟨V, hV⟩ : ∃ V : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
    V = fun x => gm x.left z _ (s (J ((x ≫ q).left ≫ β)) (I (x ≫ q).left)) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
    ∀ x, U x = gw u x.left z (I (x.left ≫ q.left)) (K x.left) := ⟨_, fun _ => rfl⟩
  rw [← hV]
  obtain ⟨a₁, a₂, a₃⟩ := Hw.vals T z K J hK hJ (fun x => V x * U x) (fun x => by
    rw [hV, hU, ← Category.assoc]
    exact (hs _ x.left z _ _ _ (hJ ((x.left ≫ q.left) ≫ β)) (hI (x.left ≫ q.left)) (hK x.left)).symm)
  obtain ⟨b₁, b₂, b₃⟩ := Hu.vals T z K I hK hI U hU
  refine ⟨?_, fun x => ?_, fun x y v => ?_⟩
  · rw [Category.comp_id] at b₁
    rw [a₁, b₁, _root_.mul_assoc]
  · have a := a₂ x
    have b := b₂ x
    rw [← Category.assoc] at a
    rw [Over.comp_left]
    apply Additive.ofMul.injective
    have a' := congrArg Additive.ofMul a
    have b' := congrArg Additive.ofMul b
    simp only [ofMul_mul] at a' b' ⊢
    linear_combination (norm := abel) a' - b'
  · have a := a₃ x y v
    have b := b₃ x y v
    have e : ∀ x : T ⟶ G, toBase hw x = toBase hβ (x ≫ q) := fun x =>
      Over.OverMorphism.ext (Category.assoc _ _ _).symm
    rw [e, e, e] at a
    rw [_root_.id, cubV_toBase_hom] at b
    generalize @id (T.left.presheaf.stalk z)ˣ (cubV M.c (T := Over.mk (T.hom ≫ f)) z J (toBase hβ (x ≫ q))
      (toBase hβ (y ≫ q)) (toBase hβ (v ≫ q))) = C at a ⊢
    apply Additive.ofMul.injective
    have a' := congrArg Additive.ofMul a
    have b' := congrArg Additive.ofMul b
    simp only [ofMul_mul] at a' b' ⊢
    linear_combination (norm := abel) a' - b'

theorem Eqns.ker (mul : ∀ (T : Over S') (x y : T ⟶ B'), toBase hβ (x * y) = toBase hβ x * toBase hβ y)
    {T : Over S'} {z : T.left} {I J} (hI : Good M'.L.L z I) (hJ : Good M.L.L z J) {A : Type} [Group A]
    {π : A → (T ⟶ B')} {V : A → (T.left.presheaf.stalk z)ˣ} (h : Eqns M' M hβ z I J π V) {t : A} (ht : π t = 1) :
    V t = V t⁻¹ ∧ ∀ y u, V (t * y) * V (t * u) * V (y * u) * V 1 = V (t * y * u) * V t * V y * V u := by
  have o : toBase hβ (1 : T ⟶ B') = 1 := map_one (toBaseHom mul T)
  constructor
  · have a := h.2.1 t
    have o' : (1 : T ⟶ B').left ≫ β = (1 : Over.mk (T.hom ≫ f) ⟶ B).left := congrArg (fun a => a.left) o
    have c := M.val_sym_one (T := Over.mk (T.hom ≫ f)) hJ
    rw [ht, M'.val_sym_one hI, o', _root_.mul_one] at a
    exact ((_root_.one_mul _).symm.trans (congrArg (· * V t) c.symm)).trans a
  · intro y u
    have a := h.2.2 t y u
    have c : @id (T.left.presheaf.stalk z)ˣ (cubV M.c (T := Over.mk (T.hom ≫ f)) z J 1
      (toBase hβ (π y)) (toBase hβ (π u))) = 1 := (isCub_cubV M.c (T := Over.mk (T.hom ≫ f)) hJ).face _ _
    rwa [ht, o, c, (isCub_cubV M'.c hI).face, _root_.one_mul, _root_.mul_one] at a

theorem exists_lift [Flat q.left] [Surjective q.left] {T : Over S'} (x : T ⟶ B') :
    ∃ (T' : Over S') (ρ : T' ⟶ T) (x' : T' ⟶ G), Flat ρ.left ∧ Surjective ρ.left ∧ x' ≫ q = ρ ≫ x :=
  ⟨Over.mk (pullback.fst x.left q.left ≫ T.hom), Over.homMk (pullback.fst x.left q.left) rfl,
    Over.homMk (pullback.snd x.left q.left) (by
      show pullback.snd x.left q.left ≫ G.hom = pullback.fst x.left q.left ≫ T.hom
      rw [← Over.w q, ← pullback.condition_assoc, Over.w]),
    inferInstanceAs (Flat (pullback.fst x.left q.left)), inferInstanceAs (Surjective (pullback.fst x.left q.left)),
    Over.OverMorphism.ext pullback.condition.symm⟩

theorem exists_lift₃ [Flat q.left] [Surjective q.left] {T : Over S'} (x y u : T ⟶ B') :
    ∃ (T' : Over S') (ρ : T' ⟶ T) (x' y' u' : T' ⟶ G), Flat ρ.left ∧ Surjective ρ.left ∧ x' ≫ q = ρ ≫ x ∧
      y' ≫ q = ρ ≫ y ∧ u' ≫ q = ρ ≫ u := by
  obtain ⟨T₁, ρ₁, x₁, _, _, e₁⟩ := exists_lift (q := q) x
  obtain ⟨T₂, ρ₂, y₂, _, _, e₂⟩ := exists_lift (q := q) (ρ₁ ≫ y)
  obtain ⟨T₃, ρ₃, u₃, _, _, e₃⟩ := exists_lift (q := q) (ρ₂ ≫ ρ₁ ≫ u)
  refine ⟨T₃, ρ₃ ≫ ρ₂ ≫ ρ₁, ρ₃ ≫ ρ₂ ≫ x₁, ρ₃ ≫ y₂, u₃, inferInstanceAs (Flat (ρ₃.left ≫ ρ₂.left ≫ ρ₁.left)),
    inferInstanceAs (Surjective (ρ₃.left ≫ ρ₂.left ≫ ρ₁.left)), ?_, ?_, ?_⟩ <;> simp [*]

theorem isCPMap_of_lift [IsMonHom q] [Flat q.left] [Surjective q.left]
    (mul : ∀ (T : Over S') (x y : T ⟶ B'), toBase hβ (x * y) = toBase hβ x * toBase hβ y)
    {v : LB.Iso M'.L.L (M.L.L.pull β)} (hv : PGen v)
    (H : ∀ (T : Over S') (z : T.left) (I J), Good M'.L.L z I → Good M.L.L z J →
      Eqns M' M hβ z I J (fun x : T ⟶ G => x ≫ q)
        (fun x => gw v (x ≫ q).left z (J ((x ≫ q).left ≫ β)) (I (x ≫ q).left))) :
    IsCPMap M' M f β hβ v := by
  refine ⟨mul, (isGen_iff v).2 hv, fun T z I J hI hJ W hW => ⟨?_, fun x => ?_, fun x y u => ?_⟩⟩
  · have := (H T z I J hI hJ).1
    simp only [MonObj.one_comp] at this
    rw [hW]; exact this
  on_goal 1 => obtain ⟨T', ρ, x', _, _, e₁⟩ := exists_lift (q := q) x
  on_goal 2 => obtain ⟨T', ρ, x', y', u', _, _, e₁, e₂, e₃⟩ := exists_lift₃ (q := q) x y u
  all_goals
    obtain ⟨z, rfl⟩ := ρ.left.surjective z
    have : Epi ρ.left := Flat.epi_of_flat_of_surjective _
    obtain ⟨I', hI', eI⟩ := exists_good_epi M'.L.isLB ρ.left z hI
    obtain ⟨J', hJ', eJ⟩ := exists_good_epi M.L.isLB ρ.left z hJ
    obtain ⟨W', hW'⟩ : ∃ W' : (T' ⟶ B') → (T'.left.presheaf.stalk z)ˣ,
      ∀ b, gw v b.left z (J' (b.left ≫ β)) (I' b.left) = W' b := ⟨_, fun _ => rfl⟩
    have k : ∀ b, kap ρ.left z (W b) = W' (ρ ≫ b) := fun b => by
      rw [hW, kap_gw, ← hW', Over.comp_left, Category.assoc, eI, eJ]
    have E := H T' z I' J' hI' hJ'
    simp only [hW'] at E
    apply kap_injective ρ.left z
  · have a := E.2.1 x'
    simp only [GrpObj.inv_comp, e₁] at a
    rw [map_mul, map_mul, k, k, kap_val _ _ _ eI, kap_val _ _ _ eJ, GrpObj.comp_inv, ← Category.assoc]
    exact a
  · have a := E.2.2 x' y' u'
    simp only [MonObj.mul_comp, MonObj.one_comp, e₁, e₂, e₃] at a
    have c' : kap ρ.left z (cubV M'.c (ρ.left z) I x y u) = cubV M'.c z I' (ρ ≫ x) (ρ ≫ y) (ρ ≫ u) := by
      refine (kap_val (L := M'.L.L) (φ := thφ B' (x3 B')) (ε := thε) M'.c.t ρ.left z eI _).trans ?_
      refine congrArg (fun r => val (L := M'.L.L) (φ := thφ B' (x3 B')) (ε := thε) M'.c.t r z I') ?_
      rw [← comp_lift, ← comp_lift]; rfl
    have c : kap ρ.left z (@id (T.left.presheaf.stalk (ρ.left z))ˣ (cubV M.c (T := Over.mk (T.hom ≫ f)) (ρ.left z) J
        (toBase hβ x) (toBase hβ y) (toBase hβ u))) = @id (T'.left.presheaf.stalk z)ˣ
        (cubV M.c (T := Over.mk (T'.hom ≫ f)) z J' (toBase hβ (ρ ≫ x)) (toBase hβ (ρ ≫ y)) (toBase hβ (ρ ≫ u))) := by
      let ρ' : Over.mk (T'.hom ≫ f) ⟶ Over.mk (T.hom ≫ f) := Over.homMk ρ.left (by simp)
      have e : ∀ a : T ⟶ B', toBase hβ (ρ ≫ a) = ρ' ≫ toBase hβ a := fun a =>
        Over.OverMorphism.ext (Category.assoc _ _ _)
      rw [e, e, e]
      refine (kap_val (L := M.L.L) (φ := thφ B (x3 B)) (ε := thε) M.c.t ρ.left z eJ _).trans ?_
      refine congrArg (fun r => val (L := M.L.L) (φ := thφ B (x3 B)) (ε := thε) M.c.t r z J') ?_
      rw [← comp_lift, ← comp_lift]; rfl
    simp only [map_mul, k, c, c', MonObj.comp_mul, MonObj.comp_one]
    exact a

end Groups

theorem factor_alg {T G U : Type} [CommGroup T] [CommGroup G] [CommGroup U] (e₀ : T →* G) (V : G → U) (A : T → G → U)
    (hA : ∀ t g, V (e₀ t * g) = A t g * V g)
    (h : ∀ t, V (e₀ t) = V (e₀ t)⁻¹ ∧ ∀ y u, V (e₀ t * y) * V (e₀ t * u) * V (y * u) * V 1 =
      V (e₀ t * y * u) * V (e₀ t) * V y * V u) :
    (∀ t t' u, A (t * t') u * (A (t * t') 1)⁻¹ = A t u * (A t 1)⁻¹ * (A t' u * (A t' 1)⁻¹)) ∧
      (∀ t t', A (t * t') 1 = A t (e₀ t') * A t' 1) ∧ ∀ t, A t⁻¹ 1 = A t 1 := by
  have e : ∀ t g, A t g = V (e₀ t * g) * (V g)⁻¹ := fun t g => by rw [hA, mul_inv_cancel_right]
  refine ⟨fun t t' u => ?_, fun t t' => ?_, fun t => ?_⟩
  · have a := congrArg Additive.ofMul ((h t).2 (e₀ t') u)
    apply Additive.ofMul.injective
    simp only [e, map_mul, _root_.mul_one, ofMul_mul, ofMul_inv] at a ⊢
    linear_combination (norm := abel) -a
  · apply Additive.ofMul.injective
    simp only [e, map_mul, _root_.mul_one, ofMul_mul, ofMul_inv]
    abel
  · simp only [e, map_inv, _root_.mul_one, ← (h t).1]

section Torus
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] (Y : Over S) [ConnectedSpace Y.left]

theorem exists_char (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ)
    (h : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (z : Z.left),
      gm (lift (t * t') y).left z ⊤ ρ = gm (lift t y).left z ⊤ ρ * gm (lift t' y).left z ⊤ ρ) :
    ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (z : Z.left),
      gm (lift t y).left z ⊤ ρ = gm (𝟙 Z.left) z ⊤ (chV t χ) := by
  obtain ⟨χ, hχ, -⟩ := existsUnique_character_of_mul S X Y ρ fun Z t t' y =>
    (appTop_eq_iff (Units.map (lift (t * t') y).left.appTop.hom.toMonoidHom ρ)
      (Units.map (lift t y).left.appTop.hom.toMonoidHom ρ * Units.map (lift t' y).left.appTop.hom.toMonoidHom ρ)).2
      fun z => by rw [map_mul, ← gm_top, ← gm_top, ← gm_top, h]
  refine ⟨χ, fun Z t y z => ?_⟩
  rw [gm_top]
  refine congrArg _ (Units.ext ?_)
  show (lift t y).left.appTop.hom ρ.val = _
  rw [hχ, chV_val, Rosenlicht.over_appTop_comp, lift_fst]

include Y in
theorem char_eq_zero {χ : X} (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (_ : Z ⟶ Y) (z : Z.left),
    gm (𝟙 Z.left) z ⊤ (chV t χ) = 1) : χ = 0 := by
  refine (existsUnique_character_of_mul S X Y 1 fun Z t t' y => by simp).unique ?_ ?_
  · rw [← chV_val]
    exact (appTop_eq_iff _ _).2 fun z => (map_one _).trans (h _ _ (snd _ _) z).symm
  · rw [← chV_val, chV_zero]

end Torus

section Main
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] [Module.Free ℤ X] {G : Over S'} {B : Over S}
  [GrpObj G] [IsCommMonObj G] [ConnectedSpace G.left] [GrpObj B] [IsCommMonObj B] {Q : TQ G X} {P : CP G}
  {M' : CP Q.B} {M : CP B} {β : Q.B.left ⟶ B.left} {hβ : β ≫ B.hom = Q.B.hom ≫ f}

theorem mul_comp_q {Z : Over S'} (t : Z ⟶ splitTorus S' X) (g : Z ⟶ G) : ((t ≫ Q.i) * g) ≫ Q.q = g ≫ Q.q := by
  have := Q.q_hom
  rw [MonObj.mul_comp, Category.assoc, Q.isKernel.w, ← Category.assoc, toUnit_unique (t ≫ toUnit _) (toUnit _),
    ← Hom.one_def, _root_.one_mul]

theorem quot_invariant (mul : ∀ (T : Over S') (x y : T ⟶ Q.B), toBase hβ (x * y) = toBase hβ x * toBase hβ y)
    {hq : Q.q.left ≫ Q.B.hom = G.hom ≫ 𝟙 S'} {hw : (Q.q.left ≫ β) ≫ B.hom = G.hom ≫ f} {u w}
    (Hu : IsCPMap P M' (𝟙 S') Q.q.left hq u) (Hw : IsCPMap P M f (Q.q.left ≫ β) hw w) {s} (hs : IsQuot u w s)
    {Z : Over S'} (t : Z ⟶ splitTorus S' X) (g : Z ⟶ G) (z : Z.left) (j i)
    (hz : Q.q.left (g.left z) ∈ dom M'.L.L M.L.L β j i) :
    gm ((t ≫ Q.i) * g).left z _ (s j i) = gm g.left z _ (s j i) := by
  have := Q.i_hom
  obtain ⟨a, ha⟩ := hs.exists_ratio P.L.isLB M'.L.isLB M.L.isLB ((isGen_iff _).1 Hu.gen) ((isGen_iff _).1 Hw.gen)
    ((fst (splitTorus S' X) G ≫ Q.i) * snd (splitTorus S' X) G).left (snd (splitTorus S' X) G).left
    (congrArg (fun k => k.left) (mul_comp_q (Q := Q) (fst (splitTorus S' X) G) (snd (splitTorus S' X) G)))
  obtain ⟨A, hA⟩ : ∃ A : ∀ {Z : Over S'} (z : Z.left), (Z ⟶ splitTorus S' X) → (Z ⟶ G) → (Z.left.presheaf.stalk z)ˣ,
    ∀ {Z : Over S'} (z : Z.left) (t : Z ⟶ splitTorus S' X) (g : Z ⟶ G), gm (lift t g).left z ⊤ a = A z t g := ⟨_, fun _ _ _ => rfl⟩
  have hr : ∀ {Z : Over S'} (t : Z ⟶ splitTorus S' X) (g : Z ⟶ G) (z : Z.left) (j i),
      Q.q.left (g.left z) ∈ dom M'.L.L M.L.L β j i →
      gm ((t ≫ Q.i) * g).left z _ (s j i) = A z t g * gm g.left z _ (s j i) := fun t g z j i hz => by
    have e : (lift t g).left ≫ (snd (splitTorus S' X) G).left = g.left := by rw [← Over.comp_left, lift_snd]
    have := ha _ (lift t g).left z j i (by
      have e' : (snd (splitTorus S' X) G).left ((lift t g).left z) = g.left z := congrArg (fun k => k z) e
      rw [e']; exact hz)
    rwa [e, hA, ← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd] at this
  have alg : ∀ {Z : Over S'} (z : Z.left),
      (∀ t t' u, A z (t * t') u * (A z (t * t') 1)⁻¹ = A z t u * (A z t 1)⁻¹ * (A z t' u * (A z t' 1)⁻¹)) ∧
      (∀ t t', A z (t * t') 1 = A z t (t' ≫ Q.i) * A z t' 1) ∧ ∀ t, A z t⁻¹ 1 = A z t 1 := fun {Z} z => by
    obtain ⟨I, hI⟩ := exists_good_pt M'.L.isLB z
    obtain ⟨J, hJ⟩ := exists_good_pt M.L.isLB z
    refine factor_alg (MonoidHom.mk' (fun t : Z ⟶ splitTorus S' X => t ≫ Q.i) fun _ _ => MonObj.mul_comp _ _ _)
      (fun x => gm x.left z _ (s (J ((x ≫ Q.q).left ≫ β)) (I (x ≫ Q.q).left))) (A z) (fun t g => ?_) fun t =>
      (eqns_quot (hβ := hβ) Hu Hw hs hI hJ).ker mul hI hJ ?_
    · show gm ((t ≫ Q.i) * g).left z _ (s (J ((((t ≫ Q.i) * g) ≫ Q.q).left ≫ β)) (I (((t ≫ Q.i) * g) ≫ Q.q).left)) = _
      rw [mul_comp_q]
      exact hr t g z _ _ ⟨mem_pull.2 (hJ ((g ≫ Q.q).left ≫ β)), hI (g ≫ Q.q).left⟩
    · have := mul_comp_q (Q := Q) t 1
      have _ := Q.q_hom
      rwa [_root_.mul_one, MonObj.one_comp] at this
  obtain ⟨χ, hχ⟩ := exists_char G (a * (Units.map (lift (fst (splitTorus S' X) G) (1 : _ ⟶ G)).left.appTop.hom.toMonoidHom a)⁻¹)
    (fun Z t t' y z => by
      have e : ∀ t : Z ⟶ splitTorus S' X, gm (lift t y).left z ⊤
          (Units.map (lift (fst (splitTorus S' X) G) (1 : _ ⟶ G)).left.appTop.hom.toMonoidHom a) = A z t 1 := fun t => by
        refine (gm_pull _ _ z ⊤ trivial a).trans ?_
        rw [← Over.comp_left, comp_lift, lift_fst, MonObj.comp_one, hA]
      simp only [map_mul, map_inv, e]
      rw [hA, hA, hA]
      exact (alg z).1 t t' y)
  have c : ∀ {Z : Over S'} (z : Z.left) t g, A z t g = A z t 1 := fun {Z} z t g => by
    have e : ∀ y : Z ⟶ G, gm (lift t y).left z ⊤
        (Units.map (lift (fst (splitTorus S' X) G) (1 : _ ⟶ G)).left.appTop.hom.toMonoidHom a) = A z t 1 := fun y => by
      refine (gm_pull _ _ z ⊤ trivial a).trans ?_
      rw [← Over.comp_left, comp_lift, lift_fst, MonObj.comp_one, hA]
    have := (hχ Z t g z).trans (hχ Z t 1 z).symm
    simp only [map_mul, map_inv, e] at this
    rw [hA, hA] at this
    exact mul_right_cancel this
  obtain ⟨ψ, hψ⟩ := exists_char G a (fun Z t t' y z => by
    rw [hA, hA, hA, c z _ y, c z _ y, c z _ y, (alg z).2.1, c z t])
  have h2 : ψ + ψ = 0 := char_eq_zero G fun Z t _ z => by
    have := (alg z).2.2 t
    rw [← hA, ← hA, hψ, hψ, chV_inv, map_inv] at this
    rw [chV_add, map_mul]
    exact (congrArg (· * _) this.symm).trans (inv_mul_cancel _)
  have h0 : ψ = 0 := by
    rw [← two_smul ℤ ψ] at h2
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  rw [hr t g z j i hz, ← hA, hψ, h0, chV_zero, map_one, _root_.one_mul]

end Main

end GlobalTheory.IsoDesc

open GlobalTheory.IsoDesc in

theorem GlobalTheory.isCPMap_descends : ∀ (S S' : Scheme.{0}) [ConnectedSpace S'] (f : S' ⟶ S) (X : Type) [AddCommGroup X] [Module.Free ℤ X] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] [ConnectedSpace G'.left] (Q : TQ G' X) (P' : CP G') (D : Q.Desc P') (B : Over S) [GrpObj B] [IsCommMonObj B] (M : CP B) (β : Q.B.left ⟶ B.left) (hβ : β ≫ B.hom = Q.B.hom ≫ f) (hw) (w), (∀ (T : Over S') (x y : T ⟶ Q.B), toBase hβ (x * y) = toBase hβ x * toBase hβ y) → IsCPMap P' M f (Q.q.left ≫ β) hw w → ∃ v, IsCPMap D.M M f β hβ v := by
  intro S S' _ f X _ _ G _ _ _ Q P D B _ _ M β hβ hw w mul Hw
  have := Q.q_hom
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  have gu := (isGen_iff _).1 D.map.gen
  have gw' := (isGen_iff _).1 Hw.gen
  obtain ⟨s, hs⟩ := exists_isQuot P.L.isLB D.M.L.isLB M.L.isLB gu gw'
  have desc : ∀ j i, ∃ v : Γ(Q.B.left, dom D.M.L.L M.L.L β j i)ˣ, pullU Q.q.left _ v = s j i := fun j i => by
    obtain ⟨-, h₁, h₂⟩ := GlobalTheory.invariant_functions_descend S' G Q.B _ Q.q Q.i Q.q_hom Q.i_hom Q.q_flat Q.q_surj
      inferInstance Q.isKernel (dom D.M.L.L M.L.L β j i)
    obtain ⟨a, ha⟩ := h₂ (s j i).val fun Z t g k₁ k₂ => appLE_eq_of_gm _ _ _ k₁ k₂ _ fun z =>
      quot_invariant mul D.map Hw hs t g z j i (k₂ trivial)
    exact ⟨(h₁ a (ha ▸ (s j i).isUnit)).unit, Units.ext ha⟩
  choose v hv using desc
  have val_v : ∀ (Y : Scheme.{0}) (r : Y ⟶ G.left) (y : Y) j i, Q.q.left (r y) ∈ dom D.M.L.L M.L.L β j i →
      gw (⟨fun p => v (p.1 PUnit.unit) p.2⟩ : LB.Iso D.M.L.L (M.L.L.pull β)) (r ≫ Q.q.left) y j i =
        gm r y _ (s j i) := fun Y r y j i h => by
    rw [← hv]; exact (gm_pull r Q.q.left y _ h _).symm
  refine ⟨_, isCPMap_of_lift (q := Q.q) mul (hs.pgen P.L.isLB gu gw' val_v) fun T z I J hI hJ => ?_⟩
  have := eqns_quot (hβ := hβ) D.map Hw hs hI hJ
  refine cast (congrArg _ (funext fun x => ?_)) this
  exact (val_v _ x.left z _ _ ⟨mem_pull.2 (hJ ((x ≫ Q.q).left ≫ β)), hI (x ≫ Q.q).left⟩).symm

end
