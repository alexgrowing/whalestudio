import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalSymmetryTransport
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU
variable {S S' : Scheme.{0}}

structure CP (G : Over S) [GrpObj G] [IsCommMonObj G] where

  L : RigLB G

  c : CubicalStr G L

  sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])
  sym_gen : sym.IsGen
  sym_rig : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L)
  sym_cub : ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J), Good L.L z J →
    cubV c z J x⁻¹ y⁻¹ u⁻¹ * val sym (x * y).left z J * val sym (x * u).left z J * val sym (y * u).left z J =
      cubV c z J x y u * val sym (x * y * u).left z J * val sym x.left z J * val sym y.left z J * val sym u.left z J

structure IsCPMap {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (P' : CP G') (P : CP G) (f : S' ⟶ S) (F : G'.left ⟶ G.left) (hw : F ≫ G.hom = G'.hom ≫ f)
    (w : LB.Iso P'.L.L (P.L.L.pull F)) : Prop where
  mul : ∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y
  gen : w.IsGen
  vals : ∀ (T : Over S') (z : T.left) (J' : (T.left ⟶ G'.left) → P'.L.L.ι) (J : (T.left ⟶ G.left) → P.L.L.ι),
    Good P'.L.L z J' → Good P.L.L z J →
    ∀ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left)) →
      (val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig (T.hom ≫ f) z J =
        W 1 * val (L := P'.L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) P'.L.rig T.hom z J') ∧
      (∀ x : T ⟶ G', val P.sym (x.left ≫ F) z J * W x = W x⁻¹ * val P'.sym x.left z J') ∧
      ∀ x y u : T ⟶ G', @id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := Over.mk (T.hom ≫ f)) z J (toBase hw x) (toBase hw y) (toBase hw u)) *
          W (x * y) * W (x * u) * W (y * u) * W 1 =
        W (x * y * u) * W x * W y * W u * cubV P'.c z J' x y u

section
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H]

def lamφ (i : H ⟶ G) : Fin 4 → ((H ⊗ G).left ⟶ G.left) :=
  ![((fst H G ≫ i) * snd H G).left, (fst H G ≫ i).left, (snd H G).left, (1 : H ⊗ G ⟶ G).left]

structure BiTriv {L : RigLB G} (c : CubicalStr G L) (i : H ⟶ G) where

  s : LB.Gen (LB.LinComb L.L (lamφ i) Oε)
  gen : s.IsGen
  law1 : ∀ (T : Over S) (t t' : T ⟶ H) (x : T ⟶ G) (z : T.left) (J), Good L.L z J →
    val s (lift (t * t') x).left z J = cubV c z J (t ≫ i) (t' ≫ i) x * val s (lift t x).left z J * val s (lift t' x).left z J
  law2 : ∀ (T : Over S) (t : T ⟶ H) (x x' : T ⟶ G) (z : T.left) (J), Good L.L z J →
    val s (lift t (x * x')).left z J = cubV c z J (t ≫ i) x x' * val s (lift t x).left z J * val s (lift t x').left z J

structure CubTriv {L : RigLB G} (c : CubicalStr G L) (i : H ⟶ G) where

  s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![i.left, (1 : H ⟶ G).left] ![1, -1])
  gen : s.IsGen
  cub : ∀ (T : Over S) (x y u : T ⟶ H) (z : T.left) (J), Good L.L z J →
    val s (x * y * u).left z J * val s x.left z J * val s y.left z J * val s u.left z J =
      cubV c z J (x ≫ i) (y ≫ i) (u ≫ i) * val s (x * y).left z J * val s (x * u).left z J * val s (y * u).left z J

def CubTriv.Even {P : CP G} {i : H ⟶ G} (σ : CubTriv P.c i) : Prop :=
  ∀ (T : Over S) (x : T ⟶ H) (z : T.left) (J), Good P.L.L z J →
    val σ.s (x⁻¹).left z J = val P.sym (x ≫ i).left z J * val σ.s x.left z J

def CubWeil {L : RigLB G} (c : CubicalStr G L) (N : ℕ) {T : Over S} (x y : T ⟶ G) (ζ : Γ(T.left, ⊤)ˣ) : Prop :=
  x ^ N = 1 ∧ y ^ N = 1 ∧ ∀ (z : T.left) (J), Good L.L z J →
    gm (𝟙 T.left) z ⊤ ζ * cubN (cubV c z J) N 1 x y = cubN (cubV c z J) N 1 y x

end

def IsWt {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (i : splitTorus S X ⟶ G) (V : G.left.Opens)
    (u : Γ(G.left, V)) (χ : X) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
    (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom u = t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom u

structure TQ (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] where

  B : Over S
  [grp : GrpObj B]
  [comm : IsCommMonObj B]
  isAb : IsAbelianScheme B

  q : G ⟶ B

  i : splitTorus S X ⟶ G
  q_hom : IsMonHom q
  i_hom : IsMonHom i
  q_flat : Flat q.left
  q_surj : Surjective q.left
  q_affine : IsAffineHom q.left
  isKernel : IsPullback i (toUnit _) q (η[B])
  loc : ∀ (b : B.left) (χ : X), ∃ V : B.left.Opens, b ∈ V ∧ ∃ u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ, IsWt i _ u.val χ

attribute [instance] TQ.grp TQ.comm

structure TQ.Desc {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X] (Q : TQ G X) (P : CP G) where

  M : CP Q.B

  w : LB.Iso P.L.L (M.L.L.pull Q.q.left)
  map : IsCPMap P M (𝟙 S) Q.q.left (by simp) w

def TQ.GenWt {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (Q : TQ G X) (N : LB Q.B.left)
    (t : LB.Gen (N.pull Q.q.left)) (χ : X) : Prop :=
  t.IsGen ∧ ∀ j, IsWt Q.i _ (t.s j).val χ

def IsLevelCP {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (P' : CP (thickObj R I e G)) (P : CP G) : Prop :=
  ∃ w, IsCPMap P' P (thick R I e) (pullback.fst G.hom (thick R I e)) pullback.condition w

section Basic
variable {X Y Z : Scheme.{0}} {K : Type} [Fintype K]

theorem exists_good_pt {L : LB X} (hL : L.IsLB) (z : Z) : ∃ J, Good L z J := by
  exact ⟨fun ψ => (exists_chart hL (ψ z)).choose, fun ψ => (exists_chart hL (ψ z)).choose_spec⟩

def scaleGen {M : LB Y} (u : Γ(Y, ⊤)ˣ) (t : LB.Gen M) : LB.Gen M := ⟨fun j => res le_top u * t.s j⟩

theorem scaleGen_isGen {M : LB Y} (u : Γ(Y, ⊤)ˣ) {t : LB.Gen M} (ht : t.IsGen) : (scaleGen u t).IsGen := by
  have rr : ∀ {U V W : Y.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (a : Γ(Y, U)ˣ),
      res h₁ (res h₂ a) = res (h₁.trans h₂) a := by
    intro U V W h₁ h₂ a
    refine unit_ext fun x hx => ?_
    rw [gm_res (𝟙 Y) x h₁ hx, gm_res (𝟙 Y) x h₂ (h₁ hx), gm_res (𝟙 Y) x (h₁.trans h₂) hx]
  intro i j
  have e := ht i j
  simp only [scaleGen, map_mul]
  rw [e, rr, rr]
  exact mul_left_comm _ _ _

theorem val_scaleGen {L : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε))
    (r : Z ⟶ Y) {z : Z} {J} (hJ : Good L z J) : val (scaleGen u t) r z J = gm r z ⊤ u * val t r z J := by
  have hm := hJ.mem φ r
  have e := map_mul (gm r z (LB.wchart L φ fun k => J (r ≫ φ k))) (res le_top u) (t.s fun k => J (r ≫ φ k))
  exact e.trans (congrArg (· * gm r z _ (t.s fun k => J (r ≫ φ k))) (gm_res r z le_top hm u))

def unitGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) : LB.Gen (LB.LinComb (Inh.trivLB X) φ ε) := ⟨fun _ => 1⟩

theorem unitGen_isGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) : (unitGen φ ε).IsGen := by
  intro i j
  have e₁ : ∀ {A B : Y.Opens} (h : A ≤ B), res h (1 : Γ(Y, B)ˣ) = 1 := fun h => map_one _
  have e₂ : ∀ {A : X.Opens} (f : Y ⟶ X), pullU f A (1 : Γ(X, A)ˣ) = 1 := fun f => map_one _
  have e₃ : ∀ a b, (Inh.trivLB X).g a b = 1 := fun _ _ => rfl
  simp only [unitGen]
  rw [e₁, e₁, _root_.mul_one]
  symm
  refine Finset.prod_eq_one fun k _ => ?_
  rw [e₃, e₂]
  exact (congrArg (· ^ ε k) (e₁ _)).trans (one_zpow _)

theorem val_unitGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (J) : val (unitGen φ ε) r z J = 1 := by
  exact map_one _

theorem gm_top (r : Z ⟶ Y) (z : Z) (u : Γ(Y, ⊤)ˣ) :
    gm r z ⊤ u = gm (𝟙 Z) z ⊤ (Units.map r.appTop.hom.toMonoidHom u) := by
  have h := gm_pull (𝟙 Z) r z ⊤ trivial u
  rw [Category.id_comp] at h
  exact h.symm

end Basic

theorem one_left (G : Over S) [GrpObj G] (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ eSec G := by
  have h : (toUnit T).left = T.hom := by simp
  rw [← h]
  rfl

section Triv
variable (G : Over S) [GrpObj G] [IsCommMonObj G]

def trivRig : RigLB G := ⟨Inh.trivLB _, unitGen _ _, Inh.trivLB_isLB _, unitGen_isGen _ _⟩

def trivCub : CubicalStr G (trivRig G) :=
  CubTransport.cubicalOfVal (unitGen (thφ G (x3 G)) thε) (unitGen_isGen _ _) fun _ _ _ _ =>
    ⟨fun _ _ => val_unitGen _ _ _ _ _, fun _ _ _ => (val_unitGen _ _ _ _ _).trans (val_unitGen _ _ _ _ _).symm,
      fun _ _ _ => (val_unitGen _ _ _ _ _).trans (val_unitGen _ _ _ _ _).symm,
      fun _ _ _ _ => congrArg₂ (· * ·) ((val_unitGen _ _ _ _ _).trans (val_unitGen _ _ _ _ _).symm)
        ((val_unitGen _ _ _ _ _).trans (val_unitGen _ _ _ _ _).symm)⟩

theorem cubV_trivCub {T : Over S} (z : T.left) (J) (x y u : T ⟶ G) : cubV (trivCub G) z J x y u = 1 := by
  exact val_unitGen _ _ _ _ _

def CP.triv : CP G where
  L := trivRig G
  c := trivCub G
  sym := unitGen _ _
  sym_gen := unitGen_isGen _ _
  sym_rig := corr_of_val (Inh.trivLB_isLB _) fun _ _ hJ =>
    (val_pull hJ _ _ _).trans ((val_unitGen _ _ _ _ _).trans (val_one _).symm)
  sym_cub T x y u z J _ := by
    have e : ∀ r, val (L := (trivRig G).L) (unitGen ![(ι[G]).left, 𝟙 G.left] ![1, -1]) r z J = 1 :=
      fun r => val_unitGen _ _ _ _ _
    simp only [cubV_trivCub, e, _root_.mul_one]

instance : Inhabited (CP G) := ⟨CP.triv G⟩

theorem val_sym_triv {Z : Scheme.{0}} (r : Z ⟶ G.left) (z : Z) (J) : val (CP.triv G).sym r z J = 1 := by
  exact val_unitGen _ _ _ _ _

variable {G} {H : Over S} [GrpObj H]

theorem CP.val_sym_one (P : CP G) {T : Over S} {z : T.left} {J} (hJ : Good P.L.L z J) :
    val P.sym (1 : T ⟶ G).left z J = 1 := by
  rw [one_left, ← val_pull hJ, val_corr hJ P.sym_rig, val_one]

def BiTriv.triv (i : H ⟶ G) : BiTriv (trivCub G) i where
  s := unitGen _ _
  gen := unitGen_isGen _ _
  law1 T t t' x z J _ := by
    have e : ∀ r, val (L := (trivRig G).L) (unitGen (lamφ i) Oε) r z J = 1 := fun r => val_unitGen _ _ _ _ _
    simp only [cubV_trivCub, e, _root_.mul_one]
  law2 T t x x' z J _ := by
    have e : ∀ r, val (L := (trivRig G).L) (unitGen (lamφ i) Oε) r z J = 1 := fun r => val_unitGen _ _ _ _ _
    simp only [cubV_trivCub, e, _root_.mul_one]

def CubTriv.triv (i : H ⟶ G) : CubTriv (trivCub G) i where
  s := unitGen _ _
  gen := unitGen_isGen _ _
  cub T x y u z J _ := by
    have e : ∀ r, val (L := (trivRig G).L) (unitGen ![i.left, (1 : H ⟶ G).left] ![1, -1]) r z J = 1 :=
      fun r => val_unitGen _ _ _ _ _
    simp only [cubV_trivCub, e, _root_.mul_one]

theorem CubTriv.triv_even (i : H ⟶ G) : CubTriv.Even (P := CP.triv G) (CubTriv.triv i) := by
  intro T x z J _
  erw [val_unitGen, val_unitGen, val_unitGen, _root_.mul_one]

end Triv

section Maps
variable {S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}

def toBaseHom (mul : ∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y) (T : Over S') :
    (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) := MonoidHom.mk' (toBase hw) (mul T)

theorem toBase_mul_of_isMonHom {A B : Over S} [GrpObj A] [GrpObj B] (q : A ⟶ B) [IsMonHom q]
    (hq : q.left ≫ B.hom = A.hom ≫ 𝟙 S) (T : Over S) (x y : T ⟶ A) :
    toBase hq (x * y) = toBase hq x * toBase hq y := by
  have e : ∀ a : T ⟶ A, toBase hq a = (Over.homMk (𝟙 T.left) (by simp) : Over.mk (T.hom ≫ 𝟙 S) ⟶ T) ≫ a ≫ q := by
    intro a
    ext
    simp [toBase]
  rw [e, e, e, MonObj.mul_comp, MonObj.comp_mul]

theorem toBase_mul_pullback (G : Over S) [GrpObj G] (f : S' ⟶ S) (T : Over S') (x y : T ⟶ (Over.pullback f).obj G) :
    toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f) pullback.condition (x * y) =
      toBase pullback.condition x * toBase pullback.condition y :=
  map_mul (pushHom (isGrpPullback_pullback G f) T) x y

theorem IsCPMap.triv (mul : ∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y) :
    IsCPMap (CP.triv G') (CP.triv G) f F hw ⟨fun _ => 1⟩ where
  mul := mul
  gen := by
    rw [isGen_iff]
    intro Y f' y j j' k k' _ _ _ _
    have e1 : gw (⟨fun _ => 1⟩ : LB.Iso (CP.triv G').L.L ((CP.triv G).L.L.pull F)) f' y j k = 1 := map_one _
    have e2 : gw (⟨fun _ => 1⟩ : LB.Iso (CP.triv G').L.L ((CP.triv G).L.L.pull F)) f' y j' k' = 1 := map_one _
    have e3 : gm (f' ≫ F) y _ ((CP.triv G).L.L.g j j') = 1 := map_one _
    have e4 : gm f' y _ ((CP.triv G').L.L.g k k') = 1 := map_one _
    rw [e1, e2, e3, e4, inv_one, _root_.mul_one, _root_.mul_one]
  vals := by
    intro T z J' J _ _ W hW
    have hW1 : ∀ x, W x = 1 := fun x => (hW x).trans (map_one _)
    refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
    · rw [hW1, _root_.one_mul]
      exact (val_unitGen _ _ _ _ _).trans (val_unitGen _ _ _ _ _).symm
    · rw [hW1, hW1, _root_.mul_one, _root_.one_mul]
      exact (val_unitGen _ _ _ _ _).trans (val_unitGen _ _ _ _ _).symm
    · have ha : cubV (CP.triv G).c z J (toBase hw x) (toBase hw y) (toBase hw u) = 1 := cubV_trivCub _ _ _ _ _ _
      have hb : cubV (CP.triv G').c z J' x y u = 1 := cubV_trivCub _ _ _ _ _ _
      rw [id_eq, ha, hb, hW1 (x * y), hW1 (x * u), hW1 (y * u), hW1 1, hW1 (x * y * u), hW1 x, hW1 y, hW1 u]

def idIso {X : Scheme.{0}} (L : LB X) : LB.Iso L (L.pull (𝟙 X)) :=
  ⟨fun p => res (le_inf (fun _ hx => mem_pull.1 hx.1) inf_le_right :
    (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2) (L.g (p.1 PUnit.unit) p.2)⟩

theorem gw_idIso {X Y : Scheme.{0}} (L : LB X) (r : Y ⟶ X) (y : Y) {j k : L.ι} (hj : r y ∈ L.U j) (hk : r y ∈ L.U k) :
    gw (idIso L) r y j k = gm r y _ (L.g j k) :=
  gm_res r y (V := (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k) _
    (TopologicalSpace.Opens.mem_inf.2 ⟨mem_pull.2 hj, hk⟩) _

theorem idIso_isGen {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : (idIso L).IsGen := by
  rw [isGen_iff]
  intro Y f y j j' k k' hj hj' hk hk'
  rw [gw_idIso L f y hj hk, gw_idIso L f y hj' hk', Category.comp_id]
  have c1 := congrArg Additive.ofMul (gm_cocycle hL f y hj hj' hk')
  have c2 := congrArg Additive.ofMul (gm_cocycle hL f y hj hk hk')
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at c1 c2 ⊢
  linear_combination (norm := abel) c2 - c1

theorem val_change {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (r : Z ⟶ Y) {z : Z} {J J'} (hJ : Good L z J) (hJ' : Good L z J') :
    val t r z J = (∏ k, gm (r ≫ φ k) z _ (L.g (J (r ≫ φ k)) (J' (r ≫ φ k))) ^ ε k) * val t r z J' :=
  gen_trans ht r z (hJ.mem φ r) (hJ'.mem φ r)

theorem cubV_toBase_id {L : RigLB G} (c : CubicalStr G L) (h : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 S) {T : Over S}
    (z : T.left) (J) (x y u : T ⟶ G) :
    cubV c (T := Over.mk (T.hom ≫ 𝟙 S)) z J (toBase h x) (toBase h y) (toBase h u) = cubV c z J x y u := by
  have e : ∀ a : T ⟶ G, toBase h a = (Over.homMk (𝟙 T.left) (by simp) : Over.mk (T.hom ≫ 𝟙 S) ⟶ T) ≫ a := by
    intro a
    ext
    simp [toBase]
  unfold cubV
  rw [e, e, e, ← comp_lift, ← comp_lift]
  simp only [Over.comp_left, Over.homMk_left]
  exact congrArg (fun r => val c.t r z J) (Category.id_comp _)

theorem prod_sym {T : Over S} (x : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k : Fin 2, h (x.left ≫ ![(ι[G]).left, 𝟙 G.left] k) ^ (![1, -1] : Fin 2 → ℤ) k = h (x⁻¹).left * (h x.left)⁻¹ := by
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg, Category.comp_id]
  rfl

theorem IsCPMap.id (P : CP G) : IsCPMap P P (𝟙 S) (𝟙 G.left) (by simp) (idIso P.L.L) where
  mul := fun T x y => toBase_mul_of_isMonHom (𝟙 G) _ T x y
  gen := idIso_isGen P.L.isLB
  vals := by
    intro T z J' J hJ' hJ W hW
    simp only [Category.comp_id] at hW
    have hW1 : ∀ x : T ⟶ G, W x = gm x.left z _ (P.L.L.g (J x.left) (J' x.left)) := fun x =>
      (hW x).trans (gw_idIso P.L.L x.left z (hJ x.left) (hJ' x.left))
    refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
    · rw [Category.comp_id, val_change P.L.rigGen _ hJ hJ', hW1 1, one_left]
      simp only [Fintype.prod_unique, zpow_one]
    · rw [Category.comp_id, val_change P.sym_gen _ hJ hJ',
        prod_sym x (fun ψ => gm ψ z _ (P.L.L.g (J ψ) (J' ψ))), hW1, hW1]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · have hc0 := val_change (φ := thφ G (x3 G)) (ε := thε) P.c.isGen (lift x (lift y u)).left hJ hJ'
      have hc : cubV P.c z J x y u = _ :=
        hc0.trans (congrArg (fun a => a * val P.c.t (lift x (lift y u)).left z J')
          (prod_cub x y u (fun ψ => gm ψ z _ (P.L.L.g (J ψ) (J' ψ)))))
      have hc2 : cubV P.c z J' x y u = val P.c.t (lift x (lift y u)).left z J' := rfl
      rw [id_eq, cubV_toBase_id, hc, ← hc2]
      simp only [hW1]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel

theorem one_left_comp (mul : ∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y)
    (T : Over S') : (1 : T ⟶ G').left ≫ F = (T.hom ≫ f) ≫ eSec G := by
  have h1 : toBase hw (1 : T ⟶ G') = 1 := map_one (toBaseHom mul T)
  have h2 := congrArg (fun a => a.left) h1
  simpa [toBase, one_left] using h2

theorem inv_left_comp (mul : ∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y)
    {T : Over S'} (x : T ⟶ G') : (x⁻¹).left ≫ F = (x.left ≫ F) ≫ (ι[G]).left := by
  have h1 : toBase hw x⁻¹ = (toBase hw x)⁻¹ := map_inv (toBaseHom mul T) x
  exact congrArg (fun a => a.left) h1

theorem IsCPMap.comp {P : CP G} {P' : CP G'} {P'' : CP G''} {f' : S'' ⟶ S'} {F' : G''.left ⟶ G'.left}
    {hw' : F' ≫ G'.hom = G''.hom ≫ f'} {w : LB.Iso P'.L.L (P.L.L.pull F)} {w' : LB.Iso P''.L.L (P'.L.L.pull F')}
    (h : IsCPMap P' P f F hw w) (h' : IsCPMap P'' P' f' F' hw' w')
    (hw'' : (F' ≫ F) ≫ G.hom = G''.hom ≫ f' ≫ f) {w'' : LB.Iso P''.L.L (P.L.L.pull (F' ≫ F))} (Tw : Tri w w' w'') :
    IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'' := by
  have e : ∀ (T : Over S'') (x : T ⟶ G''), toBase hw'' x =
      (Over.homMk (𝟙 T.left) (by simp) : Over.mk (T.hom ≫ f' ≫ f) ⟶ Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f)) ≫
        toBase hw (toBase hw' x) := by
    intro T x
    ext
    simp [toBase]
  have pgen : PGen w'' := Tw.pgen_comp P'.L.isLB ((isGen_iff w).1 h.gen) ((isGen_iff w').1 h'.gen)
  refine ⟨fun T x y => ?_, (isGen_iff w'').2 pgen, ?_⟩
  · rw [e, e, e, h'.mul, h.mul, MonObj.comp_mul]
  · intro T z J'' J hJ'' hJ W'' hW''
    obtain ⟨J', hJ'⟩ := exists_good_pt P'.L.isLB z
    obtain ⟨W₁, hW₁⟩ : ∃ W₁ : (Over.mk (T.hom ≫ f') ⟶ G') → (T.left.presheaf.stalk z)ˣ,
        ∀ y, W₁ y = gw w y.left z (J (y.left ≫ F)) (J' y.left) := ⟨_, fun _ => rfl⟩
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G'') → (T.left.presheaf.stalk z)ˣ,
        ∀ x, W x = gw w' x.left z (J' (x.left ≫ F')) (J'' x.left) := ⟨_, fun _ => rfl⟩
    obtain ⟨r1, s1, c1⟩ := h.vals (Over.mk (T.hom ≫ f')) z J' J hJ' hJ W₁ hW₁
    obtain ⟨r2, s2, c2⟩ := h'.vals T z J'' J' hJ'' hJ' W hW
    have t1 : toBase hw' (1 : T ⟶ G'') = 1 := map_one (toBaseHom h'.mul T)
    have tinv : ∀ x : T ⟶ G'', toBase hw' x⁻¹ = (toBase hw' x)⁻¹ := fun x => map_inv (toBaseHom h'.mul T) x
    have tmul : ∀ x y : T ⟶ G'', toBase hw' (x * y) = toBase hw' x * toBase hw' y := h'.mul T
    have tl : ∀ x : T ⟶ G'', (toBase hw' x).left = x.left ≫ F' := fun _ => rfl
    have hrel : ∀ x : T ⟶ G'', W'' x = W₁ (toBase hw' x) * W x := by
      intro x
      have hm1 : F (F' (x.left z)) ∈ P.L.L.U (J (x.left ≫ F' ≫ F)) := hJ _
      have hm2 : F' (x.left z) ∈ P'.L.L.U (J' (x.left ≫ F')) := hJ' _
      have hm3 : x.left z ∈ P''.L.L.U (J'' x.left) := hJ'' _
      rw [hW'', Tw T.left x.left z _ _ _ hm1 hm2 hm3, hW₁, hW, tl, Category.assoc]
    refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
    · simp only [Over.mk_hom] at r1
      rw [hrel, t1, _root_.mul_assoc, ← r2, ← r1, Category.assoc]
    · have s1' := s1 (toBase hw' x)
      have s2' := s2 x
      rw [tl, Category.assoc, ← tinv] at s1'
      rw [hrel, hrel]
      apply Additive.ofMul.injective
      replace s1' := congrArg Additive.ofMul s1'
      replace s2' := congrArg Additive.ofMul s2'
      simp only [ofMul_mul] at s1' s2' ⊢
      linear_combination (norm := abel) s1' + s2'
    · have c1' := c1 (toBase hw' x) (toBase hw' y) (toBase hw' u)
      have c2' := c2 x y u
      have hcub : cubV P.c (T := Over.mk (T.hom ≫ f' ≫ f)) z J (toBase hw'' x) (toBase hw'' y) (toBase hw'' u) =
          cubV P.c z J (toBase hw (toBase hw' x)) (toBase hw (toBase hw' y)) (toBase hw (toBase hw' u)) := by
        unfold cubV
        rw [e, e, e, ← comp_lift, ← comp_lift]
        simp only [Over.comp_left, Over.homMk_left]
        exact congrArg (fun r => val P.c.t r z J) (Category.id_comp _)
      simp only [← tmul, ← t1, id_eq] at c1'
      simp only [id_eq] at c2' ⊢
      rw [hcub]
      simp only [hrel]
      apply Additive.ofMul.injective
      replace c1' := congrArg Additive.ofMul c1'
      replace c2' := congrArg Additive.ofMul c2'
      simp only [ofMul_mul] at c1' c2' ⊢
      linear_combination (norm := abel) c1' + c2'

theorem IsCPMap.exists_comp {P : CP G} {P' : CP G'} {P'' : CP G''} {f' : S'' ⟶ S'} {F' : G''.left ⟶ G'.left}
    {hw' : F' ≫ G'.hom = G''.hom ≫ f'} {w : LB.Iso P'.L.L (P.L.L.pull F)} {w' : LB.Iso P''.L.L (P'.L.L.pull F')}
    (h : IsCPMap P' P f F hw w) (h' : IsCPMap P'' P' f' F' hw' w')
    (hw'' : (F' ≫ F) ≫ G.hom = G''.hom ≫ f' ≫ f) :
    ∃ w'', Tri w w' w'' ∧ IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'' := by
  obtain ⟨w'', Tw⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_comp P'.L.isLB w w' ((isGen_iff w).1 h.gen)
    ((isGen_iff w').1 h'.gen) P.L.isLB P''.L.isLB
  exact ⟨w'', Tw, h.comp h' hw'' Tw⟩

theorem cub_alg {U : Type} [CommGroup U] {C C' a b c d e g h k : U}
    (H : C = a * b⁻¹ * c⁻¹ * d⁻¹ * e * g * h * k⁻¹ * C') : C * b * c * d * k = a * e * g * h * C' := by
  subst H
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem sym_cub_alg {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] (β : A' →* A) (W : A' → U)
    {θ : A → A → A → U} {θ' : A' → A' → A' → U} {σ : A → U} {σ' : A' → U}
    (hθ : ∀ a b d, θ (β a) (β b) (β d) = W (a * b * d) * (W (a * b))⁻¹ * (W (a * d))⁻¹ * (W (b * d))⁻¹ * W a * W b *
      W d * (W 1)⁻¹ * θ' a b d) (hσ : ∀ a, σ (β a) = W a⁻¹ * (W a)⁻¹ * σ' a) {x y u : A'}
    (e : θ (β x)⁻¹ (β y)⁻¹ (β u)⁻¹ * σ (β x * β y) * σ (β x * β u) * σ (β y * β u) =
      θ (β x) (β y) (β u) * σ (β x * β y * β u) * σ (β x) * σ (β y) * σ (β u)) :
    θ' x⁻¹ y⁻¹ u⁻¹ * σ' (x * y) * σ' (x * u) * σ' (y * u) =
      θ' x y u * σ' (x * y * u) * σ' x * σ' y * σ' u := by
  have h1 := congrArg Additive.ofMul (hθ x⁻¹ y⁻¹ u⁻¹)
  have h2 := congrArg Additive.ofMul (hθ x y u)
  have s1 := congrArg Additive.ofMul (hσ (x * y))
  have s2 := congrArg Additive.ofMul (hσ (x * u))
  have s3 := congrArg Additive.ofMul (hσ (y * u))
  have s4 := congrArg Additive.ofMul (hσ (x * y * u))
  have s5 := congrArg Additive.ofMul (hσ x)
  have s6 := congrArg Additive.ofMul (hσ y)
  have s7 := congrArg Additive.ofMul (hσ u)
  have e' := congrArg Additive.ofMul e
  apply Additive.ofMul.injective
  simp only [map_mul, map_inv, mul_inv, ofMul_mul, ofMul_inv] at h1 h2 s1 s2 s3 s4 s5 s6 s7 e' ⊢
  linear_combination (norm := abel) e' - h1 + h2 - s1 - s2 - s3 + s4 + s5 + s6 + s7

theorem exists_isCPMap (P : CP G)
    (mul : ∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y)
    (L' : LB G'.left) (hL' : L'.IsLB) (w : LB.Iso L' (P.L.L.pull F)) (hg : w.IsGen) :
    ∃ (rig : LB.Gen (L'.pull (eSec G'))) (hr : rig.IsGen) (c : CubicalStr G' ⟨L', rig, hL', hr⟩) (s : _) (h₁ : _)
      (h₂ : _) (h₃ : _), IsCPMap ⟨⟨L', rig, hL', hr⟩, c, s, h₁, h₂, h₃⟩ P f F hw w := by
  have hw' : PGen w := (isGen_iff w).1 hg
  have hL := P.L.isLB
  have he : eSec G' ≫ F = f ≫ eSec G := by
    have h1 := one_left_comp mul (𝟙_ (Over S'))
    rw [one_left] at h1
    simpa using h1
  obtain ⟨rig, hr, hrm⟩ := CubTransport.exists_pmaps hw' hL hL' (φ' := fun _ : PUnit => eSec G')
    (φ := fun _ => eSec G) (ε := fun _ => 1) f (fun _ => he) P.L.rig P.L.rigGen
  have hc2 : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ F = F ≫ ![(ι[G]).left, 𝟙 G.left] k := by
    have h0 : ((𝟙 G' : G' ⟶ G').left ≫ (ι[G']).left) ≫ F = ((𝟙 G' : G' ⟶ G').left ≫ F) ≫ (ι[G]).left :=
      inv_left_comp mul (𝟙 G')
    intro k
    fin_cases k
    · simpa using h0
    · simp
  obtain ⟨s, hs, hsm⟩ := CubTransport.exists_pmaps hw' hL hL' (φ' := ![(ι[G']).left, 𝟙 G'.left])
    (φ := ![(ι[G]).left, 𝟙 G.left]) (ε := ![1, -1]) F hc2 P.sym P.sym_gen
  let σ : Over.mk ((G3 G').hom ≫ f) ⟶ G3 G :=
    lift (toBase hw (x3 G' 0)) (lift (toBase hw (x3 G' 1)) (toBase hw (x3 G' 2)))
  have hσ : ∀ i, σ ≫ x3 G i = toBase hw (x3 G' i) := by
    intro i
    fin_cases i <;> simp [σ, x3]
  have hc3 : ∀ I : thK, thφ G' (x3 G') I ≫ F = σ.left ≫ thφ G (x3 G) I := by
    intro I
    have e1 : toBase hw (psum G' (x3 G') I.down) = psum G (fun i => toBase hw (x3 G' i)) I.down :=
      psum_hom (toBaseHom mul (G3 G')) (x3 G') I.down
    have e2 : σ ≫ psum G (x3 G) I.down = psum G (fun i => σ ≫ x3 G i) I.down := psum_hom (preHom σ) (x3 G) I.down
    simp only [hσ] at e2
    have e3 := congrArg Over.Hom.left (e1.trans e2.symm)
    show (psum G' (x3 G') I.down).left ≫ F = σ.left ≫ (psum G (x3 G) I.down).left
    simpa [toBase] using e3
  obtain ⟨t', ht', htm⟩ := CubTransport.exists_pmaps hw' hL hL' (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G))
    (ε := thε) σ.left hc3 P.c.t P.c.isGen
  have key1 : ∀ (T : Over S') (z : T.left) (J0 : (T.left ⟶ G.left) → P.L.L.ι) (J : (T.left ⟶ G'.left) → L'.ι),
      Good P.L.L z J0 → Good L' z J →
      val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig (T.hom ≫ f) z J0 =
        gw w (1 : T ⟶ G').left z (J0 ((1 : T ⟶ G').left ≫ F)) (J (1 : T ⟶ G').left) * val rig T.hom z J := by
    intro T z J0 J hJ0 hJ
    rw [CubTransport.val_pmaps (fun _ => he) hrm T.hom hJ0 hJ, one_left]
    simp only [Fintype.prod_unique, zpow_one]
  have key2 : ∀ (T : Over S') (z : T.left) (J0 : (T.left ⟶ G.left) → P.L.L.ι) (J : (T.left ⟶ G'.left) → L'.ι),
      Good P.L.L z J0 → Good L' z J → ∀ a : T ⟶ G',
      val P.sym (a.left ≫ F) z J0 = gw w (a⁻¹).left z (J0 ((a⁻¹).left ≫ F)) (J (a⁻¹).left) *
        (gw w a.left z (J0 (a.left ≫ F)) (J a.left))⁻¹ * val s a.left z J := by
    intro T z J0 J hJ0 hJ a
    rw [CubTransport.val_pmaps hc2 hsm a.left hJ0 hJ, prod_sym a (fun ψ => gw w ψ z (J0 (ψ ≫ F)) (J ψ))]
  have key3 : ∀ (T : Over S') (z : T.left) (J0 : (T.left ⟶ G.left) → P.L.L.ι) (J : (T.left ⟶ G'.left) → L'.ι),
      Good P.L.L z J0 → Good L' z J → ∀ a b c : T ⟶ G',
      cubV P.c z J0 (toBase hw a) (toBase hw b) (toBase hw c) =
        gw w (a * b * c).left z (J0 ((a * b * c).left ≫ F)) (J (a * b * c).left) *
        (gw w (a * b).left z (J0 ((a * b).left ≫ F)) (J (a * b).left))⁻¹ *
        (gw w (a * c).left z (J0 ((a * c).left ≫ F)) (J (a * c).left))⁻¹ *
        (gw w (b * c).left z (J0 ((b * c).left ≫ F)) (J (b * c).left))⁻¹ *
        gw w a.left z (J0 (a.left ≫ F)) (J a.left) * gw w b.left z (J0 (b.left ≫ F)) (J b.left) *
        gw w c.left z (J0 (c.left ≫ F)) (J c.left) *
        (gw w (1 : T ⟶ G').left z (J0 ((1 : T ⟶ G').left ≫ F)) (J (1 : T ⟶ G').left))⁻¹ *
        val (φ := thφ G' (x3 G')) (ε := thε) t' (lift a (lift b c)).left z J := by
    intro T z J0 J hJ0 hJ a b c
    let ρ : Over.mk (T.hom ≫ f) ⟶ Over.mk ((G3 G').hom ≫ f) := Over.homMk (lift a (lift b c)).left (by
      show (lift a (lift b c)).left ≫ (G3 G').hom ≫ f = T.hom ≫ f
      rw [← Category.assoc, Over.w])
    have q : ∀ (i : Fin 3) (d : T ⟶ G'), lift a (lift b c) ≫ x3 G' i = d → toBase hw d = ρ ≫ toBase hw (x3 G' i) := by
      intro i d hd
      ext
      show d.left ≫ F = (lift a (lift b c)).left ≫ ((x3 G' i).left ≫ F)
      rw [← Category.assoc, ← Over.comp_left, hd]
    have hl : lift (toBase hw a) (lift (toBase hw b) (toBase hw c)) = ρ ≫ σ := by
      simp only [σ, comp_lift]
      rw [← q 0 a (by simp [x3]), ← q 1 b (by simp [x3]), ← q 2 c (by simp [x3])]
    have e' : cubV P.c z J0 (toBase hw a) (toBase hw b) (toBase hw c) =
        val (φ := thφ G (x3 G)) (ε := thε) P.c.t ((lift a (lift b c)).left ≫ σ.left) z J0 := by
      show val (φ := thφ G (x3 G)) (ε := thε) P.c.t (lift (toBase hw a) (lift (toBase hw b) (toBase hw c))).left z J0 = _
      rw [hl]
      rfl
    rw [e', CubTransport.val_pmaps hc3 htm (lift a (lift b c)).left hJ0 hJ]
    congr 1
    exact prod_cub a b c (fun ψ => gw w ψ z (J0 (ψ ≫ F)) (J ψ))
  have hcub : ∀ (T : Over S') (z : T.left) (J : (T.left ⟶ G'.left) → L'.ι), Good L' z J →
      IsCub (CubTransport.thV (L := ⟨L', rig, hL', hr⟩) t' z J) := by
    intro T z J hJ
    obtain ⟨J0, hJ0⟩ := exists_good_pt hL z
    exact CubTransport.isCub_of_twist (isCub_cubV (T := Over.mk (T.hom ≫ f)) P.c hJ0) (toBaseHom mul T)
      (fun a => gw w a.left z (J0 (a.left ≫ F)) (J a.left)) (fun a b c => key3 T z J0 J hJ0 hJ a b c)
  let c : CubicalStr G' ⟨L', rig, hL', hr⟩ := CubTransport.cubicalOfVal t' ht' hcub
  have hsr : LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ s (eSec G')) (LB.oneGen L') := by
    refine corr_of_val hL' fun y J hJ => ?_
    rw [val_pull hJ, val_one]
    obtain ⟨J0, hJ0⟩ := exists_good_pt hL y
    have k := key2 (𝟙_ (Over S')) y J0 J hJ0 hJ 1
    have one1 : (1 : 𝟙_ (Over S') ⟶ G').left = (𝟙_ (Over S')).hom ≫ eSec G' := one_left G' (𝟙_ (Over S'))
    rw [inv_one, _root_.mul_inv_cancel, _root_.one_mul, one1] at k
    have r1 : val P.sym (((𝟙_ (Over S')).hom ≫ f) ≫ eSec G) y J0 = 1 :=
      (val_pull hJ0 P.sym (eSec G) ((𝟙_ (Over S')).hom ≫ f)).symm.trans ((val_corr hJ0 P.sym_rig _).trans (val_one _))
    show val s ((𝟙_ (Over S')).hom ≫ eSec G') y J = 1
    rw [← k, Category.assoc, he, ← Category.assoc, r1]
  have hsc : ∀ (T : Over S') (x y u : T ⟶ G') (z : T.left) (J : (T.left ⟶ G'.left) → L'.ι), Good L' z J →
      cubV c z J x⁻¹ y⁻¹ u⁻¹ * val s (x * y).left z J * val s (x * u).left z J * val s (y * u).left z J =
        cubV c z J x y u * val s (x * y * u).left z J * val s x.left z J * val s y.left z J * val s u.left z J := by
    intro T x y u z J hJ
    obtain ⟨J0, hJ0⟩ := exists_good_pt hL z
    exact sym_cub_alg (toBaseHom mul T) (fun a => gw w a.left z (J0 (a.left ≫ F)) (J a.left))
      (θ := cubV (T := Over.mk (T.hom ≫ f)) P.c z J0) (θ' := cubV c z J) (σ := fun a => val P.sym a.left z J0) (σ' := fun a => val s a.left z J)
      (fun a b d => key3 T z J0 J hJ0 hJ a b d) (fun a => key2 T z J0 J hJ0 hJ a)
      (P.sym_cub (Over.mk (T.hom ≫ f)) (toBase hw x) (toBase hw y) (toBase hw u) z J0 hJ0)
  refine ⟨rig, hr, c, s, hs, hsr, hsc, mul, hg, ?_⟩
  intro T z J' J hJ' hJ W hW
  dsimp only
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · rw [key1 T z J J' hJ hJ', hW]
  · rw [key2 T z J J' hJ hJ' x, hW, hW]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have hc' : cubV c z J' x y u = val (φ := thφ G' (x3 G')) (ε := thε) t' (lift x (lift y u)).left z J' := rfl
    rw [id_eq, key3 T z J J' hJ hJ' x y u, hc']
    simp only [hW]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

def pullIso {X Y : Scheme.{0}} (L : LB X) (F : Y ⟶ X) : LB.Iso (L.pull F) (L.pull F) :=
  ⟨fun p => (L.pull F).g p.1 p.2⟩

theorem pullIso_isGen {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) : (pullIso L F).IsGen := by
  rw [isGen_iff]
  intro Y f y j j' k k' hj hj' hk hk'
  have hk1 : F (f y) ∈ L.U (k PUnit.unit) := mem_pull.1 hk
  have hk1' : F (f y) ∈ L.U (k' PUnit.unit) := mem_pull.1 hk'
  have key : ∀ (a b : PUnit → L.ι), f y ∈ (L.pull F).U a ⊓ (L.pull F).U b →
      gm f y _ ((L.pull F).g a b) =
        gm (f ≫ F) y (L.U (a PUnit.unit) ⊓ L.U (b PUnit.unit)) (L.g (a PUnit.unit) (b PUnit.unit)) := by
    intro a b hab
    have hF : F (f y) ∈ L.U (a PUnit.unit) ⊓ L.U (b PUnit.unit) :=
      TopologicalSpace.Opens.mem_inf.2 ⟨mem_pull.1 (TopologicalSpace.Opens.mem_inf.1 hab).1,
        mem_pull.1 (TopologicalSpace.Opens.mem_inf.1 hab).2⟩
    rw [← gm_pull f F y _ hF]
    unfold LB.pull LB.LinComb
    simp only [Fintype.prod_unique, zpow_one]
    exact gm_res f y _ hab _
  have g1 : gw (pullIso L F) f y j k = gm (f ≫ F) y _ (L.g j (k PUnit.unit)) :=
    key (fun _ => j) k (TopologicalSpace.Opens.mem_inf.2 ⟨mem_pull.2 hj, hk⟩)
  have g2 : gw (pullIso L F) f y j' k' = gm (f ≫ F) y _ (L.g j' (k' PUnit.unit)) :=
    key (fun _ => j') k' (TopologicalSpace.Opens.mem_inf.2 ⟨mem_pull.2 hj', hk'⟩)
  rw [g1, g2, key k k' (TopologicalSpace.Opens.mem_inf.2 ⟨hk, hk'⟩)]
  have c1 := congrArg Additive.ofMul (gm_cocycle hL (f ≫ F) y hj hj' hk1')
  have c2 := congrArg Additive.ofMul (gm_cocycle hL (f ≫ F) y hj hk1 hk1')
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at c1 c2 ⊢
  linear_combination (norm := abel) c2 - c1

theorem exists_pull (P : CP G)
    (mul : ∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y) :
    ∃ (P' : CP G') (w : _), IsCPMap P' P f F hw w := by
  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, H⟩ :=
    exists_isCPMap P mul (P.L.L.pull F) (pull_isLB P.L.isLB F) (pullIso P.L.L F) (pullIso_isGen P.L.isLB F)
  exact ⟨_, _, H⟩

end Maps

theorem exists_isLevelCP {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (P : CP G) :
    ∃ P' : CP (thickObj R I e G), IsLevelCP I e P' P := by
  obtain ⟨P', w, H⟩ := exists_pull P (toBase_mul_pullback G (thick R I e))
  exact ⟨P', w, H⟩

theorem isLevelCP_triv {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] :
    IsLevelCP I e (CP.triv (thickObj R I e G)) (CP.triv G) :=
  ⟨_, IsCPMap.triv (toBase_mul_pullback G (thick R I e))⟩

section Abelian
variable {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem sym_cub_of_surjective (h3 : Function.Surjective (G3 G).hom.appTop.hom) {L : RigLB G} (c : CubicalStr G L)
    (sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : sym.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L))
    (T : Over S) (x y u : T ⟶ G) (z : T.left) (J) (hJ : Good L.L z J) :
    cubV c z J x⁻¹ y⁻¹ u⁻¹ * val sym (x * y).left z J * val sym (x * u).left z J * val sym (y * u).left z J =
      cubV c z J x y u * val sym (x * y * u).left z J * val sym x.left z J * val sym y.left z J *
        val sym u.left z J := by
  have hq : ∀ {T' : Over S} (a b d : T' ⟶ G), lift a (lift b d) ≫ x3 G 0 = a ∧ lift a (lift b d) ≫ x3 G 1 = b ∧
      lift a (lift b d) ≫ x3 G 2 = d := fun a b d => by simp [x3]
  let g1 := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift (x3 G 0)⁻¹ (lift (x3 G 1)⁻¹ (x3 G 2)⁻¹)).left)
      (LB.pullGen L.L _ _ sym (x3 G 0 * x3 G 1).left))
      (LB.pullGen L.L _ _ sym (x3 G 0 * x3 G 2).left))
      (LB.pullGen L.L _ _ sym (x3 G 1 * x3 G 2).left)
  let g2 := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift (x3 G 0) (lift (x3 G 1) (x3 G 2))).left)
      (LB.pullGen L.L _ _ sym (x3 G 0 * x3 G 1 * x3 G 2).left))
      (LB.pullGen L.L _ _ sym (x3 G 0).left))
      (LB.pullGen L.L _ _ sym (x3 G 1).left))
      (LB.pullGen L.L _ _ sym (x3 G 2).left)
  have hg1 : g1.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _) (DVR.pullGen_isGen _ _ _ _ hs _))
    (DVR.pullGen_isGen _ _ _ _ hs _)) (DVR.pullGen_isGen _ _ _ _ hs _)
  have hg2 : g2.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _) (DVR.pullGen_isGen _ _ _ _ hs _))
    (DVR.pullGen_isGen _ _ _ _ hs _)) (DVR.pullGen_isGen _ _ _ _ hs _)) (DVR.pullGen_isGen _ _ _ _ hs _)

  have vals3 : ∀ {T' : Over S} (a b d : T' ⟶ G) (w : T'.left) (J' : (T'.left ⟶ G.left) → L.L.ι), Good L.L w J' →
      val g1 (lift a (lift b d)).left w J' = cubV c w J' a⁻¹ b⁻¹ d⁻¹ * val sym (a * b).left w J' *
        val sym (a * d).left w J' * val sym (b * d).left w J' ∧
      val g2 (lift a (lift b d)).left w J' = cubV c w J' a b d * val sym (a * b * d).left w J' *
        val sym a.left w J' * val sym b.left w J' * val sym d.left w J' := by
    intro T' a b d w J' hJ'
    obtain ⟨h0, h1, h2⟩ := hq a b d
    constructor
    · rw [val_mul hJ', val_mul hJ']
      erw [val_mul hJ', val_cub c (lift a (lift b d)) hJ']
      rw [val_pull hJ', val_pull hJ', val_pull hJ']
      simp only [← Over.comp_left, MonObj.comp_mul, GrpObj.comp_inv, h0, h1, h2]
    · rw [val_mul hJ', val_mul hJ', val_mul hJ']
      erw [val_mul hJ', val_cub c (lift a (lift b d)) hJ']
      rw [val_pull hJ', val_pull hJ', val_pull hJ', val_pull hJ']
      simp only [← Over.comp_left, MonObj.comp_mul, h0, h1, h2]
  clear_value g1 g2

  have hone : ∀ (w : (𝟙_ (Over S)).left) (J'), Good L.L w J' → val sym (1 : 𝟙_ (Over S) ⟶ G).left w J' = 1 := by
    intro w J' hJ'
    rw [one_left G (𝟙_ (Over S))]
    have e1 := val_corr hJ' hr (𝟙_ (Over S)).hom
    rwa [val_pull hJ', val_one] at e1

  have hagree : ∀ w J', Good L.L w J' → val g1 (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left w J' =
      val g2 (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left w J' := by
    intro w J' hJ'
    rw [(vals3 1 1 1 w J' hJ').1, (vals3 1 1 1 w J' hJ').2]
    simp only [inv_one, _root_.mul_one, hone w J' hJ', (isCub_cubV c hJ').face]
  have key : val g1 (lift x (lift y u)).left z J = val g2 (lift x (lift y u)).left z J := by
    refine gen_unique' L.isLB ?_ (G3 G).hom (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left
      (Over.w (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1))) h3 hg1 hg2 hagree T.left _ z J hJ
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    erw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, prod_sym]
    erw [prod_cub, prod_cub]
    simp only [_root_.mul_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [(vals3 x y u z J hJ).1, (vals3 x y u z J hJ).2] at key
  exact key

def CP.ofSurjective (h3 : Function.Surjective (G3 G).hom.appTop.hom) (L : RigLB G) (c : CubicalStr G L)
    (sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : sym.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L)) : CP G :=
  ⟨L, c, sym, hs, hr, sym_cub_of_surjective h3 c sym hs hr⟩

theorem surjective_cube (hG : GlobalFnsSt) (hA : IsAbelianScheme G) : Function.Surjective (G3 G).hom.appTop.hom := by
  have h1 : Function.Surjective G.hom.appTop.hom := (hG S G hA).2
  have h2 : Function.Surjective (G ⊗ G).hom.appTop.hom := by
    rw [← Over.w (snd G G)]
    exact surj_comp (surj_snd hG hA G) h1
  have h3 : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom := by
    rw [← Over.w (snd G (G ⊗ G))]
    exact surj_comp (surj_snd hG hA (G ⊗ G)) h2
  exact h3

def CP.ofDegPre (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : CP D.P.A :=
  CP.ofSurjective (surjective_cube hG D.P.isAb) ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ D.cub D.sym D.sym_gen D.sym_rig

end Abelian

section Weil
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {L : RigLB G} {c : CubicalStr G L} {N : ℕ}
  {T : Over S} {x y : T ⟶ G}

theorem CubWeil.unique {ζ ζ' : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) (h' : CubWeil c N x y ζ') : ζ = ζ' := by
  refine unit_ext fun p _ => ?_
  obtain ⟨J, hJ⟩ := exists_good_pt L.isLB p
  exact mul_right_cancel ((h.2.2 p J hJ).trans (h'.2.2 p J hJ).symm)

theorem cubWeil_iff_isRatio {ζ : Γ(T.left, ⊤)ˣ} :
    CubWeil c N x y ζ ↔ x ^ N = 1 ∧ y ^ N = 1 ∧ WeilCube.IsRatio c N x y ζ := by
  have at1 : ∀ {e : Γ(T.left, ⊤)ˣ}, WeilCube.IsRatio c N x y e → ∀ (z : T.left) (J), Good L.L z J →
      gm (𝟙 T.left) z ⊤ e * cubN (cubV c z J) N 1 x y = cubN (cubV c z J) N 1 y x := by
    intro e he z J hJ
    simpa only [Over.id_left, Category.id_comp] using he T (𝟙 T) z J hJ
  constructor
  · rintro ⟨hx, hy, h⟩
    obtain ⟨e, he⟩ := WeilCube.exists_isRatio c N x y hx hy
    have hζ : ζ = e := CubWeil.unique ⟨hx, hy, h⟩ ⟨hx, hy, at1 he⟩
    exact ⟨hx, hy, hζ ▸ he⟩
  · rintro ⟨hx, hy, h⟩
    exact ⟨hx, hy, at1 h⟩

theorem existsUnique_cubWeil (c : CubicalStr G L) (hx : x ^ N = 1) (hy : y ^ N = 1) : ∃! ζ, CubWeil c N x y ζ := by
  obtain ⟨e, he⟩ := WeilCube.exists_isRatio c N x y hx hy
  have h0 : CubWeil c N x y e := cubWeil_iff_isRatio.2 ⟨hx, hy, he⟩
  exact ⟨e, h0, fun ζ hζ => CubWeil.unique hζ h0⟩

theorem CubWeil.symm {ζ : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) : CubWeil c N y x ζ⁻¹ := by
  refine ⟨h.2.1, h.1, fun z J hJ => ?_⟩
  rw [map_inv, ← h.2.2 z J hJ, inv_mul_cancel_left]

theorem cubWeil_self (c : CubicalStr G L) (hx : x ^ N = 1) : CubWeil c N x x 1 := by
  exact ⟨hx, hx, fun z J _ => by rw [map_one, _root_.one_mul]⟩

theorem CubWeil.comp {ζ : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) {T' : Over S} (σ : T' ⟶ T) :
    CubWeil c N (σ ≫ x) (σ ≫ y) (Units.map σ.left.appTop.hom.toMonoidHom ζ) := by
  obtain ⟨hx, hy, hr⟩ := cubWeil_iff_isRatio.1 h
  have hp : ∀ a : T ⟶ G, a ^ N = 1 → (σ ≫ a) ^ N = 1 := fun a ha => by
    rw [← MonObj.comp_pow, ha, MonObj.comp_one]
  exact cubWeil_iff_isRatio.2 ⟨hp x hx, hp y hy, WeilCube.IsRatio.comp c hr σ⟩

theorem cubWeil_iff_weilIs (hG : GlobalFnsSt) (hA : IsAbelianScheme G) (hx : x ^ N = 1) (hy : y ^ N = 1)
    (ζ : Γ(T.left, ⊤)ˣ) : CubWeil c N x y ζ ↔ WeilIs G L.L N x y ζ := by
  obtain ⟨e, he⟩ := WeilCube.exists_isRatio c N x y hx hy
  have h0 : CubWeil c N x y e := cubWeil_iff_isRatio.2 ⟨hx, hy, he⟩
  rw [WeilCube.weilIs_iff c hG hA hx hy he ζ]
  exact ⟨fun h => CubWeil.unique h h0, fun h => h ▸ h0⟩

theorem cubWeil_triv (hx : x ^ N = 1) (hy : y ^ N = 1) : CubWeil (trivCub G) N x y 1 := by
  refine ⟨hx, hy, fun z J _ => ?_⟩
  simp only [cubN, cubV_trivCub, Finset.prod_const_one, map_one, _root_.one_mul]

variable {i : H ⟶ G} {z : T.left} {J : (T.left ⟶ G.left) → L.L.ι}

theorem BiTriv.val_one_right (σ : BiTriv c i) (hJ : Good L.L z J) (t : T ⟶ H) :
    val σ.s (lift t (1 : T ⟶ G)).left z J = 1 := by
  have e := σ.law2 T t 1 1 z J hJ
  simp only [_root_.mul_one, (isCub_cubV c hJ).face₂, _root_.one_mul] at e
  exact mul_left_cancel (e.symm.trans (_root_.mul_one _).symm)

theorem BiTriv.val_one_left [IsMonHom i] (σ : BiTriv c i) (hJ : Good L.L z J) (x : T ⟶ G) :
    val σ.s (lift (1 : T ⟶ H) x).left z J = 1 := by
  have e := σ.law1 T 1 1 x z J hJ
  simp only [_root_.mul_one, MonObj.one_comp, (isCub_cubV c hJ).face, _root_.one_mul] at e
  exact mul_left_cancel (e.symm.trans (_root_.mul_one _).symm)

theorem BiTriv.cubWeil [IsMonHom i] (σ : BiTriv c i) {t : T ⟶ H} (ht : t ^ N = 1) (hx : x ^ N = 1) :
    CubWeil c N (t ≫ i) x 1 := by
  refine ⟨by rw [← MonObj.pow_comp, ht, MonObj.one_comp], hx, fun z J hJ => ?_⟩
  have hcub := isCub_cubV c hJ
  have tele : ∀ (f g : ℕ → (T.left.presheaf.stalk z)ˣ) (a : (T.left.presheaf.stalk z)ˣ), f N = f 0 →
      (∀ k, g k = f (k + 1) / f k * a⁻¹) → ∏ k ∈ Finset.range N, g k = (a ^ N)⁻¹ := by
    intro f g a hN hg
    rw [Finset.prod_congr rfl fun k _ => hg k, Finset.prod_mul_distrib, Finset.prod_range_div, hN, div_self',
      Finset.prod_const, Finset.card_range, _root_.one_mul, inv_pow]
  have A : cubN (cubV c z J) N 1 (t ≫ i) x = ((val σ.s (lift t x).left z J) ^ N)⁻¹ := by
    refine tele (fun k => val σ.s (lift (t ^ k) x).left z J) (fun k => cubV c z J (1 * (t ≫ i) ^ k) (t ≫ i) x) _
      (by simp only [ht, pow_zero]) fun k => ?_
    have e := σ.law1 T (t ^ k) t x z J hJ
    rw [← pow_succ] at e
    simp only [_root_.one_mul, ← MonObj.pow_comp]
    rw [e]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv]
    abel
  have B : cubN (cubV c z J) N 1 x (t ≫ i) = ((val σ.s (lift t x).left z J) ^ N)⁻¹ := by
    refine tele (fun k => val σ.s (lift t (x ^ k)).left z J) (fun k => cubV c z J (1 * x ^ k) x (t ≫ i)) _
      (by simp only [hx, pow_zero]) fun k => ?_
    have e := σ.law2 T t (x ^ k) x z J hJ
    rw [← pow_succ] at e
    simp only [_root_.one_mul]
    rw [hcub.s12 (x ^ k) x (t ≫ i), hcub.s01 (x ^ k) (t ≫ i) x, e]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv]
    abel
  rw [map_one, _root_.one_mul, A, B]

theorem CubTriv.val_one [IsMonHom i] (σ : CubTriv c i) (hJ : Good L.L z J) : val σ.s (1 : T ⟶ H).left z J = 1 := by
  have e := σ.cub T 1 1 1 z J hJ
  simp only [_root_.mul_one, MonObj.one_comp, (isCub_cubV c hJ).face, _root_.one_mul] at e
  exact mul_left_cancel (e.trans (_root_.mul_one _).symm)

end Weil

section Torus
variable {X : Type} [AddCommGroup X]

def chV {Z : Over S} (t : Z ⟶ splitTorus S X) (χ : X) : Γ(Z.left, ⊤)ˣ :=
  splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd χ)

theorem chV_val {Z : Over S} (t : Z ⟶ splitTorus S X) (χ : X) :
    (chV t χ).val = t.left.appTop.hom (charUnit S X χ).val := by
  exact splitTorusPointsEquiv_val S X Z t χ

theorem chV_mul {Z : Over S} (t t' : Z ⟶ splitTorus S X) (χ : X) : chV (t * t') χ = chV t χ * chV t' χ := by
  simp only [chV, map_mul, MonoidHom.mul_apply]

theorem chV_inv {Z : Over S} (t : Z ⟶ splitTorus S X) (χ : X) : chV t⁻¹ χ = (chV t χ)⁻¹ := by
  simp only [chV, map_inv, MonoidHom.inv_apply]

theorem chV_add {Z : Over S} (t : Z ⟶ splitTorus S X) (χ χ' : X) : chV t (χ + χ') = chV t χ * chV t χ' := by
  simp only [chV, ofAdd_add, map_mul]

theorem chV_zero {Z : Over S} (t : Z ⟶ splitTorus S X) : chV t 0 = 1 := by
  simp only [chV, ofAdd_zero, map_one]

theorem gm_charUnit {Z : Over S} (t : Z ⟶ splitTorus S X) (z : Z.left) (χ : X) :
    gm t.left z ⊤ (charUnit S X χ) = gm (𝟙 Z.left) z ⊤ (chV t χ) := by
  rw [gm_top]
  congr 1
  ext
  rw [chV_val]
  rfl

section Twist
variable {G : Over S} [GrpObj G] [IsCommMonObj G] {i : splitTorus S X ⟶ G}

def CubTriv.twist {L : RigLB G} {c : CubicalStr G L} (σ : CubTriv c i) (χ : X) : CubTriv c i where
  s := scaleGen (charUnit S X χ) σ.s
  gen := scaleGen_isGen _ σ.gen
  cub T x y u z J hJ := by
    have e := σ.cub T x y u z J hJ
    simp only [val_scaleGen _ _ _ hJ, gm_charUnit, chV_mul, map_mul]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul] at e' ⊢
    linear_combination (norm := abel) e'

theorem CubTriv.val_twist {L : RigLB G} {c : CubicalStr G L} (σ : CubTriv c i) (χ : X) {T : Over S}
    (x : T ⟶ splitTorus S X) {z : T.left} {J} (hJ : Good L.L z J) :
    val (σ.twist χ).s x.left z J = gm (𝟙 T.left) z ⊤ (chV x χ) * val σ.s x.left z J := by
  show val (scaleGen (charUnit S X χ) σ.s) x.left z J = _
  rw [val_scaleGen _ _ _ hJ, gm_charUnit]

theorem CubTriv.twist_even_iff {P : CP G} {σ : CubTriv P.c i} (hσ : σ.Even) (χ : X) :
    (σ.twist χ).Even ↔ ∀ (T : Over S) (t : T ⟶ splitTorus S X), chV t (χ + χ) = 1 := by
  constructor
  · intro htw T t
    apply unit_ext
    intro z _
    obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    have h1 := htw T t z J hJ
    have h0 := hσ T t z J hJ
    rw [CubTriv.val_twist _ _ _ hJ, CubTriv.val_twist _ _ _ hJ, h0, chV_inv, map_inv] at h1
    have h2 : (gm (𝟙 T.left) z ⊤ (chV t χ))⁻¹ = gm (𝟙 T.left) z ⊤ (chV t χ) :=
      mul_right_cancel (b := val P.sym (t ≫ i).left z J * val σ.s t.left z J) (by rw [h1, mul_left_comm])
    rw [chV_add, map_mul, map_one]
    have h3 := mul_inv_cancel (gm (𝟙 T.left) z ⊤ (chV t χ))
    rwa [h2] at h3
  · intro h T x z J hJ
    have hc : (chV x χ)⁻¹ = chV x χ := inv_eq_of_mul_eq_one_right (by rw [← chV_add]; exact h T x)
    rw [CubTriv.val_twist _ _ _ hJ, CubTriv.val_twist _ _ _ hJ, hσ T x z J hJ, chV_inv, hc, mul_left_comm]

def CP.twistSym (P : CP (splitTorus S X)) (χ : X) : CP (splitTorus S X) where
  L := P.L
  c := P.c
  sym := scaleGen (charUnit S X χ) P.sym
  sym_gen := scaleGen_isGen _ P.sym_gen
  sym_rig := corr_of_val P.L.isLB fun y J hJ => by
    have e := (val_scaleGen (charUnit S X χ) P.sym (1 : 𝟙_ (Over S) ⟶ splitTorus S X).left hJ).trans
      (congrArg₂ (· * ·) (gm_charUnit _ y χ) (P.val_sym_one hJ))
    have o : chV (1 : 𝟙_ (Over S) ⟶ splitTorus S X) χ = 1 := by rw [chV, map_one]; rfl
    rw [o, map_one, _root_.one_mul, one_left] at e
    exact (val_pull hJ _ _ _).trans (e.trans (val_one _).symm)
  sym_cub T x y u z J hJ := by
    have e := P.sym_cub T x y u z J hJ
    simp only [val_scaleGen _ _ _ hJ, gm_charUnit, chV_mul, map_mul]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul] at e' ⊢
    linear_combination (norm := abel) e'

theorem CubTriv.twist_even_twistSym {P : CP (splitTorus S X)} {σ : CubTriv P.c (𝟙 _)} (hσ : σ.Even) (ψ : X) :
    CubTriv.Even (P := P.twistSym (-(ψ + ψ))) (σ.twist ψ) := by
  intro T x
  show ∀ (z : T.left) (J : (T.left ⟶ (splitTorus S X).left) → P.L.L.ι), Good P.L.L z J →
    val (scaleGen (charUnit S X ψ) σ.s) (x⁻¹).left z J =
      val (scaleGen (charUnit S X (-(ψ + ψ))) P.sym) (x ≫ 𝟙 _).left z J *
        val (scaleGen (charUnit S X ψ) σ.s) x.left z J
  intro z J hJ
  have hn : chV (x ≫ 𝟙 _) (-(ψ + ψ)) = (chV x ψ * chV x ψ)⁻¹ := by
    rw [Category.comp_id]
    exact eq_inv_of_mul_eq_one_left (by rw [← chV_add, ← chV_add, neg_add_cancel, chV_zero])
  rw [val_scaleGen _ _ _ hJ, val_scaleGen _ _ _ hJ, val_scaleGen _ _ _ hJ, gm_charUnit, gm_charUnit, gm_charUnit,
    hσ T x z J hJ, chV_inv, hn]
  simp only [map_inv, map_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Twist

section Wt
variable {G : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {V V' : G.left.Opens}

theorem isWt_one : IsWt i V 1 0 := by
  intro Z t g h₁ h₂
  rw [← chV_val, chV_zero]
  simp

theorem isWt_zero (χ : X) : IsWt i V 0 χ := by
  intro Z t g h₁ h₂
  simp only [map_zero, mul_zero]

theorem IsWt.mul {u v : Γ(G.left, V)} {χ χ' : X} (hu : IsWt i V u χ) (hv : IsWt i V v χ') :
    IsWt i V (u * v) (χ + χ') := by
  intro Z t g h₁ h₂
  simp only [map_mul]
  rw [hu Z t g h₁ h₂, hv Z t g h₁ h₂, ← chV_val, ← chV_val, ← chV_val, chV_add, Units.val_mul]
  ring

theorem IsWt.add {u v : Γ(G.left, V)} {χ : X} (hu : IsWt i V u χ) (hv : IsWt i V v χ) : IsWt i V (u + v) χ := by
  intro Z t g h₁ h₂
  simp only [map_add]
  rw [hu Z t g h₁ h₂, hv Z t g h₁ h₂]
  ring

theorem IsWt.inv {u : Γ(G.left, V)ˣ} {χ : X} (hu : IsWt i V u.val χ) : IsWt i V (u⁻¹).val (-χ) := by
  intro Z t g h₁ h₂
  have e1 : (((t ≫ i) * g).left.appLE V ⊤ h₁).hom (u⁻¹).val * (((t ≫ i) * g).left.appLE V ⊤ h₁).hom u.val = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have e2 : (g.left.appLE V ⊤ h₂).hom (u⁻¹).val * (g.left.appLE V ⊤ h₂).hom u.val = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have e3 : t.left.appTop.hom (charUnit S X (-χ)).val * t.left.appTop.hom (charUnit S X χ).val = 1 := by
    rw [← chV_val, ← chV_val, ← Units.val_mul, ← chV_add, neg_add_cancel, chV_zero, Units.val_one]
  have e4 := hu Z t g h₁ h₂
  linear_combination (-((((t ≫ i) * g).left.appLE V ⊤ h₁).hom (u⁻¹).val * (g.left.appLE V ⊤ h₂).hom (u⁻¹).val *
      (g.left.appLE V ⊤ h₂).hom u.val)) * e3 - (((t ≫ i) * g).left.appLE V ⊤ h₁).hom (u⁻¹).val * e2 -
    t.left.appTop.hom (charUnit S X (-χ)).val * (g.left.appLE V ⊤ h₂).hom (u⁻¹).val *
      (((t ≫ i) * g).left.appLE V ⊤ h₁).hom (u⁻¹).val * e4 +
    t.left.appTop.hom (charUnit S X (-χ)).val * (g.left.appLE V ⊤ h₂).hom (u⁻¹).val * e1

theorem IsWt.res {u : Γ(G.left, V)} {χ : X} (hu : IsWt i V u χ) (h : V' ≤ V) :
    IsWt i V' ((G.left.presheaf.map (homOfLE h).op).hom u) χ := by
  intro Z t g h₁ h₂
  have k : ∀ (f : Z.left ⟶ G.left) (e : ⊤ ≤ f ⁻¹ᵁ V'),
      (f.appLE V' ⊤ e).hom ((G.left.presheaf.map (homOfLE h).op).hom u) =
        (f.appLE V ⊤ (e.trans (f.preimage_mono h))).hom u := by
    intro f e
    exact congrArg (fun φ => φ.hom u) (Scheme.Hom.map_appLE f e (homOfLE h).op)
  rw [k, k]
  exact hu Z t g _ _

theorem isWt_top_iff {u : Γ(G.left, ⊤)} {χ : X} : IsWt i ⊤ u χ ↔ ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G),
    ((t ≫ i) * g).left.appTop.hom u = (chV t χ).val * g.left.appTop.hom u := by
  have k : ∀ {Y : Scheme.{0}} (f : Y ⟶ G.left) (e : ⊤ ≤ f ⁻¹ᵁ ⊤), (f.appLE ⊤ ⊤ e).hom u = f.appTop.hom u := by
    intro Y f e
    exact congrArg (fun φ => φ.hom u) (Scheme.Hom.appLE_eq_app f (U := ⊤))
  constructor
  · intro h Z t g
    rw [chV_val, ← k ((t ≫ i) * g).left (Scheme.Hom.preimage_top _).ge, ← k g.left (Scheme.Hom.preimage_top _).ge]
    exact h Z t g _ _
  · intro h Z t g h₁ h₂
    rw [k, k, ← chV_val]
    exact h Z t g

theorem isWt_of_retraction (p : G ⟶ splitTorus S X) [IsMonHom p] (hp : i ≫ p = 𝟙 _) (χ : X) :
    IsWt i ⊤ (chV p χ).val χ := by
  rw [isWt_top_iff]
  intro Z t g
  have k : ∀ {Y : Over S} (f : Y ⟶ G), f.left.appTop.hom (chV p χ).val = (chV (f ≫ p) χ).val := by
    intro Y f
    rw [chV_val, chV_val]
    rfl
  rw [k, k, MonObj.mul_comp, chV_mul, Units.val_mul, Category.assoc, hp, Category.comp_id]

theorem isWt_charUnit (χ : X) : IsWt (𝟙 (splitTorus S X)) ⊤ (charUnit S X χ).val χ := by
  have e : (charUnit S X χ).val = (chV (𝟙 (splitTorus S X)) χ).val := by
    rw [chV_val]
    rfl
  rw [e]
  exact isWt_of_retraction (𝟙 _) (Category.id_comp _) χ

end Wt

theorem isAbelianScheme_unit (S : Scheme.{0}) : IsAbelianScheme (𝟙_ (Over S)) := by
  constructor
  all_goals first
    | infer_instance
    | (show Smooth (𝟙 S); infer_instance)
    | (show IsProper (𝟙 S); infer_instance)
    | (show GeometricallyConnected (𝟙 S)
       refine ⟨fun K _ y Z fst snd h => ?_⟩
       have : IsIso snd := h.isIso_snd_of_isIso
       exact ObjectProperty.prop_of_iso (fun Y : Scheme.{0} => ConnectedSpace Y) (asIso snd).symm
         (inferInstance : ConnectedSpace (Spec (CommRingCat.of K))))

def TQ.torus (S : Scheme.{0}) (X : Type) [AddCommGroup X] : TQ (splitTorus S X) X where
  B := 𝟙_ (Over S)
  isAb := isAbelianScheme_unit S
  q := toUnit _
  i := 𝟙 _
  q_hom := inferInstance
  i_hom := inferInstance
  q_flat := by rw [Rosenlicht.toUnit_left]; exact Diag.flat_hom S X
  q_surj := by rw [Rosenlicht.toUnit_left]; exact Diag.surjective_hom S X
  q_affine := by rw [Rosenlicht.toUnit_left]; exact Diag.isAffineHom_hom S X
  isKernel := by
    have : IsIso (η[𝟙_ (Over S)]) := by rw [toUnit_unique η[𝟙_ (Over S)] (𝟙 _)]; infer_instance
    exact IsPullback.of_horiz_isIso ⟨toUnit_unique _ _⟩
  loc _ χ := ⟨⊤, trivial, charUnit S X χ, isWt_charUnit χ⟩

theorem point_eq_of_subsingleton [Subsingleton X] {Z : Over S} (t t' : Z ⟶ splitTorus S X) : t = t' := by
  refine (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun x => ?_)
  rw [show x = 1 from Multiplicative.toAdd.injective (Subsingleton.elim _ _), map_one, map_one]

def TQ.abelian (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) (X : Type) [AddCommGroup X] [Subsingleton X] :
    TQ G X where
  B := G
  comm := hG.comm
  isAb := hG
  q := 𝟙 G
  i := toUnit _ ≫ η[G]
  q_hom := inferInstance
  i_hom := inferInstance
  q_flat := by rw [Over.id_left]; infer_instance
  q_surj := by rw [Over.id_left]; infer_instance
  q_affine := by rw [Over.id_left]; infer_instance
  isKernel := by
    have : IsIso (toUnit (splitTorus S X)) := ⟨η, point_eq_of_subsingleton _ _, toUnit_unique _ _⟩
    exact IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
  loc _ χ := ⟨⊤, trivial, 1, Subsingleton.elim 0 χ ▸ isWt_one⟩

def TQ.prod (X : Type) [AddCommGroup X] (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) :
    TQ (splitTorus S X ⊗ A) X where
  B := A
  comm := hA.comm
  isAb := hA
  q := snd _ _
  i := lift (𝟙 _) (toUnit _ ≫ η[A])
  q_hom := inferInstance
  i_hom := inferInstance
  q_flat := by show Flat (pullback.snd _ _); infer_instance
  q_surj := by show Surjective (pullback.snd _ _); infer_instance
  q_affine := isAffineHom_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (splitTorus S X).hom A.hom) (Diag.isAffineHom_hom S X)
  isKernel := IsPullback.of_isLimit' ⟨lift_snd _ _⟩ (PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ fst _ _)
    (fun s => by
      ext
      · simp
      · simp only [Category.assoc, lift_snd]
        rw [s.condition, ← Category.assoc, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) s.snd])
    (fun s => toUnit_unique _ _) (fun s m h _ => by rw [← h]; simp))
  loc _ χ := ⟨⊤, trivial, chV (fst _ _) χ, isWt_of_retraction (fst _ _) (lift_fst _ _) χ⟩

def TQ.Desc.triv {G : Over S} [GrpObj G] [IsCommMonObj G] (Q : TQ G X) : Q.Desc (CP.triv G) where
  M := CP.triv Q.B
  w := ⟨fun _ => 1⟩
  map := IsCPMap.triv (have := Q.q_hom; toBase_mul_of_isMonHom Q.q _)

def TQ.Desc.abelian {G : Over S} [GrpObj G] [IsCommMonObj G] (hG : IsAbelianScheme G) [Subsingleton X] (P : CP G) :
    (TQ.abelian G hG X).Desc P where
  M := P
  w := idIso P.L.L
  map := IsCPMap.id P

theorem TQ.exists_desc {G : Over S} [GrpObj G] [IsCommMonObj G] (Q : TQ G X) (M : CP Q.B) :
    ∃ (P : CP G) (D : Q.Desc P), D.M = M := by
  have := Q.q_hom
  obtain ⟨P, w, hw⟩ := exists_pull (f := 𝟙 S) (F := Q.q.left) (hw := by simp) M (toBase_mul_of_isMonHom Q.q (by simp))
  exact ⟨P, ⟨M, w, hw⟩, rfl⟩

theorem TQ.genWt_triv {G : Over S} [GrpObj G] (Q : TQ G X) (u : Γ(G.left, ⊤)ˣ) {χ : X} (hu : IsWt Q.i ⊤ u.val χ) :
    Q.GenWt (Inh.trivLB _) (scaleGen u (unitGen _ _)) χ := by
  refine ⟨scaleGen_isGen u (unitGen_isGen _ _), fun j => ?_⟩
  show IsWt Q.i _ (res le_top u * 1).val χ
  rw [_root_.mul_one]
  exact hu.res le_top

example (χ : X) : (TQ.torus S X).GenWt (Inh.trivLB _) (scaleGen (charUnit S X χ) (unitGen _ _)) χ :=
  (TQ.torus S X).genWt_triv _ (isWt_charUnit χ)

end Torus

section Basic₂

theorem exists_point_two : ∃ t : 𝟙_ (Over (Spec (CommRingCat.of ℚ))) ⟶ splitTorus (Spec (CommRingCat.of ℚ)) ℤ,
    ∀ n : ℤ, chV t n = 1 → n = 0 := by
  let e : ℚ ≃+* Γ(Spec (CommRingCat.of ℚ), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of ℚ)).symm.commRingCatIsoToRingEquiv
  let u : Γ(Spec (CommRingCat.of ℚ), ⊤)ˣ := Units.map e.toMonoidHom (Units.mk0 2 two_ne_zero)
  refine ⟨(splitTorusPointsEquiv _ ℤ _).symm (zpowersHom _ u), fun n hn => ?_⟩
  have h1 : u ^ n = 1 := by
    simpa only [chV, MulEquiv.apply_symm_apply, zpowersHom_apply, toAdd_ofAdd] using hn
  have h2 : (Units.mk0 (2:ℚ) two_ne_zero) ^ n = 1 := by
    have hu : Units.map e.symm.toMonoidHom u = Units.mk0 2 two_ne_zero := Units.ext (by simp [u])
    rw [← hu, ← map_zpow, h1, map_one]
  have h3 : (2:ℚ) ^ n = 1 := by
    have h4 := congrArg Units.val h2
    rwa [Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_one] at h4
  exact zpow_right_injective₀ (by norm_num : (0:ℚ) < 2) (by norm_num) (h3.trans (zpow_zero (2:ℚ)).symm)

example : ¬ CubTriv.Even (P := CP.triv (splitTorus (Spec (CommRingCat.of ℚ)) ℤ))
    ((CubTriv.triv (𝟙 _)).twist (1 : ℤ)) := fun h => by
  obtain ⟨t, ht⟩ := exists_point_two
  exact absurd (ht _ ((CubTriv.twist_even_iff (CubTriv.triv_even _) 1).1 h _ t)) (by norm_num)

example : ¬ CubTriv.Even (P := (CP.triv (splitTorus (Spec (CommRingCat.of ℚ)) ℤ)).twistSym 1)
    (CubTriv.triv (𝟙 _)) := fun h => by
  obtain ⟨t, ht⟩ := exists_point_two
  refine absurd (ht 1 (unit_ext fun z _ => ?_)) one_ne_zero
  obtain ⟨J, hJ⟩ := exists_good_pt (Inh.trivLB_isLB (splitTorus (Spec (CommRingCat.of ℚ)) ℤ).left) z
  have e := ((val_unitGen _ _ _ _ _).symm.trans (h _ t z J hJ)).trans (congrArg₂ (· * ·)
    ((val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) (gm_charUnit _ z _) (val_unitGen _ _ _ _ _)))
    (val_unitGen _ _ _ _ _))
  rw [_root_.mul_one, _root_.mul_one, Category.comp_id] at e
  exact e.symm.trans (map_one _).symm

example : IsWt (𝟙 _) ⊤ (charUnit (Spec (CommRingCat.of ℚ)) ℤ 1).val (1 : ℤ) ∧
    ¬ IsWt (𝟙 _) ⊤ (charUnit (Spec (CommRingCat.of ℚ)) ℤ 1).val (-1 : ℤ) := by
  refine ⟨isWt_charUnit 1, fun h => ?_⟩
  obtain ⟨t, ht⟩ := exists_point_two
  have a := isWt_top_iff.1 h _ t t
  rw [Category.comp_id, ← chV_val, ← chV_val, chV_mul, ← Units.val_mul, Units.val_inj, mul_left_inj] at a
  have b : chV t (1 + 1) = 1 := by
    rw [chV_add]
    exact (congrArg (· * chV t 1) a).trans (by rw [← chV_add, neg_add_cancel, chV_zero])
  exact absurd (ht _ b) (by norm_num)

example : Nonempty (TQ (splitTorus S ℤ) ℤ) := ⟨TQ.torus S ℤ⟩

example (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) : Nonempty (TQ G PUnit) := ⟨TQ.abelian G hG PUnit⟩

end Basic₂

end GlobalTheory.UU
end
