import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ObjComp

section Bundle

variable {X : Scheme.{0}}

def idPullIso (L : LB X) : LB.Iso L (L.pull (𝟙 X)) :=
  ⟨fun p => res (fun _ hy => ⟨mem_pull.1 hy.1, hy.2⟩ :
    (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2) (L.g (p.1 PUnit.unit) p.2)⟩

theorem gw_idPullIso (L : LB X) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j)
    (hk : f y ∈ L.U k) : gw (idPullIso L) f y j k = gm f y _ (L.g j k) := by
  have hm : f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k := ⟨mem_pull.2 hj, hk⟩
  show gm f y _ (res _ (L.g j k)) = _
  exact gm_res f y _ hm _

theorem pgen_idPullIso {L : LB X} (hL : L.IsLB) : PGen (idPullIso L) := by
  intro Y f y j j' k k' hj hj' hk hk'
  have hj₀ : f y ∈ L.U j := hj
  have hj₀' : f y ∈ L.U j' := hj'
  rw [gw_idPullIso L f y j k hj₀ hk, gw_idPullIso L f y j' k' hj₀' hk', Category.comp_id]
  have a := gm_cocycle hL f y hj₀ hk hk'
  have b := gm_cocycle hL f y hj₀ hj₀' hk'
  rw [mul_right_comm, b, ← a, mul_inv_cancel_right]

theorem pmaps_idPullIso (L : LB X) {K : Type} [Fintype K] {Y : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : PMaps (idPullIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have hp₀ : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨Set.mem_iInter.2 hp₀, Set.mem_iInter.2 hq⟩
  have e := congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  rw [gw_idPullIso L (r ≫ φ k) z (p k) (q k) (hp₀ k) (hq k)]
  exact (gm_res r z _ hm _).trans (gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp₀ k, hq k⟩ _)

end Bundle

section Group

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

theorem isGrpPullback_id : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (mul_left_congr (b := T.hom) (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm

variable [IsCommMonObj G]

def cubeMapId : CubeMap G G where
  F := 𝟙 _
  F3 := 𝟙 _
  e := 𝟙 _
  e_comm := by rw [Category.comp_id, Category.id_comp]
  psum_comm := fun _ => by rw [Category.comp_id, Category.id_comp]

theorem isPullCubical_id {L : RigLB G} (c : CubicalStr G L) : (cubeMapId G).IsPullCubical c c :=
  (isPullCubical_iff _ c c).2 ⟨idPullIso L.L, pgen_idPullIso L.isLB,
    pmaps_idPullIso L.L _ _ L.rig L.rigGen, pmaps_idPullIso L.L _ _ c.t c.isGen⟩

end Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def sabMapId {S : Scheme.{0}} (t : SAB H S) : SABMap t t (𝟙 S) where
  cm := cubeMapId t.G
  cart := isGrpPullback_id t.G
  base := rfl
  act := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
  lin := isPullCubical_id t.G t.cub

variable {D : Datum H} {l : Level H}

def objMapId {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) :
    ObjMap o o (𝟙 S) where
  toSABMap := sabMapId o.t
  eta := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
  etaA := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm

section

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {b : Base l B} {b' : Base l B'} {b'' : Base l B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {o : Obj D l b s} {o' : Obj D l b' s'} {o'' : Obj D l b'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}

theorem sec_comp {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    {x : S ⟶ G.left} {x' : S' ⟶ G'.left} {x'' : S'' ⟶ G''.left} (h : x' ≫ φ = f ≫ x) (h' : x'' ≫ φ' = f' ≫ x') :
    x'' ≫ φ' ≫ φ = (f' ≫ f) ≫ x := by
  rw [← Category.assoc, h', Category.assoc, h, Category.assoc]

theorem sec_cancel {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    (hp : IsPullback φ G'.hom G.hom f) (w : φ' ≫ G'.hom = G''.hom ≫ f')
    {x : S ⟶ G.left} {x' : S' ⟶ G'.left} {x'' : S'' ⟶ G''.left} (hx' : x' ≫ G'.hom = 𝟙 _) (hx'' : x'' ≫ G''.hom = 𝟙 _)
    (h : x' ≫ φ = f ≫ x) (h'' : x'' ≫ φ' ≫ φ = (f' ≫ f) ≫ x) : x'' ≫ φ' = f' ≫ x' := by
  apply hp.hom_ext
  · rw [Category.assoc, h'', Category.assoc, Category.assoc, h]
  · rw [Category.assoc, w, ← Category.assoc, hx'', Category.assoc, hx']; simp

theorem objMap_comp (m : ObjMap o' o f) (m' : ObjMap o'' o' f') :
    ∃ n : ObjMap o'' o (f' ≫ f), n.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ := by
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H S S' S'' o.t o'.t o''.t f f' m.toSABMap m'.toSABMap
  have hn' : n.cm.F = m'.cm.F ≫ m.cm.F := hn
  exact ⟨⟨n, fun a => by rw [hn']; exact sec_comp (m.eta a) (m'.eta a),
    fun a => by rw [hn']; exact sec_comp (m.etaA a) (m'.etaA a)⟩, hn⟩

theorem objMap_cancel (m : ObjMap o' o f) (n : ObjMap o'' o (f' ≫ f)) :
    ∃ m' : ObjMap o'' o' f', n.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ := by
  obtain ⟨m', hn⟩ := sabCancel pullCubCancel E H S S' S'' o.t o'.t o''.t f f' m.toSABMap n.toSABMap
  have hn' : n.cm.F = m'.cm.F ≫ m.cm.F := hn
  exact ⟨⟨m', fun a => sec_cancel m.cart.1 m'.cart.1.w (Over.w (o'.eta a)) (Over.w (o''.eta a)) (m.eta a)
      (by rw [← hn']; exact n.eta a),
    fun a => sec_cancel m.cart.1 m'.cart.1.w (Over.w (o'.etaA a)) (Over.w (o''.etaA a)) (m.etaA a)
      (by rw [← hn']; exact n.etaA a)⟩, hn⟩

end

end GlobalTheory.ObjComp

namespace GlobalTheory

end GlobalTheory
