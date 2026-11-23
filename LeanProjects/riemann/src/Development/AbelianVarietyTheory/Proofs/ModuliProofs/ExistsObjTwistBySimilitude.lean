import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.LevelTwist

section Identity

variable {X : Scheme.{0}}

def selfIso (L : LB X) : LB.Iso L (L.pull (𝟙 X)) :=
  ⟨fun p => res (show (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2 from
    fun _ hx => ⟨mem_pull (F := 𝟙 X).1 hx.1, hx.2⟩) (L.g (p.1 PUnit.unit) p.2)⟩

theorem gw_selfIso (L : LB X) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j)
    (hk : f y ∈ L.U k) : gw (selfIso L) f y j k = gm f y _ (L.g j k) :=
  gm_res f y _ (show f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k from ⟨mem_pull (F := 𝟙 X).2 hj, hk⟩) _

theorem pgen_selfIso {L : LB X} (hL : L.IsLB) : PGen (selfIso L) := by
  intro Y f y j j' k k' hj hj' hk hk'
  rw [gw_selfIso L f y j k hj hk, gw_selfIso L f y j' k' hj' hk', Category.comp_id, mul_right_comm,
    gm_cocycle hL f y hj hj' hk', ← gm_cocycle hL f y hj hk hk', mul_inv_cancel_right]

theorem pmaps_selfIso {L : LB X} {K : Type} [Fintype K] {Y : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : PMaps (selfIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩
  have h := congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans (h.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ =>
    (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact ((gm_res r z _ hm _).trans (gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp k, hq k⟩ _)).trans
    (gw_selfIso L (r ≫ φ k) z (p k) (q k) (hp k) (hq k)).symm

variable {S : Scheme.{0}}

def cubeMapId (G : Over S) [GrpObj G] [IsCommMonObj G] : CubeMap G G where
  F := 𝟙 _
  F3 := 𝟙 _
  e := 𝟙 _
  e_comm := by rw [Category.id_comp, Category.comp_id]
  psum_comm := fun I => by rw [Category.id_comp, Category.comp_id]

theorem isPullCubical_id {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) :
    (cubeMapId G).IsPullCubical c c :=
  (isPullCubical_iff _ c c).2 ⟨selfIso L.L, pgen_selfIso L.isLB, pmaps_selfIso _ _ L.rig L.rigGen,
    pmaps_selfIso _ _ c.t c.isGen⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def sabMapId (t : SAB H S) : SABMap t t (𝟙 S) where
  cm := cubeMapId t.G
  cart := @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl t.G) (inferInstanceAs (IsMonHom (𝟙 t.G)))
  base := rfl
  act := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
  lin := isPullCubical_id t.cub

theorem sabMapId_φ (t : SAB H S) : (sabMapId t).φ = 𝟙 _ := rfl

end Identity

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_congr (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) {a a' : D.La} (h : D.ModN n (a - a')) :
    I.ev n a = I.ev n a' := by
  have : a = (a - a') + a' := (sub_add_cancel a a').symm
  rw [this, I.add, (I.ker n hn _).2 h, _root_.one_mul]

theorem zeta_zpow_congr (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) {i j : ℤ} (h : (n : ℤ) ∣ i - j) :
    I.ζ n ^ i = I.ζ n ^ j := by
  have : i = (i - j) + j := (sub_add_cancel i j).symm
  rw [this, zpow_add, ((I.ζ_prim n hn).zpow_eq_one_iff_dvd _).2 h, _root_.one_mul]

def twist (I : TateIso D k Q act e) (g : Sim D)
    (hν : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) :
    TateIso D k Q act e where
  ζ n := I.ζ n ^ g.ν n
  ζ_prim n hn := (I.ζ_prim n hn).zpow_of_gcd_eq_one _ (Int.isCoprime_iff_gcd_eq_one.1 (hν n 1 hn one_pos).2)
  ζ_pow n m hn hm := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm (g.ν _), zpow_mul, zpow_natCast, I.ζ_pow n m hn hm]
    exact zeta_zpow_congr I hn (hν n m hn hm).1
  ev n a := I.ev n (g.f n a)
  add n a b := by rw [map_add, I.add]
  lin n c a := by rw [map_smul, I.lin]
  ker n hn a := by
    rw [I.ker n hn]
    obtain ⟨g', hg'⟩ := g.inv n hn
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨c, hc⟩ := (hg' a).1
      refine ⟨g' b - c, ?_⟩
      rw [smul_sub, ← hc, hb, map_nsmul, sub_sub_cancel]
    · rintro ⟨b, rfl⟩
      exact ⟨g.f n b, map_nsmul _ _ _⟩
  onto n hn x := by
    rw [I.onto n hn]
    obtain ⟨g', hg'⟩ := g.inv n hn
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨g' a, ev_congr I hn (hg' a).2⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, rfl⟩
  tower n m hn hm a := by
    rw [I.tower n m hn hm]
    exact ev_congr I hn (g.tower n m hn hm a)
  isom n hn a b := by
    rw [← zpow_mul, ← zeta_zpow_congr I hn (g.mult n hn a b)]
    exact I.isom n hn _ _

@[simp] theorem twist_ζ (I : TateIso D k Q act e) (g : Sim D)
    (hν : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) (n : ℕ) :
    (twist I g hν).ζ n = I.ζ n ^ g.ν n := rfl

@[simp] theorem twist_ev (I : TateIso D k Q act e) (g : Sim D)
    (hν : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) (n : ℕ)
    (a : D.La) : (twist I g hν).ev n a = I.ev n (g.f n a) := rfl

theorem map_mem_smul_top (f : D.La →ₗ[𝓞 E] D.La) (J : Ideal (𝓞 E)) {a : D.La}
    (ha : a ∈ J • (⊤ : Submodule (𝓞 E) D.La)) : f a ∈ J • (⊤ : Submodule (𝓞 E) D.La) := by
  have h := Submodule.mem_map_of_mem (f := f) ha
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

def objTwist (o : Obj D l b s) (g : Sim D)
    (hν : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ))
    (hA : (l.A : ℤ) ∣ g.ν l.A - 1) : Obj D l b s where
  t := o.t
  proper := o.proper
  ample := o.ample
  ktriv := o.ktriv
  eta a := o.eta (g.f l.M a)
  eta_add a c := by rw [map_add, o.eta_add]
  eta_ker a ha := o.eta_ker _ (map_mem_smul_top _ _ ha)
  etaA a := o.etaA (g.f l.A a)
  etaA_add a c := by rw [map_add, o.etaA_add]
  etaA_ker a := by rw [map_nsmul, o.etaA_ker]
  geom k _ _ x β hx := by
    obtain ⟨hd, I, hζ, hA', hM⟩ := o.geom k x β hx
    refine ⟨hd, twist I g hν, ?_, fun a => hA' _, fun a ha => hM _ (map_mem_smul_top _ _ ha)⟩
    rw [twist_ζ, zeta_zpow_congr I l.A_pos hA, zpow_one, hζ]

end Twist

end GlobalTheory.LevelTwist

namespace GlobalTheory

theorem exists_obj_twist_by_similitude :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (g : Sim D), 1 ≤ D.p + D.q → (l.A : ℤ) ∣ g.ν l.A - 1 → ∃ (o' : Obj D l b s) (m : SABMap o'.t o.t (𝟙 S)), (∀ a, (o'.eta a).left ≫ m.φ = (o.eta (g.f l.M a)).left) ∧ ∀ a, (o'.etaA a).left ≫ m.φ = (o.etaA (g.f l.A a)).left := by
  intro h E _ _ _ H D l B _ b S s o g hpq hA
  exact ⟨LevelTwist.objTwist o g ((h E H D hpq).1 g) hA, LevelTwist.sabMapId o.t,
    fun _ => Category.comp_id _, fun _ => Category.comp_id _⟩

end GlobalTheory
