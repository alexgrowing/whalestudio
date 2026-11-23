import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

def CubWeilBasicSt : Prop := ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L)
  (N : ℕ) (T : Over S), (∀ x y : T ⟶ G, x ^ N = 1 → y ^ N = 1 → ∃! ζ, CubWeil c N x y ζ) ∧
  (∀ (x x' y : T ⟶ G) ζ ζ', CubWeil c N x y ζ → CubWeil c N x' y ζ' → CubWeil c N (x * x') y (ζ * ζ')) ∧
  (∀ (x y : T ⟶ G) ζ, CubWeil c N x y ζ → CubWeil c N y x ζ⁻¹ ∧ ζ ^ N = 1) ∧
  (∀ (T' : Over S) (ρ : T' ⟶ T) (x y : T ⟶ G) ζ, CubWeil c N x y ζ →
    CubWeil c N (ρ ≫ x) (ρ ≫ y) (Units.map ρ.left.appTop.hom.toMonoidHom ζ)) ∧
  ∀ (H : Over S) [GrpObj H] (i : H ⟶ G), IsMonHom i → Nonempty (BiTriv c i) →
    ∀ (t : T ⟶ H) (y : T ⟶ G), t ^ N = 1 → y ^ N = 1 → CubWeil c N (t ≫ i) y 1

def CubWeilMapSt : Prop := ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
  (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (P : CP G) (P' : CP G') (F : G'.left ⟶ G.left) (hw) (w),
  IsCPMap P' P f F hw w → ∀ (N : ℕ) (T : Over S') (x y : T ⟶ G') (ζ : Γ(T.left, ⊤)ˣ), CubWeil P'.c N x y ζ →
    CubWeil P.c N (toBase hw x) (toBase hw y) ζ

def CubWeilKerSt : Prop := GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B →
  ∀ (L : RigLB B) (c : CubicalStr B L) (N : ℕ) (T : Over S) (x y : T ⟶ B), x ^ N = 1 → y ^ N = 1 →
  (∃ u : LB.Gen (translDiff B L.L x), u.IsGen) → CubWeil c N x y 1

def CubWeilIsSt : Prop := GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B →
  ∀ (L : RigLB B) (c : CubicalStr B L) (N : ℕ) (T : Over S) (x y : T ⟶ B) (ζ : Γ(T.left, ⊤)ˣ),
  CubWeil c N x y ζ → WeilIs B L.L N x y ζ

namespace SignCube

section Alg
variable {R : Type} [CommRing R]

def tri (a b c : R) : R := 1 - (1 - a) * (1 - b) * (1 - c)

theorem tri_sq (h : (3 : R) = 0) {a b c : R} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) :
    tri a b c * tri a b c = 1 := by
  unfold tri; grind

theorem tri_mul (h : (3 : R) = 0) (a a' : R) {b c : R} (hb : b * b = 1) (hc : c * c = 1) :
    tri (a * a') b c = tri a b c * tri a' b c := by
  unfold tri; grind

theorem tri_swap₁ (a b c : R) : tri a b c = tri b a c := by unfold tri; ring

theorem tri_swap₂ (a b c : R) : tri a b c = tri a c b := by unfold tri; ring

theorem map_tri {R' : Type} [CommRing R'] (φ : R →+* R') (a b c : R) : φ (tri a b c) = tri (φ a) (φ b) (φ c) := by
  simp [tri]

end Alg

theorem isCub_of_mul {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
    (hm : ∀ x x' y z, θ (x * x') y z = θ x y z * θ x' y z) (s₁ : ∀ x y z, θ x y z = θ y x z)
    (s₂ : ∀ x y z, θ x y z = θ x z y) : IsCub θ where
  face x y := by
    have := hm 1 1 x y
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  s01 := s₁
  s12 := s₂
  coc x x' x'' y := by
    rw [hm, s₁ x (x' * x''), hm, s₁ x' x, s₁ x'' x]
    ac_rfl

abbrev base : Scheme.{0} := Spec (CommRingCat.of (ZMod 3))

abbrev Ch : Type := Additive (ℤˣ × ℤˣ)

abbrev grp : Over base := splitTorus base Ch

def χ₁ : Ch := Additive.ofMul (-1, 1)

def χ₂ : Ch := Additive.ofMul (1, -1)

def baseEquiv : ZMod 3 ≃+* Γ(base, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (ZMod 3))).symm.commRingCatIsoToRingEquiv

theorem three_eq_zero (T : Over base) : (3 : Γ(T.left, ⊤)) = 0 := by
  have := map_ofNat (T.hom.appTop.hom.comp baseEquiv.toRingHom) 3
  rw [show (OfNat.ofNat 3 : ZMod 3) = 0 from rfl, map_zero] at this
  exact this.symm

variable {T T' : Over base}

theorem chV_sq (x : T ⟶ grp) (χ : Ch) : (chV x χ).val * (chV x χ).val = 1 := by
  have : χ + χ = 0 := Prod.ext (Int.units_mul_self _) (Int.units_mul_self _)
  rw [← Units.val_mul, ← chV_add, this, chV_zero, Units.val_one]

theorem mul_self_eq_one (x : T ⟶ grp) : x * x = 1 :=
  (splitTorusPointsEquiv base Ch T).injective (MonoidHom.ext fun χ => Units.ext (by
    rw [map_mul, map_one]; exact chV_sq x χ.toAdd))

theorem sq_eq_one (x : T ⟶ grp) : x ^ 2 = 1 := (sq x).trans (mul_self_eq_one x)

theorem chV_comp (ρ : T' ⟶ T) (x : T ⟶ grp) (χ : Ch) : (chV (ρ ≫ x) χ).val = ρ.left.appTop.hom (chV x χ).val := by
  rw [chV_val, chV_val, Rosenlicht.over_appTop_comp]

def triU (χ ψ ω : Ch) (x y u : T ⟶ grp) : Γ(T.left, ⊤)ˣ :=
  ⟨tri (chV x χ).val (chV y ψ).val (chV u ω).val, tri (chV x χ).val (chV y ψ).val (chV u ω).val,
    tri_sq (three_eq_zero T) (chV_sq _ _) (chV_sq _ _) (chV_sq _ _),
    tri_sq (three_eq_zero T) (chV_sq _ _) (chV_sq _ _) (chV_sq _ _)⟩

theorem triU_mul (χ ψ ω : Ch) (x x' y u : T ⟶ grp) : triU χ ψ ω (x * x') y u = triU χ ψ ω x y u * triU χ ψ ω x' y u :=
  Units.ext (by
    show tri (chV (x * x') χ).val _ _ = tri _ _ _ * tri _ _ _
    rw [chV_mul, Units.val_mul]
    exact tri_mul (three_eq_zero T) _ _ (chV_sq _ _) (chV_sq _ _))

theorem triU_swap₁ (χ ψ ω : Ch) (x y u : T ⟶ grp) : triU χ ψ ω x y u = triU ψ χ ω y x u := Units.ext (tri_swap₁ _ _ _)

theorem triU_swap₂ (χ ψ ω : Ch) (x y u : T ⟶ grp) : triU χ ψ ω x y u = triU χ ω ψ x u y := Units.ext (tri_swap₂ _ _ _)

theorem triU_comp (ρ : T' ⟶ T) (χ ψ ω : Ch) (x y u : T ⟶ grp) :
    Units.map ρ.left.appTop.hom.toMonoidHom (triU χ ψ ω x y u) = triU χ ψ ω (ρ ≫ x) (ρ ≫ y) (ρ ≫ u) :=
  Units.ext (by
    show ρ.left.appTop.hom (tri _ _ _) = tri _ _ _
    rw [map_tri, chV_comp, chV_comp, chV_comp])

def sgn (x y u : T ⟶ grp) : Γ(T.left, ⊤)ˣ := triU χ₁ χ₁ χ₂ x y u * triU χ₁ χ₂ χ₁ x y u * triU χ₂ χ₁ χ₁ x y u

theorem sgn_comp (ρ : T' ⟶ T) (x y u : T ⟶ grp) :
    Units.map ρ.left.appTop.hom.toMonoidHom (sgn x y u) = sgn (ρ ≫ x) (ρ ≫ y) (ρ ≫ u) := by
  rw [sgn, map_mul, map_mul, triU_comp, triU_comp, triU_comp, sgn]

theorem sgn_mul (x x' y u : T ⟶ grp) : sgn (x * x') y u = sgn x y u * sgn x' y u := by
  simp only [sgn, triU_mul]; ac_rfl

theorem sgn_swap₁ (x y u : T ⟶ grp) : sgn x y u = sgn y x u := by
  rw [sgn, sgn, triU_swap₁ χ₁ χ₁ χ₂, triU_swap₁ χ₁ χ₂ χ₁, triU_swap₁ χ₂ χ₁ χ₁ x]; ac_rfl

theorem sgn_swap₂ (x y u : T ⟶ grp) : sgn x y u = sgn x u y := by
  rw [sgn, sgn, triU_swap₂ χ₁ χ₁ χ₂, triU_swap₂ χ₁ χ₂ χ₁ x y, triU_swap₂ χ₂ χ₁ χ₁ x y]; ac_rfl

def gen : LB.Gen (Theta grp (trivRig grp).L) :=
  scaleGen (sgn (x3 grp 0) (x3 grp 1) (x3 grp 2)) (unitGen (thφ grp (x3 grp)) thε)

theorem thV_gen {z : T.left} {J} (hJ : Good (trivRig grp).L z J) (x y u : T ⟶ grp) :
    CubTransport.thV (L := trivRig grp) gen z J x y u = gm (𝟙 T.left) z ⊤ (sgn x y u) := by
  have a₀ : lift x (lift y u) ≫ x3 grp 0 = x := by simp [x3]
  have a₁ : lift x (lift y u) ≫ x3 grp 1 = y := by simp [x3]
  have a₂ : lift x (lift y u) ≫ x3 grp 2 = u := by simp [x3]
  refine (val_scaleGen _ _ _ hJ).trans ((congrArg₂ (· * ·) (gm_top _ z _) (val_unitGen _ _ _ _ _)).trans ?_)
  rw [_root_.mul_one, sgn_comp, a₀, a₁, a₂]

def cub : CubicalStr grp (trivRig grp) :=
  CubTransport.cubicalOfVal gen (scaleGen_isGen _ (unitGen_isGen _ _)) fun T z J hJ =>
    isCub_of_mul (fun x x' y u => by simp only [thV_gen hJ, sgn_mul, map_mul])
      (fun x y u => by rw [thV_gen hJ, thV_gen hJ, sgn_swap₁]) (fun x y u => by rw [thV_gen hJ, thV_gen hJ, sgn_swap₂])

theorem cubV_cub {z : T.left} {J} (hJ : Good (trivRig grp).L z J) (x y u : T ⟶ grp) :
    cubV cub z J x y u = gm (𝟙 T.left) z ⊤ (sgn x y u) := thV_gen hJ x y u

def pkg : CP grp where
  L := trivRig grp
  c := cub
  sym := (CP.triv grp).sym
  sym_gen := (CP.triv grp).sym_gen
  sym_rig := (CP.triv grp).sym_rig
  sym_cub T x y u z J _ := by
    have e : ∀ r, val (L := (trivRig grp).L) (CP.triv grp).sym r z J = 1 := fun r => val_sym_triv _ _ _ _
    have i : ∀ a : T ⟶ grp, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (mul_self_eq_one a)
    simp only [i, e, _root_.mul_one]

def pt (T : Over base) (φ : ℤˣ × ℤˣ →* ℤˣ) : T ⟶ grp :=
  (splitTorusPointsEquiv base Ch T).symm ((Units.map (Int.castRingHom Γ(T.left, ⊤)).toMonoidHom).comp φ)

theorem chV_pt (φ : ℤˣ × ℤˣ →* ℤˣ) (χ : Ch) : (chV (pt T φ) χ).val = ((φ χ.toMul : ℤ) : Γ(T.left, ⊤)) := by
  rw [chV, pt, MulEquiv.apply_symm_apply]; rfl

def p₁ (T : Over base) : T ⟶ grp := pt T (MonoidHom.fst _ _)

def p₂ (T : Over base) : T ⟶ grp := pt T (MonoidHom.snd _ _)

theorem sgn_p₁ : sgn (p₁ T) (p₁ T) (p₂ T) = -1 := Units.ext (by
  have h := three_eq_zero T
  simp only [sgn, triU, Units.val_mul, p₁, p₂, chV_pt, χ₁, χ₂, tri]
  simp
  grind)

theorem sgn_p₂ : sgn (p₂ T) (p₂ T) (p₁ T) = 1 := Units.ext (by
  simp only [sgn, triU, Units.val_mul, p₁, p₂, chV_pt, χ₁, χ₂, tri]
  simp)

theorem cubWeil_neg_one (T : Over base) : CubWeil cub 2 (p₁ T) (p₂ T) (-1) :=
  ⟨sq_eq_one _, sq_eq_one _, fun z J hJ => by
    have C := isCub_cubV cub hJ
    simp only [cubN, Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, _root_.one_mul, C.face]
    rw [cubV_cub hJ, cubV_cub hJ, sgn_p₁, sgn_p₂, ← map_mul, neg_mul_neg, _root_.one_mul]⟩

theorem neg_one_ne_one : (-1 : Γ((𝟙_ (Over base)).left, ⊤)ˣ) ≠ 1 := fun h => by
  have a : (-1 : Γ(base, ⊤)) = 1 := congrArg Units.val h
  have b : baseEquiv (-1) = baseEquiv 1 := by rw [map_neg, map_one]; exact a
  exact absurd (baseEquiv.injective b) (by decide)

theorem not_cubWeil_one : ¬ CubWeil cub 2 (p₁ (𝟙_ _)) (p₂ (𝟙_ _)) 1 := fun h =>
  neg_one_ne_one ((cubWeil_neg_one _).unique h)

example : CubWeil cub 2 (p₁ T * p₁ T) (p₂ T) (-1 * -1) ∧ (-1 : Γ(T.left, ⊤)ˣ) ^ 2 = 1 := by
  refine ⟨?_, by simp⟩
  rw [mul_self_eq_one, neg_mul_neg, _root_.one_mul]
  refine ⟨one_pow _, sq_eq_one _, fun z J hJ => ?_⟩
  have C := isCub_cubV cub hJ
  simp only [cubN, C.face₂, C.face₃, map_one, _root_.one_mul]

example : ¬ Nonempty (BiTriv cub (𝟙 grp)) := fun ⟨σ⟩ =>
  not_cubWeil_one (by simpa using σ.cubWeil (sq_eq_one (p₁ (𝟙_ _))) (sq_eq_one (p₂ (𝟙_ _))))

example : IsMonHom (𝟙 grp) ∧ Nonempty (BiTriv (trivCub grp) (𝟙 grp)) ∧
    CubWeil (trivCub grp) 2 (p₁ T ≫ 𝟙 grp) (p₂ T) 1 :=
  ⟨inferInstance, ⟨BiTriv.triv _⟩, cubWeil_triv (sq_eq_one _) (sq_eq_one _)⟩

example : ∃ hw w, IsCPMap pkg pkg (𝟙 base) (𝟙 grp.left) hw w ∧ CubWeil pkg.c 2 (p₁ T) (p₂ T) (-1) ∧
    CubWeil pkg.c 2 (toBase hw (p₁ T)) (toBase hw (p₂ T)) (-1 : Γ(T.left, ⊤)ˣ) := by
  refine ⟨_, _, IsCPMap.id pkg, cubWeil_neg_one T, ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 base) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e : ∀ (h) (a : T ⟶ grp), toBase (f := 𝟙 base) (g := 𝟙 grp.left) h a = ρ ≫ a := fun h a =>
    Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm)
  have n : Units.map ρ.left.appTop.hom.toMonoidHom (-1) = -1 := Units.ext (by simp)
  rw [e, e]
  exact n ▸ (cubWeil_neg_one T).comp ρ

example {S' : Scheme.{0}} (f : S' ⟶ base) : ∃ (P' : CP ((Over.pullback f).obj grp)) (w : _),
    IsCPMap P' pkg f (pullback.fst grp.hom f) pullback.condition w :=
  exists_pull pkg (toBase_mul_pullback grp f)

example : (∃ u : LB.Gen (translDiff grp (trivRig grp).L (p₁ (𝟙_ _))), u.IsGen) ∧
    ¬ CubWeil cub 2 (p₁ (𝟙_ _)) (p₂ (𝟙_ _)) 1 :=
  ⟨⟨unitGen _ _, unitGen_isGen _ _⟩, not_cubWeil_one⟩

end SignCube

section Abelian
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S}

example {N : ℕ} {x y : T ⟶ B} (hx : x ^ N = 1) (hy : y ^ N = 1) :
    (∃ u : LB.Gen (translDiff B (trivRig B).L x), u.IsGen) ∧ CubWeil (trivCub B) N x y 1 :=
  ⟨⟨unitGen _ _, unitGen_isGen _ _⟩, cubWeil_triv hx hy⟩

example {L : RigLB B} (c : CubicalStr B L) {N : ℕ} {y : T ⟶ B} (hy : y ^ N = 1) : CubWeil c N 1 y 1 :=
  ⟨one_pow _, hy, fun z J hJ => by
    have C := isCub_cubV c hJ
    simp only [cubN, C.face₂, C.face₃, map_one, _root_.one_mul]⟩

example (hG : GlobalFnsSt) (N : ℕ) : IsAbelianScheme (𝟙_ (Over S)) ∧ CubWeil (trivCub (𝟙_ (Over S))) N (1 : T ⟶ _) 1 1 ∧
    WeilIs (𝟙_ (Over S)) (trivRig _).L N (1 : T ⟶ _) 1 1 :=
  ⟨isAbelianScheme_unit S, cubWeil_triv (one_pow _) (one_pow _),
    (cubWeil_iff_weilIs hG (isAbelianScheme_unit S) (one_pow _) (one_pow _) 1).1 (cubWeil_triv (one_pow _) (one_pow _))⟩

theorem mul_self_eq_one_of_weilIs_inv (hG : GlobalFnsSt) (hB : IsAbelianScheme B) {L : RigLB B} {c : CubicalStr B L}
    {N : ℕ} {x y : T ⟶ B} {ζ : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) (h' : WeilIs B L.L N x y ζ⁻¹) : ζ * ζ = 1 :=
  mul_eq_one_iff_eq_inv.2 (h.unique ((cubWeil_iff_weilIs hG hB h.1 h.2.1 _).2 h'))

theorem exists_weilIs_not_inv (hG : GlobalFnsSt) (hW : WeilSt) (hN : WeilNondegSt) {K : Type} [Field K] [IsAlgClosed K]
    (P : PolAV (Spec (CommRingCat.of K))) (rig : LB.Gen (P.L.pull (eSec P.A))) (hr : rig.IsGen)
    (c : CubicalStr P.A ⟨P.L, rig, P.isLB, hr⟩) {N : ℕ} (ho : Odd N) (hK : (N : K) ≠ 0) {x : baseOver _ ⟶ P.A}
    (hx : x ^ N = 1) (h₁ : x ≠ 1) :
    ∃ y ζ, CubWeil c N x y ζ ∧ ζ ≠ 1 ∧ WeilIs P.A P.L N x y ζ ∧ ¬ WeilIs P.A P.L N x y ζ⁻¹ := by
  have := mt (hN K P N hK x hx) h₁
  push Not at this
  obtain ⟨y, hy, hxy⟩ := this
  obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil c hx hy
  have w : WeilIs P.A P.L N x y ζ := (cubWeil_iff_weilIs hG P.isAb hx hy ζ).1 hζ
  have n : ζ ≠ 1 := fun e => hxy (e ▸ w)
  refine ⟨y, ζ, hζ, n, w, fun h' => n ?_⟩
  have s := mul_self_eq_one_of_weilIs_inv hG P.isAb hζ h'
  obtain ⟨hex, hmul, -, -⟩ := hW _ P N (baseOver _)
  obtain ⟨k, rfl⟩ := ho
  have pw : ∀ j : ℕ, WeilIs P.A P.L (2 * k + 1 : ℕ) (x ^ (j + 1)) y (ζ ^ (j + 1)) := fun j => by
    induction j with
    | zero => rw [zero_add, pow_one, pow_one]; exact w
    | succ j ih => rw [pow_succ x, pow_succ ζ]; exact hmul _ _ _ _ _ ih w
  have a := pw (2 * k + 1)
  rw [pow_succ x, hx, _root_.one_mul] at a
  have b := (hex x y hx hy).unique a w
  rwa [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul, sq, s, one_pow, eq_comm] at b

end Abelian

end GlobalTheory.UU
end
