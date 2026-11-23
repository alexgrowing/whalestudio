import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

def thirdDiff {A U : Type} [CommGroup A] [CommGroup U] (f : A → U) (x y w : A) : U :=
  f (x * y * w) * (f (x * y))⁻¹ * (f (x * w))⁻¹ * (f (y * w))⁻¹ * f x * f y * f w * (f 1)⁻¹

section Sym

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

abbrev symLB (L : LB G.left) : LB G.left :=
  LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]

variable {G}

def rigV (L : RigLB G) {T : Over S} (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι) :
    (T.left.presheaf.stalk z)ˣ :=
  val (L := L.L) L.rig (toUnit T).left z J

def symV {L : LB G.left} (σ : LB.Gen (symLB G L)) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.ι) (x : T ⟶ G) : (T.left.presheaf.stalk z)ˣ :=
  val (L := L) σ x.left z J

variable (G)

structure CubSym where

  L : RigLB G

  cub : CubicalStr G L

  sym : LB.Gen (symLB G L.L)
  sym_gen : sym.IsGen
  sym_rig : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L)
  sym_cub : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
    ∀ x y w : T ⟶ G, cubV cub z J x⁻¹ y⁻¹ w⁻¹ = thirdDiff (symV sym z J) x y w * cubV cub z J x y w

variable {G}

def CubSym.IsInvolutive (L : CubSym G) : Prop :=
  ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.L.ι), Good L.L.L z J →
    ∀ x : T ⟶ G, symV L.sym z J x * symV L.sym z J x⁻¹ = 1

end Sym

section Iso

def isoV {Y' Y Z : Scheme.{0}} {L' : LB Y'} {L : LB Y} {F : Y' ⟶ Y} (w : LB.Iso L' (L.pull F))
    (z : Z) (J' : (Z ⟶ Y') → L'.ι) (J : (Z ⟶ Y) → L.ι) (ψ : Z ⟶ Y') : (Z.presheaf.stalk z)ˣ :=
  gm ψ z ((LB.div (L.pull F) L').U (fun _ => J (ψ ≫ F), J' ψ)) (w.s (fun _ => J (ψ ≫ F), J' ψ))

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G']
  [GrpObj G] [IsCommMonObj G]

structure IsRigIso (m : CubeMap G' G) (L' : RigLB G') (L : RigLB G)
    (w : LB.Iso L'.L (L.L.pull m.F)) : Prop where
  gen : w.IsGen
  rig : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig
    (m.rigPull L.L L.rig)

structure IsCubSymIso (m : CubeMap G' G) (L' : CubSym G') (L : CubSym G)
    (w : LB.Iso L'.L.L (L.L.L.pull m.F)) : Prop extends IsRigIso m L'.L L.L w where
  cub : LB.Gen.Maps (LB.linCombIso w (thφ G' (x3 G')) thε) L'.cub.t (m.thetaPull L.L.L L.cub.t)
  even : ∀ (Z : Scheme.{0}) (z : Z) (J' : (Z ⟶ G'.left) → L'.L.L.ι) (J : (Z ⟶ G.left) → L.L.L.ι),
    Good L'.L.L z J' → Good L.L.L z J → ∀ ψ : Z ⟶ G'.left,
      val (L := L.L.L) L.sym (ψ ≫ m.F) z J * isoV w z J' J ψ =
        isoV w z J' J (ψ ≫ (ι[G']).left) * val (L := L'.L.L) L'.sym ψ z J'

theorem IsCubSymIso.isPullCubical {m : CubeMap G' G} {L' : CubSym G'} {L : CubSym G}
    {w : LB.Iso L'.L.L (L.L.L.pull m.F)} (h : IsCubSymIso m L' L w) :
    m.IsPullCubical L'.cub L.cub := ⟨w, h.gen, h.rig, h.cub⟩

end Iso

section Triv

variable {S : Scheme.{0}} {H G : Over S} [GrpObj H] [IsCommMonObj H] [GrpObj G] [IsCommMonObj G]

abbrev lamOn (i : H ⟶ G) (L : LB G.left) : LB (H ⊗ G).left :=
  LB.LinComb L (K := Fin 4)
    ![((fst H G ≫ i) * snd H G).left, (fst H G ≫ i).left, (snd H G).left, (1 : H ⊗ G ⟶ G).left]
    ![1, -1, -1, 1]

def lamV {i : H ⟶ G} {L : LB G.left} (s : LB.Gen (lamOn i L)) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.ι) (t : T ⟶ H) (x : T ⟶ G) : (T.left.presheaf.stalk z)ˣ :=
  val (L := L) s (lift t x).left z J

structure IsBiextTriv {L : RigLB G} (c : CubicalStr G L) (i : H ⟶ G) [IsMonHom i]
    (s : LB.Gen (lamOn i L.L)) : Prop where
  gen : s.IsGen
  law₁ : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
    ∀ (t t' : T ⟶ H) (x : T ⟶ G), lamV s z J (t * t') x =
      cubV c z J (t ≫ i) (t' ≫ i) x * lamV s z J t x * lamV s z J t' x
  law₂ : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
    ∀ (t : T ⟶ H) (x x' : T ⟶ G), lamV s z J t (x * x') =
      cubV c z J (t ≫ i) x x' * lamV s z J t x * lamV s z J t x'

theorem IsBiextTriv.axes {L : RigLB G} {c : CubicalStr G L} {i : H ⟶ G} [IsMonHom i]
    {s : LB.Gen (lamOn i L.L)} (h : IsBiextTriv c i s) {T : Over S} {z : T.left}
    {J : (T.left ⟶ G.left) → L.L.ι} (hJ : Good L.L z J) (t : T ⟶ H) (x : T ⟶ G) :
    lamV s z J 1 x = 1 ∧ lamV s z J t 1 = 1 := by
  have a := h.law₁ T z J hJ 1 1 x
  have b := h.law₂ T z J hJ t 1 1
  have e : (1 : T ⟶ H) ≫ i = 1 := by simp [Hom.one_def]
  rw [e, (isCub_cubV c hJ).face, _root_.mul_one, _root_.one_mul] at a
  rw [(isCub_cubV c hJ).face₃, _root_.mul_one, _root_.one_mul] at b
  exact ⟨left_eq_mul.1 a, left_eq_mul.1 b⟩

def trivV {i : H ⟶ G} {L : LB G.left} (σ : LB.Gen (L.pull i.left)) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.ι) (t : T ⟶ H) : (T.left.presheaf.stalk z)ˣ :=
  val (L := L) σ t.left z J

structure IsCubTriv {L : RigLB G} (c : CubicalStr G L) (i : H ⟶ G) [IsMonHom i]
    (σ : LB.Gen (L.L.pull i.left)) : Prop where
  gen : σ.IsGen
  rig : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
    trivV σ z J 1 = rigV L z J
  cub : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
    ∀ t t' t'' : T ⟶ H,
      thirdDiff (trivV σ z J) t t' t'' = cubV c z J (t ≫ i) (t' ≫ i) (t'' ≫ i)

def IsEven (L : CubSym G) (i : H ⟶ G) [IsMonHom i] (σ : LB.Gen (L.L.L.pull i.left)) : Prop :=
  ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.L.ι), Good L.L.L z J →
    ∀ t : T ⟶ H, trivV σ z J t⁻¹ = symV L.sym z J (t ≫ i) * trivV σ z J t

def Induces {L : LB G.left} (i : H ⟶ G) [IsMonHom i] (σ : LB.Gen (L.pull i.left))
    (s : LB.Gen (lamOn i L)) : Prop :=
  ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.ι), Good L z J → ∀ t t' : T ⟶ H,
    lamV s z J t (t' ≫ i) =
      trivV σ z J (t * t') * (trivV σ z J t)⁻¹ * (trivV σ z J t')⁻¹ * trivV σ z J 1

def actV (L : RigLB G) {i : H ⟶ G} (s : LB.Gen (lamOn i L.L)) (σ : LB.Gen (L.L.pull i.left))
    {T : Over S} (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι) (t : T ⟶ H) (x : T ⟶ G) :
    (T.left.presheaf.stalk z)ˣ :=
  lamV s z J t x * trivV σ z J t * (rigV L z J)⁻¹

variable {B : Over S} [GrpObj B] [IsCommMonObj B]

structure IsDescent (L : RigLB G) (i : H ⟶ G) [IsMonHom i] (s : LB.Gen (lamOn i L.L))
    (σ : LB.Gen (L.L.pull i.left)) (q : G ⟶ B) [IsMonHom q] (M : RigLB B)
    (w : LB.Iso L.L (M.L.pull (CubeMap.ofHom q).F)) : Prop
    extends IsRigIso (CubeMap.ofHom q) L M w where
  kill : i ≫ q = 1
  equivariant : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι)
    (I : (T.left ⟶ B.left) → M.L.ι), Good L.L z J → Good M.L z I → ∀ (t : T ⟶ H) (x : T ⟶ G),
      isoV w z J I ((t ≫ i) * x).left * actV L s σ z J t x = isoV w z J I x.left

def IsCubSymDescent (L : CubSym G) (i : H ⟶ G) [IsMonHom i] (s : LB.Gen (lamOn i L.L.L))
    (σ : LB.Gen (L.L.L.pull i.left)) (q : G ⟶ B) [IsMonHom q] (M : CubSym B)
    (w : LB.Iso L.L.L (M.L.L.pull (CubeMap.ofHom q).F)) : Prop :=
  IsDescent L.L i s σ q M.L w ∧ IsCubSymIso (CubeMap.ofHom q) L M w

end Triv

section Pairing

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}
  (c : CubicalStr G L)

def IsPairing (N : ℕ) {T : Over S} (x x' : T ⟶ G) (e : Γ(T.left, ⊤)ˣ) : Prop :=
  x ^ N = 1 ∧ x' ^ N = 1 ∧ ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J : (T'.left ⟶ G.left) → L.L.ι), Good L.L z J →
    gm ρ.left z ⊤ e * cubN (cubV c z J) N 1 (ρ ≫ x) (ρ ≫ x') =
      cubN (cubV c z J) N 1 (ρ ≫ x') (ρ ≫ x)

theorem existsUnique_isPairing (N : ℕ) {T : Over S} (x x' : T ⟶ G) (hx : x ^ N = 1)
    (hx' : x' ^ N = 1) : ∃! e, IsPairing c N x x' e := by
  obtain ⟨u, hu, hv⟩ := exists_cubN c 1 x' x N
  obtain ⟨u', hu', hv'⟩ := exists_cubN c 1 x x' N
  obtain ⟨t, -, ht⟩ := exists_gen L.isLB (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      rw [hx, hx', mul_comm x' x]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen L.L _ _ _ _ u (LB.invGen L.L _ _ u'))
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ hu (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : T.left.Opens) ≤ LB.wchart L.L (PEmpty.elim : PEmpty → (T.left ⟶ G.left)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), ⟨hx, hx', fun T' ρ z J hJ => ?_⟩, fun e ⟨_, _, he⟩ => ?_⟩
  · have e1 : ρ ≫ (1 : T ⟶ G) = 1 := map_one (preHom ρ)
    have a := ht _ ρ.left z J hJ
    rw [val_mul hJ, val_inv, hv T' ρ z J hJ, hv' T' ρ z J hJ, e1,
      val_of t ρ.left z J PEmpty.elim (fun k => k.elim)] at a
    exact (congrArg (· * _) ((gm_res ρ.left z le trivial _).trans a)).trans (inv_mul_cancel_right _ _)
  · refine unit_ext fun y _ => ?_
    choose J hJ using fun χ : T.left ⟶ G.left => exists_chart L.isLB (χ y)
    have e1 : 𝟙 T ≫ (1 : T ⟶ G) = 1 := Category.id_comp _
    have a := ht _ (𝟙 T : T ⟶ T).left y J hJ
    rw [val_mul hJ, val_inv, hv T (𝟙 T) y J hJ, hv' T (𝟙 T) y J hJ, e1,
      val_of t _ y J PEmpty.elim (fun k => k.elim), ← he T (𝟙 T) y J hJ, mul_inv_cancel_right] at a
    exact a.symm.trans (gm_res _ y le trivial _).symm

def pairing (N : ℕ) {T : Over S} (x x' : T ⟶ G) (hx : x ^ N = 1) (hx' : x' ^ N = 1) :
    Γ(T.left, ⊤)ˣ := (existsUnique_isPairing c N x x' hx hx').exists.choose

theorem isPairing_pairing (N : ℕ) {T : Over S} (x x' : T ⟶ G) (hx : x ^ N = 1) (hx' : x' ^ N = 1) :
    IsPairing c N x x' (pairing c N x x' hx hx') :=
  (existsUnique_isPairing c N x x' hx hx').exists.choose_spec

end Pairing

section Torus

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

def charV (χ : X) {T : Over S} (z : T.left) (t : T ⟶ splitTorus S X) : (T.left.presheaf.stalk z)ˣ :=
  gm t.left z ⊤ (charUnit S X χ)

def IsStable (i : splitTorus S X ⟶ G) (U : G.left.Opens) : Prop :=
  ∀ (T : Over S) (z : T.left) (t : T ⟶ splitTorus S X) (x : T ⟶ G),
    x.left z ∈ U → ((t ≫ i) * x).left z ∈ U

def IsWeight (i : splitTorus S X ⟶ G) (χ : X) (U : G.left.Opens) (f : Γ(G.left, U)) : Prop :=
  IsStable i U ∧ ∀ (T : Over S) (z : T.left) (t : T ⟶ splitTorus S X) (x : T ⟶ G), x.left z ∈ U →
    gs ((t ≫ i) * x).left z U f = (charV χ z t).val * gs x.left z U f

structure IsWeightGen (i : splitTorus S X ⟶ G) (χ : X) {Y : Scheme.{0}} (M : LB Y) {K : Type}
    [Fintype K] (φ : K → (G.left ⟶ Y)) (ε : K → ℤ) (u : LB.Gen (LB.LinComb M φ ε)) : Prop where
  gen : u.IsGen
  invariant : ∀ (k : K) (T : Over S) (t : T ⟶ splitTorus S X) (x : T ⟶ G),
    ((t ≫ i) * x).left ≫ φ k = x.left ≫ φ k
  weight : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ Y) → M.ι), Good M z J →
    ∀ (t : T ⟶ splitTorus S X) (x : T ⟶ G),
      val u ((t ≫ i) * x).left z J = charV χ z t * val u x.left z J

variable {B : Over S} [GrpObj B]

structure IsTorusExt (i : splitTorus S X ⟶ G) (q : G ⟶ B) : Prop where
  free : Module.Free ℤ X
  finite : Module.Finite ℤ X
  comm : IsCommMonObj G
  abelian : IsAbelianScheme B
  i_hom : IsMonHom i
  q_hom : IsMonHom q
  isKernel : IsPullback i (toUnit _) q (η[B])
  locTriv : ∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧
    ∃ r : V.toScheme ⟶ G.left, r ≫ q.left = V.ι

def weightPart (i : splitTorus S X ⟶ G) (q : G ⟶ B) (χ : X) (V : B.left.Opens) :
    Set Γ(G.left, q.left ⁻¹ᵁ V) := {f | IsWeight i χ (q.left ⁻¹ᵁ V) f}

def IsLocalWeightGen (i : splitTorus S X ⟶ G) (q : G ⟶ B) (χ : X) (V : B.left.Opens)
    (u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ) : Prop := u.val ∈ weightPart i q χ V

def IsWeightBundle (i : splitTorus S X ⟶ G) (q : G ⟶ B) (χ : X) (N : LB B.left) : Prop :=
  N.IsLB ∧ ∃ u, IsWeightGen i χ N (K := PUnit) (fun _ => q.left) (fun _ => -1) u

theorem IsTorusExt.isStable {i : splitTorus S X ⟶ G} {q : G ⟶ B} (h : IsTorusExt i q)
    (V : B.left.Opens) : IsStable i (q.left ⁻¹ᵁ V) := by
  intro T z t x hx
  have := h.q_hom
  have e : ((t ≫ i) * x) ≫ q = x ≫ q := by
    rw [MonObj.mul_comp, Category.assoc, h.isKernel.w, ← Category.assoc, comp_toUnit,
      ← Hom.one_def, _root_.one_mul]
  have e' : (((t ≫ i) * x) ≫ q).left z ∈ V := by rw [e]; exact hx
  exact e'

end Torus

section Examples

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

def trivLB (Y : Scheme.{0}) : LB Y := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩

def trivGen {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ Y)) (ε : K → ℤ) :
    LB.Gen (LB.LinComb (trivLB Y) φ ε) := ⟨fun _ => 1⟩

theorem trivGen_isGen {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ Y)) (ε : K → ℤ) :
    (trivGen φ ε).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Finset.prod_eq_one fun _ _ =>
    (congrArg (· ^ _) ((congrArg _ (map_one _)).trans (map_one _))).trans (one_zpow _))
    (map_one _)).trans (_root_.mul_one _)).symm

theorem val_trivGen {Y Z W : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ Y)) (ε : K → ℤ)
    (r : W ⟶ Z) (z : W) (J) : val (trivGen φ ε) r z J = 1 := map_one _

def trivRig : RigLB G where
  L := trivLB _
  rig := trivGen _ _
  isLB := ⟨by simp [trivLB], fun _ => map_one _, fun _ _ _ =>
    ((congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)).trans (map_one _).symm⟩
  rigGen := trivGen_isGen _ _

def trivCubSym : CubSym G where
  L := trivRig G
  cub :=
    { t := trivGen _ _
      isGen := trivGen_isGen _ _
      face := fun _ => corr_of_val (trivRig G).isLB fun _ _ hJ =>
        (val_pull hJ _ _ _).trans ((val_trivGen _ _ _ _ _).trans (val_one _).symm)
      cubeSymmetric_swap_first := corr_of_val (trivRig G).isLB fun _ _ hJ =>
        (val_trivGen _ _ _ _ _).trans ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _)).symm
      cubeSymmetric_swap_last := corr_of_val (trivRig G).isLB fun _ _ hJ =>
        (val_trivGen _ _ _ _ _).trans ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _)).symm
      cocycle := corr_of_val (trivRig G).isLB fun _ _ hJ =>
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _))
          ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _)))).trans
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _))
          ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _)))).symm }
  sym := trivGen _ _
  sym_gen := trivGen_isGen _ _
  sym_rig := corr_of_val (trivRig G).isLB fun _ _ hJ =>
    (val_pull hJ _ _ _).trans ((val_trivGen _ _ _ _ _).trans (val_one _).symm)
  sym_cub := fun T z J _ x y w => by
    have a : ∀ x : T ⟶ G, symV (L := (trivRig G).L) (trivGen _ _) z J x = 1 := fun _ => val_trivGen _ _ _ _ _
    simp only [thirdDiff, a, inv_one, _root_.mul_one, _root_.one_mul]
    exact (val_trivGen _ _ _ _ _).trans (val_trivGen _ _ _ _ _).symm

example {H : Over S} [GrpObj H] [IsCommMonObj H] (i : H ⟶ G) [IsMonHom i] :
    IsBiextTriv (trivCubSym G).cub i (trivGen _ _) ∧ IsCubTriv (trivCubSym G).cub i (trivGen _ _) ∧
      IsEven (trivCubSym G) i (trivGen _ _) := by
  have a : ∀ (T : Over S) z J (x y w : T ⟶ G), cubV (trivCubSym G).cub z J x y w = 1 :=
    fun _ _ _ _ _ _ => val_trivGen _ _ _ _ _
  have b : ∀ (T : Over S) z J t (x : T ⟶ G),
      lamV (i := i) (L := (trivCubSym G).L.L) (trivGen _ _) z J t x = 1 :=
    fun _ _ _ _ _ => val_trivGen _ _ _ _ _
  have c : ∀ (T : Over S) z J (t : T ⟶ H),
      trivV (i := i) (L := (trivCubSym G).L.L) (trivGen _ _) z J t = 1 :=
    fun _ _ _ _ => val_trivGen _ _ _ _ _
  refine ⟨⟨trivGen_isGen _ _, fun T z J _ t t' x => by simp only [a, b, _root_.mul_one],
    fun T z J _ t x x' => by simp only [a, b, _root_.mul_one]⟩,
    ⟨trivGen_isGen _ _, fun T z J _ => (c _ _ _ _).trans (val_trivGen _ _ _ _ _).symm,
    fun T z J _ t t' t'' => by simp only [thirdDiff, a, c, inv_one, _root_.mul_one]⟩,
    fun T z J _ t => ?_⟩
  rw [c, c, _root_.mul_one]
  exact (val_trivGen _ _ _ _ _).symm

example (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [IsCommMonObj (splitTorus S X)] (B : Over S) [GrpObj B] [hB : IsAbelianScheme B] :
    IsTorusExt (G := splitTorus S X ⊗ B) (lift (𝟙 _) 1) (snd _ _) where
  free := inferInstance
  finite := inferInstance
  comm := have := hB.comm; inferInstance
  abelian := hB
  i_hom := by simp only [Hom.one_def]; infer_instance
  q_hom := inferInstance
  isKernel := ⟨⟨by simp [Hom.one_def]⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ fst _ _)
    (fun s => by
      have := s.condition
      ext1
      · simp
      · simp [Hom.one_def, this, toUnit_unique (toUnit s.pt) s.snd])
    (fun s => toUnit_unique _ _) (fun s m h _ => by simp [← h])⟩⟩
  locTriv := fun b => ⟨⊤, trivial, (⊤ : B.left.Opens).ι ≫ (lift 1 (𝟙 B) : B ⟶ splitTorus S X ⊗ B).left, by
    rw [Category.assoc, ← Over.comp_left]; simp⟩

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv
