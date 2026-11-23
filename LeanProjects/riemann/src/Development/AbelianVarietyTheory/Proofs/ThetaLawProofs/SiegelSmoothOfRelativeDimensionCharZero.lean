import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SiegDim

theorem card_torsion_of_level {G J : Type} [Group G] [Fintype J] (k : ℕ) (hk : k ≠ 0) (l : (J → ℤ) → G)
    (hadd : ∀ a b, l (a + b) = l a * l b) (htors : ∀ a, l a ^ k = 1)
    (hker : ∀ a, l a = 1 ↔ ∃ b, a = k • b) (hsurj : ∀ g : G, g ^ k = 1 → ∃ a, l a = g) :
    Nat.card {g : G // g ^ k = 1} = k ^ Fintype.card J := by
  classical
  have : NeZero k := ⟨hk⟩
  have key : ∀ a b, l a = l b ↔ ∀ i, ((a i : ℤ) : ZMod k) = (b i : ℤ) := fun a b => by
    have e : l b = l a * l (b - a) := by rw [← hadd]; congr 1; abel
    rw [e, left_eq_mul, hker]
    constructor
    · rintro ⟨c, hc⟩ i
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact ⟨c i, by simpa using congrFun hc i⟩
    · intro H
      choose c hc using fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (H i)
      exact ⟨c, funext fun i => by simpa using hc i⟩
  let F : (J → ZMod k) → {g : G // g ^ k = 1} := fun c => ⟨l fun i => ((c i).val : ℤ), htors _⟩
  have hF : Function.Bijective F := by
    constructor
    · intro c c' e
      funext i
      simpa using (key _ _).1 (congrArg Subtype.val e) i
    · rintro ⟨g, hg⟩
      obtain ⟨a, rfl⟩ := hsurj g hg
      exact ⟨fun i => (a i : ZMod k), Subtype.ext ((key _ _).2 fun i => by simp)⟩
  rw [← Nat.card_eq_of_bijective F hF]
  simp [Nat.card_pi]

noncomputable def pointsEquiv {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) (T : Over S') :
    (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G) where
  toFun y := Over.homMk (y.left ≫ φ) (by simp [hp.1.w])
  invFun q := Over.homMk (hp.1.lift q.left T.hom (Over.w q)) (hp.1.lift_snd _ _ _)
  left_inv y := Over.OverMorphism.ext (hp.1.hom_ext (by simp) (by simp))
  right_inv q := Over.OverMorphism.ext (by simp)
  map_mul' y y' := Over.OverMorphism.ext (hp.2 T y y' _ _ rfl rfl).symm

theorem dim_geometric_fibre {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (c : SiegPre h k ζ s) (hk : 2 ≤ k) (hζ : IsUnit ζ) {K : Type} [Field K] [IsAlgClosed K] (hK : (k : K) ≠ 0)
    (x : Sp K ⟶ S) {d : ℕ} (hd : SmoothOfRelativeDimension d ((Over.pullback x).obj c.A).hom) : d = h := by
  let T := 𝟙_ (Over (Sp K))
  let β : o →+* K := (Spec.preimage ((T.hom ≫ x) ≫ s)).hom
  have hβ : (T.hom ≫ x) ≫ s = spMap β := (Spec.map_preimage ((T.hom ≫ x) ≫ s)).symm
  obtain ⟨h₁, h₂, -⟩ := c.geom K (T.hom ≫ x) β (hζ.map β).unit hβ rfl
  have n₁ := card_torsion_of_level k (by omega) (fun a => toUnit (Over.mk (T.hom ≫ x)) ≫ c.lev a)
    (fun a b => by rw [c.lev_add, MonObj.comp_mul])
    (fun a => by rw [← MonObj.comp_pow, c.lev_tors, MonObj.comp_one]) h₁ h₂
  have := c.ab.comm
  have := c.ab.smooth
  have := c.ab.proper
  have := c.ab.geomConnected
  have hab : IsAbelianScheme ((Over.pullback x).obj c.A) :=
    { comm := Functor.isCommMonObj_obj
      smooth := by change Smooth (pullback.snd c.A.hom x); infer_instance
      proper := by change IsProper (pullback.snd c.A.hom x); infer_instance
      geomConnected := by change GeometricallyConnected (pullback.snd c.A.hom x); infer_instance }
  have n₂ := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional K _ d k hab hd hK
  let e := pointsEquiv (isGrpPullback_pullback c.A x) T
  have n₃ := Nat.card_congr (e.toEquiv.subtypeEquiv (p := fun y => y ^ k = 1) (q := fun y => y ^ k = 1)
    fun y => by
      change _ ↔ e y ^ k = 1
      rw [← map_pow, MulEquiv.map_eq_one_iff])
  have n₄ : k ^ (2 * d) = k ^ (h + h) := by
    rw [← n₂, n₃, n₁]; simp
  have := Nat.pow_right_injective hk n₄
  omega

theorem smoothOfRelativeDimension :
    Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [Algebra ℚ R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)), 2 ≤ k → IsUnit ζ → SmoothOfRelativeDimension h c.A.hom := by
  intro _ h k o _ ζ R _ _ β c hk hζ
  have := c.ab.smooth
  have := c.ab.geomConnected
  choose n W hW hd using H1.exists_dim c.A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension h) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let κ := (Sp R).residueField (c.A.hom y)
  let K := AlgebraicClosure κ
  let x : Sp K ⟶ Sp R := spMap (algebraMap κ K) ≫ (Sp R).fromSpecResidueField (c.A.hom y)
  have hK : (k : K) ≠ 0 := by
    have := map_natCast ((Spec.preimage x).hom.comp (algebraMap ℚ R)) k
    rw [← this]
    exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 (by omega))
  have hp := (isGrpPullback_pullback c.A x).1
  obtain ⟨y', hy', -⟩ := Scheme.exists_preimage_of_isPullback hp y (default : PrimeSpectrum K)
    (Scheme.fromSpecResidueField_apply _ _).symm
  have : Smooth ((Over.pullback x).obj c.A).hom := by change Smooth (pullback.snd c.A.hom x); infer_instance
  have : ConnectedSpace ((Over.pullback x).obj c.A).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := c.A.hom) x _ _ hp
  obtain ⟨d, hd'⟩ := exists_dim_of_preconnected ((Over.pullback x).obj c.A).hom y'
  have e : n y = h :=
    (H1.dim_base hp (hd y) hd' y' (by rw [hy']; exact hW y)).trans (dim_geometric_fibre c hk hζ hK x hd')
  have := hd y
  rwa [e] at this

end GlobalTheory.SiegDim
