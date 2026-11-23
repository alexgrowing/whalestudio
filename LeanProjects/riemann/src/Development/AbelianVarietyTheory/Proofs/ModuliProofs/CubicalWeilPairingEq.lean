import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FlatTors

theorem weilIs_of_cubWeil_of_proper {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (hpr : IsProper (pullback.snd G.hom f)) {L : RigLB G} (c : CubicalStr G L) (k : ℕ)
    (T : Over S') (x y : Over.mk (T.hom ≫ f) ⟶ G) (z : Γ(T.left, ⊤)ˣ) (h : GlobalTheory.UU.CubWeil c k x y z) :
    WeilIs G L.L (k : ℤ) x y z := by
  let G' : Over S' := (Over.pullback f).obj G
  have hp : IsGrpPullback G' G f (pullback.fst G.hom f) := isGrpPullback_pullback G f
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback f G hG
  have := hG'.comm
  have hA : IsAbelianScheme G' := ⟨hG'.comm, hG'.smooth, hpr, hG'.geomConnected⟩
  obtain ⟨hL, hr, ⟨c', hc'⟩, -⟩ := CubePf.cubePull _ _ G G' (cubeMapOf hp) L c
  have hw : pullback.fst G.hom f ≫ G.hom = G'.hom ≫ f := pullback.condition
  let β := GlobalTheory.UU.toBaseHom (GlobalTheory.UU.toBase_mul_pullback G f) T
  have inj : Function.Injective β := fun a b e =>
    Over.OverMorphism.ext (hp.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w a).trans (Over.w b).symm))
  have sur : Function.Surjective β := fun p =>
    ⟨Over.homMk (hp.1.lift p.left T.hom (Over.w p)) (hp.1.lift_snd _ _ _),
      Over.OverMorphism.ext (hp.1.lift_fst _ _ _)⟩
  obtain ⟨u, rfl⟩ := sur x
  obtain ⟨v, rfl⟩ := sur y
  have hu : u ^ k = 1 := inj (by rw [map_pow, map_one]; exact h.1)
  have hv : v ^ k = 1 := inj (by rw [map_pow, map_one]; exact h.2.1)
  obtain ⟨z', hz', -⟩ := GlobalTheory.UU.existsUnique_cubWeil c' hu hv
  have h₁ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f G G' (cubeMapOf hp) hw (GlobalTheory.UU.toBase_mul_pullback G f) L _ c c' hc'
    k T u v z' hz'
  obtain rfl : z = z' := h.unique h₁
  have h₂ := (GlobalTheory.UU.cubWeil_iff_weilIs GlobalTheory.SemiRigid.globalFns hA hu hv z).1 hz'
  exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ G G' f _ L.L _ L.isLB hL hp
    ⟨GlobalTheory.UU.pullIso _ _, GlobalTheory.UU.pullIso_isGen L.isLB _⟩ T k u v (β u) (β v) z rfl rfl).1 h₂

end GlobalTheory.FlatTors
