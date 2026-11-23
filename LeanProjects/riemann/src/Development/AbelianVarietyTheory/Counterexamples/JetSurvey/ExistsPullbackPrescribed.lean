import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalSymmetryTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSymmetricIffExistsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SabBaseChange

theorem lbIso_cube {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L M : LB G.left} (h : LBIso L M) : LBIso (cubeLB G x L) (cubeLB G x M) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨_, DVR.linCombIso_isGen w hw _ _⟩

theorem cube_isLB {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L : LB G.left} (h : L.IsLB) : (cubeLB G x L).IsLB := DVR.linComb_isLB _ h _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pullback_prescribed {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S)
    (PP' : RigLB ((Over.pullback f).obj t.G))
    (hw : ∃ w : LB.Iso PP'.L (t.PP.L.pull (pullback.fst t.G.hom f)), w.IsGen) :
    ∃ (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
      (m : SABMap ⟨(Over.pullback f).obj t.G, IsSemiAbelian.pullback f t.G t.semi, OAct.pullback f t.G t.act, PP', cub,
        sym, adj, prim⟩ t f), m.φ = pullback.fst t.G.hom f := by
  have h := isGrpPullback_pullback t.G f
  obtain ⟨P₀, c₀, s₀, adj₀, prim₀, m₀, hm₀⟩ := sabPull Out.CubePf.cubePull f t
  have hP : (t.PP.L.pull (pullback.fst t.G.hom f)).IsLB := DVR.linComb_isLB _ t.PP.isLB _ _
  have i₀ : LBIso P₀.L (t.PP.L.pull (pullback.fst t.G.hom f)) := by
    obtain ⟨w, hw, -⟩ := m₀.lin
    rw [← hm₀]; exact ⟨w, hw⟩
  have i : LBIso PP'.L P₀.L := LBIso.trans PP'.isLB hP P₀.isLB hw i₀.symm
  obtain ⟨w, hg, hr⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso S S' f t.G _ _ (cubeMapOf h).e_comm t.PP PP' hw
  obtain ⟨s, hs, hs'⟩ := (GlobalTheory.isSymmetric_iff_exists_gen S t.G t.PP).1 t.sym
  obtain ⟨c', s', h₁, h₂, h₃, -⟩ :=
    GlobalTheory.cubical_symmetry_transport S S' f t.G _ _ h t.PP PP' w (cubeMapOf h).e_comm hg hr t.cub s hs hs'
  refine ⟨c', (GlobalTheory.isSymmetric_iff_exists_gen S' _ PP').2 ⟨s', h₁, h₂⟩, fun a => ?_, ?_,
    ⟨cubeMapOf h, h, rfl, fun a => pullback.lift_fst _ _ _, w, hg, hr, ?_⟩, rfl⟩
  · exact LBIso.trans (cube_isLB _ PP'.isLB) (cube_isLB _ P₀.isLB) (cube_isLB _ PP'.isLB)
      (LBIso.trans (cube_isLB _ PP'.isLB) (cube_isLB _ P₀.isLB) (cube_isLB _ P₀.isLB) (lbIso_cube _ i) (adj₀ a))
      (lbIso_cube _ i.symm)
  · exact LBIso.trans PP'.isLB (cube_isLB _ P₀.isLB) (cube_isLB _ PP'.isLB)
      (LBIso.trans PP'.isLB P₀.isLB (cube_isLB _ P₀.isLB) i prim₀) (lbIso_cube _ i.symm)
  · exact (maps_iff w _ (thφ t.G (x3 t.G)) _ c'.t t.cub.t (cubeMapOf h).F3 _ ((cubeMapOf h).theta_le t.PP.L)
      (fun _ => rfl)).2 h₃

theorem exists_prescribed {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ PP' : RigLB ((Over.pullback f).obj t.G),
      ∃ w : LB.Iso PP'.L (t.PP.L.pull (pullback.fst t.G.hom f)), w.IsGen := by
  obtain ⟨P₀, c₀, s₀, adj₀, prim₀, m₀, hm₀⟩ := sabPull Out.CubePf.cubePull f t
  obtain ⟨w, hw, -⟩ := m₀.lin
  refine ⟨P₀, ?_⟩
  rw [← hm₀]; exact ⟨w, hw⟩

theorem isGrpPullback_inv {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] :
    IsGrpPullback G G (𝟙 S) (ι[G]).left := by
  have hi : ι[G] ≫ ι[G] = 𝟙 G := GrpObj.inv_comp_inv G
  have : IsIso (ι[G]).left := ⟨⟨(ι[G]).left, by rw [← Over.comp_left, hi, Over.id_left],
    by rw [← Over.comp_left, hi, Over.id_left]⟩⟩
  refine ⟨IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  have e := mul_left_congr (G := G) (a := T.hom ≫ 𝟙 S) (b := T.hom) (Category.comp_id _) x₀ y₀ x⁻¹ y⁻¹ hx hy
  refine e.trans ?_
  exact congrArg (fun z : T ⟶ G => z.left) (mul_inv x y).symm

end GlobalTheory.SabBaseChange
