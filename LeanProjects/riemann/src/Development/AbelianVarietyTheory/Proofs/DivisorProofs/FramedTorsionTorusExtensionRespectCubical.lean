import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HRedFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralDataFramedTorsionPointTorusExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointFrameMulEqIntegralGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationSectionsExtendingPointsMultiplyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalPointsAbelianPartsMultiplyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramesRespectCubicalStructuresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationCubicalStructureGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

namespace GlobalTheory.Poinc.Sep.LiesCube

theorem alternating_alg {M : Type} [CommGroup M] (u e w f t : Finset (Fin 3) → M) (a b c : M)
    (v : ∀ S, u S * e S * w S = f S * t S)
    (c₁ : f {0, 1, 2} * f {0} * f {1} * f {2} * (t {0, 1, 2} * t {0} * t {1} * t {2}) * b =
      a * (f {0, 1} * f {0, 2} * f {1, 2} * f ∅) * (t {0, 1} * t {0, 2} * t {1, 2} * t ∅))
    (c₂ : u {0, 1, 2} * u {0} * u {1} * u {2} * c = a * (u {0, 1} * u {0, 2} * u {1, 2} * u ∅)) :
    e {0, 1, 2} * e {0} * e {1} * e {2} * (w {0, 1, 2} * w {0} * w {1} * w {2}) * b =
      c * (e {0, 1} * e {0, 2} * e {1, 2} * e ∅) * (w {0, 1} * w {0, 2} * w {1, 2} * w ∅) := by
  have E := fun {p q : M} (e : p = q) => congrArg Additive.ofMul e
  have v₀ := E (v ∅); have v₁ := E (v {0}); have v₂ := E (v {1}); have v₃ := E (v {2})
  have v₄ := E (v {0, 1}); have v₅ := E (v {0, 2}); have v₆ := E (v {1, 2}); have v₇ := E (v {0, 1, 2})
  have d₁ := E c₁; have d₂ := E c₂
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at *
  linear_combination (norm := abel) v₁ + v₂ + v₃ + v₇ - v₀ - v₄ - v₅ - v₆ + d₁ - d₂

theorem cube_of_liesOver : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) (c : CubicalStr A.A ⟨A.L, ρ, A.isLB, hρ⟩) (g : Finset (Fin 3) → GtPtF D.toPre (FractionRing V)) (w : ∀ S, Frm D.toPre (FractionRing V) 1 (g S).b) (x : Finset (Fin 3) → (TFK (R := V) (FractionRing V) ⟶ A.A)) (e : ∀ S, FrAt (x S)), x ∅ = 1 → x {0, 1} = x {0} * x {1} → x {0, 2} = x {0} * x {2} → x {1, 2} = x {1} * x {2} → x {0, 1, 2} = x {0} * x {1} * x {2} → (∀ S, (∃ o, GtPtF.IsNsmul N (g S) o ∧ o.IsZero) ∧ (w S).IsGen ∧ (e S).IsGen ∧ LiesOver U.toUnifPre w₀ (g S) (w S) (x S) (e S)) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JB : ((TF (R := V) (FractionRing V)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good A.L z JA → Good D.toPre.P.L z JB → @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 1, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {1}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {2}) (𝟙 _) z JA) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 1, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {1}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {2}) (𝟙 _) z JB)) * cubV D.toPre.cub z JB (g {0}).b (g {1}).b (g {2}).b = @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x {0}) (x {1}) (x {2})) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 1}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {1, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e ∅) (𝟙 _) z JA)) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 1}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {1, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w ∅) (𝟙 _) z JB)) := by
  intro V _ _ _ hV D A G _ _ hG U w₀ hw₀ N hN ρ hρ c g w x e hx₀ hx₁ hx₂ hx₃ hx₄ hS z JA JB hJA hJB
  choose h g' f t hF hE hP hf ht hT using fun S => GlobalTheory.T.exists_integral_data_framed_torsion_point_torus_ext V hV D A G hG U w₀ hw₀ N hN (g S) (w S) (x S) (e S)
    (hS S).1 (hS S).2.1 (hS S).2.2.1 (hS S).2.2.2
  have hm : ∀ S T S', x S' = x S * x T → h S' = h S * h T ∧ (g' S').b = (g' S).b * (g' T).b := fun S T S' hx => by
    have a := GlobalTheory.T.uniformisation_sections_extending_points_multiply V hV D A G hG U (x S) (x T) (h S) (h T) (h S') (hE S) (hE T) (hx ▸ hE S')
    exact ⟨a, GlobalTheory.T.formal_points_abelian_parts_multiply V hV D A G hG U (h S) (h T) (g' S) (g' T) (g' S') (hF S) (hF T) (a ▸ hF S')⟩
  have m₀ := hm ∅ ∅ ∅ (by rw [hx₀, _root_.mul_one])
  have m₁ := hm _ _ _ hx₁
  have m₂ := hm _ _ _ hx₂
  have m₃ := hm _ _ _ hx₃
  have m₄ := hm {0, 1} {2} {0, 1, 2} (by rw [hx₄, hx₁])
  have a₀ : h ∅ = 1 := mul_eq_left.1 m₀.1.symm
  have b₀ : (g' ∅).b = 1 := mul_eq_left.1 m₀.2.symm
  have a₄ : h {0, 1, 2} = h {0} * h {1} * h {2} := m₄.1.trans (by rw [m₁.1])
  have b₄ : (g' {0, 1, 2}).b = (g' {0}).b * (g' {1}).b * (g' {2}).b := m₄.2.trans (by rw [m₁.2])
  obtain ⟨JG, hJG⟩ : ∃ J, Good U.LG.L z J := by
    choose I hI using fun χ : _ ⟶ G.left => exists_chart U.LG.isLB (χ z)
    exact ⟨I, hI⟩
  have v := fun S => GlobalTheory.T.torsionPointFrame_mul_eq_integralGenerators V hV D A G hG U w₀ hw₀ N hN (g S) (w S) (x S) (e S)
    (hS S).1 (hS S).2.1 (hS S).2.2.1 (hS S).2.2.2 (h S) (g' S) (f S) (t S) (hF S) (hE S) (hP S) (hf S) (ht S) (hT S)
    z JA JG JB hJA hJG hJB
  have c₁ := GlobalTheory.T.integral_frames_respect_cubical_structures V hV D A G hG U h g' f t a₀ m₁.1 m₂.1 m₃.1 a₄ b₀ m₁.2 m₂.2 m₃.2 b₄ hF hf ht hT z JG JB hJG hJB
  have c₂ := GlobalTheory.T.uniformisation_cubical_structure_generic_fibre V hV D A G hG U w₀ hw₀ ρ hρ c x h hx₀ hx₁ hx₂ hx₃ hx₄ a₀ m₁.1 m₂.1 m₃.1 a₄ hE z JA JG hJA hJG
  have hb : ∀ S, toUnit (TF (R := V) (FractionRing V)) ≫ (g' S).b = (g S).b := fun S =>
    Over.OverMorphism.ext (hP S).1.symm
  rw [hb, hb, hb] at c₁
  exact alternating_alg (M := ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ) _
    (fun S => val (Z := (TF (R := V) (FractionRing V)).left) (e S) (𝟙 _) z JA) (fun S => val (w S) (𝟙 _) z JB)
    (fun S => val (f S) (toUnit (TF (R := V) (FractionRing V))).left z JG)
    (fun S => val (t S) (toUnit (TF (R := V) (FractionRing V))).left z JB) _ _ _ v c₁ c₂

end GlobalTheory.Poinc.Sep.LiesCube
