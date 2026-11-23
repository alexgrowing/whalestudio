import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentLinearisedLineBundleGaloisCover
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDescentSymmetricLinearisedBundle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke.PullInj

variable {X Y Z : Scheme.{0}}

theorem gen_germ {L : LB X} {w : LB.Gen L} (hw : w.IsGen) (r : Z ⟶ X) (z : Z) {k l : L.ι}
    (hk : r z ∈ L.U k) (hl : r z ∈ L.U l) :
    gm r z _ (w.s k) = gm r z (L.U k ⊓ L.U l) (L.g k l) * gm r z _ (w.s l) := by
  have hm : r z ∈ L.U k ⊓ L.U l := ⟨hk, hl⟩
  exact (gm_res r z inf_le_left hm _).symm.trans ((congrArg (gm r z _) (hw k l)).trans
    ((map_mul _ _ _).trans (congrArg _ (gm_res r z inf_le_right hm _))))

theorem gm_pull_g (Q : LB Y) (F : X ⟶ Y) (r : Z ⟶ X) (z : Z) {j j' : PUnit → Q.ι}
    (hj : F (r z) ∈ Q.U (j PUnit.unit)) (hj' : F (r z) ∈ Q.U (j' PUnit.unit)) :
    gm r z ((Q.pull F).U j ⊓ (Q.pull F).U j') ((Q.pull F).g j j') =
      gm (r ≫ F) z (Q.U (j PUnit.unit) ⊓ Q.U (j' PUnit.unit)) (Q.g (j PUnit.unit) (j' PUnit.unit)) := by
  have hp : r z ∈ (Q.pull F).U j ⊓ (Q.pull F).U j' := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm r z _ (∏ _k : PUnit, (res _ (pullU F _ (Q.g _ _))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res r z _ hp _).trans (gm_pull r F z (Q.U (j PUnit.unit) ⊓ Q.U (j' PUnit.unit)) ⟨hj, hj'⟩ _)

theorem germ_div_g (M L : LB X) (r : Z ⟶ X) (z : Z) {p q : M.ι × L.ι}
    (hp : r z ∈ (LB.div M L).U p) (hq : r z ∈ (LB.div M L).U q) :
    gm r z _ ((LB.div M L).g p q) =
      gm r z (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) * (gm r z (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ := by
  have hm : r z ∈ (LB.div M L).U p ⊓ (LB.div M L).U q := ⟨hp, hq⟩
  show gm r z _ (res _ (M.g _ _) * (res _ (L.g _ _))⁻¹) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _) ((map_inv _ _).trans (congrArg _ (gm_res r z _ hm _))))

theorem mem_divPull {Q₁ Q₂ : LB Y} {F : X ⟶ Y} {x : X} {k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)} :
    x ∈ (LB.div (Q₂.pull F) (Q₁.pull F)).U k ↔ F x ∈ Q₂.U (k.1 PUnit.unit) ∧ F x ∈ Q₁.U (k.2 PUnit.unit) :=
  ⟨fun h => ⟨mem_pull.1 h.1, mem_pull.1 h.2⟩, fun h => ⟨mem_pull.2 h.1, mem_pull.2 h.2⟩⟩

theorem gm_top_eq {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (g : Γ(A.left, ⊤)ˣ)
    (r r' : Z ⟶ A.left) (e : r ≫ A.hom = r' ≫ A.hom) (z : Z) : gm r z ⊤ g = gm r' z ⊤ g := by
  obtain ⟨c, hc⟩ := (GlobalTheory.globalFns_holds S A hA).2 g.val
  have h1 : ∀ r₀ : Z ⟶ A.left, gs r₀ z ⊤ g.val = gs (r₀ ≫ A.hom) z ⊤ c := fun r₀ => by
    rw [← hc]; exact gs_pull r₀ A.hom z ⊤ trivial c
  apply Units.ext
  rw [← gs_unit r z ⊤ trivial, ← gs_unit r' z ⊤ trivial, h1, h1, e]

end GlobalTheory.UPel.HT.Hecke.PullInj

namespace GlobalTheory.UPel.HT.Hecke.PullInj

variable {S : Scheme.{0}}

theorem transl_axis₁ (A : Over S) [GrpObj A] [IsCommMonObj A] (h : 𝟙_ (Over S) ⟶ A) :
    lift (1 : A ⟶ A) (𝟙 A) ≫ transl (lift (1 : 𝟙_ (Over S) ⟶ A) h : 𝟙_ (Over S) ⟶ G2 A) =
      transl h ≫ lift (1 : A ⟶ A) (𝟙 A) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]

theorem transl_axis₂ (A : Over S) [GrpObj A] [IsCommMonObj A] (h : 𝟙_ (Over S) ⟶ A) :
    lift (𝟙 A) (1 : A ⟶ A) ≫ transl (lift h (1 : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S) ⟶ G2 A) =
      transl h ≫ lift (𝟙 A) (1 : A ⟶ A) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]

theorem grpScheme_monHom_square_lift_one_left {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A')
    [IsMonHom ψ] : lift (1 : A ⟶ A) (𝟙 A) ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) = ψ ≫ lift (1 : A' ⟶ A') (𝟙 A') := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp

theorem grpScheme_monHom_square_lift_one_right {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A')
    [IsMonHom ψ] : lift (𝟙 A) (1 : A ⟶ A) ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) = ψ ≫ lift (𝟙 A') (1 : A' ⟶ A') := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp

end GlobalTheory.UPel.HT.Hecke.PullInj
