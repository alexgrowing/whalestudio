import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaLin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushSecOfLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.PreEtaPull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
  {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

theorem one_left (h : IsGrpPullback A' A f φ) : (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  have e : (1 : A' ⟶ A').left ≫ φ = (1 : Over.mk (A'.hom ≫ f) ⟶ A).left :=
    congrArg (fun q => q.left) (map_one (pushHom h A'))
  rw [e, Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left,
    ← Category.assoc, h.1.w]
  rfl

theorem lift_one_id (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (1 : A' ⟶ A') (𝟙 A')
    (Z := A) φ (1 : A ⟶ A) (𝟙 A) (by exact (Category.id_comp _).trans (one_left h)) (by simp)
  exact (Category.id_comp _).symm.trans this

theorem lift_id_one (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (1 : A ⟶ A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (𝟙 A') (1 : A' ⟶ A')
    (Z := A) φ (𝟙 A) (1 : A ⟶ A) (by simp) (by exact (Category.id_comp _).trans (one_left h))
  exact (Category.id_comp _).symm.trans this

omit [GrpObj A] [GrpObj A'] in

theorem lift_swap (sq : IsSquare φ φ₂) :
    (lift (snd A' A') (fst A' A')).left ≫ φ₂ = φ₂ ≫ (lift (snd A A) (fst A A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (A ⊗ A).hom)) (T' := A' ⊗ A') (𝟙 _) (snd A' A') (fst A' A')
    (Z := A ⊗ A) φ₂ (snd A A) (fst A A) (by exact (Category.id_comp _).trans sq.2.symm)
    (by exact (Category.id_comp _).trans sq.1.symm)
  exact (Category.id_comp _).symm.trans this

end GlobalTheory.PreEtaPull

namespace GlobalTheory.UPel.HT

open GlobalTheory.PreEtaPull

theorem exists_preEta_of_siegPull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ o : PreEta b N (πX ≫ t), ∀ (k : Type) [Field k] (x : Sp k ⟶ X), (o.GeomAt k x ↔ GeomAt D N actX (c.P.pull φ₂X) ηX k x) := by
  intro p _ D R _ b N h M B _ ζ S s₁ t c e he hK X πX AX _ _ φX φ₂X actX ηX hpb hsq hros heta
  have hP : (c.P.pull φ₂X).IsLB := pull_isLB c.isLB φ₂X
  have H : LBIso (c.P.pull φ₂X) (c.P.pull φ₂X) := ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ hP
  refine ⟨{
    A := AX
    ab := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab hpb
    act := actX
    P := c.P.pull φ₂X
    isLB := hP
    rig₁ := by
      obtain ⟨t₁, ht₁⟩ := c.rig₁
      exact gen_chartPull (chartPullLinComb c.P φ₂X _ _ _ φX fun _ => lift_one_id hpb hsq) t₁ ht₁
    rig₂ := by
      obtain ⟨t₂, ht₂⟩ := c.rig₂
      exact gen_chartPull (chartPullLinComb c.P φ₂X _ _ _ φX fun _ => lift_id_one hpb hsq) t₂ ht₂
    symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P _ _ rfl)
      (chartPullLinComb c.P _ _ _ _ φ₂X fun _ => lift_swap hsq) c.symm
    ample := (GlobalTheory.pol_pull S X c.A AX πX φX c.diag _ (pull_isLB c.isLB _) (pull_isLB hP _) c.ab hpb
      (GlobalTheory.SiegelPull.diag_iso hsq H)).2.1 hK.1
    kerP := ⟨e, he, kerBy_pull hpb hsq c.isLB hP H e hK.2⟩
    rosati := hros
    eta := ηX
    eta_add := heta.1
    eta_lin := heta.2.1
    eta_ker := heta.2.2 }, fun k _ x => Iff.rfl⟩

end GlobalTheory.UPel.HT
