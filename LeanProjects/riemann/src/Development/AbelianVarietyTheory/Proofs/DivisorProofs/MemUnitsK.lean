import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEvenCubicalValuesNotMemMaximalIdealPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositive
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitValEqMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInIffScalarMem
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiScalarsRelationsUpToBaseUnits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit

noncomputable section

namespace GlobalTheory.Mum.TensPol

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem exists_int (A : Over (Spec (CommRingCat.of R))) [IsSeparated A.hom] (L : LB A.left) (hL : L.IsLB) (z : (TK R).left) :
    ∃ J, Good L z J ∧
      ∀ p : Spec (CommRingCat.of R) ⟶ A.left, p ≫ A.hom = 𝟙 _ → p (closedPoint R) ∈ L.U (J (jK R ≫ p)) := by
  have : IsDominant (jK R) := DVR.isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ A.left => exists_chart hL (p (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good L hL (Z := (TK R).left) z
    (K := {p : Spec (CommRingCat.of R) ⟶ A.left // p ≫ A.hom = 𝟙 _}) (fun p => jK R ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R)) A.hom
      (a.2.trans b.2.symm) (jK R) h))
    (fun p => (IsLocalRing.specializes_closedPoint (jK R z)).mem_open (p.1 ⁻¹ᵁ L.U (pick p.1)).isOpen (hpk p.1))
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

theorem val_mem {A : Over (Spec (CommRingCat.of R))} {L : LB A.left} (z : (TK R).left) {J : ((TK R).left ⟶ A.left) → L.ι}
    (hJ : ∀ p : Spec (CommRingCat.of R) ⟶ A.left, p ≫ A.hom = 𝟙 _ → p (closedPoint R) ∈ L.U (J (jK R ≫ p)))
    {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of R) ⟶ A.left)) (hφ : ∀ k, φ k ≫ A.hom = 𝟙 _) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) : val t (toUnit (TK R)).left z J ∈ unitsS z := by
  have := gm_mem z (𝟙 _) (LB.wchart L φ (fun k => J (jK R ≫ φ k))) (Set.mem_iInter.2 fun k => hJ (φ k) (hφ k))
    (t.s (fun k => J (jK R ≫ φ k)))
  rw [Category.comp_id] at this
  exact this

theorem mem_unitsK (z : (TK R).left) {x : (FractionRing R)ˣ} (h : Units.map (ev z).toMonoidHom x ∈ unitsS z) : x ∈ unitsK R := by
  obtain ⟨y, hy, e⟩ := h
  exact (Units.map_injective (ev_inj z) e) ▸ hy

theorem gm_unitOn (z : (TK R).left) (k : (FractionRing R)ˣ) :
    gm (𝟙 (TK R).left) z ⊤ (unitOn k) = Units.map (ev z).toMonoidHom k :=
  Units.ext ((gs_unit _ z ⊤ trivial _).symm.trans (ev_eq z k))

end GlobalTheory.Mum.TensPol
