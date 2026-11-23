import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctorialOfUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.EndLattice

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem congMod_y_of_end : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (m : ℕ) (pk pk' : QkPt D.toPre K m) (x : TFK (R := R) K ⟶ A.A), 1 ≤ m → QkToAkU U.toUnifPre K m pk x → QkToAkU U.toUnifPre K m pk' (x ≫ E.aA) → CongMod m pk'.y (E'.h pk.y) := by
  intro R _ _ _ hBase G _ _ hG D A U E E' hE K _ _ _ m pk pk' x hm h1 h2
  haveI : CharZero R := hBase.2
  have hAdm := hBase.1
  obtain ⟨-, hFE⟩ := GlobalTheory.UT.functorial_of_unif R (maximalIdeal R) hAdm D A G hG U
  obtain ⟨-, hK⟩ := hFE E E' hE
  obtain ⟨hex, hiota, hmap⟩ := hK K
  have hcalc := (GlobalTheory.EndCalc.end_calculus GlobalTheory.firstFiveLaws R (maximalIdeal R) hAdm D A G hG U K E E E).2.1
  choose φ hφ using fun g => (hex g).exists
  have hadd : ∀ g g' : GtPtF D.toPre K, φ (g + g') = φ g + φ g' := fun g g' =>
    (isAdd_iff_eq _ _ _).1 (hcalc g g' (g + g') _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (hφ g) (hφ g') (hφ _))
  let φh : GtPtF D.toPre K →+ GtPtF D.toPre K :=
    AddMonoidHom.mk' φ hadd
  obtain ⟨h, hns, hio⟩ := pk.eq
  have hh : h = m • pk.g := (isNsmul_iff_eq _ _ _).1 hns
  let p' : QkPt D.toPre K m :=
    ⟨E'.h pk.y, φ pk.g, φ h, (isNsmul_iff_eq _ _ _).2 (by rw [hh]; exact map_nsmul φh m pk.g), hiota _ _ _ hio (hφ h)⟩
  have h3 : QkToAkU U.toUnifPre K m p' (x ≫ E.aA) := hmap m hm pk p' x rfl (hφ pk.g) h1
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hAdm D A G hG U K m hm
  have e : f p' = f pk' := ((hf.1 _ _).1 h3).symm.trans ((hf.1 _ _).1 h2)
  obtain ⟨z, hz, -⟩ := (hf.2.2.1 _ _).1 e
  exact ⟨z, hz⟩

end GlobalTheory.EndLattice
