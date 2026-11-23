import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymFrameClause
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToFSurjectiveFractionRing
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGroupShiftHalfTorsionRoot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_eqv_expandsF : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → CharZero R → ∀ (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), IsSemiAbelian G → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ (w₀ : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w₀.IsGen → ∀ lab : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A), (∀ p, QkToAkU U.toUnifPre F N p (lab p)) → ∃ E, Eqv D.toPre A F N lab E ∧ ∀ s, U.ExpandsF F N w₀ (E s) s := by
  intro R _ _ I hI hC D A G _ _ U hG F _ _ _ N hN w₀ hw₀ lab hlab
  haveI := hC
  have hL : GlobalTheory.UT.LL := ⟨GlobalTheory.allSixLaws.1, GlobalTheory.allSixLaws.2.1, GlobalTheory.allSixLaws.2.2.1, GlobalTheory.allSixLaws.2.2.2.1,
    GlobalTheory.allSixLaws.2.2.2.2.1⟩
  have gf : GlobalFnsSt := hL.1.globalFns
  have hN1 : 1 ≤ N := hN.pos
  obtain ⟨hbij, hlin⟩ := GlobalTheory.UT.expBijF_and_expandsF_lin hL R I hI D A G hG U
  obtain ⟨b₁, b₂⟩ := hbij F N hN1 w₀ hw₀
  choose E hE using fun s => (b₂ s).exists
  obtain ⟨f, hf, hfN⟩ := GlobalTheory.TorsionIso.torsion_clause R I hI D A G hG U F N hN1
  have hlabf : ∀ p, lab p = f p := fun p => (hf.1 p (lab p)).1 (hlab p)
  have hSF := GlobalTheory.SymFrameClause.symFrame_clause R I hI D A G hG U F N hN
  refine ⟨E, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hE⟩
  · refine ⟨fun s s' h => ?_, fun t => ?_⟩
    · have h1 := hE s
      rw [h] at h1
      exact (b₁ (E s')).unique h1 (hE s')
    · obtain ⟨s, hs, -⟩ := b₁ t
      exact ⟨s, (b₂ s).unique (hE s) hs⟩
  · intro s s' s'' h j
    have hT := hlin F N w₀ (E s) (E s') (SecOps.secAdd (E s) (E s')) s s' 1 (hE s) (hE s') (fun j => by
      simp [SecOps.secAdd, liftFun])
    have e : (1 : F) • s + s' = s'' := fam_ext fun α j => by rw [h]; simp
    rw [e] at hT
    exact congrArg (fun t : GlobalTheory.UT.SecA A F N => t.f j) ((b₂ s'').unique (hE s'') hT)
  · intro c s s' hs j
    obtain rfl := (isSmul_iff c s s').1 hs
    obtain ⟨z, hz, -⟩ := b₁ SecOps.secZero
    have hz0 : z = 0 := by
      have h2 := hlin F N w₀ _ _ SecOps.secZero z z 1 hz hz (fun j => by simp [SecOps.secZero])
      have h3 := (b₁ _).unique hz h2
      rw [one_smul] at h3
      exact left_eq_add.1 h3
    have hT := hlin F N w₀ (E s) SecOps.secZero
      (SecOps.secScale ((fst (TFK (R := R) F) A.A).left.appTop.hom (fnF F c)) (E s)) s z c (hE s) hz (fun j => by
        show _ = _ + 0
        rw [add_zero]
        rfl)
    rw [hz0, add_zero] at hT
    exact congrArg (fun t : GlobalTheory.UT.SecA A F N => t.f j) ((b₂ _).unique (hE _) hT)
  · intro x
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := hf.2.1 x hx
      exact ⟨p, (hlabf p).trans hp⟩
    · rintro ⟨p, rfl⟩
      rw [hlabf]
      exact hfN p
  · intro p
    exact (hSF p).1.1
  · intro p
    exact ((hSF p).2 (lab p) (hlab p)).1
  · intro p w θ s s' hw hθ hrel
    obtain ⟨t', ht'⟩ := GlobalTheory.RootShift.exists_isActOf A.isLB θ (E s)
    obtain ⟨s'', hs'', -⟩ := b₁ t'
    have h1 := ((hSF p).2 (lab p) (hlab p)).2 θ hθ w₀ hw₀ w hw (E s) t' s s'' (hE s) hs'' ht'
    obtain rfl := GlobalTheory.ThetaTranslate.phiRel_unique gf p hw.1 hrel h1
    have e := (b₂ s').unique (hE s') hs''
    rw [← e] at ht'
    exact ht'

end GlobalTheory.Mum
