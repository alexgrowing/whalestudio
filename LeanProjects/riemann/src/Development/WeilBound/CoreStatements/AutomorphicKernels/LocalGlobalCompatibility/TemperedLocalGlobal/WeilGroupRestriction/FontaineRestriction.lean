import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.WdRestrict
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.Pst

namespace PositivityTheory.Pf1.CLGD.K.FontaineRestriction

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]

theorem wdRes_eq {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
    (h : IsPlaceOver A w) (h' : IsPlaceOver A w') :
    PositivityTheory.Pf1.CLGD.DescRes.WD.res h h' = PositivityTheory.Pf1.CLGD.WdRestrict.WD.res h h' := rfl

theorem exists_resBridge {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) :
    ∃ (LL : FinExt l) (Bw' : LocBridge l E' Ω (Dec (F := E') A) ↥(OL LL)),
      Induces Bw' ∧ PositivityTheory.Pf1.CLGD.WdRestrict.IsResBridge Bw Bw' := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosure ℚ Ω := Formalism.BasicNotions.Examples₂.LB.isAlgClosureQ E' Ω
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hA : ∀ x, x ∈ A ↔ ‖Bw.j x‖ ≤ 1 := hj
  haveI := Formalism.BasicNotions.Examples₂.LB.KwF_fin (E := E') Bw.j
  refine ⟨Formalism.BasicNotions.Examples₂.LB.nclo (Formalism.BasicNotions.Examples₂.LB.KwF (E := E') Bw.j),
    Formalism.BasicNotions.Examples₂.LB.bridgeOf (E := E') hA _ (Formalism.BasicNotions.Examples₂.LB.mem_nclo _), hA, fun g => ?_⟩
  refine congrArg (fun τ => τ) (GlobalTheory.PlaceBridge.algEquiv_ext (GlobalTheory.PlaceBridge.denseRange_embedding Bw.j)
    fun x => ?_)
  exact (Formalism.BasicNotions.Examples₂.LB.eDec_comm hA g x).trans
    (Bw.e_comm (PositivityTheory.Pf1.CLGD.WdRestrict.resDec E A g) x).symm

end PositivityTheory.Pf1.CLGD.K.FontaineRestriction

namespace PositivityTheory.Pf1.CLGD.K

theorem fontaine_weil_deligne_restriction : K6 := by
  intro E Ω _ _ _ _ _ X l a _ ι r _ P AI _ A w h w' h' O _ _ _ Bw hj hp
  obtain ⟨LL, Bw', hj', hc⟩ := FontaineRestriction.exists_resBridge (E' := X.M) Bw hj
  have e1 : (r.comp (Dec (F := E) A).subtype).comp (PositivityTheory.Pf1.CLGD.WdRestrict.resDec E A) =
      (r.comp (PositivityTheory.Pf1.CLGD.DescRes.resG E (E' := X.M))).comp (Dec (F := X.M) A).subtype :=
    MonoidHom.ext fun _ => rfl
  obtain ⟨h1, h2⟩ := PositivityTheory.Pf1.CLGD.WdRestrict.wdAt_res P ι Bw Bw' h h' hj hj' hc _ hp
  rw [e1] at h1 h2
  exact ⟨↥(OL LL), inferInstance, inferInstance, inferInstance, Bw', hj', h1,
    h2.trans (congrFun (FontaineRestriction.wdRes_eq h h').symm _)⟩

end PositivityTheory.Pf1.CLGD.K
