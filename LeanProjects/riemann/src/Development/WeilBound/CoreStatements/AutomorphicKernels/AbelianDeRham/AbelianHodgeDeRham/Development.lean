import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace MainStatements.Hodge.Free

structure Chapters : Prop where
  dict : DictSt
  cx : CxSt
  low : DictSt → LowSt
  htpy : CxSt → HtpySt
  qcalc : CxSt → QCalcSt
  fubini : CxSt → FubiniSt
  affacyc : CxSt → HtpySt → AffAcycSt
  descent : CxSt → HtpySt → QCalcSt → FubiniSt → AffAcycSt → DescentSt
  sysbc : DescentSt → LowSt → SysBCSt
  stein : SteinSt
  cot : CotSt
  par : CotSt → SteinSt → ParSt
  axo : DescentSt → LowSt → SysBCSt → SteinSt → AxOSt
  axform : CotSt → SteinSt → ParSt → AxFormSt
  cmp : CxSt → CmpSt
  fincoh : CmpSt → FinCohSt
  van : CxSt → CmpSt → VanSt
  perfnoeth : CxSt → DictSt → PerfNoethSt
  perfbase : PerfBaseSt
  perfh1 : PerfectH1BaseChange
  perfh2 : PerfectH2FromFibres
  wedgeof : LowSt → WedgeOfSt
  hopffield : CxSt → DictSt → LowSt → HopfFieldSt
  oneform : OneFormCohSt
  twoform : TwoFormCohSt
  closed : TwoFormCohSt → ClosedSt
  lift : OneFormCohSt → TwoFormCohSt → LiftSt
  alt : OneFormCohSt → TwoFormCohSt → AltSt
  hyp2 : OneFormCohSt → TwoFormCohSt → H2FieldHypothesis
  hopf : HtpySt → QCalcSt → FubiniSt → AffAcycSt → DescentSt → LowSt → AxOSt → HopfSt
  bi : DescentSt → LowSt → SteinSt → ParSt → AxOSt → AxFormSt → BiSt
  formbc : SteinSt → ParSt → FormBCSt
  oside : DescentSt → LowSt → SysBCSt → PerfSt → SteinSt → H1StructureBundle → WedgeFieldSt → HopfSt → PerfectH1BaseChange → PerfectH2FromFibres → WedgeOfSt → OBCSt ∧ WedgeSt
  perf : GlobalTheory.SpreadingModels.SchemeModels → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) → DescentSt → LowSt → SysBCSt → FinCohSt → PerfNoethSt → PerfBaseSt → PerfSt
  hopfle : CxSt → DictSt → LowSt → HopfLeSt
  h1le : DescentSt → LowSt → SteinSt → VanSt → HopfSt → HopfLeSt → PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe
  wedgefield2 : DescentSt → LowSt → SteinSt → H1StructureFieldDim → VanSt → HopfSt → HopfFieldSt → WedgeFieldSt
  noprim : DescentSt → LowSt → SteinSt → AxOSt → WedgeFieldSt → NoPrimSt
  smalllift : DescentSt → LowSt → SysBCSt → AxOSt → NoPrimSt → SmallLiftSt
  perfvb : PerfVBSt
  h1all : DescentSt → LowSt → SysBCSt → PerfSt → SteinSt → H1StructureFieldDim → SmallLiftSt → PerfVBSt → H1StructureBundle
  flatbc : DescentSt → LowSt → SysBCSt → FlatBCSt
  feweqn : FewEqSt
  stalkdim : StalkDimSt
  h1ge : PositivityTheory.ObstructionTrivialLocus.TrivLocus → PositivityTheory.ObstructionTrivialLocus.KFinite → FlatBCSt → FewEqSt → StalkDimSt → H1DimGeAbelianDim
  h1field : FlatBCSt → PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe → H1DimGeAbelianDim → H1StructureFieldDim
  final : SteinSt → ParSt → H1StructureBundle → DegenSt → WedgeHypSt → OBCSt → FormBCSt → GlobalTheory.Published.AbelianHodgeDeRham

theorem wedge_alt {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R} (h : Wedge F)
    (c : H1 F) : cup F c c = 0 := by
  obtain ⟨e, he⟩ := h
  rw [← he, (exteriorPower.ιMulti R 2).map_eq_zero_of_eq ![c, c] (i := 0) (j := 1) rfl (by decide), map_zero]

theorem Chapters.print (h : Chapters) (h₁ : GlobalTheory.SpreadingModels.SchemeModels)
    (h₂ : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f)) (h₃ : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f))
    (ht : PositivityTheory.ObstructionTrivialLocus.TrivLocus) (hk : PositivityTheory.ObstructionTrivialLocus.KFinite) : GlobalTheory.Published.AbelianHodgeDeRham := by
  have low := h.low h.dict
  have htpy := h.htpy h.cx
  have qc := h.qcalc h.cx
  have fub := h.fubini h.cx
  have aff := h.affacyc h.cx htpy
  have des := h.descent h.cx htpy qc fub aff
  have sbc := h.sysbc des low
  have par := h.par h.cot h.stein
  have axo := h.axo des low sbc h.stein
  have axf := h.axform h.cot h.stein par
  have cmp := h.cmp h.cx
  have hopf := h.hopf htpy qc fub aff des low axo
  have perf := h.perf h₁ h₂ h₃ des low sbc (h.fincoh cmp) (h.perfnoeth h.cx h.dict) h.perfbase
  have van := h.van h.cx cmp
  have fbc := h.flatbc des low sbc
  have h1f := h.h1field fbc (h.h1le des low h.stein van hopf (h.hopfle h.cx h.dict low))
    (h.h1ge ht hk fbc h.feweqn h.stalkdim)
  have wf := h.wedgefield2 des low h.stein h1f van hopf (h.hopffield h.cx h.dict low)
  have h1 := h.h1all des low sbc perf h.stein h1f
    (h.smalllift des low sbc axo (h.noprim des low h.stein axo wf)) h.perfvb
  obtain ⟨obc, w⟩ := h.oside des low sbc perf h.stein h1 wf hopf h.perfh1 h.perfh2 (h.wedgeof low)
  have bi := h.bi des low h.stein par axo axf
  have fr : AllAb fun _ _ A _ _ ↦ Framed (OAff A.hom) := fun R _ A _ g hA hg ↦
    ⟨h.stein R A g hA hg, (par R A g hA hg).1, (par R A g hA hg).2.1, (par R A g hA hg).2.2.1⟩
  have deg : DegenSt := fun R _ A _ g hA hg ↦
    have c := h.closed h.twoform R _ _ (fr R A g hA hg) (bi R A g hA hg)
    ⟨c, h.lift h.oneform h.twoform R _ _ (fr R A g hA hg) (bi R A g hA hg) c⟩
  have wh : WedgeHypSt := fun R _ A _ g hA hg ↦
    h.hyp2 h.oneform h.twoform R _ _ (fr R A g hA hg) (h1 R A g hA hg).1 (h1 R A g hA hg).2.1 (deg R A g hA hg).1
      (deg R A g hA hg).2 (w R A g hA hg)
      (h.alt h.oneform h.twoform R _ _ (fr R A g hA hg) (bi R A g hA hg) (deg R A g hA hg).1 (deg R A g hA hg).2
        (wedge_alt (w R A g hA hg)))
  exact h.final h.stein par h1 deg wh obc (h.formbc h.stein par)

theorem Chapters.h1Le (h : Chapters) : PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe := by
  have low := h.low h.dict
  have htpy := h.htpy h.cx
  have qc := h.qcalc h.cx
  have fub := h.fubini h.cx
  have aff := h.affacyc h.cx htpy
  have des := h.descent h.cx htpy qc fub aff
  have axo := h.axo des low (h.sysbc des low) h.stein
  exact h.h1le des low h.stein (h.van h.cx (h.cmp h.cx)) (h.hopf htpy qc fub aff des low axo)
    (h.hopfle h.cx h.dict low)

end MainStatements.Hodge.Free
