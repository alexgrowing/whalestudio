import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.LocStep
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.ThmA
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.DerivPos
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.BernOf
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.HighestDerivativeProducts.HighestDerivProd

namespace PositivityTheory.RgUd

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]

theorem thmB_char0 : ThmB k := AB.Final.thmB k (AB.Final.thmA k (T.Final.thmT k))

theorem bern : BernAt k :=
  Prod.Final.bern_of k (Form.U.Final.derivTop k (thmB_char0 k)) (Form.U.Final.derivPos k (thmB_char0 k))
    (GlobalTheory.RgGu.Leib.Hand.leibnizOrd k)

end PositivityTheory.RgUd
