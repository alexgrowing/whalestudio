import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

namespace KsCore

variable {D : D7} (T : Core D)

abbrev WK (j : ℕ) (κ : WeightFamilies.Wt D j) : Submodule T.Q.c.F (T.R j) := T.C j κ

def MK (j : ℕ) (κ : WeightFamilies.Wt D j) :=
  latOf (T.C j κ) (T.Vs j) (fun la => isVal_valSet la)

def bW (h : LawsCore T) (j : ℕ) (hj : InR D j) (κ : WeightFamilies.Wt D j) :
    Module.Basis (Fin (Module.finrank T.Q.c.F (WK T j κ))) T.Q.c.F (WK T j κ) :=
  haveI := h.fd j hj κ
  haveI : Module.Free T.Q.c.F (WK T j κ) := Module.Free.of_divisionRing _ _
  Module.finBasis T.Q.c.F (WK T j κ)

def coordL {ι : Type} (L : Type) [Field L] [Algebra T.Q.c.F L] {j : ℕ} {κ : WeightFamilies.Wt D j}
    (b : Module.Basis ι T.Q.c.F (WK T j κ)) : WK T j κ →ₗ[T.Q.c.F] (ι → L) :=
  (LinearMap.compLeft (Algebra.linearMap T.Q.c.F L) ι).comp (Finsupp.lcoeFun.comp b.repr.toLinearMap)

variable {G : Type} [Group G]

def KeepsCu (j : ℕ) (κ : WeightFamilies.Wt D j)
    (lev : G → ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)) : Prop :=
  ∀ g, ∀ f ∈ T.C j κ, actLev (Xo := T.Q.Xo j) T.Q.c lev g f ∈ T.C j κ

open Classical in

def rhoGeo (j : ℕ) (κ : WeightFamilies.Wt D j)
    (lev : G → ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)) :
    G →* Module.End T.Q.c.F (WK T j κ) :=
  if h : ActLev (Xo := T.Q.Xo j) T.Q.c lev ∧ KeepsCu T j κ lev then
    { toFun := fun g => (actLev (Xo := T.Q.Xo j) T.Q.c lev g).restrict (h.2 g)
      map_one' := by
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        exact actL_one _ _ _ h.1.total h.1.func h.1.one (cusp_le_sec _ _ _ _ _ f.2).1
      map_mul' := by
        intro g g'
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        exact actL_mul _ _ _ h.1.total h.1.func h.1.mul g g' (cusp_le_sec _ _ _ _ _ f.2).1 }
  else 1

set_option synthInstance.maxHeartbeats 400000 in

def actT (j : ℕ) (κ : WeightFamilies.Wt D j)
    (lev : G → ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))
    (χ : G →* (T.Q.c.F)ˣ) (g : G) : Module.End T.Q.c.F (WK T j κ) :=
  ((χ g)⁻¹ : (T.Q.c.F)ˣ).val • rhoGeo T j κ lev g

set_option synthInstance.maxHeartbeats 400000 in

def eOf [Fintype G] (j : ℕ) (κ : WeightFamilies.Wt D j)
    (lev : G → ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))
    (χ : G →* (T.Q.c.F)ˣ) (eg : G → T.Q.c.F) : Module.End T.Q.c.F (WK T j κ) :=
  ∑ g, eg g • actT T j κ lev χ g

abbrev nrm (j : ℕ) (κ : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : T.R j → ℝ := T.Ns j κ σ

end KsCore

end Formalism.L2.Pj
