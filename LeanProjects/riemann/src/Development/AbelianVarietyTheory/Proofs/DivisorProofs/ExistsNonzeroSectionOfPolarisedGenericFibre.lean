import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecUnitClosedFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN

namespace GlobalTheory.ThetaDomain

theorem exists_sec_ne_zero_of_polAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) →
    ∃ (σ : LB.Sec t.PP.L) (k : t.PP.L.ι), σ.f k ≠ 0 := by
  intro E _ _ _ H R _ _ _ t hp
  obtain ⟨h₁, h₂, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨A, -, gen, -, hL, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt h₁ h₂ E H R t hp
  obtain ⟨O, hO, θ, hθ, -, nz⟩ := PushInv.pushInvertible_any h₂.secBaseChangeAny h₁.globalSectionsRank _ A
    (IsLocalRing.closedPoint (FractionRing R))
  obtain ⟨g, i, -, hi⟩ := nz _ hO
  obtain ⟨w, hw⟩ := LBIso.symm hL
  obtain ⟨s, hs⟩ := GlobalTheory.ThetaLocal.exists_sec_pull A.isLB (pull_isLB t.PP.isLB (pullback.fst t.G.hom (jK R)))
    gen.hom.left w hw (O := A.A.hom ⁻¹ᵁ O) (fun z _ => by
      change A.A.hom (gen.hom.left z) ∈ O
      rwa [Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) (A.A.hom (gen.hom.left z))
        (IsLocalRing.closedPoint (FractionRing R))]) θ hθ
  have eg : gen.hom.left (gen.inv.left g) = g := congrArg (fun q : A.A ⟶ A.A => q.left g) gen.inv_hom_id
  obtain ⟨k, hk⟩ := hs (gen.inv.left g) i (by rw [eg]; exact hi)
  have hsk : s.f k ≠ 0 := fun e => by
    rw [e, Scheme.basicOpen_zero] at hk
    exact hk
  have := t.semi.separated
  have := t.semi.quasiCompact
  have : CompactSpace t.G.left := QuasiCompact.compactSpace_of_compactSpace t.G.hom
  have : QuasiSeparatedSpace t.G.left := quasiSeparatedSpace_of_quasiSeparated t.G.hom
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R (FractionRing R) (algebraMap R _)
    (RingHom.flat_algebraMap_iff.2 inferInstance) t.G.left t.G.hom _ _ _
    (IsPullback.of_hasPullback t.G.hom (jK R)) t.PP.L t.PP.isLB s
  by_contra hcon
  push Not at hcon
  refine hsk (fn_ext fun z hz => ?_)
  have hz' : pullback.fst t.G.hom (jK R) z ∈ t.PP.L.U (k PUnit.unit) := Set.mem_iInter.1 hz PUnit.unit
  rw [LBGerm.gs_zero _ z _ hz]
  refine (hu z (k PUnit.unit) hz').trans (Finset.sum_eq_zero fun i _ => ?_)
  rw [hcon, LBGerm.gs_zero _ z _ hz', mul_zero]

end GlobalTheory.ThetaDomain
