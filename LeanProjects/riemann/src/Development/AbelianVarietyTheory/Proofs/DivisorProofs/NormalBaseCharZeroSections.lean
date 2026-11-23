import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndIsPrincipalPol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalPointClosedPointImage
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KernelTrivialOfEveryPointCovered
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder

namespace GlobalTheory.AbLocusPol

theorem exists_polAV : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → CharZero Γ(T, ⊤) → ∀ b : T ⟶ Z.X, (∀ w : T, b w ∈ abLocus Z.t.G) → ∃ (Q : Out.PolAV T) (θ : Q.A.left ⟶ Z.t.G.left), IsGrpPullback Q.A Z.t.G b θ ∧ LBIso (Z.t.PP.L.pull θ) Q.L := by
  intro E _ _ _ H Dw l Xo c Z T _ _ _ _ b hb
  have hg : Set.range b ⊆ abLocus Z.t.G := by
    rintro _ ⟨w, rfl⟩
    exact hb w
  obtain ⟨t, ⟨m⟩⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sab b Z.t
  choose V hx hV using GlobalTheory.VertVanish.exists_open Z hg m
  choose u n using fun x : T => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sab (V x).ι t
  have hU : iSup V = ⊤ := top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩
  have hloc := fun x : T => hV x _ _ (u x) (n x).some fun q => q.2
  have hp : IsProper t.G.hom := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) V hU fun x => ?_
    have h := (hloc x).1
    have e := (n x).some.cart.1.isoIsPullback_hom_snd _ _ (isPullback_morphismRestrict t.G.hom (V x)).flip
    rw [← e] at h
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).1 h
  have hG : IsAbelianScheme t.G := ⟨t.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  have hAb : ∀ x, IsAbelianScheme (u x).G := fun x =>
    ⟨(u x).comm, (u x).semi.smooth, (hloc x).1, (u x).semi.geomConnected⟩
  have hiso : ∀ x, LBIso (u x).PP.L (t.PP.L.pull (n x).some.φ) := fun x => by
    obtain ⟨w, hw, -⟩ := (n x).some.lin
    exact ⟨w, hw⟩
  have hA : Out.RelAmple t.G t.PP.L :=
    GlobalTheory.CoverGlue.relAmple_of_cover T T V t.G (fun x => (u x).G) (fun x => (n x).some.φ) hU
      (fun x => (n x).some.cart) t.PP.L (fun x => (u x).PP.L) t.PP.isLB (fun x => (u x).PP.isLB) hiso hG hAb
      (fun x => (hloc x).2.1)
  have hK : Out.KTriv t.G t.PP.L :=
    GlobalTheory.KTrivGlob.kTriv_of_forall_point GlobalTheory.firstFiveLaws.1 E H T t hp hA fun x =>
      ⟨_, (V x).ι, u x, (n x).some, ⟨⟨x, hx x⟩, rfl⟩, (hloc x).2.2⟩
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨x₀⟩ : Nonempty T := inferInstance
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (eSec t.G x₀)
  obtain ⟨-, ws, gs', -⟩ := t.sym
  obtain ⟨w, g, -⟩ := m.lin
  refine ⟨{ A := t.G, g := d, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB, ample := hA, ktriv := hK,
            isAb := hG, rigid := ⟨t.PP.rig, t.PP.rigGen⟩,
            sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }, m.φ, m.cart, ?_⟩
  have h : LBIso t.PP.L (Z.t.PP.L.pull m.φ) := ⟨w, g⟩
  exact h.symm

end GlobalTheory.AbLocusPol
