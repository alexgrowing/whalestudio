import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGenericFibreExtendsOverDvrStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetryHypothesisSpreadFromGenericFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumExt

theorem exists_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R], ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ L : LB ((Over.pullback (jK R)).obj G).left, L.IsLB → ∃ PP : LB (G2 G).left, ExtLam G L PP := by
  intro R _ _ _ G _ _ hG L hL
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI : GeometricallyIntegral G.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hG.smooth hG.geomConnected
  obtain ⟨L', hL', hb⟩ := GlobalTheory.T.lineBundle_generic_fibre_extends_over_dvr R G L hL
  refine ⟨abelian₂ G L', DVR.linComb_isLB _ hL' _ _, fun κ₂ hκ => ?_⟩
  have h := isGrpPullback_pullback G (jK R)
  let V := lift (pushPt h.1.w (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)))
    (pushPt h.1.w (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)))
  have hV : V.left = κ₂ := by
    apply pullback.hom_ext
    · show (V ≫ fst G G).left = κ₂ ≫ (fst G G).left
      rw [hκ.1, lift_fst]
      rfl
    · show (V ≫ snd G G).left = κ₂ ≫ (snd G G).left
      rw [hκ.2, lift_snd]
      rfl
  have c := GlobalTheory.SymSpread.lbIso_cube h hL' hL hb (x2 G) (x2 _) V (fun i => by fin_cases i <;> simp [x2, V])
  rw [hV] at c
  exact c

end GlobalTheory.MumExt
