import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueAndLinearInSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveChartCoordinateRatioMemModelRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdNoetherianIntegrallyClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionSpecRingOnAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendRegularThetaSectionAnyFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSectionOfOpenImmersionSpecStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ThBdl

theorem exists_locSec_of_openImmersion (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S)
    (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (χ : Sp R ⟶ S) [IsOpenImmersion χ] (ξ : Sp K ⟶ S)
    (e : spMap (algebraMap R K) ≫ χ = ξ) (θ : SecAt t.G t.PP.L ξ) (pt : Fin N → (Over.mk ξ ⟶ t.G)) (c : Fin N → R)
    (hodd : Odd m) (hm3 : 3 ≤ m) (hm : IsUnit (m : R)) (hpol : PolFib t.G t.PP.L g ξ)
    (hth : ThList t.G t.PP.L t.PP.rig m ξ θ pt (fun a => algebraMap R K (c a))) (hu : ∃ a, IsUnit (c a)) :
    ∃ s : LocSec t.G t.PP.L χ.opensRange, IsLocSec s ∧ GenIs ξ s (SecM.ofSec t.G θ) ∧ FibNz s χ.opensRange := by
  subst e
  have hlft : LocallyOfFiniteType t.G.hom := by
    haveI := t.semi.smooth
    infer_instance
  obtain ⟨σ, hσ, hσnz⟩ := GlobalTheory.T.extend_regularThetaSection_any_fractionField E H S t g m N R K χ θ pt c hodd hm3 hm hpol hth hu
  obtain ⟨s, hs, hsgen, hsfib⟩ := GlobalTheory.T.exists_localSection_of_openImmersion_spec S t.G t.PP.L R χ σ hlft hσnz
  refine ⟨s, hs, ?_, hsfib⟩
  have := hsgen K (algebraMap R K)
  rw [hσ] at this
  exact this

theorem exists_locSec_theta_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k]
    [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ)
    (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (θ : SecAt t.G t.PP.L M.pt) (pt : Fin (n + 1) → (Over.mk M.pt ⟶ t.G)),
    Geo.Tor.IsNormalScheme M.Z → Odd m → 3 ≤ m → IsUnit (m : k) → PolFib t.G t.PP.L g M.pt →
    IsGenSec t.G t.PP.L _ θ → ThList t.G t.PP.L t.PP.rig m M.pt θ pt c → PCrd (M.pt ≫ h) c →
    ∀ (a : Fin (n + 1)) (z : M.Z), z ∈ h ⁻¹ᵁ chart k n a → ∃ N : M.Z.Opens, z ∈ N ∧ N ≤ h ⁻¹ᵁ chart k n a ∧
      ∃ s : LocSec t.G t.PP.L N, IsLocSec s ∧
        GenIs M.pt s ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • SecM.ofSec t.G θ) ∧ FibNz s N := by
  intro E _ _ _ H k Ω _ _ _ _ _ M t g m n c h θ pt hN hodd hm3 hmu hpol hgen hth hcrd a z hz
  obtain ⟨hca, hdiv⟩ := GlobalTheory.T.projective_chart_coordinate_ratio_mem_model_ring k Ω M n c h a z hcrd hz
  obtain ⟨W, hWa, hzW, hWV, hnoeth, hic⟩ := GlobalTheory.T.exists_affine_nbhd_noetherian_integrallyClosed k Ω M hN (h ⁻¹ᵁ chart k n a) z hz
  have hne : (W : Set M.Z).Nonempty := ⟨z, hzW⟩
  obtain ⟨χ, hoi, hrange, hgenpt⟩ := GlobalTheory.T.exists_openImmersion_spec_ringOn_affine k Ω M W hWa hne
  haveI := M.isFractionRing_ringOn hWa hne
  let c'' : Fin (n + 1) → M.ringOn W := fun b =>
    ⟨c b / c a, RatModel.mem_ringOn.2 fun z' hz' => hdiv z' (hWV hz') b⟩
  let θ' : SecAt t.G t.PP.L M.pt :=
    SecM.toSec t.G ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • SecM.ofSec t.G θ)
  have hmΩ : (m : Ω) ≠ 0 := by
    have := hmu.map (algebraMap k Ω)
    rw [map_natCast] at this
    exact this.ne_zero
  have hth' : ThList t.G t.PP.L t.PP.rig m M.pt θ' pt (fun b => algebraMap (M.ringOn W) Ω (c'' b)) := by
    refine ⟨hth.1, fun b => ?_, hth.2.2⟩
    have key := GlobalTheory.UMin.thG_smul_iff M.Z t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m Ω M.pt θ θ' (pt b)
      (c a)⁻¹ (c b) (c b / c a) hodd hmΩ hpol rfl (hth.2.1 b)
    exact key.2 (by rw [div_eq_inv_mul])
  have hmR : IsUnit (m : M.ringOn W) := by
    have := hmu.map (algebraMap k (M.ringOn W))
    rwa [map_natCast] at this
  have hunit : ∃ b, IsUnit (c'' b) := ⟨a, by
    have : c'' a = 1 := Subtype.ext (by simp [c'', div_self hca])
    rw [this]; exact isUnit_one⟩
  obtain ⟨s, hs, hsgen, hsfib⟩ := exists_locSec_of_openImmersion E H M.Z t g m (n + 1) (M.ringOn W) Ω χ M.pt hgenpt θ' pt c'' hodd hm3 hmR hpol hth' hunit
  exact ⟨χ.opensRange, by rw [hrange]; exact hzW, by rw [hrange]; exact hWV, s, hs, hsgen, hsfib⟩

end GlobalTheory.UMin.ThBdl
