import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelModuliIntegralNormalLocallyNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdThetaMapOnNormalCharZeroAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsFieldDetermineDescend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreExistsGeneratorStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueProjectiveSpaceMapsOfAgreeGeometricPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolFibOfPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenRingIsDomainNoetherianIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SFamCharZeroAffineOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegTh

theorem exists_thMap_of_affine_cover : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen →
    ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (q : X ⟶ S), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * g) →
    IsReduced X → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), PolFib G L g (x ≫ q)) →
    (∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsDomain Γ(X, U) ∧ IsNoetherianRing Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U) ∧ CharZero Γ(X, U)) →
    ∃ f : X ⟶ PSpace o n, f ≫ PSpace.str o n = s ∧ ThMap G L ρ m q f := by
  intro S G _ _ L ρ hL hρ g m n o _ X s q hmo hm3 hmu hn hred hP hA
  have hloc : ∀ x : X, ∃ (W : X.Opens) (h : W.toScheme ⟶ PSpace o n), x ∈ W ∧ h ≫ PSpace.str o n = W.ι ≫ s ∧
      ThMap G L ρ m (W.ι ≫ q) h := by
    intro x
    obtain ⟨U, hxU, h1, h2, h3, h4⟩ := hA x
    exact GlobalTheory.T.exists_nhd_thetaMap_on_normal_charZero_affine S G L ρ hL hρ g m n o X s q hmo hm3 hmu hn hP U h1 h2 h3 h4 x hxU
  choose W h hxW hs hT using hloc
  have hag : ∀ i j (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ (W i).toScheme) (y' : Sp K ⟶ (W j).toScheme),
      y ≫ (W i).ι = y' ≫ (W j).ι → y ≫ h i = y' ≫ h j := by
    intro i j K _ _ y y' e
    have hPK := hP K (y ≫ (W i).ι)
    obtain ⟨⟨θ, hθ⟩, -⟩ := gen_of_polFib S G L hL g K _ hPK
    have hmK : (m : K) ≠ 0 := by
      have := hmu.map (Spec.preimage (y ≫ (W i).ι ≫ s)).hom
      rw [map_natCast] at this
      exact this.ne_zero
    obtain ⟨pt, c, hc⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed S G L ρ hL hρ g m (n + 1) K _ θ hmo hmK hn hPK
    have hH : HasTh G L ρ m ((y ≫ (W i).ι) ≫ q) c := ⟨θ, pt, hθ, hc⟩
    have h1 := hT i K y c (by rw [Category.assoc] at hH; exact hH)
    have h2 := hT j K y' c (by rw [e, Category.assoc] at hH; exact hH)
    refine CrdUniq.eq_of_pCrd ?_ h1 h2
    rw [Category.assoc, Category.assoc, hs, hs, ← Category.assoc, e, Category.assoc]
  have hcov : (⨆ x, W x) = ⊤ :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩
  obtain ⟨f, hf, hfi⟩ := GlobalTheory.ThetaGlue.glue_geom o n X s X W h hcov hs hag
  refine ⟨f, hf, fun K _ x c hH => ?_⟩
  let z : X := x.base (IsLocalRing.closedPoint K)
  have hr : Set.range x.base ⊆ Set.range (W z).ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim p (IsLocalRing.closedPoint K)]
    exact hxW z
  let x' : Sp K ⟶ (W z).toScheme := IsOpenImmersion.lift (W z).ι x hr
  have hx : x' ≫ (W z).ι = x := IsOpenImmersion.lift_fac _ _ _
  have h1 := hT z K x' c (by rw [← Category.assoc, hx]; exact hH)
  rw [← hx, Category.assoc, hfi]
  exact h1

theorem exists_thAt : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ), P.g = 8 * g → GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) → rig.IsGen → Odd m → 3 ≤ m → IsUnit (m : cycAway n) → ∃ (N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f := by
  intro g n hg hn hno F W hW P rig m hPg hSh hrig hmo hm3 hmu
  obtain ⟨hI, hN, hLN⟩ := GlobalTheory.T.siegelModuli_integral_normal_locallyNoetherian g n hg hn hno F
  letI := P.isAb.comm
  have hpos : 0 < m ^ (4 * (8 * g)) := pow_pos (by omega) _
  have hA : ∀ x : F.X, ∃ U : F.X.affineOpens, x ∈ (U : F.X.Opens) ∧ IsDomain Γ(F.X, U) ∧ IsNoetherianRing Γ(F.X, U) ∧
      IsIntegrallyClosed Γ(F.X, U) ∧ CharZero Γ(F.X, U) := fun x => by
    obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp F.X.isBasis_affineOpens)
      (show x ∈ (⊤ : F.X.Opens) from trivial)
    have hne : (U : F.X.Opens) ≠ ⊥ := fun h => by simp [h] at hxU
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.affineOpen_ring_isDomain_noetherian_integrallyClosed F.X hI hN hLN ⟨U, hU⟩ hne
    exact ⟨⟨U, hU⟩, hxU, h1, h2, h3, GlobalTheory.SiegelTor.sFam_charZero_affineOpen g n F ⟨U, hU⟩ inferInstance⟩
  obtain ⟨f, hf, hT⟩ := exists_thMap_of_affine_cover F.X P.A P.L rig P.isLB hrig P.g m (m ^ (4 * (8 * g)) - 1) (cycAway n) F.X F.s (𝟙 F.X)
    hmo hm3 hmu (by rw [hPg]; omega) inferInstance (fun R _ x => by simpa using GlobalTheory.UMin.FibExist.polFib_of_point F.X P R x) hA
  exact ⟨_, f, hPg, hSh, hrig, hmo, hm3, hmu, by omega, hf, hT, hW⟩

end GlobalTheory.SiegTh

end
