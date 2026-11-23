import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisationsAgreeAtLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GmSqPullG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareIsoCarriesSquareCubicalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareIsoRespectsSymmetryPointwiseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareComparisonTorusInvariantStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

open SqLevel in
set_option maxHeartbeats 400000 in

theorem polarisation_squares_agree_at_level : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      eSec G (r z) ∈ U.LG.L.U jL → eSec G (r z) ∈ U'.LG.L.U jL' →
      gm r z _ (U.LG.rig.s (fun _ => jL)) ^ 2 =
        gv wL (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z _ (U'.LG.rig.s (fun _ => jL')) ^ 2) →
    ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom →
    (U'.gt e).q ≫ β.hom = (U.gt e).q →
    ∃ v : LB.Iso ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
        (fstG I e D'.toPre.P.A).left)
      ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
        (β.hom.left ≫ (fstG I e D.toPre.P.A).left)), v.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
      (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
      gw v (r ≫ (U'.gt e).q.left) z (fun _ => jM) (fun _ => fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 =
        gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG I e G).left) z (fun _ => jL) (fun _ => jL') := by
  intro hG R _ _ _ I hI D D' A A' G _ _ hS U U' wL hwL hrig e β hβ hq
  have hM := DVR.linComb_isLB D.toPre.P.L D.toPre.P.isLB (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)
  have hM' := DVR.linComb_isLB D'.toPre.P.L D'.toPre.P.isLB (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)
  have hL := DVR.linComb_isLB U.LG.L U.LG.isLB (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)
  have hL' := DVR.linComb_isLB U'.LG.L U'.LG.isLB (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)
  have hwL' : (isoPullId wL (rfl : 𝟙 G.left = 𝟙 G.left)).IsGen := (isGen_iff _).2 (isoPullId_pgen hwL rfl)
  obtain ⟨u, hu, hu'⟩ := LevelComparison.exists_comparison hM hM' hL hL' (sqIso_isGen (U.w_gen e))
    (sqIso_isGen (U'.w_gen e)) hwL'
  have sqrel : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι)
      (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
      gw u r z (fun _ => jM) (fun _ _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 =
        gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG I e G).left) z (fun _ => jL) (fun _ => jL') := by
    intro Z r z jM jM' jL jL' a₁ a₂ a₃ a₄
    have h := hu' Z r z (fun _ => jM) (fun _ => jM') (fun _ => jL) (fun _ => jL') (mem_sq.2 a₁) (mem_sq.2 a₂)
      (mem_sq.2 a₃) (mem_sq.2 a₄)
    rw [gw_sqIso (U'.w e) r z (fun _ => jM') (fun _ _ => jL') a₂ a₄,
      gw_sqIso (U.w e) r z (fun _ => jM) (fun _ _ => jL) a₁ a₃,
      gw_isoPullId wL rfl _ z (fun _ => jL) (fun _ => jL') (mem_sq.2 a₃) (mem_sq.2 a₄)] at h
    exact h
  have inv := GlobalTheory.T.square_comparison_torus_invariant hG R I hI D D' A A' G hS U U' wL hwL (GlobalTheory.T.square_iso_carries_square_cubical hG R I hI D D' A A' G hS U U' wL hwL)
    (GlobalTheory.T.square_iso_respects_symmetry_pointwise hG R I hI D D' A A' G hS U U' wL hwL) e β hβ hq u hu sqrel
  haveI := (U'.gt e).q_flat
  haveI := (U'.gt e).q_surj
  haveI := (U'.gt e).q_affine
  haveI := (U.gt e).q_hom
  have hql : (U'.gt e).q.left ≫ β.hom.left = (U.gt e).q.left := congrArg (·.left) hq
  obtain ⟨v, hv, hv'⟩ := LevelComparison.exists_iso_descend (U'.gt e).q.left (fstG I e D'.toPre.P.A).left
    (β.hom.left ≫ (fstG I e D.toPre.P.A).left) (p := (U.gt e).pG.left) (p' := (U'.gt e).pG.left)
    (by rw [← Category.assoc, hql]; rfl) rfl u hu (fun Z g₁ g₂ z j j' h a b => by
      obtain ⟨a₀, rfl⟩ : ∃ a₀, j = fun _ => a₀ := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim k 0)⟩
      obtain ⟨b₀, rfl⟩ : ∃ b₀, j' = fun _ => b₀ := ⟨j' 0, funext fun k => congrArg j' (Subsingleton.elim k 0)⟩
      let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (g₂ ≫ (thickObj R I e G).hom)
      let k₂ : Z' ⟶ thickObj R I e G := Over.homMk g₂ rfl
      let k₁ : Z' ⟶ thickObj R I e G := Over.homMk g₁ (by
        change g₁ ≫ (thickObj R I e G).hom = g₂ ≫ (thickObj R I e G).hom
        rw [← Over.w (U'.gt e).q, reassoc_of% h])
      have e₁ : k₁ ≫ (U'.gt e).q = k₂ ≫ (U'.gt e).q := Over.OverMorphism.ext h
      have e' : k₁ ≫ (U.gt e).q = k₂ ≫ (U.gt e).q := by rw [← hq, reassoc_of% e₁]
      have w : (k₁ * k₂⁻¹) ≫ (U.gt e).q = toUnit Z' ≫ η[thickObj R I e D.toPre.P.A] := by
        rw [MonObj.mul_comp, GrpObj.inv_comp, e', mul_inv_cancel]
        rfl
      have ht : ((U.gt e).isKernel.lift _ _ w ≫ (U.gt e).i) * k₂ = k₁ := by
        rw [(U.gt e).isKernel.lift_fst, inv_mul_cancel_right]
      have := inv Z' ((U.gt e).isKernel.lift _ _ w) k₂ z a₀ b₀ (mem_sq.1 a) (mem_sq.1 b)
      rw [ht] at this
      exact this)
  refine ⟨v, hv, fun Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  rw [hv' Z r z (fun _ => jM) (fun _ => jM') (mem_sq.2 a₁) (mem_sq.2 a₂)]
  exact sqrel Z r z jM jM' jL jL' a₁ a₂ a₃ a₄

end GlobalTheory
