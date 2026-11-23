import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCoordPtLocal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCoordPtFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionIsoOfGroupPullbackGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCoordinatesScalarMulSubfieldValuedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVPointDefinedOverOfCoordsProportionalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep

theorem points_defOver : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ D.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (D.P.L.pull π₁) (M₀.pull π₀)), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' D.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ → w.IsGen → ∀ (a : D.X) (x : Sp K ⟶ B'.left), x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ev ≫ (D.c a).left → GlobalTheory.Poinc.Sep.DefOver k₀ (x ≫ π₀) := by
  intro g n hn hodd
  obtain ⟨j₁, hC⟩ := GlobalTheory.T.torsionCoordinates_scalar_mul_subfieldValued g n hn hodd
  refine ⟨max j₁ 1, ?_⟩
  intro j hj V₁ _ _ _ hCN hunit D hg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hrat B₀ _ _ M₀ B' _ π₁ π₀ w hB₀ hM₀ h₁ h₀ hw a x hx hxa
  have hj₁ : j₁ ≤ j := le_trans (le_max_left _ _) hj
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hmodd : Odd (n ^ j) := hodd.pow
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases Nat.lt_or_ge n 3 with h | h
    · have : n = 2 := by omega
      subst this; exact absurd hodd (by decide)
    · exact h
  have hm3 : 3 ≤ n ^ j := le_trans hn3 (by
    calc n = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ j := Nat.pow_le_pow_right hn.pos hj1)
  have hmK : ((n ^ j : ℕ) : K) ≠ 0 := by
    have h := (hunit (n ^ j) (by positivity)).map ev
    rw [map_natCast] at h
    exact h.ne_zero
  haveI : IsNoetherianRing V₁ := hCN.1
  haveI : IsCommMonObj D.P.A := D.P.isAb.comm
  haveI : IsCommMonObj B' := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback h₁
  let P' : PolAV (Sp K) := GlobalTheory.TorsionTauCompare.polOfPullback D.P B' h₁
  have hw' : LBIso P'.L (M₀.pull π₀) := ⟨w, hw⟩
  have hSym : Out.Sym B₀ M₀ := (GlobalTheory.PolDescent.rigidified_sym_kTriv_descend k₀ K k₀.subtype B₀ B' π₀ M₀ P'.L hB₀ h₀
    hM₀ P'.isLB hw').2.1 P'.sym
  have h₀' : IsGrpPullback P'.A B₀ (spMap (algebraMap k₀ K)) π₀ := h₀
  have : Flat (spMap k₀.subtype) := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  let P₀ : PolAV (Sp k₀) :=
    { A := B₀, isAb := hB₀, g := P'.g,
      smoothDim := GlobalTheory.CM.smoothOfRelativeDimension_of_fibre k₀ K k₀.subtype B₀ P'.A.left π₀ P'.A.hom P'.g hB₀ h₀.1
        P'.smoothDim,
      L := M₀, isLB := hM₀, rigid := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local M₀ hM₀ _ _, sym := hSym,
      ample := GlobalTheory.AmpleDescent.relAmple_of_faithfullyFlat k₀ K B₀ P'.A π₀ M₀ P'.L hB₀ h₀' hM₀ P'.isLB hw' P'.ample,
      ktriv := GlobalTheory.AmpleDescent.kTriv_of_pull h₀ hM₀ P'.isLB hw' P'.ktriv }
  obtain ⟨Φ₀, hΦ₀⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback (G := B₀) (G' := B') h₀
    (𝟙 (Sp K)) (spMap k₀.subtype) (Category.id_comp _)
  obtain ⟨Φ₁, hΦ₁⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback (G := D.P.A) (G' := B') h₁
    (𝟙 (Sp K)) (spMap ev) (Category.id_comp _)
  let t₀ : Sp K ⟶ Sp k₀ := spMap k₀.subtype
  let t₁ : Sp K ⟶ Sp V₁ := spMap ev
  let Ix := {y : Over.mk t₀ ⟶ B₀ // y ^ (n ^ j) ^ 2 = 1}
  let X' : Ix → (baseOver (Sp K) ⟶ B') := fun i => Φ₀.symm i.1
  have hX' : ∀ i, X' i ^ (n ^ j) ^ 2 = 1 := fun i => Φ₀.injective (by
    rw [map_pow, MulEquiv.apply_symm_apply, i.2, map_one])
  let z' : baseOver (Sp K) ⟶ B' := Over.homMk x hx
  let yD : Ix → (Over.mk t₁ ⟶ D.P.A) := fun i => Φ₁ (X' i)
  have hyD : ∀ i, yD i ^ (n ^ j) ^ 2 = 1 := fun i => by
    simp only [yD]; rw [← map_pow, hX' i, map_one]
  have hzD : (Φ₁ z').left = t₁ ≫ (D.c a).left := by
    rw [hΦ₁]; simp [t₁, z', hxa]
  obtain ⟨vD, l, r, hvD, hr, hvr⟩ := hC j hj₁ V₁ hCN hunit D hg X C e u mo hmo hT K ev k₀ hk₀ hrat
    Ix yD hyD a (Φ₁ z') hzD
  have HD := GlobalTheory.FullExtend.isCoordPt_move (f := spMap ev) (T := baseOver (Sp K)) (T₀ := Over.mk t₁) (𝟙 _)
    (P₀ := D.P) (P := P') (φ := π₁) h₁ (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB D.P.isLB π₁)) (B := Over.mk t₁)
    (𝟙 _) (𝟙 _) (by simp) (by simp [t₁])
    (fun th₀ h => GlobalTheory.ThetaCoord.isGenSec_pullS D.P.isLB (𝟙 _) (𝟙 _) (by simp) h) (x := X') (x₀ := yD)
    (fun i => (Category.id_comp _).trans (hΦ₁ _)) hX' (z := z') (z₀ := Φ₁ z') ((Category.id_comp _).trans (hΦ₁ z')) hvD
  obtain ⟨v₀, hv₀⟩ := (GlobalTheory.CoordSep.coord_exists_unique_separate GlobalTheory.abelianSchemeLaws_all.1 K (Sp k₀) P₀ t₀ (n ^ j)
    hmodd hmK Ix (fun i => i.1) (fun i => i.2)).1 (Φ₀ z')
  have H0 := GlobalTheory.FullExtend.isCoordPt_move (f := spMap k₀.subtype) (T := baseOver (Sp K)) (T₀ := Over.mk t₀) (𝟙 _)
    (P₀ := P₀) (P := P') (φ := π₀) h₀ hw' (B := Over.mk t₀) (𝟙 _) (𝟙 _) (by simp) (by simp [t₀])
    (fun th₀ h => GlobalTheory.ThetaCoord.isGenSec_pullS hM₀ (𝟙 _) (𝟙 _) (by simp) h) (x := X') (x₀ := fun i => i.1)
    (fun i => (Category.id_comp _).trans ((congrArg Over.Hom.left (Φ₀.apply_symm_apply i.1)).symm.trans (hΦ₀ _)))
    hX' (z := z') (z₀ := Φ₀ z') ((Category.id_comp _).trans (hΦ₀ z')) hv₀
  have HD' : GlobalTheory.Ex.IsCoordPt P' (n ^ j) X' z' (fun i => GlobalTheory.Ex.fnOf (vD i)) := by
    convert HD using 2 with i
    simp
  have H0' : GlobalTheory.Ex.IsCoordPt P' (n ^ j) X' z' (fun i => GlobalTheory.Ex.fnOf (v₀ i)) := by
    convert H0 using 2 with i
    simp
  obtain ⟨-, U₂, -, -⟩ := GlobalTheory.CoordSep.coord_exists_unique_separate GlobalTheory.abelianSchemeLaws_all.1 K (Sp K) P' (𝟙 _)
    (n ^ j) hmodd hmK Ix X' hX'
  obtain ⟨c, hc⟩ := (U₂ z' v₀ vD H0').1 HD'
  have hv₀r : ∀ i, v₀ i = ((c⁻¹ : Kˣ) * l) * r i := fun i => by
    have := congrFun hc i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [_root_.mul_assoc, ← hvr i, this, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  have hD := GlobalTheory.T.polAV_point_defined_over_of_coords_proportional K k₀ hk₀ P₀ (n ^ j) hmodd hm3 hmK (Φ₀ z') v₀ _ r hv₀ hr hv₀r
  rwa [hΦ₀] at hD

end GlobalTheory.USep
