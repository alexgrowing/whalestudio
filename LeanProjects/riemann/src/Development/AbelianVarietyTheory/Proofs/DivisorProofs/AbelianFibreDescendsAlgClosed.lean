import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsAffineOpenPreimageBasicOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescentSmoothDimension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFieldExtensionBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationSpreadFromGenericFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetricSpreadOutLineBundleAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsKernelPolarisationTrivialSpreadLocalisatio
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAlgHomOfFiniteTypeOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.BdDim.PolDescent

set_option backward.isDefEq.respectTransparency false

theorem exists_fg_lb {k₀ k : Type} [CommRing k₀] [CommRing k] [Algebra k₀ k] {X X₀ : Scheme.{0}} {f : X ⟶ Sp k}
    {f₀ : X₀ ⟶ Sp k₀} {π : X ⟶ X₀} [QuasiCompact f₀] [QuasiSeparated f₀]
    (H : IsPullback π f f₀ (spMap (algebraMap k₀ k))) {L : LB X} (hL : L.IsLB) :
    ∃ (s : Finset k) (M : LB (pullback f₀ (spMap (algebraMap k₀ (Algebra.adjoin k₀ (s : Set k))))))
      (j : X ⟶ pullback f₀ (spMap (algebraMap k₀ (Algebra.adjoin k₀ (s : Set k))))),
      M.IsLB ∧ LBIso L (M.pull j) ∧ j ≫ pullback.fst _ _ = π ∧
        j ≫ pullback.snd _ _ = f ≫ spMap (Algebra.adjoin k₀ (s : Set k)).val.toRingHom := by
  classical
  let ρ : ∀ s : (Finset k)ᵒᵖ, X ⟶ (Spread.bcDiagram f₀ k).obj s := fun s =>
    H.isoPullback.hom ≫ (Spread.bcCone f₀ k).π.app s
  have w : ∀ {s t} (g : s ⟶ t), ρ s ≫ (Spread.bcDiagram f₀ k).map g = ρ t := fun g =>
    (Category.assoc _ _ _).trans (congrArg _ ((Spread.bcCone f₀ k).w g))
  have hc : IsLimit (schemeConeOfFamily _ ρ w) :=
    (Spread.isLimitBcCone f₀ k).ofIsoLimit (Cone.ext H.isoPullback fun _ => rfl).symm
  obtain ⟨s, M, hM, h, -⟩ := LBLimit.exists_lb_of_isLimit _ ρ w hc L hL
  refine ⟨s.unop, M, H.isoPullback.hom ≫ Spread.bcMap f₀ (Algebra.adjoin k₀ (s.unop : Set k)).val, hM, h, ?_, ?_⟩
  · rw [Category.assoc, Spread.bcMap_fst, IsPullback.isoPullback_hom_fst]
  · rw [Category.assoc, Spread.bcMap_snd, IsPullback.isoPullback_hom_snd_assoc]

theorem exists_point {k₀ R : Type} [Field k₀] [IsAlgClosed k₀] [CommRing R] [IsDomain R] [Algebra k₀ R]
    [Algebra.FiniteType k₀ R] {a : R} (ha : a ≠ 0) : ∃ g : R →ₐ[k₀] k₀, IsUnit (g a) := by
  have : Nontrivial (Localization.Away a) :=
    (IsLocalization.injective (Localization.Away a) (powers_le_nonZeroDivisors_of_noZeroDivisors ha)).nontrivial
  have : Algebra.FiniteType k₀ (Localization.Away a) :=
    Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  obtain ⟨χ⟩ := exists_algHom_of_finiteType_of_isAlgClosed k₀ (Localization.Away a) k₀
  exact ⟨χ.comp (IsScalarTower.toAlgHom k₀ R _), (IsLocalization.Away.algebraMap_isUnit a).map χ⟩

theorem exists_pol_of_family {k₀ R k : Type} [Field k₀] [IsAlgClosed k₀] [CommRing R] [IsDomain R] [Algebra k₀ R]
    [Algebra.FiniteType k₀ R] [Field k] (v : R →+* k) (hv : Function.Injective v) {B : Over (Sp k₀)} [GrpObj B]
    (hB : IsAbelianScheme B) {G : Over (Sp R)} [GrpObj G] {p : G.left ⟶ B.left}
    (hG : IsGrpPullback G B (spMap (algebraMap k₀ R)) p) {M : LB G.left} (hM : M.IsLB)
    {A : Over (Sp k)} [GrpObj A] {j : A.left ⟶ G.left} (hA : IsGrpPullback A G (spMap v) j) {L : LB A.left}
    (hL : L.IsLB) (e : LBIso L (M.pull j)) (hr : Out.Rigidified A L) (hs : Out.Sym A L) (ha : Out.RelAmple A L)
    (hk : Out.KTriv A L) :
    ∃ L₀ : LB B.left, L₀.IsLB ∧ Out.Rigidified B L₀ ∧ Out.Sym B L₀ ∧ Out.RelAmple B L₀ ∧ Out.KTriv B L₀ := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k₀ R
  have := hB.comm
  have hGab := PolPull.isAbelianScheme_of_isGrpPullback hB hG
  have := hGab.comm
  let K := FractionRing R
  let i : K →+* k := IsFractionRing.lift hv
  have ei : spMap i ≫ spMap (algebraMap R K) = spMap v := by
    rw [spMap_comp_ring]
    congr 1
    exact RingHom.ext fun x => IsFractionRing.lift_algebraMap hv x
  have q := isGrpPullback_pullback G (spMap (algebraMap R K))
  have hC := PolPull.isAbelianScheme_of_isGrpPullback hGab q
  have := hC.comm
  let u : A.left ⟶ ((Over.pullback (spMap (algebraMap R K))).obj G).left :=
    q.1.lift j (A.hom ≫ spMap i) (by rw [Category.assoc, ei, hA.1.w])
  have hu : u ≫ pullback.fst G.hom (spMap (algebraMap R K)) = j := q.1.lift_fst _ _ _
  have hu' : IsGrpPullback A ((Over.pullback (spMap (algebraMap R K))).obj G) (spMap i) u :=
    IsGrpPullback.cancel q (hA.congr ei.symm hu.symm) (q.1.lift_snd _ _ _)
  have hN := pull_isLB hM (pullback.fst G.hom (spMap (algebraMap R K)))
  have e' := LBIso.trans hL (pull_isLB hM _) (pull_isLB hN _) e (GenSpread.lbIso_pull_pull hM u hu.symm)
  obtain ⟨hr', hs', hk'⟩ := GlobalTheory.PolDescent.rigidified_sym_kTriv_descend K k i _ A u _ L hC hu' hN hL e'
  have ha' := AmpleDescent.relAmple_of_fieldExtension K k i _ A u _ L hC hu' hN hL e' ha
  have r := PolBaseChange.lbIso_refl hN
  have hP : AbLaw.IsProjBy G.hom := (ProjSpace.isProjBy_iff_isProjOver _).2
    (ProjSpace.isProjOver_of_isPullback_spMap _ hG.1
      ((ProjSpace.isProjBy_iff_isProjOver _).1 (AbelianProjective.isProjBy_of_isAbelianScheme k₀ B hB)))
  obtain ⟨a₁, h₁, H₁⟩ := GenSpread.exists_rigidified R K G _ _ M _ hGab q hM hN r (hr' hr)
  obtain ⟨a₂, h₂, H₂⟩ := GenSpread.exists_sym R K G _ _ M _ hGab q hM hN r (hs' hs)
  obtain ⟨a₃, h₃, H₃⟩ := AmpleSpread.relAmple_spread R K G M hGab.proper hM ha'
  obtain ⟨a₄, h₄, H₄⟩ := GenSpread.exists_kTriv globalFns_holds R K G _ _ M _ hGab q hM hN r hP (hk' hk)
  obtain ⟨g, hg⟩ := exists_point (k₀ := k₀) (mul_ne_zero (mul_ne_zero h₁ h₂) (mul_ne_zero h₃ h₄))
  simp only [map_mul, IsUnit.mul_iff] at hg
  have eg : spMap g.toRingHom ≫ spMap (algebraMap k₀ R) = 𝟙 _ := by
    rw [spMap_comp_ring, show g.toRingHom.comp (algebraMap k₀ R) = RingHom.id k₀ from
      RingHom.ext fun x => g.commutes x]
    exact Spec.map_id _
  have : IsMonHom (Iso.refl B).hom := inferInstanceAs (IsMonHom (𝟙 B))
  let π : B.left ⟶ G.left := hG.1.lift (𝟙 _) (B.hom ≫ spMap g.toRingHom) (by
    rw [Category.assoc, eg, Category.id_comp, Category.comp_id])
  have hπ : IsGrpPullback B G (spMap g.toRingHom) π :=
    IsGrpPullback.cancel hG ((isGrpPullback_of_iso (Iso.refl B)).congr eg.symm (hG.1.lift_fst _ _ _).symm)
      (hG.1.lift_snd _ _ _)
  have h₀ := pull_isLB hM π
  have r₀ := PolBaseChange.lbIso_refl h₀
  refine ⟨M.pull π, h₀, H₁ k₀ g.toRingHom hg.1.1 B π _ hπ h₀ r₀, H₂ k₀ g.toRingHom hg.1.2 B π _ hπ h₀ r₀, ?_,
    H₄ k₀ g.toRingHom hg.2.2 B π _ hπ h₀ r₀⟩
  obtain ⟨w, hw⟩ := GenSpread.lbIso_pull_pull hM hπ.1.isoPullback.hom hπ.1.isoPullback_hom_fst.symm
  refine relAmple_pull (f := 𝟙 _) (A := Over.mk (pullback.snd G.hom (spMap g.toRingHom)))
    (IsPullback.of_horiz_isIso ⟨?_⟩) (pull_isLB hM _) h₀ ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _)
    (fun _ => trivial) (H₃ k₀ g.toRingHom hg.2.1)
  exact hπ.1.isoPullback_hom_snd.trans (Category.comp_id _).symm

theorem exists_polAV_sameFibre : ∀ (k₀ k : Type) [Field k₀] [IsAlgClosed k₀] [Field k] [IsAlgClosed k] (ι : k₀ →+* k)
    (B : Over (Sp k₀)) [GrpObj B] (S : Scheme.{0}) (P : Out.PolAV S) (x : Sp k ⟶ S), IsAbelianScheme B →
    SameFibre P.A x B (spMap ι) → ∃ P₀ : Out.PolAV (Sp k₀), SameFibre P.A x P₀.A (spMap ι) := by
  intro k₀ k _ _ _ _ ι B _ S P x hB ⟨A, _, φ, ψ, hφ, hψ⟩
  letI := ι.toAlgebra
  have := hB.proper
  have hL := pull_isLB P.isLB φ
  obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl hL
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := x (IsLocalRing.closedPoint k)) trivial
  have ha := relAmple_pull hφ.1 P.isLB hL ((isGen_iff w).1 hw) U hU
    (fun y => (congrArg (fun V => y ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem x hc)).mpr trivial) P.ample
  have hk := kTriv_pull hφ P.isLB hL ((isGen_iff w).1 hw) P.ktriv
  obtain ⟨s, M, j, hM, e, hj₁, hj₂⟩ := exists_fg_lb (k₀ := k₀) hψ.1 hL
  have : Algebra.FiniteType k₀ (Algebra.adjoin k₀ (s : Set k)) :=
    (Subalgebra.fg_iff_finiteType _).1 ⟨s, rfl⟩
  have q := isGrpPullback_pullback B (spMap (algebraMap k₀ (Algebra.adjoin k₀ (s : Set k))))
  have es : spMap (Algebra.adjoin k₀ (s : Set k)).val.toRingHom ≫
      spMap (algebraMap k₀ (Algebra.adjoin k₀ (s : Set k))) = spMap ι := spMap_comp_ring _ _
  have hj := IsGrpPullback.cancel q (hψ.congr es.symm hj₁.symm) hj₂
  obtain ⟨L₀, h₀, h₁, h₂, h₃, h₄⟩ := exists_pol_of_family
    (Algebra.adjoin k₀ (s : Set k)).val.toRingHom Subtype.val_injective hB q hM hj hL e
    (PolBaseChange.rigidified_pull hφ P.rigid) (PolBaseChange.sym_pull hφ P.sym) ha hk
  have hd := (FieldDescentAb.isAbelianScheme_and_relDim_descend k₀ k ι B A ψ hψ
    (PolPull.isAbelianScheme_of_isGrpPullback hB hψ)).2 P.g
    ((smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback hφ.1 P.smoothDim)
  exact ⟨⟨B, hB, P.g, hd, L₀, h₀, h₁, h₂, h₃, h₄⟩, A, _, φ, ψ, hφ, hψ⟩

end GlobalTheory.BdDim.PolDescent

end
