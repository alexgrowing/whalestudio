import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalOfFreeHodgeBaseChangeRigid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystalOfDualAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedSquareZeroAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBidualityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamLocallyFreeHodgeDegeneratesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareDeRhamDualityAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilpotentDividedPowersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIsotropicLiftModIdealStatement

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AbDual

namespace GlobalTheory.BirigLift

theorem mem_smul_top_of_forall_mem {R : Type} [CommRing R] (I : Ideal R) {P : Type*} [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] (x : Module.Dual R P) (hx : ∀ c, x c ∈ I) :
    x ∈ I • (⊤ : Submodule R (Module.Dual R P)) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have e : x = ∑ i, x (f (Pi.single i 1)) • ((LinearMap.proj i : (Fin n → R) →ₗ[R] R) ∘ₗ s) := by
    ext c
    have hc : c = f (s c) := (LinearMap.congr_fun hs c).symm
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, smul_eq_mul]
    conv_lhs => rw [hc, pi_eq_sum_univ (s c), map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, map_smul, smul_eq_mul, mul_comm]
    congr 3
    ext j
    simp [Pi.single_apply, eq_comm]
  rw [e]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hx _) trivial

theorem apply_mem_of_mem_smul_top {R : Type} [CommRing R] (I : Ideal R) {P : Type*} [AddCommGroup P] [Module R P]
    {x : Module.Dual R P} (hx : x ∈ I • (⊤ : Submodule R (Module.Dual R P))) (c : P) : x c ∈ I := by
  refine Submodule.smul_induction_on (p := fun y : Module.Dual R P ↦ y c ∈ I) hx (fun r hr y _ ↦ ?_) fun y z hy hz ↦ ?_
  · rw [LinearMap.smul_apply, smul_eq_mul]; exact I.mul_mem_right _ hr
  · rw [LinearMap.add_apply]; exact I.add_mem hy hz

theorem exists_perfect_mod {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) {D H : Type*}
    [AddCommGroup D] [Module R D] [AddCommGroup H] [Module R₀ H] (red : D →ₛₗ[π] H)
    (φ : D →ₗ[R] D →ₗ[R] R) (ψ : H →ₗ[R₀] H →ₗ[R₀] R₀) (hπ : Function.Surjective π)
    (hψ : Function.Surjective ψ.flip) (hred : Function.Surjective red)
    (hker : ∀ x, red x = 0 → x ∈ (RingHom.ker π) • (⊤ : Submodule R D))
    (hrel : ∀ x y, ψ (red x) (red y) = π (φ x y)) (l : D →ₗ[R] R) :
    ∃ z, ∀ x, l x - φ x z ∈ RingHom.ker π := by
  have hl : ∀ x, x ∈ (RingHom.ker π) • (⊤ : Submodule R D) → π (l x) = 0 := by
    intro x hx
    refine Submodule.smul_induction_on (p := fun y : D ↦ π (l y) = 0) hx (fun r hr y _ ↦ ?_) fun y z hy hz ↦ ?_
    · rw [map_smul, smul_eq_mul, map_mul, RingHom.mem_ker.1 hr, zero_mul]
    · rw [map_add, map_add, hy, hz, add_zero]
  let s := Function.surjInv hred
  have hs : ∀ h, red (s h) = h := Function.surjInv_eq hred
  have key : ∀ x x', red x = red x' → π (l x) = π (l x') := fun x x' e ↦ by
    have := hl (x - x') (hker _ (by rw [map_sub, e, sub_self]))
    rwa [map_sub, map_sub, sub_eq_zero] at this
  let l₀ : H →ₗ[R₀] R₀ :=
    { toFun h := π (l (s h))
      map_add' a b := by
        rw [key (s (a + b)) (s a + s b) (by rw [map_add, hs, hs, hs]), map_add, map_add]
      map_smul' r h := by
        obtain ⟨r', rfl⟩ := hπ r
        rw [key (s (π r' • h)) (r' • s h) (by rw [map_smulₛₗ, hs, hs]), map_smul, smul_eq_mul, map_mul]
        rfl }
  obtain ⟨w, hw⟩ := hψ l₀
  obtain ⟨z, rfl⟩ := hred w
  refine ⟨z, fun x ↦ RingHom.mem_ker.2 ?_⟩
  have e := LinearMap.congr_fun hw (red x)
  rw [LinearMap.flip_apply, hrel] at e
  rw [map_sub, e, sub_eq_zero]
  exact key _ _ (hs _).symm

end GlobalTheory.BirigLift

namespace GlobalTheory.BirigLift

theorem lagr_univ {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) {D : Type*} [AddCommGroup D] [Module R D]
    [Module.Finite R D] [Module.Projective R D] (φ : D →ₗ[R] D →ₗ[R] R) (hI : I ^ 2 = ⊥) (h2 : IsUnit (2 : R))
    (anti : ∀ x y, φ x y = -φ y x) (perf : ∀ l : D →ₗ[R] R, ∃ z, ∀ x, l x - φ x z ∈ I) (F N : Submodule R D)
    (hFN : IsCompl F N) (iso : ∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) :
    ∃ E N' : Submodule R D, IsCompl E N' ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧
      E ⊔ I • (⊤ : Submodule R D) = F ⊔ I • (⊤ : Submodule R D) := by
  haveI : Module.Free R D := Module.free_of_flat_of_isLocalRing
  let ε := (Module.finBasis R D).equivFun
  let ψ : (Fin (Module.finrank R D) → R) →ₗ[R] (Fin (Module.finrank R D) → R) →ₗ[R] R :=
    φ.compl₁₂ ε.symm.toLinearMap ε.symm.toLinearMap
  have hψ : ∀ x y, ψ x y = φ (ε.symm x) (ε.symm y) := fun _ _ ↦ rfl
  obtain ⟨E, N', hEN, hE, hEF⟩ := GlobalTheory.T.maximal_isotropic_lift_mod_ideal R I _ ψ hI h2 (fun x y ↦ by simp only [hψ]; exact anti _ _)
    (fun l ↦ by
      obtain ⟨z, hz⟩ := perf (l ∘ₗ ε.toLinearMap)
      refine ⟨ε z, fun x ↦ ?_⟩
      have := hz (ε.symm x)
      simpa [hψ] using this)
    (F.map ε.toLinearMap) (N.map ε.toLinearMap) ((Submodule.orderIsoMapComap ε).isCompl hFN)
    (fun x hx y hy ↦ by
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      simpa [hψ] using iso a ha b hb)
  refine ⟨E.map ε.symm.toLinearMap, N'.map ε.symm.toLinearMap,
    (Submodule.orderIsoMapComap ε.symm).isCompl hEN, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simpa [hψ] using hE a ha b hb
  · have := congrArg (Submodule.map ε.symm.toLinearMap) hEF
    rw [Submodule.map_sup, Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range,
      ← Submodule.map_comp, LinearEquiv.symm_comp, Submodule.map_id] at this
    exact this

end GlobalTheory.BirigLift

namespace GlobalTheory.BirigLift

open GlobalTheory.Published.GrothendieckMessing in

theorem exists_lift_lam : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → IsUnit (2 : R) → ∀ P₀ : PolAV (Sp R₀), ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : P₀.A.left ⟶ A.left) (l : (P₀.A ⊗ P₀.A).left ⟶ (A ⊗ A).left) (Q : LB (A ⊗ A).left), IsAbelianScheme A ∧ IsGrpPullback P₀.A A (spMap π) i ∧ IsSquare i l ∧ Q.IsLB ∧ GlobalTheory.AbDual.IsAdditive Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ LBIso (Q.pull l) (abelian₂ P₀.A P₀.L) := by
  intro R R₀ _ _ _ _ _ π hπ hI2 h2 P₀
  have hI0 : RingHom.ker π ^ 2 = 0 := hI2
  let κ := divided₂ hI0
  have hκ : IsNilDP κ := isDPNilpotent_squareZero hI0
  have ADD : GlobalTheory.Published.DualAbelianScheme := GlobalTheory.T.dualAbelianScheme_exists_biduality
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.T.abelianScheme_firstDeRham_structure
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal_of_dualAbelianScheme ADD
  have GD : GlobalTheory.Published.GrothendieckDeformation := GlobalTheory.Published.grothendieckDeformation₂
    GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates ADD GlobalTheory.T.poincareDeRhamDuality_abelianScheme GlobalTheory.T.print_abelianLifting
  haveI := P₀.isAb.comm
  obtain ⟨A', _, i', h', hA'⟩ := GlobalTheory.T.abelianScheme_unobstructed_squareZero_affine R (RingHom.ker π) hI0 R₀ π hπ rfl P₀.A P₀.isAb
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim R A' hA'
  have C := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl hA' hg hA' hg h' h'
  have hΛ := isPerfect_lam P₀.isLB P₀.ktriv
  obtain ⟨φ₀, hφ₀⟩ := exists_isCorrForm C hΛ.isLB hΛ.zero_left hΛ.zero_right
  have anti := GlobalTheory.JetIsotropic.corrForm_antisymm C hΛ.isLB (GlobalTheory.FullSiegel.lam_symm P₀.isLB) hφ₀

  have HC := (GD R (RingHom.ker π) κ hκ R₀ π hπ rfl).1
  obtain ⟨bij, ⟨N0, hN0⟩, hAdm⟩ := HC g P₀.A A' i' h' hA' hg
  let e := LinearEquiv.ofBijective (crysToDR κ h') (HC.crysToDR_bijective h' hA' hg)
  have ee : ∀ xA, crysToDR κ h' (e.symm xA) = xA := e.apply_symm_apply
  letI : Algebra R R₀ := π.toAlgebra
  have hBC := (ADR.2.2.1 R A' g hA' hg R₀ P₀.A i' h').1
  obtain ⟨hfinA, hprojA, -⟩ := ADR.1.prim hA' hg
  haveI := hfinA
  haveI := hprojA
  haveI : Module.Finite R (Crys κ (spMap π) P₀.A) := Module.Finite.equiv e.symm
  haveI : Module.Projective R (Crys κ (spMap π) P₀.A) := Module.Projective.of_equiv e.symm

  let red : Crys κ (spMap π) P₀.A →ₛₗ[π] HdR P₀.A := hBC.bcMap.comp (crysToDR κ h')
  have hm : ∀ x, (crysRedMor κ rfl P₀.A).Corr x (red x) := fun x ↦
    (corr_crysToDR_iff rfl h' bij.2 x (red x)).1 (by exact hBC.corr_iff.2 rfl)
  have iso : LBIso ((abelian₂ P₀.A P₀.L).pull (Over.Hom.left (𝟙 (P₀.A ⊗ P₀.A)))) (abelian₂ P₀.A P₀.L) :=
    (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hΛ.isLB _) hΛ.isLB).1
      (by rw [GlobalTheory.CechPic.cls_pull hΛ.isLB, Over.id_left, GlobalTheory.CechPic.pull_id])
  obtain ⟨φ', hφ', e'⟩ := hφ₀.pull hΛ.isLB (crysRedMor κ rfl P₀.A) (crysRedMor κ rfl P₀.A)
    (h := Over.Hom.left (𝟙 (P₀.A ⊗ P₀.A))) (by simp) (by simp) hΛ.isLB iso
  obtain ⟨perf, filL, -⟩ := (GlobalTheory.Published.AbelianDualCrystal.duality ADR P₀.isAb P₀.smoothDim P₀.isAb P₀.smoothDim
    hΛ).2 φ' hφ'
  have hrel : ∀ x y, φ' (red x) (red y) = π (φ₀ x y) := fun x y ↦ e' x (red x) y (red y) (hm x) (hm y)
  have hred : Function.Surjective red := by
    intro y
    let l : primDR A' →ₗ[R] R₀ :=
      { toFun c := y ((redMor h').pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨xA, hx⟩ := Module.projective_lifting_property (Algebra.linearMap R R₀) l hπ
    refine ⟨e.symm xA, ?_⟩
    show hBC.bcMap (crysToDR κ h' (e.symm xA)) = y
    rw [ee]
    exact hBC.corr_iff.1 fun c ↦ (LinearMap.congr_fun hx c).symm
  have hker : ∀ x, red x = 0 → x ∈ (RingHom.ker π) • (⊤ : Submodule R (Crys κ (spMap π) P₀.A)) := by
    intro x hx
    have hc := hBC.corr_iff.2 hx
    have hmem := mem_smul_top_of_forall_mem (RingHom.ker π) (crysToDR κ h' x) fun c ↦
      RingHom.mem_ker.2 ((hc c).symm.trans (LinearMap.zero_apply _))
    have := Submodule.mem_map_of_mem (f := e.symm.toLinearMap) hmem
    rw [Submodule.map_smul''] at this
    have ex : e.symm.toLinearMap (crysToDR κ h' x) = x := e.symm_apply_apply x
    rw [ex] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hperf := exists_perfect_mod π red φ₀ φ' hπ perf.bijective_right.2 hred hker hrel

  have hFN : IsCompl (liftFil κ h') (N0.comap (crysToDR κ h')) :=
    (Submodule.orderIsoMapComap e).symm.isCompl hN0
  have hredFil : ∀ x ∈ liftFil κ h', red x ∈ Fil P₀.A := fun x hx ↦
    (hAdm (red x)).2 ⟨crysToDR κ h' x, hx, by exact hBC.corr_iff.2 rfl⟩
  have hFiso : ∀ x ∈ liftFil κ h', ∀ y ∈ liftFil κ h', φ₀ x y ∈ RingHom.ker π := fun x hx y hy ↦
    RingHom.mem_ker.2 ((hrel x y).symm.trans (((filL _).1 (hredFil x hx)) _ (hredFil y hy)))
  obtain ⟨E, N', hEN, hEiso, hEF⟩ := lagr_univ (RingHom.ker π) φ₀ hI2 h2
    (fun x y ↦ anti x y) hperf (liftFil κ h') _ hFN hFiso

  have shift : ∀ d d' (y : HdR P₀.A), d - d' ∈ (RingHom.ker π) • (⊤ : Submodule R (Crys κ (spMap π) P₀.A)) →
      (crysRedMor κ rfl P₀.A).Corr d y → (crysRedMor κ rfl P₀.A).Corr d' y := by
    intro d d' y hd H c
    rw [H c]
    have := RingHom.mem_ker.1 (apply_mem_of_mem_smul_top (RingHom.ker π) hd c)
    rw [LinearMap.sub_apply, map_sub, sub_eq_zero] at this
    exact this
  have hFE : ∀ y : HdR P₀.A, y ∈ Fil P₀.A ↔ ∃ d ∈ E, (crysRedMor κ rfl P₀.A).Corr d y := by
    intro y
    constructor
    · intro hy
      obtain ⟨xA, hxA, hc⟩ := (hAdm y).1 hy
      have d0F : e.symm xA ∈ liftFil κ h' := by
        show crysToDR κ h' (e.symm xA) ∈ Fil A'
        rw [ee]; exact hxA
      have hc0 : (crysRedMor κ rfl P₀.A).Corr (e.symm xA) y :=
        (corr_crysToDR_iff rfl h' bij.2 _ y).1 (by rw [ee]; exact hc)
      have hmem : e.symm xA ∈ E ⊔ (RingHom.ker π) • (⊤ : Submodule R (Crys κ (spMap π) P₀.A)) := by
        rw [hEF]; exact Submodule.mem_sup_left d0F
      obtain ⟨d, hd, j, hj, hdj⟩ := Submodule.mem_sup.1 hmem
      refine ⟨d, hd, shift _ _ y ?_ hc0⟩
      rw [← hdj, add_sub_cancel_left]; exact hj
    · rintro ⟨d, hd, hc⟩
      have hmem : d ∈ liftFil κ h' ⊔ (RingHom.ker π) • (⊤ : Submodule R (Crys κ (spMap π) P₀.A)) := by
        rw [← hEF]; exact Submodule.mem_sup_left hd
      obtain ⟨f, hf, j, hj, hfj⟩ := Submodule.mem_sup.1 hmem
      have hcf : (crysRedMor κ rfl P₀.A).Corr f y := shift d f y (by rw [← hfj, add_sub_cancel_left]; exact hj) hc
      exact (hAdm y).2 ⟨crysToDR κ h' f, hf, (corr_crysToDR_iff rfl h' bij.2 f y).2 hcf⟩

  obtain ⟨A, _, i, h, hA, hgA, hEq⟩ := GlobalTheory.RMDeform.exists_lift_abelian GD ADR κ hκ π hπ rfl h' hA' hg E ⟨N', hEN⟩ hFE
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback h h
  obtain ⟨Q, hQ, -, -, a₁, a₂, eQ⟩ := GlobalTheory.BirigidLift.exists_lift GD ADR ADC hκ hπ rfl hA hgA hA hgA h h l₁ l₂
    P₀.isLB P₀.ample P₀.isLB P₀.ample hΛ.isLB hΛ.zero_left hΛ.zero_right hφ₀ (by rw [hEq]; exact hEiso)
  exact ⟨A, _, i, l, Q, hA, h, ⟨l₁, l₂⟩, hQ, a₁, a₂, eQ⟩

end GlobalTheory.BirigLift
