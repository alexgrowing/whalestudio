import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulTopOfForallMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
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

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AbDual

namespace GlobalTheory.AltLift

theorem altLagr : ∀ (R : Type) [CommRing R] (I : Ideal R) (D : Type) [AddCommGroup D] [Module R D] [Module.Finite R D] [Module.Projective R D] (φ : D →ₗ[R] D →ₗ[R] R), I ^ 2 = ⊥ → (∀ x, φ x x = 0) → (∀ l : D →ₗ[R] R, ∃ z, ∀ x, l x - φ x z ∈ I) → ∀ F N : Submodule R D, IsCompl F N → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → ∃ E N' : Submodule R D, IsCompl E N' ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ E ⊔ I • (⊤ : Submodule R D) = F ⊔ I • (⊤ : Submodule R D) := by
  intro R _ I D _ _ _ _ φ hI2 halt hsurj F N hFN hF
  have hskew : ∀ x y, φ x y = -φ y x := by
    intro x y
    have h := halt (x + y)
    simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  have hII : ∀ a ∈ I, ∀ b ∈ I, a * b = 0 := by
    intro a ha b hb
    have h : a * b ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rw [hI2] at h; exact (Submodule.mem_bot R).1 h
  have hφI : ∀ a ∈ I • (⊤ : Submodule R D), ∀ y, φ a y ∈ I := by
    intro a ha y
    refine Submodule.smul_induction_on (p := fun a => φ a y ∈ I) ha ?_ ?_
    · intro r hr m _
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ hr
    · intro x z hx hz
      simp only [map_add, LinearMap.add_apply]
      exact I.add_mem hx hz
  have hφII : ∀ a ∈ I • (⊤ : Submodule R D), ∀ b ∈ I • (⊤ : Submodule R D), φ a b = 0 := by
    intro a ha b hb
    refine Submodule.smul_induction_on (p := fun a => φ a b = 0) ha ?_ ?_
    · intro r hr m _
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      have : φ m b ∈ I := by rw [hskew]; exact I.neg_mem (hφI b hb m)
      exact hII r hr _ this
    · intro x z hx hz
      simp only [map_add, LinearMap.add_apply, hx, hz, add_zero]
  have hsmul0 : ∀ r ∈ I, ∀ w ∈ I • (⊤ : Submodule R D), r • w = 0 := by
    intro r hr w hw
    refine Submodule.smul_induction_on (p := fun w => r • w = 0) hw ?_ ?_
    · intro r' hr' m _
      rw [smul_smul, hII r hr r' hr', zero_smul]
    · intro x z hx hz
      rw [smul_add, hx, hz, add_zero]

  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R D
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfs : ∀ x, f (s x) = x := fun x => by simpa using LinearMap.congr_fun hs x
  let e : Fin n → D := fun i => f (fun j => if i = j then 1 else 0)
  have hexp : ∀ x, x = ∑ i, s x i • e i := fun x => by
    conv_lhs => rw [← hfs x]
    exact LinearMap.pi_apply_eq_sum_univ f (s x)
  choose z hz using fun i : Fin n => hsurj ((LinearMap.proj i).comp s)
  have hz' : ∀ i x, s x i - φ x (z i) ∈ I := fun i x => by simpa using hz i x

  let P : D →ₗ[R] D := F.subtype ∘ₗ Submodule.linearProjOfIsCompl F N hFN
  have hPF : ∀ x, P x ∈ F := fun x => (Submodule.linearProjOfIsCompl F N hFN x).2
  have hPx : ∀ x ∈ F, P x = x := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hFN ⟨x, hx⟩)
  let B : D →ₗ[R] D →ₗ[R] R := φ.compl₁₂ P P
  have hB : ∀ x y, B x y = φ (P x) (P y) := fun x y => rfl
  have hBI : ∀ x y, B x y ∈ I := fun x y => hF _ (hPF x) _ (hPF y)
  have hBalt : ∀ x, B x x = 0 := fun x => halt _
  have hBskew : ∀ x y, B x y = -B y x := fun x y => hskew _ _
  have hBexp : ∀ x y, B x y = ∑ i, ∑ j, s x i * s y j * B (e i) (e j) := by
    intro x y
    conv_lhs => rw [hexp x, hexp y]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

  let M : Fin n → Fin n → R := fun i j => if i < j then B (e i) (e j) else 0
  have hMI : ∀ i j, M i j ∈ I := fun i j => by
    simp only [M]; split_ifs
    · exact hBI _ _
    · exact I.zero_mem
  have hMd : ∀ i j, M i j - M j i = B (e i) (e j) := by
    intro i j
    simp only [M]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_pos h, if_neg (lt_asymm h), sub_zero]
    · rw [if_neg (lt_irrefl _), sub_zero, hBalt]
    · rw [if_neg (lt_asymm h), if_pos h, zero_sub, hBskew, neg_neg]
  let β : D →ₗ[R] D →ₗ[R] R :=
    ∑ i, ∑ j, M i j • (LinearMap.mul R R).compl₁₂ ((LinearMap.proj i).comp s) ((LinearMap.proj j).comp s)
  have hβ : ∀ x y, β x y = ∑ i, ∑ j, M i j * (s x i * s y j) := by
    intro x y
    simp [β, LinearMap.sum_apply]
  have hβI : ∀ x y, β x y ∈ I := fun x y => by
    rw [hβ]
    exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => I.mul_mem_right _ (hMI i j)
  have hβd : ∀ x y, β x y - β y x = B x y := by
    intro x y
    rw [hβ, hβ, hBexp, Finset.sum_comm (f := fun i j => M i j * (s y i * s x j)), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hMd]; ring
  have hβexp : ∀ x y, β x y = ∑ i, s x i * β (e i) y := by
    intro x y
    conv_lhs => rw [hexp x]
    simp [map_sum, LinearMap.sum_apply, smul_eq_mul]
  let T : D →ₗ[R] D := -∑ i, LinearMap.smulRight (β (e i)) (z i)
  have hT : ∀ y, T y = -∑ i, β (e i) y • z i := fun y => by
    simp [T]
  have hTr : ∀ y, T y ∈ I • (⊤ : Submodule R D) := fun y => by
    rw [hT]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem_smul (hβI _ _) Submodule.mem_top)
  have hTI : ∀ a ∈ I • (⊤ : Submodule R D), T a = 0 := by
    intro a ha
    refine Submodule.smul_induction_on (p := fun a => T a = 0) ha ?_ ?_
    · intro r hr m _
      rw [map_smul]; exact hsmul0 r hr _ (hTr m)
    · intro x w hx hw
      rw [map_add, hx, hw, add_zero]
  have hTT : ∀ y, T (T y) = 0 := fun y => hTI _ (hTr y)
  have hkey : ∀ x y, φ x (T y) = -β x y := by
    intro x y
    have h0 : ∑ i, β (e i) y * (s x i - φ x (z i)) = 0 :=
      Finset.sum_eq_zero fun i _ => hII _ (hβI _ _) _ (hz' i x)
    rw [hT, map_neg, map_sum, hβexp]
    simp only [map_smul, smul_eq_mul]
    have h1 : ∑ i, s x i * β (e i) y - ∑ i, β (e i) y * φ x (z i) = 0 := by
      rw [← Finset.sum_sub_distrib, ← h0]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [sub_eq_zero.1 h1]
  let u : D ≃ₗ[R] D := LinearEquiv.ofLinear (LinearMap.id + T) (LinearMap.id - T)
    (LinearMap.ext fun y => by simp [hTT]) (LinearMap.ext fun y => by simp [hTT])
  have hu : ∀ x, u x = x + T x := fun x => rfl
  refine ⟨F.map (u : D →ₗ[R] D), N.map (u : D →ₗ[R] D), ?_, ?_, ?_⟩
  · exact (Submodule.orderIsoMapComap u).isCompl hFN
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show φ (u x) (u y) = 0
    rw [hu, hu, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply]
    have h1 := hkey x y
    have h2 := hkey y x
    have h3 := hskew (T x) y
    have h5 := hφII (T x) (hTr x) (T y) (hTr y)
    have h6 := hβd x y
    rw [hB, hPx x hx, hPx y hy] at h6
    linear_combination h1 + h3 - h2 + h5 - h6
  · apply le_antisymm
    · refine sup_le ?_ le_sup_right
      rintro _ ⟨x, hx, rfl⟩
      show u x ∈ _
      rw [hu]
      exact Submodule.add_mem_sup hx (hTr x)
    · refine sup_le ?_ le_sup_right
      intro x hx
      refine Submodule.mem_sup.2 ⟨u x, ⟨x, hx, rfl⟩, -T x, Submodule.neg_mem _ (hTr x), ?_⟩
      rw [hu]; abel

theorem altLagr_univ {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) {D : Type*} [AddCommGroup D] [Module R D]
    [Module.Finite R D] [Module.Projective R D] (φ : D →ₗ[R] D →ₗ[R] R) (hI : I ^ 2 = ⊥)
    (alt : ∀ x, φ x x = 0) (perf : ∀ l : D →ₗ[R] R, ∃ z, ∀ x, l x - φ x z ∈ I) (F N : Submodule R D)
    (hFN : IsCompl F N) (iso : ∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) :
    ∃ E N' : Submodule R D, IsCompl E N' ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧
      E ⊔ I • (⊤ : Submodule R D) = F ⊔ I • (⊤ : Submodule R D) := by
  haveI : Module.Free R D := Module.free_of_flat_of_isLocalRing
  let ε := (Module.finBasis R D).equivFun
  let ψ : (Fin (Module.finrank R D) → R) →ₗ[R] (Fin (Module.finrank R D) → R) →ₗ[R] R :=
    φ.compl₁₂ ε.symm.toLinearMap ε.symm.toLinearMap
  have hψ : ∀ x y, ψ x y = φ (ε.symm x) (ε.symm y) := fun _ _ ↦ rfl
  obtain ⟨E, N', hEN, hE, hEF⟩ := altLagr R I _ ψ hI (fun x ↦ by simp only [hψ]; exact alt _)
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

open GlobalTheory.BirigLift

theorem exists_isPolForm {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {S : Scheme.{0}}
    {t : S ⟶ Sp R} {A : Over S} [GrpObj A] (C : CupSquare κ t A) {L : LB A.left} (hL : L.IsLB) :
    ∃ ψ, IsPolForm κ t A L ψ := by
  obtain ⟨z, hz, -⟩ := (isChern_existsUnique_and_iso R _ κ _ (A.hom ≫ t)).1 _ hL
  obtain ⟨n, a, b, rfl⟩ := C.span z
  have hm : ∀ c, c ∈ prim κ t A := fun c ↦ C.allPrim ▸ trivial
  exact ⟨_, n, fun k ↦ ⟨a k, hm _⟩, fun k ↦ ⟨b k, hm _⟩, hz, rfl⟩

open GlobalTheory.Published.GrothendieckMessing in

theorem exists_lift_lam : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀], IsAbelianScheme Y₀ → ∀ L₀ : LB Y₀.left, L₀.IsLB → RelAmple Y₀ L₀ → KTriv Y₀ L₀ → ∃ (Y : Over (Sp R)) (_ : GrpObj Y) (i : Y₀.left ⟶ Y.left) (l : (Y₀ ⊗ Y₀).left ⟶ (Y ⊗ Y).left) (Q : LB (Y ⊗ Y).left), IsAbelianScheme Y ∧ IsGrpPullback Y₀ Y (spMap π) i ∧ IsSquare i l ∧ Q.IsLB ∧ GlobalTheory.AbDual.IsAdditive Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ LBIso (Q.pull l) (abelian₂ Y₀ L₀) := by
  intro R R₀ _ _ _ _ _ π hπ hI2 Y₀ _ hY₀ L₀ hL₀ hamp hK
  have hI0 : RingHom.ker π ^ 2 = 0 := hI2
  let κ := divided₂ hI0
  have hκ : IsNilDP κ := isDPNilpotent_squareZero hI0
  have ADD : GlobalTheory.Published.DualAbelianScheme := GlobalTheory.T.dualAbelianScheme_exists_biduality
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.T.abelianScheme_firstDeRham_structure
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal_of_dualAbelianScheme ADD
  have GD : GlobalTheory.Published.GrothendieckDeformation := GlobalTheory.Published.grothendieckDeformation₂
    GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates ADD GlobalTheory.T.poincareDeRhamDuality_abelianScheme GlobalTheory.T.print_abelianLifting
  haveI := hY₀.comm
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.AbelianDim.exists_relDim R₀ Y₀ hY₀
  obtain ⟨A', _, i', h', hA'⟩ := GlobalTheory.T.abelianScheme_unobstructed_squareZero_affine R (RingHom.ker π) hI0 R₀ π hπ rfl Y₀ hY₀
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim R A' hA'
  have C := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl hA' hg hA' hg h' h'
  have C₁ := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys ADR.1 ADC.2 hκ hπ rfl hA' hg h'.1 (liftMor κ h')
  have hΛ := isPerfect_lam hL₀ hK

  obtain ⟨φ₀, hψ⟩ := exists_isPolForm C₁ hL₀
  have hφ₀ : IsCorrForm κ (spMap π) Y₀ Y₀ (abelian₂ Y₀ L₀) φ₀ := isCorrForm_lam hψ
  have alt : ∀ x, φ₀ x x = 0 := hψ.isAlt

  have HC := (GD R (RingHom.ker π) κ hκ R₀ π hπ rfl).1
  obtain ⟨bij, ⟨N0, hN0⟩, hAdm⟩ := HC g Y₀ A' i' h' hA' hg
  let e := LinearEquiv.ofBijective (crysToDR κ h') (HC.crysToDR_bijective h' hA' hg)
  have ee : ∀ xA, crysToDR κ h' (e.symm xA) = xA := e.apply_symm_apply
  letI : Algebra R R₀ := π.toAlgebra
  have hBC := (ADR.2.2.1 R A' g hA' hg R₀ Y₀ i' h').1
  obtain ⟨hfinA, hprojA, -⟩ := ADR.1.prim hA' hg
  haveI := hfinA
  haveI := hprojA
  haveI : Module.Finite R (Crys κ (spMap π) Y₀) := Module.Finite.equiv e.symm
  haveI : Module.Projective R (Crys κ (spMap π) Y₀) := Module.Projective.of_equiv e.symm

  let red : Crys κ (spMap π) Y₀ →ₛₗ[π] HdR Y₀ := hBC.bcMap.comp (crysToDR κ h')
  have hm : ∀ x, (crysRedMor κ rfl Y₀).Corr x (red x) := fun x ↦
    (corr_crysToDR_iff rfl h' bij.2 x (red x)).1 (by exact hBC.corr_iff.2 rfl)
  have iso : LBIso ((abelian₂ Y₀ L₀).pull (Over.Hom.left (𝟙 (Y₀ ⊗ Y₀)))) (abelian₂ Y₀ L₀) :=
    (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hΛ.isLB _) hΛ.isLB).1
      (by rw [GlobalTheory.CechPic.cls_pull hΛ.isLB, Over.id_left, GlobalTheory.CechPic.pull_id])
  obtain ⟨φ', hφ', e'⟩ := hφ₀.pull hΛ.isLB (crysRedMor κ rfl Y₀) (crysRedMor κ rfl Y₀)
    (h := Over.Hom.left (𝟙 (Y₀ ⊗ Y₀))) (by simp) (by simp) hΛ.isLB iso
  obtain ⟨perf, filL, -⟩ := (GlobalTheory.Published.AbelianDualCrystal.duality ADR hY₀ hg₀ hY₀ hg₀ hΛ).2 φ' hφ'
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
  have hker : ∀ x, red x = 0 → x ∈ (RingHom.ker π) • (⊤ : Submodule R (Crys κ (spMap π) Y₀)) := by
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
  have hredFil : ∀ x ∈ liftFil κ h', red x ∈ Fil Y₀ := fun x hx ↦
    (hAdm (red x)).2 ⟨crysToDR κ h' x, hx, by exact hBC.corr_iff.2 rfl⟩
  have hFiso : ∀ x ∈ liftFil κ h', ∀ y ∈ liftFil κ h', φ₀ x y ∈ RingHom.ker π := fun x hx y hy ↦
    RingHom.mem_ker.2 ((hrel x y).symm.trans (((filL _).1 (hredFil x hx)) _ (hredFil y hy)))
  obtain ⟨E, N', hEN, hEiso, hEF⟩ := altLagr_univ (RingHom.ker π) φ₀ hI2 alt hperf (liftFil κ h') _ hFN hFiso

  have shift : ∀ d d' (y : HdR Y₀), d - d' ∈ (RingHom.ker π) • (⊤ : Submodule R (Crys κ (spMap π) Y₀)) →
      (crysRedMor κ rfl Y₀).Corr d y → (crysRedMor κ rfl Y₀).Corr d' y := by
    intro d d' y hd H c
    rw [H c]
    have := RingHom.mem_ker.1 (apply_mem_of_mem_smul_top (RingHom.ker π) hd c)
    rw [LinearMap.sub_apply, map_sub, sub_eq_zero] at this
    exact this
  have hFE : ∀ y : HdR Y₀, y ∈ Fil Y₀ ↔ ∃ d ∈ E, (crysRedMor κ rfl Y₀).Corr d y := by
    intro y
    constructor
    · intro hy
      obtain ⟨xA, hxA, hc⟩ := (hAdm y).1 hy
      have d0F : e.symm xA ∈ liftFil κ h' := by
        show crysToDR κ h' (e.symm xA) ∈ Fil A'
        rw [ee]; exact hxA
      have hc0 : (crysRedMor κ rfl Y₀).Corr (e.symm xA) y :=
        (corr_crysToDR_iff rfl h' bij.2 _ y).1 (by rw [ee]; exact hc)
      have hmem : e.symm xA ∈ E ⊔ (RingHom.ker π) • (⊤ : Submodule R (Crys κ (spMap π) Y₀)) := by
        rw [hEF]; exact Submodule.mem_sup_left d0F
      obtain ⟨d, hd, j, hj, hdj⟩ := Submodule.mem_sup.1 hmem
      refine ⟨d, hd, shift _ _ y ?_ hc0⟩
      rw [← hdj, add_sub_cancel_left]; exact hj
    · rintro ⟨d, hd, hc⟩
      have hmem : d ∈ liftFil κ h' ⊔ (RingHom.ker π) • (⊤ : Submodule R (Crys κ (spMap π) Y₀)) := by
        rw [← hEF]; exact Submodule.mem_sup_left hd
      obtain ⟨f, hf, j, hj, hfj⟩ := Submodule.mem_sup.1 hmem
      have hcf : (crysRedMor κ rfl Y₀).Corr f y := shift d f y (by rw [← hfj, add_sub_cancel_left]; exact hj) hc
      exact (hAdm y).2 ⟨crysToDR κ h' f, hf, (corr_crysToDR_iff rfl h' bij.2 f y).2 hcf⟩

  obtain ⟨A, _, i, h, hA, hgA, hEq⟩ := GlobalTheory.RMDeform.exists_lift_abelian GD ADR κ hκ π hπ rfl h' hA' hg E ⟨N', hEN⟩ hFE
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback h h
  obtain ⟨Q, hQ, -, -, a₁, a₂, eQ⟩ := GlobalTheory.BirigidLift.exists_lift GD ADR ADC hκ hπ rfl hA hgA hA hgA h h l₁ l₂
    hL₀ hamp hL₀ hamp hΛ.isLB hΛ.zero_left hΛ.zero_right hφ₀ (by rw [hEq]; exact hEiso)
  exact ⟨A, _, i, l, Q, hA, h, ⟨l₁, l₂⟩, hQ, a₁, a₂, eQ⟩

end GlobalTheory.AltLift
