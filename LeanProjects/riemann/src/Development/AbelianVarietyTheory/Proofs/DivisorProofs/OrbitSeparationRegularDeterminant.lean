import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefLineBundleWeightGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongerPublishedHypothesesImplyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRestrIsoTens
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KeepsCuspOfIsUnifAt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankHostDivTwo
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorGroupDeterminantsNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerExponentSectionMulEqZeroImpEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeatPrimeLevelAutSubgroupUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismUnipotentFixesComplexPointEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFramedPointOverComponentGenericPoinStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactificationComponentIntegralSmoothProjectivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentStabilizerActsByLevelChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantNormalProjectiveCompactificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentLinearisedLineBundleFiniteGroupQuotStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleDescendsHodgeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToroidalCanonicalBundleWeightLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleHodgeClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfPullbackSurjectiveProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsSeparateQuotientGenericFibreDescendsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspRuleOfBoundaryVanishingComponentSectioStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.OrbitSep

theorem val_ofSec_ne_zero {F : Type} [Field F] {X : Scheme.{0}} (p : X ⟶ Sp F) {B : LB X} (θ : B.Sec) (z : Sp ℂ ⟶ X)
    (k : B.ι) (hk : ⊤ ≤ z ⁻¹ᵁ B.U k) (hz : ∀ s, z s ∈ nonzeroLocus θ) :
    H0.val z k le_top hk (H0.ofSec p ⊤ θ) ≠ 0 := by
  refine (H0.val_ofSec z k le_top hk θ).trans_ne ?_
  have h : ⊤ ≤ z ⁻¹ᵁ X.basicOpen (θ.f k) := fun s hs =>
    (X.mem_basicOpen _ _ (hk hs)).2 ((isUnit_ger_iff θ (hk hs)).2 (hz s))
  rw [← TangentOrigin.evalPt_res z (X.basicOpen_le _) hk h]
  exact ((X.toRingedSpace.isUnit_res_basicOpen (θ.f k)).map _).ne_zero

theorem exists_chart_pt {X : Scheme.{0}} {B : LB X} (hB : B.IsLB) (z : Sp ℂ ⟶ X) : ∃ k, ⊤ ≤ z ⁻¹ᵁ B.U k := by
  obtain ⟨k, hk⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hB (z (IsLocalRing.closedPoint ℂ))
  refine ⟨k, fun s _ => ?_⟩
  obtain rfl : s = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact hk

theorem cls_nsmul {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ) (a : Λ) :
    cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) := by
  induction n with
  | zero =>
    have h := GlobalTheory.HSApp.cls_common_add C 0 0
    simp only [add_zero] at h
    simp only [zero_nsmul]
    exact left_eq_add.1 h
  | succ n ih => rw [succ_nsmul, GlobalTheory.HSApp.cls_common_add C, ih, succ_nsmul]

set_option maxHeartbeats 2000000 in

theorem separate_orbit (hP2 : Hypotheses2) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hSg : GlobalTheory.Published.SiegelToroidalIntegral) (hKS : GlobalTheory.Published.ToroidalForFanKS)
    (hLie : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7}
    {T : Core D} {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2)
    (hp : 1 ≤ (T.Q.Dw j).p) (hq : 1 ≤ (T.Q.Dw j).q) (S : Subgroup (LevelAut (T.Q.Dw j) Y.d.l₂))
    {I : Ideal (𝓞 D.host.E)} {g : ℕ} (hI : NeatPrime I g ((T.Q.Dw j).p + (T.Q.Dw j).q)) (hM : Y.d.l₂.Mb ≤ I)
    (hS : ∀ γ ∈ S, UnipAt I γ) (s : ℕ)
    (hs : (T.Q.Dw j).p + (T.Q.Dw j).q + ((T.Q.Dw j).dim + 1).choose 2 + 1 ≤ s) (Z : Comp Y.d.Xo₂ Y.d.c₂) :
    ∃ y : FrPt Y.d.Xo₂ Y.d.c₂ ℂ, LiesOn Z y ∧
      ∀ [Fintype {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y)}]
        (a : {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y)} → ℂ),
        (∀ u ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) ((s : ℤ) • hodgeWt (T.Q.Dw j)) 0),
          ∑ h, a h * evR Y.d.Xo₂ Y.d.c₂ u (move Y.d.Xo₂ Y.d.c₂ (h.1 : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y) = 0) → a = 0 := by
  have hP : Hypotheses₂ := GlobalTheory.T.stronger_published_hypotheses_imply hP2
  have hA : Y.d.l₂.A = 1 := hY.lev.2
  have hA' : Y.d.l₂.A.Coprime Y.d.l₂.M := hA ▸ Nat.coprime_one_left _
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hdim : 1 ≤ (T.Q.Dw j).dim := Nat.mul_pos (Nat.mul_pos (by omega) hp) hq
  have hfl : 1 ≤ FlagTan.dimFlag (T.Q.Dw j) := by
    refine Nat.mul_pos (by omega) ?_
    exact Nat.choose_pos (by omega)
  obtain ⟨TF⟩ := GlobalTheory.T.toroidal_flag_nonempty hP _ _ _ _ Y.d.Xo₂ Y.d.c₂ hfl
  have hF := hY.geo
  have hV := GlobalTheory.T.flagSpace_component_smooth_projective_connected _ _ _ _ _ _ TF Z hF
  obtain ⟨hint, hsm, hpr, hgc, hsurj, hnorm, hgen⟩ := GlobalTheory.T.compactificationComponent_integral_smooth_projective _ _ _ _ _ _ TF Z hF
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_complexFramedPoint_over_componentGenericPoint _ _ _ _ Y.d.Xo₂ Y.d.c₂ Z
  have hyZ : LiesOn Z y := fun s => hy s ▸ (Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)).mem
  refine ⟨y, hyZ, fun a ha => ?_⟩
  have lift : ∀ w : FrPt Y.d.Xo₂ Y.d.c₂ ℂ, LiesOn Z w → ∃ v : Sp ℂ ⟶ V₀ TF.Y Z, v ≫ i₀ TF.Y Z = ptF w := fun w hw =>
    ⟨IsOpenImmersion.lift (i₀ TF.Y Z) (ptF w) (by
      rintro _ ⟨s, rfl⟩
      exact ⟨⟨_, (j_mem_barComp Z _).2 (hw s)⟩, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨v₁, hv₁⟩ := lift y hyZ
  choose v hv using fun h : {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y)} => lift _ h.2
  obtain ⟨Γ, ρ, hΓ, hρ, hmem⟩ := GlobalTheory.T.componentStabilizer_acts_by_levelChange _ _ _ _ _ _ TF.Y Z hpq hA S
  obtain ⟨X', W, φ, ℓ, ρ', q, sW, hint', n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ :=
    GlobalTheory.T.equivariant_normal_projective_compactification Y.d.c₂.F _ _ (s₀ TF.Y Z) (j₀ TF.Y Z) Γ ρ hpr ⟨v₁ (IsLocalRing.closedPoint ℂ)⟩ hnorm hρ.1
  obtain ⟨δ, hδ, eδ, hlin⟩ := GlobalTheory.T.exists_line_bundle_descends_hodge hP2 _ _ _ _ _ _ TF Z hpq hA hF
  obtain ⟨N, hN, eN⟩ := GlobalTheory.T.exists_descent_linearised_lineBundle_finiteGroup_quotient Y.d.c₂.F X' W q sW Γ ρ' _ _ (n7 ▸ n2) n6
    (hlin I g hI hM Γ Γ.subtype ρ (fun γ => hS _ (hΓ γ.2)) hρ X' φ ℓ ρ' n1 n2 n3 n4 n5)
  let K := CanonLB.all (s₀ TF.Y Z) (T.Q.Dw j).dim
  obtain ⟨κ, hκ, eκ, θ, hθ⟩ := GlobalTheory.T.exists_toroidalCanonicalBundle_weight_line _ _ _ _ _ _ TF Z hpq hF K
  set m := ((T.Q.Dw j).dim + 1).choose 2 + 1 with hm
  obtain ⟨t, rfl⟩ : ∃ t, s = m + t := Nat.exists_eq_add_of_le (by omega)
  obtain ⟨N', hN', eN'⟩ := cls_surj (t • cls δ hδ - cls κ hκ)
  obtain ⟨B, hB, eB⟩ := cls_surj (m • cls δ hδ + cls N' hN')
  have C := common₀ TF.X Z
  have nef : ∀ (L : LB (X₀ TF.Y Z)) (hL : L.IsLB) (w : AllWt.Weight (T.Q.Dw j)), GapGe 0 w →
      CechPic.pull (π₀ TF.X Z) (cls L hL) = cls (L₀ TF.X Z w) (isLB_L₀ TF.X Z w) →
      (letI := algebraΓOfHom (s₀ TF.Y Z); IsNef Y.d.c₂.F L) := fun L hL w hw e =>
    GlobalTheory.T.isNefLineBundle_of_pullback_surjective_projective _ _ _ _ _ _ L hL _ _ (π₀_s₀ TF.X Z) hpr hV.2.1 hsurj e
      (GlobalTheory.T.nef_line_bundle_weight_gap hP hQ.nef hLie _ _ _ _ _ _ TF Z hF w hw)
  have ens : ∀ n : ℕ, cls (L₀ TF.X Z ((n : ℤ) • hodgeWt (T.Q.Dw j))) (isLB_L₀ TF.X Z _) =
      n • cls (L₀ TF.X Z (hodgeWt (T.Q.Dw j))) (isLB_L₀ TF.X Z _) := fun n => by
    rw [natCast_zsmul]; exact cls_nsmul (common₀ TF.X Z) n _
  have nefN' := nef N' hN' ((t : ℤ) • hodgeWt (T.Q.Dw j) - kapBase _) (gapGe_sub_kapBase _ (by omega)) (by
    have h := GlobalTheory.HSApp.cls_common_add (common₀ TF.X Z) ((t : ℤ) • hodgeWt (T.Q.Dw j) - kapBase _) (kapBase _)
    rw [sub_add_cancel] at h
    rw [eN', map_sub, map_nsmul, eδ, eκ, ← ens, sub_eq_iff_eq_add]
    exact h)
  have hKB := isLB_tens K.isLB hB
  have hθB := LB.isLB_div hκ K.isLB
  obtain ⟨Φ, hΦ, hval⟩ := GlobalTheory.T.exists_cuspRule_of_boundaryVanishing_componentSection D T j Y e o hY hf Z TF (((m + t : ℕ) : ℤ) • hodgeWt (T.Q.Dw j)) _
    (isLB_tens hθB hKB) (by
      rw [cls_tens hθB hKB, cls_div hκ K.isLB, cls_tens K.isLB hB, eB, eN', ens, ← eδ, ← map_nsmul]
      refine congrArg _ ?_
      have key : ∀ (A : Type 1) [AddCommGroup A] (a b k : A) (m t : ℕ),
          b - k + (k + (m • a + (t • a - b))) = (m + t) • a := fun A _ a b k m t => by
        rw [add_nsmul, ← add_assoc, sub_add_cancel, add_left_comm, add_sub_cancel]
      exact key _ _ _ _ _ _)
  choose k hk using fun h => exists_chart_pt hKB (v h ≫ j₀ TF.Y Z)
  choose k' hk' using fun h => exists_chart_pt hθB (v h ≫ j₀ TF.Y Z)
  choose lam hlam using fun h => hval _ (v h) (hv h) (k' h, k h) (fun s hs => ⟨hk' h hs, hk h hs⟩)
  have hc : ∀ h, H0.val (v h ≫ j₀ TF.Y Z) (k' h) le_top (hk' h) (H0.ofSec (s₀ TF.Y Z) ⊤ θ) ≠ 0 := fun h =>
    val_ofSec_ne_zero _ θ _ _ _ fun s => hθ ▸ ⟨v h s, rfl⟩
  have hvρ : ∀ h, v h = v₁ ≫ (ρ ⟨h.1, hmem _ h.1.2 y hyZ h.2⟩).hom := fun h => by
    rw [← cancel_mono (i₀ TF.Y Z), hv, Category.assoc, hρ.2 _ ℂ y v₁ hv₁]; rfl
  have h1 : LiesOn Z (move Y.d.Xo₂ Y.d.c₂ ((1 : S) : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y) := by
    rw [OneMemClass.coe_one, inv_one, LevDesc.move_one hpq hA']; exact hyZ
  have key := GlobalTheory.T.sections_separate_quotient_generic_fibre_descends hP2.q15 hQ.nef hP2.q16 Y.d.c₂.F (algebraMap _ ℂ) (X₀ TF.Y Z) X' W (V₀ TF.Y Z) (s₀ TF.Y Z) _ φ q sW
    (j₀ TF.Y Z) ℓ hpr hgc hdim n2 n8 n10 n11 n7 inferInstance n3 n4 K δ N' B hδ hN' hB N hN m eN
    (nef δ hδ _ gapGe_hodgeWt eδ) (GlobalTheory.T.descended_bundle_hodge_class hP2 hG hQ hSg hKS _ _ _ _ _ _ TF Z hp hq hF δ hδ eδ) nefN' (by omega) eB _ v
    (fun h h' e => ?_) (fun h => ?_) (fun h h' => ?_) ⟨⟨1, h1⟩, fun s => hgen _ ?_⟩ k hk
    (fun h => a h * (lam h * H0.val (v h ≫ j₀ TF.Y Z) (k' h) le_top (hk' h) (H0.ofSec (s₀ TF.Y Z) ⊤ θ))) fun u => ?_
  · funext h
    exact (mul_eq_zero.1 (congrFun key h)).resolve_right (mul_ne_zero (lam h).ne_zero (hc h))
  · have e' := (hv h').symm.trans (e ▸ hv h)
    have e₂ : move Y.d.Xo₂ Y.d.c₂ (h'.1 : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y =
        move Y.d.Xo₂ Y.d.c₂ ((h.1 * h'.1⁻¹ : S) : LevelAut (T.Q.Dw j) Y.d.l₂)
          (move Y.d.Xo₂ Y.d.c₂ (h.1 : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y) := by
      rw [← LevDesc.move_mul hpq hA']; simp
    rw [e₂] at e'
    have := GlobalTheory.T.levelAutomorphism_unipotent_fixes_complexPoint_eq_one _ _ _ _ _ _ hpq hA I g hI hM _ (hS _ (h.1 * h'.1⁻¹).2) _ e'
    exact Subtype.ext (mul_inv_eq_one.1 (Subtype.ext this))
  · have e₁ : TF.Y.j ≫ TF.Y.s = pullback.snd _ _ := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, TF.Y.jQ_over]
      exact (congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)
    rw [← Category.assoc (j₀ _ _), j₀_ι, Category.assoc, e₁, ← Category.assoc, hv]
    exact pullback.lift_snd _ _ _
  · rw [hvρ h, hvρ h', Category.assoc, Category.assoc, reassoc_of% n5, reassoc_of% n5, n6.comp_eq, n6.comp_eq]
  · change (v ⟨1, h1⟩ ≫ i₀ TF.Y Z) s = _
    rw [hv]
    simp only [OneMemClass.coe_one, inv_one, LevDesc.move_one hpq hA']
    exact hy s
  · let P := tensChart hθB hKB
    have hu := ha _ (hΦ (P.mul (H0.ofSec (s₀ TF.Y Z) ⊤ θ) u) fun x hx => ?_)
    · rw [← hu]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [hlam, mul_assoc, mul_assoc]
      exact congrArg (fun x => a h * (lam h * x)) (P.val_mul _ _ (k' h, k h) _ le_top (hk' h) (hk h) _).symm
    · obtain ⟨τ, ha', hb', hc'⟩ := P.cover x
      have hu := (isUnit_ger_iff _ hc').2 hx
      rw [ger_toSec, P.germ_mul _ _ τ x _ ha' hb' hc', H0.germ_ofSec] at hu
      exact hθ ▸ (isUnit_ger_iff θ ha').1 (isUnit_of_mul_isUnit_left hu)

end GlobalTheory.OrbitSep

namespace GlobalTheory.OrbitSep

open Formalism.MainNotions Formalism.L2.Theta GlobalTheory.DegVal GlobalTheory.DegCmp GlobalTheory.BadCount

theorem exists_cusp_levDet_regular : Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → 4 ≤ e → (∀ k, D.R.r + 1 < D.host.g k) → ∀ (fr : TypeFrame (T.Q.Dw j) Y.d.l₂) (S : Subgroup (LevelAut (T.Q.Dw j) Y.d.l₂)), (S = grpHR fr ∨ ∃ k, S = grpGHR fr k) → ∃ u ∈ Y.V (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0), ∀ f ∈ secRing Y.d.Xo₂ Y.d.c₂, levDet Y.d.Xo₂ Y.d.c₂ S u * f = 0 → f = 0 := by
  classical
  intro hP2 hG hQ hSg hKS hLie D T hT j hp hq hf hj Y e o hY _ hg fr S hS
  have hA : Y.d.l₂.A = 1 := hY.lev.2
  have hA' : Y.d.l₂.A.Coprime Y.d.l₂.M := hA ▸ Nat.coprime_one_left _
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hdat := hT.pins.2.2.2 j hj
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [hdat.1, hdat.2.1]; exact Formalism.L2.Geo.sigW_sum D hj.1 hj.2
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [hY.lev.1.2.1, hT.pins.2.1.1]
  obtain ⟨I, g, hI, hMb, hU⟩ := GlobalTheory.T.exists_neatPrime_levelAutSubgroup_unipotent D _ (T.Q.Dw j) Y.d.l₂ ⟨_, hM⟩ (hr ▸ hg) fr S hS
  have hs : (T.Q.Dw j).p + (T.Q.Dw j).q + ((T.Q.Dw j).dim + 1).choose 2 + 1 ≤ cZeroN D j := by
    have := (cZeroN_isLeast D j).1.2.1
    rw [hr, Datum.dim, GlobalTheory.FlagDim.finrank_host_div_two, hdat.1, hdat.2.1]
    omega
  choose y hyZ hy using separate_orbit hP2 hG hQ hSg hKS hLie Y hY hf hp hq S hI hMb hU _ hs
  have : Finite (Comp Y.d.Xo₂ Y.d.c₂) := CompFin.finite_comp _ _
  let G := wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0
  let ev : Comp Y.d.Xo₂ Y.d.c₂ → Y.V G →ₗ[Y.d.c₂.F] (S → ℂ) := fun Z => LinearMap.pi fun h =>
    evalL (K := Y.d.c₂.F) (fun R _ _ => FrPt Y.d.Xo₂ Y.d.c₂ R) (fun φ y z => FrMap φ y z)
      (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ (y Z)) ∘ₗ (Y.V G).subtype
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_vector_groupDeterminants_ne_zero Y.d.c₂.F (Y.V G) S _ ev
    (fun Z => {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ (y Z))}) (fun _ h => h.1)
    (fun Z => (AllWt.suppOn Z).comap (Y.V G).subtype)
    (fun Z => ⟨⟨1, by rw [OneMemClass.coe_one, inv_one, LevDesc.move_one hpq hA']; exact hyZ Z⟩, rfl⟩)
    (fun Z v hv h hh => hv ℂ _ ((AllWt.liesOff_iff Z _).2 fun h' => hh ⟨⟨h, h'⟩, rfl⟩))
    (fun Z a ha => hy Z a fun u hu => ha ⟨u, hu.1⟩ hu.2)
  have hu' := AllWt.cuspW_le_secZ _ u.2
  refine ⟨u, u.2, GlobalTheory.T.integerExponentSection_mul_eq_zero_imp_eq_zero _ _ _ _ _ _ _ _ (LevDesc.levDet_mem_secZ hpq hA' hu') fun Z => ⟨y Z, hyZ Z, ?_⟩⟩
  have ht := GlobalTheory.FlagTan.fromTest_of_isLocalRing (y Z)
  let χ : Rul Y.d.Xo₂ Y.d.c₂ →+* ℂ :=
    { toFun := fun f => evR Y.d.Xo₂ Y.d.c₂ f (y Z)
      map_one' := evalAt_one _ _ _ ht
      map_mul' := fun f g => evalAt_mul _ _ f g _
      map_zero' := evalAt_zero _ _ _
      map_add' := fun f g => evalAt_add _ _ f g _ }
  have e₁ := χ.map_det (LevDesc.levMat Y.d.Xo₂ Y.d.c₂ S u)
  refine fun h0 => hu Z ?_
  rw [← h0]
  refine Eq.trans ?_ (e₁.symm.trans ?_)
  · congr 1
    ext h g
    exact (GlobalTheory.LevelKeeps.evR_transl hpq hA' _ hu' (y Z)).symm
  · change χ _ = χ _
    unfold levDet
    congr!

end GlobalTheory.OrbitSep
