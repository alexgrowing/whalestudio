import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalIffEtalePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNefBigOfClassEqSmulAddSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulIntersectionLeOfNefClassOnClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberCurveOfClassEqSmulAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsolatedNonKltDivisorSmoothProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSectionProjectiveOverFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionOverFieldEqOfClosedPointImageEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleValueAtPointNeZeroIffMemNonzeroLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorPullbackOfDominantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassCartierDivisorPullbackEqPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProportiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSeparatingClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolatedInFibreOfEtaleRestrictionStatement
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
open GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleSep

set_option maxHeartbeats 1000000 in

theorem sections_separate_fibre : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)], IsProjOver p → IsProjOver (f ≫ p) → 1 ≤ n → letI := algebraΓOfHom p; letI := algebraΓOfHom (f ≫ p); ∀ (K : CanonLB (f ≫ p) n) (N : LB W) (hN : N.IsLB) (N' B : LB M) (hN' : N'.IsLB) (hB : B.IsLB) (m : ℕ) (x : Sp ℂ ⟶ W) (U : W.Opens), IsNef ℂ N → IsBig ℂ N → IsNef ℂ (N.pull f) → IsBig ℂ (N.pull f) → IsNef ℂ N' → (n + 1).choose 2 < m → cls B hB = m • CechPic.pull f (cls N hN) + cls N' hN' → x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → Etale (f ∣_ U) → (∀ (Z : Closeds W) (e : ℕ), IsIrreducible (Z : Set W) → Set.range x ⊆ Z → 1 ≤ e → topologicalKrullDim (Z : Set W) = e → 0 < interNumRed ℂ Z fun _ : Fin e => N) → ∀ (J : Type) [Fintype J] (z : J → (Sp ℂ ⟶ M)), Function.Injective z → (∀ j, z j ≫ f = x) → ∀ (k : J → (tens K.bundle B).ι) (hk : ∀ j, ⊤ ≤ z j ⁻¹ᵁ (tens K.bundle B).U (k j)) (a : J → ℂ), (∀ g : H0 (f ≫ p) (tens K.bundle B) ⊤, ∑ j, a j * H0.val (z j) (k j) le_top (hk j) g = 0) → a = 0 := by
  intro hK hNN M W _ _ p f _ n _ _ hp hpM hn1
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (f ≫ p)
  intro K N hN N' B hN' hB m x U hNn hNb hNfn hNfb hN'n hm hBc hxp hxU hEt hpos J _ z hzi hz k hk a hrel
  haveI : IsLocallyNoetherian W := by
    haveI := SmoothOfRelativeDimension.smooth n p; exact LocallyOfFiniteType.isLocallyNoetherian p
  haveI : IsLocallyNoetherian M := by
    haveI := SmoothOfRelativeDimension.smooth n (f ≫ p); exact LocallyOfFiniteType.isLocallyNoetherian (f ≫ p)
  set c₀ := (n + 1).choose 2 with hc₀def
  set pt : Sp ℂ := IsLocalRing.closedPoint ℂ with hpt
  set x₀ : W := x pt with hx₀
  have hrange : ∀ Z : Closeds W, x₀ ∈ Z → Set.range x ⊆ Z := by
    rintro Z h _ ⟨q, rfl⟩
    rwa [Subsingleton.elim q pt]
  have hx₀c : IsClosed ({x₀} : Set W) := GlobalTheory.T.isClosed_image_section_projective_over_field ℂ W p x hp hxp
  have hx₀U : x₀ ∈ U := hxU (Set.mem_univ pt)

  obtain ⟨N₀, h₀, hc₀, hn₀, hb₀⟩ := GlobalTheory.nef_big_of_cls_eq_smul_add_smul hNN ℂ W p hp N N hN hN (2 * c₀ + 1) 0
    hNn hNb hNn (by omega)
  obtain ⟨m', D₀, U', hm', hD₀, hcur, hxU', hklt, hnk⟩ := GlobalTheory.KollarApp.isolatedNonKlt_smooth hK.2 W p n hp hn1
    N₀ 2 x₀ two_pos hn₀ hb₀ hx₀c (fun Z e hZ hxZ he hdim => by
      have h1 := hpos Z e hZ (hrange Z hxZ) he hdim
      have h2 := GlobalTheory.mixExp_interNumRed hNN ℂ W p hp N N N₀ hN hN h₀ (2 * c₀ + 1) 0 Z e hNn hNn hc₀ hdim
      have h3 : ((2 * c₀ + 1 : ℕ) : ℤ) ^ e ≤ interNumRed ℂ Z (fun _ : Fin e => N₀) := by
        have : (0 : ℤ) ≤ ((2 * c₀ + 1 : ℕ) : ℤ) ^ e := by positivity
        nlinarith
      have h3' : (((2 * c₀ + 1 : ℕ) : ℝ)) ^ e ≤ (interNumRed ℂ Z (fun _ : Fin e => N₀) : ℝ) := by
        exact_mod_cast h3
      have h4 : (((c₀ : ℕ) : ℝ) * 2) ^ e < ((2 * c₀ + 1 : ℕ) : ℝ) ^ e := by
        refine pow_lt_pow_left₀ ?_ (by positivity) (by omega)
        exact_mod_cast (by omega : c₀ * 2 < 2 * c₀ + 1)
      rw [lt_div_iff₀ (by positivity), ← mul_pow]
      push_cast at h4 h3' ⊢
      linarith)

  obtain ⟨D₁, hD₁, heq⟩ := GlobalTheory.T.exists_effective_cartierDivisorPullback_of_dominant M W f D₀ hD₀
  have hcls := GlobalTheory.T.cechPicardClass_cartierDivisorPullback_eq_pullback M W f D₀ D₁ heq

  obtain ⟨M₀, hM₀, hcM, hnM, hbM⟩ := GlobalTheory.nef_big_of_cls_eq_smul_add_smul hNN ℂ M (f ≫ p) hpM (N.pull f) N'
    (pull_isLB hN f) hN' (2 * m - 2 * c₀ - 1) 2 hNfn hNfb hN'n (by omega)
  have hclsN : cls (N.pull f) (pull_isLB hN f) = CechPic.pull f (cls N hN) := cls_pull hN f _
  obtain ⟨Jd, hJ, hvan⟩ := GlobalTheory.NadelApp.nadel_canonical_add hK.1 M (f ≫ p) n hpM K B M₀ hB D₁ m' 2 hm' two_pos
    hD₁ hnM hbM (fun C hC => by
      have e1 := GlobalTheory.interNumRed_of_cls_eq_nsmul_add ℂ M (f ≫ p) hpM B (N.pull f) N' hB (pull_isLB hN f) hN' m 1
        C hC (by rw [hBc, one_smul, hclsN])
      have e2 := GlobalTheory.interNumRed_of_cls_eq_nsmul_add ℂ M (f ≫ p) hpM M₀ (N.pull f) N' hM₀ (pull_isLB hN f) hN'
        (2 * m - 2 * c₀ - 1) 2 C hC hcM
      have e3 := interNumRed_one_congr (k := ℂ) (isLB_toLB D₁) (pull_isLB (isLB_toLB D₀) f)
        (hcls.trans (cls_pull (isLB_toLB D₀) f _).symm) C
      have e4 := GlobalTheory.T.intersectionNumber_pullback_proportional_of_proportional M W p f hp hpM (toLB D₀) N₀ (isLB_toLB D₀) h₀ 2 m' (fun C' hC' => by
        have := hcur C' hC'
        have hm'0 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
        rw [Nat.cast_ofNat, div_eq_div_iff hm'0 two_ne_zero] at this
        have h' : ((2 * interNumRed ℂ C' ![toLB D₀] : ℤ) : ℚ) = ((m' * interNumRed ℂ C' ![N₀] : ℤ) : ℚ) := by
          push_cast; linarith
        push_cast
        exact_mod_cast h') C hC
      have e5 := GlobalTheory.interNumRed_of_cls_eq_nsmul_add ℂ M (f ≫ p) hpM (N₀.pull f) (N.pull f) (N.pull f)
        (pull_isLB h₀ f) (pull_isLB hN f) (pull_isLB hN f) (2 * c₀ + 1) 0 C hC
        (by rw [cls_pull h₀ f _, hc₀, hclsN, zero_smul, add_zero, zero_smul, add_zero, map_nsmul])
      rw [e1, e3, e2]
      have hm'0 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
      have e4' : ((interNumRed ℂ C ![(toLB D₀).pull f] : ℤ) : ℚ) = m' * (2 * c₀ + 1) / 2 * interNumRed ℂ C ![N.pull f] := by
        have : (2 : ℚ) * interNumRed ℂ C ![(toLB D₀).pull f] = m' * interNumRed ℂ C ![N₀.pull f] := by exact_mod_cast e4
        rw [e5] at this
        push_cast at this
        linarith
      have hsub : ((2 * m - 2 * c₀ - 1 : ℕ) : ℚ) = 2 * m - 2 * c₀ - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [e4']
      push_cast [hsub]
      field_simp
      ring)

  set UM : M.Opens := f ⁻¹ᵁ (U ⊓ U') with hUM
  have hEtM : Etale (UM.ι ≫ f) := by
    haveI := hEt
    have hle : UM ≤ f ⁻¹ᵁ U := fun y hy => hy.1
    have e : UM.ι ≫ f = M.homOfLE hle ≫ (f ∣_ U) ≫ U.ι := by
      rw [morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
    rw [e]; infer_instance
  have hkl := GlobalTheory.T.kawamataLogTerminal_iff_etale_pullback M W p f n m' UM D₀ D₁ hEtM hm' heq
  have hsupp : ∀ y ∈ UM, (y ∈ Jd.support ↔ f y = x₀) := by
    intro y hy
    rw [hJ, hkl y hy]
    have hyU' : f y ∈ U' := hy.2
    constructor
    · intro h; by_contra hne; exact h (hklt _ hyU' hne)
    · intro e; rw [e]; exact hnk
  have hfz : ∀ j, f (z j pt) = x₀ := fun j => by
    have := congrArg (fun h : Sp ℂ ⟶ W => h pt) (hz j)
    simpa using this
  have hzM : ∀ j, z j pt ∈ UM := fun j => by
    show f (z j pt) ∈ U ⊓ U'
    rw [hfz j]; exact ⟨hx₀U, hxU'⟩
  have hzp : ∀ j, z j ≫ f ≫ p = 𝟙 _ := fun j => by rw [← Category.assoc, hz j, hxp]
  have hzne : ∀ i j, i ≠ j → z i pt ≠ z j pt := fun i j hij e =>
    hij (hzi (GlobalTheory.T.section_over_field_eq_of_closedPoint_image_eq ℂ M (f ≫ p) (z i) (z j) (hzp i) (hzp j) e))
  funext j
  show a j = 0
  obtain ⟨V, hzV, hV⟩ := GlobalTheory.T.isolated_in_fibre_of_etale_restriction M W f U hEt (z j pt) (by rw [hfz j]; exact hx₀U)
  obtain ⟨s, hs, hs'⟩ := GlobalTheory.T.exists_section_separating_closed_point ℂ M (f ≫ p) hpM (tens K.bundle B) (isLB_tens K.isLB hB) Jd (z j pt) (V ⊓ UM)
    (GlobalTheory.T.isClosed_image_section_projective_over_field ℂ M (f ≫ p) (z j) hpM (hzp j)) ⟨hzV, hzM j⟩ (fun y hy => by
      rw [hsupp y hy.2, ← hfz j]
      exact ⟨hV y hy.1, fun e => e ▸ rfl⟩) (hvan 1 one_pos)
  have h1 := hrel (H0.ofSec (f ≫ p) ⊤ s)
  rw [Finset.sum_eq_single j (fun i _ hij => by
      have : H0.val (z i) (k i) le_top (hk i) (H0.ofSec (f ≫ p) ⊤ s) = 0 := by
        by_contra hne
        exact hs' _ ((hsupp _ (hzM i)).2 (hfz i)) (hzne i j hij)
          ((GlobalTheory.T.lineBundleValueAtPoint_ne_zero_iff_mem_nonzeroLocus ℂ M (f ≫ p) _ s (z i) (k i) (hk i)).1 hne)
      rw [this, mul_zero]) (fun h => absurd (Finset.mem_univ j) h)] at h1
  exact (mul_eq_zero.1 h1).resolve_right ((GlobalTheory.T.lineBundleValueAtPoint_ne_zero_iff_mem_nonzeroLocus ℂ M (f ≫ p) _ s (z j) (k j) (hk j)).2 hs)

end GlobalTheory.EtaleSep
