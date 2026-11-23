import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushforwardTwistHomDualIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannRochHomDualAverageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyArithDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyValueUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleSectionsAvoidClosedPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartStatementHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkCharZeroEssFiniteType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperRelAmpleKTrivOfPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperOfAbelianEverywhere
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleCanonicalTrivialLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupDivisorAmpleCriterion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTrivialTorusAbelianLocus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfDensePartOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertVanish

section Differences

variable {G : Type*} [AddCommGroup G]

theorem eq_zero_of_eventually (a y : G) : ∀ (d : ℕ) (ψ : G → ℤ), DiffVanish d ψ →
    (∀ᶠ n : ℕ in atTop, ψ (y + n • a) = 0) → ∀ n : ℕ, ψ (y + n • a) = 0
  | 0, ψ, h, _ => fun n => by rw [diffVanish_zero_iff.1 h]; rfl
  | d + 1, ψ, h, h0 => by
    obtain ⟨N, hN⟩ := eventually_atTop.1 h0
    have e (n : ℕ) : y + (n + 1) • a - a = y + n • a := by rw [succ_nsmul]; abel
    have ih := eq_zero_of_eventually a y d _ (diffVanish_succ_iff.1 h a) (eventually_atTop.2 ⟨N + 1, fun n hn => by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [bwdDiff_apply, e, hN _ (by omega), hN _ (by omega), sub_zero]⟩)
    have step (n j : ℕ) : ψ (y + (n + j) • a) = ψ (y + n • a) := by
      induction j with
      | zero => rfl
      | succ j ihj =>
        have := ih (n + j + 1)
        rw [bwdDiff_apply, e, sub_eq_zero] at this
        rw [← ihj, ← this, add_assoc n j 1]
    exact fun n => (step n N).symm.trans (hN _ (by omega))

variable {ι : Type} [Fintype ι]

def linHom (ι : Type) [Fintype ι] : (ι → ℤ) →+ MvPolynomial ι ℝ :=
  AddMonoidHom.mk' (fun n => lin fun i => (n i : ℝ)) fun n m => by
    simp only [lin, Pi.add_apply, Int.cast_add, map_add, add_mul, Finset.sum_add_distrib]

def combHom (c : ι → G) : (ι → ℤ) →+ G :=
  AddMonoidHom.mk' (fun n => ∑ i, n i • c i) fun n m => by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem apply_prod {D : ℕ} {φ : G → ℤ} (h : DiffVanish (D + 1) φ) (c : ι → G) (t : ℝ)
    (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (hΦ : ∀ n : ι → ℤ, Φ (lin (fun i => (n i : ℝ)) ^ D) = multiDiff (fun _ : Fin D => ∑ i, n i • c i) φ 0 * t)
    (m : Fin D → ι → ℤ) : Φ (∏ j, linHom ι (m j)) = h.form (fun j => combHom c (m j)) * t := by
  have e₁ := congrFun (multiDiff_comap (linHom ι) m fun P => P ^ D) 0
  rw [Function.comp_apply, multiDiff_pow] at e₁
  have e₂ := congrFun (multiDiff_map Φ.toAddMonoidHom m ((fun P => P ^ D) ∘ linHom ι)) 0
  rw [Function.comp_apply, e₁] at e₂
  have e₃ := congrFun (multiDiff_comap (combHom c) m fun y => h.form fun _ => y) 0
  rw [Function.comp_apply, h.multiDiff_form_diag] at e₃
  have e₄ := congrFun (multiDiff_map ((AddMonoidHom.mulRight t).comp (Int.castAddHom ℝ)) m
    ((fun y => h.form fun _ => y) ∘ combHom c)) 0
  rw [Function.comp_apply, e₃] at e₄
  have e₅ : Φ.toAddMonoidHom ∘ (fun P => P ^ D) ∘ linHom ι =
      ((AddMonoidHom.mulRight t).comp (Int.castAddHom ℝ)) ∘ (fun y => h.form fun _ => y) ∘ combHom c :=
    funext fun n => (hΦ n).trans (by rw [← h.form_apply _ 0]; rfl)
  rw [e₅, e₄] at e₂
  have hD : (D.factorial : ℝ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  apply mul_left_cancel₀ hD
  have e₆ : Φ ((D.factorial : MvPolynomial ι ℝ) * ∏ j, linHom ι (m j)) = D.factorial * Φ (∏ j, linHom ι (m j)) := by
    rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  rw [← e₆]
  refine e₂.symm.trans ?_
  simp [mul_assoc, Function.comp_def]

theorem apply_powerSum_mul {N : ℕ} {φ : G → ℤ} (h : DiffVanish (N + 2 + 1) φ) (c : ι → G) (t : ℝ)
    (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (hΦ : ∀ n : ι → ℤ, Φ (lin (fun i => (n i : ℝ)) ^ (N + 2)) =
      multiDiff (fun _ : Fin (N + 2) => ∑ i, n i • c i) φ 0 * t)
    (hΦ' : ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ N + 2 → P.IsHomogeneous d → Φ P = 0)
    {κ : Type} [Fintype κ] (u : κ → ι)
    (hu : ∀ y, ∑ j, (φ (c (u j) + y) + φ (-c (u j) + y) - 2 * φ y) = 0) (Q : MvPolynomial ι ℝ) :
    Φ ((∑ j, MvPolynomial.X (u j) ^ 2) * Q) = 0 := by
  have hp : (∑ j, MvPolynomial.X (u j) ^ 2 : MvPolynomial ι ℝ).IsHomogeneous 2 :=
    IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_X_pow _ _
  have key := Model.eq_zero_of_pow N (Φ ∘ₗ LinearMap.mulLeft ℝ (∑ j, MvPolynomial.X (u j) ^ 2)) (fun n => ?_)
    fun P e he hP => hΦ' _ (2 + e) (by omega) (hp.mul hP)
  · exact LinearMap.congr_fun key Q
  let g : Fin N → G := fun _ => combHom c n
  have e₁ (j : κ) : Φ (MvPolynomial.X (u j) ^ 2 * lin (fun i => (n i : ℝ)) ^ N) =
      multiDiff g (fun y => φ (c (u j) + y) + φ (-c (u j) + y) - 2 * φ y) 0 * t := by
    have a₁ : linHom ι (Pi.single (u j) 1) = MvPolynomial.X (u j) := by
      simp [linHom, lin, Pi.single_apply]
    have a₂ : combHom c (Pi.single (u j) 1) = c (u j) := by
      simp [combHom, Pi.single_apply]
    have := apply_prod h c t Φ hΦ (Fin.cons (Pi.single (u j) 1) (Fin.cons (Pi.single (u j) 1) fun _ => n))
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ] at this
    simp only [Fin.cons_zero, Fin.cons_succ, a₁, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    rw [sq, mul_assoc]
    refine this.trans ?_
    have a₃ : (fun i => combHom c ((Fin.cons (Pi.single (u j) 1) (Fin.cons (Pi.single (u j) 1) fun _ => n) :
        Fin (N + 2) → ι → ℤ) i)) = (Fin.cons (c (u j)) (Fin.cons (c (u j)) g) : Fin (N + 2) → G) := by
      funext i
      refine Fin.cases a₂ (fun i => Fin.cases a₂ (fun i => rfl) i) i
    rw [a₃, h.form_apply _ (c (u j) + 0), multiDiff_cons', multiDiff_cons', ← multiDiff_translate]
    congr 4
    funext y
    simp only [bwdDiff_apply, add_sub_cancel_left]
    rw [show y - c (u j) = -c (u j) + y by abel]
    ring
  have e₂ : ∑ j, multiDiff g (fun y => φ (c (u j) + y) + φ (-c (u j) + y) - 2 * φ y) 0 = 0 := by
    simp only [multiDiff_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun S _ => ?_
    rw [← Finset.smul_sum, hu, smul_zero]
  rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, Finset.sum_mul, map_sum, Finset.sum_congr rfl fun j _ => e₁ j,
    ← Finset.sum_mul, ← Int.cast_sum, e₂, Int.cast_zero, zero_mul]

end Differences

section Euler

open GlobalTheory.VB GlobalTheory.CechPic Limits

variable {κ : Type} [Field κ] {Y : Scheme.{0}} [Algebra κ Γ(Y, ⊤)]

theorem chiPic_rank_one {L : Y.Modules} (h : IsVB L 1) (y : Pic Y) :
    chiPic κ L y = chiPic κ (structureModule Y) (cls _ h.isLB_det + y) ∧
      chiPic κ (VB.dual L) y = chiPic κ (structureModule Y) (-cls _ h.isLB_det + y) := by
  have key {M : Y.Modules} (h : IsVB M 1) :
      chiPic κ M y = chiPic κ (structureModule Y) (cls _ h.isLB_det + y) := by
    rw [← chiPic_twist κ _ h.isLB_det, chiPic_congr κ (h.isoDet ≪≫ (Twist.unitTwistIso _).symm)]
  refine ⟨key h, (key h.dual).trans ?_⟩
  rw [← cls_dual h.isLB_det (isLB_dual h.isLB_det),
    (cls_eq_iff (isLB_dual h.isLB_det) h.dual.isLB_det).2 h.lbIso_det_dual]

theorem chiPic_flag (hY : IsProjOver (strHom κ Y)) {E : Y.Modules} {r : ℕ} (fl : Vert.Flag E r) (y : Pic Y) :
    chiPic κ E y + chiPic κ (VB.dual E) y = ∑ i, (chiPic κ (structureModule Y) (cls _ (fl.isLB_root i) + y) +
      chiPic κ (structureModule Y) (-cls _ (fl.isLB_root i) + y)) := by
  have fin {M : Y.Modules} {n : ℕ} (h : IsVB M n) : FiniteCohTwists κ M :=
    have := h.isFiniteQC
    finiteCohTwists_of_isProjOver (algebraMap_eq_strHom κ Y) M hY
  have key (i : Fin (r + 1)) : chiPic κ (fl.F i) y + chiPic κ (VB.dual (fl.F i)) y =
      ∑ j : Fin r, if (j : ℕ) < i then chiPic κ (structureModule Y) (cls _ (fl.isLB_root j) + y) +
        chiPic κ (structureModule Y) (-cls _ (fl.isLB_root j) + y) else 0 := by
    induction i using Fin.induction with
    | zero =>
      have z {M : Y.Modules} (h : IsVB M 0) : chiPic κ M y = 0 := by
        obtain ⟨M', hM, rfl⟩ := cls_surj y
        exact chi_eq_zero_of_isZero κ ((Twist.isZero_twist_iff hM).2 (isVB_zero_iff.1 h))
      rw [z (fl.isVB 0), z (fl.isVB 0).dual]
      simp
    | succ i ih =>
      have hS : (ShortComplex.mk (fl.step i) (cokernel.π _) (cokernel.condition _)).ShortExact :=
        { exact := ShortComplex.exact_cokernel _ }
      have e₁ := congrFun (chiPic_shortExact hS (fin (fl.isVB _)) (fin (fl.isVB_gr i))) y
      have e₂ := congrFun (chiPic_shortExact (GlobalTheory.DualExact.shortExact_dual Y _ 1 hS (fl.isVB_gr i))
        (fin (fl.isVB_gr i).dual) (fin (fl.isVB _).dual)) y
      obtain ⟨e₃, e₄⟩ := chiPic_rank_one (κ := κ) (fl.isVB_gr i) y
      have e₅ : ∑ j : Fin r, (if (j : ℕ) < i.succ then chiPic κ (structureModule Y) (cls _ (fl.isLB_root j) + y) +
          chiPic κ (structureModule Y) (-cls _ (fl.isLB_root j) + y) else 0) =
          ∑ j : Fin r, (if (j : ℕ) < i.castSucc then chiPic κ (structureModule Y) (cls _ (fl.isLB_root j) + y) +
            chiPic κ (structureModule Y) (-cls _ (fl.isLB_root j) + y) else 0) +
          ∑ j : Fin r, (if j = i then chiPic κ (structureModule Y) (cls _ (fl.isLB_root j) + y) +
            chiPic κ (structureModule Y) (-cls _ (fl.isLB_root j) + y) else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
        split_ifs <;> omega
      rw [e₅, ← ih, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
      change chiPic κ (fl.F i.succ) y = chiPic κ (fl.F i.castSucc) y + chiPic κ (fl.gr i) y at e₁
      change chiPic κ (VB.dual (fl.F i.succ)) y =
        chiPic κ (VB.dual (fl.gr i)) y + chiPic κ (VB.dual (fl.F i.castSucc)) y at e₂
      change _ = _ + (chiPic κ (structureModule Y) (cls _ (fl.isVB_gr i).isLB_det + y) +
        chiPic κ (structureModule Y) (-cls _ (fl.isVB_gr i).isLB_det + y))
      omega
  rw [← chiPic_congr κ (asIso (fl.ι (Fin.last r))), chiPic_congr κ (dualIso (asIso (fl.ι (Fin.last r)))), key]
  simp

variable {T : Scheme.{0}} [Algebra κ Γ(T, ⊤)]

theorem eventually_chi_pushforward (hT : IsProjOver (strHom κ T)) (hY : IsProjOver (strHom κ Y)) (ρ : Y ⟶ T)
    (hρ : ρ ≫ strHom κ T = strHom κ Y) {L : LB Y} (hL : IsAmpleLB L) (H : Y.Modules) [QCoh.IsFiniteQC H] :
    ∀ᶠ n in atTop, QCoh.IsFiniteQC ((Scheme.Modules.pushforward ρ).obj (twist H (lbPow L n))) ∧
      chi κ ((Scheme.Modules.pushforward ρ).obj (twist H (lbPow L n))) = chi κ (twist H (lbPow L n)) := by
  have hPT := (isProper_and_exists_isAmpleLB_of_isProjOver hT).1
  have hPT' := (isProper_and_exists_isAmpleLB_of_isProjOver hY).1
  have : IsProper (ρ ≫ strHom κ T) := hρ ▸ hPT'
  have : IsProper ρ := .of_comp ρ (strHom κ T)
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (strHom κ T)
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (strHom κ T)
  have := isAffineHom_diagonal_of_isSeparated (strHom κ T)
  have hπ : ∀ r : κ, ρ.appTop (algebraMap κ Γ(T, ⊤) r) = algebraMap κ Γ(Y, ⊤) r := fun r => by
    rw [algebraMap_eq_strHom κ T, algebraMap_eq_strHom κ Y, ← hρ, Scheme.Hom.comp_appTop]
    rfl
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := T) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  have hV : ∀ᶠ n : ℕ in atTop, ∀ I : Finset (Fin m), I.Nonempty → ∀ q, 0 < q →
      Subsingleton (cohOn (twist H (lbPow L n)) (ρ ⁻¹ᵁ (⨅ i ∈ I, D i)) q) :=
    eventually_all.2 fun I => eventually_all.2 fun hI =>
      GlobalTheory.ProperFinite.eventually_subsingleton_cohOn ρ hL H (hD' I hI)
  filter_upwards [hV] with n hn
  have := GlobalTheory.Twist.isFiniteQC_twist (F := H) (isLB_lbPow hL.isLB n)
  have hF := GlobalTheory.ProperFinite.isFiniteQC_pushforward ρ hL (twist H (lbPow L n))
  refine ⟨hF, chi_eq_of_linearEquiv κ fun p => ?_⟩
  exact (GlobalTheory.ProperFinite.nonempty_coh_pushforward_equiv κ ρ hπ _ hc hD' hn p).some

theorem chiPic_pullback [IsIntegral T] (hT : IndefiniteRowSideFullHecke.GenericFiniteMaps.IsProjSurface κ T) (hY : IsProjOver (strHom κ Y)) {d : ℕ}
    (hd : topologicalKrullDim Y = d) (ρ : Y ⟶ T) (hρ : ρ ≫ strHom κ T = strHom κ Y) {E : T.Modules} {r : ℕ}
    (hE : IsVB E r) (h0 : IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2 κ E = 0) (y : Pic Y) :
    chiPic κ ((Scheme.Modules.pullback ρ).obj E) y + chiPic κ (VB.dual ((Scheme.Modules.pullback ρ).obj E)) y =
      2 * r * chiPic κ (structureModule Y) y := by
  obtain ⟨-, L, hL⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hY
  obtain ⟨θ, -, -, hθ⟩ := GlobalTheory.DualPull.exists_dual_pullback T Y ρ
  have := hθ E r hE
  rw [← chiPic_congr κ (asIso (θ E))]
  have h₁ := (hE.pullback ρ).isFiniteQC
  have h₂ := (hE.dual.pullback ρ).isFiniteQC
  have h₃ := (isVB_structureModule Y).isFiniteQC
  have hv (F : Y.Modules) [QCoh.IsFiniteQC F] : DiffVanish (d + 1) (chiPic κ F) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom κ Y) F hY ((QCoh.suppDim_le F).trans hd.le)
  let ψ : Pic Y → ℤ := chiPic κ ((Scheme.Modules.pullback ρ).obj E) +
    chiPic κ ((Scheme.Modules.pullback ρ).obj (VB.dual E)) -
      (AddMonoidHom.mulLeft (2 * r : ℤ)) ∘ chiPic κ (structureModule Y)
  have hψ : DiffVanish (d + 1) ψ := fun g => by
    rw [multiDiff_sub, multiDiff_add, hv _ g, hv _ g, (hv _).map _ g]
    simp
  obtain ⟨M, hM, rfl⟩ := cls_surj y
  have key := eq_zero_of_eventually (cls L hL.isLB) (cls M hM) _ ψ hψ ?_ 0
  · rw [zero_nsmul, add_zero] at key
    exact sub_eq_zero.1 key
  have aux (H : Y.Modules) [QCoh.IsFiniteQC H] : ∀ᶠ n : ℕ in atTop,
      QCoh.IsFiniteQC ((Scheme.Modules.pushforward ρ).obj (twist H (tens M (lbPow L n)))) ∧
      chi κ ((Scheme.Modules.pushforward ρ).obj (twist H (tens M (lbPow L n)))) =
        chiPic κ H (cls M hM + n • cls L hL.isLB) := by
    have := GlobalTheory.Twist.isFiniteQC_twist (F := H) hM
    filter_upwards [eventually_chi_pushforward hT.isProjOver hY ρ hρ hL (twist H M)] with n hn
    have hP := isLB_lbPow hL.isLB n
    obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq H hM hP (isLB_tens hM hP) rfl
    have e' := (Scheme.Modules.pushforward ρ).mapIso e
    have := hn.1
    refine ⟨QCoh.IsFiniteQC.of_iso e', ?_⟩
    rw [← chi_congr κ e', hn.2, ← chiPic_cls κ _ hP, chiPic_twist κ _ hM, ← natCast_zsmul,
      ← cls_lbZPow hL.isLB (n : ℤ) (Twist.isLB_lbZPow hL.isLB (n : ℤ))]
  filter_upwards [aux ((Scheme.Modules.pullback ρ).obj E), aux ((Scheme.Modules.pullback ρ).obj (VB.dual E)),
    aux (structureModule Y)] with n a₁ a₂ a₃
  obtain ⟨⟨φ₁⟩, ⟨φ₂⟩⟩ := GlobalTheory.ProjFml.projection_formula T Y ρ E r hE _ (isLB_tens hM (isLB_lbPow hL.isLB n))
  have hA := GlobalTheory.T.riemann_roch_hom_dual_average κ T hT E r hE _ a₃.1
  rw [h0, mul_zero, ← chi_congr κ φ₁, ← chi_congr κ φ₂, a₁.2, a₂.2, a₃.2] at hA
  refine Int.cast_injective (α := ℚ) ?_
  simp only [ψ, Pi.sub_apply, Pi.add_apply, Function.comp_apply, AddMonoidHom.coe_mulLeft]
  push_cast
  linear_combination 2 * hA

end Euler

section Polarisation

open GlobalTheory.CechPic Limits MonoidalCategory CartesianMonoidalCategory GlobalTheory.PolLocal
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Geo.Tor.Datum H}
  {l : Geo.Tor.Level H} {Xo : Geo.Tor.Moduli Dw l} {c : Geo.Tor.Coeff l}
  (Z : Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))

theorem exists_chart {x : Z.X} (hx : x ∈ abLocus Z.t.G) : ∃ (U : Z.X.Opens) (hU : IsAffineOpen U), x ∈ U ∧
    ∃ (t : SAB H (Sp Γ(Z.X, U))) (_ : SABMap t Z.t hU.fromSpec),
      IsProper t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  obtain ⟨_, -, -, h₁, h₂, h₃, h₄⟩ := GlobalTheory.ModelRelCompare.densePart Z (GlobalTheory.CoeffRings.coeff_isDedFrac E H l c).1
  have hN : GlobalTheory.IsNormalScheme Z.X := (GlobalTheory.isNormalScheme_iff _).2 Z.normal
  obtain ⟨U, hU, _, hxU, hle, hic⟩ := GlobalTheory.FlatModel.exists_affine_normal_domain
    ⟨_, GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_gmod Z⟩ hx
  have := (GlobalTheory.GModStalk.charZero_essFiniteType_stalk E H Dw l Xo c Z x).1
  have : CharZero Γ(Z.X, U) := (Z.X.presheaf.germ U x hxU).hom.charZero
  have : IsNoetherianRing Γ(Z.X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨t, ⟨m⟩⟩ := exists_pull (S' := Sp Γ(Z.X, U)) hU.fromSpec Z.t
  have hg : Set.range (Out.jK Γ(Z.X, U) ≫ hU.fromSpec) ⊆ Set.range Z.j := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨v, hv⟩ := h₃.denseRange.exists_mem_open U.isOpen ⟨x, hxU⟩
    obtain ⟨p, hp⟩ := hU.range_fromSpec.ge hv
    have hs : Out.jK Γ(Z.X, U) q ⤳ p := specializes_iff_forall_open.2 fun W hW hpW =>
      GlobalTheory.LN.GenericPoint.jK_mem hW ⟨p, hpW⟩ q
    obtain ⟨v', -, e⟩ := Flat.generalizingMap Z.j (hp ▸ hs.map hU.fromSpec.continuous)
    exact ⟨v', e⟩
  obtain ⟨y, hy⟩ := GlobalTheory.HomExt.exists_lift_of_range_subset Z.j _ hg
  have hP := GlobalTheory.GoodTrait.polAt_of_point Z m _ y hy
  have hp := GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus E H _ t hP (Set.eq_univ_of_forall fun q =>
    (abLocus_pullback abLocusOne Z.t.semi m.cart.1 q).1 (hle (hU.range_fromSpec.le ⟨q, rfl⟩)))
  exact ⟨U, hU, hxU, t, m, hp, GlobalTheory.PolNormal.relAmple_kTriv_of_normal hic t hp hP⟩

theorem exists_open {T : Scheme.{0}} {g : T ⟶ Z.X} (hg : Set.range g ⊆ abLocus Z.t.G) {t : SAB H T}
    (m : SABMap t Z.t g) (x : T) : ∃ V : T.Opens, x ∈ V ∧ ∀ (S : Scheme.{0}) (s : S ⟶ T) (u : SAB H S),
      SABMap u t s → (∀ q, s q ∈ V) → IsProper u.G.hom ∧ Out.RelAmple u.G u.PP.L ∧ Out.KTriv u.G u.PP.L := by
  obtain ⟨U, hU, hx, t₀, m₀, hp, hA, hK⟩ := exists_chart Z (hg ⟨x, rfl⟩)
  refine ⟨g ⁻¹ᵁ U, hx, fun S s u n hs => ?_⟩
  obtain ⟨n', -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m n
  have hr : Set.range (s ≫ g) ⊆ Set.range hU.fromSpec := by
    rintro _ ⟨q, rfl⟩
    rw [hU.range_fromSpec]
    exact hs q
  obtain ⟨n'', -⟩ := GlobalTheory.ArcObj.exists_sab_fac m₀ n' (g := IsOpenImmersion.lift hU.fromSpec _ hr)
    (IsOpenImmersion.lift_fac _ _ hr).symm
  exact ⟨isProper_of_map n'' hp, pull_ample_kTriv n'' hA hK⟩

theorem isAbelianScheme_and_isPrincipalPol {T : Scheme.{0}} {g : T ⟶ Z.X} (hg : Set.range g ⊆ abLocus Z.t.G)
    {t : SAB H T} (m : SABMap t Z.t g) : IsAbelianScheme t.G ∧
      IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol t.G (lam (cls t.PP.L t.PP.isLB) (fst t.G t.G) (snd t.G t.G)) := by
  choose V hx hV using exists_open Z hg m
  have hp : IsProper t.G.hom := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) V
      (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩) fun x => ?_
    obtain ⟨u, ⟨n⟩⟩ := exists_pull (V x).ι t
    have h := (hV x _ _ u n fun q => q.2).1
    have e := n.cart.1.isoIsPullback_hom_snd _ _ (isPullback_morphismRestrict t.G.hom (V x)).flip
    rw [← e] at h
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).1 h
  refine ⟨⟨t.comm, t.semi.smooth, hp, t.semi.geomConnected⟩, ?_, ?_, fun Ω _ _ s => ?_⟩
  · rw [pull_lam, lift_fst, lam_one_left]
  · rw [pull_lam, lift_snd, lam_one_right]
  · obtain ⟨u, ⟨n⟩⟩ := exists_pull s t
    obtain ⟨-, hA, hK⟩ := hV (s (IsLocalRing.closedPoint Ω)) _ s u n fun q => by
      rw [Subsingleton.elim q (IsLocalRing.closedPoint Ω)]; exact hx _
    obtain ⟨-, hA', hK'⟩ := GlobalTheory.LocM.PolFibre.polAt_of_map n inferInstance hA hK
    refine ⟨_, pull_isLB t.PP.isLB (pullback.fst t.G.hom s), hA', hK', ?_⟩
    rw [IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase, pull_lam, lift_fst, lift_snd, cls_pull t.PP.isLB,
      lam_pull_of_isGrpPullback (isGrpPullback_pullback t.G s)]
    rfl

end Polarisation

section Main

open GlobalTheory.CechPic GlobalTheory.VB

theorem val_eq_zero (hC : ArCalc) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {p : X ⟶ Sp k} {d : ℕ} (hX : IsArithVar p d) {E : X.Modules} {r : ℕ} {h : VMetric p E r} (H : h.IsCInf)
    (F : FlagSp E r) (N : HermLB p) (z : X) (hz : topologicalKrullDim (closure ({z} : Set X)) = (0 + 2 : ℕ))
    (ℓ : ℕ) [Fact ℓ.Prime] [Algebra (ZMod ℓ) Γ((Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme, ⊤)]
    (h0 : IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2 (ZMod ℓ) ((Scheme.Modules.pullback (redι (clo z))).obj E) = 0) :
    F.val H N z 0 = 0 := by
  obtain ⟨y, Φ, hy, hΦ, e⟩ : F.IsVal H N z 0 (F.val H N z 0) :=
    Classical.epsilon_spec ((GlobalTheory.T.flag_variety_value_unique hC k X p d hX E r h H F N z 0).1 hz).exists
  obtain ⟨hY, -, hz'⟩ := (GlobalTheory.T.flag_variety_arith_dimension k X p d hX E r h.isVB).2 F
  obtain ⟨y', hy', hcl, hd⟩ := hz' z
  obtain rfl : y = y' := ((hy.2 y' hy'.1).antisymm (hy'.2 y hy.1)).eq
  obtain ⟨ρ, hρ⟩ := GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset (redι (clo y) ≫ F.π) (redι (clo z)) (by
    rintro _ ⟨q, rfl⟩
    rw [range_redι]
    exact hcl.le ((range_redι (clo y)).le ⟨q, rfl⟩))
  let _ : Algebra (ZMod ℓ) Γ((Scheme.IdealSheafData.vanishingIdeal (clo y)).subscheme, ⊤) :=
    (ρ.appTop.hom.comp (algebraMap (ZMod ℓ) _)).toAlgebra
  have hp := GlobalTheory.VertProj.isProjOver_strHom_zmod k _ _ _ hY _ (redι (clo y)) ℓ
  have hdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal (clo y)).subscheme = (r.choose 2 + 2 : ℕ) :=
    ((topologicalKrullDim_red (clo y)).trans (hd _ hz)).trans (by congr 1; omega)
  have hT : IndefiniteRowSideFullHecke.GenericFiniteMaps.IsProjSurface (ZMod ℓ) (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme :=
    ⟨inferInstance, (topologicalKrullDim_red (clo z)).trans hz,
      GlobalTheory.VertProj.isProjOver_strHom_zmod k _ _ _ hX _ (redι (clo z)) ℓ⟩
  have hgen : redι (clo y) (genericPoint _) = y := by
    have h₁ := (genericPoint_spec (Scheme.IdealSheafData.vanishingIdeal (clo y)).subscheme).image
      (redι (clo y)).continuous
    rw [Set.image_univ, range_redι] at h₁
    exact h₁.eq closure_closure.symm
  have hv := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom (ZMod ℓ) _) (structureModule _) hp
    ((QCoh.suppDim_le _).trans hdim.le)
  have iso : (Scheme.Modules.pullback (redι (clo y))).obj ((Scheme.Modules.pullback F.π).obj E) ≅
      (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback (redι (clo z))).obj E) :=
    (Scheme.Modules.pullbackComp _ _).app E ≪≫ (Scheme.Modules.pullbackCongr hρ.symm).app E ≪≫
      ((Scheme.Modules.pullbackComp _ _).app E).symm
  have hD : 0 + 2 + r.choose 2 = r.choose 2 + 2 := by omega
  rw [hD] at hΦ
  rw [← e, vdmPol, mul_assoc, mul_assoc, mul_left_comm]
  refine apply_powerSum_mul hv (fun o => pull (redι (clo y)) (cls _ (F.fam H N o).isLB)) (Real.log ℓ) Φ
    (fun n => ?_) hΦ.2 some (fun w => ?_) _
  · obtain ⟨g, hg, e'⟩ := hΦ.1 n
    have hL := LB.isLB_pull (comb (F.fam H N) n).isLB (redι (clo y))
    rw [← e', ← congrArg g hgen, hg.vertical _ (redι (clo y)) (ZMod ℓ) _ hdim, Nat.card_zmod, topSelf_def,
      interNum_eq_multiDiff _ _ fun _ => hL, cls_pull (comb (F.fam H N) n).isLB, GenFibreSecs.cls_comb, map_sum]
    simp only [map_zsmul]
  · have a (i : Fin r) : pull (redι (clo y)) (cls _ (F.fam H N (some i)).isLB) =
        cls _ ((F.fl.pull (redι (clo y))).isLB_root i) := by
      have h₁ := pull_isLB (F.fl.isLB_root i) (redι (clo y))
      refine (cls_pull (F.fl.isLB_root i) _ h₁).symm.trans ((cls_eq_iff h₁ _).2 ?_)
      exact ((F.fl.isVB_gr i).lbIso_det_pullback _).trans h₁ ((F.fl.isVB_gr i).pullback _).isLB_det
        ((F.fl.pull _).isLB_root i) (((F.fl.isVB_gr i).pullback _).lbIso_det_of_iso (F.fl.pullGrIso _ i))
    have b₁ := chiPic_flag hp (F.fl.pull (redι (clo y))) w
    have b₂ := chiPic_pullback hT hp hdim ρ (comp_strHom fun _ => rfl) (h.isVB.pullback _) h0 w
    rw [chiPic_congr _ iso, ← chiPic_congr _ (dualIso iso), b₂] at b₁
    simp only [a]
    rw [Finset.sum_sub_distrib, ← b₁]
    simp
    ring

theorem vertical_val_eq_zero : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.Ch2HodgeVanishes → OnObj fun _ O _ _ _ _ => ∀ c (M : DRBase O c) (I : M.Emb) (z : M.B), I.Good z 0 → ¬ CharZero (M.B.residueField z) → ∀ R : ℝ, M.val R z 0 = 0 := by
  intro _ h2 _ _ hV D O _ _ _ _ _ _ c M I z hG hz R
  have hgen : redι (clo z) (genericPoint _) = z := by
    have h₁ := (genericPoint_spec (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme).image
      (redι (clo z)).continuous
    rw [Set.image_univ, range_redι] at h₁
    exact h₁.eq closure_closure.symm
  rcases M.ar.vertical_or_horizontal (redι (clo z)) with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, -⟩
  swap
  · refine absurd ?_ hz
    rw [← hgen]
    refine ((redι (clo z)).residueFieldMap (genericPoint _)).hom.charZero_iff (RingHom.injective _) |>.2 ?_
    have : CharZero (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme.functionField :=
      ((Cartier.fnOf ⊤ (TopologicalSpace.Opens.mem_top _)).charZero_iff (Cartier.fnOf_injective ⊤ _)).1 hc
    exact ((algebraMap (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme.functionField
      (Scheme.residueField _ (genericPoint _))).charZero_iff (RingHom.injective _)).1 this
  have hab : Set.range (redι (clo z) ≫ M.b) ⊆ abLocus O.s.T.Z.t.G := by
    rintro _ ⟨q, rfl⟩
    by_contra hq
    have hne : Nonempty (I.f '' (closure {z} ∩ M.bd)) :=
      ⟨_, _, ⟨(range_redι (clo z)).le ⟨q, rfl⟩, hq⟩, rfl⟩
    obtain ⟨w⟩ := hne
    have : Nonempty (TopologicalSpace.IrreducibleCloseds (I.f '' (closure {z} ∩ M.bd))) :=
      ⟨⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have h₁ : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (I.f '' (closure {z} ∩ M.bd)) := Order.krullDim_nonneg
    have h₂ := (add_le_add_left h₁ 3).trans hG.2.1
    exact absurd h₂ (by decide)
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.PolLocal.exists_pull (redι (clo z) ≫ M.b) O.s.T.Z.t
  obtain ⟨hA, hP⟩ := isAbelianScheme_and_isPrincipalPol O.s.T.Z hab m
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)
  have := O.s.T.Z.t.semi.separated
  have := LieVB.isIso_omegaBase m.cart
  have iso : (Scheme.Modules.pullback (redι (clo z))).obj ((Scheme.Modules.pullback M.b).obj (LieVB.omega O.s.T.Z.t.G)) ≅
      IndefiniteRowSideFullHecke.ZeroSectionBase.hodge t.G := (Scheme.Modules.pullbackComp _ _).app _ ≪≫ @asIso _ _ _ _ (LieVB.omegaBase m.cart) this
  have hE := ((M.h R).isVB.pullback M.b).pullback (redι (clo z))
  obtain rfl : g = D.R.f * O.N := (IndefiniteRowSideFullHecke.ZeroSectionBase.isVB_hodge t.G hA g).rank_unique (hE.of_iso iso)
  have h0 := hV ℓ _ ⟨inferInstance, (topologicalKrullDim_red (clo z)).trans hG.1,
    GlobalTheory.VertProj.isProjOver_strHom_zmod _ _ _ _ M.ar _ (redι (clo z)) ℓ⟩ t.G _ hA hg ⟨_, hP⟩
  refine val_eq_zero h2.p4 M.ar _ M.F _ z hG.1 ℓ ?_
  rw [← IndefiniteRowSideFullHecke.ZeroSectionBase.degCh2_congr iso, IndefiniteRowSideFullHecke.ZeroSectionBase.degCh2] at h0
  rw [IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2_eq hE]
  push_cast at h0 ⊢
  linear_combination h0

end Main

end GlobalTheory.VertVanish

end
