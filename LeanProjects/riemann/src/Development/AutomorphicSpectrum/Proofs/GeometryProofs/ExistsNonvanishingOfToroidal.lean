import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsVanBdOfMemExtVanZ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfCoboundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmplePullbackPowerDivOfLocallyAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BorelWeilFlagModelDetInverseIsAmpleLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagNonempty
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRestrIsoTens
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec

theorem exists_sec_of_cls_add {X : Scheme.{0}} {L M N : LB X} (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB)
    (h : cls N hN = cls L hL + cls M hM) (s : L.Sec) (t : M.Sec) :
    ∃ u : N.Sec, nonzeroLocus u = nonzeroLocus t ⊓ nonzeroLocus s := by
  have h1 : (lbPow N 1).IsLB := isLB_lbPow hN 1
  have hD := LB.isLB_div hN hL
  have hiso : LBIso M (LB.div N L) := (cls_eq_iff hM hD).1 (by
    rw [cls_div hN hL hD, h]; abel)
  obtain ⟨u, hu⟩ := exists_sec_pow_nonzeroLocus_eq_inf hL hM hN hiso (secToPow s 1) (secToPow t 1)
  rw [nonzeroLocus_secToPow _ le_rfl, nonzeroLocus_secToPow _ le_rfl] at hu
  obtain ⟨w, hw⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hN h1
    ((cls_eq_iff hN h1).1 (by rw [cls_lbPow hN 1 h1, one_smul])) u
  exact ⟨w, hw.trans hu⟩

theorem eventually_sec_of_ample_add {X : Scheme.{0}} [IsLocallyNoetherian X] {P B T M : LB X} (hP : IsAmpleLB P)
    (hB : B.IsLB) (hT : T.IsLB) (e : cls T hT = cls P hP.isLB + cls B hB) (hM : M.IsLB) (b : B.Sec) {x : X}
    (hb : x ∈ nonzeroLocus b) :
    ∀ᶠ t : ℤ in Filter.atTop, ∀ (n : ℕ), (n : ℤ) = t → 1 ≤ n → ∀ (N : LB X) (hN : N.IsLB),
      cls N hN = cls M hM + n • cls T hT → ∃ s : N.Sec, x ∈ nonzeroLocus s := by
  refine (hP.eventually_exists_mem_nonzeroLocus_le hM (x := x) (U := ⊤) trivial).mono
    fun t ht n hn h1 N hN hc => ?_
  have hPn := isLB_lbPow hP.isLB n
  have hL := isLB_tens hM hPn
  obtain ⟨s, hs, -⟩ := ht _ hL (by
    rw [cls_tens hM hPn hL, cls_lbPow hP.isLB n hPn, ← hn, natCast_zsmul])
  have hBn := isLB_lbPow hB n
  obtain ⟨u, hu⟩ := exists_sec_of_cls_add hL hBn hN (by
    rw [cls_tens hM hPn hL, cls_lbPow hP.isLB n hPn, cls_lbPow hB n hBn, hc, e, smul_add, add_assoc]) s (secToPow b n)
  refine ⟨u, ?_⟩
  rw [hu, nonzeroLocus_secToPow _ h1]
  exact ⟨hb, hs⟩

end GlobalTheory.CompanionTheory.Ar.Rec

namespace GlobalTheory.CompanionTheory.Ar.Rec

theorem cls_nsmul_common {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ)
    (a : Λ) : cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) := by
  induction n with
  | zero =>
    have h := GlobalTheory.HSApp.cls_common_add C 0 0
    simp only [add_zero] at h
    simp only [zero_nsmul]
    exact left_eq_add.1 h
  | succ n ih => rw [succ_nsmul, GlobalTheory.HSApp.cls_common_add C, ih, succ_nsmul]

theorem val_ne_zero {F : Type} [Field F] {X : Scheme.{0}} (p : X ⟶ Sp F) {B : LB X} (θ : B.Sec) (z : Sp ℂ ⟶ X)
    (k : B.ι) (hk : ⊤ ≤ z ⁻¹ᵁ B.U k) (hz : ∀ s, z s ∈ nonzeroLocus θ) :
    H0.val z k le_top hk (H0.ofSec p ⊤ θ) ≠ 0 := by
  refine (H0.val_ofSec z k le_top hk θ).trans_ne ?_
  have h : ⊤ ≤ z ⁻¹ᵁ X.basicOpen (θ.f k) := fun s hs =>
    (X.mem_basicOpen _ _ (hk hs)).2 ((isUnit_ger_iff θ (hk hs)).2 (hz s))
  rw [← TangentOrigin.evalPt_res z (X.basicOpen_le _) hk h]
  exact ((X.toRingedSpace.isUnit_res_basicOpen (θ.f k)).map _).ne_zero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

theorem evR_ruleTop_ne_zero (T : TorFlag Xo c) (e : Ix Dw → ℤ) (θ : (T.X.F.LL e).Sec) (y : FrPt Xo c (CAt σ))
    (hy : ∀ s, T.X.ptY y s ∈ nonzeroLocus θ) (hO : ⊤ ≤ T.X.ptY y ⁻¹ᵁ flagOpen T.X) :
    evR Xo c (GlobalTheory.CompanionTheory.Ar.OntoDef.ruleTop T.X e (H0.ofSec (flagStr T.X) ⊤ θ)) y ≠ 0 := by
  classical
  have hr : _root_.IsReduced (CAt σ) := (inferInstance : _root_.IsReduced ℂ)
  have hsub : ∀ s s' : Sp (CAt σ), s = s' := Subsingleton.elim (α := PrimeSpectrum ℂ)
  let pt : Sp (CAt σ) := (IsLocalRing.closedPoint ℂ : PrimeSpectrum ℂ)
  obtain ⟨k, hk⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart (T.X.F.isLB_LL e) (T.X.ptY y pt)
  have hz : ⊤ ≤ T.X.ptY y ⁻¹ᵁ T.X.F.U k := fun s _ => by
    rw [hsub s pt]
    exact hk
  have hl := T.X.lies_ptY y
  obtain ⟨Q, hQ⟩ := T.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) hl.1 k hz
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl
  rw [GlobalTheory.CompanionTheory.Ar.OntoDef.evR_ruleTop _ hO hQ ht]
  let z : Sp (CAt σ) ⟶ T.X.YY := T.X.ptY y
  have h₁ := val_ne_zero (flagStr T.X) θ z k hz hy
  exact mul_ne_zero (M₀ := ℂ) (Units.ne_zero (M₀ := ℂ) (∏ ix, t ix ^ e ix : (CAt σ)ˣ)) h₁

end GlobalTheory.CompanionTheory.Ar.Rec

namespace GlobalTheory.CompanionTheory.Ar.Rec

theorem exists_nonvanishing_of_toroidal : GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), 1 ≤ Dw.p + Dw.q → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ y : FrPt Xo c (CAt σ), ∃ (a' : (E →+* ℂ) × ℕ → ℕ) (n' : ℕ), Dom a' n' ∧ ∃ g ∈ sec Xo c a' n', ∃ f ∈ sec Xo c (a + a') (n + n'), evR Xo c g y ≠ 0 ∧ evR Xo c f y ≠ 0 := by
  intro hS hK E _ _ _ H Dw l Xo c σ hr a n hD y
  classical
  obtain ⟨φ, Y, BD, d, k, -, -, -, -, -, a₁, a₂, a₃, a₄, -, -, hY, hA⟩ := hK.exists_model hS hr Xo c
  obtain ⟨fl⟩ := GlobalTheory.T.nonempty_integralFlagModel_of_smooth_coefficientField E H Dw l Xo c Y a₁ (GlobalTheory.CompHS.TorFlagEx.pushInvertible_of_hasTheta Y
    (GlobalTheory.ThetaNormal.hasTheta_of_smooth E H Dw hr l Xo c Y a₁))
  let TF : TorFlag Xo c := ⟨Y, a₁, a₂, a₃, fl⟩
  have : IsProper Y.s := projProper _ _ _ Y.proj
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have : IsProper TF.X.π := TF.X.proper
  have : CompactSpace TF.X.YY := QuasiCompact.compactSpace_of_compactSpace TF.X.π
  have : QuasiSeparatedSpace TF.X.YY := quasiSeparatedSpace_of_quasiSeparated (TF.X.π ≫ Y.s)
  have : IsLocallyNoetherian TF.X.YY := LocallyOfFiniteType.isLocallyNoetherian (TF.X.π ≫ Y.s)
  let e₀ : Ix Dw → ℤ := fun ix => ix.elim 0 fun p => (Dw.mult p.1 : ℤ) - ((p.2 : ℕ) : ℤ)
  let w : Ix Dw → ℤ := fun ix => ix.elim 0 fun _ => 1
  have C := commonLL TF.X
  let Lc : (Ix Dw → ℤ) → Pic TF.X.YY := fun e => cls (TF.X.F.LL e) (TF.X.F.isLB_LL e)
  have hadd : ∀ a b, Lc (a + b) = Lc a + Lc b := fun a b => GlobalTheory.HSApp.cls_common_add C a b
  have hnsm : ∀ (n : ℕ) a, Lc (n • a) = n • Lc a := fun n a => cls_nsmul_common C n a
  have hneg : ∀ a, Lc (-a) = - Lc a := fun a => by
    have h0 : Lc 0 = 0 := by
      have := hadd 0 0
      simpa using this
    have := hadd a (-a)
    rw [add_neg_cancel, h0] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hw : Lc w = CechPic.pull TF.X.π (cls _ hY) := by
    have e₁ : cls _ (TF.X.F.isLB_detOm) = cls _ (TF.X.isLB_Llam (FlagMod.mu0 Dw)) :=
      (cls_eq_iff _ _).2 (FlagHodge.lbIso_detOm_Llam TF.X)
    have e₂ := (cls_eq_iff TF.X.F.isLB_detOm (LB.isLB_pull hY _)).2 (TF.X.F.detOm_iso_pull hY)
    rw [cls_pull hY] at e₂
    rw [← e₂, e₁]
    have e₃ : AllWt.exOf Dw (FlagMod.mu0 Dw) 0 = w := FlagMod.unitaryWeightExponentVector_signatureWeightMuZero
    show cls (TF.X.F.LL w) _ = cls (TF.X.F.LL (AllWt.exOf Dw (FlagMod.mu0 Dw) 0)) _
    simp only [e₃]
  obtain ⟨n₀, hn⟩ := GlobalTheory.T.isAmple_pullbackPower_div_of_locally_ample TF.X.π _ hA (TF.X.F.LL (-e₀)) (TF.X.F.LL e₀) (TF.X.F.isLB_LL _) (TF.X.F.isLB_LL _)
    (by have := hneg e₀; show Lc e₀ = - Lc (-e₀); rw [this, neg_neg])
    (fun z => GlobalTheory.T.borelWeil_flagModel_detInverse_isAmple_local fl z)
  let m : ℕ := max n₀ 1
  have hm : 1 ≤ m := le_max_right _ _
  have hP := hn m (le_max_left _ _)
  have hBd : (BD.lb.pull TF.X.π).IsLB := LB.isLB_pull BD.isLB_lb _
  have hB := isLB_lbPow hBd m
  let τ : Ix Dw → ℤ := (m * k) • w + e₀
  have hcl : Lc τ = cls _ hP.isLB + cls _ hB := by
    have hAπ := LB.isLB_pull hA.isLB TF.X.π
    have hP1 := isLB_lbPow hAπ m
    have hΩk := isLB_lbPow hY k
    have hBDd := isLB_dual BD.isLB_lb
    have hcA : cls _ hA.isLB = k • cls _ hY - cls _ BD.isLB_lb := by
      refine (cls_tens hΩk hBDd hA.isLB).trans ?_
      rw [cls_lbPow hY k hΩk, cls_dual BD.isLB_lb hBDd, sub_eq_add_neg]
    rw [cls_div hP1 (TF.X.F.isLB_LL _) hP.isLB, cls_lbPow hAπ m hP1, cls_pull hA.isLB _ hAπ, cls_lbPow hBd m hB,
      cls_pull BD.isLB_lb _ hBd, hcA, map_sub, map_nsmul]
    show Lc τ = _ - Lc (-e₀) + _
    rw [hadd, hnsm, hw, hneg, mul_smul]
    rw [smul_sub, sub_neg_eq_add]
    abel
  let z : Sp (CAt σ) ⟶ TF.X.YY := TF.X.ptY y
  have hO : ⊤ ≤ TF.X.ptY y ⁻¹ᵁ flagOpen TF.X := by
    have := FlagMod.le_preimage_map (z := TF.X.pt y) TF.X.inc (top_le_inc TF.X) le_top
    rwa [TF.X.pt_inc] at this
  have hsub : ∀ s s' : Sp (CAt σ), s = s' := Subsingleton.elim (α := PrimeSpectrum ℂ)
  let pt : Sp (CAt σ) := (IsLocalRing.closedPoint ℂ : PrimeSpectrum ℂ)
  have hb : z pt ∈ nonzeroLocus (secToPow (lbSecPull BD.lb BD.canonical TF.X.π) m) := by
    rw [nonzeroLocus_secToPow _ hm, GlobalTheory.HodgeDominates.nonzeroLocus_lbSecPull]
    show TF.X.π (z pt) ∈ nonzeroLocus BD.canonical
    rw [← SetLike.mem_coe, BD.coe_nonzeroLocus_canonical]
    refine fun h => a₄ _ h ?_
    rw [← LogKS.coe_interior Y]
    exact hO (Set.mem_univ pt)
  let eA : Ix Dw → ℤ := fun i => (ex Dw a n i : ℤ)
  have G₁ := eventually_sec_of_ample_add hP hB (TF.X.F.isLB_LL τ) hcl (TF.X.F.isLB_LL 0) _ hb
  have G₂ := eventually_sec_of_ample_add hP hB (TF.X.F.isLB_LL τ) hcl (TF.X.F.isLB_LL eA) _ hb
  obtain ⟨t, ⟨g₁, g₂⟩, ht⟩ := ((G₁.and G₂).and (Filter.eventually_gt_atTop 0)).exists
  obtain ⟨u, rfl⟩ := Int.eq_ofNat_of_zero_le ht.le
  have hu : 1 ≤ u := by omega
  let a' : (E →+* ℂ) × ℕ → ℕ := fun q => u * (m * k + (Dw.mult q.1 - q.2))
  have hDom : Dom a' 0 := ⟨fun τ i j hij => Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.sub_le_sub_left hij _) _),
    ⟨0, rfl⟩⟩
  have hE₁ : (fun i => (ex Dw a' 0 i : ℤ)) = 0 + u • τ := by
    funext i
    rcases i with _ | ⟨ρ, i⟩
    · simp [ex, τ, w, e₀]
    · have hi : ((i : ℕ)) ≤ Dw.mult ρ := i.2.le
      show ((u * (m * k + (Dw.mult ρ - (i : ℕ))) : ℕ) : ℤ) =
        0 + u • ((m * k) • (1 : ℤ) + ((Dw.mult ρ : ℤ) - ((i : ℕ) : ℤ)))
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hi, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
      ring
  have hE₂ : (fun i => (ex Dw (a + a') (n + 0) i : ℤ)) = eA + u • τ := by
    rw [← hE₁.trans (zero_add _), ex_add]
    funext i
    simp [eA]
  have key : ∀ e f : Ix Dw → ℤ, e = f + u • τ → Lc e = Lc f + u • Lc τ := fun e f h => by
    rw [h, hadd, hnsm]
  obtain ⟨s₁, hs₁⟩ := g₁ u rfl hu (TF.X.F.LL _) (TF.X.F.isLB_LL _) (key _ _ hE₁)
  obtain ⟨s₂, hs₂⟩ := g₂ u rfl hu (TF.X.F.LL _) (TF.X.F.isLB_LL _) (key _ _ hE₂)
  refine ⟨a', 0, hDom, _, (GlobalTheory.AllWt.secZ_nat Xo c a' 0).le (GlobalTheory.CompanionTheory.Ar.OntoDef.ruleTop_mem_secZ (H0.ofSec (flagStr TF.X) ⊤ s₁)),
    _, (GlobalTheory.AllWt.secZ_nat Xo c (a + a') (n + 0)).le (GlobalTheory.CompanionTheory.Ar.OntoDef.ruleTop_mem_secZ (H0.ofSec (flagStr TF.X) ⊤ s₂)),
    evR_ruleTop_ne_zero TF _ s₁ y (fun s => by rw [hsub s pt]; exact hs₁) hO,
    evR_ruleTop_ne_zero TF _ s₂ y (fun s => by rw [hsub s pt]; exact hs₂) hO⟩

end GlobalTheory.CompanionTheory.Ar.Rec
