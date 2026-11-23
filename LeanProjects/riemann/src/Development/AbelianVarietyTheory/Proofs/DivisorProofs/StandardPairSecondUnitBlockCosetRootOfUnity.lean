import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleLevelFixesVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.BotCosetValue

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle Formalism.L2.DIV GlobalTheory.StdFrames

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

theorem cpt_toEAf (Q : Pl D.host.E) (z : Formalism.L2.Theta.AE D) :
    cpt Q (toEAf D z) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D z) Q := by
  have h : toAd D (toEAf D z) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => exact (toAd_spec D x a.2).trans ((mul_comm _ _).trans (GlobalTheory.LFun.toFinAd_tmul a.2 x).symm)
    | add a b ha hb => simp only [RingHom.map_add, RingEquiv.map_add, ha, hb]
  exact congrArg (fun s : FiniteAdeleRing (𝓞 D.host.E) D.host.E => s Q) h

theorem cpt_locIdele (Q w : Pl D.host.E) (y : (w.adicCompletion D.host.E)ˣ) :
    cpt Q (toEAf D (GlobalTheory.LFun.locIdele D.host.F w y : (Formalism.L2.Theta.AE D)ˣ)) = Neutral.B1.finiteSingle D.host.E w y Q := by
  rw [cpt_toEAf]
  exact congrArg (fun s : FiniteAdeleRing (𝓞 D.host.E) D.host.E => s Q) (GlobalTheory.LFun.finTens_locIdele w y)

theorem hom_prod {R R' ι : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : ι → R) (s : Finset ι) :
    f (∏ i ∈ s, p i) = ∏ i ∈ s, f (p i) := map_prod f p s

theorem cpt_idem {e : Formalism.L2.Theta.AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (Q : Pl D.host.E) :
    cpt Q (toEAf D e) = if Q ∈ P then 1 else 0 := by
  obtain ⟨⟨es, hes, hs⟩, -⟩ := he
  rw [hs, StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.hom_sum, StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.hom_sum]
  split_ifs with h
  · rw [Finset.sum_eq_single Q (fun w hw hne => (cpt_of_isIdemAt (hes w hw)).2 Q hne.symm) (fun h' => absurd h h'),
      (cpt_of_isIdemAt (hes Q h)).1]
  · exact Finset.sum_eq_zero fun w hw => (cpt_of_isIdemAt (hes w hw)).2 Q fun h' => h (h' ▸ hw)

theorem exists_one_add {e : Formalism.L2.Theta.AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {c : Pl D.host.E → ℕ}
    (hc : ∀ w ∈ P, 1 ≤ c w) {ν : (Formalism.L2.Theta.AE D)ˣ →* Circle} {νH : Formalism.L2.Host.HChar D.host.E} (hν : ChrEq ν νH)
    (hl : ∀ w ∈ P, νH.LevelLe w (c w)) {t : Lev.EAf D} (ht : GlobalTheory.FrameIdeal.InId (F := D.host.F) (modul P c) t)
    (het : toEAf D e * t = t) :
    ∃ z : (Formalism.L2.Theta.AE D)ˣ, infPart D (z : Formalism.L2.Theta.AE D) = 1 ∧ toEAf D (z : Formalism.L2.Theta.AE D) = 1 + t ∧
      toEAf D ((z⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) ∈ OO ∧ ν z = 1 := by
  obtain ⟨s, hs, rfl⟩ := ht
  have hv : ∀ w ∈ P, Valued.v (cpt (D := D) w s.1) ≤ WithZero.exp (-(c w : ℤ)) := fun w hw =>
    GlobalTheory.FunObj.Comparison₂.v_le_of_mem_idS (Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w => w.asIdeal ^ c w) hw)) hs
  have h0 : ∀ w, w ∉ P → cpt (D := D) w s.1 = 0 := fun w hw => by
    rw [← het, RingHom.map_mul, cpt_idem he, if_neg hw, zero_mul]
  have h1 : ∀ w, Valued.v (1 + cpt (D := D) w s.1) = 1 := fun w => by
    by_cases hw : w ∈ P
    · refine Valuation.map_one_add_of_lt _ ((hv w hw).trans_lt ?_)
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      have := hc w hw
      omega
    · rw [h0 w hw, add_zero, map_one]
  let u : ∀ w : Pl D.host.E, (w.adicCompletion D.host.E)ˣ := fun w => Units.mk0 (1 + cpt (D := D) w s.1) (by
    rw [← Valuation.ne_zero_iff (Valued.v : Valuation (w.adicCompletion D.host.E) _), h1]
    exact one_ne_zero)
  refine ⟨∏ w ∈ P, GlobalTheory.LFun.locIdele D.host.F w (u w), ?_, cpt_ext fun Q => ?_, ?_, ?_⟩
  · rw [Units.coe_prod, hom_prod]
    exact Finset.prod_eq_one fun w _ => GlobalTheory.LFun.infTens_locIdele w (u w)
  · rw [Units.coe_prod, hom_prod, hom_prod, Finset.prod_congr rfl fun w _ => cpt_locIdele Q w (u w), RingHom.map_add,
      RingHom.map_one]
    by_cases hQ : Q ∈ P
    · rw [Finset.prod_eq_single Q (fun w _ hne => GlobalTheory.LFun.finSingle_ne hne.symm _) (fun h' => absurd hQ h'),
        GlobalTheory.LFun.finSingle_self]
      rfl
    · rw [h0 Q hQ, add_zero]
      exact Finset.prod_eq_one fun w hw => GlobalTheory.LFun.finSingle_ne (fun h' : Q = w => hQ (h' ▸ hw)) _
  · rw [← Finset.prod_inv_distrib, Units.coe_prod, hom_prod]
    refine Subring.prod_mem _ fun w _ => (mem_OA_iff _).2 fun Q => ?_
    rw [← map_inv, cpt_locIdele]
    by_cases hQ : Q = w
    · subst hQ
      rw [GlobalTheory.LFun.finSingle_self, HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀]
      exact (congrArg (·⁻¹) (h1 Q)).le.trans inv_one.le
    · rw [GlobalTheory.LFun.finSingle_ne hQ]
      exact one_mem _
  · rw [map_prod]
    refine Finset.prod_eq_one fun w hw => ?_
    have h2 := hl w hw (u w) (h1 w) (by
      change Valued.v (1 + cpt (D := D) w s.1 - 1) ≤ _
      rw [add_sub_cancel_left]
      exact hv w hw)
    rw [← GlobalTheory.LFun.locChar_eq_of_chrEq hν] at h2
    exact Circle.ext (congrArg Units.val h2)

theorem idem_mul_mem {e : Formalism.L2.Theta.AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {x : D.host.E}
    (hx : ∀ w ∈ P, w.valuation D.host.E x = 1) : toEAf D e * eToEAf D x ∈ OO := by
  refine (mem_OA_iff _).2 fun Q => ?_
  rw [RingHom.map_mul, cpt_idem he]
  split_ifs with h
  · rw [one_mul, show cpt (D := D) Q (eToEAf D x) = _ from GlobalTheory.FunObj.Comparison₂.cpt_tmul Q x,
      HeightOneSpectrum.mem_adicCompletionIntegers]
    exact ((GlobalTheory.LFun.valued_alg Q x).trans (hx Q h)).le
  · rw [zero_mul]
    exact zero_mem _

theorem valuation_xi_zero_eq_one (hcc : D.host.ccK = ⊤) {w : Pl D.host.E} (hw : ((D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) :
    w.valuation D.host.E D.host.xi0 = 1 := by
  have hd : w.valuation D.host.E (D.host.d : D.host.E) = 1 := by
    have := (w.valuation_eq_one_iff_notMem (K := D.host.E) (r := (D.host.d : 𝓞 D.host.E))).2 hw
    simpa using this
  have hs : w.valuation D.host.E D.host.sqrtMinusD = 1 := by
    have := congrArg (w.valuation D.host.E) D.host.sqrtMinusD_sq
    rw [map_pow, Valuation.map_neg, hd] at this
    exact (pow_eq_one_iff_left two_ne_zero).1 this
  unfold Formalism.BasicNotions.Host.xi0
  rw [hcc, Ideal.absNorm_top, Nat.cast_one, one_mul, map_div₀, Valuation.map_neg, map_one, hs, div_one]

theorem map_conj_le (I : Ideal (𝓞 D.host.E)) : (D.host.conj • I).map (GlobalTheory.FrameIdeal.cO D) ≤ I := by
  rw [Ideal.pointwise_smul_def, Ideal.map_map, Ideal.map_le_iff_le_comap]
  intro b hb
  have e : ((GlobalTheory.FrameIdeal.cO D).comp (MulSemiringAction.toRingHom _ _ D.host.conj)) b = b := by
    apply RingOfIntegers.ext
    change star (D.host.conj (b : D.host.E)) = b
    rw [← Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D]
    exact star_star _
  rw [Ideal.mem_comap, e]
  exact hb

theorem det_sub_mem {R : Type} [CommRing R] (A : Subring R) (J : Ideal A) {k : ℕ} {M N : Matrix (Fin k) (Fin k) R}
    (hN : ∀ i j, N i j ∈ A) (h : ∀ i j, ∃ s ∈ J, (s : R) = M i j - N i j) : ∃ s ∈ J, (s : R) = M.det - N.det := by
  choose s hs e using h
  let N' : Matrix (Fin k) (Fin k) A := fun i j => ⟨N i j, hN i j⟩
  let M' : Matrix (Fin k) (Fin k) A := fun i j => N' i j + s i j
  have e1 : N = A.subtype.mapMatrix N' := rfl
  have e2 : M = A.subtype.mapMatrix M' := by
    ext i j
    change M i j = N i j + s i j
    rw [e, add_sub_cancel]
  have e3 : (Ideal.Quotient.mk J).mapMatrix M' = (Ideal.Quotient.mk J).mapMatrix N' := by
    ext i j
    change Ideal.Quotient.mk J (N' i j + s i j) = Ideal.Quotient.mk J (N' i j)
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 (hs i j), add_zero]
  refine ⟨M'.det - N'.det, Ideal.Quotient.eq.1 (by rw [RingHom.map_det, RingHom.map_det, e3]), ?_⟩
  rw [e1, e2, ← RingHom.map_det, ← RingHom.map_det]
  rfl

theorem dualCoord_eq {S T : HSp D} (hS : S.gram = 1) (hT : T.gram = 1) (β : GL (Fin S.rank) (Lev.EAf D)) (y : WO S T) (i j) :
    dualCoord S T β 1 y i j = ∑ l, (β⁻¹).1 i l * (eToEAf D D.host.xi0 * toEAf D (cA D (y j l))) := by
  rw [GlobalTheory.CompanionTheory.StdSndTheta.dualCoord_apply]
  unfold frMapAdj
  rw [hS, hT, inv_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul,
    Matrix.mul_one, Units.val_one, Matrix.mul_one, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => mul_left_comm _ _ _

theorem cA_cA (z : Formalism.L2.Theta.AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]
  | add a b ha hb => simp only [RingHom.map_add, ha, hb]

theorem inId_of {I : Ideal (𝓞 D.host.E)} {z : Lev.EAf D} (h : GlobalTheory.FrameIdeal.InId (F := D.host.F) I z) : InId I z := by
  obtain ⟨s, hs, rfl⟩ := h
  exact ⟨s.2, hs⟩

theorem adj_sub_mem {S T : HSp D} {e : Formalism.L2.Theta.AE D} {I : Ideal (𝓞 D.host.E)} {o : ℕ} {y : WO S T} {j : Fin T.rank}
    {l : Fin S.rank} (h : InId (D.host.conj • I) (toEAf D (y j l - unitPt S T (cA D e) o j l))) :
    GlobalTheory.FrameIdeal.InId (F := D.host.F) I (toEAf D (cA D (y j l)) - if j.1 = o + l.1 then toEAf D e else 0) := by
  obtain ⟨h1, h2⟩ := h
  have h3 := GlobalTheory.FrameIdeal.inId_sigR (map_conj_le I) ⟨_, h2, rfl⟩
  have h4 : Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (toEAf D (y j l - unitPt S T (cA D e) o j l)) =
      toEAf D (cA D (y j l)) - if j.1 = o + l.1 then toEAf D e else 0 := by
    refine (GlobalTheory.AdelicLatMove.toEAf_cA _).symm.trans ?_
    rw [RingHom.map_sub, RingHom.map_sub]
    unfold unitPt
    split_ifs
    · rw [cA_cA]
    · rw [RingHom.map_zero, RingHom.map_zero]
  exact h4 ▸ h3

theorem ring_unit {R : Type} [CommRing R] {ε ξ ξ' : R} (hε : ε * ε = ε) (hξ : ξ * ξ' = 1) {k : ℕ} (β : GL (Fin k) R) :
    (1 - ε + ε * ((ε * ξ) • (β⁻¹).1).det) * (1 - ε + ε * ((ε * ξ') • β.1).det) = 1 := by
  have h1 : ε * ξ' * (ε * ξ) = ε := by linear_combination ξ * ξ' * hε + ε * hξ
  rw [GlobalTheory.BotFinLevel.ring_mul hε, ← Matrix.det_mul, Matrix.smul_mul, Matrix.mul_smul, Units.inv_mul, smul_smul, mul_comm (ε * ξ),
    h1, Matrix.det_smul, Matrix.det_one, mul_one, ← pow_succ', IsIdempotentElem.pow_succ_eq _ hε, sub_add_cancel]

theorem ring_sub {R ι : Type} [CommRing R] [Fintype ι] {ε ξ : R} (B u δ : ι → R) (hu : ∀ l, ε * u l = u l) :
    ∑ l, B l * (ξ * u l) - ∑ l, B l * (ε * ξ * δ l) = ∑ l, B l * (ε * ξ) * (u l - δ l) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun l _ => by linear_combination (-(B l * ξ)) * hu l

theorem ring_fin {R : Type} [CommRing R] {ε d d' v : R} (hv : (1 - ε + ε * d) * v = 1) :
    (1 - ε + ε * d) * (1 + ε * v * (d' - d)) = 1 - ε + ε * d' := by
  linear_combination ε * (d' - d) * hv

theorem unitChar_eq (ν : (Formalism.L2.Theta.AE D)ˣ →* Circle) {e : Formalism.L2.Theta.AE D} {k : ℕ}
    {N : Matrix (Fin k) (Fin k) (Lev.EAf D)} {x : (Formalism.L2.Theta.AE D)ˣ} (hx : IsUnitDet e N x) :
    unitChar ν e N = (((ν x)⁻¹ : Circle) : ℂ) := by
  have h : ∃ x, IsUnitDet e N x := ⟨x, hx⟩
  unfold unitChar
  rw [dif_pos h, GlobalTheory.BotFinLevel.isUnitDet_unique h.choose_spec hx]

theorem unitChar_congr {e : Formalism.L2.Theta.AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {c : Pl D.host.E → ℕ}
    (hc : ∀ w ∈ P, 1 ≤ c w) {ν : (Formalism.L2.Theta.AE D)ˣ →* Circle} {νH : Formalism.L2.Host.HChar D.host.E} (hν : ChrEq ν νH)
    (hl : ∀ w ∈ P, νH.LevelLe w (c w)) {k : ℕ} {M N : Matrix (Fin k) (Fin k) (Lev.EAf D)} (hN : IsIntM N)
    (h : ∀ i j, GlobalTheory.FrameIdeal.InId (F := D.host.F) (modul P c) (M i j - N i j)) {x : (Formalism.L2.Theta.AE D)ˣ}
    (hx : IsUnitDet e N x) : unitChar ν e M = (((ν x)⁻¹ : Circle) : ℂ) := by
  have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hee : toEAf D e * toEAf D e = toEAf D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have hd : GlobalTheory.FrameIdeal.InId (F := D.host.F) (modul P c) (M.det - N.det) := det_sub_mem _ _ hN h
  obtain ⟨z, z1, z2, z3, z4⟩ := exists_one_add he hc hν hl (GlobalTheory.FrameIdeal.inId_mul (mul_mem hE hx.2.2) hd)
    (by rw [← mul_assoc, ← mul_assoc, hee])
  have hv : (1 - toEAf D e + toEAf D e * N.det) * toEAf D ((x⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = 1 := by
    rw [← hx.2.1, ← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
  have hM : IsUnitDet e M (x * z) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Units.val_mul, RingHom.map_mul, hx.1, z1, one_mul]
    · rw [Units.val_mul, RingHom.map_mul, hx.2.1, z2]
      exact ring_fin hv
    · rw [mul_inv, Units.val_mul, RingHom.map_mul]
      exact mul_mem hx.2.2 z3
  rw [unitChar_eq ν hM, map_mul, z4, mul_one]

theorem stdSnd_coset_value : ∀ {D : D7} (S T : HSp D), S.gram = 1 → T.gram = 1 → D.host.ccK = ⊤ →
    ∀ (βS : GL (Fin S.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (Formalism.L2.Col.stdLat D.host.E S.rank) →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), GoodIdem e P →
    ∀ o : ℕ, o + S.rank = T.rank → (∀ w ∈ P, 1 ≤ c w) →
    ∀ (ν : (Formalism.L2.Theta.AE D)ˣ →* Circle) (νH : Formalism.L2.Host.HChar D.host.E), ChrEq ν νH → (∀ w ∈ P, GlobalTheory.CMVal.ExpAt νH w (c w)) →
    ∃ ζ : ℂ, IsRootOne ζ ∧ ∀ y : WO S T, cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) y ≠ 0 →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e (modul P c) o S T βS 1 y = ζ := by
  intro D S T hS hT hcc β hβ e P c ⟨he, hP⟩ o ho hc ν νH hν hexp
  have hl : ∀ w ∈ P, νH.LevelLe w (c w) := fun w hw => (hexp w hw _).2 le_rfl
  have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hee : toEAf D e * toEAf D e = toEAf D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have hξ : ∀ w ∈ P, w.valuation D.host.E D.host.xi0 = 1 := fun w hw => valuation_xi_zero_eq_one hcc fun h => hP w hw (by
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ h)
  have ha := idem_mul_mem he hξ
  have ha' := idem_mul_mem (x := D.host.xi0⁻¹) he fun w hw => by rw [map_inv₀, hξ w hw, inv_one]
  have hξξ : eToEAf D D.host.xi0 * eToEAf D D.host.xi0⁻¹ = 1 := by
    rw [← RingHom.map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one]
  have hB := (GlobalTheory.BotClassDict.mem_range_intGL β).1 (GlobalTheory.BotClassDict.frame_mem_range hβ)
  have hN : IsIntM ((toEAf D e * eToEAf D D.host.xi0) • (β⁻¹).1) := fun i j => mul_mem ha (hB i j).2
  have hN' : IsIntM ((toEAf D e * eToEAf D D.host.xi0⁻¹) • β.1) := fun i j => mul_mem ha' (hB i j).1
  obtain ⟨x, x1, x2, x3⟩ := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.exists_unit (ring_unit hee hξξ β)
  have x4 : toEAf D ((x⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [x3]
    exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE (GlobalTheory.BotFinLevel.det_mem hN'))
  have hx : IsUnitDet e ((toEAf D e * eToEAf D D.host.xi0) • (β⁻¹).1) x := ⟨x1, x2, x4⟩
  refine ⟨(((ν x)⁻¹ : Circle) : ℂ), ?_, fun y hy => ?_⟩
  · obtain ⟨-, -, -, m, hm, hord⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν.1.1
    have hpow := hord x ⟨x1, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (by
      rw [x2]
      exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE (GlobalTheory.BotFinLevel.det_mem hN))),
      GlobalTheory.PlaceDatum.finPart_mem_of_toEAf x4⟩
    refine ⟨m, hm, ?_⟩
    have e1 : (((ν x)⁻¹ : Circle) : ℂ) ^ m = Circle.coeHom (((ν x) ^ m)⁻¹) := by
      rw [← inv_pow, map_pow]; rfl
    rw [e1, hpow, inv_one, map_one]
  · obtain ⟨hh, hy⟩ : IsHalf (cA D e) y ∧ ∀ i j, InId (D.host.conj • modul P c)
        (toEAf D (y i j - unitPt S T (cA D e) o i j)) := by
      by_contra h
      exact hy (if_neg h)
    have hu : ∀ j l, toEAf D e * toEAf D (cA D (y j l)) = toEAf D (cA D (y j l)) := fun j l => by
      rw [← RingHom.map_mul]
      conv_rhs => rw [← hh j l, RingHom.map_mul, cA_cA]
    have key : ∀ i j, GlobalTheory.FrameIdeal.InId (F := D.host.F) (modul P c) (dualCoord S T β 1 y i j -
        ∑ l, (β⁻¹).1 i l * (toEAf D e * eToEAf D D.host.xi0 * if j.1 = o + l.1 then toEAf D e else 0)) := fun i j => by
      rw [dualCoord_eq hS hT, ring_sub _ _ _ (hu j)]
      exact GlobalTheory.FrameIdeal.inId_sum _ fun l => GlobalTheory.FrameIdeal.inId_mul (mul_mem (hB i l).2 ha) (adj_sub_mem (hy j l))
    unfold stdSnd
    refine (if_pos ⟨hh, fun i j => ?_, fun i j hj => ?_⟩).trans ?_
    · refine unitChar_congr he hc hν hl hN (fun i j => ?_) hx
      have hj : o + j.1 < T.rank := by have := j.2; omega
      have h1 := key i ⟨o + j.1, hj⟩
      rw [Finset.sum_eq_single j (fun l _ hne => by
        rw [if_neg fun h => hne (Fin.ext (Nat.add_left_cancel h).symm), mul_zero, mul_zero])
        (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, mul_right_comm, hee, mul_comm] at h1
      unfold rightBlock
      rw [dif_pos hj]
      exact h1
    · have h1 := GlobalTheory.FrameIdeal.inId_int (key i j)
      refine (sub_add_cancel (dualCoord S T β 1 y i j) _) ▸ add_mem h1 (Subring.sum_mem _ fun l _ =>
        mul_mem (hB i l).2 (mul_mem ha ?_))
      split_ifs
      · exact hE
      · exact zero_mem _
    · have h1 := key i j
      rw [Finset.sum_eq_zero fun l _ => by rw [if_neg (by omega), mul_zero, mul_zero], sub_zero] at h1
      exact inId_of h1

end GlobalTheory.BotCosetValue

end
