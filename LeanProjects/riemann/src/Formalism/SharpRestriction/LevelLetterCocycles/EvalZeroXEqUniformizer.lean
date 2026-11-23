import Formalism.SharpRestriction.LevelLetterCocycles.FinLev
import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower
import Formalism.SharpRestriction.LevelLetterCocycles.EqZeroOfPowDvd

noncomputable section

open Classical PowerSeries

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def WF {O : Type} [CommRing O] (p : O) (F : PowerSeries O) (N : ℕ) : Prop :=
  ∃ g h : PowerSeries O, IsUnit (constantCoeff g) ∧ F = g * X ^ N + C p * h

theorem WF.mul {O : Type} [CommRing O] {p : O} {F F' : PowerSeries O} {N N' : ℕ} (h1 : WF p F N)
    (h2 : WF p F' N') : WF p (F * F') (N + N') := by
  obtain ⟨g, h, hg, rfl⟩ := h1
  obtain ⟨g', h', hg', rfl⟩ := h2
  refine ⟨g * g', g * X ^ N * h' + h * (g' * X ^ N' + C p * h'), by rw [map_mul]; exact hg.mul hg', ?_⟩
  rw [pow_add]; ring

theorem WF.one {O : Type} [CommRing O] (p : O) : WF p 1 0 :=
  ⟨1, 0, by simp, by simp⟩

theorem WF.X {O : Type} [CommRing O] (p : O) : WF p X 1 :=
  ⟨1, 0, by simp, by simp⟩

theorem WF.pow {O : Type} [CommRing O] {p : O} {F : PowerSeries O} {N : ℕ} (h : WF p F N) (k : ℕ) :
    WF p (F ^ k) (N * k) := by
  induction k with
  | zero => simpa using WF.one p
  | succ k ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul h

theorem WF.prod {O : Type} [CommRing O] {p : O} (F : ℕ → PowerSeries O) (N : ℕ → ℕ)
    (h : ∀ t, WF p (F t) (N t)) (e : ℕ) :
    WF p (∏ t ∈ Finset.range e, F t) (∑ t ∈ Finset.range e, N t) := by
  induction e with
  | zero => simpa using WF.one p
  | succ e ih => rw [Finset.prod_range_succ, Finset.sum_range_succ]; exact ih.mul (h e)

section Idem

variable {A : Type} [CommRing A] {E : A}

theorem idem_mul (_hE : E * E = E) {x y : A} (h : x * E = y * E) (z : A) : (z * x) * E = (z * y) * E := by
  rw [mul_assoc, h, ← mul_assoc]

theorem idem_pow (hE : E * E = E) {x y : A} (h : x * E = y * E) (k : ℕ) : x ^ k * E = y ^ k * E := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc x ^ (k + 1) * E = (x ^ k * E) * (x * E) := by rw [pow_succ]; linear_combination (-(x ^ k * x)) * hE
      _ = (y ^ k * E) * (y * E) := by rw [ih, h]
      _ = y ^ (k + 1) * E := by rw [pow_succ]; linear_combination (y ^ k * y) * hE

theorem idem_prod (hE : E * E = E) (x y : ℕ → A) (h : ∀ t, x t * E = y t * E) (e : ℕ) :
    (∏ t ∈ Finset.range e, x t) * E = (∏ t ∈ Finset.range e, y t) * E := by
  induction e with
  | zero => simp
  | succ e ih =>
    calc (∏ t ∈ Finset.range (e + 1), x t) * E = ((∏ t ∈ Finset.range e, x t) * E) * (x e * E) := by
          rw [Finset.prod_range_succ]; linear_combination (-((∏ t ∈ Finset.range e, x t) * x e)) * hE
      _ = ((∏ t ∈ Finset.range e, y t) * E) * (y e * E) := by rw [ih, h]
      _ = (∏ t ∈ Finset.range (e + 1), y t) * E := by
          rw [Finset.prod_range_succ]; linear_combination ((∏ t ∈ Finset.range e, y t) * y e) * hE

end Idem

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem evalZero_X_eq_uniformizer (W : LocWach PD LL O v n) (hR : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.Ring9 W) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W X = W.π₀ := by
  funext j
  rw [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_apply, subst_X (Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.hasSubst W hR)]
  rfl

theorem ps_letter [IsDomain O] (W : LocWach PD LL O v n) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hp0 : ((PD.p : ℕ) : O) ≠ 0) (a : ZMod n) (t : ℕ) :
    ∃ F : PowerSeries O, WF ((PD.p : ℕ) : O) F (PD.p ^ t) ∧
      Formalism.MainNotions.ArcLiftingSetup.ps W t * letE a = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W F * letE a := by
  obtain ⟨v, hvΔ, hvu, r, hr⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.modp hR hp0 t
  have hps : Formalism.MainNotions.ArcLiftingSetup.ps W t = v * W.π₀ ^ (PD.p ^ t) + ((PD.p : ℕ) : LetA O n) * (r + 1) := by
    have := Formalism.MainNotions.UnusedSlot80.ToolsR.pS_sub (W := W) t
    rw [hr] at this
    change Formalism.MainNotions.WachCoordinates.pS W t = _
    linear_combination this
  have hpsΔ : Formalism.MainNotions.ArcLiftingSetup.ps W t ∈ W.AΔ :=
    Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_AΔ t (Formalism.MainNotions.UnusedSlot80.ToolsR.qP_AΔ hR)
  have hpΔ : ((PD.p : ℕ) : LetA O n) ∈ W.AΔ := Subalgebra.natCast_mem _ _
  have hr1 : r + 1 ∈ W.AΔ := by
    refine Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ hpΔ (fun i => ?_) ?_
    · simp only [Pi.natCast_apply]
      exact_mod_cast (by
        intro h
        have := congrArg constantCoeff h
        simp only [map_natCast, map_zero] at this
        exact hp0 this : ((PD.p : ℕ) : PowerSeries O) ≠ 0)
    · have : ((PD.p : ℕ) : LetA O n) * (r + 1) = Formalism.MainNotions.ArcLiftingSetup.ps W t - v * W.π₀ ^ (PD.p ^ t) := by
        rw [hps]; ring
      rw [this]
      exact W.AΔ.sub_mem hpsΔ (W.AΔ.mul_mem hvΔ (W.AΔ.pow_mem hR.1 _))
  obtain ⟨gv, hgv⟩ := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.invariant_letter_eq_evaluation W hR hvΔ a
  obtain ⟨gr, hgr⟩ := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.invariant_letter_eq_evaluation W hR hr1 a
  have hE := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.letE_mul_self' (O := O) a
  refine ⟨gv * X ^ (PD.p ^ t) + C ((PD.p : ℕ) : O) * gr, ⟨gv, gr, ?_, rfl⟩, ?_⟩
  · have h1 := congrFun hgv a
    simp only [Pi.mul_apply, letE, Pi.single_eq_same, mul_one, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_apply] at h1
    have hva : IsUnit (v a) := hvu.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) a)
    rw [h1] at hva
    have := hva.map constantCoeff
    rwa [Formalism.MainNotions.UnusedSlot80.ToolsR.cc_subst (Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR)] at this
  · have hC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (C ((PD.p : ℕ) : O)) = ((PD.p : ℕ) : LetA O n) := by
      rw [map_natCast, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, map_natCast]
    have hX : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (X ^ (PD.p ^ t)) = W.π₀ ^ (PD.p ^ t) := by
      rw [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, map_pow, ← Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, evalZero_X_eq_uniformizer W hR]
    rw [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_add W hR, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evalZero_mul W hR, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evalZero_mul W hR, hX, hC,
      hps]
    linear_combination (W.π₀ ^ (PD.p ^ t)) * hgv + ((PD.p : ℕ) : LetA O n) * hgr

theorem finLev_of [IsDomain O] (W : LocWach PD LL O v n) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hp0 : ((PD.p : ℕ) : O) ≠ 0) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) : FinLev W := by
  intro a e H
  set pO : O := ((PD.p : ℕ) : O) with hpO
  set I : Ideal O := Ideal.span {pO} with hI
  have hE := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.letE_mul_self' (O := O) a
  choose Fs hFs hFe using fun t => ps_letter W hR hp0 a t
  set Gall : PowerSeries O := X * (∏ t ∈ Finset.range e, Fs t ^ H t) ^ 2 with hGall
  have hWF : WF pO Gall (1 + (∑ t ∈ Finset.range e, PD.p ^ t * H t) * 2) :=
    (WF.X pO).mul ((WF.prod (fun t => Fs t ^ H t) (fun t => PD.p ^ t * H t)
      (fun t => (hFs t).pow (H t)) e).pow 2)
  set D := 1 + (∑ t ∈ Finset.range e, PD.p ^ t * H t) * 2 with hD
  have hlet : W.π₀ * (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ H t) ^ 2 * letE a =
      Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W Gall * letE a := by
    have h1 : (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ H t) * letE a =
        (∏ t ∈ Finset.range e, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (Fs t) ^ H t) * letE a :=
      idem_prod hE _ _ (fun t => idem_pow hE (hFe t) (H t)) e
    have h2 := idem_mul hE (idem_pow hE h1 2) W.π₀
    rw [h2, hGall, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, map_mul, map_pow, map_prod, ← Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR,
      evalZero_X_eq_uniformizer W hR]
    simp only [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, map_pow]
  obtain ⟨g, h, hgu, hGe⟩ := hWF
  obtain ⟨P, uu, huu, hPm, hPd, hPc, hGP⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.weierP pO hpu D g h hgu
  have hmapP : (P : PowerSeries O).map (Ideal.Quotient.mk I) = X ^ D := by
    ext k
    rw [coeff_map, Polynomial.coeff_coe, coeff_X_pow]
    split_ifs with hk
    · subst hk; rw [← hPd, hPm.coeff_natDegree, map_one]
    · rcases lt_or_gt_of_ne hk with hlt | hgt
      · exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (hPc k hlt))
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  haveI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, hI, Ideal.span_singleton_eq_top]; exact hpu)
  have hord : ((P : PowerSeries O).map (Ideal.Quotient.mk I)).order.toNat = D := by
    rw [hmapP, order_X_pow]; rfl
  have hdiv : (P : PowerSeries O).IsWeierstrassDivisorAt I := by
    unfold PowerSeries.IsWeierstrassDivisorAt
    rw [hord, Polynomial.coeff_coe, ← hPd, hPm.coeff_natDegree]
    exact isUnit_one
  refine ⟨D, fun u hu => ?_⟩
  obtain ⟨f, hf⟩ := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.invariant_letter_eq_evaluation W hR hu a
  have HD := hdiv.isWeierstrassDivisionAt_div_mod f
  set q := hdiv.div f
  set r := hdiv.mod f
  have hdeg : r.degree < (D : WithBot ℕ) := by
    have := HD.degree_lt
    rw [hord] at this
    exact this
  have heq : f = (P : PowerSeries O) * q + (r : PowerSeries O) := HD.eq_mul_add
  have hfG : f = Gall * (↑huu.unit⁻¹ * q) + (r : PowerSeries O) := by
    rw [heq, hGe, hGP, mul_assoc, ← mul_assoc uu, IsUnit.mul_val_inv, one_mul]
  refine ⟨fun j => r.coeff j, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (↑huu.unit⁻¹ * q),
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_mem_invariants W hR _, ?_⟩
  have hr : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (r : PowerSeries O) =
      ∑ j : Fin D, algebraMap O (LetA O n) (r.coeff j) * W.π₀ ^ (j : ℕ) := by
    rw [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, Formalism.MainNotions.RamifiedCoefficientChains.S9.Ring.algHom_coe, ← Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR,
      evalZero_X_eq_uniformizer W hR]
    have hnd : r.natDegree < D := by
      by_cases hr0 : r = 0
      · rw [hr0, Polynomial.natDegree_zero]; omega
      · exact (Polynomial.natDegree_lt_iff_degree_lt hr0).2 hdeg
    rw [Polynomial.aeval_eq_sum_range' hnd, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
  have hu' : (letE a : LetA O n) * u = letE a * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f := by
    rw [mul_comm, hf, mul_comm]
  rw [hu', hfG, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_add W hR, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evalZero_mul W hR, hr]
  have h3 : (letE a : LetA O n) * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W Gall =
      W.π₀ * (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ H t) ^ 2 * letE a := by
    rw [hlet, mul_comm]
  linear_combination (Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (↑huu.unit⁻¹ * q)) * h3

end Formalism.MainNotions.UnusedSlot80.UGen
