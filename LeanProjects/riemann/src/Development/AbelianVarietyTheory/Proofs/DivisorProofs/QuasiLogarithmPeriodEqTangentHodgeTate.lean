import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupFormalChartEvNatMultipleEqConvPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEvaluationSubstCompatibleThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffNmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffs

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogPeriod

variable {p : ℕ} {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type} [Fintype σ]
  [DecidableEq σ]

open MvPowerSeries in
set_option autoImplicit false in
private theorem pderiv_map_algebraMap {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q]
    (k : σ) (g : MvPowerSeries σ B) :
    pderiv Q k (map (algebraMap B Q) g) = map (algebraMap B Q) (pderiv B k g) := by
  ext n
  simp [coeff_pderiv, coeff_map]

open MvPowerSeries in
set_option autoImplicit false in
private theorem subst_zero_eq_C_constantCoeff_divisor {σ τ Q : Type} [CommRing Q] [Finite σ] (h : MvPowerSeries σ Q) :
    subst (fun _ : σ => (0 : MvPowerSeries τ Q)) h = C (constantCoeff h) := by
  classical
  ext e
  rw [coeff_subst (hasSubst_of_constantCoeff_zero (fun _ => by simp))]
  rw [finsum_eq_single _ 0]
  · by_cases he : e = 0 <;> simp [coeff_C, coeff_one, he]
  · intro k hk
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hk
    have : (k.prod fun s n => (0 : MvPowerSeries τ Q) ^ n) = 0 := by
      apply Finset.prod_eq_zero (i := s)
      · simpa using hs
      · simp [zero_pow (by simpa using hs)]
    simp [this]

open MvPowerSeries in
set_option autoImplicit false in
private theorem dIn_univ_of_QL_of_isLaw {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : _root_.GlobalTheory.Katz.IsLaw μ)
    {f : MvPowerSeries (Fin d) Q} (hf : _root_.GlobalTheory.QLog.QL μ ⊤ f) :
    _root_.GlobalTheory.QLog.DIn (B := B) ⊤ f := by
  classical
  obtain ⟨hf0, hlin, hcob⟩ := hf
  obtain ⟨hμ0, hunit, hswap, -⟩ := hμ
  let μQ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) Q := fun j => map (algebraMap B Q) (μ j)
  have hμQ : _root_.GlobalTheory.QLog.up Q μ = μQ := rfl
  have hμQ0 : ∀ j, constantCoeff (μQ j) = 0 := fun j => by simp [μQ, constantCoeff_map, hμ0 j]
  have hsμ : HasSubst μQ := hasSubst_of_constantCoeff_zero hμQ0
  let e : Fin d ⊕ Fin d → MvPowerSeries (Fin d) Q := Sum.elim (fun i => X i) (fun _ => 0)
  have he : HasSubst e := hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp [e])
  let eB : Fin d ⊕ Fin d → MvPowerSeries (Fin d) B := Sum.elim (fun i => X i) (fun _ => 0)
  have heB : HasSubst eB := hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp [eB])
  have hmape : (fun s => map (algebraMap B Q) (eB s)) = e := by
    funext s; rcases s with i | i <;> simp [e, eB]
  have hunitB : ∀ j, subst eB (μ j) = X j := by
    intro j
    have := congrFun hunit j
    simpa [_root_.GlobalTheory.Katz.op, _root_.GlobalTheory.Katz.at2, eB] using this
  have hunitQ : ∀ j, subst e (μQ j) = X j := by
    intro j
    have := congrArg (map (algebraMap B Q)) (hunitB j)
    rw [map_subst heB, hmape, map_X] at this
    exact this
  have hρμ : ∀ h : MvPowerSeries (Fin d) Q, subst e (subst μQ h) = h := by
    intro h
    rw [subst_comp_subst_apply hsμ he]
    simp only [hunitQ]
    exact congrFun subst_self h
  have hlinμ : ∀ i j, coeff (Finsupp.single (Sum.inr i) 1) (μ j) = if i = j then 1 else 0 := by
    intro i j
    have hs1 : HasSubst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) B)) fun k : Fin d => X k) :=
      hasSubst_of_constantCoeff_zero (by rintro (k | k) <;> simp)
    have hs2 : HasSubst (Sum.elim (fun k => (X (Sum.inr k) : MvPowerSeries (Fin d ⊕ Fin d) B))
        fun k => X (Sum.inl k)) :=
      hasSubst_of_constantCoeff_zero (by rintro (k | k) <;> simp)
    have hsw := congrArg (subst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) B)) fun k : Fin d => X k)) (hswap j)
    unfold _root_.GlobalTheory.Katz.swap _root_.GlobalTheory.Katz.at2 at hsw
    rw [subst_comp_subst_apply hs2 hs1] at hsw
    have hfun : (fun s => subst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) B)) fun k : Fin d => X k)
        (Sum.elim (fun k => (X (Sum.inr k) : MvPowerSeries (Fin d ⊕ Fin d) B)) (fun k => X (Sum.inl k)) s)) = eB := by
      funext s
      rcases s with k | k <;> simp [eB, subst_X hs1]
    rw [hfun, hunitB] at hsw
    have hc := (_root_.GlobalTheory.coeff_subst_restrict_sum (μ j)).2 (Finsupp.single i 1)
    rw [← hsw, Finsupp.mapDomain_single, coeff_X] at hc
    rw [← hc]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Finsupp.single_left_inj]
  let M : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) B) :=
    fun j i => subst eB (pderiv B (Sum.inr i) (μ j))
  have hM : ∀ i j, constantCoeff (M i j) = if i = j then 1 else 0 := by
    intro i j
    rw [← coeff_zero_eq_constantCoeff_apply]
    have := (_root_.GlobalTheory.coeff_subst_restrict_sum (pderiv B (Sum.inr j) (μ i))).1 0
    simp only [M, eB]
    rw [this, Finsupp.mapDomain_zero, coeff_pderiv, zero_add, hlinμ j i]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  have hmapsub : ∀ g : MvPowerSeries (Fin d ⊕ Fin d) B,
      subst e (map (algebraMap B Q) g) = map (algebraMap B Q) (subst eB g) := by
    intro g
    rw [map_subst heB, hmape]
  have hchain : ∀ i, ∑ j, pderiv Q j f * map (algebraMap B Q) (M j i) =
      subst e (pderiv Q (Sum.inr i) (subst μQ f)) := by
    intro i
    rw [_root_.GlobalTheory.PSChain.pderiv_subst_chain μQ hμQ0 f (Sum.inr i), ← coe_substAlgHom he, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, coe_substAlgHom, hρμ]
    simp only [M, μQ]
    rw [pderiv_map_algebraMap, hmapsub]
  have hg : ∀ i, _root_.GlobalTheory.QLog.In (B := B) ⊤
      (subst e (pderiv Q (Sum.inr i) (subst μQ f))) := by
    intro i
    obtain ⟨s₀, hs₀⟩ := _root_.GlobalTheory.QLog.In.top_iff.1 hcob
    have hdec : subst μQ f = map (algebraMap B Q) s₀ + _root_.GlobalTheory.Katz.inL f +
        _root_.GlobalTheory.Katz.inR f := by
      rw [hs₀]
      unfold _root_.GlobalTheory.Katz.cob1
      rw [hμQ]
      ring
    have hleft : pderiv Q (Sum.inr i) (_root_.GlobalTheory.Katz.inL f) = 0 := by
      unfold _root_.GlobalTheory.Katz.inL
      rw [_root_.GlobalTheory.PSChain.pderiv_subst_chain _ (fun k => by simp) f (Sum.inr i)]
      simp [pderiv_X]
    have hright : pderiv Q (Sum.inr i) (_root_.GlobalTheory.Katz.inR f) =
        subst (fun k => (X (Sum.inr k) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (pderiv Q i f) := by
      unfold _root_.GlobalTheory.Katz.inR
      rw [_root_.GlobalTheory.PSChain.pderiv_subst_chain _ (fun k => by simp) f (Sum.inr i)]
      simp [pderiv_X, Pi.single_apply]
    obtain ⟨b, -, hb⟩ := hlin i
    have hX : HasSubst (fun k => (X (Sum.inr k) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
      hasSubst_of_constantCoeff_zero (fun k => by simp)
    have hrr : subst e (subst (fun k => (X (Sum.inr k) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (pderiv Q i f)) =
        map (algebraMap B Q) (C b) := by
      rw [subst_comp_subst_apply hX he]
      have hz : (fun k : Fin d => subst e (X (Sum.inr k) : MvPowerSeries (Fin d ⊕ Fin d) Q)) =
          fun _ => 0 := by
        funext k
        rw [subst_X he]
        rfl
      rw [hz, subst_zero_eq_C_constantCoeff_divisor, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
      unfold _root_.GlobalTheory.Katz.lin at hb
      simp [hb]
    rw [_root_.GlobalTheory.QLog.In.top_iff]
    refine ⟨subst eB (pderiv B (Sum.inr i) s₀) + C b, ?_⟩
    rw [hdec]
    simp only [map_add]
    rw [hleft, hright, add_zero, ← coe_substAlgHom he, map_add, coe_substAlgHom, hrr,
      pderiv_map_algebraMap, hmapsub]
  have hsol := _root_.GlobalTheory.InvSolve.solve ⊤ M hM (fun j => pderiv Q j f)
    (fun i => subst e (pderiv Q (Sum.inr i) (subst μQ f))) hchain hg
  intro α i
  by_cases hα : α i = 0
  · exact ⟨0, Submodule.mem_top, by simp [hα]⟩
  · obtain ⟨b, -, hb⟩ := hsol i (α - Finsupp.single i 1)
    refine ⟨b, Submodule.mem_top, ?_⟩
    have hαe : α - Finsupp.single i 1 + Finsupp.single i 1 = α := by
      ext k
      by_cases hk : k = i
      · subst hk; simp; omega
      · simp [Finsupp.single_apply, Ne.symm hk]
    have hαi : (((α - Finsupp.single i 1 : Fin d →₀ ℕ) i : ℕ) : Q) + 1 = (α i : Q) := by
      have : (α - Finsupp.single i 1 : Fin d →₀ ℕ) i + 1 = α i := by simp; omega
      rw [← this]
      push_cast
      ring
    rw [← hb, coeff_pderiv, hαe, hαi, mul_comm]

open MvPowerSeries in
set_option autoImplicit false in
private theorem constantCoeff_nmul_eq_zero {d : ℕ} {R : Type} [CommRing R]
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.QLog.nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [_root_.GlobalTheory.QLog.nmul]
  | succ k ih =>
    have hstep : _root_.GlobalTheory.QLog.nmul μ (k + 1) i =
        _root_.GlobalTheory.Katz.at2 (μ i) (_root_.GlobalTheory.QLog.nmul μ k) (fun j => X j) := by
      unfold _root_.GlobalTheory.QLog.nmul
      rw [Function.iterate_succ_apply']
      rfl
    rw [hstep]
    unfold _root_.GlobalTheory.Katz.at2
    have ha : ∀ j : Fin d ⊕ Fin d,
        constantCoeff (Sum.elim (_root_.GlobalTheory.QLog.nmul μ k) (fun j => (X j : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · simp
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha (hμ i)

open MvPowerSeries in
set_option autoImplicit false in
private theorem hasVal_zero_of_constantCoeff_eq_zero {p : ℕ} {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ}
    {f : MvPowerSeries (Fin d) Q} (hf : constantCoeff f = 0) :
    _root_.GlobalTheory.QLog.HasVal p (fun _ : Fin d => (0 : B)) f 0 := by
  intro m
  refine ⟨0, fun N _ => ⟨0, ?_⟩⟩
  have h0 : (fun i : Fin d => (algebraMap B Q) ((fun _ : Fin d => (0 : B)) i)) = 0 := by
    funext i; simp
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at hf
  rw [h0, MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq, MvPowerSeries.coeff_trunc']
  simp [hf]

open MvPowerSeries in
set_option autoImplicit false in

theorem _root_.GlobalTheory.QLogPeriod.hasPeriod_hodgeTate : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : _root_.GlobalTheory.PDivGroup p O) (d : ℕ) (c : _root_.GlobalTheory.QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], _root_.GlobalTheory.QLog.IsFrame p E (RingHom.id O) → ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), _root_.GlobalTheory.QLog.QL c.μ ⊤ f → c.IsLie f l → ∀ t : G.Tate, c.HasPeriod (RingHom.id O) t f (l (G.hodgeTate t)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF f l hQL hLie t
  have hF' := hF
  obtain ⟨-, hinj, -, hpunit, -, -, -, -⟩ := hF'
  rw [c.hasPeriod_iff hF]
  intro n z hz
  obtain ⟨s, hs, hsl⟩ := (c.isLie_iff hinj f l).1 hLie n
  obtain ⟨b₀, hb₀⟩ := hsl (G.hodgeTate t) (WithConv.toConv (t.pt n).toLinearMap)
    (G.hodgeTate_val t n).symm
  have hz' : ∀ i, z i = (t.pt n) (c.x n i) := hz
  have hznil : ∀ i, ∃ N, (p : O) ∣ z i ^ N := by
    intro i
    obtain ⟨N, a, ha⟩ := c.5 n i
    exact ⟨N, (t.pt n) a, by rw [hz', ← map_pow, ha, map_mul, map_natCast]⟩
  let Ez : MvPowerSeries (Fin d) O →ₐ[O] O := (t.pt n).comp (c.ev n)
  have hEz : _root_.GlobalTheory.QLog.IsEval p z Ez := by
    obtain ⟨hX, hc⟩ := c.6 n
    refine ⟨fun i => ?_, fun m => ?_⟩
    · simp [Ez, hX, hz']
    · obtain ⟨N, hN⟩ := hc m
      refine ⟨N, fun g hg => ?_⟩
      obtain ⟨a, ha⟩ := hN g hg
      exact ⟨(t.pt n) a, by simp [Ez, ha, map_mul, map_pow, map_natCast]⟩
  have hval_s := _root_.GlobalTheory.hasVal_map_of_isEval p O O E (RingHom.id O) hF
    (Fin d) z hznil Ez hEz s
  rw [hs] at hval_s
  have hdiff : _root_.GlobalTheory.QLog.DIn (B := O) ⊤ f := dIn_univ_of_QL_of_isLaw c.12 hQL
  have hu0 : ∀ j, constantCoeff (_root_.GlobalTheory.QLog.nmul c.μ (p ^ n) j) = 0 :=
    constantCoeff_nmul_eq_zero c.12.1 (p ^ n)
  have hEu : (fun j => Ez (_root_.GlobalTheory.QLog.nmul c.μ (p ^ n) j)) = fun _ => (0 : O) := by
    funext j
    simp only [Ez, AlgHom.comp_apply]
    rw [_root_.GlobalTheory.NMul.ev_nmul p C v O hv G d c n (p ^ n) j, G.mulBy_pow_self,
      c.9 n j, map_zero, map_zero]
  have hval_sub := _root_.GlobalTheory.QLog.hasVal_subst p O O E (RingHom.id O) hF (Fin d) z hznil
    Ez hEz (Fin d) (_root_.GlobalTheory.QLog.nmul c.μ (p ^ n)) f 0 hu0 hdiff
    (by rw [hEu]; exact hasVal_zero_of_constantCoeff_eq_zero hQL.1)
  have hsum := (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p O O E (RingHom.id O) hF (Fin d) z _ _ _ _
    hval_s).1 hval_sub
  set u := (hpunit.pow n).unit with hu
  have hsm := (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p O O E (RingHom.id O) hF (Fin d) z _ 0 _ 0
    hsum).2.1 (↑u⁻¹ : E)
  have hpu : ((p : E)) ^ n = ↑u := (IsUnit.unit_spec _).symm
  have hser : (↑u⁻¹ : E) • (_root_.GlobalTheory.QLog.defect c.μ (p ^ n) f +
      subst (_root_.GlobalTheory.QLog.up E (_root_.GlobalTheory.QLog.nmul c.μ (p ^ n))) f) = f := by
    unfold _root_.GlobalTheory.QLog.defect
    rw [sub_add_cancel, smul_smul]
    have hcast : (((p ^ n : ℕ)) : E) = ↑u := by rw [← hpu]; push_cast; rfl
    rw [hcast, Units.inv_mul, one_smul]
  rw [hser] at hsm
  refine ⟨_, hsm, -b₀, ?_⟩
  have hE : Ez s = l (G.hodgeTate t) + (p : O) ^ n * -b₀ := by
    have h : Ez s = (WithConv.toConv (t.pt n).toLinearMap).ofConv ((c.ev n) s) := rfl
    rw [h]
    linear_combination -hb₀
  rw [← hE, add_zero, ← mul_assoc, hpu, Units.mul_inv, one_mul]

end GlobalTheory.QLogPeriod
