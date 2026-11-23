import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardKerSubspacesAndHeckePolyOfConvolution
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeterssonFormProportionalClassSumAllLevelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuaMatchingConjugatePrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingCharactersUnramifiedOffLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaAtOfIsEtaConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.SplitChain

open Formalism.L2.Col (heckePolyOf blockPoly gaussBin)

def stepMat (q n t : ℕ) (ν s : ℂ) (k j : ℕ) : ℂ :=
  if j ≤ k then (q : ℂ) ^ ((n - j) * (k - j)) * (gaussBin q t (k - j) : ℂ) * ν ^ (k - j) * s ^ j else 0

theorem heckePolyOf_congr {n q : ℕ} {a b : ℕ → ℂ} (h : ∀ k, k ≤ n → a k = b k) :
    heckePolyOf n q a = heckePolyOf n q b := by
  unfold heckePolyOf
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]

theorem step_poly (q n t : ℕ) (ν s : ℂ) (a : ℕ → ℂ) :
    heckePolyOf (n + t) q (fun l => ∑ i ∈ Finset.range (n + 1), stepMat q n t ν s l i * a i) =
      (heckePolyOf n q a).comp (C s * X) * blockPoly (ν * (q : ℂ) ^ n) q t := by
  have h := GlobalTheory.KerRangeCount.card_ker_and_heckePolyOf_conv.2 ℂ q n t (fun j => if j ≤ n then a j else 0) ν s
    (fun j hj => if_neg (by omega))
  rw [heckePolyOf_congr (b := a) (fun k hk => if_pos hk)] at h
  rw [← h]
  refine heckePolyOf_congr fun l _ => ?_
  have e1 : ∀ (f : ℕ → ℂ) (u v : ℕ), ∑ i ∈ Finset.range (u + 1), (if i ≤ v then f i else 0) =
      ∑ i ∈ Finset.range (v + 1), (if i ≤ u then f i else 0) := by
    intro f u v
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp only [stepMat, ite_mul, zero_mul, mul_ite, mul_zero]
  exact e1 _ _ _

theorem blockPoly_comp (ν s : ℂ) (q t : ℕ) : (blockPoly ν q t).comp (C s * X) = blockPoly (ν * s) q t := by
  unfold blockPoly
  rw [Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun c _ => ?_
  simp only [sub_comp, one_comp, mul_comp, C_comp, X_comp]
  rw [← mul_assoc, ← C_mul]
  congr 3
  ring

theorem exists_chain (m : ℕ) (n : ℕ → ℕ) (M : ℕ → ℕ → ℕ → ℂ) :
    ∃ W : ℕ → ℕ → ℕ → ℂ, (∀ k i, W m k i = if i = k then 1 else 0) ∧
      ∀ j, j < m → ∀ k i, W j k i = ∑ l ∈ Finset.range (n (j + 1) + 1), W (j + 1) k l * M j l i := by
  let U : ℕ → ℕ → ℕ → ℂ := fun d => Nat.rec (fun k i => if i = k then 1 else 0)
    (fun d u k i => ∑ l ∈ Finset.range (n (m - d) + 1), u k l * M (m - d - 1) l i) d
  refine ⟨fun j => U (m - j), fun k i => by simp [U], fun j hj k i => ?_⟩
  have e1 : m - j = (m - (j + 1)) + 1 := by omega
  have e2 : m - (m - (j + 1)) = j + 1 := by omega
  show U (m - j) k i = _
  rw [e1]
  show ∑ l ∈ Finset.range (n (m - (m - (j + 1))) + 1), U (m - (j + 1)) k l * M (m - (m - (j + 1)) - 1) l i = _
  rw [e2]
  rfl

theorem chain_poly (q t m : ℕ) (n : ℕ → ℕ) (hn : ∀ j, n (j + 1) = n j + t) (ν s : ℕ → ℂ) (W : ℕ → ℕ → ℕ → ℂ)
    (h0 : ∀ k i, W m k i = if i = k then 1 else 0)
    (h1 : ∀ j, j < m → ∀ k i, W j k i = ∑ l ∈ Finset.range (n (j + 1) + 1), W (j + 1) k l * stepMat q (n j) t (ν j) (s j) l i)
    (d : ℕ) : ∀ j, j + d = m → ∀ a : ℕ → ℂ,
      heckePolyOf (n m) q (fun k => ∑ i ∈ Finset.range (n j + 1), W j k i * a i) =
        (heckePolyOf (n j) q a).comp (C (∏ i ∈ Finset.Ico j m, s i) * X) *
          ∏ i ∈ Finset.Ico j m, blockPoly (ν i * (q : ℂ) ^ n i * ∏ l ∈ Finset.Ico (i + 1) m, s l) q t := by
  induction d with
  | zero =>
    intro j hj a
    obtain rfl : j = m := hj
    simp only [Finset.Ico_self, Finset.prod_empty, C_1, one_mul, comp_X, mul_one]
    refine heckePolyOf_congr fun k hk => ?_
    simp only [h0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range]
    exact if_pos (by omega)
  | succ d ih =>
    intro j hj a
    have hjm : j < m := by omega
    have e : ∀ k, ∑ i ∈ Finset.range (n j + 1), W j k i * a i =
        ∑ l ∈ Finset.range (n (j + 1) + 1), W (j + 1) k l *
          ∑ i ∈ Finset.range (n j + 1), stepMat q (n j) t (ν j) (s j) l i * a i := by
      intro k
      simp only [h1 j hjm, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    simp only [e]
    rw [ih (j + 1) (by omega), hn j, step_poly, mul_comp, blockPoly_comp, comp_assoc,
      Finset.prod_eq_prod_Ico_succ_bot hjm, Finset.prod_eq_prod_Ico_succ_bot hjm, mul_assoc]
    simp only [mul_comp, C_comp, X_comp, C_mul, mul_assoc]

theorem prod_alt (h σ : ℂ) (hh : h ≠ 0) (m : ℕ) (hm : Even m) (d : ℕ) : ∀ j, j + d = m →
    ∏ i ∈ Finset.Ico j m, ((if Odd (i + 1) then h else h⁻¹) * σ) = (if Odd j then h⁻¹ else 1) * σ ^ d := by
  induction d with
  | zero =>
    intro j hj
    obtain rfl : j = m := hj
    simp [Nat.not_odd_iff_even.2 hm]
  | succ d ih =>
    intro j hj
    rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : j < m), ih (j + 1) (by omega)]
    rcases Nat.even_or_odd j with h1 | h1
    · rw [if_pos h1.add_one, if_pos h1.add_one, if_neg (Nat.not_odd_iff_even.2 h1)]
      field_simp
      ring
    · rw [if_neg (Nat.not_odd_iff_even.2 h1.add_one), if_neg (Nat.not_odd_iff_even.2 h1.add_one), if_pos h1]
      ring

variable {D : D7}

theorem opOf_eq {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (c : List ℤ →₀ ℂ) : opOf π P c = Finsupp.linearCombination ℂ (fun d => ∑ γ ∈ rep V P d, π γ) c := rfl

theorem dualC_eq (c : List ℤ →₀ ℂ) : dualC c = Finsupp.lmapDomain ℂ ℂ dualLab c := rfl

theorem dualC_dualC (c : List ℤ →₀ ℂ) : dualC (dualC c) = c := by
  unfold dualC
  rw [← Finsupp.mapDomain_comp]
  have : dualLab ∘ dualLab = id := by
    funext d
    simp [dualLab, List.map_reverse]
  rw [this, Finsupp.mapDomain_id]

theorem match_sum {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    {P : Pl D.host.E} (I : Finset ℕ) (w : ℕ → ℂ) (a b : ℕ → List ℤ →₀ ℂ) (h : ∀ l ∈ I, Match ψ om P (a l) (b l)) :
    Match ψ om P (∑ l ∈ I, w l • a l) (∑ l ∈ I, w l • b l) := by
  intro f hf
  simp only [opOf_eq, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun l hl => ?_
  have := h l hl f hf
  simp only [opOf_eq] at this
  rw [this]

theorem splitC_sum (n : ℕ) (I : Finset ℕ) (w : ℕ → ℂ) (M : ℕ → ℕ → ℂ) :
    splitC n (fun i => ∑ l ∈ I, w l * M l i) = ∑ l ∈ I, w l • splitC n (M l) := by
  simp only [splitC, Finsupp.single_finsetSum, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul]
  exact Finset.sum_comm

theorem dualC_splitC (n : ℕ) (w : ℕ → ℂ) :
    dualC (splitC n w) = ∑ l ∈ Finset.range (n + 1), w l • dualC (Finsupp.single (splitLab n l) 1) := by
  simp only [splitC, dualC_eq, map_sum, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem splitC_delta {n k : ℕ} (hk : k ≤ n) :
    splitC n (fun i => if i = k then 1 else 0) = Finsupp.single (splitLab n k) 1 := by
  unfold splitC
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_range.2 (by omega)) h)]
  simp

theorem absNorm_conjPl (P : Pl D.host.E) : Ideal.absNorm (conjPl P).asIdeal = Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal (conjPl P).asIdeal (Formalism.DivisionValues.cO D.host.E) rfl).toEquiv).symm

theorem unrPl_mul_inv {P : Pl D.host.E} {χ η : (AE D)ˣ →* Circle} (h : UnrPl P χ) (h' : UnrPl P η) :
    UnrPl P (χ * η⁻¹) := fun e f he x h1 h2 h3 => by
  show χ x * (η x)⁻¹ = 1
  rw [h e f he x h1 h2 h3, h' e f he x h1 h2 h3, inv_one, mul_one]

theorem unrPl_step {P : Pl D.host.E} {μ : ℕ → (AE D)ˣ →* Circle} {η : (AE D)ˣ →* Circle} {j : ℕ} (h : UnrPl P (μ j))
    (h' : UnrPl P η) : UnrPl P (Lift.chrStep μ η j).1 ∧ UnrPl P (Lift.chrStep μ η j).2 := by
  unfold Lift.chrStep
  split_ifs
  · exact ⟨unrPl_mul_inv h h', h⟩
  · exact ⟨h, unrPl_mul_inv h h'⟩

theorem step_match {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {P : Pl D.host.E} (hW : IsWeilDatumO ψ S T χS χT om)
    (hP : conjPl P ≠ P) (u : UnrPl P χS ∧ UnrPl P χT) (u' : UnrPl (conjPl P) χS ∧ UnrPl (conjPl P) χT)
    {e : AE D} {ϖ : 𝓞 D.host.E} {x : (AE D)ˣ} {t n n' : ℕ} (he : Formalism.L2.NTheta.IsIdemAt e (conjPl P))
    (h1 : ϖ ∈ (conjPl P).asIdeal) (h2 : ϖ ∉ (conjPl P).asIdeal ^ 2) (hx : (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e))
    (hS : S.rank = n) (hT : T.rank = n') (hr : n' = n + t) {q : ℕ} (hq : q = Ideal.absNorm P.asIdeal) {ν s : ℂ}
    (hν : ν = ((χS x : ℂ) * (Real.sqrt q : ℂ) ^ n)⁻¹) (hs : s = ν * ((χT x : ℂ) * (Real.sqrt q : ℂ) ^ n')) (w : ℕ → ℂ) :
    Match ψ om P (splitC n fun i => ∑ l ∈ Finset.range (n' + 1), w l * stepMat q n t ν s l i) (dualC (splitC n' w)) := by
  subst hS hT
  rw [← absNorm_conjPl] at hq
  have hP' : conjPl (conjPl P) ≠ conjPl P := by rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]; exact hP.symm
  have hv := (GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace ψ S T χS χT om P hW hP u.1 u.2).1
  have hm := ((GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace ψ S T χS χT om (conjPl P) hW hP' u'.1 u'.2).2 e ϖ x t he h1 h2 hx).1 hr
  rw [splitC_sum, dualC_splitC]
  refine match_sum _ _ _ _ fun l hl => ?_
  have h3 := (((GlobalTheory.T.thetaVacua_matching_conjugatePrime ψ S T χS χT om P hW).2 hv).2 _ _).1 (hm l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)))
  rw [dualC_dualC, ← hq, ← hν] at h3
  convert h3 using 2
  funext j
  unfold stepMat
  split_ifs with hj
  · rw [hs, mul_pow ν, ← mul_assoc, mul_assoc _ (ν ^ (l - j)), ← pow_add, Nat.sub_add_cancel hj]
  · rfl

open Formalism.L2.JoinChr in

theorem val_conj {χ : (AE D)ˣ →* Circle} {n : ℕ} (hχ : ResEta D χ n) {P : Pl D.host.E} (u : UnrPl P χ)
    {e : AE D} {ϖ : 𝓞 D.host.E} {x : (AE D)ˣ} (he : Formalism.L2.NTheta.IsIdemAt e (conjPl P))
    (h1 : ϖ ∈ (conjPl P).asIdeal) (h2 : ϖ ∉ (conjPl P).asIdeal ^ 2) (hx : (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e)) :
    ∃ (e' : AE D) (y : (AE D)ˣ), IsPlIdem D e' P ∧ (y : AE D) = locE D e' (Formalism.L2.Host.unif P : D.host.Eˣ) ∧ (χ x)⁻¹ = χ y := by
  have hc : ∀ a : 𝓞 D.host.E, Formalism.DivisionValues.cO D.host.E (Formalism.DivisionValues.cO D.host.E a) = a := fun a => Subtype.ext (star_star _)
  have hmem : ∀ (I : Ideal (𝓞 D.host.E)) (a : 𝓞 D.host.E),
      a ∈ I.map (Formalism.DivisionValues.cO D.host.E) ↔ Formalism.DivisionValues.cO D.host.E a ∈ I := by
    intro I a
    conv_lhs => rw [← hc a]
    exact Ideal.apply_mem_of_equiv_iff
  have he' : Formalism.L2.NTheta.IsIdemAt (cA D e) P := GlobalTheory.MovedIdem.isIdemAt_conj he fun a => by
    have := hmem P.asIdeal (Formalism.DivisionValues.cO D.host.E a)
    rw [hc] at this
    exact this.symm
  have hpl : IsPlIdem D (cA D e) P := by
    obtain ⟨⟨a1, a2, v, ε, a3, a4⟩, a5⟩ := he'
    exact ⟨a1, ⟨v, ε, a3, Or.inl ⟨a2, a4⟩⟩, a5⟩
  set p : 𝓞 D.host.E := Formalism.DivisionValues.cO D.host.E ϖ with hp
  have p1 : p ∈ P.asIdeal := (hmem _ _).1 h1
  have p2 : p ∉ P.asIdeal ^ 2 := fun h => h2 (by
    have := (hmem _ _).2 h
    rwa [Ideal.map_pow] at this)
  have p0 : p ≠ 0 := fun h => p2 (h ▸ zero_mem _)
  have pv : P.valuation D.host.E (p : D.host.E) = WithZero.exp (-1 : ℤ) := by
    rw [RingOfIntegers.coe_eq_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    have a1 := (P.intValuation_le_pow_iff_mem p 1).2 (by simpa using p1)
    have a2 := mt (P.intValuation_le_pow_iff_mem p 2).1 p2
    have a0 := P.intValuation_ne_zero p p0
    rw [← WithZero.exp_log a0] at a1 a2 ⊢
    rw [WithZero.exp_le_exp] at a1 a2
    congr 1
    push_cast at a1 a2
    omega
  let k : D.host.Eˣ := Units.mk0 (p : D.host.E) (RingOfIntegers.coe_ne_zero_iff.2 p0)
  let L := GlobalTheory.EtaConjLocal.locHom hpl.1
  have hu : P.valuation D.host.E ((k * (Formalism.L2.Host.unif P)⁻¹ : D.host.Eˣ) : D.host.E) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, GlobalTheory.EtaConjLocal.val_unif]
    exact mul_inv_eq_one₀ WithZero.exp_ne_zero |>.2 pv
  have h3 : χ (L (k * (Formalism.L2.Host.unif P)⁻¹)) = 1 := by
    refine u (cA D e) _ (Or.inl ⟨he', rfl⟩) _ ?_ (GlobalTheory.EtaConjLocal.locE_parts hpl _ hu.le).2 ?_
    · show _ * (locE D _ _ - 1) = locE D _ _ - 1
      unfold locE
      linear_combination (incA D ((k * (Formalism.L2.Host.unif P)⁻¹ : D.host.Eˣ) : D.host.E) - 1) * (he'.1.1 + he'.1.2.1)
    · rw [← map_inv]
      refine (GlobalTheory.EtaConjLocal.locE_parts hpl (((k * (Formalism.L2.Host.unif P)⁻¹)⁻¹ : D.host.Eˣ) : D.host.E) ?_).2
      rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have h4 : χ x * χ (L k) = 1 := GlobalTheory.SplitDetCharacter.char_norm hχ x (L k) (by
    show locE D _ _ = _
    rw [hx, map_add, map_mul, map_sub, map_one, GlobalTheory.MovedIdem.cA_incA]
    unfold locE
    have : (k : D.host.E) = star (ϖ : D.host.E) := rfl
    rw [this]
    ring)
  refine ⟨cA D e, L (Formalism.L2.Host.unif P), hpl, rfl, ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one] at h3
  rw [← h3]
  exact inv_eq_of_mul_eq_one_right h4

theorem constants (q r t m : ℕ) (hq : q ≠ 0) (hr : Odd r) (ht : Odd t) (hm : Even m) (a : ℕ → ℂ) (h : ℂ) (ha : ∀ i, a i ≠ 0)
    (hh : h ≠ 0) (cS cT ν s : ℕ → ℂ) (hS : ∀ i, cS i = if Odd (i + 1) then a i * h⁻¹ else a i)
    (hT : ∀ i, cT i = if Odd (i + 1) then a i else a i * h⁻¹)
    (hν : ∀ i, ν i = (cS i * (Real.sqrt q : ℂ) ^ (r + i * t))⁻¹)
    (hs : ∀ i, s i = ν i * (cT i * (Real.sqrt q : ℂ) ^ (r + (i + 1) * t))) :
    ∏ i ∈ Finset.Ico 0 m, s i = (q : ℂ) ^ (m / 2 * t) ∧ ∀ i, i < m →
      ν i * (q : ℂ) ^ (r + i * t) * ∏ l ∈ Finset.Ico (i + 1) m, s l = (a i)⁻¹ * (q : ℂ) ^ ((r + (m - 1) * t) / 2) := by
  set σ : ℂ := (Real.sqrt q : ℂ) with hσ
  have h2 : (q : ℂ) = σ ^ 2 := by
    rw [hσ, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg q), Complex.ofReal_natCast]
  have h0 : σ ≠ 0 := fun h => hq (by rw [h] at h2; simpa using h2)
  have e : ∀ i, s i = (if Odd (i + 1) then h else h⁻¹) * σ ^ t := by
    intro i
    have := ha i
    rw [hs, hν, hS, hT]
    split_ifs <;> field_simp <;> ring
  simp only [e]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [prod_alt h _ hh m hm m 0 (zero_add m), if_neg (by simp), one_mul, h2, ← pow_mul, ← pow_mul]
    congr 1
    obtain ⟨c, rfl⟩ := hm
    rw [show (c + c) / 2 = c by omega]
    ring
  · obtain ⟨d, rfl⟩ : ∃ d, m = i + 1 + d := ⟨m - (i + 1), by omega⟩
    have e2 : 2 * ((r + (i + 1 + d - 1) * t) / 2) = r + i * t + t * d := by
      rw [show i + 1 + d - 1 = i + d by omega, Nat.mul_div_cancel' (even_iff_two_dvd.1 (hr.add_odd (Odd.mul ?_ ht)))]
      · ring
      · rw [Nat.even_iff] at hm
        rw [Nat.odd_iff]
        omega
    have := ha i
    rw [prod_alt h _ hh _ hm d (i + 1) rfl, hν, hS, h2, ← pow_mul σ 2 (_ / 2), e2, ← pow_mul σ 2, ← pow_mul σ t,
      two_mul, pow_add, pow_add σ (r + i * t)]
    split_ifs <;> field_simp <;> ring

theorem exists_transfer : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t (P : A.ok t), ∃ z : ℕ → ℕ → ℂ, (∀ k, k ≤ D.sp.X'.rank → MatchE R t (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (splitC (Yc D 0).rank (z k))) ∧ ∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf D.sp.X'.rank (A.q P) (fun k => ∑ j ∈ Finset.range ((Yc D 0).rank + 1), z k j * a j) = (Formalism.L2.Col.heckePolyOf (Yc D 0).rank (A.q P) a).comp (C ((A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) * X) * ((A.fam.R t).blockProd P).map D.what₂.embLL := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hC hS t P
  obtain ⟨-, g2, -, g4⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev
  obtain ⟨hG, hP, hq⟩ := g4 hC.fam t P P.2
  have hG' := (g2 t _ hG).2.1
  obtain ⟨u1, u2⟩ := GlobalTheory.T.splittingCharacters_unramified_offLevels R F hC.lev t _ hG
  obtain ⟨v1, v2⟩ := GlobalTheory.T.splittingCharacters_unramified_offLevels R F hC.lev t _ hG'
  have hm := D.R.two_le_m
  have hP' : conjPl (conjPl (R.pl P)) ≠ conjPl (R.pl P) := by rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]; exact hP.symm
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt (conjPl (R.pl P)) (by
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
    exact fun h => hP' (HeightOneSpectrum.ext h))
  obtain ⟨ϖ, h1, h2⟩ : ∃ ϖ ∈ (conjPl (R.pl P)).asIdeal, ϖ ∉ (conjPl (R.pl P)).asIdeal ^ 2 :=
    SetLike.exists_of_lt (Ideal.pow_lt_self _ (conjPl (R.pl P)).ne_bot (conjPl (R.pl P)).isPrime.ne_top 2 le_rfl)
  have h0 : (ϖ : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 fun h => h2 (h ▸ zero_mem _)
  obtain ⟨x, hx⟩ : ∃ x : (AE D)ˣ, (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) :=
    ⟨Formalism.L2.JoinChr.locU he.1.1 (Units.mk0 _ h0), by
      rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, Units.val_mk0]; ring⟩
  have hY : ∀ j, j ≤ D.R.m → (Yc D j).rank = D.R.r + j * D.R.t := fun j hj => by
    rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj]; rfl
  have hX : D.sp.X'.rank = D.R.r + D.R.m * D.R.t := D.sp.X'_rank
  have hn : ∀ j, D.R.r + (j + 1) * D.R.t = D.R.r + j * D.R.t + D.R.t := fun j => by ring
  let μ := R.toLevCh.mu t
  let ν : ℕ → ℂ := fun i => (((Lift.chrStep μ R.eta (i + 1)).1 x : ℂ) * (Real.sqrt (A.q P) : ℂ) ^ (D.R.r + i * D.R.t))⁻¹
  let s : ℕ → ℂ := fun i => ν i * (((Lift.chrStep μ R.eta (i + 1)).2 x : ℂ) * (Real.sqrt (A.q P) : ℂ) ^ (D.R.r + (i + 1) * D.R.t))
  obtain ⟨W, w0, w1⟩ := exists_chain D.R.m (fun j => D.R.r + j * D.R.t)
    fun j => stepMat (A.q P) (D.R.r + j * D.R.t) D.R.t (ν j) (s j)
  have hmm : D.R.m - 1 + 1 = D.R.m := by omega
  have hfix : FixAll R t (R.pl P) := by
    refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
    · have := unrPl_step (u2 (k + 1) (by omega) hk.le) u1
      exact (GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace _ _ _ _ _ _ _ (hC.chain.ωY t k hk) hP this.1 this.2).1
    · have := unrPl_step (u2 D.R.m (by omega) le_rfl) u1
      exact (GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace _ _ _ _ _ _ _ (hC.chain.ωX t) hP this.1 this.2).1
    · have := u2 ((i : ℕ) + 1) (by omega) i.2
      exact (GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace _ _ _ _ _ _ _ (hC.thP.ωP i t) hP this (unrPl_mul_inv this u1)).1
  refine ⟨W 0, fun k hk => ?_, fun a => ?_⟩
  · rw [hY 0 (Nat.zero_le _)]
    refine GlobalTheory.T.matchE_of_chainStep_matches R F hL hC hS t _ hG hfix _ (fun j => splitC (D.R.r + j * D.R.t) (W j k)) ?_ fun j hj => ?_
    · have hW := hC.chain.ωX t
      have h3 := step_match (ν := ν (D.R.m - 1)) (s := s (D.R.m - 1)) hW hP (unrPl_step (u2 D.R.m (by omega) le_rfl) u1)
        (unrPl_step (v2 D.R.m (by omega) le_rfl) v1) he h1 h2 hx (hY _ (Nat.sub_le _ _)) hX
        (by rw [← hn, hmm]) hq (by simp only [ν, hmm, μ]) (by simp only [s, hmm, μ]) (W D.R.m k)
      rw [funext (w0 k), ← hX, splitC_delta hk] at h3
      have h4 := funext (w1 (D.R.m - 1) (by omega) k)
      simp only [hmm] at h4
      rw [funext (w0 k), ← hX] at h4
      simp only [h4]
      exact h3
    · have h3 := step_match (ν := ν j) (s := s j) (hC.chain.ωY t j hj) hP (unrPl_step (u2 (j + 1) (by omega) hj.le) u1)
        (unrPl_step (v2 (j + 1) (by omega) hj.le) v1) he h1 h2 hx (hY _ (by omega)) (hY _ hj.le)
        (hn j) hq rfl rfl (W (j + 1) k)
      simp only [funext (w1 j (by omega) k)]
      exact h3
  · have hq0 : A.q P ≠ 0 := by
      rw [hq]
      exact fun h => (R.pl P).ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    obtain ⟨c1, c2⟩ := constants (A.q P) D.R.r D.R.t D.R.m hq0 (Formalism.L2.NTheta.odd_r D.R) D.R.t_odd D.R.m_even
      (fun i => (μ (i + 1) x : ℂ)) (R.eta x : ℂ) (fun i => Circle.coe_ne_zero _) (Circle.coe_ne_zero _)
      (fun i => ((Lift.chrStep μ R.eta (i + 1)).1 x : ℂ)) (fun i => ((Lift.chrStep μ R.eta (i + 1)).2 x : ℂ)) ν s
      (fun i => by unfold Lift.chrStep; split_ifs <;> simp) (fun i => by unfold Lift.chrStep; split_ifs <;> simp)
      (fun i => rfl) (fun i => rfl)
    have h3 := chain_poly (A.q P) D.R.t D.R.m (fun j => D.R.r + j * D.R.t) hn ν s W w0 w1 D.R.m 0 (zero_add _) a
    rw [hX, hY 0 (Nat.zero_le _), h3, c1]
    congr 1
    obtain ⟨_, _, _, tie⟩ := hC.fam.tie
    obtain ⟨-, r1, r2⟩ := tie.ranks
    have hres : ∀ j, j < D.R.m → ∃ n, ResEta D (μ (j + 1)) n := by
      intro j hj
      have : (∃ n, ResEta D (Lift.chrStep μ R.eta (j + 1)).1 n) ∧ ∃ n, ResEta D (Lift.chrStep μ R.eta (j + 1)).2 n := by
        rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hj) with h | h
        · exact ⟨⟨_, (hC.chain.ωY t j h).resS⟩, _, (hC.chain.ωY t j h).resT⟩
        · rw [show j + 1 = D.R.m from h]
          exact ⟨⟨_, (hC.chain.ωX t).resS⟩, _, (hC.chain.ωX t).resT⟩
      unfold Lift.chrStep at this
      split_ifs at this
      · exact this.2
      · exact this.1
    have hval : ∀ j : Fin D.R.m, ((μ ((j : ℕ) + 1) x : Circle) : ℂ)⁻¹ = D.what₂.embLL (A.muVal j t P : D.what₂.LL) := by
      intro j
      obtain ⟨n, hn⟩ := hres j j.2
      obtain ⟨e', y, a1, a2, a3⟩ := val_conj hn (u2 ((j : ℕ) + 1) (by omega) j.2) he h1 h2 hx
      rw [← Circle.coe_inv, a3, hC.fam.muVal j t P P.2]
      have b1 := (hC.lev.mu0 j).2 _ e' a1 _ y a2
      have b2 := (hC.lev.xi t).2 _ e' a1 _ y a2
      show ((R.mu0 ((j : ℕ) + 1) y * R.xi t y : Circle) : ℂ) =
        (((R.C.mu0 j).locK (R.pl P) (Formalism.L2.Host.unif (R.pl P)) * (R.xiH t).locK (R.pl P) (Formalism.L2.Host.unif (R.pl P)) : ℂˣ) : ℂ)
      rw [Circle.coe_mul, b1, b2, Units.val_mul]
    show _ = Polynomial.map D.what₂.embLL ((List.ofFn fun j : Fin D.R.m => fun P : A.ok t =>
      Formalism.L2.Col.firstValB (fun P : Pl0 => A.muVal j t P) A.q A.r D.R.m A.t P).map fun ν => blockPoly (ν P) (A.q P) A.t).prod
    rw [List.map_ofFn, List.prod_ofFn, Polynomial.map_prod, ← Finset.range_eq_Ico, Finset.prod_range]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, Formalism.L2.Col.map_blockPoly, Formalism.L2.Col.firstValB, map_mul, map_pow, map_natCast]
    rw [c2 j j.2, hval, r1, r2]

end GlobalTheory.Hk3.SplitChain

end
