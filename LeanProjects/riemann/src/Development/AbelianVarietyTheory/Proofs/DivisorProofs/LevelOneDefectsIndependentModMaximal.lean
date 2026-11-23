import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpPull2Cob1
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmulSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentLinearKillsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstFormalGroupLawNatMultipleEqCoboundarySumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPowerSeriesFamilyToFractionsFormalGroupLawNatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstOfForallConstantCoeffZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualBasisCoordMemMaximalIdealOfForallApplyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiLogarithmBasisReductionThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmTangentVectorsBasisDualLieStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LevelOneIndep

variable {B Q O C : Type} [CommRing B] [CommRing Q] [CommRing O] [CommRing C] [Algebra B Q] [Algebra O C]
  {d : ℕ}

theorem map_up (θ : B →+* O) (Θ : Q →+* C) (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    {τ : Type} (u : MvPowerSeries τ B) :
    map Θ (map (algebraMap B Q) u) = map (algebraMap O C) (map θ u) := by
  ext α; simp [coeff_map, hΘ]

theorem map_formalGroupLawCoboundaryOne_square (θ : B →+* O) (Θ : Q →+* C) (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (hν : ∀ i, map θ (μ i) = ν i) (f : MvPowerSeries (Fin d) Q) :
    map Θ (cob1 (up Q μ) f) = cob1 (up C ν) (map Θ f) := by
  rw [← ExtCoeff.map_formalGroupLawCoboundaryOne_eq Θ (up Q μ) f (fun i => by simp [up, hμ])]
  congr 1
  funext i
  simp only [up]
  rw [map_up θ Θ hΘ, hν]

theorem map_defect (θ : B →+* O) (Θ : Q →+* C) (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (hν : ∀ i, map θ (μ i) = ν i) (n : ℕ)
    (f : MvPowerSeries (Fin d) Q) :
    map Θ (defect μ n f) = defect ν n (map Θ f) := by
  have hs : HasSubst (up Q (nmul μ n)) :=
    hasSubst_of_constantCoeff_zero fun i => by simp [up, MapNMul.cc_nmul μ hμ]
  unfold defect
  rw [map_sub, map_subst hs]
  congr 1
  · ext α; simp [coeff_map]
  · congr 1
    funext i
    simp only [up]
    rw [map_up θ Θ hΘ, MapNMul.map_nmul B O θ d μ hμ]
    congr 2
    funext j
    exact hν j

theorem constantCoeff_formalGroupLawCoboundaryOne {R : Type} [CommRing R] (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (g : MvPowerSeries (Fin d) R) :
    constantCoeff (cob1 μ g) = - constantCoeff g := by
  simp only [cob1, inL, inR, map_sub]
  rw [GlobalTheory.T.constantCoeff_subst_of_forall_constantCoeff_zero R _ _ _ hμ, GlobalTheory.T.constantCoeff_subst_of_forall_constantCoeff_zero R _ _ _ (fun _ => constantCoeff_X _),
    GlobalTheory.T.constantCoeff_subst_of_forall_constantCoeff_zero R _ _ _ (fun _ => constantCoeff_X _)]
  ring

theorem defect_add (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hν : ∀ i, constantCoeff (ν i) = 0)
    (n : ℕ) (f g : MvPowerSeries (Fin d) C) :
    defect ν n (f + g) = defect ν n f + defect ν n g := by
  have hs : HasSubst (up C (nmul ν n)) :=
    hasSubst_of_constantCoeff_zero fun i => by simp [up, MapNMul.cc_nmul ν hν]
  unfold defect
  rw [subst_add hs, smul_add]
  abel

theorem defect_log (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hν : ∀ i, constantCoeff (ν i) = 0)
    (n : ℕ) (g : MvPowerSeries (Fin d) C) (hg : cob1 (up C ν) g = 0) : defect ν n g = 0 := by
  have hνC : ∀ i, constantCoeff (up C ν i) = 0 := fun i => by simp [up, hν]
  have hc : constantCoeff g = 0 := by
    have := constantCoeff_formalGroupLawCoboundaryOne (up C ν) hνC g
    rw [hg, map_zero] at this
    exact neg_eq_zero.1 this.symm
  unfold defect
  rw [GlobalTheory.T.mapPowerSeriesFamilyToFractions_formalGroupLawNatMultiple O C d ν hν n, GlobalTheory.T.subst_formalGroupLawNatMultiple_eq_coboundary_sum C d (up C ν) hνC g n, hg, hc]
  have h0 : ∀ k, (at2 (0 : MvPowerSeries (Fin d ⊕ Fin d) C) (nmul (up C ν) k) fun i => X i) = 0 := by
    intro k
    have ha : HasSubst (Sum.elim (nmul (up C ν) k) fun i => (X i : MvPowerSeries (Fin d) C)) :=
      hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [MapNMul.cc_nmul _ hνC]
    unfold at2
    rw [← coe_substAlgHom ha, map_zero]
  simp [h0]

end GlobalTheory.LevelOneIndep

namespace GlobalTheory.LevelOneIndep

theorem map_smul' {Q C : Type} [CommRing Q] [CommRing C] (Θ : Q →+* C) {τ : Type} (r : Q)
    (g : MvPowerSeries τ Q) : map Θ (r • g) = Θ r • map Θ g := by
  ext α; simp [coeff_map]

theorem QL_map {B Q O C : Type} [CommRing B] [CommRing Q] [CommRing O] [CommRing C] [Algebra B Q]
    [Algebra O C] {d : ℕ} (θ : B →+* O) (Θ : Q →+* C)
    (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (hν : ∀ i, map θ (μ i) = ν i) (f : MvPowerSeries (Fin d) Q)
    (hf : QL μ ⊤ f) : QL ν ⊤ (map Θ f) := by
  refine ⟨?_, fun i => ?_, fun α => ?_⟩
  · rw [constantCoeff_map, hf.1, map_zero]
  · obtain ⟨b, -, hb⟩ := hf.2.1 i
    refine ⟨θ b, trivial, ?_⟩
    simp only [lin] at hb ⊢
    rw [coeff_map, hb, hΘ]
  · obtain ⟨b, -, hb⟩ := hf.2.2 α
    refine ⟨θ b, trivial, ?_⟩
    rw [← map_formalGroupLawCoboundaryOne_square θ Θ hΘ μ ν hμ hν, coeff_map, hb, hΘ]

theorem QL_comb' (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f g : MvPowerSeries (Fin d) E) (a : O) (hf : QL μ ⊤ f) (hg : QL μ ⊤ g) :
    QL μ ⊤ (f + algebraMap O E a • g) := by
  have hμE : ∀ i, constantCoeff (up E μ i) = 0 := fun i => by simp [up, hμ]
  refine ⟨?_, fun i => ?_, fun α => ?_⟩
  · simp [hf.1, hg.1]
  · obtain ⟨x, -, hx⟩ := hf.2.1 i
    obtain ⟨y, -, hy⟩ := hg.2.1 i
    refine ⟨x + a * y, trivial, ?_⟩
    simp only [lin] at hx hy ⊢
    rw [map_add, coeff_smul, hx, hy, map_add, map_mul]
  · obtain ⟨x, -, hx⟩ := hf.2.2 α
    obtain ⟨y, -, hy⟩ := hg.2.2 α
    refine ⟨x + a * y, trivial, ?_⟩
    rw [formalCoboundary_add hμE, formalCoboundary_smul hμE, map_add, coeff_smul, hx, hy, map_add, map_mul]

theorem isLie_comb (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O) (G : PDivGroup p O)
    (d : ℕ) (c : QLog.Chart G d) (E : Type) [CommRing E] [Algebra O E] (hF : IsFrame p E (RingHom.id O))
    (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Fin k → G.dual.Lie)
    (hQL : ∀ i, QL c.μ ⊤ (e i)) (hLie : ∀ j, c.IsLie (e (Sum.inr j)) (lb j)) (b : Fin k → O) :
    c.IsLie (comb (Sum.elim 0 b) e) (∑ j, b j • lb j) := by
  have hμ : ∀ i, constantCoeff (c.μ i) = 0 := c.isLaw.const
  have lin : ∀ (f g : MvPowerSeries (Fin d) E) (l l' : G.dual.Lie) (a : O), c.IsLie f l → c.IsLie g l' →
      QL c.μ ⊤ f → QL c.μ ⊤ g → c.IsLie (f + algebraMap O E a • g) (l + a • l') :=
    fun f g l l' a hf hg => (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hF f g l l' a hf hg).1
  have hQL0 : QL c.μ ⊤ (0 : MvPowerSeries (Fin d) E) := by
    refine ⟨by simp, fun i => ⟨0, trivial, by simp [Katz.lin]⟩, fun α => ⟨0, trivial, ?_⟩⟩
    have := formalCoboundary_smul (fun i => by simp [up, hμ] : ∀ i, constantCoeff (up E c.μ i) = 0) 0
      (0 : MvPowerSeries (Fin d) E)
    rw [zero_smul, zero_smul] at this
    rw [this]; simp
  have h00 : c.IsLie (0 : MvPowerSeries (Fin d) E) 0 := by
    have hd : ∀ n : ℕ, defect c.μ (p ^ n) (0 : MvPowerSeries (Fin d) E) = 0 := by
      intro n
      have ha : HasSubst (up E (nmul c.μ (p ^ n))) :=
        hasSubst_of_constantCoeff_zero fun i => by simp [up, MapNMul.cc_nmul c.μ hμ]
      unfold defect
      rw [← coe_substAlgHom ha, map_zero, smul_zero, sub_zero]
    refine ⟨fun n α => ⟨0, trivial, by rw [hd]; simp⟩, ?_⟩
    intro n w φ s _ hs
    have hs0 : s = 0 := by
      rw [hd] at hs
      ext α
      have := congrArg (coeff α) hs
      rw [coeff_map, map_zero] at this
      apply hF.inj
      rw [this]
      simp
    subst hs0
    simp
  have hsum : ∀ S : Finset (Fin k), QL c.μ ⊤ (∑ i ∈ S, algebraMap O E (b i) • e (Sum.inr i)) ∧
      c.IsLie (∑ i ∈ S, algebraMap O E (b i) • e (Sum.inr i)) (∑ i ∈ S, b i • lb i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      exact ⟨by simpa using hQL0, by simpa using h00⟩
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, add_comm (b a • lb a)]
      exact ⟨QL_comb' O E d c.μ hμ _ _ (b a) ih.1 (hQL _), lin _ _ _ _ (b a) ih.2 (hLie a) ih.1 (hQL _)⟩
  have hf_eq : comb (Sum.elim 0 b) e = ∑ i, algebraMap O E (b i) • e (Sum.inr i) := by
    simp [comb, Fintype.sum_sum_type]
  rw [hf_eq]
  exact (hsum Finset.univ).2

theorem span_le_smul {O : Type} [CommRing O] (A : Type) [CommRing A] [Algebra O A] (I : Ideal O)
    (S : Set O) (hS : ∀ o ∈ S, o ∈ I) (x : A) (hx : x ∈ Ideal.span (algebraMap O A '' S)) :
    x ∈ I • (⊤ : Submodule O A) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨o, ho, rfl⟩ := hy
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem_smul (hS o ho) trivial
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_eq_mul]
    exact Submodule.smul_induction_on (p := fun t => a * t ∈ I • (⊤ : Submodule O A)) hy
      (fun r hr t _ => by rw [mul_smul_comm]; exact Submodule.smul_mem_smul hr trivial)
      (fun u w hu hw => by rw [mul_add]; exact add_mem hu hw)

end GlobalTheory.LevelOneIndep

namespace GlobalTheory.LevelOneIndep

theorem defect_level_one_nonunit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ (w : Fin d ⊕ Fin k → F.B) (a : MvPowerSeries (Fin d) F.B), map (algebraMap F.B F.Q) a = defect μ' p (comb w e) → c.ev 1 (map F.θ a) ∈ Ideal.span (algebraMap O (G.A 1) '' {o | ¬IsUnit o}) → ∀ j, ¬IsUnit (F.θ (w (Sum.inr j))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hmap k e hbasis hadapt w a ha hev j
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hmem : ∀ o : O, o ∈ IsLocalRing.maximalIdeal O ↔ ¬IsUnit o := fun o =>
    IsLocalRing.mem_maximalIdeal o
  have hpm : (p : O) ∈ IsLocalRing.maximalIdeal O := (hmem _).2 Fact.out
  have hE := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  obtain ⟨Θ, hΘ⟩ := GlobalTheory.QLog.frame_fraction_map p F.B O F.Q F.θ F.frame C hE
  have hμ' : ∀ i, constantCoeff (μ' i) = 0 := hlift.const
  have hμ : ∀ i, constantCoeff (c.μ i) = 0 := c.isLaw.const
  have hμC : ∀ i, constantCoeff (up C c.μ i) = 0 := fun i => by simp [up, hμ]
  set e' : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C := fun l => map Θ (e l) with he'
  have hQL : ∀ l, QL c.μ ⊤ (e' l) := fun l => QL_map F.θ Θ hΘ μ' c.μ hμ' hmap _ (hbasis.1 l)
  have hlog : ∀ i, cob1 (up C c.μ) (e' (Sum.inl i)) = 0 := by
    intro i
    ext α
    obtain ⟨b, hb, hbα⟩ := (hadapt i).1 α
    rw [he', ← map_formalGroupLawCoboundaryOne_square F.θ Θ hΘ μ' c.μ hμ' hmap, coeff_map, hbα, hΘ, RingHom.mem_ker.1 hb,
      map_zero, map_zero]
  obtain ⟨lb, hlb⟩ := GlobalTheory.T.quasiLogarithm_tangentVectors_basis_dual_lie p C v O hv G d c C hE k e'
    (GlobalTheory.T.isQuasiLogarithmBasis_reduction_thickening p C v O hv ε hε F G d c μ' hlift hmap k e hbasis Θ hΘ) hlog
  set b : Fin k → O := fun j => F.θ (w (Sum.inr j)) with hb
  set f := comb (Sum.elim 0 b) e' with hf
  set L : G.dual.Lie := ∑ j, b j • lb j with hL
  have hfl : c.IsLie f L := isLie_comb p C v O hv G d c C hE k e' lb hQL hlb b
  have hlogcomb : cob1 (up C c.μ) (comb (Sum.elim (fun i => F.θ (w (Sum.inl i))) 0) e') = 0 := by
    let Φ : MvPowerSeries (Fin d) C →+ MvPowerSeries (Fin d ⊕ Fin d) C :=
      AddMonoidHom.mk' (cob1 (up C c.μ)) (formalCoboundary_add hμC)
    change Φ (comb _ e') = 0
    unfold comb
    rw [map_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    change cob1 (up C c.μ) _ = 0
    rw [formalCoboundary_smul hμC]
    cases l with
    | inl i => rw [hlog, smul_zero]
    | inr j => simp
  have hsplit : map Θ (comb w e) = comb (Sum.elim (fun i => F.θ (w (Sum.inl i))) 0) e' + f := by
    have h1 : map Θ (comb w e) = ∑ l, algebraMap O C (F.θ (w l)) • e' l := by
      unfold comb
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul', hΘ]
    rw [h1, hf]
    unfold comb
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [hb]
  have hs : map (algebraMap O C) (map F.θ a) = defect c.μ (p ^ 1) f := by
    rw [← map_up F.θ Θ hΘ, ha, map_defect F.θ Θ hΘ μ' c.μ hμ' hmap, pow_one, hsplit,
      defect_add _ hμ, defect_log _ hμ _ _ hlogcomb, zero_add]
  have key : ∀ w0 : G.dual.omega, L w0 ∈ IsLocalRing.maximalIdeal O := by
    intro w0
    obtain ⟨φ₀, hφ₀⟩ := AugCot.d_surjective _ (w0.1 1)
    set φ : CartierDual O (G.A 1) := φ₀ - algebraMap O _ (Coalgebra.counit (R := O) φ₀) with hφdef
    have hφd : PDiv.dUnit O φ = w0.1 1 := by
      rw [hφdef, PDiv.dUnit, map_sub, AugCot.d_algebraMap, sub_zero]; exact hφ₀
    obtain ⟨q, hq⟩ := hfl.2 1 w0 φ (map F.θ a) hφd hs
    have hx := span_le_smul (G.A 1) (IsLocalRing.maximalIdeal O) {o | ¬IsUnit o}
      (fun o ho => (hmem o).2 ho) _ hev
    have hle : IsLocalRing.maximalIdeal O • (⊤ : Submodule O (G.A 1)) ≤
        Submodule.comap φ.ofConv (IsLocalRing.maximalIdeal O) :=
      Submodule.smul_le.2 fun r hr x _ => by
        rw [Submodule.mem_comap, map_smul, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
    have hφm : φ (c.ev 1 (map F.θ a)) ∈ IsLocalRing.maximalIdeal O := hle hx
    have : L w0 = (p : O) ^ 1 * q + φ (c.ev 1 (map F.θ a)) := by rw [← hq]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (by simpa using hpm)) hφm
  obtain ⟨hfin, hproj⟩ := GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual
  have h6 := GlobalTheory.T.dualBasis_coord_mem_maximalIdeal_of_forall_apply O G.dual.omega k lb L key j
  have hrep : lb.repr L j = b j := by
    have : L = lb.equivFun.symm b := by rw [Module.Basis.equivFun_symm_apply]
    rw [← Module.Basis.equivFun_apply, this, LinearEquiv.apply_symm_apply]
  rw [hrep] at h6
  exact (hmem _).1 h6

end GlobalTheory.LevelOneIndep
