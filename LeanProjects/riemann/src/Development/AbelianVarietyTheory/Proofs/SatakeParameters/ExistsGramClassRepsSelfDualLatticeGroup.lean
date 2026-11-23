import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSelfEqOneIffOfLinearOrderedCommGroupWithZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteRepresentativesModUniformizerPowStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinsetRepresentativesMulInvIntegralStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteSkewHermitianValuationMaxQuotSumStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmithNormalFormGeneratorsExactOrdersStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralGramCorrectionSkewHermitianMaximalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OneAddMaximalMatrixIntegralInverseStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOneAddSkewHermitianMulLatticeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.VacuumPhaseSubTraceMemIntegersStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralOfTraceCharPairingSkewHermitianStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramDifferenceEntryMemUniformizerPowIntegersStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassEqOfSigmaHermitianFormBoundsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceSkewHermitianGramIntegralStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramHermitianSkewTraceSigmaFixedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SkewConjGramSigmaConjTransposeTraceIdentityStatement
open Matrix

namespace GlobalTheory.Hk3.GramSep

open GlobalTheory.Hk3

theorem gram_class_family : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    (Valued.v δ = 1 ∧ σ δ = -δ) → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
      (∀ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweG.HomA σ JS JT x y ↔
        ∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
      (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
        ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔
          ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) ∧
      (∀ w : Fin n → L, (∃ u v : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, v i ∈ Formalism.UG.intL L) ∧
          w = (a : Matrix (Fin n) (Fin n) L) *ᵥ u + v) ↔
        ∃ v : Fin n → L, ∃ w' : Fin n' → L, (∀ i, v i ∈ Formalism.UG.intL L) ∧ (∀ i, w' i ∈ Formalism.UG.intL L) ∧
          w = v + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') →
    ∃ Y : Finset (Matrix (Fin n') (Fin n) L), x ∈ Y ∧ (∀ y ∈ Y, GlobalTheory.Hk3.HoweG.HomA σ JS JT x y) ∧
      (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → y = y') ∧
      ∃ (B : Type) (_ : AddCommGroup B) (_ : Fintype B) (b0 : B → GL (Fin n) L)
        (l : B → Matrix (Fin n') (Fin n) L → Matrix (Fin n') (Fin n) L),
        (∀ b, GlobalTheory.Hk3.HoweG.SelfDual σ JS (b0 b)) ∧
        (∀ b, ∀ y ∈ Y, l b y ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n ∧
          ∃ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
            y + l b y = u * (((b0 b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∧
        (∀ b, ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
          ∃ y ∈ Y, u * (((b0 b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - (y + l b y) ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n) ∧
        (∀ b b', ∀ y ∈ Y, ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l (b + b') y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l (b + b') y))) / 2)) = ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l b y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l b y))) / 2)) * ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l b' y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l b' y))) / 2))) ∧
        (∀ y ∈ Y, GlobalTheory.Hk3.HoweG.GramEq σ JT x y ↔ ∀ b, ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l b y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l b y))) / 2)) = ψ (-((GlobalTheory.Hk3.locH σ δ JS JT x (l b x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (l b x))) / 2))) := by
  intro L _ _ ϖ σ q δ n n' JS JT ψ hU hodd hSint hTint hS hT hδ hpsi_int hpsi_ne x hx a ha
  obtain ⟨hSD, hHom, hN, hNv⟩ := ha
  classical
  have hσσ : ∀ z, σ (σ z) = z := hU.1
  have hσv : ∀ z, Valued.v (σ z) = Valued.v z := hU.2.1
  have hvϖ := hU.2.2.2.1
  have hϖO : ϖ ∈ Formalism.UG.intL L := by
    show Valued.v ϖ ≤ 1
    rw [hvϖ]
    exact WithZero.coe_le_coe.mpr (Multiplicative.ofAdd_le.mpr (by norm_num))
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hodd
  have hδO : δ ∈ Formalism.UG.intL L := by show Valued.v δ ≤ 1; rw [hδ.1]
  have hSJ : ∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := fun i j => glint_entry hSint i j
  have hSJi : ∀ i j, ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L :=
    fun i j => glint_entry (Subgroup.inv_mem _ hSint) i j
  have hTJ : ∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L := fun i j => glint_entry hTint i j
  have hmv : ∀ {p s : ℕ} (A : Matrix (Fin p) (Fin s) L) (v : Fin s → L), (∀ i j, A i j ∈ Formalism.UG.intL L) →
      (∀ i, v i ∈ Formalism.UG.intL L) → ∀ i, (A *ᵥ v) i ∈ Formalism.UG.intL L := by
    intro p s A v hA hv i
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hv j)

  have hxx : HoweG.HomA σ JS JT x x := by
    refine ⟨fun u _ hxu => hxu, fun w hw i => ?_⟩
    rw [Matrix.mulVec_mulVec]
    refine hmv _ w (fun k l => ?_) hw i
    have e1 : x * HoweG.adj σ JS JT x = (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) *
        (JT : Matrix (Fin n') (Fin n') L) := by
      simp only [HoweG.adj, Formalism.UG.cT, Matrix.mul_assoc]
    rw [e1]
    exact matMul_int hx hTJ k l
  have hxa : ∀ i j, (x * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L := (hHom x).mp hxx

  obtain ⟨r, M, e, he1, hMint, hD1, hD2, hD3⟩ := GlobalTheory.T.exists_smithNormalForm_generators_exactOrders L ϖ hvϖ n a
  have hR := GlobalTheory.T.exists_finite_representatives_mod_uniformizerPow L ϖ σ q hU
  obtain ⟨Y, hxY, hYa, hYd, hYc⟩ := GlobalTheory.T.exists_finset_representatives_mul_inv_integral L ϖ hvϖ hR n n' a x hxa
  haveI hfin := GlobalTheory.T.finite_skewHermitian_valuationMax_quot_sum L ϖ σ hvϖ hR r e
  set G := gam σ ϖ e with hG
  set G0 := (gam0 σ ϖ e).addSubgroupOf G with hG0
  let Γf : (G ⧸ G0) → Matrix (Fin r) (Fin r) L := fun b => ((Quotient.out b : G) : Matrix (Fin r) (Fin r) L)
  have hΓ : ∀ b, Γf b ∈ gam σ ϖ e := fun b => (Quotient.out b).2
  let E : (G ⧸ G0) → Matrix (Fin n) (Fin n) L := fun b => M * Γf b * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)
  have hEi : ∀ b, _ := fun b => GlobalTheory.T.integral_gramCorrection_skewHermitian_maximal L ϖ σ hvϖ hσv n r JS a M e (Γf b) hSJ hSD he1 hMint hD1 (hΓ b)
  have hsk : ∀ b, _ := fun b => GlobalTheory.T.skewConjGram_sigmaConjTranspose_trace_identity L σ hσσ n r JS M (Γf b) hS (hΓ b).1
  choose kf hkf hkinv using fun b => GlobalTheory.T.one_add_maximal_matrix_integral_inverse L n (E b) (hEi b).2.2
  have hEint : ∀ b i j, E b i j ∈ Formalism.UG.intL L := fun b i j => le_of_lt ((hEi b).2.2 i j)

  have hEa : ∀ b, ∀ z : Matrix (Fin n') (Fin n) L, (∀ i j, (z * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
      ∀ i j, (z * E b) i j ∈ Formalism.UG.intL L := by
    intro b z hz i j
    have e1 : z * E b = (z * (a : Matrix (Fin n) (Fin n) L)) * (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * E b) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (a : Matrix (Fin n) (Fin n) L), Units.mul_inv, Matrix.one_mul]
    rw [e1]; exact matMul_int hz (hEi b).1 i j
  have hkk : ∀ b, (((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1 =
      -(E b * (((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
    intro b
    have h1 := Units.mul_inv (kf b)
    rw [hkf b, Matrix.add_mul, Matrix.one_mul] at h1
    calc (((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1
        = ((((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) + E b * (((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) - 1 -
            E b * (((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by abel
      _ = _ := by rw [h1]; abel
  let b0 : (G ⧸ G0) → GL (Fin n) L := fun b => kf b * a
  let l : (G ⧸ G0) → Matrix (Fin n') (Fin n) L → Matrix (Fin n') (Fin n) L :=
    fun b y => y * ((((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1)
  have hb0inv : ∀ b, (((b0 b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    intro b; simp only [b0, _root_.mul_inv_rev, Units.val_mul]
  have hlint : ∀ b, ∀ z : Matrix (Fin n') (Fin n) L, (∀ i j, (z * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
      z * ((((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) ∈ HoweDuality.intMat L n' n := by
    intro b z hz i j
    rw [hkk b, Matrix.mul_neg, ← Matrix.mul_assoc]
    exact (Formalism.UG.intL L).neg_mem (matMul_int (hEa b z hz) (hkinv b) i j)

  let Φ : Matrix (Fin n') (Fin n) L → Matrix (Fin r) (Fin r) L :=
    fun y => Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M)
  let w : (G ⧸ G0) → Matrix (Fin n') (Fin n) L → L := fun b y => δ * Matrix.trace (Γf b * Φ y)
  have hPA : ∀ T w0 : L, T - w0 ∈ Formalism.UG.intL L → σ w0 = w0 → ψ (-((T + σ T) / 2)) = ψ (-w0) := by
    intro T w0 hT0 hw0
    obtain ⟨o, hoO, rfl⟩ : ∃ o, o ∈ Formalism.UG.intL L ∧ T = w0 + o := ⟨T - w0, hT0, by ring⟩
    have hp : (o + σ o) / 2 ∈ Formalism.UG.intL L := by
      show Valued.v ((o + σ o) / 2) ≤ 1
      rw [map_div₀, h2, div_one]
      exact (Valuation.map_add _ _ _).trans (max_le hoO (by show Valued.v (σ o) ≤ 1; rw [hσv]; exact hoO))
    have hpσ : σ (-((o + σ o) / 2)) = -((o + σ o) / 2) := by
      rw [map_neg, map_div₀, map_add, hσσ, map_ofNat]; ring
    have e1 : -(((w0 + o) + σ (w0 + o)) / 2) = -w0 + -((o + σ o) / 2) := by
      have h2ne : (2 : L) ≠ 0 := fun h0 => by rw [h0, map_zero] at h2; exact zero_ne_one h2
      rw [map_add, hw0]; field_simp; ring
    rw [e1, AddChar.map_add_eq_mul, hpsi_int _ ((Formalism.UG.intL L).neg_mem hp) hpσ, mul_one]
  have hkey : ∀ b y, (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
      ψ (-((locH σ δ JS JT y (l b y) + σ (locH σ δ JS JT y (l b y))) / 2)) = ψ (-(w b y)) := by
    intro b y hya
    apply hPA
    · have h1 := GlobalTheory.T.vacuumPhase_sub_trace_mem_integers L σ δ hσv hδO n n' JS a (kf b) JT (E b) y hSJ hSJi hTJ hSD (hsk b).1 (hEi b).1 (hEi b).2.1
        (hkf b) (hkinv b) hya
      rw [(hsk b).2 n' JT y] at h1
      exact h1
    · exact (GlobalTheory.T.gram_hermitian_skewTrace_sigmaFixed L σ δ hσσ hδ.2 n' r JT (y * M) (Γf b) hT (hΓ b).1).2
  have hw0 : ∀ Γ0 ∈ gam0 σ ϖ e, ∀ y, (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
      δ * Matrix.trace (Γ0 * Φ y) ∈ Formalism.UG.intL L ∧ σ (δ * Matrix.trace (Γ0 * Φ y)) = δ * Matrix.trace (Γ0 * Φ y) :=
    fun Γ0 hΓ0 y hya => ⟨GlobalTheory.T.trace_skewHermitian_gram_integral_alt L ϖ σ δ hσv hδO n n' r JT a y M e Γ0 hTJ hya hD1 hΓ0,
      (GlobalTheory.T.gram_hermitian_skewTrace_sigmaFixed L σ δ hσσ hδ.2 n' r JT (y * M) Γ0 hT hΓ0.1).2⟩
  have hψ1 : ∀ s : L, s ∈ Formalism.UG.intL L → σ s = s → ψ s = 1 ∧ ψ (-s) = 1 := fun s hs hσs =>
    ⟨hpsi_int s hs hσs, hpsi_int _ ((Formalism.UG.intL L).neg_mem hs) (by rw [map_neg, hσs])⟩
  have hsplit : ∀ b b', ∃ Γ0 ∈ gam0 σ ϖ e, Γf (b + b') = Γ0 + Γf b + Γf b' := by
    intro b b'
    have h1 : (QuotientAddGroup.mk (Quotient.out b + Quotient.out b') : G ⧸ G0) = QuotientAddGroup.mk (Quotient.out (b + b')) := by
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
    have h3 := QuotientAddGroup.eq.mp h1
    refine ⟨((-(Quotient.out b + Quotient.out b') + Quotient.out (b + b') : G) : Matrix (Fin r) (Fin r) L),
      (AddSubgroup.mem_addSubgroupOf).mp h3, ?_⟩
    simp only [Γf, AddSubgroup.coe_add, AddSubgroup.coe_neg]; abel

  have hψne : ∀ z : L, ψ z ≠ 0 := fun z h0 => by
    have := AddChar.map_add_eq_mul ψ z (-z)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
    exact one_ne_zero this
  refine ⟨Y, hxY, fun y hy => (hHom y).mpr (hYa y hy), hYd, G ⧸ G0, inferInstance, Fintype.ofFinite _, b0, l,
    fun b => GlobalTheory.T.selfDual_one_add_skewHermitian_mul_lattice L σ hσv n JS a (kf b) (E b) hSJ hSD (hsk b).1 (hEint b) (hEi b).2.1 (hkf b) (hkinv b),
    fun b y hy => ⟨hlint b y (hYa y hy), y * (a : Matrix (Fin n) (Fin n) L), hYa y hy, ?_⟩,
    fun b u hu => ?_, fun b b' y hy => ?_, fun y hy => ?_⟩
  ·
    rw [hb0inv b, Matrix.mul_assoc, ← Matrix.mul_assoc (a : Matrix (Fin n) (Fin n) L), Units.mul_inv, Matrix.one_mul]
    simp only [l, Matrix.mul_sub, Matrix.mul_one]; abel
  ·
    obtain ⟨y, hy, hz⟩ := hYc u hu
    refine ⟨y, hy, ?_⟩
    set z := u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - y with hzdef
    have hza : ∀ i j, (z * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L := by
      intro i j
      have e1 : z * (a : Matrix (Fin n) (Fin n) L) = u - y * (a : Matrix (Fin n) (Fin n) L) := by
        rw [hzdef, Matrix.sub_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [e1]; exact (Formalism.UG.intL L).sub_mem (hu i j) (hYa y hy i j)
    have e2 : u * (((b0 b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - (y + l b y) =
        z + z * ((((kf b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) := by
      rw [hb0inv b, hzdef]
      simp only [l, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]; abel
    rw [e2]
    exact (HoweDuality.intMat L n' n).add_mem hz (hlint b z hza)
  ·
    have hya := hYa y hy
    rw [hkey _ _ hya, hkey _ _ hya, hkey _ _ hya]
    obtain ⟨Γ0, hΓ0, hsum⟩ := hsplit b b'
    have e1 : -(w (b + b') y) = -(δ * Matrix.trace (Γ0 * Φ y)) + (-(w b y) + -(w b' y)) := by
      simp only [w, hsum, Matrix.add_mul, Matrix.trace_add]; ring
    obtain ⟨h0i, h0f⟩ := hw0 Γ0 hΓ0 y hya
    rw [e1, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, (hψ1 _ h0i h0f).2, one_mul]
  ·
    have hya := hYa y hy
    have hΔh : ∀ j k, σ ((Φ y - Φ x) j k) = (Φ y - Φ x) k j := by
      intro j k
      simp only [Matrix.sub_apply, map_sub]
      rw [(GlobalTheory.T.gram_hermitian_skewTrace_sigmaFixed L σ δ hσσ hδ.2 n' r JT (y * M) 0 hT (fun _ _ => by simp)).1 j k,
        (GlobalTheory.T.gram_hermitian_skewTrace_sigmaFixed L σ δ hσσ hδ.2 n' r JT (x * M) 0 hT (fun _ _ => by simp)).1 j k]
    have hwd : ∀ b, w b y - w b x = δ * Matrix.trace (Γf b * (Φ y - Φ x)) := by
      intro b; simp only [w, Matrix.mul_sub, Matrix.trace_sub]; ring
    have hfix : ∀ b, σ (δ * Matrix.trace (Γf b * (Φ y - Φ x))) = δ * Matrix.trace (Γf b * (Φ y - Φ x)) := by
      intro b
      rw [← hwd, map_sub, (GlobalTheory.T.gram_hermitian_skewTrace_sigmaFixed L σ δ hσσ hδ.2 n' r JT (y * M) (Γf b) hT (hΓ b).1).2,
        (GlobalTheory.T.gram_hermitian_skewTrace_sigmaFixed L σ δ hσσ hδ.2 n' r JT (x * M) (Γf b) hT (hΓ b).1).2]
    constructor
    · intro hg b
      rw [hkey _ _ hya, hkey _ _ hxa]
      have hb := GlobalTheory.T.gramDifference_entry_mem_uniformizerPow_integers L ϖ σ n n' r JT a x y M e hϖO hN hMint hD1 hg
      have hint : δ * Matrix.trace (Γf b * (Φ y - Φ x)) ∈ Formalism.UG.intL L := by
        refine Subring.mul_mem _ hδO ?_
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
        refine Subring.sum_mem _ fun k _ => Subring.sum_mem _ fun j _ => ?_
        show Valued.v (Γf b k j * (Φ y - Φ x) j k) ≤ 1
        calc Valued.v (Γf b k j * (Φ y - Φ x) j k) = Valued.v (Γf b k j) * Valued.v ((Φ y - Φ x) j k) := map_mul _ _ _
          _ ≤ Valued.v ϖ ^ max (e k) (e j) * Valued.v ((Φ y - Φ x) j k) := mul_le_mul_of_nonneg_right ((hΓ b).2 k j) zero_le'
          _ = Valued.v ((Φ y - Φ x) j k * ϖ ^ max (e j) (e k)) := by rw [map_mul, map_pow, max_comm, mul_comm]
          _ ≤ 1 := hb j k
      have e1 : -(w b y) = -(w b x) + -(w b y - w b x) := by ring
      rw [e1, AddChar.map_add_eq_mul, hwd, (hψ1 _ hint (hfix b)).2, mul_one]
    · intro hb
      have hb' : ∀ b, ψ (-(w b y)) = ψ (-(w b x)) := fun b => (hkey b y hya).symm.trans ((hb b).trans (hkey b x hxa))
      refine GlobalTheory.T.gramClassEq_of_sigmaHermitianForm_bounds L ϖ σ hσσ hσv hϖO n n' r JT a x y M e hTJ hT hN hxa hya hMint hD1 hD2 hD3
        (GlobalTheory.T.integral_of_traceCharPairing_skewHermitian L ϖ σ q δ ψ hU hδ hpsi_ne r e _ hΔh ?_)
      intro Γ hΓm
      let bb : G ⧸ G0 := QuotientAddGroup.mk (⟨Γ, hΓm⟩ : G)
      have hq : -(⟨Γ, hΓm⟩ : G) + Quotient.out bb ∈ G0 :=
        QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' bb).symm
      have hΓ0 : -Γ + Γf bb ∈ gam0 σ ϖ e := (AddSubgroup.mem_addSubgroupOf).mp hq
      have h1 : ψ (w bb y - w bb x) * ψ (-(w bb y)) = ψ (-(w bb y)) := by
        rw [← AddChar.map_add_eq_mul, show w bb y - w bb x + -(w bb y) = -(w bb x) by ring]
        exact (hb' bb).symm
      have h1' : ψ (w bb y - w bb x) = 1 := mul_right_cancel₀ (hψne _) (by rw [h1, one_mul])
      obtain ⟨hiy, hfy⟩ := hw0 _ hΓ0 y hya
      obtain ⟨hix, hfx⟩ := hw0 _ hΓ0 x hxa
      have hs : δ * Matrix.trace ((-Γ + Γf bb) * Φ y) - δ * Matrix.trace ((-Γ + Γf bb) * Φ x) ∈ Formalism.UG.intL L :=
        (Formalism.UG.intL L).sub_mem hiy hix
      have hsf : σ (δ * Matrix.trace ((-Γ + Γf bb) * Φ y) - δ * Matrix.trace ((-Γ + Γf bb) * Φ x)) =
          δ * Matrix.trace ((-Γ + Γf bb) * Φ y) - δ * Matrix.trace ((-Γ + Γf bb) * Φ x) := by
        rw [map_sub, hfy, hfx]
      have e2 : δ * Matrix.trace (Γ * (Φ y - Φ x)) = (w bb y - w bb x) +
          -(δ * Matrix.trace ((-Γ + Γf bb) * Φ y) - δ * Matrix.trace ((-Γ + Γf bb) * Φ x)) := by
        simp only [w, Matrix.mul_sub, Matrix.add_mul, Matrix.neg_mul, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_neg]
        ring
      rw [e2, AddChar.map_add_eq_mul, h1', (hψ1 _ hs hsf).2, one_mul]

end GlobalTheory.Hk3.GramSep
