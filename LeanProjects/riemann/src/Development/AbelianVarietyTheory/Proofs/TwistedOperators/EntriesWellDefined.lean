import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingAffPtUncurry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SecondCountableLocal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpEOmTargetUnipotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharEqOneOfOpENeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCOPrXCgrpStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsParabolicDoubleCosetFunctionEqOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentExistsResidueCardPowMemNhdsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarCompactOpenRatioEqZpowOfTopNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicHaarVolumeConjIntersectionEqMulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralTranslateIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsQuotIntCosetFnStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdaptedExponentSchwartzBruhatLastColumnStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteQuotientCosetsScaledStandardLatticeBoxStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenericLevelOfFrameStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSymmetricPositionLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericLevelOfFrameBlockAndCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetricPositionLevelShapeOnParabolicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexIteratedLevelChainInFrameStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexParahoricLevelChainTwistStatement

open MeasureTheory ValuativeRel Matrix Topology
open scoped ENNReal

noncomputable section
namespace GlobalTheory.UnfoldedEntries
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Basic
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem om_smul (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) (z : ℂ) (Φ : Matrix b a k → ℂ) :
    om μ g h (z • Φ) = z • om μ g h Φ := by
  funext x; simp only [om, Pi.smul_apply, smul_eq_mul]; ring

theorem om_ne_zero (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) {Φ : Matrix b a k → ℂ} :
    om μ g h Φ ≠ 0 ↔ Φ ≠ 0 := by
  refine not_congr ⟨fun H => ?_, fun H => ?_⟩
  · have := om_mul μ g⁻¹ g h⁻¹ h Φ
    rw [inv_mul_cancel, inv_mul_cancel, om_one, H] at this
    rw [this]; simpa using om_smul μ g⁻¹ h⁻¹ 0 Φ
  · rw [H]; simpa using om_smul μ g h 0 Φ

theorem exists_of_mem_R {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ} {r : GL (n ⊕ Fin c) k}
    (hr : r ∈ R k n c p) : ∃ u ∈ N k n c p, ∃ g, r = u * embX c g := by
  obtain ⟨x, u, hu, rfl⟩ := Radical.exists_of_mem_R hr
  exact ⟨_, Radical.conj_mem x hu, x, by simp⟩

end Basic

section Step
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k}
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
  {μ : kˣ →* ℂˣ} {P' : Level (GL (n' ⊕ Fin (c + 1)) k)} {P : Level (GL (n ⊕ Fin c) k)}
  {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}

omit [BorelSpace k] [DecidableEq n] [DecidableEq n'] in
theorem opE_smul (p : ℕ) (z : ℂ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) :
    opE ψ ν p (z • Φ) = z • opE ψ ν p Φ := by
  funext x
  simp only [opE, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

variable [ν.IsAddHaarMeasure]

theorem flat_source (hc : 1 ≤ c) (H : HasTypes μ P' P Φ) {u' : GL (n' ⊕ Fin (c + 1)) k} (hu : u' ∈ N k n' (c + 1) 1)
    (g' : GL n' k) (j' : P'.J) (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k) :
    flat ψ ν μ Φ (u' * embX (c + 1) g' * h' * (j' : GL (n' ⊕ Fin (c + 1)) k)) h =
      ((P'.lam j' : ℂ) * (ψ (simpleSum u') : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det g') ^ ((c : ℝ) / 2) : ℝ) : ℂ)) • om μ g' 1 (flat ψ ν μ Φ h' h) := by
  have e : om μ (u' * embX (c + 1) g' * h' * (j' : GL (n' ⊕ Fin (c + 1)) k)) h Φ =
      om μ u' 1 (om μ (embX (c + 1) g') 1 (om μ h' h (om μ (j' : GL (n' ⊕ Fin (c + 1)) k) 1 Φ))) := by
    rw [← om_mul, ← om_mul, ← om_mul]; simp
  unfold flat
  rw [e, RootExSource.opE_om_source k n n' c 1 le_rfl hc ψ ν μ _ _ hu,
    (opE_om_embX k n n' c 1 le_rfl hc ψ ν μ _).2, H.1, om_smul, opE_smul, om_smul, smul_smul, smul_smul,
    show ((c : ℝ) + 2) / 2 - (1 : ℕ) = c / 2 by push_cast; ring]
  congr 1; ring

theorem flat_target (hc : 1 ≤ c) (H : HasTypes μ P' P Φ) {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c 1)
    (g : GL n k) (j : P.J) (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k) :
    flat ψ ν μ Φ h' (u * embX c g * h * (j : GL (n ⊕ Fin c) k)) =
      ((((P.lam j)⁻¹ : ℂˣ) : ℂ) * (ψ (-simpleSum u) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - 1) : ℝ) : ℂ)) •
          om μ 1 g (flat ψ ν μ Φ h' h) := by
  have e : om μ h' (u * embX c g * h * (j : GL (n ⊕ Fin c) k)) Φ =
      om μ 1 u (om μ 1 (embX c g) (om μ h' h (om μ 1 (j : GL (n ⊕ Fin c) k) Φ))) := by
    rw [← om_mul, ← om_mul, ← om_mul]; simp
  unfold flat
  rw [e, opE_om_target_unipotent k n n' c 1 le_rfl hc ψ ν μ _ _ hu,
    (opE_om_embX k n n' c 1 le_rfl hc ψ ν μ _).1, H.2, om_smul, opE_smul, om_smul, smul_smul, smul_smul,
    Nat.cast_one]
  congr 1; ring

theorem flat_ne_zero_congr (hc : 1 ≤ c) (H : HasTypes μ P' P Φ) {h₁' h₂' : GL (n' ⊕ Fin (c + 1)) k}
    {h₁ h₂ : GL (n ⊕ Fin c) k}
    (e' : DoubleCoset.mk (R k n' (c + 1) 1) P'.J h₁' = DoubleCoset.mk (R k n' (c + 1) 1) P'.J h₂')
    (e : DoubleCoset.mk (R k n c 1) P.J h₁ = DoubleCoset.mk (R k n c 1) P.J h₂) :
    flat ψ ν μ Φ h₁' h₁ ≠ 0 ↔ flat ψ ν μ Φ h₂' h₂ ≠ 0 := by
  obtain ⟨r', hr', j', hj', rfl⟩ := (DoubleCoset.eq _ _ _ _).1 e'
  obtain ⟨r, hr, j, hj, rfl⟩ := (DoubleCoset.eq _ _ _ _).1 e
  obtain ⟨u', hu', g', rfl⟩ := exists_of_mem_R hr'
  obtain ⟨u, hu, g, rfl⟩ := exists_of_mem_R hr
  have n1 : ∀ (x : kˣ) (t : ℝ), ((nabs k x ^ t : ℝ) : ℂ) ≠ 0 := fun x t =>
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (nabs_pos k x) _).ne'
  have n2 : ∀ (l : ℂˣ) (z : Circle) (x : kˣ) (t : ℝ) (f : Matrix n n' k → ℂ),
      ((l : ℂ) * (z : ℂ) * ((nabs k x ^ t : ℝ) : ℂ)) • f ≠ 0 ↔ f ≠ 0 := fun l z x t f => by
    rw [smul_ne_zero_iff, and_iff_right (mul_ne_zero (mul_ne_zero l.ne_zero z.coe_ne_zero) (n1 x t))]
  rw [flat_source hc H hu' g' ⟨j', hj'⟩, flat_target hc H hu g ⟨j, hj⟩,
    n2 _ _ _ _, om_ne_zero, n2 _ _ _ _, om_ne_zero]

theorem mem_idxAt (hc : 1 ≤ c) (H : HasTypes μ P' P Φ) {h' : GL (n' ⊕ Fin (c + 1)) k} {h : GL (n ⊕ Fin c) k} :
    DoubleCoset.mk (R k n c 1) P.J h ∈ idxAt ψ ν μ Φ P.J h' ↔ flat ψ ν μ Φ h' h ≠ 0 :=
  ⟨fun ⟨_, e, h0⟩ => (flat_ne_zero_congr hc H rfl e).1 h0, fun h0 => ⟨h, rfl, h0⟩⟩

theorem idxAt_finite (hψ : HasConductor ψ 1) (hc : 1 ≤ c) (hΦ : Φ ∈ SB _) {J : Subgroup (GL (n ⊕ Fin c) k)}
    (hJ : IsOpen (J : Set (GL (n ⊕ Fin c) k))) (h' : GL (n' ⊕ Fin (c + 1)) k) : (idxAt ψ ν μ Φ J h').Finite := by
  have hΨ := om_mem_SB μ h' 1 hΦ
  obtain ⟨Λ, hΛ, hinv⟩ := sb_matrix_exists_isOpen_addSubgroup k _ _ _ hΨ
  obtain ⟨Ω, hΩ, hs⟩ := opE_support_compact_mod_R k n n' c 1 le_rfl hc ψ hψ.continuous hψ.ne_one ν _ hΨ.2 Λ hΛ
  obtain ⟨S, hS⟩ := QuotInt.finite_quot J hJ hΩ
  refine (S.finite_toSet.image fun q => DoubleCoset.mk (R k n c 1) J q.out).subset ?_
  rintro _ ⟨h, rfl, h0⟩
  obtain ⟨x₀, hx⟩ := Function.ne_iff.1 h0
  obtain ⟨r, hr, w, hw, rfl⟩ := hs μ _ (subset_tsupport _) hinv (fun _ => 1) (IsLocallyConstant.const 1) h x₀ (by
    simp only [one_mul]
    rw [show (fun x => om μ 1 h (om μ h' 1 Φ) x) = om μ h' h Φ by rw [← om_mul]; simp]
    exact hx)
  refine ⟨(w : _ ⧸ J), hS w hw, (DoubleCoset.eq _ _ _ _).2 ⟨r, hr, ((w : _ ⧸ J).out)⁻¹ * w, ?_, by simp [mul_assoc]⟩⟩
  exact QuotientGroup.eq.1 (QuotientGroup.out_eq' _)

theorem stepWellDefined (hψ : HasConductor ψ 1) : StepWellDefined ψ ν := by
  intro n n' _ _ _ _ c hc μ P' P Φ hΦ _ hJ H
  refine ⟨fun h' h => opE_mem_SB 1 ψ ν (om_mem_SB μ h' h hΦ), idxAt_finite hψ hc hΦ hJ.1,
    fun u hu => flat_source hc H hu, fun u hu => flat_target hc H hu,
    fun _ _ _ _ => flat_ne_zero_congr hc H, fun h₁' h₂' e => ?_, fun b h' h => ?_⟩
  · ext β
    exact exists_congr fun h => and_congr_right fun _ => flat_ne_zero_congr hc H e rfl
  · rw [mem_idxAt hc H, Ne, xi_eq_zero_iff ψ ν μ Φ hJ.1 hJ.2]

theorem nabs_det_of_mem {J : Subgroup (GL (n ⊕ Fin c) k)} (hJ : IsCO J) {h u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c 1)
    {g : GL n k} (hm : h⁻¹ * (u * embX c g) * h ∈ J) : nabs k (Matrix.GeneralLinearGroup.det g) = 1 :=
  nabs_eq_one_of_valuation_eq_one (((T.isCO_prX_Cgrp_and_det_valuation_deltaR_eq_one k n c J hJ h).2 g ⟨u, hu, mem_Cgrp.2
    ⟨mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left ⟨g, rfl⟩), hm⟩⟩).1)

theorem target_law (hc : 1 ≤ c) (hJ : IsCO P.J) (H : HasTypes μ P' P Φ) (h' : GL (n' ⊕ Fin (c + 1)) k)
    (h : GL (n ⊕ Fin c) k) {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c 1) (g : GL n k)
    (hm : h⁻¹ * (u * embX c g) * h ∈ P.J) :
    om μ 1 g (flat ψ ν μ Φ h' h) =
      ((ψ (simpleSum u) : ℂ) * (((P.lam ⟨_, hm⟩)⁻¹ : ℂˣ) : ℂ)) • flat ψ ν μ Φ h' h := by
  have := flat_target (ψ := ψ) (ν := ν) hc H hu g (⟨_, hm⟩ : P.J)⁻¹ h' h
  rw [show u * embX c g * h * (((⟨_, hm⟩ : P.J)⁻¹ : P.J) : GL (n ⊕ Fin c) k) = h by simp [mul_assoc],
    nabs_det_of_mem hJ hu hm, map_inv, inv_inv, AddChar.map_neg_eq_inv] at this
  conv_rhs => rw [this, smul_smul]
  have := Circle.coe_ne_zero (ψ (simpleSum u))
  symm
  convert one_smul ℂ _
  simp; field_simp

theorem source_law (hc : 1 ≤ c) (hJ : IsCO P'.J) (H : HasTypes μ P' P Φ) (h' : GL (n' ⊕ Fin (c + 1)) k)
    (h : GL (n ⊕ Fin c) k) {u : GL (n' ⊕ Fin (c + 1)) k} (hu : u ∈ N k n' (c + 1) 1) (g : GL n' k)
    (hm : h'⁻¹ * (u * embX (c + 1) g) * h' ∈ P'.J) :
    om μ g 1 (flat ψ ν μ Φ h' h) = ((ψ (simpleSum u) : ℂ)⁻¹ * (P'.lam ⟨_, hm⟩ : ℂ)) • flat ψ ν μ Φ h' h := by
  have := flat_source (ψ := ψ) (ν := ν) hc H hu g (⟨_, hm⟩ : P'.J)⁻¹ h' h
  rw [show u * embX (c + 1) g * h' * (((⟨_, hm⟩ : P'.J)⁻¹ : P'.J) : GL (n' ⊕ Fin (c + 1)) k) = h' by simp [mul_assoc],
    nabs_det_of_mem hJ hu hm, map_inv] at this
  conv_rhs => rw [this, smul_smul]
  have := Circle.coe_ne_zero (ψ (simpleSum u))
  symm
  convert one_smul ℂ _
  simp; field_simp

end Step

section Laws
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]

theorem sourceLaw : SourceLaw ψ ν :=
  fun _ _ _ _ _ _ _ hc _ _ _ _ _ hJ _ H h' h _ hu g hm => source_law hc hJ H h' h hu g hm

theorem exists_char {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (S : Subgroup (GL b k)) {f : Matrix b a k → ℂ} (hf : f ≠ 0) (H : ∀ g ∈ S, ∃ z : ℂ, om μ 1 g f = z • f) :
    ∃ χ : S →* ℂˣ, ∀ g : S, om μ 1 (g : GL b k) f = (χ g : ℂ) • f := by
  choose z hz using H
  have h0 : ∀ g : S, z g g.2 ≠ 0 := fun g e => (om_ne_zero μ 1 (g : GL b k)).2 hf (by rw [hz g g.2, e, zero_smul])
  refine ⟨MonoidHom.mk' (fun g => Units.mk0 _ (h0 g)) fun g g' => Units.ext (smul_left_injective ℂ hf ?_),
    fun g => hz g g.2⟩
  have := om_mul μ 1 1 (g : GL b k) g' f
  rw [hz g' g'.2, om_smul, hz g g.2, smul_smul, mul_one, mul_comm] at this
  exact (hz _ (g * g').2).symm.trans this

omit [BorelSpace k] [ν.IsAddHaarMeasure] in
theorem xi_eq_smul {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (μ : kˣ →* ℂˣ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (J : Subgroup (GL (n ⊕ Fin c) k)) (b h' h) :
    xi ψ ν μ Φ J b h' h = (((volNat ν b (Cgrp J h))⁻¹ : ℝ) : ℂ) • flat ψ ν μ Φ h' h := rfl

theorem targetLaw : TargetLaw ψ ν := by
  intro n n' _ _ _ _ c hc μ P' P Φ hΦ _ hJ H h' h
  refine ⟨fun u hu => target_law hc hJ H h' h hu, fun h0 => ?_⟩
  obtain ⟨χ, hχ⟩ := exists_char μ (prX (Cgrp P.J h)) h0 fun g ⟨u, hu, hm⟩ =>
    ⟨_, target_law hc hJ H h' h hu g (mem_Cgrp.1 hm).2⟩
  refine ⟨χ, fun g u hu hm => smul_left_injective ℂ h0 ((hχ g).symm.trans (target_law hc hJ H h' h hu g hm)),
    fun g => ⟨hχ g, fun b => ?_, fun V' V _ _ _ _ π' π θ hθ φ => ?_⟩⟩
  · rw [xi_eq_smul, om_smul, hχ, smul_comm]
  · rw [← hθ 1 g φ (flat ψ ν μ Φ h' h) (opE_mem_SB 1 ψ ν (om_mem_SB μ h' h hΦ)), map_one, Module.End.one_apply]
    exact (congrArg _ (hχ g)).trans (map_smul _ _ _)

variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]

omit [MeasurableSpace k] [BorelSpace k] in
theorem isCO_lev {T : Chain k s X Z} (hT : T.Regular) (j c h) : IsCO (T.lev j c h).J :=
  ⟨(hT.2.2 j c h).1, (hT.2.2 j c h).2.1⟩

omit [MeasurableSpace k] [BorelSpace k] in
theorem psi_law (ψ : AddChar k Circle) {T : Chain k s X Z} (hL : T.Laws) (h) {u} (hu : u ∈ N k (X s) (0 + 1) 1)
    (g : GL (X s) k) (hm : h⁻¹ * (u * embX (0 + 1) g) * h ∈ (T.lev s (0 + 1) rfl).J) (y : X (s + 1) → k) :
    om (T.mu (s + 1)) g 1 (fun x₀ => T.Psi h x₀ y) =
      ((ψ (simpleSum u) : ℂ)⁻¹ * ((T.lev s (0 + 1) rfl).lam ⟨_, hm⟩ : ℂ)) • fun x₀ => T.Psi h x₀ y := by
  obtain rfl : u = 1 := Units.ext (Matrix.ext fun r t => Model.mem_N_iff.1 hu r t (by
    rcases r with r | r <;> rcases t with t | t <;> simp [lev]))
  have e : om (T.mu (s + 1)) (embX (0 + 1) g) 1 (om (T.mu (s + 1)) h 1 (T.Phi s 0 rfl)) =
      ((T.lev s (0 + 1) rfl).lam ⟨_, hm⟩ : ℂ) • om (T.mu (s + 1)) h 1 (T.Phi s 0 rfl) := by
    rw [← om_smul, ← (hL.1 s 0 rfl).1 ⟨_, hm⟩, ← om_mul, ← om_mul]; simp [mul_assoc]
  have d : Matrix.GeneralLinearGroup.det (embX (0 + 1) g) = Matrix.GeneralLinearGroup.det g :=
    Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply, Radical.embX_val])
  funext x
  have w : withCol x y * (embX (0 + 1) g).val = withCol (x * g.val) y := by
    simp [withCol, Radical.embX_val, fromBlocks_multiply]
  have := congrFun e (withCol x y)
  rw [om, d] at this
  simp only [inv_one, Units.val_one, Matrix.one_mul, w] at this
  rw [om, Radical.simpleSum_eq_zero (by simp [Matrix.one_apply])]
  simpa [Chain.Psi, nabs_one] using this

theorem entry_target {T : Chain k s X Z} (hT : T.Regular) (hL : T.Laws) (j c) (H : j + 1 + c = s) (h' h) {u}
    (hu : u ∈ N k (X (j + 1)) (c + 1) 1) (g) (hm : h⁻¹ * (u * embX (c + 1) g) * h ∈ (T.lev (j + 1) (c + 1) (by omega)).J) :
    om (T.mu (j + 1)) 1 g (T.entry ψ ν j c H h' h) =
      ((ψ (simpleSum u) : ℂ) * ((((T.lev (j + 1) (c + 1) (by omega)).lam ⟨_, hm⟩)⁻¹ : ℂˣ) : ℂ)) •
        T.entry ψ ν j c H h' h := by
  rw [Chain.entry, xi_eq_smul, om_smul,
    target_law (by omega) (isCO_lev hT _ _ _) (hL.1 j (c + 1) (by omega)) h' h hu g hm, smul_comm]

theorem chainInvariant : ChainInvariant ψ ν := by
  intro s X _ _ Z _ _ T hT hL
  refine ⟨?_, fun h u hu => psi_law ψ hL h hu⟩
  rintro j c H h' h h'' g ⟨u, hu, hm⟩ x x'
  have hm := (mem_Cgrp.1 hm).2
  rw [entry_target hT hL j (c + 1) _ h' h hu g hm, show T.entry ψ ν (j + 1) c H h h'' = _ from xi_eq_smul _ _ _ _ _ _, om_smul,
    source_law (by omega) (isCO_lev hT _ _ _) (hL.1 (j + 1) (c + 1) (by omega)) h h'' hu g hm]
  have := Circle.coe_ne_zero (ψ (simpleSum u))
  simp only [Pi.smul_apply, smul_eq_mul, Units.val_inv_eq_inv_val]
  field_simp

theorem chainInvariantLast : ChainInvariantLast ψ ν := by
  rintro j X _ _ Z _ _ T hT hL h' h g ⟨u, hu, hm⟩ x x' y
  have hm := (mem_Cgrp.1 hm).2
  rw [entry_target hT hL j 0 _ h' h hu g hm, psi_law ψ hL h hu g hm]
  have := Circle.coe_ne_zero (ψ (simpleSum u))
  simp only [Pi.smul_apply, smul_eq_mul, Units.val_inv_eq_inv_val]
  field_simp

theorem reps_finite (hψ : HasConductor ψ 1) {T : Chain k s X Z} (hT : T.Regular) {A : RepFam k s X}
    (hA : T.IsRepSystem A ψ ν) (j : ℕ) : ∀ c h, (A j c h).Finite := by
  induction j with
  | zero => intro c h; rw [hA.zero]; exact Set.finite_singleton _
  | succ j ih =>
    intro c h
    refine Set.Finite.of_finite_image ?_ (hA.bij j c h).injOn
    rw [(hA.bij j c h).image_eq]
    exact (ih _ _).biUnion fun g _ => idxAt_finite hψ (by omega) (hT.1 _ _ _) (hT.2.2 _ _ _).1 g

theorem reps_image {T : Chain k s X Z} (hL : T.Laws) {A A' : RepFam k s X}
    (hA : T.IsRepSystem A ψ ν) (hA' : T.IsRepSystem A' ψ ν) (j : ℕ) : ∀ c (h : j + c = s),
    DoubleCoset.mk (R k (X j) (c + 1) 1) (T.lev j (c + 1) (by omega)).J '' A j c h =
      DoubleCoset.mk (R k (X j) (c + 1) 1) (T.lev j (c + 1) (by omega)).J '' A' j c h := by
  induction j with
  | zero => intro c h; rw [hA.zero, hA'.zero]
  | succ j ih =>
    intro c h
    rw [(hA.bij j c h).image_eq, (hA'.bij j c h).image_eq]
    have key : ∀ {B B' : Set (GL (X j ⊕ Fin (c + 1 + 1)) k)},
        DoubleCoset.mk (R k (X j) (c + 1 + 1) 1) (T.lev j (c + 1 + 1) (by omega)).J '' B =
          DoubleCoset.mk (R k (X j) (c + 1 + 1) 1) (T.lev j (c + 1 + 1) (by omega)).J '' B' →
        ⋃ g ∈ B, T.idx ψ ν j c h g ⊆ ⋃ g ∈ B', T.idx ψ ν j c h g := by
      intro B B' e β hβ
      obtain ⟨g, hg, x, rfl, hx⟩ := Set.mem_iUnion₂.1 hβ
      obtain ⟨g', hg', e'⟩ := e ▸ Set.mem_image_of_mem _ hg
      exact Set.mem_iUnion₂.2 ⟨g', hg', x, rfl,
        (flat_ne_zero_congr (by omega) (hL.1 j (c + 1) (by omega)) e' rfl).2 hx⟩
    exact (key (ih _ _)).antisymm (key (ih _ _).symm)

theorem chainFinite (hψ : HasConductor ψ 1) : ChainFinite ψ ν := by
  intro s X _ _ Z _ _ T hT hL
  refine ⟨fun j c h g g' => ?_, fun A hA => ⟨reps_finite hψ hT hA, fun A' hA' => reps_image hL hA hA',
    fun ϖ hϖ => ?_, fun c₁ c₂ => (GlobalTheory.T.finite_quotient_cosets_scaledStandardLatticeBox k _ c₁ c₂).subset fun yb ⟨y, hy, e, _⟩ => ⟨y, hy, e⟩⟩⟩
  · exact (stepWellDefined hψ _ _ (c + 1) (by omega) _ _ _ _ (hT.1 _ _ _) (isCO_lev hT _ _ _) (isCO_lev hT _ _ _)
      (hL.1 j (c + 1) (by omega))).2.2.2.2.2.2 _ g g'
  · obtain ⟨e, he, H⟩ := GlobalTheory.T.exists_adapted_exponent_schwartzBruhat_lastColumn k _ _ _ ((reps_finite hψ hT hA s 0 rfl).image
      fun g => om (T.mu (s + 1)) g 1 (T.Phi s 0 rfl)) (by
        rintro _ ⟨g, -, rfl⟩; exact om_mem_SB _ _ _ (hT.1 _ _ _)) ϖ hϖ
    exact ⟨e, he, fun g hg => H _ ⟨g, hg, rfl⟩⟩

end Laws

section Volumes
variable [MeasurableSpace k] [BorelSpace k] {ν : Measure k} [ν.IsAddHaarMeasure]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

omit [MeasurableSpace k] [BorelSpace k] in
theorem isCO_subgroupOf {H : Subgroup (GL (n ⊕ Fin c) k)} (hH : IsCO H) : IsCO (H.subgroupOf (N k n c 1)) :=
  ⟨hH.1.preimage continuous_subtype_val, (VolN.isClosed_N 1).isClosedEmbedding_subtypeVal.isCompact_preimage hH.2⟩

theorem volNat_zpow (hq : (resCard k).Prime) {J : Subgroup (GL (n ⊕ Fin c) k)} (hJ : IsCO J)
    (h b : GL (n ⊕ Fin c) k) : ∃ z : ℤ, volNat ν b (Cgrp J h) = (resCard k : ℝ) ^ z := by
  obtain ⟨bG, -⟩ := volGL_haar k (n ⊕ Fin c) ν
  have := VolN.isHaarMeasure_volN (n := n) (c := c) ν 1
  have e : (Cgrp J h).subgroupOf (N k n c 1) = (J.comap (MulAut.conj h⁻¹).toMonoidHom).subgroupOf (N k n c 1) := by
    ext u
    exact ⟨fun H => H.2, fun H => ⟨(le_sup_right : N k n c 1 ≤ R k n c 1) u.2, H⟩⟩
  unfold volNat
  rw [e]
  refine GlobalTheory.T.haar_compactOpen_ratio_eq_zpow_of_topNilpotent (N k n c 1) (volN ν n c 1) _ hq (fun u U hU => ?_) _ _
    (isCO_subgroupOf (isOpen_isCompact_conj h hJ.1 hJ.2))
    (isCO_subgroupOf (isOpen_isCompact_conj b SplitFlip.isOpen_KO SplitFlip.isCompact_KO))
  obtain ⟨V, hV, hVU⟩ := (mem_nhds_subtype _ _ _).1 hU
  obtain ⟨m, hm⟩ := GlobalTheory.T.rootExchangeUnipotent_exists_residueCardPow_mem_nhds k n c 1 hq u u.2 V hV
  exact ⟨m, hVU hm⟩

theorem cosetMeasure : CosetMeasure ν := by
  intro n _ _ c hc J hJ h
  obtain ⟨hC, hd⟩ := GlobalTheory.T.isCO_prX_Cgrp_and_det_valuation_deltaR_eq_one k n c J hJ h
  refine ⟨hC, hd, GlobalTheory.T.exists_parabolicDoubleCosetFunction_eq_one k n c J h fun g hg => (hd g hg).2, fun hq => volNat_zpow hq hJ h, fun m hm => ?_⟩
  have hv := GlobalTheory.T.parabolicHaarVolume_conjIntersection_eq_mul k ν n c J h hC.1
  obtain ⟨h0, h1⟩ := volN_Cgrp ν hJ.1 hJ.2 h
  have m0 : m (prX (Cgrp J h)) ≠ 0 := hC.1.measure_ne_zero m ⟨1, one_mem _⟩
  have m1 : m (prX (Cgrp J h)) ≠ ⊤ := hC.2.measure_lt_top.ne
  have v0 : volR ν m (Cgrp J h) ≠ 0 := by rw [hv]; exact mul_ne_zero h0 m0
  have v1 : volR ν m (Cgrp J h) ≠ ⊤ := by rw [hv]; exact ENNReal.mul_ne_top h1 m1
  refine ⟨hv m, v0, v1, fun b => ?_, fun μG hμG f hf z => ?_⟩
  · rw [hv, rescale, volNat, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_inv]
    ring
  · have key := GlobalTheory.T.isQuotInt_cosetFn_alt k ν n c J hJ h m (volR ν m (Cgrp J h)).toReal (ENNReal.toReal_pos v0 v1).ne'
      (fun u hu g => by rw [GlobalTheory.T.integral_indicator_Cgrp_translate_eq_deltaR_mul k ν n c hc J hJ h hC m u hu g, hv, ENNReal.toReal_mul]) μG f hf
    exact ⟨fun hz => (QuotInt.quotInt_unique_exists k n c 1 le_rfl hc ν m μG f).1 _ _ hz key, fun e => e ▸ key⟩

theorem volumeCancels : VolumeCancels ν := by
  intro n _ _ c hc J hJ b h m hm μG hμG h1 f hf
  obtain ⟨hC, -, -, -, H⟩ := cosetMeasure (ν := ν) n c hc J hJ h
  obtain ⟨s1, s2⟩ := isOpen_isCompact_conj b (SplitFlip.isOpen_KO (n := n ⊕ Fin c)) SplitFlip.isCompact_KO
  obtain ⟨s3, s4⟩ := volN_ne_zero_ne_top ν 1 s1 s2
  have hm' : (rescale ν b m).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul m (ENNReal.inv_ne_zero.2 s4) (ENNReal.inv_ne_top.2 s3)
  have key := (H _ hm').2.2.2.2 μG hμG f hf
  refine ⟨_, (key _).2 rfl, fun z' hz => (key _).1 hz, ?_⟩
  have m0 : (m (prX (Cgrp J h))).toReal ≠ 0 :=
    (ENNReal.toReal_pos (hC.1.measure_ne_zero m ⟨1, one_mem _⟩) hC.2.measure_lt_top.ne).ne'
  rw [(H m hm).2.2.2.1 b, h1, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  have := (volNat_Cgrp_pos ν hJ.1 hJ.2 b h).ne'
  simp only [ENNReal.toReal_one]
  field_simp

end Volumes

section First
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]

theorem firstVertex {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z]
    [DecidableEq Z] {C : Chain k s X Z} (hT : C.Regular) (hL : C.Laws) {K₀ : Set (GL (X 0) k)}
    {lam : GL (X 0) k → ℂ} (H : ∀ c (H : 0 + c = s + 1), (prX (Cgrp (C.lev 0 c H).J 1) : Set (GL (X 0) k)) = K₀ ∧
      (∀ γ ∈ K₀, ∃ hm : embX c γ ∈ (C.lev 0 c H).J, ((C.lev 0 c H).lam ⟨_, hm⟩ : ℂ) = lam γ) ∧
      ∀ u ∈ N k (X 0) c 1, ∀ hm : u ∈ (C.lev 0 c H).J, ((C.lev 0 c H).lam ⟨u, hm⟩ : ℂ) = ψ (simpleSum u)) :
    FirstVertex ψ ν C K₀ lam := by
  refine ⟨fun c hc => ?_, fun c hc h γ hγ => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := H c hc
    refine ⟨h1, h2, ?_⟩
    choose hm hlam using h2
    have hK : ∀ γ : prX (Cgrp (C.lev 0 c hc).J 1), (γ : GL (X 0) k) ∈ K₀ := fun γ => h1 ▸ γ.2
    let ι : prX (Cgrp (C.lev 0 c hc).J 1) →* (C.lev 0 c hc).J :=
      ((embX c).comp (Subgroup.subtype _)).codRestrict _ fun γ => hm γ (hK γ)
    refine ⟨((C.lev 0 c hc).lam.comp ι)⁻¹, fun γ u hu hu' => ?_, fun γ => ?_⟩
    · have hu'' : u ∈ (C.lev 0 c hc).J := by simpa using mul_mem hu' (inv_mem (hm γ (hK γ)))
      rw [← h3 u hu hu'', show (⟨_, hu'⟩ : (C.lev 0 c hc).J) = ⟨u, hu''⟩ * ι γ from Subtype.ext (by simp; rfl),
        map_mul]
      simp
      field_simp
    · rw [← hlam γ (hK γ)]
      exact Units.inv_mul _
  · obtain ⟨hm, e⟩ := (H (c + 1 + 1) (by omega)).2.1 γ hγ
    rw [source_law (by omega) (isCO_lev hT _ _ _) (hL.1 0 (c + 1) hc) 1 h (one_mem _) γ (by simpa using hm),
      Radical.simpleSum_eq_zero (by simp [Matrix.one_apply]), ← e]
    simp

theorem firstVertexChains (hψ : HasConductor ψ 1) : FirstVertexChains ψ ν := by
  intro s t _ _
  refine ⟨fun κ ϖ hϖ => ⟨GlobalTheory.T.exists_genericLevelOfFrame k ψ hψ ϖ hϖ _ _, fun ρ _ => GlobalTheory.T.exists_isSymmetricPositionLevel k ψ hψ ϖ hϖ ρ _ _, fun P hP μ hμ => ?_⟩,
    fun κ _ _ δ hδ η hη => ?_⟩
  · refine firstVertex (Chain.ofType_regular _ _ _ _ _) (Chain.ofType_laws _ _ _ _ _)
      (GlobalTheory.T.firstVertex_iteratedLevelChain_in_frame k ψ ϖ s t κ P ?_ μ hμ)
    rcases hP with hP | ⟨ρ, -, hP⟩
    exacts [GlobalTheory.T.genericLevelOfFrame_block_and_character k ψ ϖ _ _ P hP, GlobalTheory.T.symmetricPositionLevel_shape_on_parabolic k ψ ϖ ρ _ _ P hP]
  · exact firstVertex (Chain.ofTwist_regular _ _ _ _ _) (Chain.ofTwist_laws _ _ _ hη _ _)
      (GlobalTheory.T.firstVertex_parahoricLevelChain_twist k ψ hψ s t κ δ hδ η)

end First

theorem entries_wellDefined : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Statement := by
  intro k _ _ _ _ _ _ ψ ν hψ hν
  have := hν.1
  exact ⟨stepWellDefined hψ, chainFinite hψ, cosetMeasure, volumeCancels, targetLaw, sourceLaw, chainInvariant,
    chainInvariantLast, firstVertexChains hψ⟩

end GlobalTheory.UnfoldedEntries
