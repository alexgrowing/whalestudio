import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps
import Formalism.DoubleCosetMeasures.LatticeCoset

noncomputable section

open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.A5x4

open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Supp in

theorem isCompact_intPairs {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] (R : Subring K) (hRc : IsCompact (R : Set K)) (s : List ℕ) (t : ℕ → Kˣ) :
    IsCompact {p : lowW K s t × upUniG K s.sum |
      IsInt R (((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
      ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))} := by
  obtain ⟨Ph, Pu, hPh, hPu, hP⟩ := lu_rec (K := K) (n := s.sum)
  obtain ⟨wi, h1, h2⟩ : ∃ wi : Matrix (Fin s.sum) (Fin s.sum) K,
      wi * pt s t = 1 ∧ pt s t * wi = 1 :=
    ⟨pt s (fun b => (t b)⁻¹), pt_mul_pt s _ _ (fun b => by simp),
      pt_mul_pt s _ _ (fun b => by simp)⟩
  have hV : Continuous fun Z : Matrix (Fin s.sum) (Fin s.sum) K => pt s t * Ph (wi * Z) * wi :=
    (continuous_const.mul (hPh.comp (continuous_const.mul continuous_id))).mul continuous_const
  have hU : Continuous fun Z : Matrix (Fin s.sum) (Fin s.sum) K => Pu (wi * Z) :=
    hPu.comp (continuous_const.mul continuous_id)
  let Φ : Matrix (Fin s.sum) (Fin s.sum) K →
      (Matrix (Fin s.sum) (Fin s.sum) K × (Matrix (Fin s.sum) (Fin s.sum) K)ᵐᵒᵖ) ×
        (Matrix (Fin s.sum) (Fin s.sum) K × (Matrix (Fin s.sum) (Fin s.sum) K)ᵐᵒᵖ) :=
    fun Z => ((pt s t * Ph (wi * Z) * wi, MulOpposite.op (pt s t * Ph (wi * Z) * wi).adjugate),
      (Pu (wi * Z), MulOpposite.op (Pu (wi * Z)).adjugate))
  have hΦ : Continuous Φ :=
    (hV.prodMk (MulOpposite.continuous_op.comp hV.matrix_adjugate)).prodMk
      (hU.prodMk (MulOpposite.continuous_op.comp hU.matrix_adjugate))
  let ι : lowW K s t × upUniG K s.sum →
      (Matrix (Fin s.sum) (Fin s.sum) K × (Matrix (Fin s.sum) (Fin s.sum) K)ᵐᵒᵖ) ×
        (Matrix (Fin s.sum) (Fin s.sum) K × (Matrix (Fin s.sum) (Fin s.sum) K)ᵐᵒᵖ) :=
    fun p => (Units.embedProduct _ (p.1 : GL (Fin s.sum) K),
      Units.embedProduct _ (p.2 : GL (Fin s.sum) K))
  have hι : IsClosedEmbedding ι :=
    (Units.isClosedEmbedding_embedProduct.comp
      (isClosed_lowW s t wi h1 h2).isClosedEmbedding_subtypeVal).prodMap
      (Units.isClosedEmbedding_embedProduct.comp
        (isClosed_upUniG (K := K) s.sum).isClosedEmbedding_subtypeVal)
  let Mset : Set (Matrix (Fin s.sum) (Fin s.sum) K) := {Z | IsInt R Z}
  have hMc : IsCompact Mset := by
    have key : Mset = Set.univ.pi fun _ => Set.univ.pi fun _ => (R : Set K) := by
      ext Z
      show (∀ a b, Z a b ∈ R) ↔ _
      constructor
      · intro h
        exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => h i j
      · intro h a b
        exact Set.mem_univ_pi.1 (Set.mem_univ_pi.1 h a) b
    rw [key]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hRc
  let S : Set (lowW K s t × upUniG K s.sum) :=
    {p | IsInt R (((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
      ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))}
  have hScl : IsClosed S :=
    hMc.isClosed.preimage (((Units.continuous_val.comp (continuous_subtype_val.comp
      continuous_fst)).mul continuous_const).mul
      (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)))
  have hSsub : S ⊆ ι ⁻¹' (Φ '' Mset) := by
    intro p hp
    refine ⟨_, hp, ?_⟩
    obtain ⟨hv1, hv2⟩ := (mem_lowW_iff s t wi h1 h2 p.1.1).1 p.1.2
    have hu : IsUpUni ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) := p.2.2
    obtain ⟨e1, e2⟩ := hP _ _ hv2 hu
    have eY : wi * (((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
        ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) =
        (wi * ((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t) *
        ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) := by
      simp only [Matrix.mul_assoc]
    have eV : pt s t * (wi * ((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
        pt s t) * wi = ((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) := by
      simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
      rw [Matrix.mul_assoc, h2, Matrix.mul_one]
    simp only [Φ, ι, eY, e1, e2, eV, Units.embedProduct_apply]
    rw [coe_inv_of_det _ (isLowUni_det K hv1), coe_inv_of_det _ (isUpUni_det K hu)]
  exact (hι.isCompact_preimage (hMc.image hΦ)).of_isClosed_subset hScl hSsub

theorem isInt_orbZ_inv {K : Type} [CommRing K] (R : Subring K) (w : Point K)
    (a : lowW K w.1 w.2) (ha : a ∈ intSub R (lowW K w.1 w.2))
    (b : upUniG K w.1.sum) (hb : b ∈ intSub R (upUniG K w.1.sum))
    (x : lowW K w.1 w.2) (y : upUniG K w.1.sum) :
    IsInt R (orbZ w (a * x, y * b)) ↔ IsInt R (orbZ w (x, y)) := by
  have h := Formalism.DoubleCosetMeasures.P.intInv K R w.1.sum _ _ (orbZ w (x, y)) a.2.1 b.2 ha.1 hb.1
  rw [← h]
  have : orbZ w (a * x, y * b) =
      ((a : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) * orbZ w (x, y) *
        ((b : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := by
    simp only [orbZ, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
  rw [this]

end Formalism.FourierDecayAlt.P.A5x4

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.A5x4

theorem integral_points_finite : Formalism.FourierDecayAlt.A5.IntFinite := by
  intro K _ _ _ R ψ hL w
  have := hL.t2
  classical
  let f : lowW K w.1 w.2 × upUniG K w.1.sum → ℝ := fun p => if IsInt R (orbZ w p) then 1 else 0
  have hinv : ∀ a ∈ intSub R (lowW K w.1 w.2), ∀ b ∈ intSub R (upUniG K w.1.sum),
      ∀ (x : lowW K w.1 w.2) (y : upUniG K w.1.sum), f (a * x, y * b) = f (x, y) := by
    intro a ha b hb x y
    simp only [f, isInt_orbZ_inv R w a ha b hb x y]
  have hS := isCompact_intPairs R hL.isCompact w.1 w.2
  have hc : HasCompactSupport f := by
    refine hS.of_isClosed_subset isClosed_closure (closure_minimal ?_ hS.isClosed)
    intro p hp
    by_contra hn
    apply hp
    simp only [f]
    rw [if_neg]
    exact hn
  have : (0 : Measure (lowW K w.1 w.2)).IsMulRightInvariant := ⟨fun g => by simp⟩
  have : (0 : Measure (upUniG K w.1.sum)).IsMulLeftInvariant := ⟨fun g => by simp⟩
  have key := (Formalism.DoubleCosetMeasures.P.intTwoSided (lowW K w.1 w.2) (upUniG K w.1.sum) 0 0
    (intSub R (lowW K w.1 w.2)) (intSub R (upUniG K w.1.sum))
    (Formalism.DoubleCosetMeasures.P.isOpen_intSub R hL.isOpen _) (Formalism.DoubleCosetMeasures.P.isOpen_intSub R hL.isOpen _) ℝ f hinv hc).1
  refine key.subset ?_
  intro q hq
  have hq' : IsInt R (orbZ w (q.1.out, q.2.out)) := hq
  simp [f, hq']

theorem kernel_quotient_finite : Formalism.FourierDecayAlt.A5.KpFinite := by
  intro K _ _ _ R ψ hL w w'
  refine ((integral_points_finite K R ψ hL w).prod (integral_points_finite K R ψ hL w')).subset ?_
  intro q hq
  simp only [Function.mem_support, pairTerm] at hq
  by_contra hcon
  apply hq
  rw [if_neg]
  · simp
  · intro hI
    exact hcon ⟨hI.1, hI.2⟩

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.A5x4

section Sums

theorem Kp_eq_sum {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (w w' : Point K)
    (h : {q : Cos R w | IsInt R (orbZ w (rep R q))}.Finite)
    (h' : {q : Cos R w' | IsInt R (orbZ w' (rep R q))}.Finite) :
    Kp R ψ w w' = ∑ q ∈ h.toFinset, ∑ q' ∈ h'.toFinset,
      (Nat.card (isoZZ R (orbZ w (rep R q)) (orbZ w' (rep R q'))) : ℂ) * phase ψ (rep R q) *
        conj (phase ψ (rep R q')) := by
  unfold Kp
  rw [finsum_eq_sum_of_support_subset (s := h.toFinset ×ˢ h'.toFinset), Finset.sum_product]
  · refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun q' hq' => ?_
    have h1 : IsInt R (orbZ w (rep R q)) := by simpa using hq
    have h2 : IsInt R (orbZ w' (rep R q')) := by simpa using hq'
    simp only [pairTerm]
    rw [if_pos ⟨h1, h2⟩]
  · intro q hq
    simp only [Function.mem_support, pairTerm] at hq
    by_contra hcon
    apply hq
    rw [if_neg]
    · simp
    · intro hI
      apply hcon
      simp [hI.1, hI.2]

open Classical in

theorem BB_eq_sum {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (R : Subring K) (ψ : AddChar K ℂ) (hL : LocalDatum K R ψ) (w : Point K)
    (μ₁ : Measure (lowW K w.1 w.2)) (μ₂ : Measure (upUniG K w.1.sum))
    [μ₁.IsMulRightInvariant] [μ₂.IsMulLeftInvariant] [SFinite μ₁] [SFinite μ₂]
    (h1 : μ₁ (intSub R (lowW K w.1 w.2) : Set (lowW K w.1 w.2)) = 1)
    (h2 : μ₂ (intSub R (upUniG K w.1.sum) : Set (upUniG K w.1.sum)) = 1)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R)
    (h : {q : Cos R w | IsInt R (orbZ w (rep R q))}.Finite) :
    BB R w.1 w.2 ψ C e lam μ₁ μ₂ = ∑ q ∈ h.toFinset,
      (Nat.card (isoSet R (orbZ w (rep R q)) C e lam) : ℂ) * phase ψ (rep R q) := by
  have := hL.t2
  have hψ : ∀ r ∈ R, ψ r = 1 := by
    intro r hr
    have := (hL.selfDual 1).2 R.one_mem r hr
    simpa using this
  rw [Formalism.DoubleCosetMeasures.Final.bbNorm K R hL.isOpen w.1 w.2 ψ hψ μ₁ μ₂ h1 h2 C e lam
    (Formalism.DoubleCosetMeasures.Final.suppCompact K R hL.isOpen hL.isCompact w.1 w.2 ψ C e lam),
    finsum_eq_sum_of_support_subset (s := h.toFinset)]
  · refine Finset.sum_congr rfl fun q hq => ?_
    have h1 : IsInt R (orbZ w (rep R q)) := by simpa using hq
    have h3 : phi R w.1 w.2 ψ C e lam (q.1.out, q.2.out) =
      (if IsInt R (orbZ w (rep R q)) then
        (Nat.card (isoSet R (orbZ w (rep R q)) C e lam) : ℂ) else 0) * phase ψ (rep R q) := rfl
    rw [h3, if_pos h1]
  · intro q hq
    have h3 : phi R w.1 w.2 ψ C e lam (q.1.out, q.2.out) =
      (if IsInt R (orbZ w (rep R q)) then
        (Nat.card (isoSet R (orbZ w (rep R q)) C e lam) : ℂ) else 0) * phase ψ (rep R q) := rfl
    simp only [Function.mem_support] at hq
    rw [h3] at hq
    by_contra hcon
    apply hq
    rw [if_neg]
    · simp
    · intro hI
      apply hcon
      simpa using hI

end Sums

section Count

variable {K : Type} [CommRing K] (R : Subring K)

theorem card_isoSet {n : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R)
    (φ0 : coker R Z ≃ₗ[R] C) (hφ0 : φ0 ∈ isoSet R Z C e lam) :
    Nat.card (isoSet R Z C e lam) = Nat.card (autSet R C e lam) := by
  refine Nat.card_congr ⟨fun φ => ⟨φ0.symm.trans φ.1, ?_⟩, fun σ => ⟨φ0.trans σ.1, ?_⟩, ?_, ?_⟩
  · refine ⟨?_, fun c => ?_⟩
    · have : φ0.symm e = eZ R Z := by rw [← hφ0.1]; simp
      simp [this, φ.2.1]
    · obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (φ0.symm c)
      have h3 : φ0 (Submodule.Quotient.mk v) = c := by rw [hv]; simp
      simp only [LinearEquiv.trans_apply]
      rw [← hv, φ.2.2 v, ← hφ0.2 v, h3]
  · refine ⟨?_, fun v => ?_⟩
    · simp [hφ0.1, σ.2.1]
    · simp only [LinearEquiv.trans_apply]
      rw [σ.2.2, hφ0.2]
  · intro φ; ext x; simp
  · intro σ; ext x; simp

theorem card_isoZZ {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (Z' : Matrix (Fin n') (Fin n') K)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R)
    (φ0 : coker R Z ≃ₗ[R] C) (hφ0 : φ0 ∈ isoSet R Z C e lam) :
    Nat.card (isoSet R Z' C e lam) = Nat.card (isoZZ R Z Z') := by
  refine Nat.card_congr ⟨fun ρ => ⟨φ0.trans ρ.1.symm, ?_⟩, fun φ => ⟨φ.1.symm.trans φ0, ?_⟩, ?_, ?_⟩
  · refine ⟨?_, fun v v' hv => ?_⟩
    · simp only [LinearEquiv.trans_apply, hφ0.1]
      exact (LinearEquiv.symm_apply_eq _).2 ρ.2.1.symm
    · simp only [LinearEquiv.trans_apply] at hv
      have h4 : φ0 (Submodule.Quotient.mk v) = ρ.1 (Submodule.Quotient.mk v') := by
        rw [← hv]; simp
      rw [← ρ.2.2 v', ← h4, hφ0.2]
  · refine ⟨?_, fun v' => ?_⟩
    · have : φ.1.symm (eZ R Z') = eZ R Z := by rw [← φ.2.1]; simp
      simp [this, hφ0.1]
    · obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (φ.1.symm (Submodule.Quotient.mk v'))
      have h3 : φ.1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' := by rw [hv]; simp
      simp only [LinearEquiv.trans_apply]
      rw [← hv, hφ0.2 v, φ.2.2 v v' h3]
  · intro ρ; ext x; simp
  · intro φ; ext x; simp

theorem isoCount {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (Z' : Matrix (Fin n') (Fin n') K) (ι : Type) [Fintype ι] (C : ι → Type)
    [∀ a, AddCommGroup (C a)] [∀ a, Module R (C a)] (e : ∀ a, C a) (lam : ∀ a, C a →ₗ[R] KR R)
    (hne : ∀ a b, a ≠ b → ¬ ∃ φ : C a ≃ₗ[R] C b, φ (e a) = e b ∧ ∀ c, lam b (φ c) = lam a c)
    (hex : ∃ a, (isoSet R Z (C a) (e a) (lam a)).Nonempty) :
    ∑ a, (Nat.card (isoSet R Z (C a) (e a) (lam a)) : ℂ) *
        (Nat.card (isoSet R Z' (C a) (e a) (lam a)) : ℂ) /
        (Nat.card (autSet R (C a) (e a) (lam a)) : ℂ) = (Nat.card (isoZZ R Z Z') : ℂ) := by
  obtain ⟨a0, φ0, hφ0⟩ := hex
  classical
  have hzero : ∀ b, b ≠ a0 → IsEmpty (isoSet R Z (C b) (e b) (lam b)) := by
    intro b hb
    refine ⟨fun ⟨φ1, h1⟩ => hne b a0 hb ⟨φ1.symm.trans φ0, ?_, ?_⟩⟩
    · have : φ1.symm (e b) = eZ R Z := by rw [← h1.1]; simp
      simp [this, hφ0.1]
    · intro c
      obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (φ1.symm c)
      have h3 : φ1 (Submodule.Quotient.mk v) = c := by rw [hv]; simp
      simp only [LinearEquiv.trans_apply]
      rw [← hv, hφ0.2 v, ← h1.2 v, h3]
  rw [Finset.sum_eq_single a0 (fun b _ hb => by have := hzero b hb; simp) (by simp)]
  rw [card_isoSet R Z _ _ _ φ0 hφ0, ← card_isoZZ R Z Z' _ _ _ φ0 hφ0]
  by_cases hN : Nat.card (autSet R (C a0) (e a0) (lam a0)) = 0
  · have hM : Nat.card (isoSet R Z' (C a0) (e a0) (lam a0)) = 0 := by
      by_cases hE : (isoSet R Z' (C a0) (e a0) (lam a0)).Nonempty
      · obtain ⟨ρ, hρ⟩ := hE
        rw [card_isoSet R Z' _ _ _ ρ hρ, hN]
      · rw [Set.not_nonempty_iff_eq_empty] at hE
        rw [hE]; simp
    simp [hN, hM]
  · have : (Nat.card (autSet R (C a0) (e a0) (lam a0)) : ℂ) ≠ 0 := by exact_mod_cast hN
    field_simp

end Count

end Formalism.FourierDecayAlt.P.A5x4

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.A5x4

theorem gram_kernel_identity : Formalism.FourierDecayAlt.A5.GramIdentity := by
  intro K _ _ _ R ψ hL w w' μ₁ μ₂ μ₁' μ₂' _ _ _ _ _ _ _ _ h1 h2 h1' h2' ι _ C _ _ e lam hne hex
  have hf := integral_points_finite K R ψ hL w
  have hf' := integral_points_finite K R ψ hL w'
  rw [Kp_eq_sum R ψ w w' hf hf']
  have hterm : ∀ a, BB R w.1 w.2 ψ (C a) (e a) (lam a) μ₁ μ₂ *
        conj (BB R w'.1 w'.2 ψ (C a) (e a) (lam a) μ₁' μ₂') /
        (Nat.card (autSet R (C a) (e a) (lam a)) : ℂ) =
      ∑ q ∈ hf.toFinset, ∑ q' ∈ hf'.toFinset,
        ((Nat.card (isoSet R (orbZ w (rep R q)) (C a) (e a) (lam a)) : ℂ) *
        (Nat.card (isoSet R (orbZ w' (rep R q')) (C a) (e a) (lam a)) : ℂ) /
        (Nat.card (autSet R (C a) (e a) (lam a)) : ℂ)) * phase ψ (rep R q) *
        conj (phase ψ (rep R q')) := by
    intro a
    rw [BB_eq_sum R ψ hL w μ₁ μ₂ h1 h2 (C a) (e a) (lam a) hf,
      BB_eq_sum R ψ hL w' μ₁' μ₂' h1' h2' (C a) (e a) (lam a) hf', map_sum,
      Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun q' _ => ?_
    rw [map_mul, map_natCast]
    ring
  rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q' _ => ?_
  have hq1 : IsInt R (orbZ w (rep R q)) := by simpa using hq
  rw [← isoCount R (orbZ w (rep R q)) (orbZ w' (rep R q')) ι C e lam hne (hex _ hq1),
    Finset.sum_mul, Finset.sum_mul]

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.A5x4

section Groupoid

variable {K : Type} [CommRing K] (R : Subring K)

theorem lamLin_mk_eq {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) {v v' : Fin n → R}
    (h : (Submodule.Quotient.mk v : coker R Z) = Submodule.Quotient.mk v') :
    lamLin R Z v = lamLin R Z v' := by
  have h1 : v - v' ∈ latZ R Z := (Submodule.Quotient.eq _).1 h
  obtain ⟨y, hy⟩ := (Formalism.DoubleCosetMeasures.P.mem_latZ R Z _).1 h1
  have h2 : lamLin R Z (v - v') = 0 := by
    rw [Formalism.DoubleCosetMeasures.P.lamLin_apply, ← hy, Matrix.mulVec_mulVec]
    by_cases hd : IsUnit Z.det
    · rw [Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Formalism.DoubleCosetMeasures.P.lastCoord_apply]
      refine Submodule.sum_mem _ fun j _ => ?_
      split_ifs
      · exact ⟨y j, (Formalism.DoubleCosetMeasures.P.coeLin_apply R y j).symm⟩
      · exact Submodule.zero_mem _
    · rw [Matrix.nonsing_inv_apply_not_isUnit _ hd]
      simp
  rw [map_sub, sub_eq_zero] at h2
  exact h2

theorem isoZZ_refl {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) :
    LinearEquiv.refl R (coker R Z) ∈ isoZZ R Z Z :=
  ⟨rfl, fun _ _ h => (lamLin_mk_eq R Z h).symm⟩

theorem isoZZ_symm {n n' : ℕ} {Z : Matrix (Fin n) (Fin n) K} {Z' : Matrix (Fin n') (Fin n') K}
    {φ : coker R Z ≃ₗ[R] coker R Z'} (h : φ ∈ isoZZ R Z Z') : φ.symm ∈ isoZZ R Z' Z := by
  refine ⟨by rw [← h.1]; simp, fun v' v hv => ?_⟩
  have : φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' := by rw [← hv]; simp
  exact (h.2 v v' this).symm

theorem isoZZ_trans {n n' n'' : ℕ} {Z : Matrix (Fin n) (Fin n) K}
    {Z' : Matrix (Fin n') (Fin n') K} {Z'' : Matrix (Fin n'') (Fin n'') K}
    {φ : coker R Z ≃ₗ[R] coker R Z'} {φ' : coker R Z' ≃ₗ[R] coker R Z''}
    (h : φ ∈ isoZZ R Z Z') (h' : φ' ∈ isoZZ R Z' Z'') : φ.trans φ' ∈ isoZZ R Z Z'' := by
  refine ⟨by simp [h.1, h'.1], fun v v'' hv => ?_⟩
  obtain ⟨v', hv'⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk v))
  simp only [LinearEquiv.trans_apply] at hv
  rw [← hv'] at hv
  rw [h'.2 v' v'' hv, h.2 v v' hv'.symm]

theorem card_isoZZ_congr {n n' m m' : ℕ} {A : Matrix (Fin n) (Fin n) K}
    {A' : Matrix (Fin n') (Fin n') K} {B : Matrix (Fin m) (Fin m) K}
    {B' : Matrix (Fin m') (Fin m') K}
    {φ1 : coker R A ≃ₗ[R] coker R A'} {φ2 : coker R B ≃ₗ[R] coker R B'}
    (h1 : φ1 ∈ isoZZ R A A') (h2 : φ2 ∈ isoZZ R B B') :
    Nat.card (isoZZ R A B) = Nat.card (isoZZ R A' B') := by
  refine Nat.card_congr ⟨fun φ => ⟨φ1.symm.trans (φ.1.trans φ2), ?_⟩,
    fun ρ => ⟨φ1.trans (ρ.1.trans φ2.symm), ?_⟩, ?_, ?_⟩
  · exact isoZZ_trans R (isoZZ_symm R h1) (isoZZ_trans R φ.2 h2)
  · exact isoZZ_trans R h1 (isoZZ_trans R ρ.2 (isoZZ_symm R h2))
  · intro φ; ext x; simp
  · intro ρ; ext x; simp

end Groupoid

section PSD

theorem sum_of_classes {T Q : Type} [Fintype T] [Fintype Q] [DecidableEq Q] (f : T → Q)
    (μ : Q → ℝ) (c : T → ℂ) :
    ∑ i, ∑ j, c i * conj (c j) * (if f i = f j then (μ (f i) : ℂ) else 0) =
      ((∑ κ, μ κ * Complex.normSq (∑ i, if f i = κ then c i else 0) : ℝ) : ℂ) := by
  have h : ∀ κ, ((μ κ * Complex.normSq (∑ i, if f i = κ then c i else 0) : ℝ) : ℂ) =
      ∑ i, ∑ j, (μ κ : ℂ) * ((if f i = κ then c i else 0) *
        conj (if f j = κ then c j else 0)) := by
    intro κ
    rw [Complex.ofReal_mul, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [Complex.ofReal_sum, Finset.sum_congr rfl fun κ _ => h κ,
    Finset.sum_comm (s := (Finset.univ : Finset Q))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset Q))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (f i)]
  · by_cases h : f i = f j
    · simp [h]; ring
    · have h' : ¬ f j = f i := fun e => h e.symm
      simp [h, h']
  · intro κ _ hκ
    have : ¬ f i = κ := fun e => hκ e.symm
    simp [this]
  · simp

theorem psd_of_rel {T : Type} [Fintype T] (r : Setoid T) (N : T → T → ℕ)
    (h0 : ∀ i j, ¬ r i j → N i j = 0) (h1 : ∀ i j k, r i j → r i k → N i j = N k k)
    (c : T → ℂ) :
    (∑ i, ∑ j, c i * conj (c j) * (N i j : ℂ)).im = 0 ∧
      0 ≤ (∑ i, ∑ j, c i * conj (c j) * (N i j : ℂ)).re := by
  classical
  have key : ∑ i, ∑ j, c i * conj (c j) * (N i j : ℂ) =
      ((∑ κ : Quotient r, ((N κ.out κ.out : ℕ) : ℝ) *
        Complex.normSq (∑ i, if (Quotient.mk r i) = κ then c i else 0) : ℝ) : ℂ) := by
    rw [← sum_of_classes (fun i => Quotient.mk r i) (fun κ => ((N κ.out κ.out : ℕ) : ℝ)) c]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    by_cases h : r i j
    · rw [if_pos (Quotient.sound h),
        h1 i j (Quotient.mk r i).out h (Setoid.symm (Quotient.mk_out i))]
      simp
    · rw [if_neg (fun e => h (Quotient.exact e)), h0 i j h]
      simp
  rw [key]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact Finset.sum_nonneg fun κ _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

end PSD

end Formalism.FourierDecayAlt.P.A5x4

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.A5x4

theorem kernel_gram_property : Formalism.FourierDecayAlt.A5.KpGram := by
  intro K _ _ _ R ψ hL F a
  classical
  have hfin := integral_points_finite K R ψ hL
  let I : ∀ x : Point K, Finset (Cos R x) := fun x => (hfin x).toFinset
  let S : Finset (Σ x : Point K, Cos R x) := F.sigma I
  let c : (Σ x : Point K, Cos R x) → ℂ := fun i => a i.1 * phase ψ (rep R i.2)
  let N : (Σ x : Point K, Cos R x) → (Σ x : Point K, Cos R x) → ℕ :=
    fun i j => Nat.card (isoZZ R (orbZ i.1 (rep R i.2)) (orbZ j.1 (rep R j.2)))
  have hsum : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * Kp R ψ x y =
      ∑ i : S, ∑ j : S, c i * conj (c j) * (N i j : ℂ) := by
    rw [Finset.sum_coe_sort S (fun i => ∑ j : S, c i * conj (c j) * (N i j : ℂ))]
    have hin : ∀ i, ∑ j : S, c i * conj (c j) * (N i j : ℂ) =
        ∑ y ∈ F, ∑ q' ∈ I y, c i * conj (c ⟨y, q'⟩) * (N i ⟨y, q'⟩ : ℂ) := by
      intro i
      rw [Finset.sum_coe_sort S (fun j => c i * conj (c j) * (N i j : ℂ)), Finset.sum_sigma]
    rw [Finset.sum_congr rfl fun i _ => hin i, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Kp_eq_sum R ψ x y (hfin x) (hfin y), Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q' _ => ?_
    simp only [c, N, map_mul]
    ring
  rw [hsum]
  let r : Setoid S :=
    { r := fun i j => (isoZZ R (orbZ i.1.1 (rep R i.1.2)) (orbZ j.1.1 (rep R j.1.2))).Nonempty
      iseqv := ⟨fun i => ⟨_, isoZZ_refl R _⟩, fun ⟨_, h⟩ => ⟨_, isoZZ_symm R h⟩,
        fun ⟨_, h⟩ ⟨_, h'⟩ => ⟨_, isoZZ_trans R h h'⟩⟩ }
  refine psd_of_rel r (fun i j => N i j) ?_ ?_ (fun i => c i)
  · intro i j h
    have h' : isoZZ R (orbZ i.1.1 (rep R i.1.2)) (orbZ j.1.1 (rep R j.1.2)) = ∅ :=
      Set.not_nonempty_iff_eq_empty.1 h
    simp only [N]
    rw [h']
    simp
  · rintro i j k ⟨φ, hφ⟩ ⟨φ', hφ'⟩
    exact card_isoZZ_congr R hφ' (isoZZ_trans R (isoZZ_symm R hφ) hφ')

end Formalism.FourierDecayAlt.P
