import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedAdjoint

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
open GlobalTheory.RealPar.DerivedAdjoint
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift.CoverKernel

variable {p q r s : ℕ}

theorem exists_real_imag (Z : Mat p q) : ∃ X Y : Mat p q, X ∈ upq p q ∧ Y ∈ upq p q ∧
    Z = X + Complex.I • Y ∧ adjZ Z = -X + Complex.I • Y := by
  have hs : star ((2:ℂ)⁻¹) = (2:ℂ)⁻¹ := by simp
  have hs' : star (-(Complex.I * (2:ℂ)⁻¹)) = Complex.I * (2:ℂ)⁻¹ := by
    simp [Complex.conj_I]
  have hc : Complex.I * -(Complex.I * (2:ℂ)⁻¹) = (2:ℂ)⁻¹ := by
    linear_combination (-(2:ℂ)⁻¹) * Complex.I_sq
  refine ⟨(2:ℂ)⁻¹ • (Z - adjZ Z), (-(Complex.I * (2:ℂ)⁻¹)) • (Z + adjZ Z),
    mem_upq_of_adjZ ?_, mem_upq_of_adjZ ?_, ?_, ?_⟩
  · rw [adjZ_smul, adjZ_sub, adjZ_adjZ, hs]
    module
  · rw [adjZ_smul, adjZ_add, adjZ_adjZ, hs']
    module
  · rw [smul_smul, hc]
    module
  · rw [smul_smul, hc]
    module

theorem adjRule_of_pair {N : GKMod r s} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    {B : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z} (h : IsCoverPair N B) : AdjRule B := by
  intro X P P' y y'
  obtain ⟨A, C, hA, hC, rfl, hadj⟩ := exists_real_imag X
  rw [hadj]
  have sA := h.skew A hA P P' y y'
  have sC := h.skew C hC P P' y y'
  simp only [map_add, map_smul, map_neg, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_neg_right, Complex.conj_I]
  linear_combination sA - Complex.I * sC

theorem invRule_of_pair {N : GKMod r s} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    {B : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z} (h : IsCoverPair N B) : InvRule N B := by
  intro Y P y
  obtain ⟨A, C, hA, hC, rfl, hadj⟩ := exists_real_imag Y
  rw [hadj]
  have iA := eq_neg_of_add_eq_zero_left (h.inv A hA P y)
  have iC := eq_neg_of_add_eq_zero_left (h.inv C hC P y)
  simp only [map_add, map_smul, map_neg, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, Complex.conj_I]
  rw [iA, iC]
  module

def pairSum {U Y Z₁ Z₂ : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup Y] [Module ℂ Y]
    [NormedAddCommGroup Z₁] [InnerProductSpace ℂ Z₁] [NormedAddCommGroup Z₂] [InnerProductSpace ℂ Z₂]
    (B₁ : U →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z₁) (B₂ : U →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z₂) :
    U →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] WithLp 2 (Z₁ × Z₂) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun P y => WithLp.toLp 2 (B₁ P y, B₂ P y))
    (fun _ _ _ => by simp [← WithLp.toLp_add])
    (fun _ _ _ => by simp [← WithLp.toLp_smul])
    (fun _ _ _ => by simp [← WithLp.toLp_add])
    (fun _ _ _ => by simp [← WithLp.toLp_smul])

theorem pairSum_apply {U Y Z₁ Z₂ : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup Y] [Module ℂ Y]
    [NormedAddCommGroup Z₁] [InnerProductSpace ℂ Z₁] [NormedAddCommGroup Z₂] [InnerProductSpace ℂ Z₂]
    (B₁ : U →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z₁) (B₂ : U →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z₂) (P : U) (y : Y) :
    pairSum B₁ B₂ P y = WithLp.toLp 2 (B₁ P y, B₂ P y) := rfl

theorem contr_tmul {A V H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H) (y : V) (a : A) (v : V) :
    contr ι y (a ⊗ₜ[ℂ] v) = ⟪ι y, ι v⟫_ℂ • a := by
  simp [contr]

theorem contr_map_left {A A' V H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
    [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H) (y : V) (g : A →ₗ[ℂ] A') (t : A ⊗[ℂ] V) :
    contr ι y (TensorProduct.map g LinearMap.id t) = g (contr ι y t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp only [TensorProduct.map_tmul, LinearMap.id_apply, contr_tmul, map_smul]
  | add x w hx hw => simp only [map_add, hx, hw]

theorem contr_map_right {A : Type} [AddCommGroup A] [Module ℂ A] {T : GrpData r s} (R : DSRep T)
    (Y : Mat r s) (y : R.HK.V) (t : A ⊗[ℂ] R.HK.V) :
    contr R.ι y (TensorProduct.map LinearMap.id (R.HK.act Y) t) = contr R.ι (R.HK.act (adjZ Y) y) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, contr_tmul]
    congr 1
    have key := derived_adjoint r s T R.U R.HK R.ι R.der (adjZ Y) y v
    rw [adjZ_adjZ] at key
    exact key.symm
  | add x w hx hw => simp only [map_add, hx, hw]

private theorem inner_eq_inner_of_eq_on_spanning {V W : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {S : Set V} (hS : Submodule.span ℂ S = ⊤) (f g k l : V →ₗ[ℂ] W)
    (h : ∀ x ∈ S, ∀ w ∈ S, ⟪f x, g w⟫_ℂ = ⟪k x, l w⟫_ℂ) (x w : V) : ⟪f x, g w⟫_ℂ = ⟪k x, l w⟫_ℂ := by
  have hx : x ∈ Submodule.span ℂ S := by
    rw [hS]
    exact Submodule.mem_top
  have hw : w ∈ Submodule.span ℂ S := by
    rw [hS]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hxS =>
    induction hw using Submodule.span_induction with
    | mem w hwS => exact h x hxS w hwS
    | zero => simp
    | add a b _ _ ha hb => simp only [map_add, inner_add_right, ha, hb]
    | smul c a _ ha => simp only [map_smul, inner_smul_right, ha]
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, inner_add_left, ha, hb]
  | smul c a _ ha => simp only [map_smul, inner_smul_left, ha]

theorem coverKer_of_down : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), Formalism.MainNotions.SchurIrreducible.ARiiiDown X lam lam' → Formalism.MainNotions.SchurIrreducible.IrrGK (X.ds p q lam).HK → UnitaryImage p q r s → FiniteSupport p q (X.ds r s lam') → TensorForm → CoverKer p q (X.ds r s lam').HK := by
  intro X p q r s lam lam' hD hIrr hU hF hT Z₁ Z₂ _ _ _ _ B₁ B₂ h₁ h₂ hne
  unfold Formalism.MainNotions.SchurIrreducible.ARiiiDown at hD
  unfold Formalism.MainNotions.SchurIrreducible.IrrGK at hIrr
  unfold UnitaryImage at hU
  unfold FiniteSupport at hF
  unfold TensorForm at hT

  have hB : IsCoverPair (X.ds r s lam').HK (pairSum B₁ B₂) := by
    constructor
    · intro Y hY P P' y y'
      simp only [pairSum_apply, WithLp.prod_inner_apply]
      linear_combination h₁.skew Y hY P P' y y' + h₂.skew Y hY P P' y y'
    · intro Y hY P y
      rw [pairSum_apply, pairSum_apply, ← WithLp.toLp_add, Prod.mk_add_mk, h₁.inv Y hY P y,
        h₂.inv Y hY P y, Prod.mk_zero_zero, WithLp.toLp_zero]

  obtain ⟨A, j, B', hj, hjB, hspan, hB'act⟩ := hU _ _ (pairSum B₁ B₂) (adjRule_of_pair hB)
  have hinv' : InvRule (X.ds r s lam').HK B' := by
    intro Y P y
    apply hj
    rw [hjB, hjB]
    exact invRule_of_pair hB Y P y

  obtain ⟨hsep, hfac⟩ := hT (Pol p q r s) A.M.V (X.ds r s lam').HK.V (X.ds r s lam').U.H
    (X.ds r s lam').ι (X.ds r s lam').ι_inj
  obtain ⟨f, hf⟩ := hfac B' (hF A.M.V B' hinv')
  have hint1 : ∀ Y : Mat p q,
      f ∘ₗ (X.fock p q r s).act1 Y = TensorProduct.map (A.M.act Y) LinearMap.id ∘ₗ f := by
    intro Y
    refine LinearMap.ext fun P => ?_
    rw [← sub_eq_zero]
    refine hsep _ fun y => ?_
    rw [map_sub, sub_eq_zero, LinearMap.comp_apply, LinearMap.comp_apply, contr_map_left, hf, hf]
    exact hB'act Y P y
  have hint2 : ∀ Y : Mat r s,
      f ∘ₗ (X.fock p q r s).act2 Y = TensorProduct.map LinearMap.id ((X.ds r s lam').HK.act Y) ∘ₗ f := by
    intro Y
    refine LinearMap.ext fun P => ?_
    rw [← sub_eq_zero]
    refine hsep _ fun y => ?_
    rw [map_sub, sub_eq_zero, LinearMap.comp_apply, LinearMap.comp_apply, contr_map_right, hf, hf]
    exact hinv' Y P y
  have hψ : ∀ P y, WithLp.ofLp (j (B' P y)) = (B₁ P y, B₂ P y) := by
    intro P y
    rw [hjB, pairSum_apply, WithLp.ofLp_toLp]
  have hfne : f ≠ 0 := by
    intro hf0
    apply hne
    refine LinearMap.ext fun P => LinearMap.ext fun y => ?_
    have h0 : B' P y = 0 := by rw [← hf, hf0, LinearMap.zero_apply, map_zero]
    have h1 := hψ P y
    rw [h0, map_zero, WithLp.ofLp_zero] at h1
    obtain ⟨e1, -⟩ := Prod.mk.inj (h1.symm.trans Prod.mk_zero_zero.symm)
    rw [LinearMap.zero_apply, LinearMap.zero_apply]
    exact e1
  have hIW : Formalism.BasicNotions.TH.IsIntw (X.fock p q r s) A.M (X.ds r s lam').HK f := by
    unfold Formalism.BasicNotions.TH.IsIntw
    exact ⟨hint1, hint2⟩

  obtain ⟨⟨N, -, e, he, hrange⟩, -⟩ := hD A f hIW hfne
  have memN : ∀ P y, B' P y ∈ N := by
    intro P y
    have hP : f P ∈ LinearMap.range (TensorProduct.map N.subtype LinearMap.id) := by
      rw [← hrange]
      exact LinearMap.mem_range_self f P
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hP
    rw [← hf, ← ht, contr_map_left]
    exact (contr (X.ds r s lam').ι y t).2

  let ψ₁ : A.M.V →ₗ[ℂ] Z₁ :=
    LinearMap.fst ℂ Z₁ Z₂ ∘ₗ (WithLp.linearEquiv 2 ℂ (Z₁ × Z₂)).toLinearMap ∘ₗ j
  let ψ₂ : A.M.V →ₗ[ℂ] Z₂ :=
    LinearMap.snd ℂ Z₁ Z₂ ∘ₗ (WithLp.linearEquiv 2 ℂ (Z₁ × Z₂)).toLinearMap ∘ₗ j
  have hψ₁ : ∀ P y, ψ₁ (B' P y) = B₁ P y := fun P y => congrArg Prod.fst (hψ P y)
  have hψ₂ : ∀ P y, ψ₂ (B' P y) = B₂ P y := fun P y => congrArg Prod.snd (hψ P y)

  have hsesq : ∀ (Y : Mat p q) (x w : A.M.V),
      ⟪ψ₁ (A.M.act Y x), ψ₁ w⟫_ℂ = ⟪ψ₁ x, ψ₁ (A.M.act (adjZ Y) w)⟫_ℂ := by
    intro Y
    refine inner_eq_inner_of_eq_on_spanning hspan (ψ₁ ∘ₗ A.M.act Y) ψ₁ ψ₁ (ψ₁ ∘ₗ A.M.act (adjZ Y)) ?_
    rintro _ ⟨P, y, rfl⟩ _ ⟨P', y', rfl⟩
    simp only [LinearMap.comp_apply]
    rw [← hB'act, ← hB'act]
    simp only [hψ₁]
    exact adjRule_of_pair h₁ Y P P' y y'
  have hstab : ∀ (Y : Mat p q) (x : A.M.V), ψ₁ x = 0 → ψ₁ (A.M.act Y x) = 0 := by
    intro Y x hx
    have h1 := hsesq Y x (A.M.act Y x)
    rw [hx, inner_zero_left] at h1
    exact inner_self_eq_zero.mp h1

  let N' : Submodule ℂ (X.ds p q lam).HK.V := (LinearMap.ker ψ₁).comap (N.subtype ∘ₗ e.toLinearMap)
  have hN'st : ∀ (Y : Mat p q), ∀ x ∈ N', (X.ds p q lam).HK.act Y x ∈ N' := by
    intro Y x hx
    have hx' : ψ₁ ((e x : N) : A.M.V) = 0 := hx
    show ψ₁ ((e ((X.ds p q lam).HK.act Y x) : N) : A.M.V) = 0
    rw [he]
    exact hstab Y _ hx'
  rcases hIrr.2 N' hN'st with hbot | htop
  · intro n a b hsum
    have hwN : ∑ i, B' (a i) (b i) ∈ N := Submodule.sum_mem _ fun i _ => memN (a i) (b i)
    have h1 : ψ₁ (∑ i, B' (a i) (b i)) = 0 := by
      rw [map_sum]
      simp only [hψ₁]
      exact hsum
    have hz : e.symm ⟨_, hwN⟩ ∈ N' := by
      show ψ₁ ((e (e.symm ⟨_, hwN⟩) : N) : A.M.V) = 0
      rw [LinearEquiv.apply_symm_apply]
      exact h1
    rw [hbot, Submodule.mem_bot] at hz
    have h0 : ∑ i, B' (a i) (b i) = 0 := by
      have h3 := congrArg e hz
      rw [LinearEquiv.apply_symm_apply, map_zero] at h3
      exact congrArg Subtype.val h3
    have h2 := congrArg ψ₂ h0
    rw [map_sum, map_zero] at h2
    simp only [hψ₂] at h2
    exact h2
  · exfalso
    apply hne
    refine LinearMap.ext fun P => LinearMap.ext fun y => ?_
    rw [LinearMap.zero_apply, LinearMap.zero_apply, ← hψ₁]
    have hz : e.symm ⟨_, memN P y⟩ ∈ N' := by
      rw [htop]
      exact Submodule.mem_top
    have h1 : ψ₁ ((e (e.symm ⟨_, memN P y⟩) : N) : A.M.V) = 0 := hz
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1

end GlobalTheory.Chain.IoLift.CoverKernel

end
