import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV

noncomputable section

namespace GlobalTheory.DRFil

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']

theorem spans_iff (ρ : Representation LL G V) : Spans PD ρ ↔
    ∀ y, y ∈ Submodule.span LL {z | ∃ (b : F), ∃ d ∈ DdR PD ρ, z = mulR Qp F LL V b d} := by
  refine ⟨fun h y => ?_, fun h y => ?_⟩
  · obtain ⟨m, b, d, hd, rfl⟩ := h y
    exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨b i, d i, hd i, rfl⟩
  · obtain ⟨m, c, z, rfl⟩ := Submodule.mem_span_set'.1 (h y)
    choose b d hd hz using fun i => (z i).2
    exact ⟨m, b, fun i => c i • d i, fun i => Submodule.smul_mem _ _ (hd i), by simp only [hz, map_smul]⟩

theorem mulR_mulR (b b' : F) (x : V ⊗[Qp] F) :
    mulR Qp F LL V b (mulR Qp F LL V b' x) = mulR Qp F LL V (b * b') x := by
  simp only [← sm_one_tmul, ← sm_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem mulR_one (x : V ⊗[Qp] F) : mulR Qp F LL V 1 x = x := by
  rw [← sm_one_tmul, ← Algebra.TensorProduct.one_def, sm_one]

theorem mulR_mem_FilV {a n : ℤ} {b : F} {x : V ⊗[Qp] F} (hb : b ∈ PD.Fil a)
    (hx : x ∈ FilV PD (LL := LL) (V := V) n) :
    mulR Qp F LL V b x ∈ FilV PD (LL := LL) (V := V) (a + n) := by
  rw [← sm_one_tmul]
  exact sm_mem_FilV PD (tmul_mem_FilV PD 1 hb) hx

abbrev tensBil (E : V ⊗[LL] V' ≃ₗ[LL] V'') : V →ₗ[LL] V' →ₗ[LL] V'' :=
  (TensorProduct.mk LL V V').compr₂ E.toLinearMap

theorem bil_mem_DdR (ρ : Representation LL G V) (ρ' : Representation LL G V') (ρ'' : Representation LL G V'')
    (β : V →ₗ[LL] V' →ₗ[LL] V'') (hβ : ∀ g v w, β (ρ g v) (ρ' g w) = ρ'' g (β v w))
    {x : V ⊗[Qp] F} {y : V' ⊗[Qp] F} (hx : x ∈ DdR PD ρ) (hy : y ∈ DdR PD ρ') :
    bil Qp F β x y ∈ DdR PD ρ'' :=
  (mem_DdR PD _ _).2 fun g => by
    rw [act_bil PD ρ ρ' ρ'' β hβ, (mem_DdR PD _ _).1 hx, (mem_DdR PD _ _).1 hy]

theorem tmul_eq_sm_bil (E : V ⊗[LL] V' ≃ₗ[LL] V'') (v : V) (w : V') (b : F) :
    E (v ⊗ₜ[LL] w) ⊗ₜ[Qp] b = sm Qp F LL V'' ((1 : LL) ⊗ₜ[Qp] b)
      (bil Qp F (tensBil E) (v ⊗ₜ[Qp] (1 : F)) (w ⊗ₜ[Qp] (1 : F))) := by
  simp

theorem Spans.tensor {ρ : Representation LL G V} {ρ' : Representation LL G V'} {ρ'' : Representation LL G V''}
    (E : V ⊗[LL] V' ≃ₗ[LL] V'') (hE : ∀ g x y, ρ'' g (E (x ⊗ₜ[LL] y)) = E (ρ g x ⊗ₜ[LL] ρ' g y))
    (h : Spans PD ρ) (h' : Spans PD ρ') : Spans PD ρ'' := by
  rw [spans_iff]
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul u b =>
    obtain ⟨t, rfl⟩ := E.surjective u
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add, add_tmul] using Submodule.add_mem _ hx hy
    | tmul v w =>
      obtain ⟨m, c, d, hd, h1⟩ := h (v ⊗ₜ[Qp] (1 : F))
      obtain ⟨m', c', d', hd', h2⟩ := h' (w ⊗ₜ[Qp] (1 : F))
      rw [tmul_eq_sm_bil, h1, h2]
      simp only [map_sum, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => Submodule.subset_span
        ⟨b * (c i * c' j), _, bil_mem_DdR PD ρ ρ' ρ'' (tensBil E) (fun g v w => (hE g v w).symm)
          (hd i) (hd' j), ?_⟩
      rw [← sm_one_tmul (c i), ← sm_one_tmul (c' j), bil_sm_left, bil_sm_right]
      simp only [sm_one_tmul, mulR_mulR]

section Twist

variable (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V') (w : F) (ψ : G → Qp)
  (hw : ∀ g, PD.actdR g w = ψ g • w) (hf : ∀ g x, ψ g • ρ' g (f x) = f (ρ g x))
include hw hf

theorem twist_mem_DdR {x : V ⊗[Qp] F} (hx : x ∈ DdR PD ρ) :
    mulR Qp F LL V' w (ext Qp F f x) ∈ DdR PD ρ' := by
  rw [mem_DdR] at hx ⊢
  intro g
  have : ∀ x, actVdR PD ρ' g (mulR Qp F LL V' w (ext Qp F f x)) =
      mulR Qp F LL V' w (ext Qp F f (actVdR PD ρ g x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v b => simp [hw, ← hf, TensorProduct.smul_tmul]
  rw [this, hx]

theorem twist_mem_FildR (τ : K →ₐ[Qp] LL) {n a : ℤ} (hn : w ∈ PD.Fil n) {x : V ⊗[Qp] F}
    (hx : x ∈ FildR PD ρ τ a) : mulR Qp F LL V' w (ext Qp F f x) ∈ FildR PD ρ' τ (n + a) := by
  refine ⟨(mem_DdRE PD _ _ _).2 ⟨twist_mem_DdR PD ρ ρ' f w ψ hw hf hx.1.1, fun c => ?_⟩,
    mulR_mem_FilV PD hn (ext_mem_FilV PD f hx.2)⟩
  rw [mulR_mulR, mul_comm, ← mulR_mulR, ← sm_one_tmul (algebraMap K F c), ← ext_sm, sm_one_tmul,
    ((mem_DdRE PD _ _ _).1 hx.1).2 c, map_smul, map_smul]

end Twist

theorem exists_twist_equiv (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (h : IsTwistRep (cycLL PD LL) ρ ρ') (u : F) (hu : PD.ι PD.t * u = 1) (hu' : u ∈ PD.Fil (-1)) :
    ∃ Φ : V ⊗[Qp] F ≃ₗ[LL] V' ⊗[Qp] F, (DdR PD ρ).map Φ.toLinearMap = DdR PD ρ' ∧
      ∀ τ a, (FildR PD ρ τ a).map Φ.toLinearMap = FildR PD ρ' τ (a - 1) := by
  obtain ⟨e, he⟩ := h
  have he' : ∀ g x, ρ' g (e x) = ((PD.χ g : Qpˣ) : Qp) • e (ρ g x) := fun g x => by
    rw [he]
    exact algebraMap_smul LL _ _
  have hsm : ∀ (q : Qp) (b : B), PD.ι (q • b) = q • PD.ι b := fun q b =>
    (PD.ι.toLinearMap.restrictScalars Qp).map_smul q b
  have ht : ∀ g, PD.actdR g (PD.ι PD.t) = ((PD.χ g : Qpˣ) : Qp) • PD.ι PD.t := fun g => by
    rw [← PD.ι_comm, PD.t_act, hsm]
  have hug : ∀ g, PD.actdR g u = ((PD.χ g : Qpˣ) : Qp)⁻¹ • u := fun g => by
    have h1 := congrArg (PD.actdR g) hu
    rw [map_mul, map_one, ht, smul_mul_assoc] at h1
    have h2 := congrArg (fun z => ((PD.χ g : Qpˣ) : Qp)⁻¹ • (u * z)) h1
    simp only [mul_smul_comm, smul_smul, ← mul_assoc, mul_comm u (PD.ι PD.t), hu, one_mul, mul_one] at h2
    rw [inv_mul_cancel₀ (Units.ne_zero _), one_smul] at h2
    exact h2
  have f1 : ∀ g x, ((PD.χ g : Qpˣ) : Qp)⁻¹ • ρ' g (e.toLinearMap x) = e.toLinearMap (ρ g x) := fun g x => by
    simp [he', smul_smul]
  have f2 : ∀ g x, ((PD.χ g : Qpˣ) : Qp) • ρ g (e.symm.toLinearMap x) = e.symm.toLinearMap (ρ' g x) := by
    intro g x
    obtain ⟨x, rfl⟩ := e.surjective x
    apply e.injective
    simp [he']
  let Φ : V ⊗[Qp] F →ₗ[LL] V' ⊗[Qp] F := mulR Qp F LL V' u ∘ₗ ext Qp F e.toLinearMap
  let Ψ : V' ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F := mulR Qp F LL V (PD.ι PD.t) ∘ₗ ext Qp F e.symm.toLinearMap
  have h1 : ∀ x, Φ (Ψ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v b => simp [Φ, Ψ, ← mul_assoc, (mul_comm u _).trans hu]
  have h2 : ∀ x, Ψ (Φ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v b => simp [Φ, Ψ, ← mul_assoc, hu]
  refine ⟨LinearEquiv.ofLinear Φ Ψ (LinearMap.ext h1) (LinearMap.ext h2), le_antisymm ?_ fun y hy => ?_,
    fun τ a => le_antisymm ?_ fun y hy => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact twist_mem_DdR PD ρ ρ' _ u _ hug f1 hx
  · exact ⟨Ψ y, twist_mem_DdR PD ρ' ρ _ _ _ ht f2 hy, h1 y⟩
  · rintro _ ⟨x, hx, rfl⟩
    have := twist_mem_FildR PD ρ ρ' _ u _ hug f1 τ hu' hx
    rwa [neg_add_eq_sub] at this
  · have := twist_mem_FildR PD ρ' ρ _ _ _ ht f2 τ PD.mem_filtration_one hy
    rw [add_sub_cancel] at this
    exact ⟨Ψ y, this, h1 y⟩

variable [FiniteDimensional Qp K] [CharZero Qp]

theorem idem_notMem_FilV_one (τ : K →ₐ[Qp] LL) : idem F τ ∉ FilV PD (LL := LL) (V := LL) 1 := by
  intro h
  have := nontrivial_dR PD
  refine idem_ne_zero (F := F) τ (eq_zero_of_forall_mem_FilV PD (LL := LL) _ fun a => ?_)
  have hn : ∀ n : ℕ, idem F τ ∈ FilV PD (LL := LL) (V := LL) n := by
    intro n
    induction n with
    | zero => exact idem_mem_FilV PD τ
    | succ n ih => simpa [idem_mul_idem] using mul_mem_FilV PD ih h
  exact FilV_antitone PD (Int.self_le_toNat a) (hn a.toNat)

theorem FildR_antitone (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) : Antitone (FildR PD ρ τ) :=
  fun _ _ h => inf_le_inf_left _ (FilV_antitone PD h)

namespace Adapted

variable {PD} {ρ : Representation LL G V} {τ : K →ₐ[Qp] LL} {ι : Type} [Fintype ι]
    {d : ι → V ⊗[Qp] F} {k : ι → ℤ} (h : Adapted PD ρ τ d k)
include h

theorem sm_idem (i : ι) : sm Qp F LL V (idem F τ) (d i) = d i := sm_idem_of_mem_DdRE PD ρ τ (h.mem i).1

theorem linearIndependent : LinearIndependent LL d := by
  have := nontrivial_dR PD
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h1 := h.indep (fun i => c i • 1) (by simpa using hc) i
  rw [mul_smul_comm, mul_one] at h1
  exact (smul_eq_zero.1 h1).resolve_right (idem_ne_zero τ)

theorem fil_eq (a : ℤ) : FildR PD ρ τ a = Submodule.span LL (d '' {i | a ≤ k i}) := by
  refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨r, hr, hy'⟩ := h.span a y hy.2
    rw [sm_idem_of_mem_DdRE PD ρ τ hy.1] at hy'
    have hinv : ∀ i g, actR PD LL g (idem F τ * r i) = idem F τ * r i := by
      intro i g
      have := h.indep (fun i => actR PD LL g (r i) - r i) (by
        have h1 := (mem_DdR PD ρ y).1 hy.1.1 g
        rw [hy', map_sum] at h1
        simp only [act_sm, (mem_DdR PD ρ _).1 (h.mem _).1.1 g] at h1
        simp only [map_sub, LinearMap.sub_apply, Finset.sum_sub_distrib, h1, sub_self]) i
      rw [actR_mul, actR_idem, ← sub_eq_zero, ← mul_sub, this]
    have hc : ∀ i, ∃ c : LL, idem F τ * r i = c • idem F τ := by
      intro i
      obtain ⟨n, a, c, hn⟩ := exists_of_actR_fixed PD _ (hinv i)
      exact ⟨_, by rw [← exists_smul_idem τ n a c, ← hn, ← mul_assoc, idem_mul_idem]⟩
    choose c hc using hc
    rw [hy']
    refine Submodule.sum_mem _ fun i _ => ?_
    have e1 : sm Qp F LL V (r i) (d i) = c i • d i := by
      rw [← h.sm_idem i, ← sm_mul, mul_comm, hc, map_smul, LinearMap.smul_apply, h.sm_idem i]
    rw [e1]
    by_cases hi : a ≤ k i
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · by_cases h0 : c i = 0
      · simp [h0]
      · exfalso
        have h1 := mul_mem_FilV PD (idem_mem_FilV PD τ) (hr i)
        rw [hc] at h1
        have h2 := Submodule.smul_mem _ (c i)⁻¹ h1
        rw [smul_smul, inv_mul_cancel₀ h0, one_smul] at h2
        exact idem_notMem_FilV_one PD τ (FilV_antitone PD (by omega) h2)
  · rintro _ ⟨i, hi, rfl⟩
    exact FildR_antitone PD ρ τ hi (h.mem i)

theorem finrank_fil (a : ℤ) :
    finrank LL ↥(FildR PD ρ τ a) = (Finset.univ.filter fun i => a ≤ k i).card := by
  rw [h.fil_eq, Set.image_eq_range]
  exact (finrank_span_eq_card (h.linearIndependent.comp (Subtype.val : {i | a ≤ k i} → ι)
    Subtype.val_injective)).trans (Fintype.card_subtype _)

theorem multV_eq (a : ℤ) : multV PD ρ τ a = ∑ i, if k i = a then 1 else 0 := by
  rw [multV, h.finrank_fil, h.finrank_fil, Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> omega

theorem isJumpV_iff (a : ℤ) : IsJumpV PD ρ τ a ↔ ∃ i, k i = a := by
  refine ⟨fun hj => ?_, fun ⟨i, hi⟩ hj => ?_⟩
  · by_contra hn
    push Not at hn
    apply hj
    rw [h.fil_eq, h.fil_eq]
    congr 2
    ext i
    have := hn i
    simp only [Set.mem_setOf_eq]
    omega
  · have h1 := h.multV_eq a
    rw [multV, hj, sub_self] at h1
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h1.symm i (Finset.mem_univ i)
    simp [hi] at this

theorem dual [FiniteDimensional LL V] (ρ' : Representation LL G V') (β : V →ₗ[LL] V' →ₗ[LL] LL)
    (hβ : ∀ g x y, β (ρ g x) (ρ' g y) = β x y) (hβ' : Function.Bijective β.flip) :
    ∃ d' : ι → V' ⊗[Qp] F, Adapted PD ρ' τ d' fun i => -k i := by
  classical
  obtain ⟨v, w, hvw⟩ := exists_dual_bases β hβ'
  choose r hr hr' using fun a => h.span 0 (v a ⊗ₜ[Qp] (1 : F)) (tmul_mem_FilV PD _ PD.one_mem)
  obtain ⟨h1, h2, h3⟩ := dual_family PD ρ ρ' β hβ v w hvw (idem F τ) (idem_mul_idem τ) (actR_idem PD τ) d
    (fun i => (h.mem i).1.1) h.sm_idem h.indep r hr' _ (fun _ => rfl)
  refine ⟨_, fun i => ⟨?_, ?_⟩, fun s hs i => ?_, fun n y hy => ⟨_, fun i => ?_, h3 y⟩⟩
  · have := sm_idem_mem_DdRE PD ρ' τ (h1 i)
    rwa [sm_idem_idem] at this
  · refine sm_idem_mem_FilV PD τ (Submodule.sum_mem _ fun a _ => ?_)
    simpa using sm_mem_FilV PD (hr a i) (tmul_mem_FilV PD (w a) PD.one_mem)
  · have := congrArg (bil Qp F β (d i)) hs
    rw [map_sum, map_zero] at this
    simp only [bil_sm_right β (s _), h2, sm_self] at this
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)] at this
    simpa [mul_comm] using this
  · have := bil_mem_FilV PD β (h.mem i).2 hy
    rwa [show k i + n = n - -k i by ring] at this

theorem tensor {ρ' : Representation LL G V'} {ι' : Type} [Fintype ι'] {d' : ι' → V' ⊗[Qp] F} {k' : ι' → ℤ}
    (h' : Adapted PD ρ' τ d' k') (ρ'' : Representation LL G V'') (E : V ⊗[LL] V' ≃ₗ[LL] V'')
    (hE : ∀ g x y, ρ'' g (E (x ⊗ₜ[LL] y)) = E (ρ g x ⊗ₜ[LL] ρ' g y)) :
    Adapted PD ρ'' τ (fun p : ι × ι' => bil Qp F (tensBil E) (d p.1) (d' p.2)) fun p => k p.1 + k' p.2 := by
  refine ⟨fun p => ⟨?_, bil_mem_FilV PD _ (h.mem p.1).2 (h'.mem p.2).2⟩, fun r hr p => ?_, fun n y hy => ?_⟩
  · have := sm_idem_mem_DdRE PD ρ'' τ (bil_mem_DdR PD ρ ρ' ρ'' (tensBil E) (fun g v w => (hE g v w).symm)
      (h.mem p.1).1.1 (h'.mem p.2).1.1)
    rwa [← bil_sm_left, h.sm_idem] at this
  · have key : ∑ j, sm Qp F LL V' (idem F τ * r (p.1, j)) (d' j) = 0 := by
      refine eq_zero_of_forall_ext (LL := LL) _ fun φ => ?_
      let C : V'' →ₗ[LL] V := (TensorProduct.rid LL V).toLinearMap ∘ₗ φ.lTensor V ∘ₗ E.symm.toLinearMap
      have hC : ∀ x y, ext Qp F C (bil Qp F (tensBil E) x y) = sm Qp F LL V (ext Qp F φ y) x := by
        intro x y
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs]
        | tmul v b' =>
          induction y using TensorProduct.induction_on with
          | zero => simp
          | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs]
          | tmul w b'' => simp [C, mul_comm]
      have h1 := congrArg (ext Qp F C) hr
      rw [map_sum, map_zero, Fintype.sum_prod_type] at h1
      simp only [ext_sm, hC, ← sm_mul] at h1
      have h2 := h.indep (fun i => ∑ j, r (i, j) * ext Qp F φ (d' j))
        (by simpa only [map_sum, LinearMap.sum_apply] using h1) p.1
      rw [map_sum]
      simp only [ext_sm, sm_self, mul_assoc]
      rw [← Finset.mul_sum, h2]
    have := h'.indep _ key p.2
    rwa [← mul_assoc, idem_mul_idem] at this
  · let q : V'' ⊗[Qp] F → Prop := fun y => ∃ r : ι × ι' → LL ⊗[Qp] F,
      (∀ p, r p ∈ FilV PD (LL := LL) (V := LL) (n - (k p.1 + k' p.2))) ∧
        sm Qp F LL V'' (idem F τ) y = ∑ p, sm Qp F LL V'' (r p) (bil Qp F (tensBil E) (d p.1) (d' p.2))
    have q0 : q 0 := ⟨0, fun _ => Submodule.zero_mem _, by simp⟩
    have qa : ∀ x y, q x → q y → q (x + y) := by
      rintro x y ⟨r, hr, hx⟩ ⟨s, hs, hy⟩
      exact ⟨r + s, fun p => Submodule.add_mem _ (hr p) (hs p), by
        simp only [map_add, hx, hy, Pi.add_apply, LinearMap.add_apply, Finset.sum_add_distrib]⟩
    refine FilV_induction PD (p := q) q0 (fun u b hb => ?_) qa hy
    obtain ⟨t, rfl⟩ := E.surjective u
    induction t using TensorProduct.induction_on with
    | zero => simpa using q0
    | add x y hx hy => simpa only [map_add, add_tmul] using qa _ _ hx hy
    | tmul v w =>
      obtain ⟨r, hr, h1⟩ := h.span 0 (v ⊗ₜ[Qp] (1 : F)) (tmul_mem_FilV PD _ PD.one_mem)
      obtain ⟨s, hs, h2⟩ := h'.span 0 (w ⊗ₜ[Qp] (1 : F)) (tmul_mem_FilV PD _ PD.one_mem)
      refine ⟨fun p => ((1 : LL) ⊗ₜ[Qp] b) * (r p.1 * s p.2), fun p => ?_, ?_⟩
      · have := mul_mem_FilV PD (tmul_mem_FilV PD (1 : LL) hb) (mul_mem_FilV PD (hr p.1) (hs p.2))
        rwa [show n + (0 - k p.1 + (0 - k' p.2)) = n - (k p.1 + k' p.2) by ring] at this
      · rw [tmul_eq_sm_bil, sm_comm, ← sm_idem_idem, ← bil_sm_right, ← bil_sm_left, h1, h2,
          Fintype.sum_prod_type_right, map_sum, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_sum, LinearMap.sum_apply, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [bil_sm_left, bil_sm_right, sm_mul, sm_mul]

end Adapted

end GlobalTheory.DRFil
