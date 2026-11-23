import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open scoped TensorProduct
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.TotalFrame

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineSummand

variable {O X k : Type} [CommRing O] [AddCommGroup X] [Module O X] [Field k] {p : ℕ} [CharP k p]

theorem tmul_nsmul_eq_zero (c : k) (y : X) : c ⊗ₜ[ℤ] (p • y) = 0 := by
  show (TensorProduct.mk ℤ k X c) (p • y) = 0
  rw [map_nsmul, TensorProduct.mk_apply, TensorProduct.smul_tmul', nsmul_eq_mul, CharP.cast_eq_zero, zero_mul,
    TensorProduct.zero_tmul]

theorem tmul_eq_zero_of_mem_smul_top {x : X} (hx : x ∈ (Ideal.span {(p : O)} • ⊤ : Submodule O X)) (c : k) :
    c ⊗ₜ[ℤ] x = 0 := by
  refine Submodule.smul_induction_on (p := fun x => c ⊗ₜ[ℤ] x = 0) hx (fun r hr n _ => ?_) fun x y hx hy => ?_
  · obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    have e : (a * (p : O)) • n = p • (a • n) := by rw [mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
    rw [e]
    exact tmul_nsmul_eq_zero c _
  · simp only [TensorProduct.tmul_add, hx, hy, add_zero]

variable (k) in

theorem baseChange_mkQ_injective (P : Submodule O X) (hP : ∀ x ∈ P, ∀ c : k, c ⊗ₜ[ℤ] x = 0) :
    Function.Injective ((P.mkQ.restrictScalars ℤ).baseChange k) := by
  let g : X →ₗ[ℤ] X ⧸ P := P.mkQ.restrictScalars ℤ
  have hex := lTensor_exact k (LinearMap.exact_subtype_ker_map g) P.mkQ_surjective
  rw [LinearMap.baseChange_eq_ltensor]
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨z, rfl⟩ := (hex y).1 hy
  clear hy
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    rw [LinearMap.lTensor_tmul]
    exact hP _ ((Submodule.Quotient.mk_eq_zero P).1 (LinearMap.mem_ker.1 x.2)) c
  | add u v hu hv => rw [map_add, hu, hv, add_zero]

end GlobalTheory.LineSummand

namespace GlobalTheory.LineSummand

variable {O X k : Type} [CommRing O] [AddCommGroup X] [Module O X] [Field k] {p : ℕ} [CharP k p]

variable (k) in

theorem line_summand (P : Submodule O X) (hPz : ∀ x ∈ P, ∀ c : k, c ⊗ₜ[ℤ] x = 0) (l l' : Submodule O (X ⧸ P))
    (h : IsCompl l l')
    (e : l ≃ₗ[O] (O ⧸ Ideal.span {(p : O)})) :
    ∃ (M' : Submodule k (k ⊗[ℤ] X)) (n₀ : k ⊗[ℤ] X),
      IsCompl (Submodule.span k {s | ∃ a : X, Submodule.Quotient.mk a ∈ l ∧ s = 1 ⊗ₜ a}) M' ∧
      (∀ a, ∀ x ∈ Submodule.span k {s | ∃ a : X, Submodule.Quotient.mk a ∈ l ∧ s = 1 ⊗ₜ a},
        baseChangeAction k (Module.toModuleEnd ℤ X : O →+* Module.End ℤ X) a x ∈
          Submodule.span k {s | ∃ a : X, Submodule.Quotient.mk a ∈ l ∧ s = 1 ⊗ₜ a}) ∧
      (∀ a, ∀ x ∈ M', baseChangeAction k (Module.toModuleEnd ℤ X : O →+* Module.End ℤ X) a x ∈ M') ∧
      Submodule.span k {s | ∃ a : X, Submodule.Quotient.mk a ∈ l ∧ s = 1 ⊗ₜ a} =
        Submodule.span k (Set.range fun a => baseChangeAction k (Module.toModuleEnd ℤ X : O →+* Module.End ℤ X) a n₀) ∧
      ∀ t : k ⊗[ℤ] O, tensorAction (baseChangeAction k (Module.toModuleEnd ℤ X : O →+* Module.End ℤ X)) t n₀ = 0 → t = 0 := by
  set ρb : O →+* Module.End k (k ⊗[ℤ] X) := baseChangeAction k (Module.toModuleEnd ℤ X : O →+* Module.End ℤ X)
  let bar : Submodule O (X ⧸ P) → Submodule k (k ⊗[ℤ] X) := fun m =>
    Submodule.span k {s | ∃ a : X, Submodule.Quotient.mk a ∈ m ∧ s = 1 ⊗ₜ a}
  have hρ : ∀ (a : O) (c : k) (x : X), ρb a (c ⊗ₜ x) = c ⊗ₜ (a • x) := fun a c x => by
    simp [ρb, baseChangeAction_apply, LinearMap.baseChange_tmul]
  have hz : ∀ x ∈ P, (1 : k) ⊗ₜ[ℤ] x = 0 := fun x hx => hPz x hx 1

  have hst : ∀ (m : Submodule O (X ⧸ P)) (a : O), ∀ x ∈ bar m, ρb a x ∈ bar m := by
    intro m a x hx
    refine (Submodule.span_le (p := (bar m).comap (ρb a))).2 (fun s hs => ?_) hx
    obtain ⟨b, hb, rfl⟩ := hs
    show ρb a (1 ⊗ₜ b) ∈ bar m
    rw [hρ]
    exact Submodule.subset_span ⟨a • b, by rw [Submodule.Quotient.mk_smul]; exact m.smul_mem a hb, rfl⟩

  have htop : bar l ⊔ bar l' = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul c a =>
      have e1 : c ⊗ₜ[ℤ] a = c • ((1 : k) ⊗ₜ[ℤ] a) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e1]
      refine Submodule.smul_mem _ c ?_
      have hm : (Submodule.Quotient.mk a : X ⧸ P) ∈ l ⊔ l' := h.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨u, hu, u', hu', e2⟩ := Submodule.mem_sup.1 hm
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective P u
      obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective P u'
      have hd : a - b - b' ∈ P := by
        rw [← Submodule.Quotient.mk_eq_zero P, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, ← e2]
        abel
      have e3 : (1 : k) ⊗ₜ[ℤ] a = 1 ⊗ₜ b + 1 ⊗ₜ b' + 1 ⊗ₜ (a - b - b') := by
        rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_add]
        congr 1
        abel
      rw [e3, hz _ hd, add_zero]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨b, hu, rfl⟩) (Submodule.subset_span ⟨b', hu', rfl⟩)
    | add x y hx hy => exact add_mem hx hy

  let π : X →ₗ[ℤ] X ⧸ P := P.mkQ.restrictScalars ℤ
  let proj : (X ⧸ P) →ₗ[O] l := LinearMap.ofIsCompl h LinearMap.id 0
  let q : X →ₗ[ℤ] l := (proj ∘ₗ P.mkQ).restrictScalars ℤ
  let ls : l →ₗ[ℤ] X ⧸ P := l.subtype.restrictScalars ℤ
  have hπ : Function.Injective (π.baseChange k) :=
    baseChange_mkQ_injective k P hPz
  have h1 : bar l ≤ LinearMap.eqLocus (π.baseChange k) ((ls.baseChange k) ∘ₗ (q.baseChange k)) := by
    refine Submodule.span_le.2 fun s hs => ?_
    obtain ⟨b, hb, rfl⟩ := hs
    show π.baseChange k (1 ⊗ₜ b) = ls.baseChange k (q.baseChange k (1 ⊗ₜ b))
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    congr 1
    show Submodule.Quotient.mk b = ((proj (Submodule.Quotient.mk b) : l) : X ⧸ P)
    have := LinearMap.ofIsCompl_apply_left h (φ := LinearMap.id) (ψ := 0) ⟨_, hb⟩
    exact (congrArg Subtype.val this).symm
  have h2 : bar l' ≤ LinearMap.ker (q.baseChange k) := by
    refine Submodule.span_le.2 fun s hs => ?_
    obtain ⟨b, hb, rfl⟩ := hs
    show q.baseChange k (1 ⊗ₜ b) = 0
    rw [LinearMap.baseChange_tmul]
    have := LinearMap.ofIsCompl_apply_right h (φ := LinearMap.id) (ψ := 0) ⟨_, hb⟩
    show (1 : k) ⊗ₜ[ℤ] proj (Submodule.Quotient.mk b) = 0
    rw [this, LinearMap.zero_apply, TensorProduct.tmul_zero]
  have hcompl : IsCompl (bar l) (bar l') := by
    refine ⟨Submodule.disjoint_def.2 fun x hx hx' => hπ ?_, codisjoint_iff.2 htop⟩
    rw [LinearMap.mem_eqLocus.1 (h1 hx), LinearMap.comp_apply, LinearMap.mem_ker.1 (h2 hx'), map_zero, map_zero]

  obtain ⟨a₀, ha₀⟩ := Submodule.Quotient.mk_surjective P (e.symm 1 : X ⧸ P)
  have hmk : ∀ c : O, (Submodule.Quotient.mk (c • a₀) : X ⧸ P) = (e.symm (Ideal.Quotient.mk _ c) : X ⧸ P) := by
    intro c
    have : (Ideal.Quotient.mk (Ideal.span {(p : O)}) c) = c • 1 := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [Submodule.Quotient.mk_smul, ha₀, this, map_smul, Submodule.coe_smul]
  refine ⟨bar l', 1 ⊗ₜ a₀, hcompl, hst l, hst l', le_antisymm ?_ ?_, ?_⟩
  · refine Submodule.span_le.2 fun s hs => ?_
    obtain ⟨b, hb, rfl⟩ := hs
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (e ⟨_, hb⟩)
    have hd : b - c • a₀ ∈ P := by
      rw [← Submodule.Quotient.mk_eq_zero P, Submodule.Quotient.mk_sub, hmk, hc, LinearEquiv.symm_apply_apply, sub_self]
    have e4 : (1 : k) ⊗ₜ[ℤ] b = ρb c (1 ⊗ₜ a₀) + 1 ⊗ₜ (b - c • a₀) := by
      rw [hρ, ← TensorProduct.tmul_add, add_sub_cancel]
    rw [SetLike.mem_coe, e4, hz _ hd, add_zero]
    exact Submodule.subset_span ⟨c, rfl⟩
  · refine Submodule.span_le.2 fun s hs => ?_
    obtain ⟨c, rfl⟩ := hs
    show ρb c (1 ⊗ₜ a₀) ∈ bar l
    rw [hρ]
    exact Submodule.subset_span ⟨c • a₀, by rw [hmk]; exact (e.symm _).2, rfl⟩
  ·
    let fA : O →ₗ[ℤ] X := (LinearMap.toSpanSingleton O X a₀).restrictScalars ℤ
    have hT : ∀ t, tensorAction ρb t (1 ⊗ₜ a₀) = fA.baseChange k t := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul c a =>
        rw [tensorAction_tmul, hρ, LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rfl
      | add s t hs ht => rw [map_add, LinearMap.add_apply, hs, ht, map_add]
    let mO : O →ₗ[ℤ] O ⧸ Ideal.span {(p : O)} := (Submodule.mkQ (Ideal.span {(p : O)})).restrictScalars ℤ
    let es : (O ⧸ Ideal.span {(p : O)}) →ₗ[ℤ] l := (e.symm : (O ⧸ Ideal.span {(p : O)}) →ₗ[O] l).restrictScalars ℤ
    have key : ∀ t, π.baseChange k (fA.baseChange k t) = ls.baseChange k (es.baseChange k (mO.baseChange k t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul c a =>
        simp only [LinearMap.baseChange_tmul]
        congr 1
        exact hmk a
      | add s t hs ht => simp only [map_add, hs, ht]
    have hmO : Function.Injective (mO.baseChange k) := by
      refine baseChange_mkQ_injective k (Ideal.span {(p : O)}) fun x hx c => ?_
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      have e5 : a * (p : O) = p • a := by rw [mul_comm, ← nsmul_eq_mul]
      rw [e5]
      exact tmul_nsmul_eq_zero c a
    have hes : Function.Injective (es.baseChange k) := by
      refine Function.LeftInverse.injective (g := ((e : l →ₗ[O] O ⧸ Ideal.span {(p : O)}).restrictScalars ℤ).baseChange k)
        fun y => ?_
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul c u => simp [es]
      | add s t hs ht => simp only [map_add, hs, ht]
    have hls : Function.Injective (ls.baseChange k) := by
      refine Function.LeftInverse.injective (g := (proj.restrictScalars ℤ).baseChange k) fun y => ?_
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul c u =>
        simp only [LinearMap.baseChange_tmul]
        congr 1
        exact LinearMap.ofIsCompl_apply_left h (φ := LinearMap.id) (ψ := 0) u
      | add s t hs ht => simp only [map_add, hs, ht]
    intro t ht
    rw [hT] at ht
    have h0 : ls.baseChange k (es.baseChange k (mO.baseChange k t)) = 0 := by rw [← key, ht, map_zero]
    exact (injective_iff_map_eq_zero _).1 hmO _ ((injective_iff_map_eq_zero _).1 hes _
      ((injective_iff_map_eq_zero _).1 hls _ h0))

end GlobalTheory.LineSummand

namespace GlobalTheory.LineSummand

theorem sum1_bar_line : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p) (l : ct.Sum1),
  ∃ (M' : Submodule ct.kbar ct.LaBar) (n₀ : ct.LaBar), IsCompl l.bar M' ∧
    (∀ a, ∀ x ∈ l.bar, (baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) a x ∈ l.bar) ∧ (∀ a, ∀ x ∈ M', (baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) a x ∈ M') ∧
    l.bar = Submodule.span ct.kbar (Set.range fun a => (baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) a n₀) ∧
    ∀ t : ct.kbar ⊗[ℤ] 𝓞 D.host.E, tensorAction (baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) t n₀ = 0 → t = 0 := by
  intro D A N j S κ p ct l
  obtain ⟨l', hl'⟩ := l.2.1
  obtain ⟨e⟩ := l.2.2
  exact line_summand ct.kbar _ (fun x hx c => tmul_eq_zero_of_mem_smul_top (p := p) hx c) l.1 l' hl' e

end GlobalTheory.LineSummand
