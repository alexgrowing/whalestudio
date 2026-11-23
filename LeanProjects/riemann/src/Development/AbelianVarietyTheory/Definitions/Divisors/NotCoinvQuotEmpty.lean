import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecMapApply
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConclusionRankZero

noncomputable section

open GlobalTheory.WeilM GlobalTheory.Published.HoweDualityFiniteModel
open scoped Matrix

namespace GlobalTheory.LinPair.Model

section General

variable {k : Type} [Field k] [Invertible (2 : k)] {E : Type} [Field E] [Algebra k E] {c : E →ₐ[k] E}
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
  [TopologicalSpace k] [IsTopologicalRing k] [LocallyCompactSpace k] [TopologicalSpace E] [IsModuleTopology k E]
  {ψ : AddChar k ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d : Darboux (symp c ξ JA JB) κ} {χ : Eˣ →* Circle}
  {Cy : Matrix β ν E} {om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ)} {l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ}

theorem comm {G H Y : Type} [Group G] [Group H] (om : G × H →* Module.End ℂ (Y → ℂ)) (g : G) (h : H) (φ : Y → ℂ) :
    om (1, h) (om (g, 1) φ) = om (g, 1) (om (1, h) φ) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]; simp

theorem locAug_le_ker (h : IsLinPair c ψ ξ JA JB d χ Cy om) (hl : IsYInv c ψ d Cy l) :
    locAug om ≤ LinearMap.ker (secMap om l) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, φ, hφ, rfl⟩
  refine LinearMap.mem_ker.2 (funext fun x => ?_)
  rw [map_sub, Pi.sub_apply, secMap_apply, secMap_apply, comm, h.lin l hl g (om (1, x) φ) (h.split.2.1.pres x φ hφ)]
  simp

theorem locAug_le_SB (h : IsLinPair c ψ ξ JA JB d χ Cy om) : locAug om ≤ SB (κ → k) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, φ, hφ, rfl⟩
  exact (SB _).sub_mem (h.pres g φ hφ) hφ

theorem locAug_ne_SB (h : IsLinPair c ψ ξ JA JB d χ Cy om) (hl : IsYForm c ψ d Cy l) : locAug om ≠ SB (κ → k) := by
  intro e
  obtain ⟨φ, hφ, h0⟩ := hl.2
  have := congrFun (LinearMap.mem_ker.1 (locAug_le_ker h hl.1 (e ▸ hφ))) 1
  rw [secMap_apply, show ((1 : UG c JA), (1 : UG c JB)) = 1 from rfl, map_one] at this
  exact h0 this

theorem sec_left (h : IsLinPair c ψ ξ JA JB d χ Cy om) (hl : IsYInv c ψ d Cy l) {f : UG c JB → ℂ} (hf : f ∈ secSpace om l)
    (p : UG c JB) (t : GL ν E) (hp : ((p : GL β E) : Matrix β β E) * Cy = Cy * (t : Matrix ν ν E)) (x : UG c JB) :
    f (p * x) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((MeasureTheory.distribHaarChar k (Units.map (Algebra.norm k : E →* k) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^
        ((Fintype.card α : ℝ) / 2) : ℝ) : ℂ) * f x := by
  obtain ⟨φ, hφ, rfl⟩ := hf
  have := h.split.2.2 l trivial hl p t hp _ (h.split.2.1.pres x φ hφ)
  rw [secMap_apply, secMap_apply, show ((1 : UG c JA), p * x) = (1, p) * (1, x) by simp, map_mul]
  exact this

theorem sec_right (h : IsLinPair c ψ ξ JA JB d χ Cy om) {f : UG c JB → ℂ} (hf : f ∈ secSpace om l) (y : UG c JB) :
    (fun x => f (x * y)) ∈ secSpace om l := by
  obtain ⟨φ, hφ, rfl⟩ := hf
  refine ⟨om (1, y) φ, h.split.2.1.pres y φ hφ, funext fun x => ?_⟩
  rw [secMap_apply, secMap_apply, show ((1 : UG c JA), x * y) = (1, x) * (1, y) by simp, map_mul]
  rfl

omit [IsTopologicalRing k] [LocallyCompactSpace k] [TopologicalSpace E] [IsModuleTopology k E] [DecidableEq α]
  [DecidableEq β] [DecidableEq ν] in

theorem isYInv_eval_zero (hd : ∀ z : Matrix α ν E, (d.e (z * Cyᵀ)).1 = 0) :
    IsYInv c ψ d Cy (LinearMap.proj (0 : κ → k)) := by
  intro z φ _
  simp [Darboux.rho, schr, hd]

end General

section Abstract

theorem SB_top (Y : Type) [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] : SB Y = ⊤ :=
  eq_top_iff.2 fun _ _ => ⟨IsLocallyConstant.of_discrete _, HasCompactSupport.of_compactSpace _⟩

theorem locAug_one (G H Y : Type) [Group G] [Group H] [TopologicalSpace Y] :
    locAug (1 : G × H →* Module.End ℂ (Y → ℂ)) = ⊥ := by
  refine le_bot_iff.1 (Submodule.span_le.2 ?_)
  rintro _ ⟨g, φ, -, rfl⟩
  simp

theorem coinvQuot_point (G G' H Y Y' : Type) [Group G] [Group G'] [Group H] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] [Nonempty Y] [TopologicalSpace Y'] [Unique Y'] :
    IsCoinvQuot (1 : G × H →* Module.End ℂ (Y → ℂ)) (1 : G' × H →* Module.End ℂ (Y' → ℂ)) := by
  have hf : Module.finrank ℂ (Y' → ℂ) = 1 := by rw [Module.finrank_fintype_fun_eq_card]; simp
  haveI : IsSimpleOrder (Submodule ℂ (Y' → ℂ)) := is_simple_module_of_finrank_eq_one hf
  obtain ⟨y⟩ := ‹Nonempty Y›
  refine ⟨?_, fun N _ _ _ => ?_, (locAug 1).mkQ ∘ₗ LinearMap.funLeft ℂ ℂ (fun _ => y), ?_, ?_, fun h φ _ φ' _ e => e⟩
  · rw [locAug_one, SB_top]; exact bot_ne_top
  · rw [locAug_one, SB_top]; exact eq_bot_or_eq_top N
  · rw [Submodule.map_comp, SB_top, SB_top, Submodule.map_top (LinearMap.funLeft ℂ ℂ _), LinearMap.range_eq_top.2]
    exact fun f => ⟨fun _ => f default, funext fun z => by simp [LinearMap.funLeft, Subsingleton.elim z default]⟩
  · rw [locAug_one]; exact bot_le

theorem not_coinvQuot_two {G Y : Type} [Group G] [TopologicalSpace Y] (om : G × Unit →* Module.End ℂ (Y → ℂ)) :
    ¬ IsCoinvQuot om (1 : Unit × Unit →* Module.End ℂ (Bool → ℂ)) := by
  rintro ⟨-, h, -⟩
  rw [locAug_one, SB_top] at h
  rcases h (LinearMap.ker (LinearMap.proj true)) bot_le le_top (fun _ _ h => h) with e | e
  · have : (Pi.single false 1 : Bool → ℂ) ∈ LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Bool => ℂ) true) := by simp
    rw [e] at this
    simpa using congrFun ((Submodule.mem_bot ℂ).1 this) false
  · have : (1 : Bool → ℂ) ∈ LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Bool => ℂ) true) := e ▸ trivial
    simp at this

theorem not_coinvQuot_empty {G G' H Y' : Type} [Group G] [Group G'] [Group H] [TopologicalSpace Y']
    (om : G × H →* Module.End ℂ (Empty → ℂ)) (om' : G' × H →* Module.End ℂ (Y' → ℂ)) (hle : locAug om' ≤ SB Y') :
    ¬ IsCoinvQuot om om' := by
  rintro ⟨h0, -, p, hp, -⟩
  refine h0 (le_antisymm hle fun φ hφ => ?_)
  obtain ⟨z, -, hz⟩ : (locAug om').mkQ φ ∈ (SB Empty).map p := hp ▸ ⟨φ, hφ, rfl⟩
  rw [Subsingleton.elim z 0, map_zero] at hz
  exact (Submodule.Quotient.mk_eq_zero _).1 hz.symm

theorem not_coinvQuot_sign (om : Unit × ℂˣ →* Module.End ℂ (Unit → ℂ)) (hom : ∀ u φ, om (1, u) φ = (u : ℂ) • φ) :
    ¬ IsCoinvQuot om (1 : Unit × ℂˣ →* Module.End ℂ (Unit → ℂ)) := by
  rintro ⟨-, -, p, hp, -, he⟩
  rw [SB_top] at hp he
  obtain ⟨z, -, hz⟩ : (locAug 1).mkQ (1 : Unit → ℂ) ∈ (⊤ : Submodule ℂ (Unit → ℂ)).map p := hp ▸ ⟨1, trivial, rfl⟩
  have := he (-1) z trivial 1 trivial hz
  rw [hom, map_smul, hz, ← map_smul] at this
  have h2 := (Submodule.Quotient.eq _).1 this
  rw [locAug_one] at h2
  have := congrFun ((Submodule.mem_bot ℂ).1 h2) ()
  simp at this
  norm_num at this

end Abstract

section Witt

variable {k E : Type} [Field k] [Field E] [Algebra k E] (c : E →ₐ[k] E)

theorem wittStep_plane : IsWittStep c 1 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) (1 : Matrix (Fin 0) (Fin 0) E) := by
  refine ⟨rfl, Matrix.of fun i j => Sum.elim (fun x => x.elim0) (Sum.elim (fun _ => if i = 0 then 1 else 0)
    (fun _ => if i = 1 then 1 else 0)) j, ?_⟩
  ext (i | i | i) (j | j | j) <;> first | exact i.elim0 | exact j.elim0 |
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Subsingleton.elim i j]

theorem not_wittStep_aniso {a a' r : ℕ} (hr : 0 < r) (JA : Matrix (Fin a) (Fin a) E) (JA' : Matrix (Fin a') (Fin a') E)
    (h : ∀ x : Fin a → E, x ⬝ᵥ JA *ᵥ (c ∘ x) = 0 → x = 0) : ¬ IsWittStep c r JA JA' := by
  rintro ⟨-, P, hP⟩
  let i : Fin r := ⟨0, hr⟩
  have key : ∀ u v, (fun s => P s u) ⬝ᵥ JA *ᵥ (c ∘ fun s => P s v) = (Pᵀ * JA * P.map c) u v := fun u v => by
    rw [Matrix.mul_assoc]; rfl
  have h1 := h (fun s => P s (.inr (.inl i))) (by rw [key, hP]; simp)
  have h2 := key (.inr (.inl i)) (.inr (.inr i))
  rw [h1, hP] at h2
  simp at h2

end Witt

section RankZero

variable {k : Type} [Field k] [Invertible (2 : k)] {E : Type} [Field E] [Algebra k E] (c : E →ₐ[k] E)

omit [Invertible (2 : k)] in
theorem lagr_plane : IsLagr c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E) (!![1; 0] : Matrix (Fin 2) (Fin 1) E) := by
  refine ⟨?_, !![0; 1], Matrix.fromRows !![1, 0] !![0, 1], ?_, ?_, ?_⟩
  · ext i j; simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fintype.sum_sum_type]
  · ext (i | i) (j | j) <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Subsingleton.elim i j]

variable [TopologicalSpace k] [IsTopologicalRing k] [LocallyCompactSpace k] [TopologicalSpace E] [IsModuleTopology k E]

theorem linPair_one (ψ : AddChar k ℂ) (ξ : E) (JA : Matrix (Fin 0) (Fin 0) E) {β ν : Type} [Fintype β] [DecidableEq β]
    [Fintype ν] [DecidableEq ν] (JB : Matrix β β E) (Cy : Matrix β ν E) (hL : IsLagr c JB Cy)
    (co : Darboux (symp c ξ JA JB) Empty) : IsLinPair c ψ ξ JA JB co 1 Cy 1 := by
  refine ⟨⟨hL, ?_, fun l _ _ p t hp φ _ => by simp⟩, fun _ _ h => h, fun g w φ _ => ?_, fun _ _ _ _ _ => rfl⟩
  · rw [MonoidHom.one_comp]; exact split_one ψ _
  · rw [Subsingleton.elim (_ * w) w]; rfl

def RankZero (ψ : AddChar k ℂ) : Prop :=
  ∃ (JA : Matrix (Fin 0) (Fin 0) E) (JB : Matrix (Fin 2) (Fin 2) E) (Cy : Matrix (Fin 2) (Fin 1) E)
    (co : Darboux (symp c (-1) JA JB) Empty) (om : UG c JA × UG c JB →* Module.End ℂ ((Empty → k) → ℂ))
    (l : ((Empty → k) → ℂ) →ₗ[ℂ] ℂ),
    IsHerm c JA ∧ (∀ i j, c (JB j i) = -JB i j) ∧
    JB.det ≠ 0 ∧ IsLagr c JB Cy ∧ IsLinPair c ψ (-1) JA JB co 1 Cy om ∧ IsUWeilPair c (sbClass k) ψ (-1) JA JB co 1 1 om ∧
    IsYForm c ψ co Cy l ∧ IsCoinvQuot om om

theorem rankZero (ψ : AddChar k ℂ) : RankZero c ψ := by
  refine ⟨1, !![0, 1; -1, 0], !![1; 0], GlobalTheory.WeilM.SiegelModel.darbZero _ _ _ _, 1, LinearMap.proj 0,
    ⟨fun i => i.elim0, by simp⟩, fun i j => by fin_cases i <;> fin_cases j <;> simp, by simp, lagr_plane c,
    linPair_one c ψ _ _ _ _ (lagr_plane c) _,
    ⟨weilB_one ψ _, ⟨GlobalTheory.WeilM.SiegelModel.darbZero _ _ _ _, fun _ => Subsingleton.elim _ _, weilB_one ψ _⟩,
      fun l _ φ _ => continuous_const (y := l φ)⟩,
    ⟨isYInv_eval_zero fun _ => Subsingleton.elim _ _, 1, ?_, ?_⟩, ?_⟩
  · exact ⟨IsLocallyConstant.const 1, HasCompactSupport.of_compactSpace _⟩
  · exact one_ne_zero
  · exact coinvQuot_point _ _ _ _ _

end RankZero

theorem rankZero_sqrt (K : Type) [Field K] [CharZero K] [Invertible (2 : K)] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (e : K) [Fact (∀ r : K, r ^ 2 ≠ e + 0 * r)] :
    ∃ (_ : TopologicalSpace (QuadraticAlgebra K e 0)) (_ : IsModuleTopology K (QuadraticAlgebra K e 0))
      (c : QuadraticAlgebra K e 0 →ₐ[K] QuadraticAlgebra K e 0) (δ : QuadraticAlgebra K e 0) (ψ : AddChar K ℂ),
      IsQuad c δ ∧ Continuous ψ ∧ (∀ t, ‖ψ t‖ = 1) ∧ ψ ≠ 1 ∧ RankZero c ψ := by
  obtain ⟨t, m, c, δ, -, ψ, -, hq, -, h1, h2, h3, -, -⟩ := GlobalTheory.SplitUnitary.Model.isQuad_isHerm_continuous_resEtaPow K e 0
  exact ⟨t, m, c, δ, ψ, hq, h1, h2, h3, rankZero c ψ⟩

end GlobalTheory.LinPair.Model

end
