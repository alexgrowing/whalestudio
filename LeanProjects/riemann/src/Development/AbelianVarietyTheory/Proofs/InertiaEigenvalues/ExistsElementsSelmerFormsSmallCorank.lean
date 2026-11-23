import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlternatingFormLeftCorankLeOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearCoefficientMapCocycles
import Development.AutomorphicArithmetic.CyclotomicBounds.CyclotomicOrders.ExistsCycZPowNeOne

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ChooseForms

section Linear

variable {K : Type} [Field K]

theorem exists_comb {ι : Type} {n n' : ℕ} (M : ι → Fin n → Fin n' → K) (w : Fin n → Fin n' → K)
    (hw : ∀ c : Fin n → Fin n' → K, (∀ t, ∑ a, ∑ b, c a b * M t a b = 0) → ∑ a, ∑ b, c a b * w a b = 0) :
    ∃ (m : ℕ) (j : Fin m → ι) (d : Fin m → K), m ≤ n * n' ∧ ∀ a b, w a b = ∑ k, d k * M (j k) a b := by
  classical
  let M' : ι → Fin n × Fin n' → K := fun t p => M t p.1 p.2
  have key : ∀ (φ : Module.Dual K (Fin n × Fin n' → K)) (v : Fin n × Fin n' → K),
      φ v = ∑ a, ∑ b, φ (fun q => if (a, b) = q then 1 else 0) * v (a, b) := by
    intro φ v
    rw [LinearMap.pi_apply_eq_sum_univ, Fintype.sum_prod_type]
    simp only [smul_eq_mul, mul_comm]
  have hmem : (fun p : Fin n × Fin n' => w p.1 p.2) ∈ Submodule.span K (Set.range M') := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    rw [key]
    refine hw _ fun t => ?_
    have := (Submodule.mem_dualAnnihilator φ).1 hφ (M' t) (Submodule.subset_span ⟨t, rfl⟩)
    rwa [key] at this
  obtain ⟨f, hf, hsp, -⟩ := Submodule.exists_fun_fin_finrank_span_eq K (Set.range M')
  choose j hj using hf
  rw [← hsp, Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨d, hd⟩ := hmem
  refine ⟨_, j, d, ?_, fun a b => ?_⟩
  · refine (Submodule.finrank_le _).trans ?_
    simp
  · have := congrFun hd (a, b)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hj] at this
    exact this.symm

theorem sum_symm_alt {n : ℕ} (c w : Fin n → Fin n → K) (hc : ∀ a b, c a b = c b a) (h0 : ∀ a, w a a = 0)
    (hw : ∀ a b, w a b + w b a = 0) : ∑ a, ∑ b, c a b * w a b = 0 := by
  rw [← Fintype.sum_prod_type' (fun a b => c a b * w a b)]
  refine Finset.sum_involution (fun p _ => p.swap) (fun p _ => ?_) (fun p _ hp he => hp ?_) (fun _ _ => Finset.mem_univ _)
    (fun p _ => rfl)
  · simp only [Prod.fst_swap, Prod.snd_swap]
    rw [hc p.2 p.1, ← mul_add, hw, mul_zero]
  · have : p.2 = p.1 := congrArg Prod.fst he
    rw [this, h0, mul_zero]

end Linear

section Abstract

variable {K : Type} [Field K] [TopologicalSpace K] [DiscreteTopology K] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  [IsTopologicalGroup Γ] {r : ℕ}

def fm (cj : Γ →* Γ) {ρ ρ' : Representation K Γ (Fin r → K)} (x : Z1 ρ) (y : Z1 ρ') (h : Γ) : K :=
  x.1 h ⬝ᵥ y.1 h - x.1 (cj h) ⬝ᵥ y.1 (cj h)

variable {ρ : Representation K Γ (Fin r → K)}

omit [IsTopologicalGroup Γ] in
theorem val_one (x : Z1 ρ) : x.1 1 = 0 := by
  have := x.2.2 1 1
  simpa using this

omit [IsTopologicalGroup Γ] in
theorem val_conj (x : Z1 ρ) {h : Γ} (hh : ρ h = 1) (g : Γ) : x.1 (g * h * g⁻¹) = ρ g (x.1 h) := by
  have e := x.2.2 g g⁻¹
  rw [mul_inv_cancel, val_one] at e
  rw [x.2.2, x.2.2, map_mul, hh, mul_one, add_right_comm, ← e, zero_add]

omit [IsTopologicalGroup Γ] in
theorem val_eq {x x' : Z1 ρ} (e : (Submodule.Quotient.mk x : H1 ρ) = Submodule.Quotient.mk x') {h : Γ} (hh : ρ h = 1) :
    x.1 h = x'.1 h := by
  have e' : x - x' ∈ (B1 ρ).comap (Z1 ρ).subtype := (Submodule.Quotient.eq _).1 e
  obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ _).1 e'
  have := hm h
  rw [hh] at this
  simpa [sub_eq_zero] using this

omit [IsTopologicalGroup Γ] in
theorem val_comb {n : ℕ} {x : Fin n → Z1 ρ} {x₀ : Z1 ρ} {α : Fin n → K}
    (e : (Submodule.Quotient.mk x₀ : H1 ρ) = ∑ a, α a • (Submodule.Quotient.mk (x a) : H1 ρ)) {h : Γ} (hh : ρ h = 1) :
    x₀.1 h = ∑ a, α a • (x a).1 h := by
  have e' : (Submodule.Quotient.mk x₀ : H1 ρ) = Submodule.Quotient.mk (∑ a, α a • x a) := by
    rw [e, ← Submodule.mkQ_apply, map_sum]
    simp
  rw [val_eq e' hh]
  simp

def kerOn (L : Subgroup Γ) (hL : ∀ g ∈ L, ρ g = 1) (x : Z1 ρ) : Subgroup Γ where
  carrier := {u | u ∈ L ∧ x.1 u = 0}
  one_mem' := ⟨L.one_mem, val_one x⟩
  mul_mem' := fun {a b} ha hb => ⟨L.mul_mem ha.1 hb.1, by rw [x.2.2, ha.2, hb.2, map_zero, add_zero]⟩
  inv_mem' := fun {a} ha => ⟨L.inv_mem ha.1, by
    have e := x.2.2 a a⁻¹
    rw [mul_inv_cancel, val_one, ha.2, hL a ha.1, zero_add] at e
    exact e.symm⟩

omit [IsTopologicalGroup Γ] in
theorem kerOn_open {L : Subgroup Γ} (hL : ∀ g ∈ L, ρ g = 1) (ho : IsOpen (L : Set Γ)) (x : Z1 ρ) :
    IsOpen (kerOn L hL x : Set Γ) :=
  ho.inter ((isOpen_discrete {0}).preimage x.2.1)

omit [IsTopologicalGroup Γ] in
theorem kerOn_normal {L : Subgroup Γ} (hL : ∀ g ∈ L, ρ g = 1) (hn : L.Normal) (x : Z1 ρ) : (kerOn L hL x).Normal :=
  ⟨fun u hu g => ⟨hn.conj_mem u hu.1 g, by rw [val_conj x (hL u hu.1), hu.2, map_zero]⟩⟩

omit [IsTopologicalGroup Γ] in
theorem val_of_mem {L : Subgroup Γ} (hL : ∀ g ∈ L, ρ g = 1) (x : Z1 ρ) {g φ h : Γ} (hφ : φ ∈ L)
    (hu : g * φ * g⁻¹ * h⁻¹ ∈ kerOn L hL x) : x.1 h = ρ g (x.1 φ) := by
  have e := x.2.2 (g * φ * g⁻¹ * h⁻¹) h
  rw [inv_mul_cancel_right, val_conj x (hL φ hφ), hu.2, hL _ hu.1, zero_add] at e
  exact e.symm

variable {ρ' : Representation K Γ (Fin r → K)} (cj : Γ →* Γ) (hcj : Continuous cj) (ε : Γ → K)
  (hε : ∀ g v w, ρ g v ⬝ᵥ ρ' g w = ε g * (v ⬝ᵥ w)) (hεc : ∀ g, ε (cj g) = ε g)
  (L : Subgroup Γ) (ho : IsOpen (L : Set Γ)) (hn : L.Normal) (hc : ∀ g ∈ L, cj g ∈ L)
  (hL : ∀ g ∈ L, ρ g = 1) (hL' : ∀ g ∈ L, ρ' g = 1)

omit [IsTopologicalGroup Γ] in
include hcj hε hεc ho hn hc hL hL' in
theorem core {n n' : ℕ} (x : Fin n → Z1 ρ) (y : Fin n' → Z1 ρ') (w : Fin n → Fin n' → K)
    (hw : ∀ c : Fin n → Fin n' → K, (∀ h ∈ L, ∑ a, ∑ b, c a b * fm cj (x a) (y b) h = 0) → ∑ a, ∑ b, c a b * w a b = 0) :
    ∃ (h : Fin (n * n') → Γ) (U : Subgroup Γ), (∀ a, h a ∈ L) ∧ IsOpen (U : Set Γ) ∧ U.Normal ∧
      ∀ (R : ℕ) (φ : Fin R → Γ), (∀ a, ∃ b g, g * φ b * g⁻¹ * (h a)⁻¹ ∈ U) →
        ∃ c : Fin R → K, ∀ (x₀ : Z1 ρ) (y₀ : Z1 ρ') (α : Fin n → K) (β : Fin n' → K),
          (Submodule.Quotient.mk x₀ : H1 ρ) = ∑ a, α a • (Submodule.Quotient.mk (x a) : H1 ρ) →
          (Submodule.Quotient.mk y₀ : H1 ρ') = ∑ a, β a • (Submodule.Quotient.mk (y a) : H1 ρ') →
          ∑ b, c b * fm cj x₀ y₀ (φ b) = ∑ a, ∑ b, α a * β b * w a b := by
  classical
  obtain ⟨m, j, d, hm, hd⟩ := exists_comb (fun (t : L) a b => fm cj (x a) (y b) t) w
    fun c hc => hw c fun h hh => hc ⟨h, hh⟩
  refine ⟨fun k => if hk : k.1 < m then (j ⟨k.1, hk⟩ : Γ) else 1,
    L ⊓ ((⨅ a, kerOn L hL (x a) ⊓ (kerOn L hL (x a)).comap cj) ⊓
      ⨅ a, kerOn L hL' (y a) ⊓ (kerOn L hL' (y a)).comap cj), fun k => ?_, ?_, ?_, fun R φ hφ => ?_⟩
  · dsimp only
    split_ifs
    · exact (j _).2
    · exact L.one_mem
  · simp only [Subgroup.coe_inf, Subgroup.coe_iInf, Subgroup.coe_comap]
    exact ho.inter ((isOpen_iInter_of_finite fun a => (kerOn_open hL ho _).inter ((kerOn_open hL ho _).preimage hcj)).inter
      (isOpen_iInter_of_finite fun a => (kerOn_open hL' ho _).inter ((kerOn_open hL' ho _).preimage hcj)))
  · refine ⟨fun u hu g => ?_⟩
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf] at hu ⊢
    exact ⟨hn.conj_mem u hu.1 g,
      fun a => ⟨(kerOn_normal hL hn _).conj_mem u (hu.2.1 a).1 g, ((kerOn_normal hL hn _).comap cj).conj_mem u (hu.2.1 a).2 g⟩,
      fun a => ⟨(kerOn_normal hL' hn _).conj_mem u (hu.2.2 a).1 g, ((kerOn_normal hL' hn _).comap cj).conj_mem u (hu.2.2 a).2 g⟩⟩
  · choose bb g hg using fun k : Fin m => hφ (Fin.castLE hm k)
    simp only [Fin.val_castLE, Fin.is_lt, dite_true, Fin.eta, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap,
      map_mul, map_inv] at hg
    have hφL : ∀ k, φ (bb k) ∈ L := fun k => by
      have h1 := L.mul_mem (hg k).1 (j k).2
      rw [inv_mul_cancel_right] at h1
      simpa [mul_assoc] using hn.conj_mem _ h1 (g k)⁻¹
    have hfm : ∀ k a b, fm cj (x a) (y b) (j k) = ε (g k) * fm cj (x a) (y b) (φ (bb k)) := fun k a b => by
      unfold fm
      rw [val_of_mem hL (x a) (hφL k) ((hg k).2.1 a).1, val_of_mem hL (x a) (hc _ (hφL k)) ((hg k).2.1 a).2,
        val_of_mem hL' (y b) (hφL k) ((hg k).2.2 b).1, val_of_mem hL' (y b) (hc _ (hφL k)) ((hg k).2.2 b).2,
        hε, hε, hεc, mul_sub]
    refine ⟨fun b => ∑ k with bb k = b, d k * ε (g k), fun x₀ y₀ α β hx hy => ?_⟩
    have h1 : ∑ b, (∑ k with bb k = b, d k * ε (g k)) * fm cj x₀ y₀ (φ b) =
        ∑ k, d k * ε (g k) * fm cj x₀ y₀ (φ (bb k)) := by
      rw [← Finset.sum_fiberwise Finset.univ bb]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [(Finset.mem_filter.1 hk).2]
    have h2 : ∀ h ∈ L, fm cj x₀ y₀ h = ∑ a, ∑ b, α a * β b * fm cj (x a) (y b) h := fun h hh => by
      unfold fm
      rw [val_comb hx (hL _ hh), val_comb hx (hL _ (hc _ hh)), val_comb hy (hL' _ hh), val_comb hy (hL' _ (hc _ hh))]
      simp only [sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [h1]
    simp only [h2 _ (hφL _), hd, hfm, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring

def Body (cj : Γ →* Γ) (S : Submodule K (H1 ρ)) (S' : Submodule K (H1 ρ')) {R : ℕ} (φ : Fin R → Γ) (e : ℕ) : Prop :=
  ∃ c : Fin R → K, ∀ x : Fin (e + 1) → Z1 ρ, (∀ a, (Submodule.Quotient.mk (x a) : H1 ρ) ∈ S) →
    (∀ a (y : Z1 ρ'), (Submodule.Quotient.mk y : H1 ρ') ∈ S' → ∑ b, c b * fm cj (x a) y (φ b) = 0) →
    ¬ LinearIndependent K (fun a => (Submodule.Quotient.mk (x a) : H1 ρ))

omit [IsTopologicalGroup Γ] in

theorem Body.succ {cj : Γ →* Γ} {S : Submodule K (H1 ρ)} {S' : Submodule K (H1 ρ')} {R : ℕ} {φ : Fin R → Γ} {e : ℕ}
    (h : Body cj S S' φ e) : Body cj S S' φ (e + 1) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun x hx h0 hi => hc (fun a => x a.castSucc) (fun a => hx _) (fun a => h0 _)
    (hi.comp Fin.castSucc (Fin.castSucc_injective _))⟩

omit [IsTopologicalGroup Γ] in
theorem exists_lift (S : Submodule K (H1 ρ)) {n : ℕ} (b : Module.Basis (Fin n) K S) :
    ∃ x : Fin n → Z1 ρ, (∀ a, (Submodule.Quotient.mk (x a) : H1 ρ) = (b a : H1 ρ)) ∧
      LinearIndependent K (fun a => (Submodule.Quotient.mk (x a) : H1 ρ)) ∧
      ∀ t : S, (t : H1 ρ) = ∑ a, b.repr t a • (Submodule.Quotient.mk (x a) : H1 ρ) := by
  choose x hx using fun a => Submodule.Quotient.mk_surjective _ (b a : H1 ρ)
  refine ⟨x, hx, ?_, fun t => ?_⟩
  · simp only [hx]
    exact b.linearIndependent.map' S.subtype S.ker_subtype
  · simp only [hx]
    have := congrArg S.subtype (b.sum_repr t)
    rw [map_sum] at this
    simp only [map_smul, Submodule.subtype_apply] at this
    exact this.symm

omit [IsTopologicalGroup Γ] in
include hcj hε hεc ho hn hc hL hL' in
theorem abs_odd (S : Submodule K (H1 ρ)) (S' : Submodule K (H1 ρ')) [Module.Finite K S] [Module.Finite K S']
    (hd : Module.finrank K S = Module.finrank K S')
    (hsp : ∀ (n n' : ℕ) (x : Fin n → Z1 ρ) (y : Fin n' → Z1 ρ'),
      LinearIndependent K (fun a => (Submodule.Quotient.mk (x a) : H1 ρ)) →
      LinearIndependent K (fun a => (Submodule.Quotient.mk (y a) : H1 ρ')) → ∀ c : Fin n → Fin n' → K,
      (∀ h ∈ L, ∑ a, ∑ b, c a b * fm cj (x a) (y b) h = 0) → c = 0) :
    ∃ (h : Fin (Module.finrank K S * Module.finrank K S) → Γ) (U : Subgroup Γ), (∀ a, h a ∈ L) ∧ IsOpen (U : Set Γ) ∧
      U.Normal ∧ ∀ (R : ℕ) (φ : Fin R → Γ), (∀ a, ∃ b g, g * φ b * g⁻¹ * (h a)⁻¹ ∈ U) → Body cj S S' φ 0 := by
  classical
  obtain ⟨x, -, hxl, hxs⟩ := exists_lift S (Module.finBasis K S)
  obtain ⟨y, hy, hyl, -⟩ := exists_lift S' (Module.finBasisOfFinrankEq K S' hd.symm)
  obtain ⟨h, U, h1, h2, h3, h4⟩ := core cj hcj ε hε hεc L ho hn hc hL hL' x y (fun a b => if a = b then 1 else 0)
    fun c hc => by simp [hsp _ _ x y hxl hyl c hc]
  refine ⟨h, U, h1, h2, h3, fun R φ hφ => ?_⟩
  obtain ⟨c, hc⟩ := h4 R φ hφ
  refine ⟨c, fun x₀ hx₀ h0 hli => hli.ne_zero 0 ?_⟩
  have e := hxs ⟨_, hx₀ 0⟩
  have hz : ∀ b, (Module.finBasis K S).repr ⟨_, hx₀ 0⟩ b = 0 := fun b => by
    have := hc (x₀ 0) (y b) _ (fun a => if a = b then 1 else 0) e (by simp)
    rw [h0 0 (y b) (by rw [hy]; exact Subtype.property _)] at this
    simpa using this.symm
  simpa [hz] using e

def twZ (A : (Fin r → K) →ₗ[K] (Fin r → K)) (hA : ∀ g m, A (ρ (cj g) m) = ρ' g (A m)) : Z1 ρ →ₗ[K] Z1 ρ' :=
  (cocycles1MapOfEquivariant (ρ.comp cj) ρ' A continuous_of_discreteTopology hA).comp (restrictCocycles1 ρ cj hcj)

def twH (A : (Fin r → K) →ₗ[K] (Fin r → K)) (hA : ∀ g m, A (ρ (cj g) m) = ρ' g (A m)) : H1 ρ →ₗ[K] H1 ρ' :=
  (mapH1 (ρ.comp cj) ρ' A continuous_of_discreteTopology hA).comp (resH1 ρ cj hcj)

omit [IsTopologicalGroup Γ] in
theorem twH_twH (hcc : ∀ g, cj (cj g) = g) (A A' : (Fin r → K) →ₗ[K] (Fin r → K))
    (hA : ∀ g m, A (ρ (cj g) m) = ρ' g (A m)) (hA' : ∀ g m, A' (ρ' (cj g) m) = ρ g (A' m)) (hAA : ∀ m, A' (A m) = m)
    (ξ : H1 ρ) : twH cj hcj A' hA' (twH cj hcj A hA ξ) = ξ := by
  induction ξ using Submodule.Quotient.induction_on with
  | H z =>
    change (Submodule.Quotient.mk (twZ cj hcj A' hA' (twZ cj hcj A hA z)) : H1 ρ) = _
    congr 1
    refine Subtype.ext (funext fun g => ?_)
    change A' (A (z.1 (cj (cj g)))) = _
    rw [hAA, hcc]

omit [IsTopologicalGroup Γ] in
include hcj hε hεc in
theorem abs_two (hcc : ∀ g, cj (cj g) = g) (A : (Fin r → K) ≃ₗ[K] (Fin r → K))
    (hA : ∀ g m, A (ρ (cj g) m) = ρ' g (A m))
    (S : Submodule K (H1 ρ)) (S' : Submodule K (H1 ρ')) [Module.Finite K S] [Module.Finite K S']
    (hd : Module.finrank K S = Module.finrank K S') :
    ∃ R₀ : ℕ, ∀ L : Subgroup Γ, IsOpen (L : Set Γ) → L.Normal → (∀ g ∈ L, cj g ∈ L) → (∀ g ∈ L, ρ g = 1) →
      (∀ g ∈ L, ρ' g = 1) →
      (∀ (n : ℕ) (x : Fin n → Z1 ρ) (y : Fin n → Z1 ρ'),
        LinearIndependent K (fun a => (Submodule.Quotient.mk (x a) : H1 ρ)) →
        (∀ a g, (y a).1 (cj g) = A ((x a).1 g)) → ∀ c : Fin n → Fin n → K,
        (∀ h ∈ L, ∑ a, ∑ b, c a b * fm cj (x a) (y b) h = 0) → ∀ a b, c a b = c b a) →
      ∃ (h : Fin R₀ → Γ) (U : Subgroup Γ), (∀ a, h a ∈ L) ∧ IsOpen (U : Set Γ) ∧
        U.Normal ∧ ∀ (R : ℕ) (φ : Fin R → Γ), (∀ a, ∃ b g, g * φ b * g⁻¹ * (h a)⁻¹ ∈ U) → Body cj S S' φ 1 := by
  classical
  have hA' : ∀ g m, A.symm.toLinearMap (ρ' (cj g) m) = ρ g (A.symm.toLinearMap m) := fun g m => by
    apply A.injective
    have := hA (cj g) (A.symm m)
    rw [hcc] at this
    simp [this]
  let C : H1 ρ' ≃ₗ[K] H1 ρ := LinearEquiv.ofLinear (twH cj hcj A.symm.toLinearMap hA') (twH cj hcj A.toLinearMap hA)
    (LinearMap.ext fun ξ => twH_twH cj hcj hcc _ _ hA hA' A.symm_apply_apply ξ)
    (LinearMap.ext fun ξ => twH_twH cj hcj hcc _ _ hA' hA A.apply_symm_apply ξ)
  let S₂ : Submodule K (H1 ρ) := S'.map C.toLinearMap
  let T : Submodule K (H1 ρ) := S ⊔ S₂
  refine ⟨Module.finrank K T * Module.finrank K T, fun L ho hn hc hL hL' hsp => ?_⟩
  obtain ⟨ω, hω0, hω⟩ := GlobalTheory.T.exists_alternating_form_left_corank_le_one K T (S.comap T.subtype) (S₂.comap T.subtype) (by
    rw [(Submodule.comapSubtypeEquivOfLe (le_sup_left : S ≤ T)).finrank_eq,
      (Submodule.comapSubtypeEquivOfLe (le_sup_right : S₂ ≤ T)).finrank_eq, hd]
    exact (LinearEquiv.finrank_map_eq C S').symm)
  let bT := Module.finBasis K T
  obtain ⟨x, -, hxl, hxs⟩ := exists_lift T bT
  obtain ⟨h, U, h1, h2, h3, h4⟩ := core cj hcj ε hε hεc L ho hn hc hL hL' x
    (fun a => twZ cj hcj A.toLinearMap hA (x a)) (fun a b => ω (bT a) (bT b))
    fun c hc => sum_symm_alt c _ (hsp _ x _ hxl (fun a g => by
        change A ((x a).1 (cj (cj g))) = _
        rw [hcc]) c hc) (fun a => hω0 _) fun a b => by
      have := hω0 (bT a + bT b)
      simp only [map_add, LinearMap.add_apply, hω0, zero_add, add_zero] at this
      rw [add_comm]; exact this
  refine ⟨h, U, h1, h2, h3, fun R φ hφ => ?_⟩
  obtain ⟨c, hc⟩ := h4 R φ hφ
  refine ⟨c, fun x₀ hx₀ h0 hli => ?_⟩
  let t : Fin 2 → T := fun a => ⟨_, (le_sup_left : S ≤ T) (hx₀ a)⟩
  refine hω t hx₀ (fun a t' ht' => ?_) (LinearIndependent.of_comp T.subtype hli)
  obtain ⟨η, hη, hηt⟩ := ht'
  obtain ⟨y₀, rfl⟩ := Submodule.Quotient.mk_surjective _ η
  have e : (Submodule.Quotient.mk y₀ : H1 ρ') = ∑ b, bT.repr t' b •
      (Submodule.Quotient.mk (twZ cj hcj A.toLinearMap hA (x b)) : H1 ρ') := by
    have e1 : (Submodule.Quotient.mk y₀ : H1 ρ') = C.symm (t' : H1 ρ) := by
      rw [LinearEquiv.eq_symm_apply]; exact hηt
    rw [e1, hxs t', map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul]
    rfl
  have := hc (x₀ a) y₀ _ _ (hxs (t a)) e
  rw [h0 a y₀ hη] at this
  rw [← bT.sum_repr (t a), ← bT.sum_repr t']
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [this, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end Abstract

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)

open GlobalTheory.TwistDet

theorem isCj_iff {g g' : GE N} : IsCj X g g' ↔ g' = cConj X g :=
  ⟨fun h => AlgEquiv.ext h, fun h => h ▸ cConj_apply X g⟩

theorem continuous_cj : Continuous (cConj X) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff D.host.E N.Om U).1 hU
  have h := isOpen_comap_cConj X (IntermediateField.fixingSubgroup_isOpen L)
  exact Filter.mem_map.2 (Filter.mem_of_superset (h.mem_nhds (Subgroup.one_mem _)) fun g hg => hLU hg)

theorem eps_cj (g : GE N) : eps0 X i (cConj X g) = eps0 X i g := by
  have e : MulSemiringAction.toRingAut (GE N) N.Om (cConj X g) =
      (X.cc : RingAut N.Om) * MulSemiringAction.toRingAut (GE N) N.Om g * (X.cc : RingAut N.Om)⁻¹ := by
    ext x; exact cConj_apply X g x
  have : cycZ D.host.E N.Om (X.l i) (cConj X g) = cycZ D.host.E N.Om (X.l i) g := by
    simp only [cycZ, MonoidHom.comp_apply]
    rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  simp only [eps0, MonoidHom.comp_apply, this]

theorem transpose_mul_dual (g : GE N) :
    (Tmat i s g).transpose * Tdual i s g = ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix _ _ (X.O0 i)) := by
  rw [Tdual, Matrix.mul_smul, ← Matrix.transpose_mul, ← Tgl_coe, ← Matrix.coe_units_inv, Units.inv_mul,
    Matrix.transpose_one]

section Field

variable (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]

omit [TopologicalSpace K] [DiscreteTopology K] in
theorem red_apply (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (g : GE N) (v : Fin D.R.r → K) :
    red i K ρ g v = ((ρ g : Matrix _ _ (X.O0 i)).map (algebraMap (X.O0 i) K)).mulVec v := by
  funext a
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

omit [TopologicalSpace K] [DiscreteTopology K] in
theorem map_transpose_mul_dual (g : GE N) :
    ((Tmat i s g).map (algebraMap (X.O0 i) K)).transpose * (Tdual i s g).map (algebraMap (X.O0 i) K) =
      algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix _ _ K) := by
  rw [← Matrix.transpose_map, ← Matrix.map_mul, transpose_mul_dual]
  ext a b
  by_cases h : a = b <;> simp [Matrix.one_apply, h]

omit [TopologicalSpace K] [DiscreteTopology K] in
theorem pairing {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hρ : IsDual i s ρ) (g : GE N) (v w : Fin D.R.r → K) :
    red i K (Tgl i s) g v ⬝ᵥ red i K ρ g w = algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) * (v ⬝ᵥ w) := by
  rw [red_apply, red_apply, Tgl_coe, hρ, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    map_transpose_mul_dual, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

omit [TopologicalSpace K] [DiscreteTopology K] in
theorem res_congr (hK : IsRes i K) {a b : X.O0 i}
    (h : IsLocalRing.residue (X.O0 i) a = IsLocalRing.residue (X.O0 i) b) :
    algebraMap (X.O0 i) K a = algebraMap (X.O0 i) K b := by
  rw [← sub_eq_zero, ← map_sub] at h ⊢
  exact hK _ ((IsLocalRing.residue_eq_zero_iff _).1 h)

omit [TopologicalSpace K] [DiscreteTopology K] in
theorem resTriv_red (hK : IsRes i K) {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hρ : IsDual i s ρ) {g : GE N}
    (hg : ResTriv i s g) : red i K (Tgl i s) g = 1 ∧ red i K ρ g = 1 := by
  have h1 : (Tmat i s g).map (algebraMap (X.O0 i) K) = 1 := by
    ext a b
    have := congrFun (congrFun hg.1 a) b
    rw [Matrix.map_apply, res_congr i K hK (b := (1 : Matrix _ _ (X.O0 i)) a b)]
    · by_cases h : a = b <;> simp [Matrix.one_apply, h]
    · rw [Matrix.map_apply] at this
      rw [this]
      by_cases h : a = b <;> simp [Matrix.one_apply, h]
  have h2 := map_transpose_mul_dual i s K g
  rw [h1, Matrix.transpose_one, one_mul, res_congr i K hK (b := 1) (by rw [hg.2, map_one]), map_one, one_smul] at h2
  constructor
  · refine LinearMap.ext fun v => ?_
    rw [red_apply, Tgl_coe, h1, Matrix.one_mulVec]; rfl
  · refine LinearMap.ext fun v => ?_
    rw [red_apply, hρ, h2, Matrix.one_mulVec]; rfl

omit [TopologicalSpace K] [DiscreteTopology K] in

theorem nu_pos_of_resIso (hsd : SelfDual i s) (h : ResIso i s K) : 0 < nu X i := by
  obtain ⟨A₀, hA₀⟩ := hsd
  obtain ⟨A, hu, hA⟩ := h
  refine UpperTheory.KStar.nu_pos_of_res X i K fun g => ?_
  have hc : IsCj X g (cConj X g) := isCj_iff.2 rfl
  have hT : IsUnit (Tmat i s g).det := by
    rw [← Tgl_coe, ← Matrix.isUnit_iff_isUnit_det]
    exact Units.isUnit _
  have e0 : (Tdual i s (cConj X g)).det =
      ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ (D.R.t * D.R.r) * (Tmat i s g).det := by
    rw [hA₀ g _ hc, Matrix.det_mul_comm, ← mul_assoc, Units.inv_mul, one_mul, Matrix.det_smul, Fintype.card_fin, ← pow_mul]
  have e1 := congrArg Matrix.det (hA g _ hc)
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm A.det,
    mul_left_inj' ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero,
    ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det, e0, map_mul, map_pow] at e1
  exact (mul_eq_right₀ (hT.map (algebraMap (X.O0 i) K)).ne_zero).1 e1

theorem single_field (hK : IsRes i K) {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hρ : IsDual i s ρ) (hsd : SelfDual i s)
    (h1 : SpanOdd i s) (h2 : SpanTwo i s) (h3 : EqDim bkP i s) :
    ∃ R₀ : ℕ, ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ L, Small i s L z → ∃ (h : Fin R₀ → GE N) (U : Subgroup (GE N)), (∀ a, h a ∈ L) ∧
      IsOpen (U : Set (GE N)) ∧ U.Normal ∧ ∀ (R : ℕ) (φ : Fin R → GE N), (∀ a, ∃ b g, g * φ b * g⁻¹ * (h a)⁻¹ ∈ U) →
        Body (cConj X) (selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅) (selOn bkP i ρ (1 : GE N →* Kˣ) K ∅) φ
          (if nu X i = 0 then 0 else 1) := by
  obtain ⟨f1, f2, hd⟩ := h3 K hK ρ hρ
  have hεc : ∀ g, algebraMap (X.O0 i) K ((eps0 X i (cConj X g) : (X.O0 i)ˣ) : X.O0 i) =
      algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) := fun g => by rw [eps_cj]
  by_cases hl : ResIso i s K
  · rw [if_neg (nu_pos_of_resIso i s K hsd hl).ne']
    obtain ⟨A₁, hu, hA⟩ := hl
    obtain ⟨A, rfl⟩ := hu
    obtain ⟨R₀, hR⟩ := abs_two (ρ := red i K (Tgl i s)) (ρ' := red i K ρ) (cConj X) continuous_cj _ (pairing i s K hρ) hεc
      (cConj_cConj X) (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv (fun g m => by
        change (A : Matrix (Fin D.R.r) (Fin D.R.r) K).mulVec _ = red i K ρ g ((A : Matrix (Fin D.R.r) (Fin D.R.r) K).mulVec m)
        rw [red_apply, red_apply, Tgl_coe, hρ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          hA (cConj X g) g (isCj_iff.2 (cConj_cConj X g).symm)]) _ _ hd
    refine ⟨R₀, fun z hz L hL => hR L hL.1 hL.2.1 (fun g hg => (hL.2.2.1 g _ (isCj_iff.2 rfl)).1 hg)
      (fun g hg => (resTriv_red i s K hK hρ (hL.2.2.2.2 g hg)).1) (fun g hg => (resTriv_red i s K hK hρ (hL.2.2.2.2 g hg)).2)
      fun n x y hx hy c hc => h2 K hK ρ hρ z hz L hL (A : Matrix (Fin D.R.r) (Fin D.R.r) K) A.isUnit hA n x y hx (fun a g g' hg => ?_) c fun h hh h' hh' => ?_⟩
    · rw [isCj_iff.1 hg]; exact hy a g
    · rw [isCj_iff.1 hh']; exact hc h hh
  · suffices H : ∃ R₀ : ℕ, ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ L, Small i s L z → ∃ (h : Fin R₀ → GE N) (U : Subgroup (GE N)),
        (∀ a, h a ∈ L) ∧ IsOpen (U : Set (GE N)) ∧ U.Normal ∧ ∀ (R : ℕ) (φ : Fin R → GE N),
        (∀ a, ∃ b g, g * φ b * g⁻¹ * (h a)⁻¹ ∈ U) →
        Body (cConj X) (selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅) (selOn bkP i ρ (1 : GE N →* Kˣ) K ∅) φ 0 by
      obtain ⟨R₀, H⟩ := H
      refine ⟨R₀, fun z hz L hL => ?_⟩
      obtain ⟨h, U, a1, a2, a3, a4⟩ := H z hz L hL
      refine ⟨h, U, a1, a2, a3, fun R φ hφ => ?_⟩
      split_ifs
      · exact a4 R φ hφ
      · exact (a4 R φ hφ).succ
    refine ⟨_, fun z hz L hL => abs_odd (ρ := red i K (Tgl i s)) (ρ' := red i K ρ) (cConj X) continuous_cj _
      (pairing i s K hρ) hεc L hL.1 hL.2.1 (fun g hg => (hL.2.2.1 g _ (isCj_iff.2 rfl)).1 hg)
      (fun g hg => (resTriv_red i s K hK hρ (hL.2.2.2.2 g hg)).1) (fun g hg => (resTriv_red i s K hK hρ (hL.2.2.2.2 g hg)).2)
      _ _ hd fun n n' x y hx hy c hc => h1 K hK hl ρ hρ z hz L hL n n' x y hx hy c fun h hh h' hh' => ?_⟩
    rw [isCj_iff.1 hh']; exact hc h hh

end Field

section Transfer

variable {i} {K K' : Type} [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]
  [Field K'] [Algebra (X.O0 i) K'] [TopologicalSpace K'] [DiscreteTopology K']

omit [TopologicalSpace K] [DiscreteTopology K] [TopologicalSpace K'] [DiscreteTopology K'] in
theorem red_map (f : K →ₐ[X.O0 i] K') (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (g : GE N) (v : Fin D.R.r → K) (a : Fin D.R.r) :
    f (red i K ρ g v a) = red i K' ρ g (fun b => f (v b)) a := by
  simp [repOn, matAct, map_sum]

def mapC (f : K →ₐ[X.O0 i] K') {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (x : Z1 (red i K ρ)) : Z1 (red i K' ρ) :=
  ⟨fun g a => f (x.1 g a),
    (continuous_of_discreteTopology (f := fun (v : Fin D.R.r → K) a => f (v a))).comp x.2.1, fun g h => funext fun a => by
      dsimp only
      rw [x.2.2, Pi.add_apply, map_add, red_map]; rfl⟩

theorem fm_mapC (f : K →ₐ[X.O0 i] K') {ρ ρ' : GE N →* GL (Fin D.R.r) (X.O0 i)} (x : Z1 (red i K ρ)) (y : Z1 (red i K ρ'))
    (h : GE N) : fm (cConj X) (mapC f x) (mapC f y) h = f (fm (cConj X) x y h) := by
  simp [fm, mapC, dotProduct, map_sum]

theorem mapC_mapC (e : K ≃ₐ[X.O0 i] K') {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (x : Z1 (red i K' ρ)) :
    mapC (e : K →ₐ[X.O0 i] K') (mapC (e.symm : K' →ₐ[X.O0 i] K) x) = x :=
  Subtype.ext (funext fun g => funext fun a => e.apply_symm_apply _)

theorem not_indep_mapC (f : K →ₐ[X.O0 i] K') {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} {n : ℕ} (x : Fin n → Z1 (red i K ρ))
    (h : ¬ LinearIndependent K fun a => cl (x a)) : ¬ LinearIndependent K' fun a => cl (mapC f (x a)) := by
  rw [Fintype.not_linearIndependent_iff] at h ⊢
  obtain ⟨c, hc, a₀, ha₀⟩ := h
  refine ⟨fun a => f (c a), ?_, a₀, (map_ne_zero f).2 ha₀⟩
  have e : (Submodule.mkQ _ (∑ a, c a • x a) : H1 (red i K ρ)) = 0 := by
    rw [map_sum]; exact hc
  have e1 : ∑ a, c a • x a ∈ (B1 (red i K ρ)).comap (Z1 (red i K ρ)).subtype := (Submodule.Quotient.mk_eq_zero _).1 e
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 e1
  have e2 : ∑ a, f (c a) • mapC f (x a) ∈ (B1 (red i K' ρ)).comap (Z1 (red i K' ρ)).subtype := by
    refine (mem_coboundaries1 _ _).2 ⟨fun b => f (m b), fun g => funext fun b => ?_⟩
    have := congrArg f (congrFun (hm g) b)
    rw [Pi.sub_apply, map_sub, red_map] at this
    rw [Pi.sub_apply, ← this]
    simp [mapC, map_sum]
  have e3 : (Submodule.mkQ _ (∑ a, f (c a) • mapC f (x a)) : H1 (red i K' ρ)) = 0 := (Submodule.Quotient.mk_eq_zero _).2 e2
  rw [map_sum] at e3
  exact e3

theorem body_transfer (e : K ≃ₐ[X.O0 i] K') {ρ ρ' : GE N →* GL (Fin D.R.r) (X.O0 i)} {R n : ℕ} {φ : Fin R → GE N}
    (h : Body (cConj X) (selOn bkP i ρ (1 : GE N →* Kˣ) K ∅) (selOn bkP i ρ' (1 : GE N →* Kˣ) K ∅) φ n) :
    Body (cConj X) (selOn bkP i ρ (1 : GE N →* K'ˣ) K' ∅) (selOn bkP i ρ' (1 : GE N →* K'ˣ) K' ∅) φ n := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun b => e (c b), fun x hx h0 => ?_⟩
  have := not_indep_mapC (e : K →ₐ[X.O0 i] K') _ (hc (fun a => mapC (e.symm : K' →ₐ[X.O0 i] K) (x a))
    (fun a => GlobalTheory.ResSel.CoefMap.cl_mem_selOn_of_algHom D N X bkP i ρ K' K (e.symm : K' →ₐ[X.O0 i] K) ∅ (x a) _ (fun _ _ => rfl) (hx a))
    fun a y hy => by
      have h1 := h0 a (mapC (e : K →ₐ[X.O0 i] K') y)
        (GlobalTheory.ResSel.CoefMap.cl_mem_selOn_of_algHom D N X bkP i ρ' K K' (e : K →ₐ[X.O0 i] K') ∅ y _ (fun _ _ => rfl) hy)
      apply e.injective
      rw [map_zero, ← h1, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul]
      congr 1
      conv_rhs => rw [← mapC_mapC e (x a), fm_mapC]
      rfl)
  simpa only [mapC_mapC] using this

end Transfer

theorem single (hsd : SelfDual i s) (h1 : SpanOdd i s) (h2 : SpanTwo i s) (h3 : EqDim bkP i s) :
    ∃ R₀ : ℕ, ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ L, Small i s L z → ∃ (h : Fin R₀ → GE N) (U : Subgroup (GE N)), (∀ a, h a ∈ L) ∧
      IsOpen (U : Set (GE N)) ∧ U.Normal ∧ ∀ (R : ℕ) (φ φ' : Fin R → GE N), (∀ b, IsCj X (φ b) (φ' b)) →
        (∀ a, ∃ b g, g * φ b * g⁻¹ * (h a)⁻¹ ∈ U) → Corank bkP i s φ φ' (if nu X i = 0 then 0 else 1) := by
  by_cases hρ : ∃ ρ, IsDual i s ρ
  · obtain ⟨ρ, hρ⟩ := hρ
    letI : TopologicalSpace (IsLocalRing.ResidueField (X.O0 i)) := ⊥
    haveI : DiscreteTopology (IsLocalRing.ResidueField (X.O0 i)) := ⟨rfl⟩
    obtain ⟨R₀, hR⟩ := single_field bkP i s (IsLocalRing.ResidueField (X.O0 i))
      (fun x hx => (IsLocalRing.residue_eq_zero_iff x).2 hx) hρ hsd h1 h2 h3
    refine ⟨R₀, fun z hz L hL => ?_⟩
    obtain ⟨h, U, a1, a2, a3, a4⟩ := hR z hz L hL
    refine ⟨h, U, a1, a2, a3, fun R φ φ' hc hφ K _ _ _ _ hK hs ρ' hρ' => ?_⟩
    obtain rfl : ρ = ρ' := MonoidHom.ext fun g => Units.ext ((hρ g).trans (hρ' g).symm)
    obtain rfl : φ' = fun b => cConj X (φ b) := funext fun b => isCj_iff.1 (hc b)
    let f : IsLocalRing.ResidueField (X.O0 i) →ₐ[X.O0 i] K :=
      Ideal.Quotient.liftₐ (IsLocalRing.maximalIdeal (X.O0 i)) (Algebra.ofId _ _) hK
    have hf : Function.Bijective f := ⟨f.toRingHom.injective, fun y => by
      obtain ⟨x, rfl⟩ := hs y
      exact ⟨_, f.commutes x⟩⟩
    exact body_transfer bkP (AlgEquiv.ofBijective f hf) (a4 R φ hφ)
  · exact ⟨0, fun z _ L hL => ⟨Fin.elim0, ⊤, fun a => a.elim0, isOpen_univ, inferInstance,
      fun R φ φ' _ _ K _ _ _ _ _ _ ρ h => (hρ ⟨ρ, h⟩).elim⟩⟩

theorem chooseH : GlobalFiniteness → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N)
    (bkP : BKPh X) (i : X.Tw), (∀ s, GalHyp bkP i s → SpanOdd i s ∧ SpanTwo i s ∧ EqDim bkP i s) → ChooseH bkP i := by
  intro _ D N X bkP i H T hT
  classical
  choose R hR using fun s : T => single bkP i s.1 (hT s.1 s.2).2.2.1 (H _ (hT s.1 s.2)).1 (H _ (hT s.1 s.2)).2.1
    (H _ (hT s.1 s.2)).2.2
  haveI : Fintype T := Fintype.ofFinite T
  let e := Fintype.equivFin (Σ s : T, Fin (R s))
  refine ⟨Fintype.card (Σ s : T, Fin (R s)), fun z hz L ho hn hL => ?_⟩
  choose h U a1 a2 a3 a4 using fun s : T => hR s z hz L (hL s.1 s.2)
  refine ⟨fun a => h (e.symm a).1 (e.symm a).2, L ⊓ ⨅ s, U s, fun a => a1 _ _, ?_, ?_, inf_le_left,
    fun φ φ' hφ s hs => a4 ⟨s, hs⟩ _ φ φ' (fun b => (hφ b).1) fun a => ?_⟩
  · simp only [Subgroup.coe_inf, Subgroup.coe_iInf]
    exact ho.inter (isOpen_iInter_of_finite a2)
  · refine ⟨fun u hu g => ?_⟩
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf] at hu ⊢
    exact ⟨hn.conj_mem u hu.1 g, fun s => (a3 s).conj_mem u (hu.2 s) g⟩
  · obtain ⟨g, hg⟩ := (hφ (e ⟨⟨s, hs⟩, a⟩)).2
    dsimp only at hg
    rw [Equiv.symm_apply_apply] at hg
    exact ⟨_, g, Subgroup.mem_iInf.1 hg.2 _⟩

end GlobalTheory.ChooseForms

end
