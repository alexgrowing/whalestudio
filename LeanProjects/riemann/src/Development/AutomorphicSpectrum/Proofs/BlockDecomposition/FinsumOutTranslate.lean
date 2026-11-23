import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil

noncomputable section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 Pointwise

namespace GlobalTheory.CompanionTheory.HeckeMul

section Generic

variable {G : Type} [Group G]

theorem out_mk_of_right_inv {M : Type} (K : Subgroup G) (φ : G → M)
    (hφ : ∀ x, ∀ k ∈ K, φ (x * k) = φ x) (x : G) :
    φ (QuotientGroup.mk x : G ⧸ K).out = φ x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hh]
  exact hφ x h h.2

theorem finsum_out_translate {M : Type} [AddCommMonoid M] (K : Subgroup G) (φ : G → M)
    (hφ : ∀ x, ∀ k ∈ K, φ (x * k) = φ x) (a : G) :
    ∑ᶠ q : G ⧸ K, φ (a * q.out) = ∑ᶠ q : G ⧸ K, φ q.out := by
  rw [← finsum_comp_equiv (MulAction.toPerm a : Equiv.Perm (G ⧸ K)) (f := fun q : G ⧸ K => φ q.out)]
  refine finsum_congr fun q => ?_
  have h : (MulAction.toPerm a : Equiv.Perm (G ⧸ K)) q = (QuotientGroup.mk (a * q.out) : G ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [h, out_mk_of_right_inv K φ hφ]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_out_mem (K : Subgroup G) (hK : IsOpen (K : Set G)) {C : Set G} (hC : IsCompact C) :
    {q : G ⧸ K | q.out ∈ C}.Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' C) :=
    hC.image QuotientGroup.continuous_mk
  refine hc.finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, hq, QuotientGroup.out_eq' q⟩

end Generic

section Hecke

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isHk_right {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (h : IsHk K e) (x : GL ι F)
    {k : GL ι F} (hk' : k ∈ K) : e (x * k) = e x := by
  simpa using h.2.2.2 1 K.one_mem k hk' x

theorem isHk_left {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (h : IsHk K e) (x : GL ι F)
    {k : GL ι F} (hk' : k ∈ K) : e (k * x) = e x := by
  simpa using h.2.2.2 k hk' 1 K.one_mem x

theorem support_hconv (K : Subgroup (GL ι F)) (e₁ e₂ : GL ι F → ℂ) :
    Function.support (hconv K e₁ e₂) ⊆ tsupport e₁ * tsupport e₂ := by
  intro g hg
  obtain ⟨q, hq⟩ : ∃ q : GL ι F ⧸ K, e₁ q.out * e₂ (q.out⁻¹ * g) ≠ 0 := by
    by_contra h
    push_neg at h
    refine (Function.mem_support.1 hg) ?_
    unfold hconv
    simp only [h]
    exact finsum_zero
  exact Set.mem_mul.2 ⟨q.out, subset_tsupport _ (left_ne_zero_of_mul hq), q.out⁻¹ * g,
    subset_tsupport _ (right_ne_zero_of_mul hq), mul_inv_cancel_left _ _⟩

theorem hconv_biinv {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂)
    {k₁ k₂ : GL ι F} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K) (g : GL ι F) :
    hconv K e₁ e₂ (k₁ * g * k₂) = hconv K e₁ e₂ g := by
  have hφ : ∀ x, ∀ k ∈ K, (fun y => e₁ y * e₂ (y⁻¹ * g)) (x * k) = (fun y => e₁ y * e₂ (y⁻¹ * g)) x := by
    intro x k hk'
    show e₁ (x * k) * e₂ ((x * k)⁻¹ * g) = e₁ x * e₂ (x⁻¹ * g)
    rw [isHk_right h₁ x hk', mul_inv_rev, mul_assoc, isHk_left h₂ _ (K.inv_mem hk')]
  have ht := finsum_out_translate K (fun y => e₁ y * e₂ (y⁻¹ * g)) hφ k₁⁻¹
  unfold hconv
  rw [← ht]
  refine finsum_congr fun q => ?_
  show e₁ q.out * e₂ (q.out⁻¹ * (k₁ * g * k₂)) = e₁ (k₁⁻¹ * q.out) * e₂ ((k₁⁻¹ * q.out)⁻¹ * g)
  rw [isHk_left h₁ _ (K.inv_mem hk₁), ← mul_assoc, isHk_right h₂ _ hk₂]
  simp [mul_assoc]

theorem isHk_hconv {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂) :
    IsHk K (hconv K e₁ e₂) := by
  refine ⟨h₁.1, h₁.2.1, ?_, fun k₁ hk₁ k₂ hk₂ g => hconv_biinv h₁ h₂ hk₁ hk₂ g⟩
  have hc : IsCompact (tsupport e₁ * tsupport e₂) := IsCompact.mul h₁.2.2.1 h₂.2.2.1
  exact HasCompactSupport.of_support_subset_isCompact hc (support_hconv K e₁ e₂)

theorem hk_eq_sum {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V)
    (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (w : V) (A : Finset (GL ι F ⧸ K))
    (hA : ∀ q : GL ι F ⧸ K, e q.out ≠ 0 → q ∈ A) :
    hk ρ K e w = ∑ q ∈ A, e q.out • ρ q.out w := by
  unfold hk
  refine finsum_eq_sum_of_support_subset _ ?_
  intro q hq
  refine Finset.mem_coe.2 (hA q fun h0 => (Function.mem_support.1 hq) ?_)
  show e q.out • ρ q.out w = 0
  rw [h0, zero_smul]

theorem hk_hconv {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V) {v : V}
    (hv : v ∈ fixed ρ K) :
    hk ρ K (hconv K e₁ e₂) v = hk ρ K e₁ (hk ρ K e₂ v) := by
  have hvk : ∀ k ∈ K, ρ k v = v := fun k hk' => by
    have := hv ⟨k, hk'⟩
    simpa using this
  have c1 : IsCompact (tsupport e₁) := h₁.2.2.1
  have c2 : IsCompact (tsupport e₂) := h₂.2.2.1
  have c12 : IsCompact (tsupport e₁ * tsupport e₂) := IsCompact.mul c1 c2
  let A := (finite_out_mem K h₁.1 c1).toFinset
  let A₂ := (finite_out_mem K h₁.1 c2).toFinset
  let B := (finite_out_mem K h₁.1 c12).toFinset
  have memA : ∀ q : GL ι F ⧸ K, q ∈ A ↔ q.out ∈ tsupport e₁ := fun q => by simp [A]
  have memA₂ : ∀ q : GL ι F ⧸ K, q ∈ A₂ ↔ q.out ∈ tsupport e₂ := fun q => by simp [A₂]
  have memB : ∀ q : GL ι F ⧸ K, q ∈ B ↔ q.out ∈ tsupport e₁ * tsupport e₂ := fun q => by simp [B]
  have hc : ∀ g, hconv K e₁ e₂ g = ∑ q ∈ A, e₁ q.out * e₂ (q.out⁻¹ * g) := fun g => by
    unfold hconv
    refine finsum_eq_sum_of_support_subset _ ?_
    intro q hq
    exact Finset.mem_coe.2 ((memA q).2 (subset_tsupport _ (left_ne_zero_of_mul hq)))
  have hL := hk_eq_sum ρ K (hconv K e₁ e₂) v B
    (fun s hs => (memB s).2 (support_hconv K e₁ e₂ hs))
  have hT : ∀ x : GL ι F, ∑ᶠ r : GL ι F ⧸ K, e₂ r.out • ρ (x * r.out) v
      = ∑ᶠ s : GL ι F ⧸ K, e₂ (x⁻¹ * s.out) • ρ s.out v := fun x => by
    have hr : ∀ y, ∀ k ∈ K, (fun y => e₂ (x⁻¹ * y) • ρ y v) (y * k) = (fun y => e₂ (x⁻¹ * y) • ρ y v) y := by
      intro y k hk'
      show e₂ (x⁻¹ * (y * k)) • ρ (y * k) v = e₂ (x⁻¹ * y) • ρ y v
      rw [← mul_assoc, isHk_right h₂ _ hk', map_mul, Module.End.mul_apply, hvk k hk']
    have ht := finsum_out_translate K (fun y => e₂ (x⁻¹ * y) • ρ y v) hr x
    simpa only [inv_mul_cancel_left] using ht
  have hI : ∀ q ∈ A, ρ q.out (hk ρ K e₂ v) = ∑ s ∈ B, e₂ (q.out⁻¹ * s.out) • ρ s.out v := by
    intro q hq
    have hq' := (memA q).1 hq
    rw [hk_eq_sum ρ K e₂ v A₂ (fun r hr => (memA₂ r).2 (subset_tsupport _ hr)), map_sum]
    have h1 : ∑ r ∈ A₂, ρ q.out (e₂ r.out • ρ r.out v) = ∑ᶠ r : GL ι F ⧸ K, e₂ r.out • ρ (q.out * r.out) v := by
      symm
      rw [finsum_eq_sum_of_support_subset (s := A₂)]
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [map_smul, map_mul, Module.End.mul_apply]
      · intro r hr
        refine Finset.mem_coe.2 ((memA₂ r).2 (subset_tsupport _ fun h0 => (Function.mem_support.1 hr) ?_))
        show e₂ r.out • ρ (q.out * r.out) v = 0
        rw [h0, zero_smul]
    rw [h1, hT]
    refine finsum_eq_sum_of_support_subset _ ?_
    intro s hs
    refine Finset.mem_coe.2 ((memB s).2 (Set.mem_mul.2 ⟨q.out, hq', q.out⁻¹ * s.out,
      subset_tsupport _ fun h0 => (Function.mem_support.1 hs) ?_, mul_inv_cancel_left _ _⟩))
    show e₂ (q.out⁻¹ * s.out) • ρ s.out v = 0
    rw [h0, zero_smul]
  have hR : hk ρ K e₁ (hk ρ K e₂ v)
      = ∑ q ∈ A, e₁ q.out • ∑ s ∈ B, e₂ (q.out⁻¹ * s.out) • ρ s.out v := by
    rw [hk_eq_sum ρ K e₁ _ A (fun q hq => (memA q).2 (subset_tsupport _ hq))]
    exact Finset.sum_congr rfl (fun q hq => by rw [hI q hq])
  rw [hL, hR]
  simp only [hc, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

end Hecke

theorem hk_mul : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)) (e₁ e₂ : GL ι F → ℂ), IsHk K e₁ → IsHk K e₂ → IsHk K (hconv K e₁ e₂) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V), ∀ v ∈ fixed ρ K, hk ρ K (hconv K e₁ e₂) v = hk ρ K e₁ (hk ρ K e₂ v) := by
  intro F _ _ _ _ ι _ _ K e₁ e₂ h₁ h₂
  exact ⟨isHk_hconv h₁ h₂, fun V _ _ ρ v hv => hk_hconv h₁ h₂ ρ hv⟩

end GlobalTheory.CompanionTheory.HeckeMul
