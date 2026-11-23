import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexCj
open GlobalTheory.ClassRefine GlobalTheory.ClassPet

noncomputable section

namespace GlobalTheory.TwoLattices

open scoped Classical

variable {G : Type} [Group G]

theorem finite_stab_mono {Γ Γ' K K' : Subgroup G} (h : Γ' ≤ Γ) (hK : K' ≤ K) (t : G) (hf : Finite (stabQ Γ K t)) :
    Finite (stabQ Γ' K' t) :=
  Finite.of_injective (fun γ : stabQ Γ' K' t => (⟨⟨γ.1, h γ.1.2⟩, mem_stabQ.2 (hK (mem_stabQ.1 γ.2))⟩ : stabQ Γ K t))
    fun _ _ e => Subtype.ext (Subtype.ext (congrArg (fun z : stabQ Γ K t => (z.1 : G)) e))

theorem Cover.of_finite {Γ Γ' K : Subgroup G} (hc : Cover Γ K) {α : Type} [Finite α] (r : Γ → α)
    (hr : ∀ a b, r a = r b → (a : G) * (b : G)⁻¹ ∈ Γ') : Cover Γ' K := by
  obtain ⟨S, hS⟩ := hc
  haveI := Fintype.ofFinite α
  refine ⟨(Finset.univ ×ˢ S).image fun p : α × G => ((Function.invFun r p.1 : Γ) : G) * p.2, fun g => ?_⟩
  obtain ⟨s, hs, γ, κ, hκ, e⟩ := hS g
  exact ⟨_, Finset.mem_image.2 ⟨(r γ, s), Finset.mem_product.2 ⟨Finset.mem_univ _, hs⟩, rfl⟩,
    ⟨_, hr γ _ (Function.invFun_eq ⟨γ, rfl⟩).symm⟩, κ, hκ, by rw [e]; simp [mul_assoc]⟩

def Kn (G X : Type) : Type := G × G → X → X → ℂ

variable {W X : Type} [AddCommGroup W] [Module ℂ W]

instance : MulAction G (Kn G X) where
  smul δ k := fun p => k (δ⁻¹ * p.1, δ⁻¹ * p.2)
  one_smul k := funext fun p => by
    show k (1⁻¹ * p.1, 1⁻¹ * p.2) = k p
    simp
  mul_smul a b k := funext fun p => by
    show k ((a * b)⁻¹ * p.1, (a * b)⁻¹ * p.2) = k (b⁻¹ * (a⁻¹ * p.1), b⁻¹ * (a⁻¹ * p.2))
    simp [mul_assoc]

theorem smul_kn (δ : G) (k : Kn G X) (p : G × G) : (δ • k) p = k (δ⁻¹ * p.1, δ⁻¹ * p.2) := rfl

def kn (f : X → G → W) (b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : Kn G X := fun p x x' => b (f x p.1) (f x' p.2)

def acts (f : X → G → W) : Subgroup G where
  carrier := {δ | (∃ A : W →ₗ[ℂ] W, ∀ x g, f x (δ * g) = A (f x g)) ∧ ∃ A : W →ₗ[ℂ] W, ∀ x g, f x (δ⁻¹ * g) = A (f x g)}
  one_mem' := ⟨⟨LinearMap.id, by simp⟩, ⟨LinearMap.id, by simp⟩⟩
  mul_mem' := by
    rintro a b ⟨⟨A, hA⟩, A', hA'⟩ ⟨⟨B, hB⟩, B', hB'⟩
    exact ⟨⟨A.comp B, fun x g => by rw [mul_assoc, hA, hB]; rfl⟩,
      ⟨B'.comp A', fun x g => by rw [mul_inv_rev, mul_assoc, hB', hA']; rfl⟩⟩
  inv_mem' := by
    rintro a ⟨h, h'⟩
    exact ⟨h', by simpa using h⟩

theorem le_acts {f : X → G → W} {Γ : Subgroup G} (h : ∀ γ ∈ Γ, ∃ A : W →ₗ[ℂ] W, ∀ x g, f x (γ * g) = A (f x g)) : Γ ≤ acts f :=
  fun γ hγ => ⟨h γ hγ, h _ (Γ.inv_mem hγ)⟩

def IsPos (b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : Prop := (∀ x y, b x y = starRingEnd ℂ (b y x)) ∧ ∀ x, x ≠ 0 → 0 < (b x x).re

section Span

variable {f : X → G → W} {ι : Type} {p : ι → X × G} (hs : Submodule.span ℂ (Set.range fun i => f (p i).1 (p i).2) = ⊤)
include hs

theorem smul_kn_pos {δ : G} (hδ : δ ∈ acts f) {b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} (hb : IsPos b) : ∃ b', IsPos b' ∧ kn f b' = δ • kn f b := by
  obtain ⟨⟨A, hA⟩, A', hA'⟩ := hδ
  have h : A.comp A' = LinearMap.id := LinearMap.ext_on_range hs fun i => by
    rw [LinearMap.comp_apply, ← hA', ← hA]
    simp
  refine ⟨(b.comp A').compl₂ A', ⟨fun x y => hb.1 _ _, fun x hx => hb.2 _ fun h0 => hx ?_⟩, funext fun q => ?_⟩
  · have := LinearMap.congr_fun h x
    rw [LinearMap.comp_apply, h0, map_zero] at this
    exact this.symm
  · funext x x'
    show b (A' _) (A' _) = b _ _
    rw [hA', hA']

theorem fix_of_mem {K : Subgroup G} (hr : ∀ κ ∈ K, ∀ x g, f x (g * κ) = f x g) {δ : G} (hδ : δ ∈ acts f)
    (h : ∀ i, δ ∈ cj K (p i).2) (b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : δ • kn f b = kn f b := by
  obtain ⟨-, A, hA⟩ := hδ
  have e : A = LinearMap.id := LinearMap.ext_on_range hs fun i => by
    rw [← hA, LinearMap.id_apply, ← hr _ (mem_cj.1 (h i))]
    simp [mul_assoc]
  funext q x x'
  show b _ _ = b _ _
  rw [hA, hA, e]
  rfl

theorem finite_orbit [Finite ι] {K Γ : Subgroup G} (hK : ∀ x, (cj K x).relIndex K ≠ 0) (hr : ∀ κ ∈ K, ∀ x g, f x (g * κ) = f x g)
    (hΓ : Γ ≤ acts f) (hc : Cover Γ K) {b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} (hb : IsPos b) (hinv : ∀ γ ∈ Γ, γ • kn f b = kn f b) :
    Finite (MulAction.orbit (acts f) (kn f b)) := by
  obtain ⟨S, hS⟩ := hc.of_relIndex (Subgroup.relIndex_iInf_ne_zero fun i => hK (p i).2)
  choose s hs' γ κ hκ e using hS
  choose δ hδ using fun k : MulAction.orbit (acts f) (kn f b) => k.2
  refine Finite.of_injective (fun k => (⟨s (δ k : G)⁻¹, hs' _⟩ : S)) fun k k' h => Subtype.ext ?_
  have h1 : s (δ k : G)⁻¹ = s (δ k' : G)⁻¹ := congrArg Subtype.val h
  have h2 := e (δ k : G)⁻¹
  have h3 := e (δ k' : G)⁻¹
  rw [h1] at h2
  rw [← hδ k, ← hδ k']
  generalize γ (δ k : G)⁻¹ = a at h2
  generalize γ (δ k' : G)⁻¹ = a' at h3
  have h4 := hκ (δ k : G)⁻¹
  have h5 := hκ (δ k' : G)⁻¹
  generalize κ (δ k : G)⁻¹ = c at h2 h4
  generalize κ (δ k' : G)⁻¹ = c' at h3 h5
  generalize s (δ k' : G)⁻¹ = t at h2 h3
  have h6 : c⁻¹ * c' = δ k * (a * (a' : G)⁻¹) * (δ k' : G)⁻¹ := by
    rw [h3, inv_eq_iff_eq_inv.1 h2]; group
  have h7 : (δ k : G) = c⁻¹ * c' * δ k' * (a' * (a : G)⁻¹) := by rw [h6]; group
  obtain ⟨b', -, hb'⟩ := smul_kn_pos hs (δ k').2 hb
  show (δ k : G) • kn f b = (δ k' : G) • kn f b
  rw [h7, mul_smul, mul_smul, hinv _ (Γ.mul_mem a'.2 (Γ.inv_mem a.2)), ← hb']
  refine fix_of_mem hs hr ?_ (fun i => Subgroup.mem_iInf.1 (Subgroup.mul_mem _ (Subgroup.inv_mem _ h4) h5) i) b'
  rw [h6]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (δ k).2 (hΓ (Γ.mul_mem a.2 (Γ.inv_mem a'.2)))) (Subgroup.inv_mem _ (δ k').2)

theorem exists_form [Finite ι] {K Γ₁ Γ₂ : Subgroup G} (hK : ∀ x, (cj K x).relIndex K ≠ 0)
    (hr : ∀ κ ∈ K, ∀ x g, f x (g * κ) = f x g) (h₁ : Γ₁ ≤ acts f) (h₂ : Γ₂ ≤ acts f) (hc₁ : Cover Γ₁ K) (hc₂ : Cover Γ₂ K)
    (hf₁ : ∀ t, Finite (stabQ Γ₁ K t)) (hf₂ : ∀ t, Finite (stabQ Γ₂ K t)) {b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} (hb : IsPos b)
    (hinv : ∀ γ ∈ Γ₂, ∀ x x' g g', b (f x (γ * g)) (f x' (γ * g')) = b (f x g) (f x' g')) :
    ∃ (β : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (c : ℝ), IsPos β ∧ 0 < c ∧
      (∀ γ ∈ Γ₁, ∀ x x' g g', β (f x (γ * g)) (f x' (γ * g')) = β (f x g) (f x' g')) ∧
      ∀ x x', dsum Γ₂ K (fun g => b (f x g) (f x' g)) = c * dsum Γ₁ K fun g => β (f x g) (f x' g) := by
  have hinv' : ∀ γ ∈ Γ₂, γ • kn f b = kn f b := fun γ hγ => funext fun q => funext fun x => funext fun x' =>
    hinv _ (Γ₂.inv_mem hγ) x x' q.1 q.2
  haveI := finite_orbit hs hK hr h₂ hc₂ hb hinv'
  set O := MulAction.orbit (acts f) (kn f b) with hO
  haveI := Fintype.ofFinite O
  have hk₀ : kn f b ∈ O := MulAction.mem_orbit_self _
  choose δ hδ using fun k : O => k.2
  choose B hB eB using fun k : O => smul_kn_pos hs (δ k).2 hb
  have eB' : ∀ k, kn f (B k) = k := fun k => (eB k).trans (hδ k)
  have hβ : ∀ x x' g g', (∑ k, B k) (f x g) (f x' g') = ∑ k : O, (k : Kn G X) (g, g') x x' := fun x x' g g' => by
    rw [LinearMap.sum_apply, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [← eB' k]; rfl
  have hβinv : ∀ γ ∈ acts f, ∀ x x' g g', (∑ k, B k) (f x (γ * g)) (f x' (γ * g')) = (∑ k, B k) (f x g) (f x' g') := by
    intro γ hγ x x' g g'
    rw [hβ, hβ, ← Equiv.sum_comp (MulAction.toPerm (⟨γ, hγ⟩ : acts f))]
    refine Finset.sum_congr rfl fun k _ => ?_
    show (γ • (k : Kn G X)) (γ * g, γ * g') x x' = _
    simp [smul_kn]
  let Δ : Subgroup G := fixingSubgroup G O
  have hΔ : ∀ a, a ∈ Δ ↔ ∀ k ∈ O, a • k = k := fun a => mem_fixingSubgroup_iff G
  have hst : ∀ a ∈ acts f, ∀ k ∈ O, a • k ∈ O := fun a ha k hk => (((⟨a, ha⟩ : acts f) • (⟨k, hk⟩ : O) : O)).2
  have hc₃ : Cover (Γ₂ ⊓ Δ) K := hc₂.of_finite (fun γ (k : O) => (⟨(γ : G)⁻¹ • (k : Kn G X), hst _ (h₂ (Γ₂.inv_mem γ.2)) _ k.2⟩ : O))
    fun a a' e => ⟨Γ₂.mul_mem a.2 (Γ₂.inv_mem a'.2), (hΔ _).2 fun k hk => by
      have : (a : G)⁻¹ • k = (a' : G)⁻¹ • k := congrArg Subtype.val (congrFun e ⟨k, hk⟩)
      rw [mul_smul, ← this, smul_inv_smul]⟩
  have hf₃ : ∀ t, Finite (stabQ (Γ₂ ⊓ Δ) K t) := fun t => finite_stab_mono inf_le_left le_rfl t (hf₂ t)
  have hl₀ : ∀ x x', ∀ γ ∈ Γ₂, ∀ g, b (f x (γ * g)) (f x' (γ * g)) = b (f x g) (f x' g) := fun x x' γ hγ g => hinv γ hγ x x' g g
  have hr₀ : ∀ (b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) x x', ∀ κ ∈ K, ∀ g, b (f x (g * κ)) (f x' (g * κ)) = b (f x g) (f x' g) :=
    fun b x x' κ hκ g => by rw [hr κ hκ, hr κ hκ]
  have hk : ∀ k : O, ∃ c : ℝ, 0 < c ∧ ∀ x x', dsum (Γ₂ ⊓ Δ) K (fun g => (k : Kn G X) (g, g) x x') =
      c * dsum (Γ₂ ⊓ Δ) K fun g => b (f x g) (f x' g) := by
    intro k
    obtain ⟨T, hT⟩ := hc₃.reps
    have hc₄ := (reps_conj hT (δ k) 1).cover
    rw [cj_one] at hc₄
    obtain ⟨c, hc, e⟩ := dsum_prop (Δ := Δ) hK inf_le_right (fun a ha => (hΔ _).2 fun k' hk' => by
        have := (hΔ _).1 (mem_cj.1 ha).2 _ (hst _ (Subgroup.inv_mem _ (δ k).2) _ hk')
        rw [mul_smul, smul_inv_smul, mul_smul] at this
        exact smul_left_cancel _ this) hc₃ hc₄ hf₃ (fun t => by
        have := (stabConj (Γ₂ ⊓ Δ) K (δ k) 1 ((δ k : G)⁻¹ * t)).finite_iff.2 (hf₃ _)
        rwa [cj_one, inv_one, mul_one, mul_inv_cancel_left] at this)
    refine ⟨c, hc, fun x x' => ?_⟩
    rw [e _ (fun a ha g => ?_) (fun κ hκ g => ?_), ← dsum_conj hc₃ (fun γ => hl₀ x x' γ γ.2.1) (hr₀ b x x') (δ k) 1, cj_one]
    · congr 2
      funext g
      rw [← hδ k, mul_one]
      rfl
    · conv_rhs => rw [← (hΔ _).1 (Δ.inv_mem ha) k k.2]
      simp [smul_kn]
    · rw [← eB' k]
      exact hr₀ _ x x' κ hκ g
  choose c hc ec using hk
  obtain ⟨c₁, hc₁', e₁⟩ := dsum_prop hK (inf_le_left.trans h₂) h₁ hc₃ hc₁ hf₃ hf₁
  obtain ⟨c₂, hc₂', e₂⟩ := dsum_prop hK le_rfl inf_le_left hc₂ hc₃ hf₂ hf₃
  have hpos : 0 < ∑ k, c k := Finset.sum_pos (fun k _ => hc k) ⟨⟨_, hk₀⟩, Finset.mem_univ _⟩
  refine ⟨∑ k, B k, c₂ * c₁ / ∑ k, c k, ⟨fun x y => ?_, fun x hx => ?_⟩, by positivity, fun γ hγ => hβinv γ (h₁ hγ), fun x x' => ?_⟩
  · simp only [LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => (hB k).1 x y
  · simp only [LinearMap.sum_apply, Complex.re_sum]
    exact Finset.sum_pos (fun k _ => (hB k).2 x hx) ⟨⟨_, hk₀⟩, Finset.mem_univ _⟩
  · have e₃ := e₁ (fun g => (∑ k, B k) (f x g) (f x' g)) (fun a ha g => hβinv a ha x x' g g) (hr₀ _ x x')
    have e₄ : dsum (Γ₂ ⊓ Δ) K (fun g => (∑ k, B k) (f x g) (f x' g)) =
        ((∑ k, c k : ℝ) : ℂ) * dsum (Γ₂ ⊓ Δ) K fun g => b (f x g) (f x' g) := by
      simp_rw [hβ]
      rw [dsum_sum, Complex.ofReal_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => ec k x x'
    have hne : ((∑ k, c k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
    rw [e₂ _ (hl₀ x x') (hr₀ b x x'), Complex.ofReal_div, Complex.ofReal_mul, div_mul_eq_mul_div, mul_assoc, ← e₃, e₄]
    field_simp

end Span

end GlobalTheory.TwoLattices

end
