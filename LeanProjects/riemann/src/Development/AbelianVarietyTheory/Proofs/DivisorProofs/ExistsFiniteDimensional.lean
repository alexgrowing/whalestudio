import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocType

noncomputable section

open Topology GlobalTheory.PRep

namespace GlobalTheory.ThK.CoinvFin

variable {G : Type} [Group G]

def IsAvg (K K' : Subgroup G) (t : Finset G) : Prop :=
  t.Nonempty ∧ (∀ g ∈ t, g ∈ K) ∧ ∀ (V : Type) [AddCommMonoid V] (φ : G → V), (∀ g, ∀ k ∈ K', φ (g * k) = φ g) →
    ∀ k ∈ K, ∑ g ∈ t, φ (k * g) = ∑ g ∈ t, φ g

theorem IsAvg.mono {K K' K'' : Subgroup G} {t : Finset G} (h : IsAvg K K'' t) (hle : K'' ≤ K') : IsAvg K K' t :=
  ⟨h.1, h.2.1, fun V _ φ hφ => h.2.2 V φ fun g k hk => hφ g k (hle hk)⟩

theorem IsAvg.card_ne {K K' : Subgroup G} {t : Finset G} (h : IsAvg K K' t) : (t.card : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 (Finset.card_pos.2 h.1).ne'

def stab {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem IsAvg.fix {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) {K : Subgroup G}
    {t : Finset G} (h : IsAvg K (stab ρ v) t) : ∀ k ∈ K, ρ k (∑ g ∈ t, ρ g v) = ∑ g ∈ t, ρ g v := by
  intro k hk
  rw [map_sum, ← h.2.2 V (fun g => ρ g v) (fun g k hk => by
    rw [map_mul, Module.End.mul_apply, show ρ k v = v from hk]) k hk]
  simp only [map_mul, Module.End.mul_apply]

theorem mem_fixed {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    simpa using h ⟨k, hk⟩
  · intro h k
    simpa using h k.1 k.2

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_quot {K K' : Subgroup G} (hK : IsCompact (K : Set G)) (hK' : IsOpen (K' : Set G)) :
    Finite (K ⧸ K'.subgroupOf K) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  exact Subgroup.quotient_finite_of_isOpen _ (hK'.preimage continuous_subtype_val)

theorem exists_isAvg {K K' : Subgroup G} (hK : IsCompact (K : Set G)) (hK' : IsOpen (K' : Set G)) :
    ∃ t, IsAvg K K' t := by
  classical
  haveI := finite_quot hK hK'
  haveI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)
  let o : (K ⧸ K'.subgroupOf K) → G := fun q => (q.out : K)
  have ho : Function.Injective o := fun q q' h => Quotient.out_injective (Subtype.ext h)
  refine ⟨Finset.univ.image o, Finset.univ_nonempty.image _, ?_, fun V _ φ hφ k hk => ?_⟩
  · intro g hg
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hg
    exact q.out.2
  · rw [Finset.sum_image fun _ _ _ _ h => ho h, Finset.sum_image fun _ _ _ _ h => ho h,
      ← Equiv.sum_comp (MulAction.toPerm (⟨k, hk⟩ : K)) fun q => φ (o q)]
    refine Finset.sum_congr rfl fun q _ => ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K'.subgroupOf K) ((⟨k, hk⟩ : K) * q.out)
    have e : (MulAction.toPerm (⟨k, hk⟩ : K)) q = QuotientGroup.mk ((⟨k, hk⟩ : K) * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    simp only [e, o, hh]
    exact (hφ _ _ h.2).symm

theorem mem_of_avg {Z : Type} [AddCommGroup Z] [Module ℂ Z] (ζ : Representation ℂ G Z) {K : Subgroup G}
    (hK : IsCompact (K : Set G)) (S : Set Z) (W : Submodule ℂ Z)
    (h : ∀ x ∈ S, ∃ K' : Subgroup G, IsOpen (K' : Set G) ∧ ∀ t, IsAvg K K' t → ∑ g ∈ t, ζ g x ∈ W) :
    ∀ x ∈ Submodule.span ℂ S, (∀ k ∈ K, ζ k x = x) → x ∈ W := by
  have key : ∀ x ∈ Submodule.span ℂ S, ∃ K' : Subgroup G, IsOpen (K' : Set G) ∧
      ∀ t, IsAvg K K' t → ∑ g ∈ t, ζ g x ∈ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => exact ⟨⊤, isOpen_univ, fun t _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨K₁, o₁, h₁⟩ := hx
      obtain ⟨K₂, o₂, h₂⟩ := hy
      refine ⟨K₁ ⊓ K₂, o₁.inter o₂, fun t ht => ?_⟩
      simp only [map_add, Finset.sum_add_distrib]
      exact add_mem (h₁ t (ht.mono inf_le_left)) (h₂ t (ht.mono inf_le_right))
    | smul c x _ hx =>
      obtain ⟨K₁, o₁, h₁⟩ := hx
      refine ⟨K₁, o₁, fun t ht => ?_⟩
      simp only [map_smul, ← Finset.smul_sum]
      exact W.smul_mem c (h₁ t ht)
  intro x hx hfix
  obtain ⟨K', o, h'⟩ := key x hx
  obtain ⟨t, ht⟩ := exists_isAvg hK o
  have h1 := h' t ht
  rw [Finset.sum_congr rfl fun g hg => hfix g (ht.2.1 g hg), Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at h1
  exact (W.smul_mem_iff ht.card_ne).1 h1

def orb {U : Type} [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ G U) (w : U) : Submodule ℂ U :=
  Submodule.span ℂ (Set.range fun g => ρ g w)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem orb_stable {U : Type} [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ G U) (w : U) :
    ∀ g, ∀ u ∈ orb ρ w, ρ g u ∈ orb ρ w := by
  intro g u hu
  refine (Submodule.span_le (p := (orb ρ w).comap (ρ g))).2 ?_ hu
  rintro _ ⟨x, rfl⟩
  exact Submodule.subset_span ⟨g * x, by simp⟩

theorem isAdmissible_orb {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (π : Representation ℂ G V) (ρ : Representation ℂ G U) (hπ : IsAdmissible π) (w : U)
    (hw : w ∈ GlobalTheory.LocTypeGood.imgSpan π ρ) : IsAdmissible (sub ρ (orb ρ w) (orb_stable ρ w)) := by
  obtain ⟨s, hs, hT, hws⟩ : ∃ s : Set (V →ₗ[ℂ] U), s.Finite ∧ (∀ T ∈ s, ∀ g, T ∘ₗ π g = ρ g ∘ₗ T) ∧
      w ∈ Submodule.span ℂ {x | ∃ T ∈ s, ∃ v, x = T v} := by
    unfold GlobalTheory.LocTypeGood.imgSpan at hw
    induction hw using Submodule.iSup_induction' with
    | mem T x hx =>
      by_cases h : ∀ g, T ∘ₗ π g = ρ g ∘ₗ T
      · rw [iSup_pos h] at hx
        obtain ⟨v, rfl⟩ := hx
        exact ⟨{T}, Set.finite_singleton _, by simpa using h, Submodule.subset_span ⟨T, rfl, v, rfl⟩⟩
      · rw [iSup_neg h, Submodule.mem_bot] at hx
        exact ⟨∅, Set.finite_empty, by simp, by simp [hx]⟩
    | zero => exact ⟨∅, Set.finite_empty, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, h1, h2⟩ := hx
      obtain ⟨s', hs', h1', h2'⟩ := hy
      refine ⟨s ∪ s', hs.union hs', fun T hT => hT.elim (h1 T) (h1' T), add_mem ?_ ?_⟩
      · exact Submodule.span_mono (by rintro _ ⟨T, hT, v, rfl⟩; exact ⟨T, Or.inl hT, v, rfl⟩) h2
      · exact Submodule.span_mono (by rintro _ ⟨T, hT, v, rfl⟩; exact ⟨T, Or.inr hT, v, rfl⟩) h2'
  have hTv : ∀ T ∈ s, ∀ g v, ρ g (T v) = T (π g v) := fun T h g v => (LinearMap.congr_fun (hT T h g) v).symm
  set N := Submodule.span ℂ {x | ∃ T ∈ s, ∃ v, x = T v} with hN
  have hle : orb ρ w ≤ N := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    refine (Submodule.span_le (p := N.comap (ρ g))).2 ?_ hws
    rintro _ ⟨T, h, v, rfl⟩
    exact Submodule.subset_span ⟨T, h, π g v, hTv T h g v⟩
  have hsm : ∀ u ∈ N, (stab ρ u : Set G) ∈ 𝓝 (1 : G) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨T, h, v, rfl⟩ := hx
      refine Filter.mem_of_superset ((hπ.1 v).mem_nhds (by simp)) fun g hg => ?_
      show ρ g (T v) = T v
      rw [hTv T h, show π g v = v from hg]
    | zero => exact Filter.mem_of_superset Filter.univ_mem fun g _ => map_zero _
    | add x y _ _ hx hy =>
      refine Filter.mem_of_superset (Filter.inter_mem hx hy) fun g hg => ?_
      show ρ g (x + y) = x + y
      rw [map_add, show ρ g x = x from hg.1, show ρ g y = y from hg.2]
    | smul c x _ hx =>
      refine Filter.mem_of_superset hx fun g hg => ?_
      show ρ g (c • x) = c • x
      rw [map_smul, show ρ g x = x from hg]
  refine ⟨fun u => ?_, fun K ho hc => ?_⟩
  · have := (stab ρ u.1).isOpen_of_mem_nhds (hsm u.1 (hle u.2))
    convert this using 1
    ext g
    exact Subtype.ext_iff
  · haveI := hπ.2 K ho hc
    haveI : Finite s := hs
    let W : Submodule ℂ U := ⨆ T : s, (fixed π K).map T.1
    have hW : ∀ x ∈ N, (∀ k ∈ K, ρ k x = x) → x ∈ W := by
      refine mem_of_avg ρ hc _ W ?_
      rintro _ ⟨T, h, v, rfl⟩
      refine ⟨stab π v, hπ.1 v, fun t ht => ?_⟩
      refine Submodule.mem_iSup_of_mem ⟨T, h⟩ ⟨∑ g ∈ t, π g v, (mem_fixed _ _ _).2 (ht.fix π v), ?_⟩
      simp only [map_sum, hTv T h]
    let L : fixed (sub ρ (orb ρ w) (orb_stable ρ w)) K →ₗ[ℂ] W :=
      (((orb ρ w).subtype.comp (Submodule.subtype _))).codRestrict W fun x =>
        hW _ (hle x.1.2) fun k hk => congrArg Subtype.val ((mem_fixed _ _ _).1 x.2 k hk)
    exact FiniteDimensional.of_injective L fun x y h =>
      Subtype.ext (Subtype.ext (show (L x).1 = (L y).1 from congrArg Subtype.val h))

theorem exists_finiteDimensional {G₂ : Type} [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
    {U P Z J : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup P] [Module ℂ P] [AddCommGroup Z] [Module ℂ Z] [Finite J]
    (π : Representation ℂ G₂ U) (ω₁ : Representation ℂ G P) (ω₂ : Representation ℂ G₂ P) (ζ : Representation ℂ G Z)
    (b : U →ₗ[ℂ] P →ₗ⋆[ℂ] Z) (D : J → Submodule ℂ P) (hπ : IsAdmissible π)
    (h1 : ∀ j g, ∀ s ∈ D j, ω₁ g s ∈ D j)
    (eq1 : ∀ g u s, ζ g (b u s) = b u (ω₁ g s)) (eq2 : ∀ h u s, b (π h u) (ω₂ h s) = b u s)
    (sm1 : ∀ j, ∀ s ∈ D j, IsOpen (stab ω₁ s : Set G)) (sm2 : ∀ j, ∀ s ∈ D j, IsOpen (stab ω₂ s : Set G₂))
    (K₀ : Subgroup G₂) (ho : IsOpen (K₀ : Set G₂)) (hc : IsCompact (K₀ : Set G₂))
    (K : Subgroup G) (hK : IsCompact (K : Set G))
    (fg : ∀ j, ∃ A : Set P, A.Finite ∧ (∀ a ∈ A, a ∈ D j) ∧ ∀ s ∈ D j, (∀ k ∈ K, ω₁ k s = s) →
      s ∈ Submodule.span ℂ {x | ∃ a ∈ A, ∃ h, x = ω₂ h a}) :
    ∃ W : Submodule ℂ Z, FiniteDimensional ℂ W ∧
      ∀ x ∈ Submodule.span ℂ {x | ∃ j u, ∃ s ∈ D j, x = b u s}, (∀ k ∈ K, ζ k x = x) → x ∈ W := by
  choose A hA hAD hfg using fg
  haveI : ∀ j, Finite (A j) := hA
  let Ka : P → Subgroup G₂ := fun a => stab ω₂ a ⊓ K₀
  have hKo : ∀ j, ∀ a ∈ A j, IsOpen (Ka a : Set G₂) := fun j a ha => (sm2 j a (hAD j a ha)).inter ho
  have hKc : ∀ j, ∀ a ∈ A j, IsCompact (Ka a : Set G₂) := fun j a ha =>
    hc.inter_left ((stab ω₂ a).isClosed_of_isOpen (sm2 j a (hAD j a ha)))
  haveI : ∀ i : (Σ j, A j), FiniteDimensional ℂ (fixed π (Ka i.2.1)) := fun i =>
    hπ.2 _ (hKo i.1 _ i.2.2) (hKc i.1 _ i.2.2)
  let W : Submodule ℂ Z := ⨆ i : (Σ j, A j), (fixed π (Ka i.2.1)).map (b.flip i.2.1)
  have hA1 : ∀ j, ∀ a ∈ A j, ∀ u, b u a ∈ W := by
    intro j a ha u
    obtain ⟨t, ht⟩ := exists_isAvg (hKc j a ha) (show IsOpen (stab π u : Set G₂) from hπ.1 u)
    have h : b (∑ g ∈ t, π g u) a ∈ W :=
      Submodule.mem_iSup_of_mem ⟨j, a, ha⟩ ⟨_, (mem_fixed _ _ _).2 (ht.fix π u), rfl⟩
    have e : ∀ g ∈ t, b (π g u) a = b u a := fun g hg => by
      conv_lhs => rw [← show ω₂ g a = a from (ht.2.1 g hg).1]
      exact eq2 g u a
    rw [map_sum, LinearMap.sum_apply, Finset.sum_congr rfl e, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at h
    exact (W.smul_mem_iff ht.card_ne).1 h
  refine ⟨W, inferInstance, mem_of_avg ζ hK _ W ?_⟩
  rintro _ ⟨j, u, s, hs, rfl⟩
  refine ⟨stab ω₁ s, sm1 j s hs, fun t ht => ?_⟩
  simp only [eq1, ← map_sum]
  have h := hfg j _ (sum_mem fun g _ => h1 j g s hs) (ht.fix ω₁ s)
  generalize ∑ g ∈ t, ω₁ g s = y at h
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, h, rfl⟩ := hx
    have := eq2 h (π h⁻¹ u) a
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    rw [this]
    exact hA1 j a ha _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [LinearMap.map_smulₛₗ]; exact W.smul_mem _ hx

end GlobalTheory.ThK.CoinvFin

end
