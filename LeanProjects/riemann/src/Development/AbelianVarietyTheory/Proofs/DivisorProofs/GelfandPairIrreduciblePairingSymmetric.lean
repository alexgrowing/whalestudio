import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DixmierCommutantScalar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandPairSphericalVectorUnique

open GlobalTheory.GelfandLine
open GlobalTheory.PRep (fixed)

namespace GlobalTheory.GelfandCount

variable {G : Type} [Group G]

theorem stabSub_subgroupOf_eq (K : Subgroup G) (g : G) :
    (stabSub K g).subgroupOf K = (K.map (MulAut.conj g).toMonoidHom).subgroupOf K := by
  ext ⟨h, hK⟩
  simp only [Subgroup.mem_subgroupOf, mem_stabSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨-, h2⟩
    exact ⟨_, h2, by group⟩
  · rintro ⟨k, hk, rfl⟩
    have e : g⁻¹ * (g * k * g⁻¹) * g = k := by group
    exact ⟨hK, by rw [e]; exact hk⟩

theorem finiteIndex_stabSub (K : Subgroup G) (g : G)
    (h : (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0) :
    ((stabSub K g).subgroupOf K).FiniteIndex := by
  rw [stabSub_subgroupOf_eq]; exact ⟨h⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem avg_mem_span_hecke (K : Subgroup G) [∀ g, Fintype (K ⧸ (stabSub K g).subgroupOf K)]
    (hFI : ∀ g, ((stabSub K g).subgroupOf K).FiniteIndex)
    (ρ : Representation ℂ G V) {x : V} (hx : ∀ k ∈ K, ρ k x = x) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun g : G => ρ g x), ∃ H₀ : Subgroup K,
      H₀.FiniteIndex ∧ ∀ H : Subgroup K, H ≤ H₀ → H.FiniteIndex →
        ∑ᶠ q : K ⧸ H, ρ (q.out : G) w ∈ Submodule.span ℂ (Set.range fun g : G => heckeOp ρ K g x) := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem y h =>
    obtain ⟨g, rfl⟩ := h
    haveI := hFI g
    refine ⟨(stabSub K g).subgroupOf K, inferInstance, fun H hH hHf => ?_⟩
    haveI := hHf
    have key := finsum_quot_le hH (fun y : K => ρ ((y : G) * g) x) (fun y h hh => by
      have hh' : (h : G) ∈ stabSub K g := Subgroup.mem_subgroupOf.1 hh
      have e : ((y * h : K) : G) * g = (y : G) * g * (g⁻¹ * (h : G) * g) := by
        simp only [Subgroup.coe_mul]; group
      show ρ (((y * h : K) : G) * g) x = ρ ((y : G) * g) x
      rw [e, map_mul, Module.End.mul_apply, hx _ hh'.2])
    have hs : ∑ᶠ p : K ⧸ (stabSub K g).subgroupOf K, ρ (((p.out : K) : G) * g) x =
        heckeOp ρ K g x := by
      rw [finsum_eq_sum_of_fintype, heckeOp_apply]
    have e2 : ∀ q : K ⧸ H, ρ (q.out : G) (ρ g x) = ρ ((q.out : G) * g) x := fun q => by
      rw [map_mul, Module.End.mul_apply]
    rw [finsum_congr e2, key, hs]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  | zero => exact ⟨⊤, inferInstance, fun H _ _ => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨H₁, hf₁, h₁⟩ := ha
    obtain ⟨H₂, hf₂, h₂⟩ := hb
    refine ⟨H₁ ⊓ H₂, inferInstance, fun H hH hHf => ?_⟩
    haveI := hHf
    simp only [map_add]
    rw [finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
    exact Submodule.add_mem _ (h₁ H (hH.trans inf_le_left) hHf) (h₂ H (hH.trans inf_le_right) hHf)
  | smul c a _ ha =>
    obtain ⟨H₀, hf, h⟩ := ha
    refine ⟨H₀, hf, fun H hH hHf => ?_⟩
    simp only [map_smul]
    rw [← smul_finsum]
    exact Submodule.smul_mem _ _ (h H hH hHf)

end GlobalTheory.GelfandCount

open GlobalTheory.GelfandLine GlobalTheory.GelfandCount in

theorem GlobalTheory.fixed_line_of_gelfand_countable : ∀ (G : Type) [Group G] (K : Subgroup G), (∀ g : G, (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0) →
    ∀ θ : G → G, (∀ x y, θ (x * y) = θ y * θ x) → (∀ x, θ (θ x) = x) → (∀ g, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), Module.rank ℂ V ≤ Cardinal.aleph0 →
    (∀ N : Submodule ℂ V, (∀ g, ∀ x ∈ N, ρ g x ∈ N) → N = ⊥ ∨ N = ⊤) →
    ∀ x y : V, (∀ k ∈ K, ρ k x = x) → (∀ k ∈ K, ρ k y = y) → x ≠ 0 → ∃ c : ℂ, y = c • x := by
  intro G _ K hrel θ hmul hinv hdc V _ _ ρ hrank hirr x y hx hy hx0
  have hFI : ∀ g, ((stabSub K g).subgroupOf K).FiniteIndex := fun g => finiteIndex_stabSub K g (hrel g)
  haveI : ∀ g, Fintype (K ⧸ (stabSub K g).subgroupOf K) := fun g => by
    haveI := hFI g; exact Fintype.ofFinite _
  have hfix : ∀ g, ∀ v ∈ fixed ρ K, heckeOp ρ K g v ∈ fixed ρ K := fun g v hv =>
    mem_fixed_iff.2 (heckeOp_fixed ρ K g (mem_fixed_iff.1 hv))
  let T : G → Module.End ℂ (fixed ρ K) := fun g => (heckeOp ρ K g).restrict (hfix g)
  have hTc : ∀ a b, Commute (T a) (T b) := fun a b => by
    ext ⟨v, hv⟩
    exact heckeOp_comm ρ K θ hmul hinv hdc a b (mem_fixed_iff.1 hv)
  have hspanV : ∀ z : V, z ≠ 0 → Submodule.span ℂ (Set.range fun g : G => ρ g z) = ⊤ := by
    intro z hz0
    refine (hirr _ ?_).resolve_left ?_
    · intro g v hv
      induction hv using Submodule.span_induction with
      | mem y h =>
        obtain ⟨a, rfl⟩ := h
        exact Submodule.subset_span ⟨g * a, by simp [map_mul]⟩
      | zero => simp
      | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
    · intro h
      have : z ∈ Submodule.span ℂ (Set.range fun g : G => ρ g z) :=
        Submodule.subset_span ⟨1, by simp⟩
      rw [h] at this
      exact hz0 ((Submodule.mem_bot ℂ).1 this)
  have hcover : ∀ z ∈ fixed ρ K, z ≠ 0 → ∀ v ∈ fixed ρ K,
      v ∈ Submodule.span ℂ (Set.range fun g : G => heckeOp ρ K g z) := by
    intro z hz hz0 v hv
    obtain ⟨H₀, hf, hH⟩ := avg_mem_span_hecke K hFI ρ (mem_fixed_iff.1 hz) v
      (hspanV z hz0 ▸ Submodule.mem_top)
    have h1 := hH H₀ le_rfl hf
    haveI := hf
    haveI := Fintype.ofFinite (K ⧸ H₀)
    have e : ∑ᶠ q : K ⧸ H₀, ρ (q.out : G) v = (Fintype.card (K ⧸ H₀) : ℂ) • v := by
      rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl fun q _ => mem_fixed_iff.1 hv _ (q.out).2,
        Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [e] at h1
    exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)).1 h1
  have hirrW : ∀ N : Submodule ℂ (fixed ρ K), (∀ g, ∀ w ∈ N, T g w ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    by_cases h : N = ⊥
    · exact Or.inl h
    right
    obtain ⟨z, hzN, hz0⟩ := (Submodule.ne_bot_iff N).1 h
    rw [eq_top_iff]
    intro v _
    have hv := hcover z z.2 (fun e => hz0 (Subtype.ext e)) v v.2
    have hsub : Submodule.span ℂ (Set.range fun g : G => heckeOp ρ K g (z : V)) ≤
        N.map (fixed ρ K).subtype := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨T g z, hN g z hzN, rfl⟩
    obtain ⟨w, hw, hwv⟩ := hsub hv
    have : w = v := Subtype.ext hwv
    exact this ▸ hw
  have hrankW : Module.rank ℂ (fixed ρ K) ≤ Cardinal.aleph0 := (Submodule.rank_le _).trans hrank
  have hxF : x ∈ fixed ρ K := mem_fixed_iff.2 hx
  have hscal : ∀ g, heckeOp ρ K g x ∈ ℂ ∙ x := by
    intro g
    obtain ⟨c, hc⟩ := GlobalTheory.dixmier_commutant_scalar G (fixed ρ K) T hrankW hirrW (T g)
      (fun i => (hTc g i).eq)
    have h2 : T g ⟨x, hxF⟩ = c • ⟨x, hxF⟩ := by rw [hc]; rfl
    have h3 : heckeOp ρ K g x = c • x := congrArg Subtype.val h2
    rw [h3]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  have hyS := hcover x hxF hx0 y (mem_fixed_iff.2 hy)
  have hle : Submodule.span ℂ (Set.range fun g : G => heckeOp ρ K g x) ≤ ℂ ∙ x := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hscal g
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hle hyS)
  exact ⟨a, ha.symm⟩
