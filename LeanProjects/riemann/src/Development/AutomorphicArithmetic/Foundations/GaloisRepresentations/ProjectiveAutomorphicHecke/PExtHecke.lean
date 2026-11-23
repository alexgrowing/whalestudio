import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap
open Module
universe u v

namespace UpperTheory.Gal.CertificateRingHomMap.ExtensionHeckeOperators

open GlobalTheory.LKDef.HeckeTraceForms

variable {H A : Type} [Group H] [Group A]

private theorem finsum_comp_inj {α β M : Type*} [AddCommMonoid M] {m : α → β}
    (hm : Function.Injective m) (f : β → M) (hs : Function.support f ⊆ Set.range m) :
    ∑ᶠ b, f b = ∑ᶠ a, f (m a) := by
  rw [← finsum_mem_range hm, ← finsum_mem_inter_support, Set.inter_eq_right.2 hs, finsum_mem_support]

private theorem mk_injective (c : H →* A) (K : Subgroup H) {w : H} (hw : ∀ g, w * g = g * w) :
    Function.Injective (fun q : c.ker ⧸ K.subgroupOf c.ker =>
      (QuotientGroup.mk ((q.out : H) * w) : H ⧸ K)) := by
  intro a b hab
  have h1 : ((a.out : H) * w)⁻¹ * ((b.out : H) * w) ∈ K := QuotientGroup.eq.1 hab
  have e : ((a.out : H) * w)⁻¹ * ((b.out : H) * w) = (a.out : H)⁻¹ * (b.out : H) := by
    rw [← hw (a.out : H), ← hw (b.out : H)]; group
  rw [e] at h1
  have h2 : (a.out)⁻¹ * b.out ∈ K.subgroupOf c.ker := Subgroup.mem_subgroupOf.2 (by simpa using h1)
  calc a = QuotientGroup.mk a.out := (QuotientGroup.out_eq' a).symm
    _ = QuotientGroup.mk b.out := QuotientGroup.eq.2 h2
    _ = b := QuotientGroup.out_eq' b

private theorem out_inv {X : Type*} (K : Subgroup H) {G : H → X} (hG : ∀ k ∈ K, ∀ g, G (g * k) = G g)
    (x : H) : G ((QuotientGroup.mk x : H ⧸ K).out) = G x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hk]; exact hG k k.2 x

private theorem mem_range_mk (c : H →* A) (K : Subgroup H) {w : H} (hw : ∀ g, w * g = g * w) {F : H → ℂ}
    (hsup : ∀ g, F g ≠ 0 → ∃ u k, c u = 1 ∧ k ∈ K ∧ g = u * w * k) (h : H ⧸ K) (hh : F h.out ≠ 0) :
    h ∈ Set.range (fun q : c.ker ⧸ K.subgroupOf c.ker =>
      (QuotientGroup.mk ((q.out : H) * w) : H ⧸ K)) := by
  obtain ⟨u, k, hu, hk, e⟩ := hsup _ hh
  have huk : u ∈ c.ker := MonoidHom.mem_ker.2 hu
  obtain ⟨k', hk'⟩ := QuotientGroup.mk_out_eq_mul (K.subgroupOf c.ker) (⟨u, huk⟩ : c.ker)
  refine ⟨QuotientGroup.mk ⟨u, huk⟩, ?_⟩
  have e1 : (((QuotientGroup.mk ⟨u, huk⟩ : c.ker ⧸ K.subgroupOf c.ker).out : c.ker) : H)
      = u * ((k' : c.ker) : H) := by
    rw [hk']; rfl
  have e2 : h = (QuotientGroup.mk (u * w) : H ⧸ K) :=
    calc h = QuotientGroup.mk h.out := (QuotientGroup.out_eq' h).symm
      _ = QuotientGroup.mk (u * w * k) := by rw [← e]
      _ = QuotientGroup.mk (u * w) := QuotientGroup.mk_mul_of_mem _ hk
  have e3 : u * ((k' : c.ker) : H) * w = u * w * ((k' : c.ker) : H) := by
    rw [mul_assoc, ← hw, mul_assoc]
  show (QuotientGroup.mk (((QuotientGroup.mk ⟨u, huk⟩ : c.ker ⧸ K.subgroupOf c.ker).out : H) * w) : H ⧸ K) = h
  rw [e1, e3, e2]
  exact QuotientGroup.mk_mul_of_mem _ (Subgroup.mem_subgroupOf.1 k'.2)

private theorem hecke_eq {V : Type} [AddCommGroup V] [Module ℂ V] (c : H →* A) (K : Subgroup H) {w : H}
    (hw : ∀ g, w * g = g * w) {F : H → ℂ} (hFK : ∀ k ∈ K, ∀ g, F (g * k) = F g)
    (hsup : ∀ g, F g ≠ 0 → ∃ u k, c u = 1 ∧ k ∈ K ∧ g = u * w * k)
    (Φ : H → V) (hΦ : ∀ k ∈ K, ∀ g, Φ (g * k) = Φ g) (g : H) :
    ∑ᶠ h : H ⧸ K, F h.out • Φ (g * h.out) =
      ∑ᶠ q : c.ker ⧸ K.subgroupOf c.ker, F ((q.out : H) * w) • Φ (g * ((q.out : H) * w)) := by
  rw [finsum_comp_inj (mk_injective c K hw) (fun h : H ⧸ K => F h.out • Φ (g * h.out))]
  · refine finsum_congr fun q => ?_
    have hG : ∀ k ∈ K, ∀ x, Φ (g * (x * k)) = Φ (g * x) := fun k hk x => by
      rw [← mul_assoc, hΦ k hk]
    show F (QuotientGroup.mk ((q.out : H) * w) : H ⧸ K).out •
        Φ (g * (QuotientGroup.mk ((q.out : H) * w) : H ⧸ K).out) = _
    rw [out_inv K hFK, out_inv K (G := fun x => Φ (g * x)) hG]
  · intro h hh
    refine mem_range_mk c K hw hsup h fun h0 => hh ?_
    simp [h0]

private theorem finite_supp (c : H →* A) (K : Subgroup H) {w : H} (hw : ∀ g, w * g = g * w) {F : H → ℂ}
    (hFK : ∀ k ∈ K, ∀ g, F (g * k) = F g) (hfin : Set.Finite {h : H ⧸ K | F h.out ≠ 0}) :
    Set.Finite {q : c.ker ⧸ K.subgroupOf c.ker | F ((q.out : H) * w) ≠ 0} := by
  refine (hfin.preimage (mk_injective c K hw).injOn).subset fun q hq => ?_
  show F (QuotientGroup.mk ((q.out : H) * w) : H ⧸ K).out ≠ 0
  rw [out_inv K hFK]
  exact hq

private theorem exists_r {V : Type} [AddCommGroup V] [Module ℂ V] (c : H →* A) (K : Subgroup H) {w : H}
    (hw : ∀ g, w * g = g * w) {F : H → ℂ} (hFK : ∀ k ∈ K, ∀ g, F (g * k) = F g)
    (hfin : Set.Finite {h : H ⧸ K | F h.out ≠ 0}) :
    ∃ r : H →₀ ℂ, (∀ u ∈ r.support, c u = 1) ∧ ∀ (Ψ : H → V) (g : H),
      rop r Ψ g = ∑ᶠ q : c.ker ⧸ K.subgroupOf c.ker, F ((q.out : H) * w) • Ψ (g * (q.out : H)) := by
  classical
  have hs := finite_supp c K hw hFK hfin
  refine ⟨∑ q ∈ hs.toFinset, Finsupp.single (q.out : H) (F ((q.out : H) * w)), fun u hu => ?_,
    fun Ψ g => ?_⟩
  · obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hu)
    have : u = (q.out : H) := by simpa using Finsupp.support_single_subset hq
    rw [this]
    exact MonoidHom.mem_ker.1 q.out.2
  · unfold rop
    rw [← Finsupp.sum_finset_sum_index (h := fun u (a : ℂ) => a • Ψ (g * u)) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _)]
    rw [finsum_eq_sum_of_support_subset (s := hs.toFinset)]
    · refine Finset.sum_congr rfl fun q _ => ?_
      exact Finsupp.sum_single_index (zero_smul _ _)
    · intro q hq
      have : F ((q.out : H) * w) ≠ 0 := fun h0 => hq (by simp [h0])
      simpa using this

end UpperTheory.Gal.CertificateRingHomMap.ExtensionHeckeOperators

open UpperTheory.Gal.CertificateRingHomMap.ExtensionHeckeOperators GlobalTheory.LKDef.HeckeTraceForms in
theorem UpperTheory.Gal.CertificateRingHomMap.pExtHecke_holds :
    UpperTheory.Gal.CertificateRingHomMap.ExtEig → UpperTheory.Gal.CertificateRingHomMap.ExtHecke := by
  intro hE Γ H A Z V _ _ _ _ _ _ ι K ξ _ c ζ hζ φ hφ hne J F z T θ hT hFK hfin hsup hθ
  have hw : ∀ j, ∀ g, ζ (z j) * g = g * ζ (z j) := fun j => hζ (z j)
  have mem : ∀ Ψ : H → V, Ψ ∈ forms ι K ξ ↔
      ((∀ γ g, Ψ (ι γ * g) = ξ γ (Ψ g)) ∧ ∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) := fun _ => Iff.rfl
  have hFK' : ∀ j, ∀ k ∈ K, ∀ g, F j (g * k) = F j g := hFK
  choose r hr1 hr2 using fun j => exists_r (V := V) c K (hw j) (hFK' j) (hfin j)
  have hT' : ∀ j (Ψ : forms ι K ξ) g, (T j Ψ : H → V) g = rop (r j) (Ψ : H → V) (g * ζ (z j)) := by
    intro j Ψ g
    rw [hT j Ψ g, hecke_eq c K (hw j) (hFK' j) (hsup j) (Ψ : H → V) ((mem _).1 Ψ.2).2, hr2]
    refine finsum_congr fun q => ?_
    rw [mul_assoc g (ζ (z j)), hw j]
  have hpres : ∀ j, ∀ Φ ∈ forms ι K ξ, rop (r j) Φ ∈ forms ι K ξ := by
    intro j Φ hΦ
    have e : ∀ g, rop (r j) Φ g = (T j ⟨Φ, hΦ⟩ : H → V) (g * (ζ (z j))⁻¹) := by
      intro g
      rw [hT']
      simp
    have hf := (mem _).1 (T j ⟨Φ, hΦ⟩).2
    refine (mem _).2 ⟨fun γ g => ?_, fun k hk g => ?_⟩
    · rw [e, e, mul_assoc]
      exact hf.1 γ _
    · have hc : (ζ (z j))⁻¹ * k = k * (ζ (z j))⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hw j k, mul_inv_cancel_right]
      rw [e, e, mul_assoc, ← hc, ← mul_assoc]
      exact hf.2 k hk _
  obtain ⟨Φ, hΦ, hne', hev, ψ, hψ⟩ := hE Γ H A Z V ι K ξ c ζ hζ φ hφ hne J r θ hr1 hpres
    (fun j u hu => by rw [hr2]; exact hθ j u hu)
  refine ⟨⟨Φ, hΦ⟩, fun h => hne' (congrArg Subtype.val h), ψ, hψ, fun j => ?_⟩
  apply Subtype.ext
  funext g
  rw [hT', hev j]
  show θ j • Φ (g * ζ (z j)) = (θ j * (ψ (z j) : ℂ)) • Φ g
  rw [hψ.1, mul_smul]
