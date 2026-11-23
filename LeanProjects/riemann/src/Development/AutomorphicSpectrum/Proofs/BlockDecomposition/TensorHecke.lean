import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.TensHkSum

open PositivityTheory.Rg.BcB.F.Tail.PExp

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem extTensor_apply_eq (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (m : G × H) :
    extTensor ρ σ m = TensorProduct.map (ρ m.1) (σ m.2) := by
  rfl

theorem hkE_eq_sum (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ)
    (hs : {q : G ⧸ K | f q.out ≠ 0}.Finite) :
    hkE ρ K f = ∑ q ∈ hs.toFinset, f q.out • ρ q.out := by
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.hkE
  apply finsum_eq_sum_of_support_subset
  intro q hq
  rw [Function.mem_support] at hq
  rw [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
  intro h0
  exact hq (by simp [h0])

theorem map_sum_sum_apply {A B : Type} (s : Finset A) (t : Finset B) (a : A → ℂ) (b : B → ℂ)
    (P : A → Module.End ℂ V) (Q : B → Module.End ℂ W) (v : V ⊗[ℂ] W) :
    TensorProduct.map (∑ i ∈ s, a i • P i) (∑ j ∈ t, b j • Q j) v =
      ∑ p ∈ s ×ˢ t, (a p.1 * b p.2) • TensorProduct.map (P p.1) (Q p.2) v := by
  have hB : ∀ (P' : Module.End ℂ V) (Q' : Module.End ℂ W),
      TensorProduct.map P' Q' v = TensorProduct.mapBilinear (RingHom.id ℂ) V W V W P' Q' v := fun P' Q' => by
    rw [TensorProduct.mapBilinear_apply]
  simp only [hB, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_product,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem bijective_mk_out_prod (K : Subgroup G) (L : Subgroup H) :
    Function.Bijective (fun p : (G ⧸ K) × (H ⧸ L) =>
      (QuotientGroup.mk (p.1.out, p.2.out) : (G × H) ⧸ K.prod L)) := by
  constructor
  · rintro ⟨q1, r1⟩ ⟨q2, r2⟩ h
    simp only at h
    rw [QuotientGroup.eq, Subgroup.mem_prod] at h
    obtain ⟨h1, h2⟩ := h
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv] at h1 h2
    have e1 : (QuotientGroup.mk q1.out : G ⧸ K) = QuotientGroup.mk q2.out := QuotientGroup.eq.mpr h1
    have e2 : (QuotientGroup.mk r1.out : H ⧸ L) = QuotientGroup.mk r2.out := QuotientGroup.eq.mpr h2
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at e1 e2
    rw [e1, e2]
  · intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    refine ⟨((QuotientGroup.mk x.1 : G ⧸ K), (QuotientGroup.mk x.2 : H ⧸ L)), ?_⟩
    simp only
    rw [QuotientGroup.eq, Subgroup.mem_prod]
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
    exact ⟨QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk x.1 : G ⧸ K)),
      QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk x.2 : H ⧸ L))⟩

theorem apply_out_mk {X : Type} (K : Subgroup G) (Φ : G → X) (hΦ : ∀ x, ∀ k ∈ K, Φ (x * k) = Φ x) (x : G) :
    Φ (QuotientGroup.mk x : G ⧸ K).out = Φ x := by
  have hk : x⁻¹ * (QuotientGroup.mk x : G ⧸ K).out ∈ K :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk x : G ⧸ K)).symm
  have e := hΦ x _ hk
  rw [mul_inv_cancel_left] at e
  exact e

theorem tensHk : TensHk := by
  intro G H V W _ _ _ _ _ _ ρ σ K L f e hf he hsf hse v hv
  have hfix : ∀ k ∈ K.prod L, extTensor ρ σ k v = v := by
    intro k hk
    have h1 := hv ⟨k, hk⟩
    simpa using h1
  have hinv : ∀ x : G × H, ∀ k ∈ K.prod L,
      (f (x * k).1 * e (x * k).2) • extTensor ρ σ (x * k) v = (f x.1 * e x.2) • extTensor ρ σ x v := by
    intro x k hk
    have hk' := Subgroup.mem_prod.mp hk
    rw [Prod.fst_mul, Prod.snd_mul, hf _ _ hk'.1, he _ _ hk'.2, map_mul, Module.End.mul_apply, hfix k hk]
  have key : (∑ᶠ q : (G × H) ⧸ K.prod L, (f q.out.1 * e q.out.2) • extTensor ρ σ q.out v)
      = ∑ᶠ p : (G ⧸ K) × (H ⧸ L), (f p.1.out * e p.2.out) • TensorProduct.map (ρ p.1.out) (σ p.2.out) v := by
    rw [← finsum_comp_equiv (Equiv.ofBijective _ (bijective_mk_out_prod K L))]
    apply finsum_congr
    intro p
    rw [Equiv.ofBijective_apply]
    have h2 := apply_out_mk (K.prod L) (fun m : G × H => (f m.1 * e m.2) • extTensor ρ σ m v) hinv
      (p.1.out, p.2.out)
    simp only at h2
    rw [extTensor_apply_eq] at h2
    exact h2
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.hkS
  show (∑ᶠ q : (G × H) ⧸ K.prod L, (f q.out.1 * e q.out.2) • extTensor ρ σ q.out v) = _
  rw [key, hkE_eq_sum ρ K f hsf, hkE_eq_sum σ L e hse, map_sum_sum_apply]
  apply finsum_eq_sum_of_support_subset
  intro p hp
  rw [Function.mem_support] at hp
  rw [Finset.coe_product, Set.mem_prod, Set.Finite.coe_toFinset, Set.Finite.coe_toFinset,
    Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  constructor
  · intro h0
    exact hp (by simp [h0])
  · intro h0
    exact hp (by simp [h0])

end GlobalTheory.CompanionTheory.TensHkSum

end
