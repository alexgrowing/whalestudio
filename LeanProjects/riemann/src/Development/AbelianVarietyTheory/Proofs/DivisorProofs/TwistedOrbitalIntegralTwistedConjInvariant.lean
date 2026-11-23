import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.TwOrbConj

variable {G : Type} [Group G]

theorem mem_rStab {H : Type} [Group H] (u : H → ℂ) (k : H) : k ∈ GlobalTheory.BCT.rStab u ↔ ∀ x, u (x * k) = u x := Iff.rfl

theorem mem_twCent (θ : G →* G) (δ x : G) : x ∈ GlobalTheory.BCT.twCent θ δ ↔ x * δ = δ * θ x := Iff.rfl

theorem relIndex_map_equiv (φ : G ≃* G) (H L : Subgroup G) :
    (H.map φ.toMonoidHom).relIndex (L.map φ.toMonoidHom) = H.relIndex L := by
  first
  | (rw [Subgroup.map_equiv_eq_comap_symm, Subgroup.relIndex_comap, Subgroup.map_map]; simp)
  | exact Subgroup.relIndex_map_map_of_injective _ _ φ.injective
  | simp [Subgroup.relIndex]

theorem avg_left {H : Type} [Group H] (u : H → ℂ) (a : H) :
    GlobalTheory.BCT.avg (fun h => u (a * h)) = GlobalTheory.BCT.avg u := by
  have hR : GlobalTheory.BCT.rStab (fun h => u (a * h)) = GlobalTheory.BCT.rStab u := by
    ext k
    rw [mem_rStab, mem_rStab]
    constructor
    · intro h x
      simpa [mul_assoc] using h (a⁻¹ * x)
    · intro h x
      simpa [mul_assoc] using h (a * x)
  unfold GlobalTheory.BCT.avg
  rw [hR]
  congr 1
  have hc : ∀ q : H ⧸ GlobalTheory.BCT.rStab u, u (a * q.out) = u (a • q).out := by
    intro q
    obtain ⟨r, hr⟩ := QuotientGroup.mk_out_eq_mul (GlobalTheory.BCT.rStab u) (a * q.out)
    have hq : (a • q) = (QuotientGroup.mk (a * q.out) : H ⧸ GlobalTheory.BCT.rStab u) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, hr]
    exact ((mem_rStab u r).1 r.2 (a * q.out)).symm
  simp_rw [hc]
  exact finsum_comp_equiv (f := fun q : H ⧸ GlobalTheory.BCT.rStab u => u q.out) (MulAction.toPerm a)

theorem map_conj_self (H : Subgroup G) {h : G} (hh : h ∈ H) :
    H.map (MulAut.conj h).toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply]
  constructor
  · intro hx
    have := H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
    simpa [mul_assoc] using this
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh

theorem map_conj_mul (L : Subgroup G) (a b : G) :
    L.map (MulAut.conj (a * b)).toMonoidHom = (L.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem twCent_conj (θ : G →* G) (δ g : G) :
    GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g) = (GlobalTheory.BCT.twCent θ δ).map (MulAut.conj g⁻¹).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  have e : (MulAut.conj g⁻¹).symm x = g * x * g⁻¹ := by simp [MulAut.conj_symm_apply]
  rw [e, mem_twCent, mem_twCent, map_mul, map_mul, map_inv]
  constructor
  · intro h
    calc g * x * g⁻¹ * δ = g * (x * (g⁻¹ * δ * θ g)) * (θ g)⁻¹ := by group
      _ = g * (g⁻¹ * δ * θ g * θ x) * (θ g)⁻¹ := by rw [h]
      _ = δ * (θ g * θ x * (θ g)⁻¹) := by group
  · intro h
    calc x * (g⁻¹ * δ * θ g) = g⁻¹ * (g * x * g⁻¹ * δ) * θ g := by group
      _ = g⁻¹ * (δ * (θ g * θ x * (θ g)⁻¹)) * θ g := by rw [h]
      _ = g⁻¹ * δ * θ g * θ x := by group

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem cptPart_map (c : G) (T : Subgroup G) :
    GlobalTheory.BCT.cptPart (T.map (MulAut.conj c).toMonoidHom) = (GlobalTheory.BCT.cptPart T).map (MulAut.conj c).toMonoidHom := by
  unfold GlobalTheory.BCT.cptPart
  rw [MonoidHom.map_closure]
  congr 1
  let h : G ≃ₜ G := (Homeomorph.mulLeft c).trans (Homeomorph.mulRight c⁻¹)
  have hh : ∀ x, h x = (MulAut.conj c).toMonoidHom x := fun x => by
    simp [h, MulAut.conj_apply]
  have hz : ∀ t, (Subgroup.zpowers ((MulAut.conj c).toMonoidHom t) : Set G) = h '' (Subgroup.zpowers t : Set G) := by
    intro t
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map]
    ext y
    simp only [Set.mem_image, hh]
  have hk : ∀ t, IsCompact (closure (Subgroup.zpowers ((MulAut.conj c).toMonoidHom t) : Set G)) ↔
      IsCompact (closure (Subgroup.zpowers t : Set G)) := by
    intro t
    rw [hz, ← Homeomorph.image_closure, Homeomorph.isCompact_image]
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hc⟩
    exact ⟨t, ⟨ht, (hk t).1 hc⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, (hk t).2 hc⟩

theorem relIndex_conj (c : G) (T T' L L' : Subgroup G) (hT : T' = T.map (MulAut.conj c).toMonoidHom)
    (hL : L' = L.map (MulAut.conj c).toMonoidHom) :
    (T' ⊓ L').relIndex (GlobalTheory.BCT.cptPart T') = (T ⊓ L).relIndex (GlobalTheory.BCT.cptPart T) := by
  subst hT hL
  rw [← Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective, cptPart_map, relIndex_map_equiv]

def summand (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G) : ℂ :=
  (((GlobalTheory.BCT.twCent θ δ ⊓ K.map (MulAut.conj y).toMonoidHom).relIndex (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℕ) : ℂ) *
    GlobalTheory.BCT.avg fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))

theorem twOrb_eq (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) :
    GlobalTheory.BCT.twOrb θ K δ f = ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
      summand θ K δ f (Quotient.out q) := rfl

theorem summand_rep (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G) {t k : G}
    (ht : t ∈ GlobalTheory.BCT.twCent θ δ) (hk : k ∈ K) : summand θ K δ f (t * y * k) = summand θ K δ f y := by
  unfold summand
  congr 1
  · exact congrArg (fun n : ℕ => (n : ℂ)) (relIndex_conj t _ _ _ _ (map_conj_self _ ht).symm
      (by rw [map_conj_mul, map_conj_mul, map_conj_self K hk]))
  · have hd : t⁻¹ * δ * θ t = δ := by
      rw [mul_assoc, ← (mem_twCent θ δ t).1 ht, inv_mul_cancel_left]
    have hfun : (fun k' : K => f ((t * y * k * k')⁻¹ * δ * θ (t * y * k * k'))) =
        fun k' : K => (fun k'' : K => f ((y * k'')⁻¹ * δ * θ (y * k''))) (⟨k, hk⟩ * k') := by
      funext k'
      congr 1
      simp only [Subgroup.coe_mul]
      calc (t * y * k * ↑k')⁻¹ * δ * θ (t * y * k * ↑k')
          = (y * (k * ↑k'))⁻¹ * (t⁻¹ * δ * θ t) * θ (y * (k * ↑k')) := by
            simp only [map_mul, _root_.mul_inv_rev]; group
        _ = (y * (k * ↑k'))⁻¹ * δ * θ (y * (k * ↑k')) := by rw [hd]
    rw [hfun]
    exact avg_left (fun k'' : K => f ((y * k'')⁻¹ * δ * θ (y * k''))) ⟨k, hk⟩

theorem summand_twist (θ : G →* G) (K : Subgroup G) (δ g : G) (f : G → ℂ) (x : G) :
    summand θ K (g⁻¹ * δ * θ g) f x = summand θ K δ f (g * x) := by
  unfold summand
  congr 1
  · exact congrArg (fun n : ℕ => (n : ℂ)) (relIndex_conj g⁻¹ _ _ _ _ (twCent_conj θ δ g)
      (by rw [← map_conj_mul, inv_mul_cancel_left]))
  · congr 1
    funext k
    congr 1
    simp only [map_mul, _root_.mul_inv_rev]
    group

def dcEquiv (θ : G →* G) (K : Subgroup G) (δ g : G) :
    DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g) : Set G) (K : Set G) ≃
      DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G) where
  toFun q := DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q)
  invFun q := DoubleCoset.mk (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) K (g⁻¹ * Quotient.out q)
  left_inv q := by
    obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1
      (DoubleCoset.out_eq' (GlobalTheory.BCT.twCent θ δ) K (DoubleCoset.mk _ K (g * Quotient.out q))).symm
    show DoubleCoset.mk _ K (g⁻¹ * Quotient.out (DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q))) = q
    rw [he]
    conv_rhs => rw [← DoubleCoset.out_eq' (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) K q]
    rw [DoubleCoset.eq]
    refine ⟨g⁻¹ * t⁻¹ * g, ?_, k⁻¹, K.inv_mem hk, by group⟩
    rw [twCent_conj]
    exact ⟨t⁻¹, (GlobalTheory.BCT.twCent θ δ).inv_mem ht, by simp [MulAut.conj_apply]⟩
  right_inv q := by
    obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1
      (DoubleCoset.out_eq' (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) K (DoubleCoset.mk _ K (g⁻¹ * Quotient.out q))).symm
    show DoubleCoset.mk _ K (g * Quotient.out (DoubleCoset.mk (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) K
      (g⁻¹ * Quotient.out q))) = q
    rw [he]
    conv_rhs => rw [← DoubleCoset.out_eq' (GlobalTheory.BCT.twCent θ δ) K q]
    rw [DoubleCoset.eq]
    rw [twCent_conj] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    refine ⟨s⁻¹, (GlobalTheory.BCT.twCent θ δ).inv_mem hs, k⁻¹, K.inv_mem hk, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end GlobalTheory.TwOrbConj

namespace GlobalTheory.TwOrbConj

theorem twOrb_twConj : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G)
    (δ g : G) (f : G → ℂ), (∀ x : G, (GlobalTheory.BCT.rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0) →
    GlobalTheory.BCT.twOrb θ K (g⁻¹ * δ * θ g) f = GlobalTheory.BCT.twOrb θ K δ f := by
  intro G _ _ _ θ K δ g f _
  rw [twOrb_eq, twOrb_eq]
  calc ∑ᶠ q, summand θ K (g⁻¹ * δ * θ g) f (Quotient.out q)
      = ∑ᶠ q, summand θ K δ f (Quotient.out (dcEquiv θ K δ g q)) := by
        refine finsum_congr fun q => ?_
        rw [summand_twist]
        obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1
          (DoubleCoset.out_eq' (GlobalTheory.BCT.twCent θ δ) K (DoubleCoset.mk _ K (g * Quotient.out q))).symm
        show _ = summand θ K δ f (Quotient.out (DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q)))
        rw [he, summand_rep θ K δ f _ ht hk]
    _ = ∑ᶠ q, summand θ K δ f (Quotient.out q) :=
        finsum_comp_equiv (f := fun q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G) =>
          summand θ K δ f (Quotient.out q)) (dcEquiv θ K δ g)

end GlobalTheory.TwOrbConj
