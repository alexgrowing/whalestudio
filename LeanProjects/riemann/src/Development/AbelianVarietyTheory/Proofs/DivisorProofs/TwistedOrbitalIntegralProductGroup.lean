import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageLinearTranslateConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageProdMulEqMulStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.BCT.OrbProd

theorem relIndex_prod_prod {G G' : Type} [Group G] [Group G'] (H K : Subgroup G) (H' K' : Subgroup G') :
    (H.prod H').relIndex (K.prod K') = H.relIndex K * H'.relIndex K' := by
  unfold Subgroup.relIndex
  rw [← Subgroup.index_prod,
    ← Subgroup.index_comap_of_surjective ((H.subgroupOf K).prod (H'.subgroupOf K'))
      (f := (Subgroup.prodEquiv K K').toMonoidHom) (Subgroup.prodEquiv K K').surjective]
  congr 1

theorem prod_inf_prod {G G' : Type} [Group G] [Group G'] (H K : Subgroup G) (H' K' : Subgroup G') :
    H.prod H' ⊓ K.prod K' = (H ⊓ K).prod (H' ⊓ K') := by
  ext ⟨a, b⟩
  simp only [Subgroup.mem_inf, Subgroup.mem_prod]
  tauto

theorem twCent_prod {G G' : Type} [Group G] [Group G'] (θ : G →* G) (θ' : G' →* G') (δ : G) (δ' : G') :
    twCent (θ.prodMap θ') (δ, δ') = (twCent θ δ).prod (twCent θ' δ') := by
  ext ⟨g, g'⟩
  rw [Subgroup.mem_prod]
  change (g, g') * (δ, δ') = (δ, δ') * (θ.prodMap θ') (g, g') ↔ g * δ = δ * θ g ∧ g' * δ' = δ' * θ' g'
  simp [Prod.ext_iff]

theorem map_conj_prod {G G' : Type} [Group G] [Group G'] (K : Subgroup G) (K' : Subgroup G') (x : G) (x' : G') :
    (K.prod K').map (MulAut.conj (x, x')).toMonoidHom =
      (K.map (MulAut.conj x).toMonoidHom).prod (K'.map (MulAut.conj x').toMonoidHom) := by
  ext ⟨a, b⟩
  simp only [Subgroup.mem_map, Subgroup.mem_prod, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Prod.exists]
  constructor
  · rintro ⟨k, k', ⟨hk, hk'⟩, h⟩
    simp only [Prod.ext_iff, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv] at h
    exact ⟨⟨k, hk, h.1⟩, ⟨k', hk', h.2⟩⟩
  · rintro ⟨⟨k, hk, h⟩, ⟨k', hk', h'⟩⟩
    exact ⟨k, k', ⟨hk, hk'⟩, by simp [Prod.ext_iff, h, h']⟩

theorem map_conj_self {G : Type} [Group G] (H : Subgroup G) {h : G} (hh : h ∈ H) :
    H.map (MulAut.conj h).toMonoidHom = H := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact H.mul_mem (H.mul_mem hh ha) (H.inv_mem hh)
  · intro hy
    exact ⟨h⁻¹ * y * h, H.mul_mem (H.mul_mem (H.inv_mem hh) hy) hh, by group⟩

section Top

variable {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [T2Space H]

theorem cpt_map (f : G →* H) (hf : Continuous f) {t : G}
    (h : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    IsCompact (closure (Subgroup.zpowers (f t) : Set H)) := by
  have hK := h.image hf
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  intro y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ⟨t ^ n, subset_closure (Subgroup.zpow_mem_zpowers t n), map_zpow f t n⟩

end Top

end GlobalTheory.BCT.OrbProd

namespace GlobalTheory.BCT.OrbProd

section Top2

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G']

theorem cptPart_prod (T : Subgroup G) (T' : Subgroup G') :
    cptPart (T.prod T') = (cptPart T).prod (cptPart T') := by
  apply le_antisymm
  · rw [cptPart, Subgroup.closure_le]
    rintro ⟨t, t'⟩ ⟨ht, hc⟩
    rw [Subgroup.mem_prod] at ht
    rw [SetLike.mem_coe, Subgroup.mem_prod]
    refine ⟨Subgroup.subset_closure ⟨ht.1, ?_⟩, Subgroup.subset_closure ⟨ht.2, ?_⟩⟩
    · have h := cpt_map (MonoidHom.fst G G') continuous_fst hc
      simpa only [MonoidHom.coe_fst] using h
    · have h := cpt_map (MonoidHom.snd G G') continuous_snd hc
      simpa only [MonoidHom.coe_snd] using h
  · have h1 : (cptPart T).map (MonoidHom.inl G G') ≤ cptPart (T.prod T') := by
      rw [cptPart, MonoidHom.map_closure, cptPart, Subgroup.closure_le]
      rintro _ ⟨t, ⟨ht, hc⟩, rfl⟩
      refine Subgroup.subset_closure ⟨Subgroup.mem_prod.mpr ⟨ht, T'.one_mem⟩, ?_⟩
      exact cpt_map (MonoidHom.inl G G') (by show Continuous fun x : G => (x, (1 : G')); fun_prop) hc
    have h2 : (cptPart T').map (MonoidHom.inr G G') ≤ cptPart (T.prod T') := by
      rw [cptPart, MonoidHom.map_closure, cptPart, Subgroup.closure_le]
      rintro _ ⟨t, ⟨ht, hc⟩, rfl⟩
      refine Subgroup.subset_closure ⟨Subgroup.mem_prod.mpr ⟨T.one_mem, ht⟩, ?_⟩
      exact cpt_map (MonoidHom.inr G G') (by show Continuous fun x : G' => ((1 : G), x); fun_prop) hc
    rintro ⟨a, a'⟩ h
    rw [Subgroup.mem_prod] at h
    have e : ((a, a') : G × G') = MonoidHom.inl G G' a * MonoidHom.inr G G' a' := by simp
    rw [e]
    exact (cptPart (T.prod T')).mul_mem (h1 ⟨a, h.1, rfl⟩) (h2 ⟨a', h.2, rfl⟩)

theorem conj_cpt_le (T : Subgroup G) {t : G} (ht : t ∈ T) :
    (cptPart T).map (MulAut.conj t).toMonoidHom ≤ cptPart T := by
  rw [cptPart, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨s, ⟨hs, hc⟩, rfl⟩
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact T.mul_mem (T.mul_mem ht hs) (T.inv_mem ht)
  · exact cpt_map (MulAut.conj t).toMonoidHom
      (by show Continuous fun x : G => t * x * t⁻¹; fun_prop) hc

theorem conj_cpt (T : Subgroup G) {t : G} (ht : t ∈ T) :
    (cptPart T).map (MulAut.conj t).toMonoidHom = cptPart T := by
  refine le_antisymm (conj_cpt_le T ht) ?_
  intro y hy
  refine ⟨t⁻¹ * y * t, ?_, by simp [MulAut.conj_apply]; group⟩
  have := conj_cpt_le T (T.inv_mem ht) ⟨y, hy, rfl⟩
  simpa [MulAut.conj_apply] using this

end Top2

end GlobalTheory.BCT.OrbProd

namespace GlobalTheory.BCT.OrbProd

theorem avg_zero {H : Type} [Group H] : avg (fun _ : H => (0 : ℂ)) = 0 := by
  simp [avg]

theorem mem_rStab_comp {H H' : Type} [Group H] [Group H'] (e : H ≃* H') (u : H' → ℂ) (k : H) :
    k ∈ rStab (u ∘ e) ↔ e k ∈ rStab u := by
  change (∀ x, u (e (x * k)) = u (e x)) ↔ ∀ y, u (y * e k) = u y
  constructor
  · intro h y
    have := h (e.symm y)
    simpa using this
  · intro h x
    rw [map_mul]
    exact h (e x)

theorem avg_comp_equiv {H H' : Type} [Group H] [Group H'] (e : H ≃* H') (u : H' → ℂ) :
    avg (u ∘ e) = avg u := by
  have hS : rStab (u ∘ e) = (rStab u).comap e.toMonoidHom := by
    ext k
    exact mem_rStab_comp e u k
  have hi : (rStab (u ∘ e)).index = (rStab u).index := by
    rw [hS, Subgroup.index_comap_of_surjective _ e.surjective]
  let E : H ⧸ rStab (u ∘ e) ≃ H' ⧸ rStab u :=
    Quotient.congr e.toEquiv (fun a b => by
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, mem_rStab_comp]
      simp)
  unfold avg
  rw [hi, ← finsum_comp_equiv E]
  congr 1
  apply finsum_congr
  intro q
  induction q using QuotientGroup.induction_on with
  | H a =>
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (rStab (u ∘ e)) a
    have hE : E (a : H ⧸ rStab (u ∘ e)) = ((e a : H') : H' ⧸ rStab u) := rfl
    obtain ⟨h', hh'⟩ := QuotientGroup.mk_out_eq_mul (rStab u) (e a)
    rw [hE, hh, hh']
    have h1 : (u ∘ e) (a * h) = (u ∘ e) a := h.2 a
    have h2 : u (e a * h') = u (e a) := h'.2 (e a)
    rw [h1, h2]
    rfl

end GlobalTheory.BCT.OrbProd

namespace GlobalTheory.BCT.OrbProd

section Orb

variable {G : Type} [Group G]

def orbTerm [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (x : G) : ℂ :=
  (((twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) *
      avg fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))

theorem twOrb_eq [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) :
    twOrb θ K δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G),
      orbTerm θ K δ f (Quotient.out q) := rfl

theorem map_conj_mul_three_subgroup_of_mem (K : Subgroup G) {k : G} (hk : k ∈ K) (t x : G) :
    K.map (MulAut.conj (t * x * k)).toMonoidHom =
      (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨x * (k * a * k⁻¹) * x⁻¹, ⟨k * a * k⁻¹, K.mul_mem (K.mul_mem hk ha) (K.inv_mem hk), rfl⟩, by group⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨k⁻¹ * a * k, K.mul_mem (K.mul_mem (K.inv_mem hk) ha) hk, by group⟩

theorem fun_inv (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) {t k : G} (ht : t ∈ twCent θ δ)
    (hk : k ∈ K) (x : G) :
    (fun k1 : K => f ((t * x * k * k1)⁻¹ * δ * θ (t * x * k * k1))) =
      fun k1 : K => (fun k2 : K => f ((x * k2)⁻¹ * δ * θ (x * k2))) (⟨k, hk⟩ * k1) := by
  funext k1
  have ht0 : t * δ = δ * θ t := ht
  have ht' : θ t = δ⁻¹ * (t * δ) := eq_inv_mul_of_mul_eq ht0.symm
  simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, ht']
  congr 1
  group

variable [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem orbTerm_inv (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ)
    (hf : ∀ x : G, (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0)
    {t k : G} (ht : t ∈ twCent θ δ) (hk : k ∈ K) (x : G) :
    orbTerm θ K δ f (t * x * k) = orbTerm θ K δ f x := by
  unfold orbTerm
  have e1 : twCent θ δ ⊓ (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      (twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective, map_conj_self _ ht]
  have e2 := Subgroup.relIndex_map_map_of_injective (twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom)
    (cptPart (twCent θ δ)) (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective
  rw [conj_cpt _ ht] at e2
  rw [map_conj_mul_three_subgroup_of_mem K hk, e1, e2, fun_inv θ K δ f ht hk x]
  congr 1
  exact (GlobalTheory.T.subgroupAverage_linear_translate_const K (fun k2 : K => f ((x * k2)⁻¹ * δ * θ (x * k2))) (fun k2 : K => f ((x * k2)⁻¹ * δ * θ (x * k2))) 0 ⟨k, hk⟩ (hf x) (hf x)).2.2.1

end Orb

end GlobalTheory.BCT.OrbProd

namespace GlobalTheory.BCT.OrbProd

section Prod

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G']

theorem orbTerm_prod (θ : G →* G) (θ' : G' →* G') (K : Subgroup G) (K' : Subgroup G') (δ : G) (δ' : G')
    (f : G → ℂ) (f' : G' → ℂ) (x : G) (x' : G')
    (hf : (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0)
    (hf' : (rStab fun k : K' => f' ((x' * k)⁻¹ * δ' * θ' (x' * k))).index ≠ 0) :
    orbTerm (θ.prodMap θ') (K.prod K') (δ, δ') (fun y => f y.1 * f' y.2) (x, x') =
      orbTerm θ K δ f x * orbTerm θ' K' δ' f' x' := by
  unfold orbTerm
  rw [twCent_prod, map_conj_prod, prod_inf_prod, cptPart_prod, relIndex_prod_prod, Nat.cast_mul,
    mul_mul_mul_comm]
  congr 1
  have hA := GlobalTheory.T.subgroupAverage_prod_mul_eq_mul K K' (fun k : K => f ((x * k)⁻¹ * δ * θ (x * k)))
    (fun k : K' => f' ((x' * k)⁻¹ * δ' * θ' (x' * k))) hf hf'
  rw [← hA, ← avg_comp_equiv (Subgroup.prodEquiv K K')]
  rfl

end Prod

end GlobalTheory.BCT.OrbProd

namespace GlobalTheory.BCT.OrbProd

section DC

variable {G G' : Type} [Group G] [Group G']

def dcPair (T K : Subgroup G) (T' K' : Subgroup G') :
    DoubleCoset.Quotient (T : Set G) (K : Set G) × DoubleCoset.Quotient (T' : Set G') (K' : Set G') →
      DoubleCoset.Quotient ((T.prod T' : Subgroup (G × G')) : Set (G × G'))
        ((K.prod K' : Subgroup (G × G')) : Set (G × G')) :=
  fun z => DoubleCoset.mk (T.prod T') (K.prod K') (Quotient.out z.1, Quotient.out z.2)

theorem dcPair_bij (T K : Subgroup G) (T' K' : Subgroup G') : Function.Bijective (dcPair T K T' K') := by
  constructor
  · rintro ⟨q1, q1'⟩ ⟨q2, q2'⟩ h
    obtain ⟨a, ha, b, hb, e⟩ := (DoubleCoset.eq _ _ _ _).mp h
    rw [Subgroup.mem_prod] at ha hb
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only [Prod.fst_mul, Prod.snd_mul] at e1 e2
    refine Prod.ext ?_ ?_
    · calc q1 = DoubleCoset.mk T K (Quotient.out q1) := (DoubleCoset.out_eq' T K q1).symm
        _ = DoubleCoset.mk T K (Quotient.out q2) := (DoubleCoset.eq _ _ _ _).mpr ⟨a.1, ha.1, b.1, hb.1, e1⟩
        _ = q2 := DoubleCoset.out_eq' T K q2
    · calc q1' = DoubleCoset.mk T' K' (Quotient.out q1') := (DoubleCoset.out_eq' T' K' q1').symm
        _ = DoubleCoset.mk T' K' (Quotient.out q2') := (DoubleCoset.eq _ _ _ _).mpr ⟨a.2, ha.2, b.2, hb.2, e2⟩
        _ = q2' := DoubleCoset.out_eq' T' K' q2'
  · intro p
    obtain ⟨a, b, ha, hb, e⟩ := DoubleCoset.mk_out_eq_mul T K (Quotient.out p).1
    obtain ⟨a', b', ha', hb', e'⟩ := DoubleCoset.mk_out_eq_mul T' K' (Quotient.out p).2
    refine ⟨(DoubleCoset.mk T K (Quotient.out p).1, DoubleCoset.mk T' K' (Quotient.out p).2), ?_⟩
    unfold dcPair
    rw [e, e']
    conv_rhs => rw [← DoubleCoset.out_eq' (T.prod T') (K.prod K') p]
    rw [DoubleCoset.eq]
    refine ⟨(a, a')⁻¹, (T.prod T').inv_mem (Subgroup.mem_prod.mpr ⟨ha, ha'⟩),
      (b, b')⁻¹, (K.prod K').inv_mem (Subgroup.mem_prod.mpr ⟨hb, hb'⟩), ?_⟩
    refine Prod.ext ?_ ?_ <;> simp [mul_assoc]

end DC

theorem finsum_prod_mul_of_finite {α β : Type} (u : α → ℂ) (v : β → ℂ) (hu : (Function.support u).Finite)
    (hv : (Function.support v).Finite) :
    ∑ᶠ z : α × β, u z.1 * v z.2 = (∑ᶠ a, u a) * ∑ᶠ b, v b := by
  rw [finsum_eq_sum_of_support_subset u (s := hu.toFinset) (by simp),
    finsum_eq_sum_of_support_subset v (s := hv.toFinset) (by simp),
    finsum_eq_sum_of_support_subset _ (s := hu.toFinset ×ˢ hv.toFinset) ?_, Finset.sum_mul_sum,
    Finset.sum_product]
  intro z hz
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hz
  simp [hz.1, hz.2]

end GlobalTheory.BCT.OrbProd

namespace GlobalTheory.BCT.OrbProd

theorem support_sub {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G)
    (f : G → ℂ) :
    Function.support (fun q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G) =>
        orbTerm θ K δ f (Quotient.out q)) ⊆
      {q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G) |
        ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k)) ≠ 0} := by
  intro q hq
  by_contra h
  simp only [Set.mem_setOf_eq, not_exists, not_and, not_not] at h
  apply hq
  have h0 : (fun k : K => f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k))) = fun _ => 0 :=
    funext fun k => h k k.2
  simp only [orbTerm, h0, avg_zero, mul_zero]

theorem twOrb_prod : ∀ (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G'] (θ : G →* G) (θ' : G' →* G') (K : Subgroup G) (K' : Subgroup G') (δ : G) (δ' : G') (f : G → ℂ) (f' : G' → ℂ), (∀ x : G, (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0) → (∀ x : G', (rStab fun k : K' => f' ((x * k)⁻¹ * δ' * θ' (x * k))).index ≠ 0) → {q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G) | ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k)) ≠ 0}.Finite → {q : DoubleCoset.Quotient (twCent θ' δ' : Set G') (K' : Set G') | ∃ k ∈ K', f' ((Quotient.out q * k)⁻¹ * δ' * θ' (Quotient.out q * k)) ≠ 0}.Finite → twOrb (θ.prodMap θ') (K.prod K') (δ, δ') (fun y => f y.1 * f' y.2) = twOrb θ K δ f * twOrb θ' K' δ' f' := by
  intro G G' _ _ _ _ _ _ _ _ θ θ' K K' δ δ' f f' hf hf' hfin hfin'
  rw [twOrb_eq, twOrb_eq, twOrb_eq, twCent_prod,
    ← finsum_comp_equiv (Equiv.ofBijective _ (dcPair_bij (twCent θ δ) K (twCent θ' δ') K'))]
  have hz : ∀ z, orbTerm (θ.prodMap θ') (K.prod K') (δ, δ') (fun y => f y.1 * f' y.2)
      (Quotient.out (Equiv.ofBijective _ (dcPair_bij (twCent θ δ) K (twCent θ' δ') K') z)) =
      orbTerm θ K δ f (Quotient.out z.1) * orbTerm θ' K' δ' f' (Quotient.out z.2) := by
    intro z
    obtain ⟨a, b, ha, hb, e⟩ := DoubleCoset.mk_out_eq_mul ((twCent θ δ).prod (twCent θ' δ')) (K.prod K')
      (Quotient.out z.1, Quotient.out z.2)
    rw [Subgroup.mem_prod] at ha hb
    have e2 : Quotient.out (Equiv.ofBijective _ (dcPair_bij (twCent θ δ) K (twCent θ' δ') K') z) =
        (a.1 * Quotient.out z.1 * b.1, a.2 * Quotient.out z.2 * b.2) := e
    rw [e2, orbTerm_prod θ θ' K K' δ δ' f f' _ _ (hf _) (hf' _), orbTerm_inv θ K δ f hf ha.1 hb.1,
      orbTerm_inv θ' K' δ' f' hf' ha.2 hb.2]
  rw [finsum_congr hz]
  exact finsum_prod_mul_of_finite _ _ (hfin.subset (support_sub θ K δ f))
    (hfin'.subset (support_sub θ' K' δ' f'))

end GlobalTheory.BCT.OrbProd
