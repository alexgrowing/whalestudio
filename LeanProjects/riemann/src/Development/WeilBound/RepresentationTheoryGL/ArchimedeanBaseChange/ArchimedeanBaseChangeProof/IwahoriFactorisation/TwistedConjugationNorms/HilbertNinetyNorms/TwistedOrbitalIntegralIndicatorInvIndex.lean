import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.RelIndexNeZeroOfCompactOpen

open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

section Generic

variable {G : Type} [Group G] [TopologicalSpace G]

theorem finsum_const_mul_eq {α : Type*} (c : ℂ) (g : α → ℂ) : ∑ᶠ i, c * g i = c * ∑ᶠ i, g i :=
  (mul_finsum g c).symm

theorem avg_eq_of_rStab {H : Type} [Group H] (u : H → ℂ) (S : Subgroup H) (hS : rStab u = S) :
    avg u = ((S.index : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  subst hS
  rfl

theorem avg_const_mul {H : Type} [Group H] (c : ℂ) (u : H → ℂ) : avg (fun k => c * u k) = c * avg u := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul]
    simp [avg]
  · have hS : rStab (fun k => c * u k) = rStab u := Subgroup.ext fun k =>
      show (∀ x, c * u (x * k) = c * u x) ↔ ∀ x, u (x * k) = u x from
        forall_congr' fun x => mul_right_inj' hc
    rw [avg_eq_of_rStab _ _ hS, avg, finsum_const_mul_eq]
    ring

theorem twisted_orbital_integral_proportional (θ : G →* G) (K : Subgroup G) (δ : G) (f₁ f₂ : G → ℂ) (c : ℂ)
    (h : ∀ p : G, f₁ (p⁻¹ * δ * θ p) = c * f₂ (p⁻¹ * δ * θ p)) : twOrb θ K δ f₁ = c * twOrb θ K δ f₂ := by
  unfold twOrb
  rw [← finsum_const_mul_eq]
  refine finsum_congr fun q => ?_
  have e : (fun k : K => f₁ ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k))) =
      fun k : K => c * f₂ ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k)) := funext fun k => h _
  rw [e, avg_const_mul]
  ring

theorem twisted_orbital_integral_eq_zero_of_vanish (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (h : ∀ p : G, f (p⁻¹ * δ * θ p) = 0) :
    twOrb θ K δ f = 0 := by
  rw [twisted_orbital_integral_proportional θ K δ f f 0 (fun p => by rw [h p, zero_mul]), zero_mul]

theorem twisted_orbital_integral_indicator_inv_index [IsTopologicalGroup G] [T2Space G] (θ : G →* G) (K I : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (hθK : ∀ k ∈ K, θ k ∈ K) (hI : IsLevel θ K I) (δ : G) (X : Set G)
    (hXc : IsCompact X) (hXI : ∀ i ∈ I, ∀ g : G, (i * g ∈ X ↔ g ∈ X) ∧ (g * i ∈ X ↔ g ∈ X))
    (hC : CentOK θ K I δ) (p₀ : G) (h1 : OneCoset θ I δ X p₀) :
    twOrb θ K δ (X.indicator 1) = ((I.relIndex K : ℕ) : ℂ)⁻¹ :=
  twOrb_indicator_eq_inv_index θ K I hKo hKc hθK hI δ X hXI
    (HasCompactSupport.intro hXc fun _ hx => Set.indicator_of_notMem hx _) p₀ h1.1 h1.2

theorem twCent_prod {G' : Type} [Group G'] (θ : G →* G) (θ' : G' →* G') (δ : G) (δ' : G') :
    twCent (θ.prodMap θ') (δ, δ') = (twCent θ δ).prod (twCent θ' δ') := by
  ext p
  rw [Subgroup.mem_prod]
  show p * (δ, δ') = (δ, δ') * (θ.prodMap θ') p ↔ p.1 * δ = δ * θ p.1 ∧ p.2 * δ' = δ' * θ' p.2
  exact Prod.ext_iff

theorem map_conj_prod_le {G' : Type} [Group G'] (I : Subgroup G) (I' : Subgroup G') (x : G) (x' : G') :
    (I.map (MulAut.conj x).toMonoidHom).prod (I'.map (MulAut.conj x').toMonoidHom) ≤
      (I.prod I').map (MulAut.conj (x, x')).toMonoidHom := by
  rintro ⟨a, b⟩ hab
  obtain ⟨ha, hb⟩ := Subgroup.mem_prod.1 hab
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨j', hj', rfl⟩ := Subgroup.mem_map.1 hb
  exact Subgroup.mem_map.2 ⟨(j, j'), Subgroup.mem_prod.2 ⟨hj, hj'⟩, rfl⟩

theorem map_conj_prod_ge {G' : Type} [Group G'] (I : Subgroup G) (I' : Subgroup G') (x : G) (x' : G') :
    (I.prod I').map (MulAut.conj (x, x')).toMonoidHom ≤
      (I.map (MulAut.conj x).toMonoidHom).prod (I'.map (MulAut.conj x').toMonoidHom) := by
  intro p hp
  obtain ⟨⟨j, j'⟩, hj, rfl⟩ := Subgroup.mem_map.1 hp
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hj
  exact Subgroup.mem_prod.2 ⟨Subgroup.mem_map.2 ⟨j, h1, rfl⟩, Subgroup.mem_map.2 ⟨j', h2, rfl⟩⟩

theorem cptPart_prod_le {G' : Type} [Group G'] [TopologicalSpace G'] [T2Space G] [T2Space G']
    (T : Subgroup G) (T' : Subgroup G') : cptPart (T.prod T') ≤ (cptPart T).prod (cptPart T') := by
  unfold cptPart
  refine (Subgroup.closure_le _).2 ?_
  rintro ⟨t, t'⟩ ⟨htT, htc⟩
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 htT
  refine Subgroup.mem_prod.2 ⟨Subgroup.subset_closure ⟨h1, ?_⟩, Subgroup.subset_closure ⟨h2, ?_⟩⟩
  · have hC := htc.image continuous_fst
    refine hC.of_isClosed_subset isClosed_closure (closure_minimal ?_ hC.isClosed)
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨(t, t') ^ k, subset_closure (Subgroup.zpow_mem_zpowers _ k), map_zpow (MonoidHom.fst G G') (t, t') k⟩
  · have hC := htc.image continuous_snd
    refine hC.of_isClosed_subset isClosed_closure (closure_minimal ?_ hC.isClosed)
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨(t, t') ^ k, subset_closure (Subgroup.zpow_mem_zpowers _ k), map_zpow (MonoidHom.snd G G') (t, t') k⟩

theorem cptPart_prod_ge [IsTopologicalGroup G] {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    [T2Space G] [T2Space G'] (T : Subgroup G) (T' : Subgroup G') :
    (cptPart T).prod (cptPart T') ≤ cptPart (T.prod T') := by
  have hl : cptPart T ≤ (cptPart (T.prod T')).comap (MonoidHom.inl G G') := by
    unfold cptPart
    refine (Subgroup.closure_le _).2 ?_
    rintro t ⟨ht, htc⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    apply Subgroup.subset_closure
    refine ⟨Subgroup.mem_prod.2 ⟨ht, T'.one_mem⟩, ?_⟩
    have hC : IsCompact ((fun y : G => (y, (1 : G'))) '' closure (Subgroup.zpowers t : Set G)) :=
      htc.image (continuous_id.prodMk continuous_const)
    refine hC.of_isClosed_subset isClosed_closure (closure_minimal ?_ hC.isClosed)
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨t ^ k, subset_closure (Subgroup.zpow_mem_zpowers _ k), map_zpow (MonoidHom.inl G G') t k⟩
  have hr : cptPart T' ≤ (cptPart (T.prod T')).comap (MonoidHom.inr G G') := by
    unfold cptPart
    refine (Subgroup.closure_le _).2 ?_
    rintro t ⟨ht, htc⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    apply Subgroup.subset_closure
    refine ⟨Subgroup.mem_prod.2 ⟨T.one_mem, ht⟩, ?_⟩
    have hC : IsCompact ((fun y : G' => ((1 : G), y)) '' closure (Subgroup.zpowers t : Set G')) :=
      htc.image (continuous_const.prodMk continuous_id)
    refine hC.of_isClosed_subset isClosed_closure (closure_minimal ?_ hC.isClosed)
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨t ^ k, subset_closure (Subgroup.zpow_mem_zpowers _ k), map_zpow (MonoidHom.inr G G') t k⟩
  rintro ⟨a, b⟩ hab
  obtain ⟨ha, hb⟩ := Subgroup.mem_prod.1 hab
  have e : ((a, b) : G × G') = MonoidHom.inl G G' a * MonoidHom.inr G G' b := by simp
  rw [e]
  exact mul_mem (Subgroup.mem_comap.1 (hl ha)) (Subgroup.mem_comap.1 (hr hb))

theorem g1prod_pf [IsTopologicalGroup G] [T2Space G] {G' : Type} [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [T2Space G'] (θ : G →* G) (θ' : G' →* G') (K I : Subgroup G) (K' I' : Subgroup G')
    (δ : G) (δ' : G') (X : Set G) (X' : Set G') (p₀ : G) (p₀' : G') :
    (OneCoset θ I δ X p₀ → OneCoset θ' I' δ' X' p₀' →
      OneCoset (θ.prodMap θ') (I.prod I') (δ, δ') (X ×ˢ X') (p₀, p₀')) ∧
    (CentOK θ K I δ → CentOK θ' K' I' δ' → CentOK (θ.prodMap θ') (K.prod K') (I.prod I') (δ, δ')) := by
  unfold OneCoset CentOK
  have hcomp : ∀ p : G × G', p⁻¹ * (δ, δ') * (θ.prodMap θ') p = (p.1⁻¹ * δ * θ p.1, p.2⁻¹ * δ' * θ' p.2) :=
    fun p => rfl
  refine ⟨fun h h' => ⟨fun p => ?_, ?_⟩, fun h h' => ?_⟩
  · rw [hcomp, Set.mem_prod, h.1, h'.1, twCent_prod]
    constructor
    · rintro ⟨⟨z, hz, i, hi, e⟩, ⟨z', hz', i', hi', e'⟩⟩
      exact ⟨(z, z'), Subgroup.mem_prod.2 ⟨hz, hz'⟩, (i, i'), Subgroup.mem_prod.2 ⟨hi, hi'⟩, Prod.ext e e'⟩
    · rintro ⟨z, hz, i, hi, rfl⟩
      obtain ⟨hz1, hz2⟩ := Subgroup.mem_prod.1 hz
      obtain ⟨hi1, hi2⟩ := Subgroup.mem_prod.1 hi
      exact ⟨⟨z.1, hz1, i.1, hi1, rfl⟩, ⟨z.2, hz2, i.2, hi2, rfl⟩⟩
  · rw [twCent_prod]
    exact (cptPart_prod_le _ _).trans ((Subgroup.prod_mono h.2 h'.2).trans (map_conj_prod_le I I' p₀ p₀'))
  · rintro ⟨x1, x2⟩
    rw [twCent_prod]
    refine ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨hpT, hpK⟩ := Subgroup.mem_inf.1 hp
      obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hpT
      obtain ⟨k1, k2⟩ := Subgroup.mem_prod.1 (map_conj_prod_ge K K' x1 x2 hpK)
      exact cptPart_prod_ge _ _ (Subgroup.mem_prod.2
        ⟨(h x1).1 (Subgroup.mem_inf.2 ⟨h1, k1⟩), (h' x2).1 (Subgroup.mem_inf.2 ⟨h2, k2⟩)⟩)
    · have h1 : ((twCent θ δ ⊓ I.map (MulAut.conj x1).toMonoidHom).comap (MonoidHom.fst G G')).relIndex
          (cptPart ((twCent θ δ).prod (twCent θ' δ'))) ≠ 0 := by
        have := Subgroup.relIndex_comap_ne_zero (MonoidHom.fst G G') (h x1).2
        exact fun h0 => this (Subgroup.relIndex_eq_zero_of_le_right
          (fun p hp => (Subgroup.mem_prod.1 (cptPart_prod_le _ _ hp)).1) h0)
      have h2 : ((twCent θ' δ' ⊓ I'.map (MulAut.conj x2).toMonoidHom).comap (MonoidHom.snd G G')).relIndex
          (cptPart ((twCent θ δ).prod (twCent θ' δ'))) ≠ 0 := by
        have := Subgroup.relIndex_comap_ne_zero (MonoidHom.snd G G') (h' x2).2
        exact fun h0 => this (Subgroup.relIndex_eq_zero_of_le_right
          (fun p hp => (Subgroup.mem_prod.1 (cptPart_prod_le _ _ hp)).2) h0)
      have h12 : (((twCent θ δ ⊓ I.map (MulAut.conj x1).toMonoidHom).comap (MonoidHom.fst G G')) ⊓
          ((twCent θ' δ' ⊓ I'.map (MulAut.conj x2).toMonoidHom).comap (MonoidHom.snd G G'))).relIndex
          (cptPart ((twCent θ δ).prod (twCent θ' δ'))) ≠ 0 := by
        rw [← Subgroup.relIndex_inf_mul_relIndex]
        refine mul_ne_zero (fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h0)) h2
      refine fun h0 => h12 (Subgroup.relIndex_eq_zero_of_le_left ?_ h0)
      intro p hp
      obtain ⟨hp1, hp2⟩ := Subgroup.mem_inf.1 hp
      obtain ⟨a1, a2⟩ := Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hp1)
      obtain ⟨b1, b2⟩ := Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hp2)
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_prod.2 ⟨a1, b1⟩,
        map_conj_prod_le I I' x1 x2 (Subgroup.mem_prod.2 ⟨a2, b2⟩)⟩

theorem twisted_class_sum_eq_single_orbit (θ : G →* G) (K : Subgroup G) (S : Set G) (wt f : G → ℂ) (δ₀ : G) (c : ℂ) (hS : δ₀ ∈ S)
    (hinv : ∀ δ ∈ S, ∀ g : G, g⁻¹ * δ * θ g ∈ S)
    (hval : ∀ g : G, wt (g⁻¹ * δ₀ * θ g) * twOrb θ K (g⁻¹ * δ₀ * θ g) f = c)
    (hone : ∀ δ ∈ S, wt δ * twOrb θ K δ f ≠ 0 → ∃ g : G, δ = g⁻¹ * δ₀ * θ g) :
    clSum θ K S wt f = c := by
  have h1 := hval 1
  simp only [inv_one, one_mul, map_one, mul_one] at h1
  rw [clSum_eq_single θ K S wt f δ₀ (fun g => hinv δ₀ hS g) (fun g => (hval g).trans h1.symm)
    (fun c hc hne => hone _ hc hne), h1]

theorem g2zero_pf (θ : G →* G) (K : Subgroup G) (S : Set G) (wt f : G → ℂ)
    (h : ∀ δ ∈ S, wt δ * twOrb θ K δ f = 0) : clSum θ K S wt f = 0 := by
  unfold clSum
  refine (finsum_congr fun c => ?_).trans finsum_zero
  split_ifs with hc
  · exact h _ hc
  · rfl

end Generic

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
