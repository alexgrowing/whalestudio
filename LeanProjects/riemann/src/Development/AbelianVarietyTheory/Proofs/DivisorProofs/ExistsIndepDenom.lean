import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.GaussDown

theorem descent {R₁ E : Type} [CommRing R₁] [CommRing E] [IsLocalRing E] (a : R₁ →+* E) (ha : a.Flat)
    (q : Ideal R₁) (hq : ∀ t ∈ q, a t ∈ maximalIdeal E) {m J : ℕ} (p : Fin m → R₁) (g : Fin J → Fin m → R₁)
    (e : Fin J → E) (h : ∀ i, a (p i) = ∑ j, e j * a (g j i)) :
    ∃ s, s ∉ q ∧ ∃ r : Fin J → R₁, ∀ i, s * p i = ∑ j, r j * g j i := by
  classical
  letI : Algebra R₁ E := a.toAlgebra
  haveI : Module.Flat R₁ E := ha
  let A : Matrix (Fin (J + 1)) (Fin m) R₁ := Fin.cons p g
  let xv : Fin (J + 1) → E := Fin.cons 1 (fun j => -e j)
  let f : (Fin m → R₁) →ₗ[R₁] (Fin (J + 1) → R₁) := A.mulVecLin
  let x : (Fin (J + 1) → R₁) →ₗ[R₁] E := Fintype.linearCombination R₁ xv
  have hxf : x ∘ₗ f = 0 := by
    ext k
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, f, x, Matrix.mulVecLin_apply,
      Fintype.linearCombination_apply, Matrix.mulVec, dotProduct]
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [Fin.sum_univ_succ, A, xv, Fin.cons_zero, Fin.cons_succ, smul_eq_mul, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra, map_mul, Pi.single_apply]
    rw [h i, Finset.sum_mul, Finset.sum_mul]
    simp only [_root_.mul_one, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun j _ => by ring
  obtain ⟨k, α, y, hxy, hαf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
  let ev : ∀ {n : ℕ}, Fin n → Fin n → R₁ := fun c j => if c = j then 1 else 0
  have h1 : y (α (ev 0)) = 1 := by
    have := LinearMap.congr_fun hxy (ev 0)
    simp only [LinearMap.comp_apply] at this
    rw [← this]
    simp [x, xv, ev, Fintype.linearCombination_apply, Fin.sum_univ_succ]
  have hy : ∀ c' : Fin k →₀ R₁, y c' = ∑ l ∈ c'.support, a (c' l) * y (Finsupp.single l 1) := by
    intro c'
    conv_lhs => rw [← Finsupp.sum_single c']
    rw [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← _root_.mul_one (c' l), ← smul_eq_mul, ← Finsupp.smul_single, map_smul, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra]
    simp only [smul_eq_mul, _root_.mul_one]
  obtain ⟨l, hl⟩ : ∃ l, α (ev 0) l ∉ q := by
    by_contra hall
    push_neg at hall
    have : (1 : E) ∈ maximalIdeal E := by
      rw [← h1, hy]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hq _ (hall l))
    exact (maximalIdeal.isMaximal E).ne_top ((Ideal.eq_top_iff_one _).2 this)
  refine ⟨α (ev 0) l, hl, fun j => -(α (ev j.succ) l), fun i => ?_⟩
  have h2 := congrArg (fun z : Fin k →₀ R₁ => z l) (LinearMap.congr_fun hαf (ev i))
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply] at h2
  rw [LinearMap.pi_apply_eq_sum_univ α] at h2
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_succ] at h2
  have hA : ∀ c, (A.mulVecLin (ev i)) c = A c i := by
    intro c
    simp [Matrix.mulVec, dotProduct, ev]
  simp only [f, hA, A, Fin.cons_zero, Fin.cons_succ] at h2
  have hs : ∑ j, -(α (ev j.succ) l) * g j i = -∑ j, g j i * α (ev j.succ) l := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.finset_sum_apply, smul_eq_mul] at h2
  rw [hs]
  simp only [ev] at h2 ⊢
  linear_combination h2

end GlobalTheory.Desc.GaussDown

namespace GlobalTheory.Desc.GaussDown

theorem exists_indep_denom {R₁ F₁ : Type} [CommRing R₁] [IsDomain R₁] [Field F₁] (c₁ : R₁ →+* F₁) {n : ℕ}
    (y : Fin n → F₁) :
    ∃ (m : ℕ) (b : Fin m → F₁) (δ : R₁) (G : Fin n → Fin m → R₁),
      (∀ r : Fin m → R₁, ∑ i, c₁ (r i) * b i = 0 → r = 0) ∧ δ ≠ 0 ∧
        ∀ l, c₁ δ * y l = ∑ i, c₁ (G l i) * b i := by
  classical
  letI : Algebra R₁ F₁ := c₁.toAlgebra
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn R₁ y
  have hex : ∀ l, ∃ a : R₁, a ≠ 0 ∧ a • y l ∈ Submodule.span R₁ (y '' s) := by
    intro l
    by_cases hl : l ∈ s
    · exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span ⟨l, hl, rfl⟩⟩
    · exact hmax l hl
  choose a ha0 ha using hex
  let eqv : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let b : Fin (Fintype.card s) → F₁ := fun i => y (eqv i)
  have hb : LinearIndependent R₁ b := hs.comp eqv eqv.injective
  have hspan : Submodule.span R₁ (y '' s) = Submodule.span R₁ (Set.range b) := by
    congr 1
    ext z
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨eqv.symm ⟨l, hl⟩, by simp [b]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, (eqv i).2, rfl⟩
  have hδ : (∏ l, a l) ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => ha0 l
  have hmem : ∀ l, (∏ l, a l) • y l ∈ Submodule.span R₁ (Set.range b) := by
    intro l
    rw [← hspan, ← Finset.prod_erase_mul _ _ (Finset.mem_univ l), mul_smul]
    exact Submodule.smul_mem _ _ (ha l)
  choose G hG using fun l => (Submodule.mem_span_range_iff_exists_fun R₁).1 (hmem l)
  refine ⟨_, b, ∏ l, a l, G, ?_, hδ, ?_⟩
  · intro r hr
    have := Fintype.linearIndependent_iff.1 hb r
      (by simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hr)
    funext i
    exact this i
  · intro l
    have := hG l
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] at this
    exact this.symm

end GlobalTheory.Desc.GaussDown

namespace GlobalTheory.Desc.GaussDown

theorem gaussAt_descent : ∀ (R₀ R₁ E F F₁ FE : Type) [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁] [CommRing E] [IsDomain E] [IsLocalRing E] [Field F] [Field F₁] [Field FE] (ρ : R₀ →+* R₁) (a : R₁ →+* E) (c₀ : R₀ →+* F) (c₁ : R₁ →+* F₁) (cE : E →+* FE) (θ : F →+* F₁) (θE : F₁ →+* FE) (q : Ideal R₁) [q.IsPrime] (W : Set F) (W₁ : Set F₁) (WE : Set FE), a.Flat → Function.Injective c₁ → (∀ s, s ∉ q → IsUnit (a s)) → (∀ t, t ∈ q → a t ∈ maximalIdeal E) → θ.comp c₀ = c₁.comp ρ → θE.comp c₁ = cE.comp a → LinDisj c₀ c₁ θ → LinDisj c₁ cE θE → θE ⁻¹' WE = W₁ → GaussAt cE (maximalIdeal E) (θE.comp θ) W WE → GaussAt c₁ q θ W W₁ := by
  intro R₀ R₁ E F F₁ FE _ _ _ _ _ _ _ _ _ _ ρ a c₀ c₁ cE θ θE q _ W W₁ WE ha hc₁ hunit hmax _ hE _ hL1 hW hG
  have hcomp : ∀ r, cE (a r) = θE (c₁ r) := fun r => (RingHom.congr_fun hE r).symm
  have ha0 : ∀ d : R₁, d ≠ 0 → a d ≠ 0 := by
    intro d hd h
    apply hd
    apply hc₁
    apply θE.injective
    rw [← hcomp, h, map_zero, map_zero, map_zero]
  intro v ⟨d, hd, hdv⟩
  have hEv : ∃ d' : E, d' ≠ 0 ∧ cE d' * θE v ∈ spanBy cE (Set.range (θE.comp θ)) := by
    obtain ⟨n, r, u, hu, hsum⟩ := hdv
    refine ⟨a d, ha0 d hd, n, fun i => a (r i), fun i => θE (u i), fun i => ?_, ?_⟩
    · obtain ⟨w, hw⟩ := hu i
      exact ⟨w, by rw [RingHom.comp_apply, hw]⟩
    · have := congrArg θE hsum
      simpa [map_sum, hcomp] using this
  rw [← hW, Set.mem_preimage, hG (θE v) hEv]
  constructor
  · rintro ⟨t, ht, n, e, z, hz, hsum⟩
    choose w hwW hwz using hz
    obtain ⟨m, b, δ, G, hb, hδ, hGb⟩ := exists_indep_denom c₁ (Fin.cons v (fun j => θ (w j)) : Fin (n + 1) → F₁)
    have hv : c₁ δ * v = ∑ i, c₁ (G 0 i) * b i := by simpa using hGb 0
    have hw' : ∀ j, c₁ δ * θ (w j) = ∑ i, c₁ (G j.succ i) * b i := fun j => by simpa using hGb j.succ
    have htu : IsUnit t := by
      by_contra h
      exact ht ((mem_maximalIdeal _).2 h)
    have e1 : ∑ i, cE (a (G 0 i)) * θE (b i) = θE (c₁ δ) * θE v := by
      rw [← map_mul, hv, map_sum]
      simp [hcomp]
    have e2 : ∀ j, ∑ i, cE (a (G j.succ i)) * θE (b i) = θE (c₁ δ) * z j := by
      intro j
      rw [← hwz j, RingHom.comp_apply, ← map_mul, hw' j, map_sum]
      simp [hcomp]
    have hz0 := hL1 m b hb (fun i => t * a (G 0 i) - ∑ j, e j * a (G j.succ i)) (by
      calc ∑ i, cE (t * a (G 0 i) - ∑ j, e j * a (G j.succ i)) * θE (b i)
          = cE t * (∑ i, cE (a (G 0 i)) * θE (b i)) - ∑ j, cE (e j) * (∑ i, cE (a (G j.succ i)) * θE (b i)) := by
            simp only [map_sub, map_mul, map_sum, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
              (f := fun i j => cE (e j) * cE (a (G j.succ i)) * θE (b i))]
            congr 1
            · exact Finset.sum_congr rfl fun i _ => by ring
            · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
        _ = θE (c₁ δ) * (cE t * θE v - ∑ j, cE (e j) * z j) := by
            rw [e1, mul_sub, Finset.mul_sum]
            simp only [e2]
            congr 1
            · ring
            · exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hsum, sub_self, mul_zero])
    have hrel : ∀ i, a (G 0 i) = ∑ j, (↑htu.unit⁻¹ * e j) * a (G j.succ i) := by
      intro i
      have h1 := sub_eq_zero.1 (congrFun hz0 i)
      simp only [_root_.mul_assoc, ← Finset.mul_sum]
      rw [← h1, ← _root_.mul_assoc, IsUnit.val_inv_mul, _root_.one_mul]
    obtain ⟨s, hs, r, hr⟩ := descent a ha q hmax (G 0) (fun j => G j.succ) _ hrel
    refine ⟨s, hs, n, r, fun j => θ (w j), fun j => ⟨w j, hwW j, rfl⟩, ?_⟩
    have hδ' : c₁ δ ≠ 0 := (map_ne_zero_iff _ hc₁).2 hδ
    apply mul_left_cancel₀ hδ'
    calc c₁ δ * (c₁ s * v) = c₁ s * (c₁ δ * v) := by ring
      _ = ∑ i, c₁ (s * G 0 i) * b i := by
          rw [hv, Finset.mul_sum]
          simp only [map_mul, _root_.mul_assoc]
      _ = ∑ i, ∑ j, c₁ (r j) * (c₁ (G j.succ i) * b i) := by
          simp only [hr, map_sum, map_mul, Finset.sum_mul, _root_.mul_assoc]
      _ = ∑ j, c₁ (r j) * (c₁ δ * θ (w j)) := by
          rw [Finset.sum_comm]
          simp only [hw', Finset.mul_sum]
      _ = c₁ δ * ∑ j, c₁ (r j) * θ (w j) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  · rintro ⟨s, hs, n, r, z, hz, hsum⟩
    refine ⟨a s, fun hm => ((mem_maximalIdeal _).1 hm) (hunit s hs), n, fun i => a (r i), fun i => θE (z i),
      fun i => ?_, ?_⟩
    · obtain ⟨w, hw, hwz⟩ := hz i
      exact ⟨w, hw, by rw [RingHom.comp_apply, hwz]⟩
    · have := congrArg θE hsum
      simpa [map_sum, hcomp] using this

end GlobalTheory.Desc.GaussDown
