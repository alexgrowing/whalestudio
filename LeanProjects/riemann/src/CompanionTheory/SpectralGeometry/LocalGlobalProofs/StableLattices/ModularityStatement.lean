import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

open CompanionTheory.Rg.Fl
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeCoinv

section Action

variable (Γ : Type) {X : Type} [Group Γ] [MulAction Γ X]

def cnt (x y : X) : ℕ := Nat.card {γ : Γ // γ • x = y}

variable {Γ}

theorem cnt_congr {a b : X} (s t : Γ) : cnt Γ a b = cnt Γ (s • a) (t • b) := by
  refine Nat.card_congr ⟨fun γ => ⟨t * γ.1 * s⁻¹, ?_⟩, fun γ => ⟨t⁻¹ * γ.1 * s, ?_⟩, fun γ => ?_, fun γ => ?_⟩
  · simp [mul_smul, γ.2]
  · rw [mul_smul, mul_smul, γ.2, inv_smul_smul]
  · apply Subtype.ext; simp [mul_assoc]
  · apply Subtype.ext; simp [mul_assoc]

theorem finite_fib [∀ x : X, Finite (MulAction.stabilizer Γ x)] (x y : X) :
    Finite {γ : Γ // γ • x = y} := by
  by_cases hne : Nonempty {γ : Γ // γ • x = y}
  · obtain ⟨γ0, h0⟩ := hne
    refine Finite.of_injective (β := MulAction.stabilizer Γ x) (fun γ => ⟨γ0⁻¹ * γ.1, ?_⟩) ?_
    · rw [MulAction.mem_stabilizer_iff, mul_smul, γ.2, ← h0, inv_smul_smul]
    · intro a b hab
      apply Subtype.ext
      simpa using congrArg Subtype.val hab
  · haveI := not_nonempty_iff.1 hne
    infer_instance

theorem cnt_self_pos [∀ x : X, Finite (MulAction.stabilizer Γ x)] (x : X) : 0 < cnt Γ x x := by
  haveI := finite_fib (Γ := Γ) x x
  haveI : Nonempty {γ : Γ // γ • x = x} := ⟨⟨1, one_smul _ _⟩⟩
  exact Nat.card_pos

theorem support_finite [∀ x : X, Finite (MulAction.stabilizer Γ x)] (f : X →₀ ℂ) (x : X) :
    (Function.support fun γ : Γ => f (γ • x)).Finite := by
  refine Set.Finite.subset (Set.Finite.biUnion f.support.finite_toSet
    (t := fun z => {γ : Γ | γ • x = z}) ?_) ?_
  · intro z _
    exact Set.finite_coe_iff.1 (finite_fib (Γ := Γ) x z)
  · intro γ hγ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨γ • x, by simpa using hγ, rfl⟩

theorem finsum_eq [∀ x : X, Finite (MulAction.stabilizer Γ x)] (f : X →₀ ℂ) (x : X) :
    ∑ᶠ γ : Γ, f (γ • x) = f.sum fun z c => c * (cnt Γ x z : ℂ) := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s := (support_finite (Γ := Γ) f x).toFinset) (by simp)]
  have hmaps : ∀ γ ∈ (support_finite (Γ := Γ) f x).toFinset, γ • x ∈ f.support := by
    intro γ hγ
    simpa using hγ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finsupp.sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have h1 : ∀ γ ∈ (support_finite (Γ := Γ) f x).toFinset.filter (fun γ => γ • x = z),
      f (γ • x) = f z := by
    intro γ hγ
    rw [(Finset.mem_filter.1 hγ).2]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  have H : ∀ γ : Γ, γ • x = z ↔ γ ∈ (support_finite (Γ := Γ) f x).toFinset.filter (fun γ => γ • x = z) := by
    intro γ
    constructor
    · intro hγ
      refine Finset.mem_filter.2 ⟨?_, hγ⟩
      simpa [hγ] using Finsupp.mem_support_iff.1 hz
    · intro hγ
      exact (Finset.mem_filter.1 hγ).2
  unfold cnt
  rw [Nat.card_congr (Equiv.subtypeEquivRight H), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem exists_phi [Finite (MulAction.orbitRel.Quotient Γ X)] [∀ x : X, Finite (MulAction.stabilizer Γ x)] :
    ∃ (N : ℕ) (φ : (X →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)), Function.Surjective φ ∧
      ∀ x y, ⟪φ (Finsupp.single x 1), φ (Finsupp.single y 1)⟫_ℂ = (cnt Γ x y : ℂ) := by
  classical
  let Q := MulAction.orbitRel.Quotient Γ X
  let π : X → Q := fun x => Quotient.mk'' x
  let o : Q → X := fun q => q.out
  have hπo : ∀ q, π (o q) = q := fun q => Quotient.out_eq' q
  have hrel : ∀ x y, π x = π y → ∃ γ : Γ, γ • y = x := by
    intro x y hxy
    have : x ∈ MulAction.orbit Γ y := MulAction.orbitRel_apply.1 (Quotient.eq''.1 hxy)
    exact this
  let e : Q ≃ Fin (Nat.card Q) := Finite.equivFin Q
  let w : Q → ℕ := fun q => cnt Γ (o q) (o q)
  have hw : ∀ q, 0 < w q := fun q => cnt_self_pos _
  let cf : Q → ℂ := fun q => ((Real.sqrt (w q) : ℝ) : ℂ)
  have hcf : ∀ q, conj (cf q) * cf q = (w q : ℂ) := by
    intro q
    simp only [cf, Complex.conj_ofReal, ← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  have hcf0 : ∀ q, cf q ≠ 0 := by
    intro q
    have := Real.sqrt_pos.2 (Nat.cast_pos.2 (hw q) : (0 : ℝ) < w q)
    exact Complex.ofReal_ne_zero.2 this.ne'
  let vec : X → EuclideanSpace ℂ (Fin (Nat.card Q)) := fun x => EuclideanSpace.single (e (π x)) (cf (π x))
  refine ⟨Nat.card Q, Finsupp.linearCombination ℂ vec, ?_, ?_⟩
  · rw [← LinearMap.range_eq_top, eq_top_iff]
    intro v _
    rw [← (EuclideanSpace.basisFun (Fin (Nat.card Q)) ℂ).sum_repr v]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    refine ⟨Finsupp.single (o (e.symm i)) (cf (e.symm i))⁻¹, ?_⟩
    simp only [Finsupp.linearCombination_single, vec, hπo, Equiv.apply_symm_apply]
    ext j
    by_cases hj : j = i
    · subst hj
      simp [hcf0]
    · simp [hj]
  · intro x y
    simp only [Finsupp.linearCombination_single, one_smul, vec]
    by_cases hxy : π x = π y
    · obtain ⟨γ, hγ⟩ := hrel (o (π x)) x (hπo _ ▸ rfl)
      obtain ⟨γ', hγ'⟩ := hrel (o (π x)) y (by rw [hπo, hxy])
      have : cnt Γ x y = w (π x) := by
        show _ = cnt Γ (o (π x)) (o (π x))
        conv_rhs => rw [← hγ]
        conv_rhs => rhs; rw [hγ, ← hγ']
        exact cnt_congr γ γ'
      rw [this, ← hxy, EuclideanSpace.inner_single_left]
      simp [hcf]
    · have hne : e (π x) ≠ e (π y) := fun h => hxy (e.injective h)
      have : IsEmpty {γ : Γ // γ • x = y} := ⟨fun γ => by
        obtain ⟨γ, hγ⟩ := γ
        apply hxy
        rw [← hγ]
        exact (Quotient.eq''.2 (MulAction.orbitRel_apply.2 ⟨γ⁻¹, by simp⟩))⟩
      have h0 : cnt Γ x y = 0 := Nat.card_of_isEmpty
      rw [h0, EuclideanSpace.inner_single_left]
      simp [hne, Ne.symm hne]

end Action

section Hecke

variable {G : Type} [Group G] {K : Subgroup G}

def ent (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (x y : G ⧸ K) : ℂ := h (Finsupp.single y 1) x

theorem lam_single (g : G) (x : G ⧸ K) (c : ℂ) :
    lam K g (Finsupp.single x c) = Finsupp.single (g • x) c := by
  simp [lam, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem lam_apply_smul (g : G) (f : (G ⧸ K) →₀ ℂ) (x : G ⧸ K) : lam K g f (g • x) = f x :=
  Finsupp.mapDomain_apply (MulAction.injective g) f x

theorem comm_lam (h : Hk K) (g : G) (u : (G ⧸ K) →₀ ℂ) : h.1 (lam K g u) = lam K g (h.1 u) := by
  have := (Subalgebra.mem_centralizer_iff ℂ).1 h.2 (lam K g) ⟨g, rfl⟩
  exact (LinearMap.congr_fun this u).symm

theorem ent_smul (h : Hk K) (g : G) (x y : G ⧸ K) : ent h.1 (g • x) (g • y) = ent h.1 x y := by
  unfold ent
  rw [← lam_single, comm_lam, lam_apply_smul]

theorem row_finite (hp : IsHeckePair K) (h : Hk K) (x : G ⧸ K) : {z | ent h.1 x z ≠ 0}.Finite := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  set A := (h.1 (Finsupp.single ((1 : G) : G ⧸ K) 1)).support with hA
  refine Set.Finite.subset (Set.Finite.biUnion (s := (A : Set (G ⧸ K))) A.finite_toSet
    (t := fun a => (fun w => g • w) '' MulAction.orbit K (((Quotient.out a)⁻¹ : G) : G ⧸ K))
    (fun a _ => (hp _).image _)) ?_
  intro z hz
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective z
  have h1 : ent h.1 ((g'⁻¹ * g : G) : G ⧸ K) ((1 : G) : G ⧸ K) ≠ 0 := by
    have h2 := ent_smul h g'⁻¹ (g : G ⧸ K) (g' : G ⧸ K)
    have h3 : g'⁻¹ • (g : G ⧸ K) = ((g'⁻¹ * g : G) : G ⧸ K) := rfl
    have h4 : g'⁻¹ • (g' : G ⧸ K) = ((1 : G) : G ⧸ K) := by
      show ((g'⁻¹ * g' : G) : G ⧸ K) = _
      simp
    rw [h3, h4] at h2
    rw [h2]
    exact hz
  set a : G ⧸ K := ((g'⁻¹ * g : G) : G ⧸ K) with ha
  have haA : a ∈ A := Finsupp.mem_support_iff.2 h1
  have hk : (Quotient.out a : G)⁻¹ * (g'⁻¹ * g) ∈ K := QuotientGroup.eq.1 (QuotientGroup.out_eq' a)
  simp only [Set.mem_iUnion]
  refine ⟨a, haA, ?_⟩
  refine ⟨(⟨((Quotient.out a : G)⁻¹ * (g'⁻¹ * g))⁻¹, K.inv_mem hk⟩ : K) • (((Quotient.out a)⁻¹ : G) : G ⧸ K),
    MulAction.mem_orbit _ _, ?_⟩
  show ((g * (((Quotient.out a : G)⁻¹ * (g'⁻¹ * g))⁻¹ * (Quotient.out a)⁻¹) : G) : G ⧸ K) = _
  congr 1
  group

def rowF (hp : IsHeckePair K) (h : Hk K) (x : G ⧸ K) : (G ⧸ K) →₀ ℂ :=
  Finsupp.ofSupportFinite (fun z => conj (ent h.1 x z)) ((row_finite hp h x).subset fun z hz => by
    simpa using hz)

theorem rowF_apply (hp : IsHeckePair K) (h : Hk K) (x z : G ⧸ K) :
    rowF hp h x z = conj (ent h.1 x z) := rfl

theorem lam_rowF (hp : IsHeckePair K) (h : Hk K) (g : G) (x : G ⧸ K) :
    lam K g (rowF hp h x) = rowF hp h (g • x) := by
  ext z
  obtain ⟨z', rfl⟩ : ∃ z', g • z' = z := ⟨g⁻¹ • z, smul_inv_smul g z⟩
  rw [lam_apply_smul, rowF_apply, rowF_apply, ent_smul]

def starH (hp : IsHeckePair K) (h : Hk K) : Hk K :=
  ⟨Finsupp.linearCombination ℂ (rowF hp h), by
    refine (Subalgebra.mem_centralizer_iff ℂ).2 ?_
    rintro _ ⟨g, rfl⟩
    refine Finsupp.lhom_ext fun a b => ?_
    simp only [Module.End.mul_apply, Finsupp.linearCombination_single, lam_single, map_smul, lam_rowF]⟩

theorem starH_single (hp : IsHeckePair K) (h : Hk K) (x : G ⧸ K) :
    (starH hp h).1 (Finsupp.single x 1) = rowF hp h x := by
  simp [starH]

end Hecke

section Form

variable {G : Type} [Group G] {K : Subgroup G}

theorem inner_phi {N : ℕ} (Γ : Subgroup G) (φ : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (hφ : ∀ x y, ⟪φ (Finsupp.single x 1), φ (Finsupp.single y 1)⟫_ℂ = (cnt Γ x y : ℂ))
    (x : G ⧸ K) (f : (G ⧸ K) →₀ ℂ) :
    ⟪φ (Finsupp.single x 1), φ f⟫_ℂ = f.sum fun z c => c * (cnt Γ x z : ℂ) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, inner_add_right, ha, hb, Finsupp.sum_add_index' (by simp) (by intros; ring)]
  | single z c =>
    have hs : Finsupp.single z c = c • Finsupp.single z (1 : ℂ) := by simp
    rw [Finsupp.sum_single_index (by simp), hs, map_smul, inner_smul_right, hφ]

theorem adj_single {N : ℕ} (Γ : Subgroup G) [∀ x : G ⧸ K, Finite (MulAction.stabilizer Γ x)]
    (hp : IsHeckePair K) (h : Hk K) (φ : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (hφ : ∀ x y, ⟪φ (Finsupp.single x 1), φ (Finsupp.single y 1)⟫_ℂ = (cnt Γ x y : ℂ)) (x y : G ⧸ K) :
    ⟪φ (Finsupp.single x 1), φ (h.1 (Finsupp.single y 1))⟫_ℂ =
      ⟪φ ((starH hp h).1 (Finsupp.single x 1)), φ (Finsupp.single y 1)⟫_ℂ := by
  set F := h.1 (Finsupp.single y 1) with hF
  rw [starH_single, ← inner_conj_symm (φ (rowF hp h x)), inner_phi Γ φ hφ y, inner_phi Γ φ hφ x,
    ← finsum_eq, ← finsum_eq]
  have h1 : ∀ γ : Γ, rowF hp h x (γ • y) = conj (F (γ⁻¹ • x)) := by
    intro γ
    rw [rowF_apply]
    congr 1
    have := ent_smul h (γ : G) ((γ⁻¹ : Γ) • x) y
    have h2 : (γ : G) • ((γ⁻¹ : Γ) • x) = x := smul_inv_smul γ x
    rw [h2] at this
    exact this
  have h3 : ∑ᶠ γ : Γ, rowF hp h x (γ • y) = ∑ᶠ γ : Γ, conj (F (γ • x)) := by
    simp only [h1]
    exact finsum_comp_equiv (Equiv.inv Γ) (f := fun γ : Γ => conj (F (γ • x)))
  rw [h3]
  have h4 := AddMonoidHom.map_finsum (starRingEnd ℂ : ℂ →+* ℂ).toAddMonoidHom
    (support_finite (Γ := Γ) F x)
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at h4
  rw [← h4]
  simp

theorem adj {N : ℕ} (Γ : Subgroup G) [∀ x : G ⧸ K, Finite (MulAction.stabilizer Γ x)]
    (hp : IsHeckePair K) (φ : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (hφ : ∀ x y, ⟪φ (Finsupp.single x 1), φ (Finsupp.single y 1)⟫_ℂ = (cnt Γ x y : ℂ))
    (h : Hk K) (u v : (G ⧸ K) →₀ ℂ) :
    ⟪φ u, φ (h.1 v)⟫_ℂ = ⟪φ ((starH hp h).1 u), φ v⟫_ℂ := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, inner_add_right, ha, hb]
  | single y c =>
    have hs : Finsupp.single y c = c • Finsupp.single y (1 : ℂ) := by simp
    rw [hs]
    simp only [map_smul, inner_smul_right]
    congr 1
    induction u using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, inner_add_left, ha, hb]
    | single x d =>
      have hs' : Finsupp.single x d = d • Finsupp.single x (1 : ℂ) := by simp
      rw [hs']
      simp only [map_smul, inner_smul_left]
      rw [adj_single Γ hp h φ hφ]

theorem exists_rho {N : ℕ} (hp : IsHeckePair K) (φ : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (hs : Function.Surjective φ)
    (hadj : ∀ (h : Hk K) u v, ⟪φ u, φ (h.1 v)⟫_ℂ = ⟪φ ((starH hp h).1 u), φ v⟫_ℂ) :
    ∃ ρ : Hk K →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin N)),
      StarClosed ρ ∧ ∀ h u, ρ h (φ u) = φ (h.1 u) := by
  obtain ⟨σ, hσ⟩ := φ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hs)
  have hσ' : ∀ v, φ (σ v) = v := fun v => LinearMap.congr_fun hσ v
  have hker : ∀ (h : Hk K) u, φ u = 0 → φ (h.1 u) = 0 := by
    intro h u hu
    have := hadj h (h.1 u) u
    rw [hu, inner_zero_right] at this
    exact (inner_self_eq_zero (𝕜 := ℂ)).1 this
  have hdesc : ∀ (h : Hk K) u, φ (h.1 (σ (φ u))) = φ (h.1 u) := by
    intro h u
    have h1 : φ (σ (φ u) - u) = 0 := by rw [map_sub, hσ', sub_self]
    have h2 := hker h _ h1
    rwa [map_sub, map_sub, sub_eq_zero] at h2
  let L : Hk K →ₗ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin N)) :=
    { toFun := fun h => φ ∘ₗ h.1 ∘ₗ σ
      map_add' := fun a b => by
        ext1 v
        simp
      map_smul' := fun c a => by
        ext1 v
        simp }
  have hL : ∀ h u, L h (φ u) = φ (h.1 u) := fun h u => hdesc h u
  let ρ : Hk K →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin N)) := AlgHom.ofLinearMap L
    (by
      ext1 v
      show φ (σ v) = v
      exact hσ' v)
    (fun a b => by
      ext1 v
      obtain ⟨u, rfl⟩ := hs v
      show L (a * b) (φ u) = L a (L b (φ u))
      rw [hL, hL, hL]
      rfl)
  have hρ : ∀ h u, ρ h (φ u) = φ (h.1 u) := hL
  refine ⟨ρ, fun h => ⟨starH hp h, fun a b => ?_⟩, hρ⟩
  obtain ⟨u, rfl⟩ := hs a
  obtain ⟨v, rfl⟩ := hs b
  rw [hρ, hρ, ← inner_conj_symm, hadj h v u, inner_conj_symm]

end Form

theorem stMod : StMod := by
  intro G _ K hp hsep h
  classical
  obtain ⟨Γ, hfin, hstab, hS⟩ := hsep (h.1 (Finsupp.single ((1 : G) : G ⧸ K) 1)).support
  obtain ⟨N, φ, hs, hφ⟩ := exists_phi (Γ := Γ) (X := G ⧸ K)
  obtain ⟨ρ, hstar, hρ⟩ := exists_rho hp φ hs (adj Γ hp φ hφ)
  refine ⟨N, ρ, hstar, fun h0 => ?_⟩
  set f := h.1 (Finsupp.single ((1 : G) : G ⧸ K) 1) with hf
  have hφf : φ f = 0 := by
    rw [hf, ← hρ, h0]
    rfl
  have hf0 : f = 0 := by
    ext z
    by_contra hz
    have hzS : z ∈ f.support := Finsupp.mem_support_iff.2 hz
    have h1 := inner_phi Γ φ hφ z f
    rw [hφf, inner_zero_right, Finsupp.sum, Finset.sum_eq_single z] at h1
    · have h2 : (cnt Γ z z : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (cnt_self_pos z).ne'
      exact mul_ne_zero hz h2 h1.symm
    · intro y hy hyz
      have : IsEmpty {γ : Γ // γ • z = y} := ⟨fun γ => hyz (hS z hzS y hy γ.1 γ.2).symm⟩
      have h0 : cnt Γ z y = 0 := Nat.card_of_isEmpty
      simp [h0]
    · intro hnot
      exact absurd hzS hnot
  apply Subtype.ext
  refine Finsupp.lhom_ext fun a b => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  have h1 : Finsupp.single (g : G ⧸ K) b = b • lam K g (Finsupp.single ((1 : G) : G ⧸ K) 1) := by
    rw [lam_single]
    have : g • ((1 : G) : G ⧸ K) = (g : G ⧸ K) := by
      show ((g * 1 : G) : G ⧸ K) = _
      simp
    rw [this]
    simp
  rw [h1, map_smul, comm_lam, ← hf, hf0]
  simp

end GlobalTheory.CompanionTheory.HeckeCoinv

end
