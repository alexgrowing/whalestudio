import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

namespace GlobalTheory.ThetaGL.DualPair

section General

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def ev (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G W) :
    V ⊗[ℂ] smoothPart π.dual →ₗ[ℂ] W →ₗ[ℂ] V :=
  TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun (v : V) (l : smoothPart π.dual) => (l : Module.Dual ℂ W).smulRight v)
    (fun v v' l => by ext w; simp)
    (fun c v l => by
      ext w
      show (l : Module.Dual ℂ W) w • c • v = c • (l : Module.Dual ℂ W) w • v
      exact smul_comm _ _ _)
    (fun v l l' => by ext w; simp [add_smul])
    (fun c v l => by ext w; simp [smul_smul]))

@[simp] theorem ev_tmul (π : Representation ℂ G W) (v : V) (l : smoothPart π.dual) (w : W) :
    ev V π (v ⊗ₜ l) w = (l : Module.Dual ℂ W) w • v := rfl

theorem ev_injective (π : Representation ℂ G W) : Function.Injective (ev V π) := by
  refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
  let b := Module.Basis.ofVectorSpace ℂ V
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b t
  have hc : ∀ i ∈ c.support, c i = 0 := by
    intro i hi
    apply Subtype.ext
    refine LinearMap.ext fun w => ?_
    have h0 : ev V π (c.sum fun i n => b i ⊗ₜ[ℂ] n) w = 0 := by rw [ht]; rfl
    have h1 : ∑ j ∈ c.support, ((c j : Module.Dual ℂ W) w) • b j = 0 := by
      rw [← h0, Finsupp.sum, map_sum, LinearMap.sum_apply]
      rfl
    exact linearIndependent_iff'.1 b.linearIndependent c.support _ h1 i hi
  rw [Finsupp.sum]
  exact Finset.sum_eq_zero fun i hi => by rw [hc i hi, TensorProduct.tmul_zero]

theorem exists_fixed (π : Representation ℂ G W) (hπ : IsSmooth π) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (w : W) :
    ∃ w' ∈ fixed π K, ∀ T : W →ₗ[ℂ] V, (∀ k ∈ K, ∀ x, T (π k x) = T x) → T w = T w' := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let S : Subgroup K :=
    { carrier := {k | π (k : G) w = w}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hS : IsOpen (S : Set K) := (hπ w).preimage continuous_subtype_val
  haveI : Finite (K ⧸ S) := Subgroup.quotient_finite_of_isOpen S hS
  haveI : Fintype (K ⧸ S) := Fintype.ofFinite _
  let φ : K ⧸ S → W := fun q => Quotient.liftOn' q (fun k : K => π (k : G) w) (fun a b h => by
    have h' : a⁻¹ * b ∈ S := QuotientGroup.leftRel_apply.1 h
    have h2 : π ((a⁻¹ * b : K) : G) w = w := h'
    have h3 : π (b : G) w = π (a : G) w := by
      conv_rhs => rw [← h2]
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    exact h3.symm)
  have hφ : ∀ (k : K) (q : K ⧸ S), φ (k • q) = π (k : G) (φ q) := by
    intro k q
    induction q using QuotientGroup.induction_on with
    | H a =>
      show π ((k * a : K) : G) w = π (k : G) (π (a : G) w)
      rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  have hcard : ((Fintype.card (K ⧸ S) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨((Fintype.card (K ⧸ S) : ℕ) : ℂ)⁻¹ • ∑ q, φ q, ?_, fun T hT => ?_⟩
  · intro k
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [map_smul, map_sum]
    congr 1
    simp_rw [← hφ]
    exact Equiv.sum_comp (MulAction.toPerm k) φ
  · have h1 : ∀ q, T (φ q) = T w := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H a => exact hT _ a.2 w
    rw [map_smul, map_sum]
    simp only [h1, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

theorem exists_ev_eq (π : Representation ℂ G W) (hπ : IsAdmissible π) (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (T : W →ₗ[ℂ] V)
    (hT : ∀ k ∈ K, ∀ x, T (π k x) = T x) : ∃ t, ev V π t = T := by
  haveI : FiniteDimensional ℂ (fixed π K) := hπ.2 K hKo hKc
  have hle : LinearMap.range T ≤ (fixed π K).map T := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨w', hw', h⟩ := exists_fixed (V := V) π hπ.1 K hKc w
    exact ⟨w', hw', (h T hT).symm⟩
  haveI : FiniteDimensional ℂ (LinearMap.range T) := Submodule.finiteDimensional_of_le hle
  let b := Module.finBasis ℂ (LinearMap.range T)
  let l : _ → Module.Dual ℂ W := fun i => b.coord i ∘ₗ T.rangeRestrict
  have hl : ∀ i, l i ∈ smoothPart π.dual := fun i =>
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hKo.mem_nhds (one_mem K)) fun g hg => by
      refine LinearMap.ext fun x => ?_
      show l i (π g⁻¹ x) = l i x
      have : T.rangeRestrict (π g⁻¹ x) = T.rangeRestrict x :=
        Subtype.ext (hT _ (inv_mem hg) x)
      simp only [l, LinearMap.comp_apply, this])
  refine ⟨∑ i, (b i : V) ⊗ₜ[ℂ] (⟨l i, hl i⟩ : smoothPart π.dual), LinearMap.ext fun w => ?_⟩
  rw [map_sum, LinearMap.sum_apply]
  have h2 : ((∑ i, b.repr (T.rangeRestrict w) i • b i : LinearMap.range T) : V) = T w := by
    rw [b.sum_repr]
    rfl
  rw [Submodule.coe_sum] at h2
  exact h2

theorem ev_map {H : Type} [Group H] (σ : Representation ℂ H V) (π : Representation ℂ G W) (g : H) (h : G)
    (t : V ⊗[ℂ] smoothPart π.dual) (w : W) :
    ev V π (TensorProduct.map (σ g) (contra π h) t) w = σ g (ev V π t (π h⁻¹ w)) := by
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul v l => simp
end General

end GlobalTheory.ThetaGL.DualPair

open GlobalTheory.ThetaGL.DualPair in

theorem GlobalTheory.ThetaGL.omQuot_contra_of_thetaPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W), IsSmoothChar μ → IsAdmissible π → ThetaPair μ σ π → OmQuot μ σ (contra π) := by
  intro k _ _ _ _ r n μ V _ _ W _ _ σ π hμ hπ ⟨B, hB0, hB⟩
  obtain ⟨-, hmul, -, -, hop⟩ := om_isSmoothRepresentation k (Fin r) (Fin n) μ hμ
  have hone := (om_isSmoothRepresentation k (Fin r) (Fin n) μ hμ).1
  have hmem : ∀ Φ, B Φ ∈ LinearMap.range (ev V π) := by
    intro Φ
    let S : Subgroup (GL (Fin n) k) :=
      { carrier := {h | om μ (1 : GL (Fin r) k) h Φ.1 = Φ.1}
        one_mem' := hone _
        mul_mem' := fun {x y} hx hy => by
          show om μ (1 : GL (Fin r) k) (x * y) Φ.1 = Φ.1
          have := hmul 1 1 x y Φ.1
          rw [mul_one] at this
          rw [this, hy, hx]
        inv_mem' := fun {x} hx => by
          show om μ (1 : GL (Fin r) k) x⁻¹ Φ.1 = Φ.1
          have hx' : om μ (1 : GL (Fin r) k) x Φ.1 = Φ.1 := hx
          conv_lhs => rw [← hx']
          have := hmul 1 1 x⁻¹ x Φ.1
          rw [mul_one, inv_mul_cancel, hone] at this
          exact this.symm }
    have hSo : IsOpen (S : Set (GL (Fin n) k)) :=
      (hop Φ.1 Φ.2).preimage (Continuous.prodMk continuous_const continuous_id)
    have hKo : IsOpen ((S ⊓ KO k (Fin n) : Subgroup _) : Set (GL (Fin n) k)) :=
      hSo.inter SplitFlip.isOpen_KO
    have hKc : IsCompact ((S ⊓ KO k (Fin n) : Subgroup _) : Set (GL (Fin n) k)) :=
      SplitFlip.isCompact_KO.of_isClosed_subset
        (Subgroup.isClosed_of_isOpen _ hKo) Set.inter_subset_right
    obtain ⟨t, ht⟩ := exists_ev_eq π hπ _ hKo hKc (B Φ) fun h hh x => by
      have := hB 1 h Φ Φ (hh.1 : om μ (1 : GL (Fin r) k) h Φ.1 = Φ.1).symm x
      simpa using this
    exact ⟨t, ht⟩
  let e := LinearEquiv.ofInjective (ev V π) (ev_injective π)
  let f : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] V ⊗[ℂ] smoothPart π.dual :=
    e.symm.toLinearMap ∘ₗ B.codRestrict _ hmem
  have hf : ∀ Φ, ev V π (f Φ) = B Φ := fun Φ => by
    have := e.apply_symm_apply (B.codRestrict _ hmem Φ)
    exact congrArg Subtype.val this
  refine ⟨f, fun h0 => hB0 (LinearMap.ext fun Φ => ?_), fun g h Φ Φ' hΦ => ?_⟩
  · rw [← hf, h0]
    simp
  · apply ev_injective π
    refine LinearMap.ext fun w => ?_
    rw [ev_map, hf, hf, ← hB g h Φ Φ' hΦ (π h⁻¹ w), ← Module.End.mul_apply, ← map_mul]
    simp
