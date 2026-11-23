import Development.DiscreteGroups.GlobalIrreducibility.LConvCut

noncomputable section

open GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv

theorem alt_std_eq_zero {A : Type} [Ring A] [Algebra ℂ A] [Module.Finite ℂ A] {M : ℕ}
    (hM : Module.finrank ℂ A < M) (b : Fin M → A) :
    ∑ σ : Equiv.Perm (Fin M), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun i => b (σ i)).prod = 0 := by
  have hdep : ¬ LinearIndependent ℂ b := fun h => by
    have := h.fintype_card_le_finrank
    rw [Fintype.card_fin] at this
    omega
  have h := (MultilinearMap.alternatization (MultilinearMap.mkPiAlgebraFin ℂ M A)).map_linearDependent b hdep
  rw [MultilinearMap.alternatization_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [MultilinearMap.domDomCongr_apply, MultilinearMap.mkPiAlgebraFin_apply, Units.smul_def,
    Int.cast_smul_eq_zsmul]

theorem alt_isOpen_fix {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (v : V) (U : Subgroup G) (hU : IsOpen (U : Set G))
    (h : ∀ u ∈ U, ρ u v = v) : IsOpen {g | ρ g v = v} := by
  let T : Subgroup G :=
    { carrier := {g | ρ g v = v}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at ha hb ⊢
        rw [hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  exact Subgroup.isOpen_mono (H₁ := U) (H₂ := T) (fun u hu => h u hu) hU

theorem alt_star_eq {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G →* (H →L[ℂ] H)) (hπ : ∀ g x, ‖π g x‖ = ‖x‖) (g : G) : star (π g) = π g⁻¹ := by
  have hin : ∀ x y, inner ℂ (π g x) (π g y) = inner ℂ x y := fun x y =>
    LinearIsometry.inner_map_map ⟨(π g : H →ₗ[ℂ] H), hπ g⟩ x y
  have h1 : star (π g) * π g = 1 := by
    ext x
    refine ext_inner_left ℂ fun v => ?_
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, hin, ContinuousLinearMap.one_apply]
  calc star (π g) = star (π g) * (π g * π g⁻¹) := by rw [← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = π g⁻¹ := by rw [← mul_assoc, h1, one_mul]

theorem alt_avg {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (hKc : IsCompact (K : Set G)) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G →* (H →L[ℂ] H)) (e : H →L[ℂ] H) (heK : ∀ κ ∈ K, e * π κ = e)
    (hfix : ∀ x, (∀ κ ∈ K, π κ x = x) → e x = x)
    (Z : Submodule ℂ (H →L[ℂ] H)) (hZ : ∀ κ ∈ K, ∀ z ∈ Z, π κ * z ∈ Z)
    (y : H →L[ℂ] H) (hy : y ∈ Z) (U : Subgroup G) (hUo : IsOpen (U : Set G)) (hU : ∀ u ∈ U, π u * y = y) :
    e * y ∈ Z := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hU'o : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.coe_subgroupOf]
    exact hUo.preimage continuous_subtype_val
  haveI : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hU'o
  haveI : Fintype (K ⧸ U.subgroupOf K) := Fintype.ofFinite _
  let F : K ⧸ U.subgroupOf K → (H →L[ℂ] H) := fun q => Quotient.liftOn' q (fun κ : K => π κ * y) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ U.subgroupOf K := QuotientGroup.leftRel_apply.mp hab
    have hu : ((a⁻¹ * b : K) : G) ∈ U := Subgroup.mem_subgroupOf.mp hab'
    have hb : (b : G) = (a : G) * ((a⁻¹ * b : K) : G) := by simp
    show π a * y = π b * y
    rw [hb, map_mul, mul_assoc, hU _ hu])
  have hF : ∀ κ : K, F (κ : K ⧸ U.subgroupOf K) = π κ * y := fun κ => rfl
  have hFZ : ∀ q, F q ∈ Z := fun q => QuotientGroup.induction_on q fun κ => by
    rw [hF]; exact hZ κ κ.2 y hy
  have hFe : ∀ q, e * F q = e * y := fun q => QuotientGroup.induction_on q fun κ => by
    rw [hF, ← mul_assoc, heK κ κ.2]
  have hFs : ∀ (κ : K) q, π κ * F q = F (κ • q) := fun κ q => QuotientGroup.induction_on q fun a => by
    rw [MulAction.Quotient.smul_mk, hF, hF, smul_eq_mul, Subgroup.coe_mul, map_mul, mul_assoc]
  have hwK : ∀ κ : K, π κ * ∑ q, F q = ∑ q, F q := by
    intro κ
    rw [Finset.mul_sum]
    simp_rw [hFs κ]
    exact Equiv.sum_comp (MulAction.toPerm κ) F
  have hew : e * ∑ q, F q = ∑ q, F q := by
    ext x
    rw [ContinuousLinearMap.mul_apply]
    exact hfix _ fun κ hκ => congrArg (fun T : H →L[ℂ] H => T x) (hwK ⟨κ, hκ⟩)
  have hcard : e * ∑ q, F q = (Fintype.card (K ⧸ U.subgroupOf K) : ℂ) • (e * y) := by
    rw [Finset.mul_sum]
    simp_rw [hFe]
    rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hn : (Fintype.card (K ⧸ U.subgroupOf K) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have : e * y = (Fintype.card (K ⧸ U.subgroupOf K) : ℂ)⁻¹ • ∑ q, F q := by
    rw [← hew, hcard, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rw [this]
  exact Z.smul_mem _ (Z.sum_mem fun q _ => hFZ q)

end DiscreteGroups.sglob.LConv
