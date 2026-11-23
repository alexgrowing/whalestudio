import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

section

variable {O A X τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup X]
  {𝒜 : X → Submodule O A} {x : A →ₐ[O] O} {wt : τ → X} {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)}

private noncomputable def crLin (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) :
    A →ₗ[O] FractionRing O :=
  ((MvPowerSeries.coeff (Finsupp.single i 1)).restrictScalars O) ∘ₗ φ.toLinearMap

private theorem crLin_apply (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) (f : A) :
    crLin φ i f = MvPowerSeries.coeff (Finsupp.single i 1) (φ f) := rfl

private theorem crLin_sat (h : IsChart 𝒜 x wt φ) (i : τ) : ∀ f ∈ satSq x, crLin φ i f = 0 := by
  classical
  have h2 : ∀ f ∈ RingHom.ker x ^ 2, crLin φ i f = 0 := by
    intro f hf
    rw [sq] at hf
    refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
    have ha' : MvPowerSeries.coeff 0 (φ a) = 0 := by
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.const, show x a = 0 from ha, map_zero]
    have hb' : MvPowerSeries.coeff 0 (φ b) = 0 := by
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.const, show x b = 0 from hb, map_zero]
    rw [crLin_apply, map_mul, MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]
    simp [Finset.Nat.antidiagonal_succ, ha', hb']
  rintro f ⟨c, hc, hf⟩
  have := h2 _ hf
  rw [map_smul] at this
  exact (smul_eq_zero.1 this).resolve_left hc

private theorem crLin_wt (h : IsChart 𝒜 x wt φ) (i : τ) {j : X} (hij : wt i ≠ j)
    {f : A} (hf : f ∈ 𝒜 j) : crLin φ i f = 0 :=
  h.graded j f hf _ (by simpa [Finsupp.weight_single] using hij)

private theorem crLin_const (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) (c : O) :
    crLin φ i (algebraMap O A c) = 0 := by
  classical
  rw [crLin_apply, AlgHom.commutes, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, if_neg (by simp)]

private theorem cr_fixed (h : IsChart 𝒜 x wt φ) {j : X} (hj : j ≠ 0) {f : A} (hf : f ∈ 𝒜 j) : x f = 0 := by
  have h1 := h.graded j f hf 0 (by simpa using hj.symm)
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.const] at h1
  exact IsFractionRing.injective O (FractionRing O) (by rw [h1, map_zero])

private theorem crLin_proj [DecidableEq X] [GradedAlgebra 𝒜] (h : IsChart 𝒜 x wt φ) (i : τ) {j : X}
    (hij : wt i = j) (f : A) : crLin φ i (DirectSum.decompose 𝒜 f j) = crLin φ i f := by
  induction f using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous k f =>
    by_cases hk : k = j
    · subst hk
      rw [DirectSum.decompose_of_mem_same 𝒜 f.2]
    · rw [DirectSum.decompose_of_mem_ne 𝒜 f.2 hk, map_zero, crLin_wt h i (fun h' => hk (h'.symm.trans hij)) f.2]
  | add f g hf hg => simp [hf, hg]

private theorem cr_comp [DecidableEq X] [GradedAlgebra 𝒜] (h : IsChart 𝒜 x wt φ) (j : X) (f : A) :
    ∃ g : A, g ∈ 𝒜 j ∧ x g = 0 ∧ ∀ i, wt i = j → crLin φ i g = crLin φ i f := by
  have hm : (DirectSum.decompose 𝒜 f j : A) ∈ 𝒜 j := (DirectSum.decompose 𝒜 f j).2
  by_cases hj : j = 0
  · subst hj
    refine ⟨(DirectSum.decompose 𝒜 f 0 : A) - algebraMap O A (x (DirectSum.decompose 𝒜 f 0 : A)),
      sub_mem hm (SetLike.algebraMap_mem_graded 𝒜 _), by simp, fun i hi => ?_⟩
    rw [map_sub, crLin_const, sub_zero, crLin_proj h i hi]
  · exact ⟨_, hm, cr_fixed h hj hm, fun i hi => crLin_proj h i hi f⟩

end

theorem UpperTheory.V.Alg.chart_rank :
    ∀ (O A X : Type) [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup X] [DecidableEq X] (𝒜 : X → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O) (τ : Type) [Fintype τ] (wt : τ → X) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart 𝒜 x wt φ →
      ∀ j, Module.finrank O (cotLat x 𝒜 j) = Nat.card {i // wt i = j} := by
  intro O A X _ _ _ _ _ _ 𝒜 _ x τ _ wt φ h j
  classical
  rw [Nat.card_eq_fintype_card]
  let ψ : cotLat x 𝒜 j →ₗ[O] ({i // wt i = j} → FractionRing O) :=
    LinearMap.pi fun i => ((satSq x).liftQ (crLin φ i.1) (crLin_sat h i.1)) ∘ₗ (cotLat x 𝒜 j).subtype
  have hψ : ∀ (f : A) (hf : (satSq x).mkQ f ∈ cotLat x 𝒜 j) i, ψ ⟨_, hf⟩ i = crLin φ i.1 f := fun f hf i => rfl
  apply Module.finrank_eq_of_rank_eq
  apply le_antisymm
  · have hinj : Function.Injective ψ := by
      rw [injective_iff_map_eq_zero]
      rintro ⟨_, f, hf, rfl⟩ h0
      apply Subtype.ext
      refine (Submodule.Quotient.mk_eq_zero _).2 (h.inj f hf.2 fun i => ?_)
      by_cases hi : wt i = j
      · exact congrFun h0 ⟨i, hi⟩
      · exact crLin_wt h i hi hf.1
    have h1 := LinearMap.rank_le_of_injective ψ hinj
    rwa [← IsLocalization.rank_eq (FractionRing O) (nonZeroDivisors O) le_rfl (N := {i // wt i = j} → FractionRing O),
      rank_fun'] at h1
  · choose g hg hg' using h.onto
    choose p hp hpx hpl using cr_comp h j
    have hm : ∀ i, (satSq x).mkQ (p (g i)) ∈ cotLat x 𝒜 j := fun i => ⟨_, ⟨hp _, hpx _⟩, rfl⟩
    have hli : LinearIndependent O fun i : {i // wt i = j} => (⟨_, hm i.1⟩ : cotLat x 𝒜 j) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have h1 := congrFun (congrArg ψ hc) i
      rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i, map_zero, map_smul, Pi.smul_apply, hψ,
        hpl _ _ i.2] at h1
      · exact (smul_eq_zero.1 h1).resolve_right (hg i.1)
      · intro k _ hk
        rw [map_smul, Pi.smul_apply, hψ, hpl _ _ i.2, crLin_apply,
          hg' k.1 i.1 (fun h' => hk (Subtype.ext h').symm), smul_zero]
      · simp
    have h2 := hli.cardinal_le_rank
    rwa [Cardinal.mk_fintype] at h2
