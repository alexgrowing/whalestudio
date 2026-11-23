import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.AdjMulSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SmallExt

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

theorem UpperTheory.V.Ws.Pp.smallFlag :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (r : Γ →* M4 𝔞.V) (u : M4 𝔞.V), 𝔞.Small (⟨r, fun _ => 1⟩ : PD Unit _ _) → 𝔞.Small (⟨r, fun _ => u⟩ : PD Unit _ _) := by
  classical
  intro l _ 𝔞 Γ _ _ r u hS
  unfold Amb.Small at hS ⊢
  obtain ⟨A, _, _, _, f, P₁, hf, hc, hP⟩ := hS
  obtain ⟨A', _, _, _, f', g, hf', hcomp, hcl⟩ :=
    smallExt 𝔞 A f hf (Finset.univ.image (fun ij : Fin 4 × Fin 4 => 𝔞.toK (u ij.1 ij.2)))
  have hinj : Function.Injective f' := hf'.inj
  have hloc : IsLocalHom g := by
    have := Amb.IsDvr.loc hf
    refine ⟨fun z hz => isUnit_of_map_unit f z ?_⟩
    rw [← hcomp]
    exact hz.map f'
  have hle : (maximalIdeal A).map g ≤ maximalIdeal A' := by
    rw [Ideal.map_le_iff_le_comap]
    intro z hz
    simp only [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff] at hz ⊢
    exact fun h => hz (isUnit_of_map_unit g z h)
  have huR : ∀ i j, u i j ∈ f'.range := fun i j =>
    hcl _ (Subfield.subset_closure (Or.inr
      (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j))))))
  let e : 𝔞.V → A' := Function.invFun f'
  have hE : ∀ i j, f' (e (u i j)) = u i j := fun i j => by
    obtain ⟨y, hy⟩ := huR i j
    exact Function.invFun_eq ⟨y, hy⟩
  have hr : ∀ γ i j, f (P₁.r γ i j) = r γ i j := fun γ i j =>
    congrArg (fun P => PD.r P γ i j) hP
  refine ⟨A', inferInstance, inferInstance, inferInstance, f',
    ⟨(P₁.map g).r, fun _ => u.map e⟩, hf', ?_, ?_⟩
  · unfold PD.Cont
    intro i j N
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hA := (IsLocallyConstant.iff_eventually_eq _).1 (hc i j N) x
    filter_upwards [hA] with y hy
    rw [Ideal.Quotient.eq] at hy ⊢
    change g (P₁.r y i j) - g (P₁.r x i j) ∈ _
    rw [← map_sub]
    have h2 := Ideal.mem_map_of_mem g hy
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono hle _ h2
  · apply PD.ext
    · ext γ i j
      change ((f' (g (P₁.r γ i j)) : 𝔞.K)) = (r γ i j : 𝔞.K)
      rw [← RingHom.comp_apply f' g, hcomp, hr]
    · ext v i j
      exact congrArg Subtype.val (hE i j)
