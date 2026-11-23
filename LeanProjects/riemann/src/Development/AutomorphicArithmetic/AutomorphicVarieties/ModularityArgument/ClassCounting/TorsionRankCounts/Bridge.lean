import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCount

open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up CategoryTheory

private theorem d_eq (A G : Type) [CommRing A] [Group G] (k : ℕ) (z : Ch A G (k + 1)) :
    (groupHomology.inhomogeneousChains (Rep.trivial A G A)).d (k + 1) k z = bd A G k z := by
  rw [groupHomology.inhomogeneousChains.d_def]
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | single g c =>
    rw [groupHomology.inhomogeneousChains.d_single]
    simp [bd, Finsupp.linearCombination_single, Finset.smul_sum, smul_smul, mul_comm c]

private theorem i_inj (A G : Type) [CommRing A] [Group G] (k : ℕ) :
    Function.Injective (groupHomology.iCycles (Rep.trivial A G A) k) :=
  (ModuleCat.mono_iff_injective (groupHomology.iCycles (Rep.trivial A G A) k)).1 inferInstance

private noncomputable def mk (A G : Type) [CommRing A] [Group G] (k : ℕ) :
    LinearMap.ker (bd A G k) →ₗ[A] groupHomology.cycles (Rep.trivial A G A) (k + 1) where
  toFun z := groupHomology.cyclesMk (k + 1) k (by simp) z.1 ((d_eq A G k z.1).trans z.2)
  map_add' a b := i_inj A G _ (by rw [map_add, groupHomology.iCycles_mk, groupHomology.iCycles_mk, groupHomology.iCycles_mk]; rfl)
  map_smul' c a := i_inj A G _ (by rw [map_smul, groupHomology.iCycles_mk, groupHomology.iCycles_mk]; rfl)

private theorem i_mk (A G : Type) [CommRing A] [Group G] (k : ℕ) (z : LinearMap.ker (bd A G k)) :
    groupHomology.iCycles (Rep.trivial A G A) (k + 1) (mk A G k z) = z.1 := by
  simp only [_root_.mk, LinearMap.coe_mk, AddHom.coe_mk]
  exact groupHomology.iCycles_mk _ _ _

private theorem pi_zero (A G : Type) [CommRing A] [Group G] (k : ℕ) (z : LinearMap.ker (bd A G k)) :
    groupHomology.π (Rep.trivial A G A) (k + 1) (mk A G k z) = 0 ↔ Bd z.1 := by
  let K := groupHomology.inhomogeneousChains (Rep.trivial A G A)
  have hex : (ShortComplex.mk (K.toCycles (k + 2) (k + 1)) (K.homologyπ (k + 1))
      (K.toCycles_comp_homologyπ _ _)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel (k + 2) (k + 1) (by simp))
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have hti : ∀ y, groupHomology.iCycles (Rep.trivial A G A) (k + 1) (K.toCycles (k + 2) (k + 1) y) =
      bd A G (k + 1) y := by
    intro y
    rw [← d_eq A G (k + 1) y, ← K.toCycles_i (k + 2) (k + 1)]
    rfl
  constructor
  · intro h
    obtain ⟨y, hy⟩ := hex _ h
    refine ⟨y, ?_⟩
    have := congrArg (groupHomology.iCycles (Rep.trivial A G A) (k + 1)) hy
    rw [i_mk] at this
    simpa [hti] using this
  · rintro ⟨y, hy⟩
    have hm : mk A G k z = K.toCycles (k + 2) (k + 1) y := by
      apply i_inj
      rw [i_mk, hti, hy]
    rw [hm]
    exact congrArg (fun f => f y) (congrArg ModuleCat.Hom.hom (K.toCycles_comp_homologyπ (k + 2) (k + 1)))

theorem UpperTheory.V.ZK.Up.bridge : UpperTheory.V.ZK.Up.Bridge := by
  intro k
  refine ⟨fun G _ => ((groupHomology.π (Rep.trivial ℤ G ℤ) (k + 1)).hom ∘ₗ mk ℤ G k).toAddMonoidHom,
    ?_, ?_, ?_⟩
  · intro G _ x
    refine groupHomology_induction_on x ?_
    intro c
    have hc : groupHomology.iCycles (Rep.trivial ℤ G ℤ) (k + 1) c ∈ LinearMap.ker (bd ℤ G k) := by
      rw [LinearMap.mem_ker, ← d_eq]
      exact congrArg (fun g => g.hom c)
        ((groupHomology.inhomogeneousChains (Rep.trivial ℤ G ℤ)).iCycles_d (k + 1) k)
    refine ⟨⟨_, hc⟩, ?_⟩
    have hm : mk ℤ G k ⟨_, hc⟩ = c := i_inj ℤ G _ (by rw [i_mk])
    simp [hm]
  · intro G _ z
    exact pi_zero ℤ G k z
  · intro G H _ _ f z z' hz
    simp only [LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp, Function.comp_apply, grpHMap]
    rw [groupHomology.π_map_apply]
    congr 1
    apply i_inj
    have h1 := congrArg (fun g => g.hom (mk ℤ G k z))
      (HomologicalComplex.cyclesMap_i (groupHomology.chainsMap f (trivHom f)) (k + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    rw [i_mk, hz]
    erw [h1, i_mk]
    induction (z : Ch ℤ G (k + 1)) using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | single g a =>
      rw [groupHomology.chainsMap_f_single]
      simp only [cm, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rfl
