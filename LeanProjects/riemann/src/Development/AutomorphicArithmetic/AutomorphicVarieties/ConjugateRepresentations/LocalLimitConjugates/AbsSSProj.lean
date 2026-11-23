import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem exists_orthogonal_decomposition_of_isPos {W : Type} [AddCommGroup W] [Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (M : Submodule ℂ W) (hB : IsPos B M) (F K : Submodule ℂ W) (hF : F ≤ M) (hK : K ≤ F)
    [FiniteDimensional ℂ F] (v : W) (hv : v ∈ F) :
    ∃ a ∈ K, ∃ b ∈ F, v = a + b ∧ ∀ x ∈ K, B x b = 0 := by
  letI core : InnerProductSpace.Core ℂ F :=
    { inner := fun x y => B x y
      conj_inner_symm := fun x y => by
        show (starRingEnd ℂ) (B y x) = B x y
        rw [hB.herm]; simp
      re_inner_nonneg := fun x => hB.nonneg x (hF x.2)
      add_left := fun x y z => by
        show B (x + y : F) z = B x z + B y z
        simp
      smul_left := fun x y r => by
        show B (r • x : F) y = (starRingEnd ℂ) r * B x y
        simp
      definite := fun x hx => Subtype.ext (hB.definite x (hF x.2) hx) }
  letI : NormedAddCommGroup F := InnerProductSpace.Core.toNormedAddCommGroup (cd := core)
  letI : InnerProductSpace ℂ F := InnerProductSpace.ofCore (𝕜 := ℂ) (F := F) inferInstance
  let K' : Submodule ℂ F := K.comap F.subtype
  haveI : CompleteSpace K' := FiniteDimensional.complete ℂ K'
  obtain ⟨y, hy, z, hz, hyz⟩ := K'.exists_add_mem_mem_orthogonal ⟨v, hv⟩
  refine ⟨y, hy, z, z.2, congrArg Subtype.val hyz, fun x hx => ?_⟩
  have := (Submodule.mem_orthogonal K' z).1 hz ⟨x, hK hx⟩ hx
  exact this

private theorem orbit_of_compact_finite_of_open_stabilizer {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (n : W) (U V : Subgroup G)
    (hUc : IsCompact (U : Set G)) (hVo : IsOpen (V : Set G)) (hVn : ∀ u ∈ V, ρ u n = n) :
    ((fun u => ρ u n) '' (U : Set G)).Finite := by
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover (fun u : U => (fun g => (u : G)⁻¹ * g) ⁻¹' (V : Set G))
    (fun u => hVo.preimage (continuous_const.mul continuous_id))
    (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp [V.one_mem]⟩)
  apply ((t : Set U).toFinite.image (fun u : U => ρ (u : G) n)).subset
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨u, hu, hgu⟩ := Set.mem_iUnion₂.1 (ht hg)
  refine ⟨u, hu, ?_⟩
  have hg' : g = (u : G) * ((u : G)⁻¹ * g) := by group
  show ρ (u : G) n = ρ g n
  rw [hg', map_mul, Module.End.mul_apply, hVn _ hgu]

theorem UpperTheory.V.Cj.H.absSS :
    UpperTheory.V.Cj.H.AbsSS := by
  intro G W _ _ _ _ _ ρ M B hB hM hc hsm hfd N hNM hN
  have hρ : ∀ (g h : G) (x : W), ρ g (ρ h x) = ρ (g * h) x := by
    intro g h x
    rw [map_mul, Module.End.mul_apply]
  let N' : Submodule ℂ W :=
    { carrier := {w | w ∈ M ∧ ∀ n ∈ N, B n w = 0}
      add_mem' := fun {a b} ha hb => ⟨M.add_mem ha.1 hb.1, fun n hn => by simp [ha.2 n hn, hb.2 n hn]⟩
      zero_mem' := ⟨M.zero_mem, fun n _ => by simp⟩
      smul_mem' := fun r w hw => ⟨M.smul_mem r hw.1, fun n hn => by simp [hw.2 n hn]⟩ }
  have memN' : ∀ w, w ∈ N' ↔ w ∈ M ∧ ∀ n ∈ N, B n w = 0 := fun w => Iff.rfl
  refine ⟨N', fun w hw => ((memN' w).1 hw).1, ?_, ?_, ?_⟩
  · intro g w hw
    rw [memN'] at hw ⊢
    refine ⟨hM g w hw.1, fun n hn => ?_⟩
    obtain ⟨c, hcg⟩ := hc g
    have hn' : ρ g⁻¹ n ∈ N := hN _ _ hn
    have h1 : ρ g (ρ g⁻¹ n) = n := by rw [hρ, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← h1, hcg _ (hNM hn') _ hw.1, hw.2 _ hn', mul_zero]
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxN, hxN'⟩ := Submodule.mem_inf.1 hx
    rw [memN'] at hxN'
    exact (Submodule.mem_bot ℂ).2 (hB.definite x (hNM hxN) (hxN'.2 x hxN))
  · refine le_antisymm (sup_le hNM fun w hw => ((memN' w).1 hw).1) ?_
    intro v hv
    obtain ⟨U, hUo, hUc, hUv⟩ := hsm v hv
    haveI := hfd U hUo
    have hFM : Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x} ≤ M :=
      Submodule.span_le.2 fun x hx => hx.1
    have hFfix : ∀ x ∈ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x}, ∀ u ∈ U, ρ u x = x := by
      intro x hx u hu
      induction hx using Submodule.span_induction with
      | mem y hy => exact hy.2 u hu
      | zero => simp
      | add y z _ _ hy hz => simp [hy, hz]
      | smul r y _ hy => simp [hy]
    have hvF : v ∈ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x} :=
      Submodule.subset_span ⟨hv, hUv⟩
    obtain ⟨a, haK, b, hbF, hvab, hb⟩ :=
      exists_orthogonal_decomposition_of_isPos B M hB _ (N ⊓ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x}) hFM inf_le_right v hvF
    rw [hvab]
    refine Submodule.add_mem_sup (Submodule.mem_inf.1 haK).1 ((memN' b).2 ⟨hFM hbF, fun n hn => ?_⟩)
    have hinv : ∀ u ∈ U, ∀ x ∈ M, B (ρ u x) b = B x b := by
      intro u hu x hx
      obtain ⟨c, hcu⟩ := hc u
      have h1 := hcu x hx b (hFM hbF)
      rw [hFfix b hbF u hu] at h1
      by_cases hb0 : b = 0
      · simp [hb0]
      have h2 := hcu b (hFM hbF) b (hFM hbF)
      rw [hFfix b hbF u hu] at h2
      have hbb : B b b ≠ 0 := fun h => hb0 (hB.definite b (hFM hbF) h)
      have hc1 : c = 1 := by
        have h3 : (c - 1) * B b b = 0 := by rw [sub_mul, ← h2]; ring
        rcases mul_eq_zero.1 h3 with h | h
        · exact sub_eq_zero.1 h
        · exact absurd h hbb
      rw [h1, hc1, one_mul]
    obtain ⟨V, hVo, -, hVn⟩ := hsm n (hNM hn)
    have hfin := orbit_of_compact_finite_of_open_stabilizer ρ n U V hUc hVo hVn
    have hmemS : ∀ x, x ∈ hfin.toFinset ↔ ∃ g ∈ U, ρ g n = x := by
      intro x
      rw [Set.Finite.mem_toFinset]
      rfl
    have hSN : ∀ x ∈ hfin.toFinset, x ∈ N ∧ B x b = B n b := by
      intro x hx
      obtain ⟨g, hg, rfl⟩ := (hmemS x).1 hx
      exact ⟨hN g n hn, hinv g hg n (hNM hn)⟩
    have hsN : (∑ x ∈ hfin.toFinset, x) ∈ N := Submodule.sum_mem _ fun x hx => (hSN x hx).1
    have hsfix : ∀ u ∈ U, ρ u (∑ x ∈ hfin.toFinset, x) = ∑ x ∈ hfin.toFinset, x := by
      intro u hu
      rw [map_sum]
      refine Finset.sum_nbij' (fun x => ρ u x) (fun x => ρ u⁻¹ x) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
      · intro x hx
        obtain ⟨g, hg, rfl⟩ := (hmemS x).1 hx
        exact (hmemS _).2 ⟨u * g, U.mul_mem hu hg, (hρ u g n).symm⟩
      · intro x hx
        obtain ⟨g, hg, rfl⟩ := (hmemS x).1 hx
        exact (hmemS _).2 ⟨u⁻¹ * g, U.mul_mem (U.inv_mem hu) hg, (hρ u⁻¹ g n).symm⟩
      · intro x _
        rw [hρ, inv_mul_cancel, map_one, Module.End.one_apply]
      · intro x _
        rw [hρ, mul_inv_cancel, map_one, Module.End.one_apply]
    have hsF : (∑ x ∈ hfin.toFinset, x) ∈ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x} :=
      Submodule.subset_span ⟨hNM hsN, hsfix⟩
    have hzero := hb _ (Submodule.mem_inf.2 ⟨hsN, hsF⟩)
    rw [map_sum, LinearMap.sum_apply, Finset.sum_congr rfl fun x hx => (hSN x hx).2,
      Finset.sum_const, nsmul_eq_mul] at hzero
    have hcard : (hfin.toFinset.card : ℂ) ≠ 0 := by
      have : n ∈ hfin.toFinset := (hmemS n).2 ⟨1, U.one_mem, by simp⟩
      exact_mod_cast (Finset.card_pos.2 ⟨n, this⟩).ne'
    exact (mul_eq_zero.1 hzero).resolve_left hcard
