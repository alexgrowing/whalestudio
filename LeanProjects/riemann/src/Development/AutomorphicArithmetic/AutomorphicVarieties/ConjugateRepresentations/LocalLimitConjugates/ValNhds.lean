import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem inf_cont (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact Continuous.units_map _ ((continuous_const.sub continuous_const).add (continuous_id.matrix_map hs))

open scoped Matrix.Norms.Operator in
private theorem val_nhds (E : Type) [Field E] [NumberField E] (a : ℕ) (y : GL (Fin a) (Cinf E))
    {N : Set (GL (Fin a) (Cinf E))} (hN : N ∈ 𝓝 y) : (fun z : GL (Fin a) (Cinf E) => toL z.val) '' N ∈ 𝓝 (toL y.val) :=
  (Units.isOpenEmbedding_val (R := Matrix (Fin a) (Fin a) (Cinf E))).isOpenMap.image_mem_nhds hN

open scoped Pointwise in
private theorem loc_fin {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] {f : G → ℂ} (hf : HasCompactSupport f) (x : G) :
    ∃ s : Finset Γ, ∀ᶠ z in 𝓝 x, GlobalTheory.AutomorphicL2Unitary.orbitSum Γ f z = ∑ γ ∈ s, f (γ * z) := by
  obtain ⟨K, hK, hx⟩ := exists_compact_mem_nhds x
  have hS : {γ : Γ | (γ : G) ∈ tsupport f * K⁻¹}.Finite := GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (hf.isCompact.mul hK.inv)
  refine ⟨hS.toFinset, Filter.mem_of_superset hx fun z hz => tsum_eq_sum fun γ hγ => ?_⟩
  by_contra h
  exact hγ (hS.mem_toFinset.2 ⟨_, subset_tsupport f h, z⁻¹, Set.inv_mem_inv.2 hz, by simp⟩)

theorem UpperTheory.V.Cj.H.orbSm :
    UpperTheory.V.Cj.H.OrbSm := by
  intro E _ _ _ a u hu
  have hm : GlobalTheory.AutomorphicL2Unitary.orbitSum (latticeGL E a) u.1 ∈ Sm E a := by
    intro g x hx
    obtain ⟨y, hy⟩ := hx
    obtain rfl : x = toL y.val := hy.symm
    obtain ⟨s, hs⟩ := loc_fin (latticeGL E a) hu.1 (g * infGL E a y)
    have hc : Continuous fun z => g * infGL E a z := continuous_const.mul (inf_cont E a)
    have h1 := val_nhds E a y (hc.continuousAt.preimage_mem_nhds hs)
    refine ((ContDiffAt.sum (s := s) fun γ _ =>
      contDiffAt_chart u.2 (γ.1 * g) (val_mem_invSet y)).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [h1]
    rintro _ ⟨z, hz, rfl⟩
    simp only [chart_val, mul_assoc]
    exact hz
  refine ⟨⟨_, hm⟩, ?_, rfl⟩
  have key : ∀ k, act (.fin k) u = u → act (.fin k) (⟨_, hm⟩ : Sm E a) = ⟨_, hm⟩ := fun k hk =>
    Subtype.ext (funext fun g => tsum_congr fun γ => by
      have h : u.1 (γ.1 * g * finGL E a k) = u.1 (γ.1 * g) := congrFun (congrArg Subtype.val hk) _
      rw [← h, mul_assoc])
  let S : ∀ φ : Sm E a, Subgroup (GL (Fin a) (Af E)) := fun φ =>
    { carrier := {k | act (.fin k) φ = φ}
      one_mem' := Subtype.ext (funext fun g => by
        change φ.1 (g * finGL E a 1) = φ.1 g
        rw [map_one, mul_one])
      mul_mem' := fun {k l} hk hl => Subtype.ext (funext fun g => by
        have h1 : φ.1 (g * finGL E a k) = φ.1 g := congrFun (congrArg Subtype.val hk) _
        have h2 : φ.1 (g * finGL E a k * finGL E a l) = φ.1 (g * finGL E a k) := congrFun (congrArg Subtype.val hl) _
        change φ.1 (g * finGL E a (k * l)) = φ.1 g
        rw [map_mul, ← mul_assoc, h2, h1])
      inv_mem' := fun {k} hk => Subtype.ext (funext fun g => by
        have h1 : φ.1 (g * finGL E a k⁻¹ * finGL E a k) = φ.1 (g * finGL E a k⁻¹) :=
          congrFun (congrArg Subtype.val hk) _
        change φ.1 (g * finGL E a k⁻¹) = φ.1 g
        rw [← h1, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]) }
  exact Subgroup.isOpen_mono (H₁ := S u) (H₂ := S ⟨_, hm⟩) key hu.2
