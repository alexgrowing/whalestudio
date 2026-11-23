import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestBump
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ValNhds
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.UnitCont
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {G H : Type} [Group G] [Group H]

private def stab (ι : H →* G) (f : G → ℂ) : Subgroup H where
  carrier := {k | ∀ g, f (g * ι k) = f g}
  one_mem' := fun g => by rw [map_one, mul_one]
  mul_mem' := fun {k l} hk hl g => by rw [map_mul, ← mul_assoc, hl, hk]
  inv_mem' := fun {k} hk g => by
    rw [← hk (g * ι k⁻¹), mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

variable [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ]

private theorem summ (u : G → ℂ) (hu : HasCompactSupport u) (g : G) : Summable fun γ : Γ => u (γ * g) := by
  have hd : _root_.IsDiscrete (Γ : Set G) := ⟨inferInstanceAs (DiscreteTopology Γ)⟩
  have ht := Subgroup.tendsto_coe_cofinite_of_discrete Γ hd
  have hK : IsCompact ((fun x => x * g⁻¹) '' tsupport u) := IsCompact.image hu (by fun_prop)
  have hf := ht hK.compl_mem_cocompact
  rw [Filter.mem_map, Filter.mem_cofinite] at hf
  refine summable_of_finite_support (hf.subset fun γ hγ => ?_)
  simp only [Set.mem_compl_iff, Set.mem_preimage, not_not]
  exact ⟨γ * g, subset_tsupport _ hγ, by simp⟩

private theorem orb_ne (u : G → ℂ) (hu : HasCompactSupport u) (hp : ∀ g, ∃ t : ℝ, 0 ≤ t ∧ u g = t) (g : G)
    (γ : G) (hγ : γ ∈ Γ) (h : u (γ * g) ≠ 0) : GlobalTheory.AutomorphicL2Unitary.orbitSum Γ u g ≠ 0 := by
  have hs := summ Γ u hu g
  have h0 : ∀ x, 0 ≤ (u x).re := fun x => by
    obtain ⟨t, ht, e⟩ := hp x
    rw [e, Complex.ofReal_re]; exact ht
  have h1 : 0 < (u (γ * g)).re := by
    obtain ⟨t, ht, e⟩ := hp (γ * g)
    rw [e] at h ⊢
    rw [Complex.ofReal_re]
    exact lt_of_le_of_ne ht fun e' => h (by rw [← e', Complex.ofReal_zero])
  intro hz
  have h2 := congrArg Complex.re hz
  rw [GlobalTheory.AutomorphicL2Unitary.orbitSum, Complex.re_tsum hs, Complex.zero_re] at h2
  exact (Summable.tsum_pos (Complex.hasSum_re hs.hasSum).summable (fun δ => h0 _) ⟨γ, hγ⟩ h1).ne' h2

end

private theorem lev_iff {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (φ : Sm E a) :
    HasLev φ ↔ IsOpen (stab (finGL E a) φ.1 : Set (GL (Fin a) (Af E))) := by
  have : {k | act (.fin k) φ = φ} = (stab (finGL E a) φ.1 : Set (GL (Fin a) (Af E))) := by
    ext k
    exact ⟨fun h g => congrFun (congrArg Subtype.val h) g, fun h => Subtype.ext (funext h)⟩
  rw [HasLev, this]

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.orbLift :
    UpperTheory.V.Cj.H.OrbLift := by
  intro E _ _ _ a φ hφ hL C hC hs
  obtain ⟨u, hu, hp, hne, -⟩ := testBump E a C Set.univ hC isOpen_univ (Set.subset_univ _)
  obtain ⟨w, hw, ew⟩ := orbSm E a u hu
  have hZ : IsClosed ((latticeGL E a : Set (GA E a)) * C) :=
    IsClosed.mul_right_of_isCompact Subgroup.isClosed_of_discrete hC
  have hwZ : ∀ g ∈ (latticeGL E a : Set (GA E a)) * C, w.1 g ≠ 0 := by
    rintro _ ⟨γ, hγ, c, hc, rfl⟩
    rw [ew]
    refine orb_ne _ u.1 hu.1 hp _ γ⁻¹ (inv_mem hγ) ?_
    rw [inv_mul_cancel_left]
    exact hne c hc
  have hφZ : ∀ g ∉ (latticeGL E a : Set (GA E a)) * C, φ.1 g = 0 := by
    intro g hg
    by_contra h
    obtain ⟨γ, hγ, hc⟩ := hs g h
    exact hg ⟨γ⁻¹, inv_mem hγ, γ * g, hc, inv_mul_cancel_left γ g⟩
  have hq := (smDiv E a φ u w).2 _ hZ hφZ hwZ
  have hf := (smDiv E a ⟨_, hq⟩ u w).1
  refine ⟨⟨_, hf⟩, ⟨HasCompactSupport.mul_left hu.1, ?_⟩, ?_⟩
  · rw [lev_iff]
    refine Subgroup.isOpen_mono
      (H₁ := stab (finGL E a) φ.1 ⊓ (stab (finGL E a) w.1 ⊓ stab (finGL E a) u.1)) ?_ ?_
    · rintro k ⟨h1, h2, h3⟩ g
      show φ.1 _ / w.1 _ * u.1 _ = φ.1 _ / w.1 _ * u.1 _
      rw [h1 g, h2 g, h3 g]
    · exact ((lev_iff φ).1 hφ).inter (((lev_iff w).1 hw).inter ((lev_iff u).1 hu.2))
  · funext g
    have hwL : GlobalTheory.AutomorphicL2Unitary.LeftInv (latticeGL E a) w.1 := ew ▸ GlobalTheory.AutomorphicL2Unitary.leftInv_orbitSum u.1
    have e : GlobalTheory.AutomorphicL2Unitary.orbitSum (latticeGL E a) (fun g => φ.1 g / w.1 g * u.1 g) g = φ.1 g / w.1 g * w.1 g := by
      conv_rhs => rw [congrFun ew g]
      rw [GlobalTheory.AutomorphicL2Unitary.orbitSum, GlobalTheory.AutomorphicL2Unitary.orbitSum, ← tsum_mul_left]
      refine tsum_congr fun γ => ?_
      rw [hL γ γ.2, hwL γ γ.2, congrFun ew g, GlobalTheory.AutomorphicL2Unitary.orbitSum]
    refine Eq.trans ?_ e.symm
    by_cases h : g ∈ (latticeGL E a : Set (GA E a)) * C
    · rw [div_mul_cancel₀ _ (hwZ g h)]
    · rw [hφZ g h, zero_div, zero_mul]
