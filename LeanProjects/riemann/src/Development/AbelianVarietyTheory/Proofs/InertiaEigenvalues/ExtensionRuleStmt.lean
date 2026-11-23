import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DictKFree

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
open TensorProduct

noncomputable section

namespace GlobalTheory.ExtDict

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

theorem exists_ext_cocycle [IsTopologicalRing LL] {T Y Z : LocLat G Qp LL O}
    (ι : LatHom T.L Y.L) (π : LatHom Y.L Z.L) (hs : IsSESLat (Qp := Qp) ι π)
    (hZ : ∀ g z, Z.ρ g z = z) (x : ↥Y.L.T) :
    ∃ c : ↥(latticeCocycles T.L), ∀ g, ι.f ((c : G → T.V) g) = Y.ρ g (x : Y.V) - (x : Y.V) := by
  obtain ⟨h1, -, -, h4, h5⟩ := hs
  obtain ⟨r, hr⟩ := ι.f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 h1)
  have hr' : ∀ y, r (ι.f y) = y := fun y => LinearMap.congr_fun hr y
  have hval : ∀ g, ι.f (r (Y.ρ g (x : Y.V) - (x : Y.V))) = Y.ρ g (x : Y.V) - (x : Y.V) := by
    intro g
    obtain ⟨y, hy⟩ := (h4 (Y.ρ g (x : Y.V) - (x : Y.V))).1 (by rw [map_sub, π.equiv, hZ, sub_self])
    rw [← hy, hr']
  have : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
  have hrc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  have : IsTopologicalAddGroup Y.V := IsModuleTopology.topologicalAddGroup LL Y.V
  refine ⟨⟨fun g => r (Y.ρ g (x : Y.V) - (x : Y.V)), ⟨?_, fun g h => ?_⟩, fun g _ => ?_⟩, hval⟩
  · exact hrc.comp ((Y.cont x).sub continuous_const)
  · apply h1
    rw [map_add, ι.equiv, hval, hval, hval, map_mul, Module.End.mul_apply, map_sub]
    abel
  · apply h5
    change ι.f (r _) ∈ _
    rw [hval]
    exact Y.L.T.sub_mem (Y.actT g x).2 x.2

variable {K₀ K : Type} [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem exists_unit_fixed (E : EtTie W RA RW inclR φR gR πA) (u : ↥W.one.L.T) :
    ∃ e₀ ∈ tableLineDegreeTwo.fixDD W W.one, E.jD W.one e₀ = (1 : RW) ⊗ₜ[O] u := by
  obtain ⟨e₁, f₀, hf₀, hj, -⟩ := E.one_e
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
    (hf₀ ▸ Submodule.mem_top : u ∈ Submodule.span O {f₀})
  have hje : E.jD W.one (c • e₁) = (1 : RW) ⊗ₜ[O] u := by
    rw [map_smul, hj, ← hc, TensorProduct.tmul_smul]
  have hφ : W.φD W.one (c • e₁) = c • e₁ := by
    apply E.jD_inj
    rw [E.jD_φ, hje]
    simp [TWmap]
  have hγ : ∀ g, W.γD W.one g (c • e₁) = c • e₁ := by
    intro g
    obtain ⟨g, rfl⟩ := W.resΓ_onto g
    apply E.jD_inj
    have hact : W.one.actT g u = u := Subtype.ext (W.one_triv g u)
    rw [E.jD_act, hje]
    simp [TWact, hact]
  refine ⟨c • e₁, ⟨⟨?_, ?_⟩, ?_⟩, hje⟩
  · exact LinearMap.mem_ker.2 (sub_eq_zero.2 hφ)
  · exact LinearMap.mem_ker.2 (sub_eq_zero.2 (hγ _))
  · exact (Submodule.mem_iInf _).2 fun δ => (Submodule.mem_iInf _).2 fun _ =>
      LinearMap.mem_ker.2 (sub_eq_zero.2 (hγ δ))

end Generic

theorem herrExt_of_dense (S : LocalSituation.Sit) (E : S.Comparison₂) [IsTopologicalRing S.LL] [T2Space S.LL]
    (hR : Function.Injective (algebraMap S.O S.RW))
    (hDel : S.PD.p = 2 → S.W.DelF = {1})
    (hdens : ∀ A : Subgroup S.G, IsClosed (A : Set S.G) → (∀ g, S.W.resΓ g ∈ S.W.DelF → g ∈ A) →
      (∀ g, S.W.resΓ g = S.W.gamK → g ∈ A) → ∀ g, g ∈ A) : tableLineDegreeTwo.HerrExt S.W E := by
  refine ⟨exists_unit_fixed E, fun T Tp ι π hs x u hu e hδ he p h1 h2 => ?_⟩
  obtain ⟨c, hc⟩ := exists_ext_cocycle ι π hs S.W.one_triv x
  exact ⟨c, (dict_of_dense S E hR hDel hdens T Tp _ ι π hs x u e hu he hδ p h1 h2 c hc).symm, hc⟩

theorem extension_rule (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) :
    InvariantsGenerators.HerrExtensionEtale D HW F := by
  intro l _ K LL hA
  let S := LocalSituation.sit D.loc HW l (D.locA l) K 1 LL hA.2.2
  let E : S.Comparison₂ := ((F l).E K 1 LL hA.2.2).tie
  have : IsTopologicalRing S.LL := inferInstanceAs (IsTopologicalRing ↥LL.1.toSubring)
  have : T2Space S.LL := inferInstanceAs (T2Space ↥LL.1)
  exact herrExt_of_dense S E (algebraMap_RW_injective LL)
    (fun h2 => absurd (((D.loc l).PD_p K).symm.trans h2) hA.2.1)
    (dense_DelF_gamK (D.loc l) S.W (D.locA l) fun h2 => absurd h2 hA.2.1)

theorem extension_rule_stmt :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), InvariantsGenerators.HerrExtensionEtaleTheorem D HW F :=
  fun D HW F _ => extension_rule D HW F

end GlobalTheory.ExtDict
