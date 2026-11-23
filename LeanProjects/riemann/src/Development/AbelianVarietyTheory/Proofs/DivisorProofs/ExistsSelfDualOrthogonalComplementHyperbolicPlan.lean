import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeComapSubspaceRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeOfEqSpanFracSmul

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaneCompl

theorem gram_sum {D : D7} (S : HSp D) (a b : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (a i) * S.gram i j * b j = S.hT (S.frame.equivFun.symm a) (S.frame.equivFun.symm b) := by
  simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul, Formalism.BasicNotions.HSpace.gram, starRingEnd_apply]
  simp only [Finset.mul_sum, RingHom.id_apply]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_compl : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x y : S.V)
    (s : (D.host.E →+* ℂ) → ℕ × ℕ), IsSelfDualC S Λ → S.hT x x = 0 → S.hT y y = 0 → S.hT x y = 1 →
    (∀ z, GlobalTheory.SqStepK.InLat S Λ z → GlobalTheory.SqStepK.InLat S Λ (S.hT y z • x) ∧ GlobalTheory.SqStepK.InLat S Λ (S.hT x z • y)) →
    ∃ (S₁ : HSp D) (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V),
      GlobalTheory.SqStepK.PlaneSplit S S₁ Λ Λ₁ ι x y ∧ IsSelfDualC S₁ Λ₁ ∧ S₁.sig = s := by
  intro D S Λ x y s hΛ hxx hyy hxy hsplit
  have hyx : S.hT y x = 1 := by rw [← S.herm.eq x y, hxy, map_one]
  let W : Submodule D.host.E S.V := LinearMap.ker (LinearMap.pi fun j : Fin 2 => S.hT (![x, y] j))
  have hW : ∀ w, w ∈ W ↔ S.hT x w = 0 ∧ S.hT y w = 0 := by
    intro w
    simp only [W, LinearMap.mem_ker, funext_iff, LinearMap.pi_apply, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.zero_apply, Matrix.head_cons]
  have hdec : ∀ z, z - S.hT y z • x - S.hT x z • y ∈ W := by
    intro z
    rw [hW]
    constructor <;> simp [map_sub, hxx, hyy, hxy, hyx]
  have hind : LinearIndependent D.host.E ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (S.hT x) hab
    have h2 := congrArg (S.hT y) hab
    simp [hxx, hyy, hxy, hyx] at h1 h2
    exact ⟨h2, h1⟩
  have hrk : 2 + Module.finrank D.host.E W = S.rank := by
    have := GlobalTheory.WittLow.finrank_orth S.herm S.nondeg ![x, y] hind
    rw [S.rank_eq] at this
    exact this

  have hrad : ∀ v : W, (∀ w : W, S.hT w v = 0) → v = 0 := by
    intro v hv
    have hv' := (hW v).1 v.2
    apply Subtype.ext
    apply S.nondeg.2 (v : S.V)
    intro z
    have e : z = S.hT y z • x + (z - S.hT y z • x - S.hT x z • y) + S.hT x z • y := by abel
    have h0 := hv ⟨_, hdec z⟩
    rw [e, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, LinearMap.smul_apply, hv'.1, hv'.2, h0]
    simp
  let h' : W →ₗ⋆[D.host.E] W →ₗ[D.host.E] D.host.E := S.hT.domRestrict₁₂ W W
  have hs' : h'.IsSymm := ⟨fun a b => S.herm.eq _ _⟩
  have hnd' : h'.Nondegenerate := ⟨fun a ha => hrad a fun b => by
    rw [← S.herm.eq]; exact (congrArg _ (ha b)).trans (map_zero _), fun a ha => hrad a ha⟩
  let Λ' : Submodule (𝓞 D.host.E) S.V := Λ.comap ((S.frame.equivFun : S.V →ₗ[D.host.E] (Fin S.rank → D.host.E)).restrictScalars (𝓞 D.host.E))
  have hΛ'm : ∀ z, z ∈ Λ' ↔ GlobalTheory.SqStepK.InLat S Λ z := fun z => Iff.rfl
  have hΛ'lat : Submodule.IsLattice D.host.E Λ' := GlobalTheory.ColRows.isLattice_comap_equiv S.frame.equivFun Λ hΛ.1
  have hΛ'd : ∀ z, z ∈ Λ' ↔ ∀ w ∈ Λ', ∃ b : 𝓞 D.host.E, (b : D.host.E) = S.hT w z := by
    intro z
    rw [hΛ'm, GlobalTheory.SqStepK.InLat, hΛ.2]
    constructor
    · intro h w hw
      obtain ⟨b, hb⟩ := h _ hw
      exact ⟨b, by rw [hb, gram_sum]; simp⟩
    · intro h a ha
      obtain ⟨b, hb⟩ := h (S.frame.equivFun.symm a) (by rw [hΛ'm, GlobalTheory.SqStepK.InLat, LinearEquiv.apply_symm_apply]; exact ha)
      exact ⟨b, by rw [hb, gram_sum]; simp⟩
  let L0 : Submodule (𝓞 D.host.E) W := Λ'.comap (W.subtype.restrictScalars (𝓞 D.host.E))
  have hL0m : ∀ u : W, u ∈ L0 ↔ (u : S.V) ∈ Λ' := fun u => Iff.rfl
  have hL0lat : Submodule.IsLattice D.host.E L0 := GlobalTheory.isLattice_comap_subtype_ringOfIntegers Λ' hΛ'lat W
  have hwz : ∀ z, z ∈ Λ' → z - S.hT y z • x - S.hT x z • y ∈ Λ' := by
    intro z hz
    obtain ⟨hs1, hr1⟩ := hsplit z ((hΛ'm z).1 hz)
    rw [hΛ'm, GlobalTheory.SqStepK.InLat, map_sub, map_sub]
    exact Λ.sub_mem (Λ.sub_mem hz hs1) hr1
  have hL0d : ∀ u : W, u ∈ L0 ↔ ∀ u' ∈ L0, ∃ b : 𝓞 D.host.E, (b : D.host.E) = S.hT u' u := by
    intro u
    have hu := (hW u).1 u.2
    rw [hL0m, hΛ'd]
    constructor
    · intro h u' hu'
      exact h _ hu'
    · intro h z hz
      obtain ⟨b, hb⟩ := h ⟨_, hdec z⟩ (hwz z hz)
      refine ⟨b, ?_⟩
      rw [hb]
      simp [map_sub, hu.1, hu.2]
  have hun : Formalism.HermitianLatticesTheory.IsUnimodular h' L0 := by
    ext v
    rw [GlobalTheory.WittLow.mem_dual, hL0d]
    refine forall₂_congr fun u' _ => ?_
    rw [Submodule.mem_one]
    rfl

  let S₁ : HSp D :=
    { V := W, hT := h', herm := hs', nondeg := hnd', rank := Module.finrank D.host.E W, rank_eq := rfl,
      frame := Module.finBasis D.host.E W, sig := s, L0 := L0, standardTuple_isLattice := hL0lat, baseLattice_isUnimodular := hun }
  let e₁ : (Fin (Module.finrank D.host.E W) → D.host.E) ≃ₗ[D.host.E] W := (Module.finBasis D.host.E W).equivFun.symm
  let Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E) :=
    L0.comap ((e₁ : (Fin (Module.finrank D.host.E W) → D.host.E) →ₗ[D.host.E] W).restrictScalars (𝓞 D.host.E))
  have hΛ₁m : ∀ v, v ∈ Λ₁ ↔ e₁ v ∈ L0 := fun v => Iff.rfl
  have hΛ₁lat : Submodule.IsLattice D.host.E Λ₁ := GlobalTheory.ColRows.isLattice_comap_equiv e₁ L0 hL0lat
  have hin : ∀ u : W, GlobalTheory.SqStepK.InLat S₁ Λ₁ u ↔ GlobalTheory.SqStepK.InLat S Λ (W.subtype u) := by
    intro u
    change (Module.finBasis D.host.E W).equivFun u ∈ Λ₁ ↔ _
    rw [hΛ₁m]
    change (Module.finBasis D.host.E W).equivFun.symm ((Module.finBasis D.host.E W).equivFun u) ∈ L0 ↔ _
    rw [LinearEquiv.symm_apply_apply, hL0m, hΛ'm]
    rfl
  refine ⟨S₁, Λ₁, W.subtype, ⟨?_, fun _ _ => rfl, hxx, hyy, hyx, fun u => ⟨((hW u).1 u.2).1, ((hW u).1 u.2).2⟩, hin, ?_⟩, ⟨hΛ₁lat, ?_⟩, rfl⟩
  · change S.rank = Module.finrank D.host.E W + 2
    omega
  · intro z hz
    obtain ⟨hs1, hr1⟩ := hsplit z hz
    refine ⟨S.hT y z, S.hT x z, ⟨_, hdec z⟩, hs1, hr1, (hin _).2 (hwz z hz), ?_⟩
    change z = S.hT y z • x + (z - S.hT y z • x - S.hT x z • y) + S.hT x z • y
    abel
  · intro v
    simp only [gram_sum]
    rw [hΛ₁m, hL0d]
    constructor
    · intro h a ha
      exact h _ ha
    · intro h u' hu'
      have := h (e₁.symm u') (by rw [hΛ₁m, LinearEquiv.apply_symm_apply]; exact hu')
      obtain ⟨b, hb⟩ := this
      refine ⟨b, ?_⟩
      rw [hb]
      change S.hT (e₁ (e₁.symm u') : S.V) _ = _
      rw [LinearEquiv.apply_symm_apply]
      rfl

end GlobalTheory.PlaneCompl
