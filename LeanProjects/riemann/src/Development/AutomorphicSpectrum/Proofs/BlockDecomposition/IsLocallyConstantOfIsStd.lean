import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerWellDefined
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecSet
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

noncomputable section

namespace GlobalTheory.CompanionTheory.SmallSec

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem isClopen_ball (n : ℤ) : IsClopen (valBall F n : Set F) :=
  ⟨isClosed_valBall n, isOpen_valBall n⟩

theorem isClopen_secSet (m : ℕ) : IsClopen (secSet F m) := by
  have e : ∀ i j, Continuous fun X : Matrix (Fin 2) (Fin 3) F => X i j :=
    fun i j => continuous_id.matrix_elem i j
  have hb : ∀ (n : ℤ) (f : Matrix (Fin 2) (Fin 3) F → F), Continuous f →
      IsClopen {X | f X ∈ valBall F n} :=
    fun n f hf => (isClopen_ball n).preimage hf
  exact (hb _ _ ((e 0 0).sub continuous_const)).inter <|
    (hb _ _ (e 0 1)).inter <| (hb _ _ (e 1 0)).inter <|
    (hb _ _ ((e 1 1).sub continuous_const)).inter <| (hb _ _ (e 0 2)).inter (hb _ _ (e 1 2))

theorem isCompact_secSet (m : ℕ) : IsCompact (secSet F m) := by
  set A : Set F := (valBall F (m : ℤ) : Set F) ∪ ((fun x => x + 1) '' (valBall F (m : ℤ) : Set F)) ∪
    (valBall F (-(m : ℤ)) : Set F) with hA
  have hAc : IsCompact A :=
    ((isCompact_valBall _).union ((isCompact_valBall _).image (continuous_id.add continuous_const))).union
      (isCompact_valBall _)
  have hbox : IsCompact (Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 3 => A) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hAc
  refine IsCompact.of_isClosed_subset hbox (isClopen_secSet m).1 ?_
  rintro X ⟨h00, h01, h10, h11, h02, h12⟩ i - j -
  have s1 : ∀ {x : F}, x ∈ valBall F (m : ℤ) → x ∈ A := fun h => Or.inl (Or.inl h)
  have s2 : ∀ {x : F}, x - 1 ∈ valBall F (m : ℤ) → x ∈ A :=
    fun {x} h => Or.inl (Or.inr ⟨x - 1, h, sub_add_cancel x 1⟩)
  have s3 : ∀ {x : F}, x ∈ valBall F (-(m : ℤ)) → x ∈ A := fun h => Or.inr h
  fin_cases i <;> fin_cases j
  · exact s2 h00
  · exact s1 h01
  · exact s3 h02
  · exact s1 h10
  · exact s2 h11
  · exact s3 h12

theorem isLocallyConstant_of_isStd {ψ : AddChar F Circle} (hψ : IsStd ψ) :
    IsLocallyConstant fun x : F => (ψ x : ℂ) := by
  obtain ⟨hc, h1, h0⟩ := hψ
  have ht := isTrivialOn_addCharConductor hc h1
  rw [h0] at ht
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  refine ⟨{y | y - x ∈ valBall F 0}, (isOpen_valBall 0).preimage (continuous_id.sub continuous_const),
    by simp [zero_mem], fun y hy => ?_⟩
  have : ψ y = ψ (y - x) * ψ x := by rw [← AddChar.map_add_eq_mul, sub_add_cancel]
  rw [this, ht _ hy, one_mul]

end

theorem secFun_mem_SB_of_isStd : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle),
    IsStd ψ → ∀ m : ℕ, secFun ψ m ∈ LFS.SB F := by
  intro F _ _ _ _ _ _ ψ hψ m
  have hg : IsLocallyConstant fun X : Matrix (Fin 2) (Fin 3) F => (ψ (X 1 2) : ℂ) :=
    (isLocallyConstant_of_isStd hψ).comp_continuous (continuous_id.matrix_elem 1 2)
  have hS := isClopen_secSet (F := F) m
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun X => ?_,
    HasCompactSupport.intro (isCompact_secSet m) fun X hX => Set.indicator_of_notMem hX _⟩
  by_cases hX : X ∈ secSet F m
  · obtain ⟨U, hU, hXU, hUc⟩ := (IsLocallyConstant.iff_exists_open _).1 hg X
    refine ⟨U ∩ secSet F m, hU.inter hS.2, ⟨hXU, hX⟩, fun Y hY => ?_⟩
    simp only [secFun]
    rw [Set.indicator_of_mem hY.2, Set.indicator_of_mem hX]
    exact hUc Y hY.1
  · refine ⟨(secSet F m)ᶜ, hS.1.isOpen_compl, hX, fun Y hY => ?_⟩
    simp only [secFun]
    rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem hX]

end GlobalTheory.CompanionTheory.SmallSec
