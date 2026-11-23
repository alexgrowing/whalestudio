import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.PeriodReps
open Formalism.L2.Th1.H

section General
variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℝ V]

theorem altE_add_left' (H : Sesq V) (x y z : V) : altE H (x + y) z = altE H x z + altE H y z := by
  simp [altE, map_add]

theorem altE_add_right' (H : Sesq V) (x y z : V) : altE H x (y + z) = altE H x y + altE H x z := by
  simp [altE, map_add]

theorem real_smul_eq (r : ℝ) (x : V) : r • x = (r : ℂ) • x := by
  rw [← algebraMap_smul ℂ r x]; rfl

theorem altE_smul_left' (H : Sesq V) (r : ℝ) (x y : V) : altE H (r • x) y = r * altE H x y := by
  rw [real_smul_eq]; simp [altE]

theorem altE_smul_right' (H : Sesq V) (r : ℝ) (x y : V) : altE H x (r • y) = r * altE H x y := by
  rw [real_smul_eq]; unfold altE; rw [(H x).map_smulₛₗ]; simp

theorem fg_of_selfDual (H : Sesq V) (Λ : AddSubgroup V) (hc : Countable Λ) (hΛ : IsSelfDual H Λ) : Λ.FG := by
  classical
  have hK : ∀ x : V, (∀ y ∈ Λ, altE H x y = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    have hmem : ∀ t : ℝ, t • x ∈ Λ := fun t => by
      have h1 : t • x ∈ dualLat H Λ := fun y hy => ⟨0, by rw [altE_smul_left', hx y hy]; simp⟩
      rwa [hΛ] at h1
    let f : ℝ → Λ := fun t => ⟨t • x, hmem t⟩
    have hf : Function.Injective f := fun s t h => by
      have : s • x = t • x := congrArg Subtype.val h
      exact smul_left_injective ℝ hx0 this
    exact not_countable (α := ℝ) hf.countable
  obtain ⟨b, hbΛ, hbspan, hbli⟩ := exists_linearIndependent ℝ (Λ : Set V)
  haveI : Finite b := hbli.setFinite.to_subtype
  have hint : ∀ x ∈ Λ, ∀ e ∈ b, ((⌊altE H x e⌋ : ℤ) : ℝ) = altE H x e := by
    intro x hx e he
    have hx' : x ∈ dualLat H Λ := by rw [hΛ]; exact hx
    obtain ⟨m, hm⟩ := hx' e (hbΛ he)
    rw [hm, Int.floor_intCast]
  let g : Λ →+ (b → ℤ) :=
    { toFun := fun x e => ⌊altE H (x : V) e⌋
      map_zero' := by funext e; simp [altE]
      map_add' := fun x y => by
        funext e
        apply Int.cast_injective (α := ℝ)
        simp only [Pi.add_apply, Int.cast_add]
        rw [hint _ (x + y).2 _ e.2, hint _ x.2 _ e.2, hint _ y.2 _ e.2]
        simp [altE_add_left'] }
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : ∀ e ∈ b, altE H (x : V) e = 0 := fun e he => by
      have h2 : ⌊altE H (x : V) e⌋ = 0 := congrFun hx ⟨e, he⟩
      rw [← hint _ x.2 _ he, h2]; simp
    have hspan : ∀ y ∈ Submodule.span ℝ b, altE H (x : V) y = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact h0 y hy
      | zero => simp [altE]
      | add y z _ _ hy hz => rw [altE_add_right', hy, hz, add_zero]
      | smul r y _ hy => rw [altE_smul_right', hy, mul_zero]
    exact Subtype.ext (hK x fun y hy => hspan y (hbspan ▸ Submodule.subset_span hy))
  haveI : IsNoetherian ℤ Λ := isNoetherian_of_injective g.toIntLinearMap hg
  have : AddGroup.FG Λ := Module.Finite.iff_addGroup_fg.1 inferInstance
  exact (AddGroup.fg_iff_addSubgroup_fg Λ).1 this

end General
end GlobalTheory.PeriodReps

namespace GlobalTheory.PeriodReps
open Formalism.L2.Th1.H

theorem countable_lamC {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] {a b : ℕ} (emb : ι → E →+* ℂ) (δ : ℂ)
    (AA0 : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) :
    Countable (Formalism.L2.Ker.LamC emb δ AA0 N N') := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin b) (Fin a) E) := inferInstanceAs (Countable (Fin b → Fin a → E))
  haveI : Countable (Formalism.L2.Col.HomE E a b) :=
    (LinearMap.toMatrix' : ((Fin a → E) →ₗ[E] (Fin b → E)) ≃ₗ[E] Matrix (Fin b) (Fin a) E).injective.countable
  have hsub : ((Formalism.L2.Ker.LamC emb δ AA0 N N' : AddSubgroup _) : Set (Formalism.L2.Ker.VV ι a b)) ⊆
      Set.range (Formalism.L2.Ker.embH emb δ) := by
    intro y hy
    simp only [Formalism.L2.Ker.LamC, Formalism.L2.Ker.laV, SetLike.mem_coe, AddSubgroup.mem_map] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact ⟨x, rfl⟩
  exact ((Set.countable_range _).mono hsub).to_subtype

theorem reps_genuine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) ∧ Formalism.L2.Th1.H.IsReps (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) ((LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) (repsOf (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) ((LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c))) ∧ Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) := by
  intro D ψ θ S T a b hS hT δ sc hSP e SS hSS N N' c hc hcS hSS2 hLa
  have hfg := fg_of_selfDual _ _ (countable_lamC _ _ _ _ _) hLa.1
  obtain ⟨i1, i2, i3⟩ := Formalism.L2.Ker.finite_index_of_fg _ _ _ _ (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c hc hfg
  exact ⟨Formalism.L2.Ker.repsOf_spec _ _ i1, Formalism.L2.Ker.repsOf_spec _ _ i2, Formalism.L2.Ker.repsOf_spec _ _ i3⟩

end GlobalTheory.PeriodReps
