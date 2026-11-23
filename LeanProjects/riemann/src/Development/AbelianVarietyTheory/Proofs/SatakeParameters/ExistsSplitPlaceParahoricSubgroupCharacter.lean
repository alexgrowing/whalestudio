import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ParaLevel

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_one (T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) :
    TrivOutside T (1 : GAf L n) := by
  intro w _
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem detDD_one (s : SplitPlace L) (r : ℕ) :
    NG.detDD s r (1 : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) = 1 := by
  unfold NG.detDD
  have : (Matrix.of fun a b : {x : Fin n // r ≤ x.val} =>
      ((1 : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a.1 b.1) = 1 := by
    ext a b
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

theorem continuous_detDD (s : SplitPlace L) (r : ℕ) :
    Continuous (NG.detDD (n := n) s r) := by
  unfold NG.detDD
  refine Continuous.matrix_det ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact (Units.continuous_val (M := Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))).matrix_elem a.1 b.1

section main
variable (s : SplitPlace L) (r : ℕ) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ)
  (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ)

def paraSub (hP : NG.LevelPara J χ s r ξ) :
    Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) where
  carrier := {g | NG.ParaRT s r g}
  one_mem' := by
    have h := (hP.mem 1 (trivOutside_one _)).1 J.one_mem
    simpa using h
  mul_mem' := by
    intro g h hg hh
    obtain ⟨x, hx, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g
    obtain ⟨y, hy, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s h
    have hxy := GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hy
    rw [← map_mul]
    exact (hP.mem _ hxy).1 (J.mul_mem ((hP.mem x hx).2 hg) ((hP.mem y hy).2 hh))
  inv_mem' := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g
    have hi := GlobalTheory.SatInd.CosetFin.trivOutside_inv hx
    show NG.ParaRT s r (s.loc n x)⁻¹
    rw [← map_inv]
    exact (hP.mem _ hi).1 (J.inv_mem ((hP.mem x hx).2 hg))

end main
end GlobalTheory.ParaLevel

namespace GlobalTheory.ParaLevel
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
section main2
variable {s : SplitPlace L} {r : ℕ} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
  {ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ}

def lift (s : SplitPlace L) (g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : GAf L n :=
  (GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g).choose

theorem lift_triv (g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
    TrivOutside {s.v} (lift s g) :=
  (GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g).choose_spec.1

theorem loc_lift (g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
    s.loc n (lift s g) = g :=
  (GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g).choose_spec.2

theorem lift_mem (hP : NG.LevelPara J χ s r ξ) (g : paraSub s r J χ ξ hP) : lift s g.1 ∈ J :=
  (hP.mem _ (lift_triv g.1)).2 (by rw [loc_lift]; exact g.2)

def thetaFun (hP : NG.LevelPara J χ s r ξ) (g : paraSub s r J χ ξ hP) : ℂˣ :=
  χ ⟨lift s g.1, lift_mem hP g⟩

theorem chi_eq (hP : NG.LevelPara J χ s r ξ) (κ : GAf L n) (hκ : TrivOutside {s.v} κ) (hJ : κ ∈ J)
    (h : s.loc n κ ∈ paraSub s r J χ ξ hP) : χ ⟨κ, hJ⟩ = thetaFun hP ⟨s.loc n κ, h⟩ := by
  unfold thetaFun
  set κ₀ := lift s (s.loc n κ) with hκ₀
  have h0 : κ₀ ∈ J := lift_mem hP ⟨s.loc n κ, h⟩
  have ht : TrivOutside {s.v} (κ * κ₀⁻¹) :=
    GlobalTheory.SatInd.CosetFin.trivOutside_mul hκ (GlobalTheory.SatInd.CosetFin.trivOutside_inv (lift_triv _))
  have hl : s.loc n (κ * κ₀⁻¹) = 1 := by
    rw [map_mul, map_inv, hκ₀, loc_lift, mul_inv_cancel]
  have hδ : κ * κ₀⁻¹ ∈ J := J.mul_mem hJ (J.inv_mem h0)
  have hc : χ ⟨κ * κ₀⁻¹, hδ⟩ = 1 := by
    rw [hP.chr _ hδ ht 1 (by rw [hl, detDD_one]; rfl), map_one]
  have hprod : (⟨κ, hJ⟩ : J) = ⟨κ * κ₀⁻¹, hδ⟩ * ⟨κ₀, h0⟩ := by
    apply Subtype.ext; simp
  rw [hprod, map_mul, hc, one_mul]

def theta (hP : NG.LevelPara J χ s r ξ) : paraSub s r J χ ξ hP →* ℂˣ where
  toFun := thetaFun hP
  map_one' := by
    have h1 : s.loc n (1 : GAf L n) ∈ paraSub s r J χ ξ hP := by rw [map_one]; exact (paraSub s r J χ ξ hP).one_mem
    have := chi_eq hP 1 (trivOutside_one _) J.one_mem h1
    have e : (⟨s.loc n 1, h1⟩ : paraSub s r J χ ξ hP) = 1 := by apply Subtype.ext; simp
    rw [e] at this
    rw [← this]
    exact map_one χ
  map_mul' := by
    intro g h
    set x := lift s g.1
    set y := lift s h.1
    have hx := lift_mem hP g
    have hy := lift_mem hP h
    have hxy : TrivOutside {s.v} (x * y) :=
      GlobalTheory.SatInd.CosetFin.trivOutside_mul (lift_triv _) (lift_triv _)
    have hm : s.loc n (x * y) ∈ paraSub s r J χ ξ hP := by
      rw [map_mul, loc_lift, loc_lift]; exact (g * h).2
    have := chi_eq hP (x * y) hxy (J.mul_mem hx hy) hm
    have e : (⟨s.loc n (x * y), hm⟩ : paraSub s r J χ ξ hP) = g * h := by
      apply Subtype.ext; simp [x, y, loc_lift]
    rw [e] at this
    rw [← this]
    have e2 : (⟨x * y, J.mul_mem hx hy⟩ : J) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [e2, map_mul]
    rfl

end main2
end GlobalTheory.ParaLevel

namespace GlobalTheory.ParaLevel

theorem exists_parahoric_char : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (r : ℕ) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelPara J χ s r ξ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → ∃ (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g, g ∈ K ↔ NG.ParaRT s r g) ∧ (∀ g (h : g ∈ K) (d : (s.v.adicCompletion (maximalRealSubfield L))ˣ), (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → θ ⟨g, h⟩ = ξ d) ∧ (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) ∧ IsOpen (θ.ker : Set K) ∧ ∀ κ, TrivOutside {s.v} κ → ∀ (hJ : κ ∈ J) (h : s.loc n κ ∈ K), χ ⟨κ, hJ⟩ = θ ⟨s.loc n κ, h⟩ := by
  intro L _ _ _ n s r J χ ξ hP hξ
  obtain ⟨N, hN⟩ := hξ
  refine ⟨paraSub s r J χ ξ hP, theta hP, fun g => Iff.rfl, ?_, fun g hg => hg.1, ?_, ?_⟩
  · intro g h d hd
    show χ ⟨lift s g, lift_mem hP ⟨g, h⟩⟩ = ξ d
    exact hP.chr _ _ (lift_triv g) d (by rw [loc_lift]; exact hd)
  · apply Subgroup.isOpen_of_mem_nhds
    have hc : Continuous fun g : paraSub s r J χ ξ hP => NG.detDD s r g.1 :=
      (continuous_detDD s r).comp continuous_subtype_val
    have h1 : NG.detDD s r ((1 : paraSub s r J χ ξ hP) : GL (Fin n) _) = 1 := detDD_one s r
    obtain ⟨π, hπ⟩ := s.v.valuation_exists_uniformizer (maximalRealSubfield L)
    set a : s.v.adicCompletion (maximalRealSubfield L) := ((π : maximalRealSubfield L) : s.v.adicCompletion (maximalRealSubfield L)) ^ N
    have ha : Valued.v a = WithZero.exp (-(N : ℤ)) := by
      simp only [a, map_pow, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ, ← WithZero.exp_nsmul]
      congr 1; simp
    have ha0 : (Valued.v a) ≠ 0 := by rw [ha]; simp
    have hnhds : {x : s.v.adicCompletion (maximalRealSubfield L) |
        Valued.v (x - 1) < WithZero.exp (-(N : ℤ))} ∈ nhds (1 : s.v.adicCompletion (maximalRealSubfield L)) := by
      refine Valued.mem_nhds.2 ⟨Units.mk0 (Valued.v.restrict a) (by rwa [ne_eq, Valuation.restrict_eq_zero_iff]), ?_⟩
      intro y hy
      simp only [Set.mem_setOf_eq, Units.val_mk0] at hy ⊢
      rw [← ha]
      exact (Valuation.restrict_lt_iff _).1 hy
    have hpre := hc.tendsto 1 (by rw [h1]; exact hnhds)
    refine Filter.mem_of_superset hpre ?_
    intro g hg
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hg
    have hne : NG.detDD s r g.1 ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg, Valuation.map_one] at hg
      exact absurd hg (not_lt.2 (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega))
    have hθ : theta hP g = ξ (Units.mk0 _ hne) := by
      show χ ⟨lift s g.1, lift_mem hP g⟩ = _
      exact hP.chr _ _ (lift_triv g.1) _ (by rw [loc_lift]; rfl)
    show theta hP g = 1
    rw [hθ]
    exact hN _ (le_of_lt hg)
  · intro κ hκ hJ h
    exact chi_eq hP κ hκ hJ h

end GlobalTheory.ParaLevel
