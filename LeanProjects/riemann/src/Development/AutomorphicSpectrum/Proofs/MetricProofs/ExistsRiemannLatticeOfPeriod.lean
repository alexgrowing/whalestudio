import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

section Diag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ}

def diagAct (ty : Fin g → (E →+* ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) :=
  (Algebra.lmul ℂ (Fin g → ℂ)).toRingHom.comp (Pi.ringHom fun i => (ty i).comp (algebraMap (𝓞 E) E))

theorem diagAct_apply (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (x : Fin g → ℂ) (i : Fin g) :
    diagAct ty a x i = ty i (a : E) * x i := rfl

theorem embedding_eq_of_integers {s t : E →+* ℂ} (h : ∀ a : 𝓞 E, s (a : E) = t (a : E)) : s = t :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)

theorem mem_eigSp_diagAct (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) (x : Fin g → ℂ) :
    x ∈ eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E)) ↔ ∀ i, ty i ≠ s → x i = 0 := by
  have key : ∀ (a : 𝓞 E) (i : Fin g),
      ((diagAct ty a - (s.comp (algebraMap (𝓞 E) E)) a • LinearMap.id : Module.End ℂ (Fin g → ℂ)) x) i = (ty i (a : E) - s (a : E)) * x i := by
    intro a i
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      diagAct_apply, RingHom.comp_apply]
    ring_nf
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h i hi
    by_contra hx
    refine hi (embedding_eq_of_integers fun a => ?_)
    have h1 := congrFun (h a) i
    rw [key] at h1
    simpa [hx, sub_eq_zero] using h1
  · intro h a
    funext i
    rw [key]
    by_cases hi : ty i = s
    · simp [hi]
    · simp [h i hi]

def eigSpDiagEquiv (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) :
    eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E)) ≃ₗ[ℂ] ({i // ty i = s} → ℂ) where
  toFun x j := x.1 j.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨fun i => open Classical in if h : ty i = s then f ⟨i, h⟩ else 0,
    (mem_eigSp_diagAct ty s _).2 fun i hi => by simp [hi]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases h : ty i = s
    · simp [h]
    · simp [h, (mem_eigSp_diagAct ty s x.1).1 x.2 i h]
  right_inv f := by
    funext j
    simp [j.2]

theorem finrank_eigSp_diagAct (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) :
    Module.finrank ℂ (eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E))) = Nat.card {i // ty i = s} := by
  classical
  rw [(eigSpDiagEquiv ty s).finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end Diag

theorem free_of_period {Λ : Type} [AddCommGroup Λ] {g : ℕ} (P : Λ →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) :
    Module.Free ℤ Λ ∧ Module.Finite ℤ Λ ∧ Module.finrank ℤ Λ = 2 * g := by
  let L : Submodule ℤ (Fin g → ℂ) := P.range.toIntSubmodule
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨by
    have : ((L : Set (Fin g → ℂ))) = Set.range P := by
      ext x; simp [L]
    rw [this, hs]⟩
  let e : Λ ≃ₗ[ℤ] L := (AddMonoidHom.ofInjective hi).toIntLinearEquiv
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  refine ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, ZLattice.rank ℝ L, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem riemLat_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)), IsTypeFn H D.p D.q ty → IsPeriod D ty P → ∃ R : RiemLat E g D.La, R.P = P ∧ R.form = D.EF ∧ (∀ a x i, R.B a x i = ty i (a : E) * x i) ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.p else D.q := by
  intro E _ _ _ H D g ty P hty hP
  obtain ⟨hact, hinj, hdisc, hspan, Hm, hherm, hpos, him⟩ := hP
  obtain ⟨hfree, hfin, hrank⟩ := free_of_period P hinj hdisc hspan
  refine ⟨{ free := hfree, fin := hfin, rank := hrank, form := D.EF, alt := D.alt, unimod := D.unimod
            adj := ?_, P := P, Hm := Hm, herm := hherm, pos := hpos, im := him, B := diagAct ty, act := ?_ },
    rfl, rfl, fun a x i => diagAct_apply ty a x i, fun s => ?_⟩
  · intro a a' h x y
    have : a' = H.bar a := by
      apply RingOfIntegers.ext
      rw [H.bar_eq a]
      exact h
    rw [this]
    exact D.adj a x y
  · intro a x
    funext i
    exact hact a x i
  · show Module.finrank ℂ (eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E))) = _
    rw [finrank_eigSp_diagAct]
    by_cases h : s (H.rt : E) = H.rt0
    · rw [if_pos h]
      exact (hty s).1 h
    · rw [if_neg h]
      exact (hty s).2 h

end GlobalTheory.CompanionTheory.Ar.Cusp
