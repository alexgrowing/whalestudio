import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CuspFinGL.Transl

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem rt_comm_of_central {h : GA E a} (hc : ∀ g : GA E a, h * g = g * h) (x : GA E a) (φ : Sm E a) :
    rt E a x (rt E a h φ) = rt E a h (rt E a x φ) := by
  refine Subtype.ext (funext fun g => ?_)
  change φ.1 (g * x * h) = φ.1 (g * h * x)
  rw [mul_assoc g x h, mul_assoc g h x, hc x]

theorem rt_injective (h : GA E a) : Function.Injective (rt E a h) := fun φ ψ e => by
  refine Subtype.ext (funext fun g => ?_)
  have := congrArg (fun f : Sm E a => f.1 (g * h⁻¹)) e
  simpa using this

theorem isAutForm_rt_of_central {h : GA E a} (hc : ∀ g : GA E a, h * g = g * h) {φ : Sm E a}
    (hφ : IsAutForm φ) : IsAutForm (rt E a h φ) where
  left γ g := by
    change φ.1 (ratGL E a γ * g * h) = φ.1 (g * h)
    rw [mul_assoc, hφ.left]
  level := by
    have e : {k | finRep E a k (rt E a h φ) = rt E a h φ} = {k | finRep E a k φ = φ} := by
      ext k
      change rt E a (finGL E a k) (rt E a h φ) = rt E a h φ ↔ rt E a (finGL E a k) φ = φ
      rw [rt_comm_of_central hc]
      exact (rt_injective h).eq_iff
    rw [e]
    exact hφ.level
  kfin := by
    have := hφ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map (rt E a h))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨cptRep E a k φ, Submodule.subset_span ⟨k, rfl⟩, (rt_comm_of_central hc _ φ).symm⟩
  zfin := by
    have := hφ.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)).map (rt E a h))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z φ, Submodule.subset_span ⟨z, hz, rfl⟩, ?_⟩
    exact (LinearMap.congr_fun (GlobalTheory.CompanionTheory.CTFin.Slice1.commute_rt_of_mem_Zalg hz h).eq φ).symm
  growth g := by
    obtain ⟨C, N, hb⟩ := hφ.growth (g * h)
    refine ⟨C, N, fun y => ?_⟩
    have e : (rt E a h φ).1 (g * infGL E a y) = φ.1 (g * h * infGL E a y) := by
      change φ.1 (g * infGL E a y * h) = _
      rw [mul_assoc g _ h, mul_assoc g h, hc]
    rw [e]
    exact hb y

theorem rt_splitCentre_mem : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))) (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))), J ⊆ Zalg E a →
    ∀ φ : Sm E a, φ ∈ genSpace L ρ J → IsCuspidal φ.1 → ∀ t : ℝ,
      rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ ∈ genSpace L ρ J ∧
        IsCuspidal (rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ).1 := by
  intro E _ _ _ a L W _ _ ρ J hJ φ hφ hcusp t
  set h := GlobalTheory.UnitaryBC.splitCentre E a t with hh
  have hc : ∀ g : GA E a, h * g = g * h := GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t
  obtain ⟨hA, hL, hK, hZ⟩ := hφ
  refine ⟨⟨isAutForm_rt_of_central hc hA, fun k hk => ?_, fun g => ?_, fun z hz => ?_⟩, ?_⟩
  · change rt E a (finGL E a k) (rt E a h φ) = rt E a h φ
    rw [rt_comm_of_central hc]
    exact congrArg (rt E a h) (hL k hk)
  · have e : (fun k : Kinf E a => (cptRep E a k (rt E a h φ)).1 g) =
        fun k : Kinf E a => (cptRep E a k φ).1 (g * h) := by
      funext k
      exact congrArg (fun f : Sm E a => f.1 g) (rt_comm_of_central hc _ φ)
    rw [e]
    exact hK (g * h)
  · have e := LinearMap.congr_fun (GlobalTheory.CompanionTheory.CTFin.Slice1.commute_rt_of_mem_Zalg (hJ hz) h).eq φ
    rw [Module.End.mul_apply, Module.End.mul_apply] at e
    rw [e, hZ z hz, map_zero]
  · intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    have e : ∀ x : BlockIx a r → Ad E, (rt E a h φ).1 (unip x * g) = φ.1 (unip x * (g * h)) :=
      fun x => congrArg φ.1 (mul_assoc _ _ _)
    simp only [e]
    exact hcusp r hr hr' μ 𝓕 hμ hF (g * h)

end GlobalTheory.CompanionTheory.CuspFinGL.Transl
