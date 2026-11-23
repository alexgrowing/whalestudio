import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemOffP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FibreAtTau

theorem comm_and_inf_trivial : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau), (∀ p ∈ GlobalTheory.FibreAtTau.atP θ V C τ, ∀ q ∈ GlobalTheory.FibreAtTau.offP θ V C τ, p * q = q * p) ∧ ∀ h, h ∈ GlobalTheory.FibreAtTau.atP θ V C τ → h ∈ GlobalTheory.FibreAtTau.offP θ V C τ → h = 1 := by
  intro D θ hθ V r C τ
  have hc : ∀ (ρ : D.what₂.Tau) (x : GA D V), cmp θ ρ x = GlobalTheory.RowReal.infMatHom V (θ ρ) x := fun _ _ => rfl
  have one_spec : GlobalTheory.RowReal.IsRealAll θ V 1 (1 : GA D V) :=
    ⟨one_mem _, fun _ => GlobalTheory.PointAtPlaceHom.infMat_one V _⟩
  refine ⟨fun p hp q hq => ?_, fun h hp hq => ?_⟩
  · rw [mem_atP] at hp
    rw [mem_offP] at hq
    obtain ⟨hpf, hpc⟩ := hp
    have hpf' : finHom V (p : GA D V) = 1 := hpf
    set c : GA D V := (p : GA D V) * q * (p : GA D V)⁻¹ * (q : GA D V)⁻¹ with hcdef
    have hcR : GlobalTheory.RowReal.IsRealAll θ V 1 c := by
      refine ⟨?_, fun ρ => ?_⟩
      · show finHom V c = 1
        simp only [hcdef, map_mul, map_inv, hpf', one_mul, inv_one, mul_one, mul_inv_cancel]
      · show GlobalTheory.RowReal.infMatHom V (θ ρ) c = 1
        by_cases hρ : ρ = τ
        · have hinv : ∀ x : GA D V, GlobalTheory.RowReal.infMatHom V (θ ρ) x * GlobalTheory.RowReal.infMatHom V (θ ρ) x⁻¹ = 1 :=
            fun x => by rw [← map_mul, mul_inv_cancel, map_one]
          have hinv1 : ∀ x : GA D V, GlobalTheory.RowReal.infMatHom V (θ ρ) x = 1 → GlobalTheory.RowReal.infMatHom V (θ ρ) x⁻¹ = 1 :=
            fun x hx => by have := hinv x; rwa [hx, Matrix.one_mul] at this
          subst hρ
          have hq' : GlobalTheory.RowReal.infMatHom V (θ ρ) (q : GA D V) = 1 := by rw [← hc]; exact hq
          rw [hcdef, map_mul, map_mul, map_mul, hq', hinv1 _ hq', Matrix.mul_one, Matrix.mul_one, hinv]
        · have hinv : ∀ x : GA D V, GlobalTheory.RowReal.infMatHom V (θ ρ) x * GlobalTheory.RowReal.infMatHom V (θ ρ) x⁻¹ = 1 :=
            fun x => by rw [← map_mul, mul_inv_cancel, map_one]
          have hinv1 : ∀ x : GA D V, GlobalTheory.RowReal.infMatHom V (θ ρ) x = 1 → GlobalTheory.RowReal.infMatHom V (θ ρ) x⁻¹ = 1 :=
            fun x hx => by have := hinv x; rwa [hx, Matrix.one_mul] at this
          have hp' : GlobalTheory.RowReal.infMatHom V (θ ρ) (p : GA D V) = 1 := by rw [← hc]; exact hpc ρ hρ
          rw [hcdef, map_mul, map_mul, map_mul, hp', hinv1 _ hp', Matrix.one_mul, Matrix.mul_one, hinv]
    have e : c = 1 := hcR.unique hθ one_spec
    apply Subtype.ext
    have e2 : (p : GA D V) * q * (p : GA D V)⁻¹ * (q : GA D V)⁻¹ = 1 := e
    have e3 : (p : GA D V) * q = (q : GA D V) * p := by
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at e2
      exact e2
    simpa using e3
  · rw [mem_atP] at hp
    rw [mem_offP] at hq
    apply Subtype.ext
    have hR : GlobalTheory.RowReal.IsRealAll θ V 1 (h : GA D V) := by
      refine ⟨hp.1, fun ρ => ?_⟩
      by_cases hρ : ρ = τ
      · subst hρ; exact hq
      · exact hp.2 ρ hρ
    exact hR.unique hθ one_spec

end GlobalTheory.FibreAtTau
