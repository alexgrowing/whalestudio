import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PClassE
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelv
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P

namespace PI.UnitaryGroupMassFormula.IAT

section AwayLocSec

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem locv_incl_int (v : HeightOneSpectrum (𝓞 F)) (e : E) (he : IsIntegral ℤ e) :
    Formalism.UG.inclE (F := F) (v.adicCompletion F) e ∈ Formalism.L2.Geo.Def.PC.SV E v := by
  have he' : e ∈ intOE E := ⟨⟨e, he⟩, rfl⟩
  exact levelv_tmul_mem v e he' 1 (one_mem _)

theorem locv_upper (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfin : Module.Finite (𝓞 E) Λ) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ z ∈ Formalism.L2.Geo.Def.PC.latV v Λ, ∀ i,
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (m : E) * z i ∈ Formalism.L2.Geo.Def.PC.SV E v := by
  classical
  obtain ⟨t, ht⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : t × Fin n => (p.1 : Fin n → E) p.2)
  have hΛ : ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k) := by
    intro x hx
    rw [← ht] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => intro k; exact hm (⟨x, hx⟩, k)
    | zero => intro k; simp [isIntegral_zero]
    | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
    | smul r x _ hx =>
      intro k
      have : (m : E) * (r • x) k = algebraMap (𝓞 E) E r * ((m : E) * x k) := by
        simp [Algebra.smul_def]; ring
      rw [this]
      exact (RingOfIntegers.isIntegral_coe r).mul (hx k)
  refine ⟨m, hm0, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    intro i
    rw [← map_mul]
    exact locv_incl_int v _ (hΛ x hx i)
  | zero => intro i; simp
  | add a b _ _ ha hb => intro i; rw [Pi.add_apply, mul_add]; exact add_mem (ha i) (hb i)
  | smul s a _ ha =>
    intro i
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem s.2 (ha i)

theorem locv_lower (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ w : Fin n → E ⊗[F] v.adicCompletion F, (∀ i, w i ∈ Formalism.L2.Geo.Def.PC.SV E v) →
      (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) (m : E) * w i) ∈ Formalism.L2.Geo.Def.PC.latV v Λ := by
  classical
  have hk : ∀ k : Fin n, ∃ N : ℕ, ∃ f : Fin N → E, ∃ w : Fin N → Λ,
      ∑ j, f j • (w j : Fin n → E) = Pi.single k 1 := by
    intro k
    have : (Pi.single k 1 : Fin n → E) ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨N, f, w, h⟩ := Submodule.mem_span_set'.1 this
    exact ⟨N, f, fun j => ⟨w j, (w j).2⟩, h⟩
  choose N f w hw using hk
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : Σ k : Fin n, Fin (N k) => f p.1 p.2)
  have hsingle : ∀ k, (Pi.single k (m : E) : Fin n → E) ∈ Λ := by
    intro k
    have : (Pi.single k (m : E) : Fin n → E) =
        ∑ j, (⟨(m : E) * f k j, hm ⟨k, j⟩⟩ : 𝓞 E) • (w k j : Fin n → E) := by
      have h1 : (Pi.single k (m : E) : Fin n → E) = (m : E) • (Pi.single k 1 : Fin n → E) := by
        rw [← Pi.single_smul', smul_eq_mul, mul_one]
      rw [h1, ← hw k, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← algebraMap_smul E, smul_smul]
      rfl
    rw [this]
    exact sum_mem fun j _ => Λ.smul_mem _ (w k j).2
  refine ⟨m, hm0, fun y hy => ?_⟩
  have : (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) (m : E) * y i) =
      ∑ k, (⟨y k, hy k⟩ : Formalism.L2.Geo.Def.PC.SV E v) •
        (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) ((Pi.single k (m : E) : Fin n → E) i)) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · show _ = (_ : Formalism.L2.Geo.Def.PC.SV E v) •
        Formalism.UG.inclE (F := F) (v.adicCompletion F) ((Pi.single i (m : E) : Fin n → E) i)
      rw [Pi.single_eq_same, Subring.smul_def, smul_eq_mul, mul_comm]
    · intro k _ hki
      show (_ : Formalism.L2.Geo.Def.PC.SV E v) •
        Formalism.UG.inclE (F := F) (v.adicCompletion F) ((Pi.single k (m : E) : Fin n → E) i) = 0
      rw [Pi.single_apply, if_neg (Ne.symm hki), map_zero, smul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  rw [this]
  exact sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsingle k, rfl⟩)

end AwayLocSec

theorem loc_bound {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Formalism.L2.GlobalTheoryTheory.Comp.IsLat Λ)
    (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ z ∈ Formalism.L2.Geo.Def.PC.latV v Λ,
      (fun i => inclE (F := F) (v.adicCompletion F) ((N : ℤ) : E) * (M *ᵥ z) i) ∈ Formalism.L2.Geo.Def.PC.latV v Λ := by
  obtain ⟨mu, hmu, hu⟩ := locv_upper v Λ hΛ.1
  obtain ⟨ml, hml, hl⟩ := locv_lower v Λ hΛ.2
  obtain ⟨N0, hN0, hN⟩ := levelv_denom_family v (fun p : Fin n × Fin n => M p.1 p.2)
  refine ⟨ml * (N0 : ℤ) * mu, mul_ne_zero (mul_ne_zero hml (by exact_mod_cast hN0)) hmu, fun z hz => ?_⟩
  set w : Fin n → E ⊗[F] v.adicCompletion F :=
    fun i => N0 • (M *ᵥ fun j => inclE (F := F) (v.adicCompletion F) (mu : E) * z j) i with hw
  have hwS : ∀ i, w i ∈ Formalism.L2.Geo.Def.PC.SV E v := by
    intro i
    simp only [hw, Matrix.mulVec, dotProduct, Finset.smul_sum]
    exact sum_mem fun j _ => by rw [← smul_mul_assoc]; exact mul_mem (hN (i, j)) (hu z hz j)
  have e : (fun i => inclE (F := F) (v.adicCompletion F) (((ml * (N0 : ℤ) * mu : ℤ)) : E) * (M *ᵥ z) i) =
      fun i => inclE (F := F) (v.adicCompletion F) (ml : E) * w i := by
    funext i
    simp only [hw, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [nsmul_eq_mul]
    push_cast
    simp only [map_mul, map_natCast]
    ring
  rw [e]
  exact hl w hwS

end PI.UnitaryGroupMassFormula.IAT

end
