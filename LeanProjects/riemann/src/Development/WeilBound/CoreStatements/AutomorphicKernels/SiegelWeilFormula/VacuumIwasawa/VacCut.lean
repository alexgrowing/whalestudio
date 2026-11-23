import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdDecomp

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def vg {d : SD σ} (R : RD d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (X : Mx F E d.m d.n) : ℂ :=
  (∏ w, fP 1 (R.loc w X)) * g fun k => (d.crd X k).2

theorem vg_mem {d : SD σ} (R : RD d) {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} (hg : g ∈ SB _) : vg R g ∈ R.vac :=
  Submodule.subset_span ⟨g, hg, rfl⟩

theorem vac_le_fock {d : SD σ} (R : RD d) : R.vac ≤ R.fock := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, rfl⟩
  exact Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩

def Tl (d : SD σ) : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' Φ Ψ := funext fun X => by
    simp only [SD.T, Pi.add_apply, ← map_add]
    congr 1
    funext z
    exact mul_add _ _ _
  map_smul' c Φ := funext fun X => by
    simp only [SD.T, Pi.smul_apply, RingHom.id_apply, ← map_smul]
    congr 1
    funext z
    exact mul_left_comm _ _ _

theorem T_inj (hB : TBij) {d : SD σ} {Φ Ψ : d.Fn} (hΦ : Φ ∈ d.sch) (hΨ : Ψ ∈ d.sch) (h : d.T Φ = d.T Ψ) : Φ = Ψ := by
  have e : d.T (Φ - Ψ) = 0 := by
    have := (Tl d).map_sub Φ Ψ
    simp only [Tl, LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [this, h, sub_self]
  exact sub_eq_zero.1 ((hB F E σ d).2.2 _ (sub_mem hΦ hΨ) e)

end PositivityTheory.SiegelWeilFormula.Avac

end
