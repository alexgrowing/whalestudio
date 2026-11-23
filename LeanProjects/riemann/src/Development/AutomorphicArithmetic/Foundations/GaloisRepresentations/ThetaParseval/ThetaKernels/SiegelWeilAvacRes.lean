import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.ContinuousIns
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacVacCut

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def ins_k (z : Fin d.m × Fin L.n × Fin 2 → Af F) : Fin d.m × Fin d.n × Fin 2 → Af F :=
  fun k => if h : ∃ j, L.em j = k.2.1 then z (k.1, h.choose, k.2.2) else 0
def ext_k (X' : Mx F E d.m L.n) : Mx F E d.m d.n := fun a i => if h : ∃ j, L.em j = i then X' a h.choose else 0
theorem choose_em_k (j : Fin L.n) (h : ∃ j', L.em j' = L.em j) : h.choose = j := L.inj h.choose_spec
theorem ext_sub_k (X : Mx F E d.m d.n) (hX : ∀ a, X a L.i₀ = 0) : _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L (X.submatrix id L.em) = X := by
  funext a i
  by_cases h : ∃ j, L.em j = i
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, dif_pos h, Matrix.submatrix_apply, id, h.choose_spec]
  · have : i = L.i₀ := by
      by_contra hi
      exact h ((L.rng i).1 hi)
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, dif_neg h]
    rw [this, hX]
theorem crd_ext_k (X' : Mx F E d.m L.n) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') k).2 = _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L (fun k' => (L.sd.crd X' k').2) k := by
  by_cases h : ∃ j, L.em j = k.2.1
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_pos h]
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_neg h, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    rfl
theorem continuous_ins_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L (F := F)) := by
  refine continuous_pi fun k => ?_
  by_cases h : ∃ j, L.em j = k.2.1
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_pos h]; exact continuous_apply _
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_neg h]; exact continuous_const
def prj_k (z : Fin d.m × Fin d.n × Fin 2 → Af F) : Fin d.m × Fin L.n × Fin 2 → Af F := fun k => z (k.1, L.em k.2.1, k.2.2)
theorem prj_ins_k (z : Fin d.m × Fin L.n × Fin 2 → Af F) : _root_.PositivityTheory.SiegelWeilFormula.Avac.prj_k L (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z) = z := by
  funext k
  have h : ∃ j, L.em j = L.em k.2.1 := ⟨_, rfl⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.prj_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_pos h, _root_.PositivityTheory.SiegelWeilFormula.Avac.choose_em_k L k.2.1 h]
theorem SB_ins_k {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} (hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F)) :
    (fun z => g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z)) ∈ SB (Fin d.m × Fin L.n × Fin 2 → Af F) := by
  refine ⟨hg.1.comp_continuous (_root_.PositivityTheory.SiegelWeilFormula.Avac.continuous_ins_k L), ?_⟩
  have hc : IsCompact (_root_.PositivityTheory.SiegelWeilFormula.Avac.prj_k L '' tsupport g) := hg.2.isCompact.image (continuous_pi fun k => continuous_apply _)
  refine hc.of_isClosed_subset (isClosed_tsupport _) ?_
  refine (tsupport_comp_subset_preimage g (_root_.PositivityTheory.SiegelWeilFormula.Avac.continuous_ins_k L)).trans fun z hz => ⟨_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z, hz, _root_.PositivityTheory.SiegelWeilFormula.Avac.prj_ins_k L z⟩
theorem sum_loc_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (X : Mx F E d.m d.n) :
    ∑ a, ∑ i, ‖R.loc w X a i‖ ^ 2 = ∑ i, ∑ a, ‖(((R.fr w)⁻¹).1 *ᵥ fun b => d.cw w X b i) a‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, Matrix.map_apply, norm_star]
  rfl
theorem hζ'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.ζ = 1 ∨ R.ζ = Complex.I := by
  rcases R.hζ with h | h
  · exact Or.inl h.2
  · exact Or.inr h.2
theorem gauss_ext_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (w : InfinitePlace F) (X' : Mx F E d.m L.n) :
    fP 1 (R.loc w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X')) = fP 1 (R'.loc w X') := by
  suffices key : ∑ a, ∑ i, ‖R'.loc w X' a i‖ ^ 2 = ∑ a, ∑ i, ‖R.loc w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') a i‖ ^ 2 by
    simp only [fP, gs, key, evX, map_one]
  rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.sum_loc_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.sum_loc_k]
  refine Fintype.sum_of_injective L.em L.inj _ _ (fun i hi => ?_) (fun j => ?_)
  · have h : ¬ ∃ j, L.em j = i := fun ⟨j, hj⟩ => hi ⟨j, hj⟩
    have : (fun b => d.cw w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') b i) = 0 := by
      funext b
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, Matrix.map_apply, dif_neg h, map_zero, Pi.zero_apply]
    simp [this]
  · have h : ∃ j', L.em j' = L.em j := ⟨_, rfl⟩
    have e : (fun b => d.cw w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') b (L.em j)) = fun b => L.sd.cw w X' b j := by
      funext b
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, Matrix.map_apply, dif_pos h, _root_.PositivityTheory.SiegelWeilFormula.Avac.choose_em_k L j h]
    rw [e]
    exact norm_frame_eq d.ok.hm (d.A.J.map (d.B.emb w).1) (R'.fr w) (R.fr w) R'.ζ R.ζ (R'.sg w) (R.sg w) (_root_.PositivityTheory.SiegelWeilFormula.Avac.hζ'_k R')
      (_root_.PositivityTheory.SiegelWeilFormula.Avac.hζ'_k R) (R'.hfr w) (R.hfr w) _
theorem res_vg_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) :
    (fun X' => _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X')) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R' (fun z => g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z)) := by
  funext X'
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => _root_.PositivityTheory.SiegelWeilFormula.Avac.gauss_ext_k L R R' w X'
  · congr 1
    funext k
    exact _root_.PositivityTheory.SiegelWeilFormula.Avac.crd_ext_k L X' k
def resL_k : (Mx F E d.m d.n → ℂ) →ₗ[ℂ] (Mx F E d.m L.n → ℂ) := LinearMap.funLeft ℂ ℂ (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L)
theorem res_vac_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ R.vac) : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L f ∈ R'.vac := by
  have : R.vac ≤ R'.vac.comap (_root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    show _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g) ∈ R'.vac
    have e : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R' (fun z => g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z)) := _root_.PositivityTheory.SiegelWeilFormula.Avac.res_vg_k L R R' g
    rw [e]
    exact _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_mem_k R' (_root_.PositivityTheory.SiegelWeilFormula.Avac.SB_ins_k L hg)
  exact this hf
theorem vac_res'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) :
    ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∃ Φ', L.IsRes Φ Φ' ∧ L.sd.T Φ' ∈ R'.vac := by
  intro Φ hΦ hv
  have h1 : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (d.T Φ) ∈ R'.vac := _root_.PositivityTheory.SiegelWeilFormula.Avac.res_vac_k L R R' hv
  have h2 : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (d.T Φ) ∈ L.sd.schM := (hF F E σ L.sd R').1 (_root_.PositivityTheory.SiegelWeilFormula.Avac.vac_le_fock_k R' h1)
  obtain ⟨Φ', hΦ', e⟩ := (hT.1 F E σ L.sd).2.1 _ h2
  refine ⟨Φ', ⟨hΦ', fun X hX => ?_⟩, e ▸ h1⟩
  rw [e]
  show d.T Φ (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L (X.submatrix id L.em)) = d.T Φ X
  rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_sub_k L X hX]
end PositivityTheory.SiegelWeilFormula.Avac
end
end
