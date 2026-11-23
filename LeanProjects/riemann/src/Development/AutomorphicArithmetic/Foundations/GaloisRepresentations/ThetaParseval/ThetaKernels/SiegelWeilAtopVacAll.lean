import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.VacAll
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopVacCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKmainLin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopVacLin

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Atop
open PositivityTheory.SiegelWeilFormula.KMain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.gens {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (s : Finset (InfinitePlace F)) : Set (Mx F E d.m d.n → ℂ) :=
  {f | ∃ (P : InfinitePlace F → PX d.m d.n) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ), (∀ w ∉ s, P w = 1) ∧ g ∈ SB _ ∧
    f = fun X => (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2}
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.vacOn {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (s : Finset (InfinitePlace F)) : Submodule ℂ (Mx F E d.m d.n → ℂ) :=
  Submodule.span ℂ (R.gens s)
theorem vacOn_empty_le_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.vacOn ∅ ≤ R.vac := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨P, g, hP, hg, rfl⟩
  refine Submodule.subset_span ⟨g, hg, ?_⟩
  funext X
  simp only [hP _ (Finset.notMem_empty _)]
theorem fock_le_vacOn_univ_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.fock ≤ R.vacOn Finset.univ := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨P, g, hg, rfl⟩
  exact Submodule.subset_span ⟨P, g, fun w hw => absurd (Finset.mem_univ w) hw, hg, rfl⟩
theorem vacOn_step_k (hG : AbsSt.GenCore) (c : ℂ) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hFM : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hLE : _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k)
    (hLo : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hGS : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k) (hGI : _root_.PositivityTheory.SiegelWeilFormula.GIinv_k) (hGD : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hSK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k)
    (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (s : Finset (InfinitePlace F)) (hw : w ∉ s)
    (ih : ∀ Φ ∈ d.sch, d.T Φ ∈ R.vacOn s → ∀ x,
      HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x)) :
    ∀ Φ ∈ d.sch, d.T Φ ∈ R.vacOn (insert w s) → ∀ x,
      HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x) := by
  have hgen : ∀ f ∈ R.gens (insert w s), ∃ Φf : d.Fn, d.KFin Φf ∧ d.T Φf = f ∧ ∀ x,
      HolValueAt (fun z => d.eis (d.sec0 Φf) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φf x) := by
    rintro f ⟨P, g, hP, hg, rfl⟩
    set Ψ : Mx F E d.m d.n → ℂ := fun X => (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) *
      g fun k => (d.crd X k).2 with hΨdef
    have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨P, g, hg, rfl⟩
    obtain ⟨φ, hφ⟩ := hLE F E σ d R w Ψ hΨ
    have hTP : ∀ Q : PX d.m d.n, d.T (φ Q) = fun X => (∏ w', fP (Function.update P w Q w') (R.loc w' X)) *
        g fun k => (d.crd X k).2 := by
      intro Q
      rw [(hφ Q).2]
      funext X
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hΨdef]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self, mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun w' hw' => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]
    have hfock : ∀ Q, d.T (φ Q) ∈ R.fock := fun Q => by
      rw [hTP Q]
      exact Submodule.subset_span ⟨_, g, hg, rfl⟩
    have hKF : ∀ Q, d.KFin (φ Q) := fun Q => hPK F E σ d R (φ Q) (hφ Q).1 (hfock Q)
    have hvac : ∀ x, HolValueAt (fun z => d.eis (d.sec0 (φ 1)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (φ 1) x) := by
      refine ih (φ 1) (hφ 1).1 ?_
      rw [hTP 1]
      refine Submodule.subset_span ⟨Function.update P w 1, g, fun w' hw' => ?_, hg, rfl⟩
      by_cases e : w' = w
      · subst e; exact Function.update_self _ _ _
      · rw [Function.update_of_ne e]
        exact hP w' (by simp [e, hw'])
    refine ⟨φ (P w), hKF (P w), ?_, _root_.PositivityTheory.SiegelWeilFormula.Atop.genAt_k hG c hT hAux hFM hLo hLI hGS hGI hGD hPK hSK hEW d R w hΨ hφ hvac (P w)⟩
    rw [hTP (P w), Function.update_eq_self]
  intro Φ hΦ hTΦ x
  obtain ⟨k, a, f, hf⟩ := Submodule.mem_span_set'.1 hTΦ
  choose Φf hK hTf hI using fun i => hgen (f i).1 (f i).2
  have hΦeq : Φ = ∑ i, a i • Φf i := by
    have hmem : Φ - ∑ i, a i • Φf i ∈ d.sch :=
      d.sch.sub_mem hΦ (d.sch.sum_mem fun i _ => d.sch.smul_mem _ (hK i).1)
    refine sub_eq_zero.mp ((hT.1 F E σ d).2.2 _ hmem ?_)
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, map_sub, map_sum]
    simp only [map_smul, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, hTf, hf, sub_self]
  rw [hΦeq]
  exact _root_.PositivityTheory.SiegelWeilFormula.Atop.ident_lincomb_k hT hSK hEW d c a Φf hK hI x
end PositivityTheory.SiegelWeilFormula.Atop
namespace PositivityTheory.SiegelWeilFormula
def VacAllOfC_k : Prop :=
  AbsSt.GenCore → _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocInst_k → _root_.PositivityTheory.SiegelWeilFormula.GSplit_k → _root_.PositivityTheory.SiegelWeilFormula.GIinv_k → _root_.PositivityTheory.SiegelWeilFormula.GIdil_k → _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k →
    _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.EisWk_k → _root_.PositivityTheory.SiegelWeilFormula.VacAll_k
theorem Atop.vacAllOfC_k : _root_.PositivityTheory.SiegelWeilFormula.VacAllOfC_k := by
  intro hG hT hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hEW F E _ _ _ _ _ σ d R c hV Φ hΦ x
  have claim : ∀ s : Finset (InfinitePlace F), ∀ Φ ∈ d.sch, d.T Φ ∈ R.vacOn s → ∀ x,
      HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun Φ hΦ hT x => hV Φ hΦ (_root_.PositivityTheory.SiegelWeilFormula.Atop.vacOn_empty_le_k R hT) x
    | insert w s hw ih => exact _root_.PositivityTheory.SiegelWeilFormula.Atop.vacOn_step_k hG c hT hAux hFM hLE hLo hLI hGS hGI hGD hPK hSK hEW d R w s hw ih
  exact claim Finset.univ Φ hΦ.1 (_root_.PositivityTheory.SiegelWeilFormula.Atop.fock_le_vacOn_univ_k R (hKP F E σ d R Φ hΦ)) x
end PositivityTheory.SiegelWeilFormula
end
end
