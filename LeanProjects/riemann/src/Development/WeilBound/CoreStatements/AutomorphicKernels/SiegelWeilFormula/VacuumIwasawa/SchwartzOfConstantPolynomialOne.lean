import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.VacCut
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.MatrixEqFrameConjugate
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.SchwartzPolyGauss

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics (mkGR inFrame_mul inFrame_one cw_mul cw_one form_w)

variable {d : SD σ}

theorem crd_add (X Z : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) : d.crd (X + Z) k = d.crd X k + d.crd Z k := by
  simp only [SD.crd, Matrix.add_apply, map_add, Finsupp.coe_add, Pi.add_apply]

theorem crd_fin {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (k : Fin d.m × Fin d.n × Fin 2) : (d.crd Z k).2 = 0 := by
  have h := congrArg (fun M => d.crd M k) hZ
  simp only [SD.crd, Matrix.smul_apply, map_smul, Finsupp.smul_apply, Matrix.zero_apply, map_zero, Finsupp.coe_zero,
    Pi.zero_apply, smul_eq_mul] at h
  have h2 := congrArg Prod.snd h
  have e : ∀ c : AF F, (finOne F * c).2 = c.2 := fun c => by
    show (1 : Af F) * c.2 = c.2
    exact one_mul _
  simp only [SD.crd]
  rw [← e]
  exact h2

theorem loc_add_of (R : RD d) (w : InfinitePlace F) {Z : Mx F E d.m d.n} (hZ : d.cw w Z = 0) (X : Mx F E d.m d.n) :
    R.loc w (X + Z) = R.loc w X := by
  have : d.cw w (X + Z) = d.cw w X := by
    simp only [SD.cw] at hZ ⊢
    rw [Matrix.map_add _ (map_add _), hZ, add_zero]
  unfold RD.loc
  rw [this]

def psiW (R : RD d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (w : InfinitePlace F) (X : Mx F E d.m d.n) : ℂ :=
  (∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' X)) * g fun k => (d.crd X k).2

theorem vg_tens (R : RD d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (w : InfinitePlace F) :
    vg R g = R.tens w (fP 1) (psiW R g w) := by
  funext X
  simp only [vg, RD.tens, psiW]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
  ring

theorem psiW_indep (R : RD d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (w : InfinitePlace F) :
    ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → psiW R g w (X + Z) = psiW R g w X := by
  intro X Z h1 h2
  have e1 : (∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' (X + Z))) = ∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' X) :=
    Finset.prod_congr rfl fun w' hw' => by rw [loc_add_of R w' (h1 w' (Finset.ne_of_mem_erase hw'))]
  have e2 : (fun k => (d.crd (X + Z) k).2) = fun k => (d.crd X k).2 := by
    funext k
    rw [crd_add]
    show (d.crd X k).2 + (d.crd Z k).2 = (d.crd X k).2
    rw [crd_fin h2, add_zero]
  unfold psiW
  rw [e1, e2]

theorem gauss_indep (R : RD d) :
    ∀ X Z, (∀ w, d.cw w Z = 0) → (∏ w, fP 1 (R.loc w (X + Z))) = ∏ w, fP 1 (R.loc w X) := by
  intro X Z h
  exact Finset.prod_congr rfl fun w _ => by rw [loc_add_of R w (h w)]

theorem fP_smul_one (c : ℂ) (u : Fin d.m → Fin d.n → ℂ) : fP (c • (1 : PX d.m d.n)) u = c * fP 1 u := by
  simp only [fP, evX, MvPolynomial.smul_eq_C_mul, mul_one, MvPolynomial.eval_C, map_one, one_mul]

theorem isSchwartz_indicator_one : IsSw (fP (1 : PX d.m d.n)) := by
  obtain ⟨φ, hφ⟩ := KMain.schwartz_polyGauss (m := d.m) (n := d.n) (2 * Real.pi) (by positivity) 1
  exact ⟨φ, hφ⟩

end PositivityTheory.SiegelWeilFormula.Avac

end
