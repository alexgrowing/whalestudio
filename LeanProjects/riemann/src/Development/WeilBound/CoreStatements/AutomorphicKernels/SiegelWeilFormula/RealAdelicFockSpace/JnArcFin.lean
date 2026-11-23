import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.THeis
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.FockLatticeInjective
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.IntSch

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

abbrev Yf (d : SD σ) : Type := Fin d.m × Fin d.n × Fin 2 → Af F

abbrev Iw (d : SD σ) : Type := InfinitePlace F × Fin d.m × Fin d.n × Bool

abbrev Vw (d : SD σ) : Type := EuclideanSpace ℝ (Iw d)

def fin (d : SD σ) (X : Mx F E d.m d.n) : Yf d := fun k => (d.crd X k).2

def arc (R : RD d) (X : Mx F E d.m d.n) : Vw d :=
  (EuclideanSpace.equiv (Iw d) ℝ).symm fun i => if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im

def gau (R : RD d) (X : Mx F E d.m d.n) : ℂ := ∏ w, fP (1 : PX d.m d.n) (R.loc w X)

def vac (R : RD d) (g : Yf d → ℂ) (X : Mx F E d.m d.n) : ℂ := gau R X * g (fin d X)

theorem vac_mem (R : RD d) {g : Yf d → ℂ} (hg : g ∈ SB (Yf d)) : vac R g ∈ R.fock :=
  Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩

theorem exists_lift (hT : TAll) (hF : FockMem) (R : RD d) {g : Yf d → ℂ} (hg : g ∈ SB (Yf d)) :
    ∃ Ω ∈ d.sch, d.T Ω = vac R g :=
  (hT.1 F E σ d).2.1 _ ((hF F E σ d R).1 (vac_mem R hg))

def zOf (u : Iw d → ℝ) : InfinitePlace F → Fin d.m → Fin d.n → ℂ :=
  fun w a j => ⟨u (w, a, j, true), u (w, a, j, false)⟩

theorem arc_eq_iff (R : RD d) (X : Mx F E d.m d.n) (u : Vw d) :
    arc R X = u ↔ ∀ w, R.loc w X = zOf (EuclideanSpace.equiv (Iw d) ℝ u) w := by
  constructor
  · rintro rfl w
    funext a j
    apply Complex.ext
    · simp [zOf, arc]
    · simp [zOf, arc]
  · intro h
    apply (EuclideanSpace.equiv (Iw d) ℝ).injective
    funext i
    obtain ⟨w, a, j, b⟩ := i
    have hw := congrFun (congrFun (h w) a) j
    cases b
    · simp only [arc, ContinuousLinearEquiv.apply_symm_apply, Bool.false_eq_true, if_false]
      rw [hw]
      rfl
    · simp only [arc, ContinuousLinearEquiv.apply_symm_apply, if_true]
      rw [hw]
      rfl

theorem exists_jn (R : RD d) (u : Vw d) (y : Yf d) : ∃! X : Mx F E d.m d.n, arc R X = u ∧ fin d X = y := by
  obtain ⟨L, hL⟩ := KFock.archEquiv d R
  set Z := zOf (EuclideanSpace.equiv (Iw d) ℝ u) with hZ
  let cI := L.symm Z
  let c : Fin d.m × Fin d.n × Fin 2 → AF F := fun k =>
    (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (cI k)) (y k) : AF F)
  have hc1 : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) = cI := by
    funext k
    exact RingEquiv.apply_symm_apply _ _
  refine ⟨d.cmb c, ⟨?_, ?_⟩, ?_⟩
  · rw [arc_eq_iff]
    intro w
    rw [← hL c w, hc1]
    show L (L.symm Z) w = Z w
    rw [ContinuousLinearEquiv.apply_symm_apply]
  · funext k
    show (d.crd (d.cmb c) k).2 = y k
    rw [KFock.crd_cmb']
  · rintro X ⟨hX1, hX2⟩
    rw [arc_eq_iff] at hX1
    have e1 : L (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1) = Z := by
      funext w
      rw [hL, KFock.cmb_crd]
      exact hX1 w
    have e2 : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1) = cI := by
      have h := congrArg L.symm e1
      rwa [ContinuousLinearEquiv.symm_apply_apply] at h
    have e3 : d.crd X = c := by
      funext k
      refine Prod.ext ?_ ?_
      · apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
        rw [congrFun e2 k]
        exact (congrFun hc1 k).symm
      · exact congrFun hX2 k
    rw [← e3, KFock.cmb_crd]

def jn (R : RD d) (u : Vw d) (y : Yf d) : Mx F E d.m d.n := (exists_jn R u y).exists.choose

theorem arc_jn (R : RD d) (u : Vw d) (y : Yf d) : arc R (jn R u y) = u := (exists_jn R u y).exists.choose_spec.1

theorem fin_jn (R : RD d) (u : Vw d) (y : Yf d) : fin d (jn R u y) = y := (exists_jn R u y).exists.choose_spec.2

theorem jn_arc_fin (R : RD d) (X : Mx F E d.m d.n) : jn R (arc R X) (fin d X) = X :=
  ((exists_jn R (arc R X) (fin d X)).unique (exists_jn R (arc R X) (fin d X)).exists.choose_spec ⟨rfl, rfl⟩)

def hg (R : RD d) (νf : Measure (Yf d)) (f : Mx F E d.m d.n → ℂ) (g : Yf d → ℂ) (u : Vw d) : ℂ :=
  ∫ y, f (jn R u y) * star (g y) ∂νf

def B (ν : Measure (Mx F E d.m d.n)) (Φ Ψ : d.Fn) : ℂ := ∫ X, d.T Φ X * star (d.T Ψ X) ∂ν

end PositivityTheory.SiegelWeilFormula.KFP

end
