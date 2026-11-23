import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainEq

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Atop

open PositivityTheory.SiegelWeilFormula.KMain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cosetSum_const_mul {G : Type} [Group G] (Pp Γ : Subgroup G) (a : ℂ) (f : G → ℂ) (g : G) :
    GlobalTheory.Eis.cosetSum Pp Γ (fun y => a * f y) g = a * GlobalTheory.Eis.cosetSum Pp Γ f g := by
  simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term]
  exact tsum_mul_left

theorem ident_lincomb (hT : TAll) (hSK : SecK) (hEW : EisWk) (d : SD σ) (c : ℂ) {k : ℕ} (a : Fin k → ℂ)
    (Ψ : Fin k → d.Fn) (hK : ∀ i, d.KFin (Ψ i))
    (hI : ∀ i x, HolValueAt (fun z => d.eis (d.sec0 (Ψ i)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (Ψ i) x))
    (x : d.G) :
    HolValueAt (fun z => d.eis (d.sec0 (∑ i, a i • Ψ i)) (s0 d.m d.n) z x) (s0 d.m d.n)
      (c * d.I (∑ i, a i • Ψ i) x) := by
  have hsch : ∀ i, a i • Ψ i ∈ d.sch := fun i => d.sch.smul_mem _ (hK i).1
  have hv : d.I (∑ i, a i • Ψ i) x = ∑ i, a i * d.I (Ψ i) x := by
    rw [I_sum d hT.2.2.2.1 hT.2.2.2.2 Finset.univ _ (fun i _ => hsch i), Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [I_smul d hT.2.2.2.1 (a i) (hK i).1]
    rfl
  have key : ∀ i, HolValueAt (fun z => a i * d.eis (d.sec0 (Ψ i)) (s0 d.m d.n) z x) (s0 d.m d.n)
      (a i * (c * d.I (Ψ i) x)) := fun i => (holValueAt_const (a i) _).mul (hI i x)
  have hconv : ∀ i, ∃ t : ℝ, ∀ z : ℂ, t < z.re → GlobalTheory.Eis.CosetConv (par2 σ d.Y) (rat2 σ d.Y)
      (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (Ψ i) y) x := by
    intro i
    obtain ⟨U, pp, Ê, t, -, -, -, -, -, -, -, hc⟩ := eisAll_of hSK hEW d _ (hK i) (s0 d.m d.n)
    refine ⟨t, fun z hz => ?_⟩
    obtain ⟨u, hu, hle⟩ := (hc z hz).1 {x} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hle x rfl q) hu
  choose tt htt using hconv
  have hsec : d.sec0 (∑ i, a i • Ψ i) = fun y => ∑ i, a i * d.sec0 (Ψ i) y := by
    funext y
    rw [← secl_apply, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  have heq : EqRight (fun z => ∑ i, a i * d.eis (d.sec0 (Ψ i)) (s0 d.m d.n) z x)
      (fun z => d.eis (d.sec0 (∑ i, a i • Ψ i)) (s0 d.m d.n) z x) := by
    refine ⟨∑ i, |tt i|, fun z hz => ?_⟩
    have hz' : ∀ i, tt i < z.re := fun i =>
      lt_of_le_of_lt ((le_abs_self _).trans
        (Finset.single_le_sum (fun j _ => abs_nonneg (tt j)) (Finset.mem_univ i))) hz
    have hc' : ∀ i ∈ Finset.univ, GlobalTheory.Eis.CosetConv (par2 σ d.Y) (rat2 σ d.Y)
        (fun y => a i * (((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (Ψ i) y)) x := fun i _ =>
      (htt i z (hz' i)).of_norm_le (C := ‖a i‖) fun y => (norm_mul _ _).le
    have := cosetSum_finsum (par2 σ d.Y) (rat2 σ d.Y) Finset.univ
      (fun i y => a i * (((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (Ψ i) y)) x hc'
    show ∑ i, a i * d.eis (d.sec0 (Ψ i)) (s0 d.m d.n) z x = d.eis (d.sec0 (∑ i, a i • Ψ i)) (s0 d.m d.n) z x
    rw [hsec]
    unfold SD.eis
    have e2 : (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * ∑ i, a i * d.sec0 (Ψ i) y) =
        fun y => ∑ i, a i * (((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (Ψ i) y) := by
      funext y
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e2, this]
    exact Finset.sum_congr rfl fun i _ => (cosetSum_const_mul _ _ _ _ _).symm
  have hval : c * d.I (∑ i, a i • Ψ i) x = ∑ i, a i * (c * d.I (Ψ i) x) := by
    rw [hv, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hval]
  exact (holValueAt_finsum Finset.univ fun i _ => key i).congr heq

end PositivityTheory.SiegelWeilFormula.Atop

end
