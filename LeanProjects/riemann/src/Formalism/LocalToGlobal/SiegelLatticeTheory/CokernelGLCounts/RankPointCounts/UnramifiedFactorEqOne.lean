import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvOfVolLocPos
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdFull
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValDiffProd

noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcVal
  Formalism.L2.SG.Pf.NcVal.VolOrdW Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.SG.TypedSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem absV_prod {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (s : Finset ι)
    (f : ι → Fv F v) : absV v (∏ i ∈ s, f i) = ∏ i ∈ s, absV v (f i) := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty]
    exact absV_one v
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, absV_mul, ih]

theorem absV_alp_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (h1 : absV v (dV v) = 1)
    (r : ℕ) (i : Fin (r + 1)) : absV v (alp v r i) = 1 := by
  rw [absV_alp, h1, Real.one_rpow]

section Vols

variable {X} {ψ}

theorem zz_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) : ZZX X u u' ψ v = 1 := by
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH1, -, hO1⟩ := hN v hv (Fin (D.R.rS + 1) × Fin (D.R.rS + 1))
  have := hH1
  have hsetZ : ZZOrd (E := X.B.I.E) v D.R.rS =
      Set.univ.pi fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) =>
        {c | sc (E := X.B.I.E) v (alp v D.R.rS p.1 * alp v D.R.rS p.2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [ZZOrd, locZ, Set.mem_pi, Prod.forall]
  unfold ZZX volS
  rw [if_neg hv, hsetZ, SdW.boxScaleL_holds v (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) hfin
    (sdE (E := X.B.I.E) ψ v (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
    (fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => alp v D.R.rS p.1 * alp v D.R.rS p.2)
    (fun p => mul_ne_zero (alp_ne_zero v D.R.rS p.1) (alp_ne_zero v D.R.rS p.2)), hO1, h1, one_pow, one_mul]
  refine Finset.prod_eq_one fun p _ => ?_
  rw [absV_mul, absV_alp_one v h1, absV_alp_one v h1]
  norm_num

theorem uo_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) :
    (sdE (E := X.B.I.E) ψ v (UIdx D.R.rS) (UO (E := X.B.I.E) v D.R.rS)).toReal = 1 := by
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH2, -, hO2⟩ := hN v hv (UIdx D.R.rS)
  have := hH2
  have hsetU : UO (E := X.B.I.E) v D.R.rS =
      Set.univ.pi fun q : UIdx D.R.rS =>
        {c | sc (E := X.B.I.E) v ((alp v D.R.rS q.1.1)⁻¹ * alp v D.R.rS q.1.2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [UO, Set.mem_pi]
  rw [hsetU, SdW.boxScaleL_holds v (UIdx D.R.rS) hfin (sdE (E := X.B.I.E) ψ v (UIdx D.R.rS))
    (fun q : UIdx D.R.rS => (alp v D.R.rS q.1.1)⁻¹ * alp v D.R.rS q.1.2)
    (fun q => mul_ne_zero (inv_ne_zero (alp_ne_zero v D.R.rS q.1.1)) (alp_ne_zero v D.R.rS q.1.2)), hO2, h1,
    one_pow, one_mul]
  refine Finset.prod_eq_one fun q _ => ?_
  rw [absV_mul, absV_inv v (alp_ne_zero v D.R.rS q.1.1), absV_alp_one v h1, absV_alp_one v h1]
  norm_num

theorem unramified_factor_eq_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) : localVolumeUnit X ψ v = 1 := by
  obtain ⟨hH2, hS2, -⟩ := hN v hv (UIdx D.R.rS)
  have := hH2
  have := hS2
  unfold localVolumeUnit volU
  rw [if_neg hv, localVolumeOrdinary, Measure.prod_prod, ENNReal.toReal_mul, uo_one hN hv h1, one_mul]

theorem pp_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) (l : Fin (D.R.rS + 1)) :
    PPX X u u' ψ l v = 1 := by
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH, -, hO⟩ := hN v hv Unit
  have := hH
  have hset : (fun c : Unit → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E => c ()) ⁻¹' PPOrd (E := X.B.I.E) v D.R.rS l =
      Set.univ.pi fun _ : Unit => {c | sc (E := X.B.I.E) v (alp v D.R.rS l ^ 2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [PPOrd, Set.mem_pi]
    exact ⟨fun h i => h, fun h => h ()⟩
  unfold PPX volC
  rw [if_neg hv, hset, SdW.boxScaleL_holds v Unit hfin (sdE (E := X.B.I.E) ψ v Unit)
    (fun _ : Unit => alp v D.R.rS l ^ 2) (fun _ => pow_ne_zero _ (alp_ne_zero v D.R.rS l)), hO, h1, one_pow, one_mul]
  refine Finset.prod_eq_one fun q _ => ?_
  rw [absV_pow, absV_alp_one v h1]
  norm_num

theorem jac_one {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) : jacX X v = 1 := by
  unfold jacX jacS
  refine Finset.prod_eq_one fun l _ => ?_
  rw [if_neg hv, mul_one, absV_prod]
  rw [Finset.prod_eq_one fun i _ => by rw [absV_pow, absV_alp_one v h1, one_pow]]
  norm_num

end Vols

theorem VolOneAEC_holds (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) : VolOneAEC X u u' ψ := by
  have hN : SdNormDV X ψ := sdNormDV_of X ψ (annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different) hψ hs
  have hT : Set.Finite {v : PlX X | TypAt X v} := (typSet X.B.I.F (D.host.g 0) (D.host.g 1)).finite_toSet
  have hI := differentIdeal_ne_zero' X.B.I.F
  have hD := Ideal.hasFiniteMulSupport hI
  refine (hT.union hD).subset fun v hv => ?_
  by_contra hnot
  simp only [Set.mem_union, Set.mem_setOf_eq, Function.mem_mulSupport, not_or, not_not] at hnot
  obtain ⟨htyp, hmax⟩ := hnot
  have h1 : absV v (dV v) = 1 := by rw [absV_dV, hmax, map_one, Nat.cast_one, inv_one]
  exact hv ⟨unramified_factor_eq_one hN htyp h1, zz_one u u' hN htyp h1, fun l => pp_one u u' hN htyp h1 l, jac_one htyp h1⟩

end Formalism.L2.SG.Pf.ProdConvCut2
