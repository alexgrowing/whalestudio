import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict

noncomputable section

namespace GlobalTheory.CuspSplit

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 200000

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem idem_mul_mem_cuspOn (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c) {G : WTZ D.host.E}
    (F : cuspW Xo c U G) : idem Z * (F : Rul Xo c) ∈ cuspOn U Z G := by
  refine ⟨GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2, ?_⟩
  rw [mul_comm]
  exact mul_mem_suppOn _ (idem_mem_suppOn Z)

theorem idem_mul_of_mem_cuspOn {Z : Comp Xo c} {G : WTZ D.host.E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) :
    idem Z * f = f :=
  (mem_suppOn_iff_idem_mul (cuspW_le_secZ G hf.1) Z).1 hf.2

theorem idem_mul_eq_zero {Z Z' : Comp Xo c} (h : Z ≠ Z') {G : WTZ D.host.E} {f : Rul Xo c}
    (hf : f ∈ cuspOn U Z' G) : idem Z * f = 0 := by
  calc idem Z * f = idem Z * (idem Z' * f) := by rw [idem_mul_of_mem_cuspOn hf]
    _ = 0 := by rw [← mul_assoc, idem_mul_idem_of_ne h, zero_mul]

theorem finsum_parts (f : Rul Xo c) : ∑ᶠ Z : Comp Xo c, idem Z * f = f := by
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  rw [finsum_eq_sum_of_fintype, sum_idem_mul]

theorem mem_latOn_part (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G : WTZ D.host.E} (F : cuspW Xo c U G)
    (hF : F ∈ latW U G) (Z : Comp Xo c) :
    (⟨_, idem_mul_mem_cuspOn hU Z F⟩ : cuspOn U Z G) ∈ latOn U Z G := by
  rw [latOn, mem_supLat_iff (idem_mul_mem_cuspOn hU Z F).2]
  intro la v hv
  show 0 ≤ v (idem Z * (F : Rul Xo c))
  rw [(isVal_valOn hv).mul, val_idem hv, zero_add]
  exact (mem_supLat.1 hF) la v (valOn_subset Z la hv)

theorem mem_latW_of_parts (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G : WTZ D.host.E} (F : cuspW Xo c U G)
    (h : ∀ Z, (⟨_, idem_mul_mem_cuspOn hU Z F⟩ : cuspOn U Z G) ∈ latOn U Z G) : F ∈ latW U G := by
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  refine mem_supLat.2 ?_
  intro la v hv
  have hval := isVal_valSet la v hv
  rw [← sum_idem_mul (F : Rul Xo c)]
  refine Finset.sum_induction _ (fun x => 0 ≤ v x) (fun a b ha hb => (le_min ha hb).trans (hval.add a b))
    (by rw [hval.zero]; exact le_top) fun Z _ => ?_
  exact (mem_supLat.1 ((mem_latOn U).1 (h Z))) la v hv

theorem cuspOn_indep (G : WTZ D.host.E) : iSupIndep (fun Z : Comp Xo c => cuspOn U Z G) := fun Z => by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ Z), cuspOn U j G) ≤ LinearMap.ker (LinearMap.mulLeft c.F (idem Z)) :=
    iSup₂_le fun j hj y hy => by
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply]
      exact idem_mul_eq_zero (Ne.symm hj) hy
  have h0 : idem Z * x = 0 := by
    have := hle hx'
    rwa [LinearMap.mem_ker, LinearMap.mulLeft_apply] at this
  calc x = idem Z * x := (idem_mul_of_mem_cuspOn hx).symm
    _ = 0 := h0

theorem iSup_cuspOn (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (G : WTZ D.host.E) :
    ⨆ Z : Comp Xo c, cuspOn U Z G = cuspW Xo c U G := by
  refine le_antisymm (iSup_le fun Z => cuspOn_le U Z G) fun F hF => ?_
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  rw [← sum_idem_mul F]
  exact Submodule.sum_mem _ fun Z _ => Submodule.mem_iSup_of_mem Z (idem_mul_mem_cuspOn hU Z ⟨F, hF⟩)

theorem coe_mem_of_mem_partLat {Z : Comp Xo c} {G : WTZ D.host.E} {g : cuspW Xo c U G}
    (hg : g ∈ partLat U Z G) : (g : Rul Xo c) ∈ cuspOn U Z G := by
  obtain ⟨f, -, rfl⟩ := hg
  exact f.2

theorem partLat_indep (G : WTZ D.host.E) : iSupIndep (fun Z : Comp Xo c => partLat U Z G) := fun Z => by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ Z), partLat U j G) ≤
      (LinearMap.ker ((LinearMap.mulLeft c.F (idem Z)).comp (cuspW Xo c U G).subtype)).restrictScalars (𝓞 c.F) :=
    iSup₂_le fun j hj y hy => by
      rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.mulLeft_apply]
      exact idem_mul_eq_zero (Ne.symm hj) (coe_mem_of_mem_partLat hy)
  have h0 : idem Z * (x : Rul Xo c) = 0 := by
    have := hle hx'
    rwa [Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.mulLeft_apply] at this
  apply Subtype.ext
  calc (x : Rul Xo c) = idem Z * x := (idem_mul_of_mem_cuspOn (coe_mem_of_mem_partLat hx)).symm
    _ = 0 := h0

theorem iSup_partLat (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (G : WTZ D.host.E) :
    ⨆ Z : Comp Xo c, partLat U Z G = latW U G := by
  refine le_antisymm (iSup_le fun Z => partLat_le U Z G) fun F hF => ?_
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  have hF' : F = ∑ Z : Comp Xo c,
      (⟨idem Z * (F : Rul Xo c), GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2⟩ : cuspW Xo c U G) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact (sum_idem_mul _).symm
  rw [hF']
  refine Submodule.sum_mem _ fun Z _ => Submodule.mem_iSup_of_mem Z ?_
  exact ⟨⟨_, idem_mul_mem_cuspOn hU Z F⟩, mem_latOn_part hU F hF Z, rfl⟩

theorem splits : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ G : WTZ D.host.E, Splits U G :=
  fun _ _ _ _ _ _ _ _ _ _ hU G =>
    ⟨fun F => ⟨(finsum_parts _).symm, fun Z => idem_mul_mem_cuspOn hU Z F,
        ⟨fun hF Z => mem_latOn_part hU F hF Z, mem_latW_of_parts hU F⟩⟩,
      ⟨cuspOn_indep G, iSup_cuspOn hU G⟩, partLat_indep G, iSup_partLat hU G⟩

end GlobalTheory.CuspSplit
