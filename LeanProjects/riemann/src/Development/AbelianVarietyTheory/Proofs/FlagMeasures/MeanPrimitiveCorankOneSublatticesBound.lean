import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleFamilyOfSteps
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemVN
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesMeanEqGenusMean
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianGenusMassEqOrbitStabilizerMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticesMoveWithIsometries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeLatIn
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CyclicDiscriminantLatticesFormOneGenus
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalLatticeOfUnimodularLandherr
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StdLatIsOrthoLatticeAndMassProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeMassRatio
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbMassStabilizerLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeRatioMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRowLatticeOrthogonalSplitPrime
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanCountPrimitiveSublatticesOverGenus

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimMeanCorankOne

theorem num (a b Mk X Y c₁ c₂ de NT HH l m : ℝ) (j : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hMk : 0 ≤ Mk)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hA : a ≤ Mk * (X * Y)) (hB : b ≤ c₁ * c₂) (hm : Mk * NT ^ j ≤ m) (hde : 1 ≤ de) (hdH : de ≤ HH)
    (hN : 1 ≤ NT) (hNH : NT ≤ HH) (hl : 0 ≤ l) :
    a * b * de ^ j * (de ^ (4 + l) * NT ^ 2 * (de * NT) ^ (2 + l)) ≤
      ((de / NT) ^ j * X * (Y * c₁ * c₂ * HH ^ (11 + 3 * l))) * m := by
  have hd0 : 0 ≤ de := by linarith
  have hN0 : 0 < NT := by linarith
  have hH1 : 1 ≤ HH := le_trans hde hdH
  have hH0 : 0 < HH := by linarith
  have hR : de ^ (4 + l) * NT ^ 2 * (de * NT) ^ (2 + l) ≤ HH ^ (11 + 3 * l) := by
    have e1 : de ^ (4 + l) ≤ HH ^ (4 + l) := Real.rpow_le_rpow hd0 hdH (by linarith)
    have e2 : NT ^ 2 ≤ HH ^ 2 := pow_le_pow_left₀ hN0.le hNH 2
    have e3 : (de * NT) ^ (2 + l) ≤ (HH * HH) ^ (2 + l) :=
      Real.rpow_le_rpow (by positivity) (mul_le_mul hdH hNH hN0.le hH0.le) (by linarith)
    have e4 : HH ^ (4 + l) * HH ^ 2 * (HH * HH) ^ (2 + l) = HH ^ (10 + 3 * l) := by
      rw [Real.mul_rpow hH0.le hH0.le, ← Real.rpow_natCast HH 2, ← Real.rpow_add hH0,
        ← Real.rpow_add hH0, ← Real.rpow_add hH0]
      congr 1; push_cast; ring
    have e5 : HH ^ (10 + 3 * l) ≤ HH ^ (11 + 3 * l) := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
    calc _ ≤ HH ^ (4 + l) * HH ^ 2 * (HH * HH) ^ (2 + l) := by
          gcongr
      _ = HH ^ (10 + 3 * l) := e4
      _ ≤ _ := e5
  have hR0 : 0 ≤ de ^ (4 + l) * NT ^ 2 * (de * NT) ^ (2 + l) := by positivity
  calc a * b * de ^ j * (de ^ (4 + l) * NT ^ 2 * (de * NT) ^ (2 + l))
      ≤ (Mk * (X * Y)) * (c₁ * c₂) * de ^ j * HH ^ (11 + 3 * l) := by gcongr
    _ = ((de / NT) ^ j * X * (Y * c₁ * c₂ * HH ^ (11 + 3 * l))) * (Mk * NT ^ j) := by
        rw [div_pow]; field_simp
    _ ≤ _ := by gcongr

end GlobalTheory.Mass.PrimMeanCorankOne

namespace GlobalTheory.Mass.PrimMeanCorankOne

theorem main : ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), UnitaryVolumeMass.stMassRatio D → Formalism.MainNotions.BridgeLemma₂.PrimitiveMeanCorankOne D large₂ u u' C' Cl Cg cb Cu cT CT C0 A := by
  intro D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hR
  letI := D.host.cmStar
  intro hyp F0 he hz what₂ hrows de hde HH hdH hNH
  obtain ⟨-, ⟨-, hTp, -, hT3, -, hTs, -⟩, -⟩ := hyp
  unfold Cnt.MeanLe
  rcases what₂.eq_empty_or_nonempty with e | ⟨Λ₀, hΛ₀⟩
  · subst e; simp
  have hΛ₀r := hrows.1 Λ₀ hΛ₀
  have hK : IsCMUnram D.host.E := D.sp.cm.cmUnram
  obtain ⟨⟨hPD, hrk⟩, hrow⟩ := GlobalTheory.Mass.RowPerp.main D u F0 he hz
  obtain ⟨hint, hcyc⟩ := hrow Λ₀ hΛ₀r
  have hs := (D.sp.X 0).herm
  have hM := (GlobalTheory.Mass.RowPerpMass.main D u F0 he hz hTp hTs Λ₀ hΛ₀r).2
  have hgen := (GlobalTheory.Mass.CyclicGenus.main _ _ _ hK hs (D.sp.X 0).nondeg _ hTp hTs).2
  have hMG := GlobalTheory.MeanGenus.mean_rows_eq_mean_genus D u hTp hT3 hTs F0 he hz what₂ hrows Λ₀ hΛ₀r
  set h := (D.sp.X 0).hT with hh
  obtain ⟨reps, hreps⟩ := (final_massBasic _ _ h hs (GlobalTheory.Mass.GenusOrb.trace_pos_of_PD h hPD) _ hint.1).1
  set N : Submodule (𝓞 D.host.E) (D.sp.X 0).V → ℕ∞ := fun L => (primSp h L (D.R.k - 1) (de ^ 2)).encard with hN
  have hNinv : ∀ γ ∈ isom h, ∀ L, N (gmap γ L) = N L := fun γ hγ L =>
    (GlobalTheory.Mass.PrimMove.main _ _ h hK hs (D.sp.X 0).nondeg ⟨γ, hγ⟩ L ⊥ _ _).2
  have hMG' := hMG reps hreps N hNinv
  have hl : (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) *
      (Cnt.cntPrim h (Lat.L0X D Λ (lf D F0)) (D.R.k - 1) de : ℝ≥0∞)) =
      ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * (N (Lat.L0X D Λ (lf D F0)) : ℝ≥0∞) := by
    refine Finset.sum_congr rfl fun Λ hΛ => ?_
    rw [(GlobalTheory.Mass.DetAgree.main _ _ h hK hs hPD _ (hrow Λ (hrows.1 Λ hΛ)).1).2.2.1]
  generalize Lat.L0X D Λ₀ (lf D F0) = L₀ at *
  obtain ⟨hm1, hm2, hst, -, hsum⟩ := GlobalTheory.Mass.GenusOrb.main _ _ h hK hs hPD L₀ hint.1
  have hr := hsum reps (fun L => (N L : ℝ≥0∞)) hreps (fun g M => by
    change ((N (gmap g.1 M) : ℕ∞) : ℝ≥0∞) = _
    rw [hNinv g.1 g.2 M])
  rw [hl]
  have hf : 1 ≤ D.R.f := by
    have h1 := D.R.toFrame.ord_pos
    have h2 : D.R.f = 2 * D.R.toFrame.ord := rfl
    omega
  have hk3 : 3 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  set t : ℕ := Lat.Tu D u ^ D.R.f with ht_def
  have ht : 1 ≤ t := Nat.one_le_pow _ _ hTp.pos
  have hmem : ∀ L ∈ genus h L₀, IsIntLat h L ∧ discN h L = t ^ 2 ∧
      (∃ s : Finset (D.sp.X 0).V, s.card ≤ 1 ∧
        dual h L = L ⊔ Submodule.span (𝓞 D.host.E) (s : Set (D.sp.X 0).V)) ∧
      ∀ x ∈ dual h L, ((Lat.Tu D u : ℕ) : 𝓞 D.host.E) • x ∈ L := by
    intro L hL
    obtain ⟨a, ⟨e⟩⟩ := (hgen L₀ L hint hcyc).1 hL
    obtain ⟨b, c⟩ := GlobalTheory.Mass.PrimMeanRow.disc_of_equiv h L _ e
    refine ⟨a, by rw [b, GlobalTheory.Mass.PrimMeanRow.finrank_E, ht_def, ← pow_mul]; ring_nf,
      ((GlobalTheory.Mass.DetAgree.main _ _ h hK hs hPD L a).2.2.2.1 1).1 c, ?_⟩
    intro x hx
    have h1 : ((Lat.Tu D u : ℕ) : 𝓞 D.host.E) • e (Submodule.Quotient.mk ⟨x, hx⟩) = 0 := by
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e (Submodule.Quotient.mk ⟨x, hx⟩))
      rw [← hr, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    have h3 : ((Lat.Tu D u : ℕ) : 𝓞 D.host.E) •
        (Submodule.Quotient.mk ⟨x, hx⟩ : ↥(dual h L) ⧸ L.comap (dual h L).subtype) = 0 :=
      e.injective (by rw [map_smul, h1, map_zero])
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h3
    exact h3
  have hU := GlobalTheory.Mass.StdMass.main _ hK
  have hT0 : ((Lat.Tu D u : ℕ) : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  have hnorm : Ideal.absNorm (Ideal.span {((Lat.Tu D u : ℕ) : 𝓞 D.host.E)}) = t ^ 2 := by
    rw [Ideal.absNorm_span_singleton, Algebra.norm_natCast, RingOfIntegers.rank,
      GlobalTheory.Mass.PrimMeanRow.finrank_E, ht_def, ← pow_mul]
    simp only [Int.natAbs_pow, Int.natAbs_natCast]
    ring_nf
  have hP := GlobalTheory.Mass.PrimMeanOne.main GlobalTheory.Mass.MaxFormula.main _ _ h hK hs hPD
    (GlobalTheory.Mass.exists_orthoLattice_of_unimodular _ hK) (D.R.k - 1) (by omega) (by rw [hrk]; omega)
    _ _ _ (hU (D.R.k - 1)).1 (hU (D.R.k - 1)).2.1 _ _ _ (hU 1).1 (hU 1).2.1 de t _ hde ht hT0 hnorm
    (genus h L₀) hst hmem
  have hv : 0 < D.host.v := Formalism.MainNotions.StandardLattice.host_v_pos D
  have hNT1 : 1 ≤ Cnt.NT D u := one_le_pow₀ (by exact_mod_cast hTp.one_le)
  have htNT : ((t : ℕ) : ℝ) = Cnt.NT D u := by
    rw [ht_def, Cnt.NT]; push_cast; rfl
  have hfd : fDeg D.host.E = D.R.f := GlobalTheory.Mass.PrimMeanRow.fDeg_E D
  have hA : Cnt.massU D.host.E (D.R.k - 1) ≤ Cnt.massS D D.R.k *
      ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
        (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f) :=
    GlobalTheory.MassRatioInvBound.mass_pred_le D hR
  have hB : Cnt.massU D.host.E 1 ≤ (classNumber D.host.E : ℝ) * 2 ^ D.R.f := by
    have e1 := ((hU 1).2.2.2.2 _ (Formalism.HermitianLattices.Ext.L3.stdForm D.host.E 1) (Formalism.HermitianLattices.Ext.L3.stdLat D.host.E 1)
      (Formalism.HermitianLattices.Ext.L3.stdLat_isOrtho D.host.E 1)).1
    have e2 := Formalism.MainNotions.BridgeLemVN.mass_std_one_le hK
    rw [e1, hfd] at e2
    push_cast at e2
    exact e2
  have hbound := num (Cnt.massU D.host.E (D.R.k - 1)) (Cnt.massU D.host.E 1) (Cnt.massS D D.R.k)
    ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f))
    ((2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f) (classNumber D.host.E : ℝ) (2 ^ D.R.f)
    de (Cnt.NT D u) HH (Real.logb 2 D.R.f) (mass h L₀) (D.R.k - 1)
    (hU (D.R.k - 1)).2.2.1.le (hU 1).2.2.1.le (hU D.R.k).2.2.1.le (by positivity)
    (by have := GlobalTheory.Mass.PrimMeanRow.one_le_rdE D; positivity) (Nat.cast_nonneg _) (by positivity)
    hA hB hM (by exact_mod_cast hde) hdH hNT1 hNH
    (Real.logb_nonneg one_lt_two (by exact_mod_cast hf))
  have key : (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * ((N (Lat.L0X D Λ (lf D F0)) : ℕ∞) : ℝ≥0∞)) *
      ENNReal.ofReal (mass h L₀) ≤
      ((∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) *
        ENNReal.ofReal (((de : ℝ) / Cnt.NT D u) ^ (D.R.k - 1) *
          (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
          (Formalism.MainNotions.BridgeLemma₂.classWeightAlt D * HH ^ (11 + 3 * Real.logb 2 D.R.f)))) * ENNReal.ofReal (mass h L₀) := by
    rw [hMG', hr, mul_assoc, ← ENNReal.ofReal_mul' hm2.le]
    refine mul_le_mul' le_rfl (hP.trans (ENNReal.ofReal_le_ofReal ?_))
    rw [hfd, htNT]
    unfold Formalism.MainNotions.BridgeLemma₂.classWeightAlt
    exact hbound
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.2 hm2).ne' ENNReal.ofReal_ne_top).1 key

end GlobalTheory.Mass.PrimMeanCorankOne
