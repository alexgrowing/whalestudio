import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightInvertiblePairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatWeightPairProductUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedUnitSumComponentStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatUnit
open GlobalTheory.FlatLine

theorem val_sum_nonneg {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    {la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : Formalism.L2.Pj.IsVal la v) {ι : Type}
    (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, 0 ≤ v (f i)) : 0 ≤ v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hv.zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))) (hv.add _ _)

theorem val_nsmul_nonneg {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    {la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : Formalism.L2.Pj.IsVal la v) (n : ℕ) {f : R}
    (h : 0 ≤ v f) : 0 ≤ v (n • f) := by
  have := val_sum_nonneg hv (Finset.range n) (fun _ => f) (fun _ _ => h)
  simpa [Finset.sum_const, Finset.card_range] using this

theorem pnorm_sum_le {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) {ι : Type} (s : Finset ι) (P : ι → ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ)
    (y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) : X.pnorm la (∑ i ∈ s, P i) y ≤ ∑ i ∈ s, X.pnorm la (P i) y := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
    Real.rpow_nonneg (norm_nonneg _) _)
  rw [Finset.sum_apply]
  exact norm_sum_le _ _

theorem exists_flat_unit : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ N : ℕ, 0 < N ∧ ∀ w : GlobalTheory.AllWt.Psi T.Q.H → ℤ, ∃ (φ φ' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), φ ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) (GlobalTheory.FlatLine.parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) ∧ t ≠ 0 ∧ φ * φ' = t • 1 ∧ (∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v φ') ∧ ∀ σ, GoodEmb Y.d.c₂ σ → ∀ kk, ∃ C : ℝ, ∀ y ∈ ((Y.U σ).X kk).dom, ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) (GlobalTheory.FlatLine.parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) kk) (rdU (Y.U σ) φ kk) y ≤ C := by
  intro hP D T j Y e o hY hE
  obtain ⟨N, hN, hA⟩ := GlobalTheory.T.exists_flat_weight_invertible_pair hP D T j Y e o hY hE
  refine ⟨N, hN, fun w => ?_⟩
  classical
  let G : Psi T.Q.H → WTZ D.host.E := fun τ => wtOf (T.Q.Dw j) ((N : ℤ) • flatWt (T.Q.Dw j) τ) 0
  let φw : GlobalTheory.AllWt.Weight (T.Q.Dw j) →+ WTZ D.host.E :=
    { toFun := fun la => wtOf (T.Q.Dw j) la 0, map_zero' := GlobalTheory.AllWt.wtOf_zero,
      map_add' := fun a b => wtOf_add' a b }
  have hsum : wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0 = ∑ τ, (-w τ) • G τ := by
    rw [parWt_eq_sum]
    show φw _ = _
    rw [map_sum]
    refine Finset.sum_congr (Finset.eq_univ_of_forall fun x => by simp) fun τ _ => ?_
    show φw _ = (-w τ) • φw _
    rw [map_zsmul, map_zsmul, smul_smul]
    congr 1; ring
  have hpair : ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) τ, ∃ s t : Rul Y.d.Xo₂ Y.d.c₂, (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (G τ)) ∧ t ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (G τ)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (G τ) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(G τ)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • t) := fun Z τ => by
    obtain ⟨s, i, h⟩ := hA Z τ
    exact ⟨s, i, h, GlobalTheory.T.flat_weight_pair_product_unit hP D T j Y e o hY hE (N : ℤ) Z τ s i h⟩
  have hZ : ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂), ∃ s t : Rul Y.d.Xo₂ Y.d.c₂, (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)) ∧ t ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • t) := fun Z => by
    obtain ⟨s, t, h⟩ := GlobalTheory.T.exists_boundedUnit_sum_component _ _ _ _ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D) Z (Psi T.Q.H) G
      (fun τ => GlobalTheory.AllWt.even_wtOf _ _) (hpair Z) (fun τ => -w τ)
    refine ⟨s, t, ?_⟩
    rw [hsum]
    exact h
  choose s t hst using hZ
  haveI := CompFin.finite_comp Y.d.Xo₂ Y.d.c₂
  haveI := Fintype.ofFinite (Comp Y.d.Xo₂ Y.d.c₂)
  choose m hm hv using fun Z => (hst Z).2
  have hsZ : ∀ Z, s Z ∈ GlobalTheory.AllWt.suppOn Z := fun Z => by
    rw [← (hst Z).1.2.2.1, mul_comm]; exact GlobalTheory.AllWt.mul_mem_suppOn _ (idem_mem_suppOn Z)
  have htZ : ∀ Z, t Z ∈ GlobalTheory.AllWt.suppOn Z := fun Z => by
    rw [← (hst Z).1.2.2.2.1, mul_comm]; exact GlobalTheory.AllWt.mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hM0 : ((∏ Z, m Z : ℕ) : Y.d.c₂.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun Z _ => (hm Z).ne')
  refine ⟨∑ Z, s Z, ((∏ Z, m Z : ℕ) : Y.d.c₂.F) • ∑ Z, t Z, ((∏ Z, m Z : ℕ) : Y.d.c₂.F),
    Submodule.sum_mem _ fun Z _ => (hst Z).1.1, hM0, ?_, ?_, ?_⟩
  · rw [mul_smul_comm, Finset.sum_mul_sum]
    have hd : ∑ Z, ∑ Z', s Z * t Z' = ∑ Z, idem Z := Finset.sum_congr rfl fun Z _ => by
      rw [Finset.sum_eq_single Z]
      · exact (hst Z).1.2.2.2.2.1
      · intro Z' _ hne
        rw [← (hst Z).1.2.2.1, ← (hst Z').1.2.2.2.1, mul_mul_mul_comm, idem_mul_idem_of_ne (Ne.symm hne),
          zero_mul]
      · intro h; exact absurd (Finset.mem_univ Z) h
    rw [hd, sum_idem]
  · intro la' v hv'
    have hV := isVal_valSet la' v hv'
    rw [Finset.smul_sum]
    refine val_sum_nonneg hV _ _ fun Z _ => ?_
    rcases mem_valOn_or (Z := Z) hv' with h | h
    · have hsplit : ((∏ Z, m Z : ℕ) : Y.d.c₂.F) • t Z =
          (∏ Z' ∈ Finset.univ.erase Z, m Z') • ((m Z : Y.d.c₂.F) • t Z) := by
        rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ Z), Nat.cast_mul, mul_comm, mul_smul]
        exact Nat.cast_smul_eq_nsmul Y.d.c₂.F _ _
      rw [hsplit]
      exact val_nsmul_nonneg hV _ (hv Z la' v h).2
    · rw [h _ (Submodule.smul_mem _ _ (htZ Z))]
      exact le_top
  · intro σ hσ kk
    choose C hC using fun Z => (hst Z).1.2.2.2.2.2 σ hσ
    have hL := GlobalTheory.AllWt.lieFacZ_pos (Dw := T.Q.Dw j) (xiR D)
      (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)
    refine ⟨∑ Z, max (C Z) 0 / GlobalTheory.AllWt.lieFacZ (T.Q.Dw j) (xiR D)
      (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0), fun y hy => ?_⟩
    have e1 : rdU (Y.U σ) (∑ Z, s Z) kk = ∑ Z, rdU (Y.U σ) (s Z) kk := by
      rw [map_sum, Finset.sum_apply]
    rw [e1]
    refine (pnorm_sum_le _ _ _ _ y).trans (Finset.sum_le_sum fun Z _ => ?_)
    by_cases hz : (⟨kk, y⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((Y.U σ).X k).Ψ D.R.r) ∈ framesOn (Y.U σ) Z
    · rw [le_div_iff₀ hL]
      have h1 := (hC Z ⟨kk, y⟩ hz).1
      calc _ = GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)
            (s Z) ⟨kk, y⟩ := by unfold GlobalTheory.AllWt.homN GlobalTheory.AllWt.ptN; ring
        _ ≤ C Z := h1
        _ ≤ max (C Z) 0 := le_max_left _ _
    · have h0 : rdU (Y.U σ) (s Z) kk y = 0 := GlobalTheory.AllWt.rdU_eq_zero (Y.U σ) (hsZ Z) hz
      have : ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ)
          (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) kk) (rdU (Y.U σ) (s Z) kk) y = 0 := by
        unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm; rw [h0, norm_zero, zero_mul]
      rw [this]
      exact div_nonneg (le_max_right _ _) hL.le

end GlobalTheory.FlatUnit

end
