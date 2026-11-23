import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QDivBdQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleModelsOfHtBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundAffine
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovHt.Link.BdFin

section General

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.TrueGeo.SmallSec
  GlobalTheory.TrueGeo.BddFin GlobalTheory.LineNorm

variable {F : Type} [Field F] [NumberField F]

theorem fromModel_of_induced {C : CxSt F} {Y : Var F} {A : Adl C Y} {M : TrueGeo.Model Y} {L : HermLB M.p} {k : ℕ+}
    (h : A.Induced M L k 0) : FromModel Y A.D (eqn A.D) A.lg := by
  obtain ⟨-, r, hr, -, hfin⟩ := h
  exact ⟨M, L.B, k, r, L.isLB, hr, fun v e y yt i hy hi => by rw [hfin v e y yt i hy hi]; simp⟩

theorem fromModel_comb {Y : Var F} {ι : Type} [Fintype ι] (ρ : ι → Adl (cxSt F) Y) (t : ι → ℚ)
    (g : ∀ σ, Pts Y σ → ℝ) (h : ∀ i, FromModel Y (ρ i).D (eqn (ρ i).D) (ρ i).lg) :
    FromModel Y (comb ρ t g).D (eqn (comb ρ t g).D) (comb ρ t g).lg := by
  have h₁ := good_sum Finset.univ fun i _ =>
    (show Good Y (ρ i).D (eqn (ρ i).D) (ρ i).lg from ⟨fun y => Base.isEqn_eqn _ y, h i⟩).zsmul (combNum ρ t i)
  have h₂ := h₁.change (t' := eqn (comb ρ t g).D) fun y => Base.isEqn_eqn _ y
  have e : (comb ρ t g).lg = fun v e y =>
      Real.log (e.w (valAt y.1 (((∏ i, eqn (ρ i).D (below y.1) ^ combNum ρ t i) *
        (eqn (comb ρ t g).D (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn))) + ∑ i, (combNum ρ t i : ℝ) * (ρ i).lg v e y := by
    funext v e y
    simp only [GlobalTheory.ShFam.comb, GlobalTheory.ShFam.combEqn, div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [e]
  exact h₂

theorem exists_pow_le {C : CxSt F} {Y : Var F} {A : Adl C Y} (hA : FromModel Y A.D (eqn A.D) A.lg) {τ : ℕ}
    {f : Y.Fn} (hf : f ∈ A.secs τ) :
    ∃ (a : 𝓞 F) (k : ℕ+), a ≠ 0 ∧ ∀ v e y,
      NumberField.HeightOneSpectrum.adicAbv F v a * A.nrmFin v τ f e y ^ (A.n * k : ℕ) ≤ 1 := by
  obtain ⟨M, L, k, r, hL, hr, hfin⟩ := hA
  have := M.ar.isIntegral
  have := isPreimmersion_j M
  have : QuasiCompact M.p := by
    obtain ⟨N, c, hc, h⟩ := M.ar.isProjOver
    have := isProper_str (𝓞 F) N
    rw [← h]
    infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace M.p
  have hη := j_gen_specializes M
  choose t ht using fun i : L.ι => fnMap_surjective M.j hη ((f ^ (A.n : ℕ)) ^ (k : ℕ) * (r fun _ => i) ^ τ)
  have hmem {x : Y.X} {i : L.ι} (h : M.j x ∈ L.U i) :
      x ∈ (L.pull M.j).U fun _ => i := Set.mem_iInter.2 fun _ => h
  have hreg (x : Y.X) (i : L.ι) (h : M.j x ∈ L.U i) : RegAt (M.j x) (t i) := by
    have hu : A.D.IsEqn _ (eqn A.D x) := Base.isEqn_eqn _ _
    have hb := ((hu.nsmul τ).regularAt_iff).1 (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 hf _)
    rw [Units.val_pow_eq_pow_val] at hb
    rw [← regAt_fnMap_iff M.j hη, ht, ← regAt_iff hu (hr.isEqn _ x (hmem h)), pow_mul, ← mul_pow]
    exact regAt_pow hb _
  obtain ⟨a, ha, hb⟩ := exists_bound M.p L.U (exists_chart hL) t fun i z hz h => by
    obtain ⟨z, rfl⟩ := mem_range_j M h
    exact hreg z i hz
  refine ⟨a, k, ha, fun v e y => ?_⟩
  obtain ⟨yt, h⟩ := exists_lift M e y
  obtain ⟨i, hi, h₁⟩ := hb v e yt (by rw [h, Category.assoc, M.pb.w, ← Category.assoc, y.2])
  have h₂ : M.j (below y.1) ∈ L.U i := by
    change below (y.1 ≫ M.j) ∈ _
    rw [← h]
    exact hi (x := spMap e.O.subtype (IsLocalRing.closedPoint _)) trivial
  rw [h] at h₁
  have hl := hfin v e y yt (fun _ => i) h hi
  rw [nrmFin_pow A hf e y (hr.isEqn _ _ (hmem h₂)) (c := 0) (by rw [hl, sub_zero]), ← ht,
    valAt_fnMap _ _ _ (hreg _ i h₂), mul_zero, neg_zero, Real.exp_zero, mul_one]
  exact h₁ (hreg _ i h₂)

theorem nrmFin_one_pow {C : CxSt F} {Y : Var F} (A : Adl C Y) (v : HeightOneSpectrum (𝓞 F)) (e : Ext v)
    (y : AlgPt Y) (h : RegAt (below y.1) (eqn A.D (below y.1) : Y.Fn)) (τ : ℕ) :
    A.nrmFin v τ 1 e y = A.nrmFin v 1 1 e y ^ τ := by
  have hn : (0 : ℝ) ≤ e.w (valAt y.1 (eqn A.D (below y.1) : Y.Fn)) := e.w.nonneg _
  simp only [Adl.nrmFin, one_pow, one_mul, pow_one, Nat.cast_one, one_mul, valAt_pow h, map_pow, mul_pow]
  congr 1
  · rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hn, ← Real.rpow_mul hn, mul_comm]
  · rw [← Real.exp_nat_mul]
    ring_nf

end General

end GlobalTheory.CovHt.Link.BdFin

namespace GlobalTheory.CovHt.Link.BdFin

open GlobalTheory.LineNorm

theorem fromModel_bdQ {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} {Φ : s.Flag}
    {hm : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL)} {h0 : RefMets Φ} (P : PolDat s Φ hm h0) (k : s.Comp) :
    FromModel (Φ.C k).Y (bdQ P k).D (eqn (bdQ P k).D) (bdQ P k).lg := by
  refine fromModel_comb _ _ _ fun o => ?_
  cases o with
  | none =>
    obtain ⟨M, L, q, hi, -⟩ := P.ab_model k
    exact fromModel_of_induced hi
  | some x =>
    have hw : ∀ a ∈ (rootSym S.Dw (fun _ => false) none (DV.tauEmb D x.1) x.2).support,
        {q | a.1 q = true}.Finite := by
      intro a ha
      have e : a.1 = fun _ => false := by
        unfold rootSym at ha
        split_ifs at ha <;>
        · have := Finsupp.support_single_subset ha
          rw [Finset.mem_singleton] at this
          rw [this]
      simp [e]
    exact exists_model_lgOf HTBound.htBound D A N j S κ s Φ (admEx_of_htBound HTBound.htBound D A N j S κ) k _ hw

end GlobalTheory.CovHt.Link.BdFin

namespace GlobalTheory.CovHt.Link

open GlobalTheory.LineNorm GlobalTheory.CovHt.Link.BdFin

theorem BdFin.eff_nsmul_of_eff {F : Type} [Field F] {Y : Var F} {Δ : Y.Dv} (h : Δ.Eff) (m : ℕ) : (m • Δ).Eff := by
  induction m with
  | zero => exact zero_nsmul Δ ▸ CartierDiv.eff_zero
  | succ n ih => exact succ_nsmul Δ n ▸ ih.add h

theorem nrmFin_one_bdQ_le : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (x : ToroidalCompactificationData s) (P : Mean4O.PolOf x Φ) (k : s.Comp), ∃ c : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ, (Function.support c).Finite ∧ ∀ v e y, (bdQ P k).nrmFin v 1 1 e y ≤ Real.exp (c v) := by
  intro _ _ D A N j S κ s Φ x P k

  obtain ⟨q, hq, hsec⟩ : ∃ q : ℕ, 0 < q ∧ (1 : (Φ.C k).Y.Fn) ∈ (bdQ P k).secs q := by
    have hn0 : (((bdQ P k).n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (bdQ P k).n.ne_zero
    have h₁ := congrArg ((((bdQ P k).n : ℕ) : ℚ) • ·) (qDiv_bdQ P k)
    simp only [qDiv, TensorProduct.smul_tmul', smul_eq_mul, mul_inv_cancel₀ hn0, mul_one] at h₁
    have e : ((((bdQ P k).n : ℕ) : ℤ) : ℚ) ⊗ₜ[ℤ] P.bd k = 1 ⊗ₜ ((((bdQ P k).n : ℕ) : ℤ) • P.bd k) := by
      rw [← TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]
    rw [Int.cast_natCast, natCast_zsmul] at e
    rw [e] at h₁
    obtain ⟨q, hq, h⟩ := one_tmul_eq_iff.1 h₁
    refine ⟨q, hq, ?_⟩
    show (1 : (Φ.C k).Y.Fn) ^ ((bdQ P k).n : ℕ) ∈ (Φ.C k).Y.H0 (q • (bdQ P k).D)
    rw [one_pow, h, smul_smul]
    exact Var.eff_iff_one_mem.1 (eff_nsmul_of_eff (P.eff_bd k) _)
  obtain ⟨a, m, ha, hb⟩ := BdFin.exists_pow_le (fromModel_bdQ P k) hsec
  set K : ℕ := q * ((bdQ P k).n * m : ℕ) with hK
  have hK0 : K ≠ 0 := Nat.mul_ne_zero hq.ne' (Nat.mul_ne_zero (bdQ P k).n.ne_zero m.ne_zero)
  have ha0 : (a : D.what₂.LL) ≠ 0 := by simpa using ha
  refine ⟨fun v => -Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v a) / K, ?_, fun v e y => ?_⟩
  · refine (Ideal.finite_factors (I := Ideal.span {a}) (by simpa using ha)).subset fun v hv => ?_
    have h₁ : NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v a ≠ 1 := fun h1 => hv (by simp [h1])
    have h₂ := v.adicAbv_coe_le_one (K := D.what₂.LL) (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a
    exact Ideal.dvd_span_singleton.2
      ((v.adicAbv_coe_lt_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a).1 (lt_of_le_of_ne h₂ h₁))
  · by_cases hr : RegAt (below y.1) (eqn (bdQ P k).D (below y.1) : (Φ.C k).Y.Fn)
    · have h0 : 0 < NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v a := AbsoluteValue.pos _ ha0
      have hZ : 0 ≤ (bdQ P k).nrmFin v 1 1 e y := by
        unfold Adl.nrmFin
        exact mul_nonneg (Real.rpow_nonneg (e.w.nonneg _) _) (Real.exp_pos _).le
      have h₁ := hb v e y
      rw [nrmFin_one_pow _ v e y hr, ← pow_mul, ← hK] at h₁
      refine (pow_le_pow_iff_left₀ hZ (Real.exp_pos _).le hK0).1 ?_
      rw [← Real.exp_nat_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hK0), Real.exp_neg, Real.exp_log h0]
      rw [← one_div, le_div_iff₀ h0, mul_comm]
      exact h₁
    · have : (bdQ P k).nrmFin v 1 1 e y = 0 := by
        simp only [Adl.nrmFin, one_pow, one_mul, pow_one]
        rw [TrueGeo.valAt, dif_neg hr, map_zero,
          Real.zero_rpow (one_div_ne_zero (Nat.cast_ne_zero.2 (bdQ P k).n.ne_zero)), zero_mul]
      rw [this]
      exact (Real.exp_pos _).le

end GlobalTheory.CovHt.Link
