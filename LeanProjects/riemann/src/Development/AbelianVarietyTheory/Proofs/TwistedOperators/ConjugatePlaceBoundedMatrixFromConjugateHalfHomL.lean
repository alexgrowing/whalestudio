import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemCompletedLatticeIffDualSplitPlace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceColumnMemCompletedLatticeIffFrameIntegStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPartMemCompletedSelfDualLatticeIffSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjHalfOnto

open GlobalTheory.SplitHecke GlobalTheory.SplitHomLattice Formalism.L2.NTheta GlobalTheory.LatticeStable GlobalTheory.SplitScalar

variable {D : D7}

theorem cA_cA' (z : AE D) : cA D (cA D z) = z := GlobalTheory.SplitDualLat.cA_cA z

theorem cA_algebraMap (y : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) y) = algebraMap (AF D.host.F) (AE D) y := by
  change y ⊗ₜ[D.host.F] star (1 : D.host.E) = y ⊗ₜ[D.host.F] (1 : D.host.E)
  rw [star_one]

theorem chart_conj {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (hπ : Chart e v π) : Chart (cA D e) v (π.comp (cA D)) := by
  refine ⟨fun x => ?_, fun a => ?_, fun y => ?_, fun a => ?_⟩
  · obtain ⟨z, rfl⟩ := hπ.1 x
    exact ⟨cA D z, by simp only [RingHom.comp_apply, cA_cA']⟩
  · rw [RingHom.comp_apply, hπ.2.1]
    constructor
    · intro h
      have := congrArg (cA D) h
      rwa [RingHom.map_mul, cA_cA', RingHom.map_zero] at this
    · intro h
      rw [← cA_cA' e, ← RingHom.map_mul, h, RingHom.map_zero]
  · rw [RingHom.comp_apply, cA_algebraMap, hπ.2.2.1]
  · rw [RingHom.comp_apply, ← hπ.2.2.2]
    have h1 : finPart D (cA D e * a) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (e * cA D a)) := by
      rw [← GlobalTheory.SplitDualLat.finPart_cA]; congr 1; rw [map_mul, cA_cA']
    have h2 : finPart D (e * cA D a) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (cA D e * a)) := by
      rw [← GlobalTheory.SplitDualLat.finPart_cA]; congr 1; rw [map_mul, cA_cA']
    constructor
    · intro h; rw [h2]; exact GlobalTheory.SplitDualLat.sigR_mem_intAE h
    · intro h; rw [h1]; exact GlobalTheory.SplitDualLat.sigR_mem_intAE h

theorem rk_mem_lat (S T : HSp D) (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    {a : D.host.E} (ha : a ∈ D.host.AA)
    {s : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hs : s ∈ latHat D.host.F D.host.E ΛS)
    {t : Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E} (ht : t ∈ latHat D.host.F D.host.E ΛT) :
    rk S T a s t ∈ latO S T ΛS ΛT fun _ => True := by
  change rkHom S T a s t ∈ _
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    induction ht using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hs
      obtain ⟨β, hβ, y, hy, rfl⟩ := ht
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, fun _ h => absurd trivial h, a, ha, x, hx, y, hy, ?_⟩
      · rw [map_mul]; exact mul_mem (hβ v) (hα v)
      · ext i j
        change liftFin D (_ * _ * ∑ k, (α ⊗ₜ[D.host.F] star (x k)) * _) = _
        rw [Matrix.of_apply, ← liftFin_tmul]
        congr 1
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [← TensorProduct.tmul_sum, Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem conj_rk {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (he : IsSplitIdem D e) (hπ : Chart e v π) (S T : HSp D) (a : D.host.E) (s : Fin S.rank → AE D)
    (t : Fin T.rank → AE D) (p : Fin T.rank) (q : Fin S.rank) :
    π (cA D (rk S T a (fun k => finPart D (e * s k)) (fun k => finPart D (cA D e * t k)) p q)) =
      π (cA D (incA D a)) * π (cA D (t p)) * ∑ k, π (s k) * π (cA D (incA D (S.gram k q))) := by
  have h := pi_rk (isSplitIdem_conj he) (chart_conj hπ) S T a s t p q
  simp only [RingHom.comp_apply, cA_cA'] at h
  exact h

theorem frame_cancel {K : Type} [Field K] {m n : ℕ} (B : GL (Fin m) K) (C : GL (Fin n) K) {c : K} (hc : c ≠ 0)
    (y : Matrix (Fin m) (Fin n) K) : (B⁻¹).1 * (c • (B.1 * ((c⁻¹ • y) * (C⁻¹).1))) * C.1 = y := by
  rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
    Units.inv_mul, Matrix.mul_one, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem map_cA_sum_apply {K : Type} [CommRing K] (π : AE D →+* K) {S T : HSp D} {n : ℕ} (M : Fin n → WO S T)
    (p : Fin T.rank) (q : Fin S.rank) :
    π (cA D ((∑ l, M l : Matrix (Fin T.rank) (Fin S.rank) (AE D)) p q)) = ∑ l, π (cA D (M l p q)) := by
  rw [Matrix.sum_apply, GlobalTheory.SplitDualLat.ringHom_sum (cA D), GlobalTheory.SplitDualLat.ringHom_sum π]

theorem adjCo_eq_map {v : FinPl D} (φ : SplitProj D v) (hQ : ∀ x : D.host.E, rdA φ (incA D x) = rdQ φ x)
    (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)) (u : WO S T) :
    adjCo φ S T BS BT u = (BS⁻¹).1 * ((S.gram⁻¹).map (rdQ φ) *
      ((u : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map fun x => rdA φ (cA D x))ᵀ * T.gram.map (rdQ φ)) * BT.1 := by
  unfold adjCo
  congr 2
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_map, Matrix.map_map]
  simp only [Function.comp_def, hQ]

end GlobalTheory.ConjHalfOnto

namespace GlobalTheory.ConjHalfOnto

open GlobalTheory.SplitHecke GlobalTheory.SplitHomLattice Formalism.L2.NTheta GlobalTheory.LatticeStable GlobalTheory.SplitScalar

set_option maxHeartbeats 1000000 in

theorem conj_half_onto : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, a ∈ D.host.AA → a ≠ 0 → ∀ y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v), (∀ i j, Valued.v (y i j) ≤ Valued.v (rdQ φ (star a))) → ∃ u, u ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf (cA D e) u ∧ adjCo φ S T (frCo φ βS) (frCo φ βT) u = y := by
  intro D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a haA ha0 y hy
  obtain ⟨hπ, -, hQ, -, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  have hsi : IsSplitIdem D e := he.1
  have hsc : IsSplitIdem D (cA D e) := isSplitIdem_conj hsi
  have hπc := chart_conj hπ
  have hc0 : rdQ φ (star a) ≠ 0 := by
    rw [← hQ]
    intro h
    have h1 : ((rdA φ).comp (incA D)) (star a) = 0 := h
    exact ha0 (star_eq_zero.1 ((map_eq_zero_iff _ ((rdA φ).comp (incA D)).injective).1 h1))
  set c : Fv D.host.F v := rdQ φ (star a) with hcdef
  set BS := frCo φ βS with hBS
  set BT := frCo φ βT with hBT
  have hGmap : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E), M.map (rdQ φ) = M.map ((rdA φ).comp (incA D)) := by
    intro m n M; ext i j; simp only [Matrix.map_apply, RingHom.comp_apply, hQ]
  set Gs : Matrix (Fin S.rank) (Fin S.rank) (Fv D.host.F v) := S.gram.map (rdQ φ) with hGs
  set Gt : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v) := T.gram.map (rdQ φ) with hGt
  have hGtu : IsUnit Gt.det := by
    have := (GlobalTheory.LatVac.gram_det_isUnit T).map ((rdA φ).comp (incA D))
    rw [RingHom.map_det] at this
    rw [hGt, hGmap]
    exact this
  have hGsi : (S.gram⁻¹).map (rdQ φ) * Gs = 1 := by
    rw [hGs, hGmap, hGmap, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  set Z : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v) := (BT⁻¹).1 * Gt⁻¹ with hZ
  have hZ1 : Z * (Gt * BT.1) = 1 := by
    rw [hZ, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hGtu, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  have hZG : Z * Gt = (BT⁻¹).1 := by
    rw [hZ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hGtu, Matrix.mul_one]
  set Y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) := c⁻¹ • y with hY
  have hYint : ∀ l m, Valued.v (Y l m) ≤ 1 := by
    intro l m
    rw [hY, Matrix.smul_apply, smul_eq_mul, Valuation.map_mul, map_inv₀,
      inv_mul_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hc0))]
    exact hy l m
  choose σ hσ using hπ.1
  clear_value Y Z Gt Gs BT BS c
  obtain ⟨s', hs'⟩ : ∃ s' : Fin S.rank → Fin S.rank → AE D, ∀ l k, s' l k = σ (BS.1 k l) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨t', ht'⟩ : ∃ t' : Fin S.rank → Fin T.rank → AE D, ∀ l k, t' l k = cA D (σ (((fun m => Y l m) ᵥ* Z) k)) :=
    ⟨_, fun _ _ => rfl⟩
  have hs : ∀ l, (fun k => finPart D (e * s' l k)) ∈ latHat D.host.F D.host.E (ΛS : Set _) := by
    intro l
    refine (GlobalTheory.T.splitPlace_column_mem_completedLattice_iff_frame_integral D S ΛS βS hS hfS v φ e he (s' l)).2 fun i => ?_
    have h1 : (fun k => rdA φ (s' l k)) = BS.1 *ᵥ Pi.single l 1 := by
      funext k
      rw [hs', hσ, Matrix.mulVec_single_one]
      rfl
    rw [← hBS, h1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases hi : i = l
    · subst hi; rw [Pi.single_eq_same, map_one]
    · rw [Pi.single_eq_of_ne hi, map_zero]; exact zero_le_one
  have ht : ∀ l, (fun k => finPart D (cA D e * t' l k)) ∈ latHat D.host.F D.host.E (ΛT : Set _) := by
    intro l
    refine (GlobalTheory.T.conjPart_mem_completedSelfDualLattice_iff_splitPlace D T ΛT βT hT hfT v φ e he (t' l)).2 fun j => ?_
    have h1 : (fun k => rdA φ (cA D (t' l k))) = (fun m => Y l m) ᵥ* Z := by
      funext k
      rw [ht', cA_cA', hσ]
    rw [← hGt, ← hBT, h1, Matrix.vecMul_vecMul, hZ1, Matrix.vecMul_one]
    exact hYint l j
  obtain ⟨U, hU⟩ : ∃ U : WO S T,
      U = ∑ l, rk S T a (fun k => finPart D (e * s' l k)) (fun k => finPart D (cA D e * t' l k)) := ⟨_, rfl⟩
  have hUmem : U ∈ latO S T ΛS ΛT fun _ => True := by
    rw [hU]; exact sum_mem fun l _ => rk_mem_lat S T _ _ haA (hs l) (ht l)
  refine ⟨cA D e • U, smul_mem_latO D S T _ _ _ (cA D e) (idem_int hsc) _ hUmem, fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hsc.1]
  · have hentry : ∀ p q, rdA φ (cA D ((cA D e • U) p q)) =
        c * ∑ l, (Y * Z) l p * ∑ k, BS.1 k l * Gs q k := by
      intro p q
      have h0 : (cA D e • U) p q = cA D e * U p q := rfl
      rw [h0, map_mul (cA D), cA_cA', map_mul (rdA φ), he.2.2, one_mul, hU, map_cA_sum_apply]
      refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) (Finset.mul_sum _ _ _).symm
      rw [conj_rk hsi hπ S T a (s' l) (t' l) p q]
      have hYZ : ((fun m => Y l m) ᵥ* Z) p = (Y * Z) l p := rfl
      have hk : ∀ k, rdA φ (s' l k) * rdA φ (cA D (incA D (S.gram k q))) = BS.1 k l * Gs q k := by
        intro k
        rw [hs', hσ, GlobalTheory.SplitDualLat.cA_incA, hQ, GlobalTheory.LatVac.gram_star, hGs, Matrix.map_apply]
      rw [GlobalTheory.SplitDualLat.cA_incA, hQ, ← hcdef, ht', cA_cA', hσ, hYZ, Finset.sum_congr rfl fun k _ => hk k, mul_assoc]
    have hT' : (((cA D e • U : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map fun x => rdA φ (cA D x))ᵀ =
        c • (Gs * (BS.1 * (Y * Z))) := by
      ext q p
      rw [Matrix.transpose_apply, Matrix.map_apply, hentry, Matrix.smul_apply, smul_eq_mul]
      congr 1
      generalize Y * Z = W
      simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have key : (S.gram⁻¹).map (rdQ φ) * (c • (Gs * (BS.1 * (Y * Z)))) * Gt = c • (BS.1 * (Y * (BT⁻¹).1)) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc _ Gs, hGsi, Matrix.one_mul, Matrix.mul_assoc BS.1,
        Matrix.mul_assoc Y, hZG]
    rw [adjCo_eq_map φ hQ, hT', ← hGt, key, hY]
    exact frame_cancel BS BT hc0 y

end GlobalTheory.ConjHalfOnto
