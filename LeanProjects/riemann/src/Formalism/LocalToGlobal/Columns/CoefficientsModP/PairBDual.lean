import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaIndependenceHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.TauLatticeLatticeHolds

open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

section Tools

variable {K : Type} [Field K] [NumberField K]

theorem mul_mem_locP_one (w : HeightOneSpectrum (𝓞 K)) {a b : K}
    (ha : a ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)) (hb : b ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)) :
    a * b ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (1 : Submodule (𝓞 K) K) := by
  rw [mem_localized_one_iff] at *
  exact mul_mem ha hb

theorem pb_common_den {W α : Type} [AddCommGroup W] [Module (𝓞 K) W] (w : HeightOneSpectrum (𝓞 K))
    (L : Submodule (𝓞 K) W) (S : Finset α) (f : α → W) (h : ∀ i ∈ S, f i ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L) :
    ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∀ i ∈ S, s • f i ∈ L := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, lc_one_notMem w, by simp⟩
  | insert a S _ ih =>
    obtain ⟨s, hs, hS⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨t, ht, ha⟩ := (lc_mem_locP w L _).1 (h a (Finset.mem_insert_self a S))
    refine ⟨s * t, lc_mul_notMem w hs ht, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [mul_smul]; exact L.smul_mem s ha
    · rw [mul_comm, mul_smul]; exact L.smul_mem t (hS i hi)

variable {n : ℕ}

theorem pb_invTr_inv_mulVec (B : GL (Fin n) K) (x : Fin n → K) (a : Fin n) :
    ((((inside₂ K n B)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) a =
      x ⬝ᵥ fun b => (B : Matrix (Fin n) (Fin n) K) b a := by
  show ((B : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ x) a = _
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem pb_isBasisAt_dualFr (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) (Fin n → K)) (hfg : M.FG)
    (B : GL (Fin n) K) (hB : IsBasisAt w M B) : IsBasisAt w (dualFr M) (inside₂ K n B) := by
  classical
  unfold IsBasisAt at hB ⊢
  ext x
  rw [mem_localized_columnLattice_iff]
  simp only [pb_invTr_inv_mulVec]
  constructor
  · intro hx a
    obtain ⟨s, hs, hx⟩ := (lc_mem_locP w _ _).1 hx
    have hc : (fun b => (B : Matrix (Fin n) (Fin n) K) b a) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := by
      rw [hB]; exact lc_le_locP w _ (lc_col_mem_colLat B a)
    obtain ⟨t, ht, hc⟩ := (lc_mem_locP w _ _).1 hc
    refine (lc_mem_locP w _ _).2 ⟨s * t, lc_mul_notMem w hs ht, ?_⟩
    have h := hx _ hc
    rwa [smul_dotProduct, dotProduct_smul, smul_smul] at h
  · intro h
    have h1 : ∀ m ∈ M, x ⬝ᵥ m ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (1 : Submodule (𝓞 K) K) := by
      intro m hm
      have hm' : m ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B) := by rw [← hB]; exact lc_le_locP w _ hm
      rw [mem_localized_columnLattice_iff] at hm'
      have e : m = (B : Matrix (Fin n) (Fin n) K) *ᵥ (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ m) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      rw [e, Matrix.dotProduct_mulVec]
      refine Submodule.sum_mem _ fun a _ => ?_
      exact mul_mem_locP_one w (h a) (hm' a)
    obtain ⟨S, hS⟩ := hfg
    obtain ⟨s, hs, hsS⟩ := pb_common_den w (1 : Submodule (𝓞 K) K) S (fun m => x ⬝ᵥ m) fun m hm =>
      h1 m (hS ▸ Submodule.subset_span hm)
    refine (lc_mem_locP w _ _).2 ⟨s, hs, ?_⟩
    intro m hm
    rw [← hS] at hm
    rw [smul_dotProduct]
    induction hm using Submodule.span_induction with
    | mem m hm => exact hsS m hm
    | zero => rw [dotProduct_zero, smul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [dotProduct_add, smul_add]; exact add_mem ha hb
    | smul c a _ ha => rw [dotProduct_smul, smul_comm]; exact Submodule.smul_mem _ c ha

end Tools

section Dual

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem pb_pairB_osmul_left (lam : ι → DomWeight n) (s : 𝓞 K) (x y : MvPolynomial (ι × Fin n × Fin n) K) :
    pairB lam (s • x) y = s • pairB lam x y := by
  rw [Algebra.smul_def s (pairB lam x y), nb_osmul s x, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem pb_pairB_osmul_right (lam : ι → DomWeight n) (t : 𝓞 K) (x y : MvPolynomial (ι × Fin n × Fin n) K) :
    pairB lam x (t • y) = t • pairB lam x y := by
  rw [Algebra.smul_def t (pairB lam x y), nb_osmul t y, map_smul, smul_eq_mul]

theorem pb_pairB_osmul (lam : ι → DomWeight n) (s t : 𝓞 K) (x y : MvPolynomial (ι × Fin n × Fin n) K) :
    pairB lam (s • x) (t • y) = (s * t) • pairB lam x y := by
  rw [pb_pairB_osmul_left, pb_pairB_osmul_right, smul_smul]

theorem pb_osmul_mem_VV (lam : ι → DomWeight n) (s : 𝓞 K) {x : MvPolynomial (ι × Fin n × Fin n) K} (hx : x ∈ VV K lam) :
    s • x ∈ VV K lam := by
  rw [nb_osmul]
  exact Submodule.smul_mem _ _ hx

theorem pb_act_inv (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (x : Pol K ι n) :
    actP lam g (actP lam g⁻¹ x) = x := by
  rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]

theorem pb_pairB_frames (lam : ι → DomWeight n) (B : ι → GL (Fin n) K) (x y : Pol K ι n) :
    pairB lam (actP lam (invTrK B)⁻¹ x) (actP lam B⁻¹ y) = pairB lam x y := by
  conv_rhs => rw [← pb_act_inv lam (invTrK B) x, ← pb_act_inv lam B y]
  rw [pairingBInvariantK_holds]

theorem pb_dual_gen (lam : ι → DomWeight n) (T T' : Submodule (𝓞 K) (Pol K ι n))
    (hTV : ∀ x ∈ T, x ∈ VV K lam) (hTV' : ∀ x ∈ T', x ∈ VV K lam)
    (hdual : ∀ x ∈ VV K lam, (x ∈ T ↔ ∀ y ∈ T', pairB lam x y ∈ (1 : Submodule (𝓞 K) K)))
    (hfg : T'.FG)
    (hInd : ∀ (w : HeightOneSpectrum (𝓞 K)) (M : ι → Submodule (𝓞 K) (Fin n → K)) (B B' : ι → GL (Fin n) K),
      (∀ τ, IsBasisAt w (M τ) (B τ)) → (∀ τ, IsBasisAt w (M τ) (B' τ)) → ∀ F : Pol K ι n,
      (actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T ↔ actP lam B'⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T))
    (hLoc : ∀ (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsLattice K (M τ)) →
      ∀ (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (M τ) (B τ)) →
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (transLat lam T' M) =
        (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T').map ((actP lam B).restrictScalars (𝓞 K)))
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) (x : Pol K ι n)
    (hx : x ∈ VV K lam) :
    x ∈ transLat lam T (fun τ => dualFr (M τ)) ↔
      ∀ y ∈ transLat lam T' M, y ∈ VV K lam → pairB lam x y ∈ (1 : Submodule (𝓞 K) K) := by
  constructor
  · intro hxT y hy _
    rw [← lc_iInf_locP (1 : Submodule (𝓞 K) K), Submodule.mem_iInf]
    intro w
    choose B hB using fun τ => latticeBasisExists_holds K n (M τ) (hM τ) w
    have hBd : ∀ τ, IsBasisAt w (dualFr (M τ)) (invTrK B τ) :=
      fun τ => pb_isBasisAt_dualFr w _ (hM τ).fg _ (hB τ)
    obtain ⟨s, hs, hsx⟩ := (nb_mem_locP w _ _).1 ((nb_mem_transLat lam T _ x).1 hxT w _ hBd)
    obtain ⟨t, ht, hty⟩ := (nb_mem_locP w _ _).1 ((nb_mem_transLat lam T' _ y).1 hy w _ hB)
    have h := (hdual _ (hTV _ hsx)).1 hsx _ hty
    rw [pb_pairB_osmul, pb_pairB_frames] at h
    exact (lc_mem_locP w _ _).2 ⟨s * t, lc_mul_notMem w hs ht, h⟩
  · intro h
    rw [nb_mem_transLat]
    intro w B' hB'
    choose B hB using fun τ => latticeBasisExists_holds K n (M τ) (hM τ) w
    have hBd : ∀ τ, IsBasisAt w (dualFr (M τ)) (invTrK B τ) :=
      fun τ => pb_isBasisAt_dualFr w _ (hM τ).fg _ (hB τ)
    rw [hInd w _ B' (invTrK B) hB' hBd]
    have hx0V : actP lam (invTrK B)⁻¹ x ∈ VV K lam := polyAction_mem_VV lam _ hx
    have h1 : ∀ y0 ∈ T', pairB lam (actP lam (invTrK B)⁻¹ x) y0 ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (1 : Submodule (𝓞 K) K) := by
      intro y0 hy0
      have h2 : actP lam B y0 ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (transLat lam T' M) := by
        rw [hLoc M hM w B hB]
        exact ⟨y0, lc_le_locP w _ hy0, rfl⟩
      obtain ⟨t, ht, hty⟩ := (nb_mem_locP w _ _).1 h2
      have h3 := h _ hty (pb_osmul_mem_VV lam t (polyAction_mem_VV lam B (hTV' _ hy0)))
      rw [pb_pairB_osmul_right, ← pb_pairB_frames lam B, ← polyAction_mul, inv_mul_cancel, polyAction_one₂] at h3
      exact (lc_mem_locP w _ _).2 ⟨t, ht, h3⟩
    obtain ⟨S, hS⟩ := hfg
    obtain ⟨s, hs, hsS⟩ := pb_common_den w (1 : Submodule (𝓞 K) K) S
      (fun y0 => pairB lam (actP lam (invTrK B)⁻¹ x) y0) fun y0 hy0 => h1 y0 (hS ▸ Submodule.subset_span hy0)
    refine (nb_mem_locP w _ _).2 ⟨s, hs, ?_⟩
    rw [hdual _ (pb_osmul_mem_VV lam s hx0V)]
    intro y hy
    rw [← hS] at hy
    rw [pb_pairB_osmul_left]
    induction hy using Submodule.span_induction with
    | mem y hy => exact hsS y hy
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add, smul_add]; exact add_mem ha hb
    | smul c a _ ha =>
      show s • pairB lam (actP lam (invTrK B)⁻¹ x) (c • a) ∈ (1 : Submodule (𝓞 K) K)
      rw [pb_pairB_osmul_right, smul_comm]
      exact Submodule.smul_mem _ c ha

end Dual

theorem pairBDualK_of : PairBDualStd → PairBDualK := by
  intro hStd K _ _ ι _ n lam M hM x
  have hnV : ∀ y ∈ nabStd K lam, y ∈ VV K lam := fun y hy => nb_nabStd_le_VV lam y hy
  have hdV : ∀ y ∈ delStd K lam, y ∈ VV K lam := fun y hy => hnV y (delStd_le_nabStd K lam hy)
  constructor
  · have h := pb_dual_gen lam (delStd K lam) (nabStd K lam) hdV hnV (fun y hy => (hStd K ι n lam y hy).1)
      (nb_nabStd_fg lam) (fun w M B B' hB hB' F => deltaIndependence_holds K ι n lam w M B B' hB hB' F)
      (fun M hM w B hB => (nablaDeltaLocal_holds K ι n lam M hM w B hB).1) M hM x.1 x.2
    constructor
    · intro hx y hy
      rw [pairBK_apply]
      exact h.1 hx y.1 hy y.2
    · intro hx
      refine h.2 fun y hy hyV => ?_
      have := hx ⟨y, hyV⟩ hy
      rwa [pairBK_apply] at this
  · have h := pb_dual_gen lam (nabStd K lam) (delStd K lam) hnV hdV (fun y hy => (hStd K ι n lam y hy).2)
      (Submodule.FG.of_le (nb_nabStd_fg lam) (delStd_le_nabStd K lam))
      (fun w M B B' hB hB' F => nablaIndependence_holds K ι n lam w M B B' hB hB' F)
      (fun M hM w B hB => (nablaDeltaLocal_holds K ι n lam M hM w B hB).2) M hM x.1 x.2
    constructor
    · intro hx y hy
      rw [pairBK_apply]
      exact h.1 hx y.1 hy y.2
    · intro hx
      refine h.2 fun y hy hyV => ?_
      have := hx ⟨y, hyV⟩ hy
      rwa [pairBK_apply] at this

theorem pairBDual_of_K : PairBDualK → PairBDual := by
  intro hK E K _ _ _ _ ι _ n emb lam L hL x
  exact hK K ι n lam (fun τ => tauLat emb τ L) (fun τ => tauLatticeLattice_holds E K ι n emb τ L hL) x

theorem pairBDual_of : PairBDualStd → PairBDual := fun h => pairBDual_of_K (pairBDualK_of h)

end Formalism.L2.DIV
