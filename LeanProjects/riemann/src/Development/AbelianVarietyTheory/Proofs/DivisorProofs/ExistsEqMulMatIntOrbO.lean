import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatIntIndicatorNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenIntegrabilityFullRankOrbit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankNormalFormOrbit
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite

open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Matrix

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv.LeftScale

theorem Y0_mul_transpose {k : Type} [Field k] {n d : ℕ} (hnd : n ≤ d) : Y0 k n d * (Y0 k n d)ᵀ = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨d - n + i, by omega⟩ : Fin d)]
  · simp [Y0, Matrix.one_apply, Fin.ext_iff]
  · intro b _ hb
    have : (b : ℕ) ≠ d - n + i := fun e => hb (Fin.ext e)
    simp [Y0, this]
  · simp

theorem orbO_clopen_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ), n < d →
    IsClopen (GlobalTheory.FullRankCoinv.LeftScale.orbO k n d) ∧ IsCompact (GlobalTheory.FullRankCoinv.LeftScale.orbO k n d) ∧
      ∀ Y ∈ GlobalTheory.FullRankCoinv.LeftScale.orbO k n d, Y.rank = n := by
  intro k _ _ _ _ n d hnd
  haveI := SplitWeil.t2Space k
  have e : orbO k n d = (fun κ : GL (Fin d) k => Y0 k n d * κ.val) '' (KO k (Fin d) : Set (GL (Fin d) k)) :=
    Set.ext fun Y => ⟨fun ⟨κ, h, e⟩ => ⟨κ, h, e.symm⟩, fun ⟨κ, h, e⟩ => ⟨κ, h, e.symm⟩⟩
  have hc : IsCompact (orbO k n d) := e ▸ isCompact_KO.image (by fun_prop)
  have hemb : Topology.IsOpenEmbedding (fun g : GL (Fin d) k => g.val) := by
    refine ⟨isEmbedding_val_GL, ?_⟩
    have : Set.range (fun g : GL (Fin d) k => g.val) = (fun A => A.det) ⁻¹' {0}ᶜ := by
      ext A
      exact (Matrix.isUnit_iff_isUnit_det A).trans isUnit_iff_ne_zero
    rw [this]
    exact isOpen_compl_singleton.preimage (continuous_id.matrix_det)
  refine ⟨⟨hc.isClosed, isOpen_iff_mem_nhds.2 ?_⟩, hc, ?_⟩
  · rintro _ ⟨κ, hκ, rfl⟩
    have ho := hemb.isOpenMap _ (isOpen_KO (k := k) (n := Fin d))
    have hcont : Continuous fun Z : Matrix (Fin n) (Fin d) k => κ.val + (Y0 k n d)ᵀ * (Z - Y0 k n d * κ.val) := by
      fun_prop
    refine Filter.mem_of_superset ((ho.preimage hcont).mem_nhds ⟨κ, hκ, by simp⟩) ?_
    rintro Z ⟨κ', hκ', e'⟩
    refine ⟨κ', hκ', ?_⟩
    simp only at e'
    rw [e', Matrix.mul_add, ← Matrix.mul_assoc, Y0_mul_transpose hnd.le, Matrix.one_mul, add_sub_cancel]
  · rintro _ ⟨κ, -, rfl⟩
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 κ.isUnit)]
    refine le_antisymm (by simpa using Matrix.rank_le_height (Y0 k n d)) ?_
    have := Matrix.rank_mul_le_left (Y0 k n d) (Y0 k n d)ᵀ
    rwa [Y0_mul_transpose hnd.le, Matrix.rank_one, Fintype.card_fin] at this

theorem invariant_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (Λ : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ),
      (∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
        (m : ℂ) * Λ (fun Y => φ (Y * h.val)) = Λ φ) →
      ∀ κ ∈ GlobalTheory.SplitWeil.KO k (Fin d), ∀ φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Λ (fun Y => φ (Y * κ.val)) = Λ φ := by
  intro k _ _ _ _ n d Λ hΛ κ hκ φ hφ
  obtain ⟨m, hm0, hm⟩ := hΛ κ
  have hcomp : ∀ (h : GL (Fin d) k), (fun Y : Matrix (Fin n) (Fin d) k => φ (Y * h.val)) ∈ fullRk k n d := fun h => by
    simpa using comp_mem_fullRk (1 : GL (Fin n) k) h hφ
  have hpow : ∀ r : ℕ, (m : ℂ) ^ r * Λ (fun Y => φ (Y * (κ ^ r).val)) = Λ φ := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [← ih, ← hm _ (hcomp (κ ^ r)), pow_succ, mul_assoc, pow_succ']
      simp only [Units.val_mul, Matrix.mul_assoc]
  haveI := finiteIndex_stabKO hφ.1
  obtain ⟨r, hr0, -, hr⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := stabKO φ)) (⟨κ, hκ⟩ : KO k (Fin d))
  have h1 := hpow r
  have h2 : (fun Y : Matrix (Fin n) (Fin d) k => φ (Y * (κ ^ r).val)) = φ := funext fun Y => hr Y
  rw [h2] at h1
  by_cases h0 : Λ φ = 0
  · have := hm φ hφ
    rw [h0] at this ⊢
    exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hm0.ne')
  · have h3 : (m : ℂ) ^ r = 1 := mul_right_cancel₀ h0 (by rw [h1, one_mul])
    have h4 : m ^ r = 1 := by exact_mod_cast h3
    have h5 : m = 1 := (pow_eq_one_iff_of_nonneg hm0.le hr0.ne').1 h4
    simpa [h5] using hm φ hφ

theorem exists_eq_mul_matInt_orbO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (ν : MeasureTheory.Measure k) [ν.IsAddHaarMeasure] (n d : ℕ),
    IsClopen (GlobalTheory.FullRankCoinv.LeftScale.orbO k n d) → IsCompact (GlobalTheory.FullRankCoinv.LeftScale.orbO k n d) →
    (∀ Y ∈ GlobalTheory.FullRankCoinv.LeftScale.orbO k n d, Y.rank = n) →
    ∀ Λ : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ,
      (∀ κ ∈ GlobalTheory.SplitWeil.KO k (Fin d), ∀ φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Λ (fun Y => φ (Y * κ.val)) = Λ φ) →
      ∃ C : ℂ, ∀ φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, φ Y ≠ 0 → Y ∈ GlobalTheory.FullRankCoinv.LeftScale.orbO k n d) →
        Λ φ = C * GlobalTheory.FullRankCoinv.LeftScale.matInt ν φ := by
  intro k _ _ _ _ _ _ ν _ n d hO hc hr Λ hΛ
  classical
  have h1 := indicator_one_mem_fullRk hO hc hr
  have hne := matInt_indicator_ne_zero ν hO.isOpen hc ⟨Y0 k n d, 1, one_mem _, by simp⟩
  refine ⟨Λ ((orbO k n d).indicator fun _ => 1) / matInt ν ((orbO k n d).indicator fun _ => 1), fun φ hφ hs => ?_⟩
  haveI := finiteIndex_stabKO hφ.1
  haveI : Fintype (KO k (Fin d) ⧸ stabKO φ) := Fintype.ofFinite _
  let f : KO k (Fin d) ⧸ stabKO φ → Matrix (Fin n) (Fin d) k → ℂ := fun q Y => φ (Y * q.out.val.val)
  have hf : ∀ (κ : KO k (Fin d)) Y, f (κ : KO k (Fin d) ⧸ stabKO φ) Y = φ (Y * κ.val.val) := by
    intro κ Y
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul (stabKO φ) κ
    simp only [f]
    rw [hs, Subgroup.coe_mul, Units.val_mul, ← Matrix.mul_assoc]
    exact s.2 _
  have hinv : ∀ (κ : KO k (Fin d)) Y, ∑ q, f q (Y * κ.val.val) = ∑ q, f q Y := by
    intro κ Y
    refine Fintype.sum_equiv (MulAction.toPerm κ) _ _ fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAction.toPerm_apply, MulAction.Quotient.smul_mk, hf, hf, smul_eq_mul, Subgroup.coe_mul, Units.val_mul,
      Matrix.mul_assoc]
  have hsum : ∑ q, f q = (∑ q, f q (Y0 k n d)) • (orbO k n d).indicator fun _ => (1 : ℂ) := by
    funext Y
    rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hY : Y ∈ orbO k n d
    · rw [Set.indicator_of_mem hY, mul_one]
      obtain ⟨κ, hκ, rfl⟩ := hY
      exact hinv ⟨κ, hκ⟩ _
    · rw [Set.indicator_of_notMem hY, mul_zero]
      refine Finset.sum_eq_zero fun q _ => ?_
      by_contra h0
      obtain ⟨κ, hκ, e⟩ := hs _ h0
      refine hY ⟨κ * (q.out.val)⁻¹, mul_mem hκ (inv_mem q.out.2), ?_⟩
      rw [Units.val_mul, ← Matrix.mul_assoc, ← e, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.mul_one]
  have hmem : ∀ q, f q ∈ fullRk k n d := fun q => by
    simpa using comp_mem_fullRk (1 : GL (Fin n) k) q.out.val hφ
  have eΛ := congrArg Λ hsum
  have eI := congrArg (matInt ν) hsum
  rw [map_sum, map_smul, smul_eq_mul, Finset.sum_congr rfl fun q _ => hΛ _ q.out.2 φ hφ] at eΛ
  have hI : ∀ q, matInt ν (f q) = matInt ν φ := fun q => by
    have := matInt_comp ν (1 : GL (Fin n) k) q.out.val φ
    rw [show nabs k (gdet q.out.val) = 1 from GlobalTheory.LGrp.nabs_det_of_mem_KO q.out.2] at this
    simpa [nabs] using this
  rw [matInt_sum ν _ f fun q _ => (hmem q).1, matInt_smul, Finset.sum_congr rfl fun q _ => hI q] at eI
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at eΛ eI
  have hN : (Fintype.card (KO k (Fin d) ⧸ stabKO φ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  apply mul_left_cancel₀ hN
  rw [eΛ, mul_left_comm, eI]
  field_simp

theorem exists_sum_pieces : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ), n < d →
    IsClopen (GlobalTheory.FullRankCoinv.LeftScale.orbO k n d) →
    ∀ φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∃ (s : Finset (GL (Fin d) k))
      (ψ : GL (Fin d) k → Matrix (Fin n) (Fin d) k → ℂ), φ = ∑ h ∈ s, ψ h ∧
        ∀ h ∈ s, ψ h ∈ GlobalTheory.FullRankCoinv.fullRk k n d ∧
          ∀ Y, ψ h (Y * h.val) ≠ 0 → Y ∈ GlobalTheory.FullRankCoinv.LeftScale.orbO k n d := by
  intro k _ _ _ _ n d hnd hO φ hφ
  classical
  let V : GL (Fin d) k → Set (Matrix (Fin n) (Fin d) k) := fun h => (fun Z => Z * (h⁻¹).val) ⁻¹' orbO k n d
  have hV : ∀ h, IsClopen (V h) := fun h => hO.preimage (by fun_prop)
  have hcan : ∀ (h : GL (Fin d) k) (Z : Matrix (Fin n) (Fin d) k), Z * h.val * (h⁻¹).val = Z := fun h Z => by
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hcl : IsClosed (Function.support φ) := by
    have h := (hφ.1.1.isOpen_fiber 0).isClosed_compl
    convert h using 1
    ext Y; simp [Function.mem_support]
  have hcs : IsCompact (Function.support φ) := IsCompact.of_isClosed_subset hφ.1.2 hcl (subset_tsupport φ)
  obtain ⟨s, hs⟩ := hcs.elim_finite_subcover V (fun h => (hV h).isOpen) fun Y hY => by
    obtain ⟨h, rfl⟩ := exists_eq_normal_form_mul_of_rank_eq k n d hnd.le Y (by_contra fun h => hY (hφ.2 Y h))
    exact Set.mem_iUnion.2 ⟨h, 1, one_mem _, by simp only [hcan]; simp⟩
  have key : ∀ (s : Finset (GL (Fin d) k)), ∀ φ ∈ fullRk k n d, (∀ Y, φ Y ≠ 0 → ∃ h ∈ s, Y ∈ V h) →
      ∃ ψ : GL (Fin d) k → Matrix (Fin n) (Fin d) k → ℂ, φ = ∑ h ∈ s, ψ h ∧
        ∀ h ∈ s, ψ h ∈ fullRk k n d ∧ ∀ Y, ψ h Y ≠ 0 → Y ∈ V h := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro φ _ h
      refine ⟨0, funext fun Y => ?_, by simp⟩
      by_contra h0
      simpa using h Y (by simpa using h0)
    | insert a s ha ih =>
      intro φ hφ h
      obtain ⟨ψ, hψ, hψ'⟩ := ih _ (Reduce.indicator_mem (hV a).compl hφ) fun Y hY => by
        have h1 := Set.mem_of_indicator_ne_zero hY
        rw [Set.indicator_of_mem h1] at hY
        obtain ⟨b, hb, hb'⟩ := h Y hY
        rcases Finset.mem_insert.1 hb with rfl | hb
        · exact absurd hb' h1
        · exact ⟨b, hb, hb'⟩
      refine ⟨Function.update ψ a ((V a).indicator φ), ?_, fun b hb => ?_⟩
      · rw [Finset.sum_insert ha, Function.update_self, Finset.sum_congr rfl fun b hb =>
          Function.update_of_ne (fun e : b = a => ha (e ▸ hb)) _ ψ, ← hψ, Set.indicator_self_add_compl]
      · rcases Finset.mem_insert.1 hb with rfl | hb
        · rw [Function.update_self]
          exact ⟨Reduce.indicator_mem (hV _) hφ, fun Y hY => Set.mem_of_indicator_ne_zero hY⟩
        · rw [Function.update_of_ne (fun e : b = a => ha (e ▸ hb))]
          exact hψ' b hb
  obtain ⟨ψ, h1, h2⟩ := key s φ hφ fun Y hY => by simpa using hs hY
  refine ⟨s, ψ, h1, fun h hh => ⟨(h2 h hh).1, fun Y hY => ?_⟩⟩
  have := (h2 h hh).2 _ hY
  rwa [Set.mem_preimage, hcan] at this

theorem induction_orbO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ), n < d →
    ∀ P : GL (Fin d) k → Prop, (∀ a b, P a → P b → P (a * b)) →
      (∀ h : GL (Fin d) k, (∃ Y ∈ GlobalTheory.FullRankCoinv.LeftScale.orbO k n d, Y * h.val ∈ GlobalTheory.FullRankCoinv.LeftScale.orbO k n d) → P h) →
      ∀ h, P h := by
  intro k _ _ _ _ n d hnd P hmul hP h
  classical
  have row : ∀ (i : Fin d) (h : GL (Fin d) k), (∀ a b, a ≠ i → h.val a b = (1 : Matrix (Fin d) (Fin d) k) a b) → P h := by
    intro i h hh
    let z : Fin d := ⟨0, by omega⟩
    have hs : Matrix.GeneralLinearGroup.swap k z i ∈ KO k (Fin d) :=
      ⟨Matrix.GeneralLinearGroup.swap _ z i, Matrix.GeneralLinearGroup.map_swap _ _ _⟩
    have hY : Y0 k n d * Matrix.swap k z i ∈ orbO k n d := ⟨_, hs, rfl⟩
    have h0 : ∀ a, (Y0 k n d * Matrix.swap k z i) a i = 0 := fun a => by
      rw [Matrix.mul_swap_apply_right]
      have : (0 : ℕ) ≠ d - n + a := by omega
      simp [Y0, z, this]
    refine hP h ⟨_, hY, ?_⟩
    convert hY using 1
    generalize Y0 k n d * Matrix.swap k z i = Y at h0
    conv_rhs => rw [← Matrix.mul_one Y]
    ext a b
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : c = i
    · rw [hc, h0, zero_mul, zero_mul]
    · rw [hh c b hc]
  have diag : ∀ (c : Fin d → kˣ) (s : Finset (Fin d)), P (diagGL fun i => if i ∈ s then c i else 1) := by
    intro c s
    induction s using Finset.induction_on with
    | empty => exact row ⟨0, by omega⟩ _ fun a b _ => by simp [diagGL]
    | insert i s hi ih =>
      have := hmul _ _ (row i (diagGL fun j => if j = i then c i else 1) fun a b ha => by
        simp [diagGL, Matrix.diagonal_apply, Matrix.one_apply, ha]) ih
      convert this using 1
      ext a b
      simp only [diagGL, Units.val_mul, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
      by_cases ha : a = i
      · subst ha; simp [hi]
      · simp [ha]
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => ∀ g : GL (Fin d) k, g.val = M → P g) h.val
    ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero (fun D hD g hg => ?_) (fun t g hg => ?_)
    (fun A B hA hB pA pB g hg => ?_) h rfl
  · rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hD
    convert diag (fun i => Units.mk0 (D i) (hD i (Finset.mem_univ i))) Finset.univ using 1
    ext a b
    simp [diagGL, hg]
  · refine row t.i g fun a b ha => ?_
    rw [hg]
    simp [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.single, ha.symm]
  · have := hmul _ _ (pA (Matrix.GeneralLinearGroup.mkOfDetNeZero A hA) rfl)
      (pB (Matrix.GeneralLinearGroup.mkOfDetNeZero B hB) rfl)
    convert this using 1
    exact Units.ext hg

end GlobalTheory.FullRankCoinv.LeftScale
