import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteria
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFacts

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem iwf_exists_pow_lt {a γ : WithZero (Multiplicative ℤ)} (ha : a < 1) (hγ : γ ≠ 0) : ∃ n : ℕ, a ^ n < γ := by
  by_cases ha0 : a = 0
  · exact ⟨1, by rw [ha0, pow_one]; exact zero_lt_iff.2 hγ⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, a = WithZero.exp k := ⟨WithZero.log a, (WithZero.exp_log ha0).symm⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, γ = WithZero.exp m := ⟨WithZero.log γ, (WithZero.exp_log hγ).symm⟩
  have hk : k < 0 := by rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at ha; exact ha
  refine ⟨m.natAbs + 1, ?_⟩
  rw [← WithZero.exp_nsmul, WithZero.exp_lt_exp, nsmul_eq_mul]
  have h1 : (m.natAbs : ℤ) = |m| := Int.natCast_natAbs m
  push_cast
  have h2 : (|m| + 1) * k ≤ -(|m| + 1) := by nlinarith [abs_nonneg m]
  linarith [neg_abs_le m]

theorem iwf_le_one_of_pow_mul {a b : WithZero (Multiplicative ℤ)} (hb : b ≠ 0)
    (h : ∀ n : ℕ, a ^ n * b < 1) : a ≤ 1 := by
  by_contra ha
  push Not at ha
  have ha0 : a ≠ 0 := (zero_lt_one.trans ha).ne'
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, a = WithZero.exp k := ⟨WithZero.log a, (WithZero.exp_log ha0).symm⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, b = WithZero.exp m := ⟨WithZero.log b, (WithZero.exp_log hb).symm⟩
  have hk : 0 < k := by rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at ha; exact ha
  have h2 := h m.natAbs
  rw [← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp, nsmul_eq_mul] at h2
  have h1 : (m.natAbs : ℤ) = |m| := Int.natCast_natAbs m
  rw [h1] at h2
  nlinarith [neg_abs_le m, abs_nonneg m]

theorem iwf_cj_continuous (w : Pl E) : Continuous (cj w) := by
  unfold cj
  split_ifs with h
  · exact h.choose_spec.1
  · exact continuous_id

theorem iwf_lt_one {w : Pl E} (σ : w.adicCompletion E →+* w.adicCompletion E) (hσ : Continuous σ)
    {x : w.adicCompletion E} (hx : Valued.v x < 1) : Valued.v (σ x) < 1 := by
  have hU : {y : w.adicCompletion E | Valued.v y < 1} ∈ nhds (0 : w.adicCompletion E) :=
    Valued.mem_nhds_zero.2 ⟨1, fun y hy => by simpa using hy⟩
  have hpre : σ ⁻¹' {y : w.adicCompletion E | Valued.v y < 1} ∈ nhds (0 : w.adicCompletion E) := by
    have := hσ.continuousAt (x := (0 : w.adicCompletion E))
    rw [ContinuousAt, map_zero] at this
    exact this hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hpre
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
    (γ.isUnit.map MonoidWithZeroHom.ValueGroup₀.embedding).ne_zero
  obtain ⟨n, hn⟩ := iwf_exists_pow_lt hx hγ0
  have hm : x ^ n ∈ σ ⁻¹' {y : w.adicCompletion E | Valued.v y < 1} :=
    hγ (by simpa [Valuation.restrict_lt_iff_lt_embedding, map_pow] using hn)
  have h1 : Valued.v (σ x) ^ n < 1 := by simpa [map_pow] using hm
  by_contra h
  push Not at h
  exact absurd h1 (not_lt.2 (one_le_pow₀ h))

theorem iwf_exists_small (w : Pl E) : ∃ y : w.adicCompletion E, y ≠ 0 ∧ Valued.v y < 1 := by
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer E w
  have hv : Valued.v (π : w.adicCompletion E) = WithZero.exp (-1) := by
    rw [← hπ]
    exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w π
  refine ⟨π, fun h => ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · rw [hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

theorem iwf_le_one {w : Pl E} (σ : w.adicCompletion E →+* w.adicCompletion E) (hσ : Continuous σ)
    {x : w.adicCompletion E} (hx : Valued.v x ≤ 1) : Valued.v (σ x) ≤ 1 := by
  obtain ⟨y, hy0, hy⟩ := iwf_exists_small w
  have hσy : σ y ≠ 0 := (map_ne_zero σ).2 hy0
  refine iwf_le_one_of_pow_mul ((Valuation.ne_zero_iff
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).2 hσy) fun n => ?_
  have h : Valued.v (x ^ n * y) < 1 := by
    rw [map_mul, map_pow]
    calc Valued.v x ^ n * Valued.v y ≤ 1 * Valued.v y := mul_le_mul' (pow_le_one₀ zero_le' hx) le_rfl
      _ < 1 := by rwa [one_mul]
  have := iwf_lt_one σ hσ h
  rwa [map_mul, map_pow, map_mul, map_pow] at this

theorem iwf_Phi_apply {K : Type} [Field K] (n : ℕ) (i k : Fin n) :
    GlobalTheory.Tw.Phi n K i k = if k = i.rev then (-1) ^ (i : ℕ) else 0 := by
  simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
  have : ((i : ℕ) + (k : ℕ) + 1 = n) ↔ k = i.rev := by
    constructor
    · intro h; ext; simp only [Fin.val_rev]; omega
    · intro h; subst h; simp only [Fin.val_rev]; omega
  simp only [this]

theorem iwf_theta_apply {K : Type} [Field K] (n : ℕ) (c : K →+* K) (g : GL (Fin n) K) (i j : Fin n) :
    (GlobalTheory.CuspRep.thetaGL n c g).val i j = (-1) ^ (i : ℕ) * (-1) ^ (j : ℕ) * c ((g⁻¹).val j.rev i.rev) := by
  have hinv : ((Matrix.GeneralLinearGroup.map c g)⁻¹ : GL (Fin n) K).val = (g⁻¹).val.map c := by
    rw [← map_inv]; rfl
  show (GlobalTheory.Tw.Phi n K * ((Matrix.GeneralLinearGroup.map c g)⁻¹ : GL (Fin n) K).valᵀ * (GlobalTheory.Tw.Phi n K)ᵀ) i j = _
  rw [hinv]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, iwf_Phi_apply, ite_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem iwf_v_sign {w : Pl E} (i j : ℕ) (x : w.adicCompletion E) :
    Valued.v ((-1) ^ i * (-1) ^ j * x) = Valued.v x := by
  rw [map_mul, map_mul, map_pow, map_pow, Valuation.map_neg, map_one, one_pow, one_pow, one_mul, one_mul]

theorem iwf_theta_KGL (w : Pl E) (n : ℕ) (g : GLw n w) (hg : g ∈ GlobalTheory.LFun.KGL w n) :
    GlobalTheory.CuspRep.thetaGL n (cj w) g ∈ GlobalTheory.LFun.KGL w n := by
  have hc := iwf_cj_continuous w
  rw [GlobalTheory.CompanionTheory.IwEntries.mem_KGL_iff] at hg ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [iwf_theta_apply, iwf_v_sign]
    exact iwf_le_one _ hc (hg.2 _ _)
  · rw [show (GlobalTheory.CuspRep.thetaGL n (cj w) g)⁻¹ = GlobalTheory.CuspRep.thetaGL n (cj w) g⁻¹ from (map_inv _ g).symm,
      iwf_theta_apply, iwf_v_sign, inv_inv]
    exact iwf_le_one _ hc (hg.1 _ _)

theorem iwf_theta_iwGL (w : Pl E) (n : ℕ) (g : GLw n w) (hg : g ∈ iwGL n w) :
    GlobalTheory.CuspRep.thetaGL n (cj w) g ∈ iwGL n w := by
  have hc := iwf_cj_continuous w
  have hg' : g⁻¹ ∈ iwGL n w := inv_mem hg
  rw [(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1] at hg
  rw [(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g⁻¹).1] at hg'
  rw [(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1]
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j hij => ?_⟩
  · rw [iwf_theta_apply, iwf_v_sign]
    exact iwf_le_one _ hc (hg.2.1 _ _)
  · rw [show (GlobalTheory.CuspRep.thetaGL n (cj w) g)⁻¹ = GlobalTheory.CuspRep.thetaGL n (cj w) g⁻¹ from (map_inv _ g).symm,
      iwf_theta_apply, iwf_v_sign, inv_inv]
    exact iwf_le_one _ hc (hg.1 _ _)
  · rw [iwf_theta_apply, iwf_v_sign]
    exact iwf_lt_one _ hc (hg'.2.2 _ _ (Fin.rev_lt_rev.2 hij))

theorem iwf_KGL_eq_KO (w : Pl E) (n : ℕ) :
    GlobalTheory.LFun.KGL w n = GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) := by
  ext g
  rw [GlobalTheory.CompanionTheory.IwEntries.mem_KGL_iff, GlobalTheory.CompanionTheory.IwEntries.mem_KO_iff]

theorem iwf_isOpen_KGL (w : Pl E) (n : ℕ) : IsOpen (GlobalTheory.LFun.KGL w n : Set (GLw n w)) := by
  rw [iwf_KGL_eq_KO]
  exact GlobalTheory.SplitFlip.isOpen_KO

theorem iwf_isCompact_KGL (w : Pl E) (n : ℕ) : IsCompact (GlobalTheory.LFun.KGL w n : Set (GLw n w)) := by
  rw [iwf_KGL_eq_KO]
  exact GlobalTheory.SplitFlip.isCompact_KO

theorem iwf_iwGL_le_KGL (w : Pl E) (n : ℕ) : iwGL n w ≤ GlobalTheory.LFun.KGL w n := by
  rw [iwf_KGL_eq_KO]
  exact GlobalTheory.SmGL.iwahori_le_KO _ _

theorem iwf_isOpen_iwGL (w : Pl E) (n : ℕ) : IsOpen (iwGL n w : Set (GLw n w)) :=
  GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin n)

theorem iwf_relIndex_ne_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H K : Subgroup G}
    (hH : IsOpen (H : Set G)) (hK : IsCompact (K : Set G)) : H.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let U : OpenSubgroup K := ⟨H.subgroupOf K, hH.preimage continuous_subtype_val⟩
  haveI : Finite (K ⧸ (U : Subgroup K)) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
  exact Subgroup.index_ne_zero_of_finite

theorem iwf_isClosed_UL {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) : IsClosed (UL n w : Set (GLw n w)) := by
  rw [GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]
  exact GlobalTheory.CompanionTheory.UnitaryWitt.isClosed_UJ_one n (iwf_cj_continuous w)

theorem iw_facts_pf (w : Pl E) (hw : ¬ IsSplitAt w) (a : ℕ) (t : GLw a w) :
    IsOpen (GlobalTheory.LFun.KGL w a : Set (GLw a w)) ∧ IsCompact (GlobalTheory.LFun.KGL w a : Set (GLw a w)) ∧
    (∀ k ∈ GlobalTheory.LFun.KGL w a, thL a w k ∈ GlobalTheory.LFun.KGL w a) ∧ IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) (iwGL a w) ∧
    IsLevel (MonoidHom.id _) (GlobalTheory.LFun.KGL w a) (iwGL a w) ∧ (iwGL a w).relIndex (GlobalTheory.LFun.KGL w a) ≠ 0 ∧
    IsCompact {g : GLw a w | dcos a w t g ≠ 0} := by
  have hθ : thL a w = GlobalTheory.CuspRep.thetaGL a (cj w) := if_neg hw
  have hKo := iwf_isOpen_KGL w a
  have hKc := iwf_isCompact_KGL w a
  have hIo := iwf_isOpen_iwGL w a
  have hIK := iwf_iwGL_le_KGL w a
  have hIc : IsCompact (iwGL a w : Set (GLw a w)) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hIo) hIK
  refine ⟨hKo, hKc, fun k hk => ?_, ⟨hIo, hIK, fun k hk => ?_⟩, ⟨hIo, hIK, fun k hk => hk⟩,
    iwf_relIndex_ne_zero hIo hKc, ?_⟩
  · rw [hθ]; exact iwf_theta_KGL w a k hk
  · rw [hθ]; exact iwf_theta_iwGL w a k hk
  · have hS : IsCompact ((fun p : GLw a w × GLw a w => p.1 * t * p.2) ''
        ((iwGL a w : Set (GLw a w)) ×ˢ (iwGL a w : Set (GLw a w)))) :=
      (hIc.prod hIc).image ((continuous_fst.mul continuous_const).mul continuous_snd)
    convert hS using 1
    ext g
    simp only [Set.mem_setOf_eq, dcos, Set.mem_image, Set.mem_prod, SetLike.mem_coe]
    constructor
    · intro h
      by_contra hn
      refine h (if_neg ?_)
      rintro ⟨x, hx, z, hz, e⟩
      exact hn ⟨(x, z), ⟨hx, hz⟩, e.symm⟩
    · rintro ⟨⟨x, z⟩, ⟨hx, hz⟩, e⟩
      rw [if_pos ⟨x, hx, z, hz, e.symm⟩]
      exact one_ne_zero

theorem iwU_facts_pf (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hb : IsWitt n w b)
    (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ) :
    IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧
    IsLevel (MonoidHom.id _) (KL n w) (iwU n w b) ∧ (iwU n w b).relIndex (KL n w) ≠ 0 ∧
    IsCompact {g : UL n w | fU n w b ϖ l g ≠ 0} := by
  have hc := iwf_cj_continuous w
  have hKc : IsCompact (KL n w : Set (UL n w)) :=
    (iwf_isClosed_UL hw n).isClosedEmbedding_subtypeVal.isCompact_preimage (iwf_isCompact_KGL w n)
  have hKo : IsOpen (KL n w : Set (UL n w)) :=
    (iwf_isOpen_KGL w n).preimage (continuous_subtype_val (p := (· ∈ UL n w)))
  have hIo : IsOpen (iwU n w b : Set (UL n w)) := by
    have hcont : Continuous fun γ : UL n w => b⁻¹ * γ.1 * b :=
      (continuous_const.mul continuous_subtype_val).mul continuous_const
    have e : (iwU n w b : Set (UL n w)) = (fun γ : UL n w => b⁻¹ * γ.1 * b) ⁻¹' (iwGL n w : Set (GLw n w)) := by
      ext γ
      exact GlobalTheory.CompanionTheory.UnitaryWitt.mem_iwU_iff n w b γ
    rw [e]
    exact (iwf_isOpen_iwGL w n).preimage hcont
  have hIK : iwU n w b ≤ KL n w := by
    intro γ hγ
    have h1 := iwf_iwGL_le_KGL w n ((GlobalTheory.CompanionTheory.UnitaryWitt.mem_iwU_iff n w b γ).1 hγ)
    have h2 : γ.1 = b * (b⁻¹ * γ.1 * b) * b⁻¹ := by group
    rw [KL, Subgroup.mem_subgroupOf, h2]
    exact mul_mem (mul_mem hb.1 h1) (inv_mem hb.1)
  refine ⟨hKo, hKc, ⟨hIo, hIK, fun k hk => hk⟩, iwf_relIndex_ne_zero hIo hKc, ?_⟩
  set t : GLw n w := b * tdiag ϖ (wexp n l) * b⁻¹ with ht
  have hI : IsCompact (iwU n w b : Set (UL n w)) := GlobalTheory.CompanionTheory.UnitaryWitt.isCompact_iwU hw n b hc
  have hS : IsCompact ((fun p : UL n w × UL n w => p.1.1 * t * p.2.1) ''
      ((iwU n w b : Set (UL n w)) ×ˢ (iwU n w b : Set (UL n w)))) :=
    (hI.prod hI).image (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
      (continuous_subtype_val.comp continuous_snd))
  have e : {g : UL n w | fU n w b ϖ l g ≠ 0} = Subtype.val ⁻¹'
      ((fun p : UL n w × UL n w => p.1.1 * t * p.2.1) ''
        ((iwU n w b : Set (UL n w)) ×ˢ (iwU n w b : Set (UL n w)))) := by
    ext γ
    simp only [Set.mem_setOf_eq, fU, Set.mem_preimage, Set.mem_image, Set.mem_prod, SetLike.mem_coe]
    constructor
    · intro h
      by_contra hn
      refine h (if_neg ?_)
      rintro ⟨x, hx, z, hz, e⟩
      exact hn ⟨(x, z), ⟨hx, hz⟩, e.symm⟩
    · rintro ⟨⟨x, z⟩, ⟨hx, hz⟩, e⟩
      rw [if_pos ⟨x, hx, z, hz, e.symm⟩]
      exact one_ne_zero
  rw [e]
  exact (iwf_isClosed_UL hw n).isClosedEmbedding_subtypeVal.isCompact_preimage hS

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
