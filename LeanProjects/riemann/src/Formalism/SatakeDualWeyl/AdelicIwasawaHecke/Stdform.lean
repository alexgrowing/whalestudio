import Formalism.SatakeDualWeyl.StatementC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureExists
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant

noncomputable section

open Matrix

namespace Formalism.UG.P

open Formalism.UG

section Stdform

variable {n : Type} [Fintype n] [DecidableEq n]

def stdformQ (M : Matrix n n ℂ) (y : n → ℂ) : ℝ :=
  (∑ i, ∑ j, starRingEnd ℂ (y i) * M i j * y j).re

theorem stdform_continuous_Q (M : Matrix n n ℂ) : Continuous (stdformQ M) := by
  unfold stdformQ
  exact Complex.continuous_re.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    ((Complex.continuous_conj.comp (continuous_apply i)).mul continuous_const).mul (continuous_apply j))

theorem stdform_Q_dot (M : Matrix n n ℂ) (y : n → ℂ) :
    stdformQ M y = (star y ⬝ᵥ (M *ᵥ y)).re := by
  unfold stdformQ
  congr 1
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def, mul_assoc]

theorem stdform_Q_reindex {m : Type} [Fintype m] [DecidableEq m] (M : Matrix n n ℂ) (e : n ≃ m)
    (y : n → ℂ) : stdformQ (M.reindex e e) (fun k => y (e.symm k)) = stdformQ M y := by
  unfold stdformQ
  congr 1
  refine Fintype.sum_equiv e.symm _ _ (fun k => ?_)
  refine Fintype.sum_equiv e.symm _ _ (fun l => ?_)
  simp [Matrix.reindex_apply]

theorem stdform_Q_real (M : Matrix n n ℂ) (hM : ∀ i j, (M i j).im = 0) (y : n → ℂ) :
    stdformQ M y = stdformQ M (fun i => ((y i).re : ℂ)) + stdformQ M (fun i => ((y i).im : ℂ)) := by
  unfold stdformQ
  simp only [Complex.re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re, Complex.mul_im, hM i j]

theorem stdform_normSq (z : ℂ) : (star z * z).re = Complex.normSq z := by
  rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

section Emb

variable {E : Type} [Field E]

theorem stdform_psd (τ : E →+* ℂ) (M : Matrix n n ℂ) (hM : ∀ i j, ∃ e, τ e = M i j) (c : ℝ)
    (hpos : ∀ x : n → E, x ≠ 0 → 0 < c * stdformQ M (fun i => τ (x i))) :
    ∀ y, 0 ≤ c * stdformQ M y := by
  intro y
  have hcont : Continuous fun y => c * stdformQ M y := continuous_const.mul (stdform_continuous_Q M)
  have hall : ∀ x : n → E, 0 ≤ c * stdformQ M (fun i => τ (x i)) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp [stdformQ]
    · exact (hpos x hx).le
  have hcl : IsClosed {y : n → ℂ | 0 ≤ c * stdformQ M y} := isClosed_le continuous_const hcont
  by_cases hre : ∃ e : E, (τ e).im ≠ 0
  · obtain ⟨e0, he0⟩ := hre
    have hsurj : Function.Surjective fun ab : ℝ × ℝ => (ab.1 : ℂ) + (ab.2 : ℂ) * τ e0 := by
      intro z
      refine ⟨(z.re - z.im / (τ e0).im * (τ e0).re, z.im / (τ e0).im), ?_⟩
      apply Complex.ext
      · simp
      · simp [he0]
    have hg : DenseRange fun ab : ℝ × ℝ => (ab.1 : ℂ) + (ab.2 : ℂ) * τ e0 := hsurj.denseRange
    have hq : DenseRange fun ab : ℚ × ℚ => ((ab.1 : ℝ), (ab.2 : ℝ)) :=
      Rat.denseRange_cast.prodMap Rat.denseRange_cast
    have h1 : DenseRange fun ab : ℚ × ℚ => τ ((ab.1 : E) + (ab.2 : E) * e0) := by
      have h0 := hg.comp hq ((Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
      convert h0 using 1
      funext ab
      simp [map_add, map_mul, map_ratCast]
    have h2 : DenseRange fun v : n → ℚ × ℚ => fun i => τ (((v i).1 : E) + ((v i).2 : E) * e0) :=
      DenseRange.piMap (fun _ => h1)
    have hsub : closure (Set.range fun v : n → ℚ × ℚ => fun i => τ (((v i).1 : E) + ((v i).2 : E) * e0)) ⊆
        {y : n → ℂ | 0 ≤ c * stdformQ M y} := by
      rw [hcl.closure_subset_iff]
      rintro _ ⟨v, rfl⟩
      exact hall fun i => ((v i).1 : E) + ((v i).2 : E) * e0
    exact hsub (by rw [h2.closure_range]; trivial)
  · push_neg at hre
    have hM' : ∀ i j, (M i j).im = 0 := fun i j => by
      obtain ⟨e, he⟩ := hM i j
      rw [← he]
      exact hre e
    have hR : ∀ r : n → ℝ, 0 ≤ c * stdformQ M (fun i => ((r i : ℝ) : ℂ)) := by
      have hclR : IsClosed {r : n → ℝ | 0 ≤ c * stdformQ M (fun i => ((r i : ℝ) : ℂ))} :=
        isClosed_le continuous_const (continuous_const.mul ((stdform_continuous_Q M).comp
          (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))))
      have hd : DenseRange fun v : n → ℚ => fun i => ((v i : ℚ) : ℝ) :=
        DenseRange.piMap (fun _ => Rat.denseRange_cast)
      have hsub : closure (Set.range fun v : n → ℚ => fun i => ((v i : ℚ) : ℝ)) ⊆
          {r : n → ℝ | 0 ≤ c * stdformQ M (fun i => ((r i : ℝ) : ℂ))} := by
        rw [hclR.closure_subset_iff]
        rintro _ ⟨v, rfl⟩
        have h3 := hall fun i => ((v i : ℚ) : E)
        simpa [map_ratCast] using h3
      intro r
      exact hsub (by rw [hd.closure_range]; trivial)
    rw [stdform_Q_real M hM' y, mul_add]
    exact add_nonneg (hR _) (hR _)

end Emb

end Stdform

theorem stdform_ext {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (ι : F →+* ℝ) :
    ∃ τ : E →+* ℂ, τ.comp (algebraMap F E) = (algebraMap ℝ ℂ).comp ι := by
  letI : Algebra F ℂ := ((algebraMap ℝ ℂ).comp ι).toAlgebra
  haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  refine ⟨(IsAlgClosed.lift : E →ₐ[F] ℂ).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : E →ₐ[F] ℂ).commutes x

section Inv

variable {n : Type} [Fintype n] [DecidableEq n] {F E : Type} [Field F] [Field E] [Algebra F E]

theorem stdform_conj (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hσ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) (e : E) :
    τ (σ e) = starRingEnd ℂ (τ e) := by
  have h := RingHom.congr_fun hσ e
  simpa using h

theorem stdform_invol (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hσ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) (e : E) : σ (σ e) = e := by
  apply τ.injective
  rw [stdform_conj σ τ hσ (σ e), stdform_conj σ τ hσ e, Complex.conj_conj]

theorem stdform_hform_map (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hσ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) (J : Matrix n n E) (x : n → E) :
    τ (hform (σ : E →+* E) J x x) =
      ∑ i, ∑ j, starRingEnd ℂ (τ (x i)) * (J.map τ) i j * τ (x j) := by
  simp only [hform, map_sum, map_mul, Matrix.map_apply, AlgHom.coe_toRingHom, stdform_conj σ τ hσ]

theorem stdform_hform_fixed (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hσ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) (J : Matrix n n E)
    (hJ : IsHerm (σ : E →+* E) J) (x : n → E) :
    σ (hform (σ : E →+* E) J x x) = hform (σ : E →+* E) J x x := by
  unfold IsHerm at hJ
  have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => by
    have h := congrFun (congrFun hJ j) i
    simpa [cT] using h
  simp only [hform, map_sum, map_mul, AlgHom.coe_toRingHom, stdform_invol σ τ hσ, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem stdform_Q_eq (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hσ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) (J : Matrix n n E) (ι : F →+* ℝ)
    (hι : τ.comp (algebraMap F E) = (algebraMap ℝ ℂ).comp ι) (x : n → E) (a : F)
    (ha : algebraMap F E a = hform (σ : E →+* E) J x x) :
    stdformQ (J.map τ) (fun i => τ (x i)) = ι a := by
  show (∑ i, ∑ j, starRingEnd ℂ (τ (x i)) * (J.map τ) i j * τ (x j)).re = ι a
  rw [← stdform_hform_map σ τ hσ J x, ← ha]
  have h := RingHom.congr_fun hι a
  simp only [RingHom.comp_apply] at h
  rw [h]
  simp

end Inv

section Sign

variable {n : Type} [Fintype n] [DecidableEq n]

private lemma re_conj_mul_self_eq_normSq (z : ℂ) : (starRingEnd ℂ z * z).re = Complex.normSq z := by
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

theorem stdform_sig_diag {p q : ℕ} (M : Matrix n n ℂ) (e : n ≃ Fin p ⊕ Fin q)
    (P : GL (Fin p ⊕ Fin q) ℂ)
    (hP : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * M.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q) (y : n → ℂ) :
    ∃ x : Fin p ⊕ Fin q → ℂ, (y ≠ 0 → x ≠ 0) ∧
      stdformQ M y = (∑ i, Complex.normSq (x (Sum.inl i))) - ∑ j, Complex.normSq (x (Sum.inr j)) := by
  have hPP : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hy' : (fun k => y (e.symm k)) = (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ (((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ (fun k => y (e.symm k))) := by
    rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
  obtain ⟨x, hx⟩ : ∃ x, (fun k => y (e.symm k)) = (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ x := ⟨_, hy'⟩
  refine ⟨x, ?_, ?_⟩
  · intro hy h0
    apply hy
    rw [h0, Matrix.mulVec_zero] at hx
    funext i
    simpa using congrFun hx (e i)
  · rw [← stdform_Q_reindex M e y, stdform_Q_dot, hx, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP]
    simp [Jpq, dotProduct, Matrix.fromBlocks_mulVec, Fintype.sum_sum_type, Complex.re_sum, stdform_normSq,
      re_conj_mul_self_eq_normSq, sub_eq_add_neg, Matrix.neg_mulVec, Matrix.one_mulVec, Complex.normSq_apply,
      Complex.neg_re, Complex.neg_im, mul_neg, Finset.sum_neg_distrib]

theorem stdform_sig_pos {p : ℕ} (M : Matrix n n ℂ) (hs : HasSignature M p 0) (y : n → ℂ)
    (hy : y ≠ 0) : 0 < stdformQ M y := by
  obtain ⟨e, P, hP⟩ := hs
  obtain ⟨x, hx0, hQ⟩ := stdform_sig_diag M e P hP y
  rw [hQ]
  simp only [Fin.sum_univ_zero, sub_zero]
  obtain ⟨k, hk⟩ := Function.ne_iff.mp (hx0 hy)
  rcases k with i | i
  · exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hk⟩
  · exact Fin.elim0 i

theorem stdform_sig_neg {q : ℕ} (M : Matrix n n ℂ) (hs : HasSignature M 0 q) (y : n → ℂ)
    (hy : y ≠ 0) : stdformQ M y < 0 := by
  obtain ⟨e, P, hP⟩ := hs
  obtain ⟨x, hx0, hQ⟩ := stdform_sig_diag M e P hP y
  rw [hQ]
  simp only [Fin.sum_univ_zero, zero_sub, neg_lt_zero]
  obtain ⟨k, hk⟩ := Function.ne_iff.mp (hx0 hy)
  rcases k with i | i
  · exact Fin.elim0 i
  · exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hk⟩

theorem stdform_sig_one : HasSignature (1 : Matrix n n ℂ) (Fintype.card n) 0 := by
  refine ⟨(Fintype.equivFin n).trans (Equiv.sumEmpty _ _).symm, 1, ?_⟩
  simp [Jpq, cT]
  ext (i | i) (j | j)
  all_goals first | exact Fin.elim0 i | exact Fin.elim0 j | simp [Matrix.one_apply]

theorem stdform_sig_neg_one : HasSignature (-1 : Matrix n n ℂ) 0 (Fintype.card n) := by
  refine ⟨(Fintype.equivFin n).trans (Equiv.emptySum _ _).symm, 1, ?_⟩
  simp [Jpq, cT]
  ext (i | i) (j | j)
  all_goals first | exact Fin.elim0 i | exact Fin.elim0 j | simp [Matrix.one_apply]

end Sign

theorem definite_form_signature : Formalism.UG.DefSig := by
  intro F E _ _ _ n _ _ σ J ι τ hσ hι hfix hJ hdet
  have hfixed : ∀ x : n → E, ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x :=
    fun x => hfix _ (stdform_hform_fixed σ τ hσ J hJ x)
  have hτx : ∀ x : n → E, x ≠ 0 → (fun i => τ (x i)) ≠ 0 := by
    intro x hx h
    apply hx
    funext i
    have := congrFun h i
    exact τ.injective (by simpa using this)
  constructor
  · intro hdef
    have hMh : IsHerm (starRingEnd ℂ) (J.map τ) := by
      have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => by
        have := congrFun (congrFun hJ j) i
        simpa [cT] using this
      ext i j
      simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
      rw [← stdform_conj σ τ hσ, hJ']
    have hMdet : IsUnit (J.map τ).det := by
      have h := (RingHom.map_det τ J).symm
      rw [show (J.map τ) = τ.mapMatrix J from rfl, h]
      exact hdet.map τ
    obtain ⟨p, q, hs⟩ := signature_exists n (J.map τ) hMh hMdet
    obtain ⟨hcard, Q, hQ⟩ := sig_data (J.map τ) p q hs
    have hM : ∀ i j, ∃ e, τ e = (J.map τ) i j := fun i j => ⟨J i j, rfl⟩
    rcases hdef with hpos | hneg
    · have hpsd := stdform_psd τ (J.map τ) hM 1 (fun x hx => by
        obtain ⟨a, ha, hιa⟩ := hpos x hx
        rw [stdform_Q_eq σ τ hσ J ι hι x a ha, one_mul]
        exact hιa)
      have hq : q = 0 := by
        by_contra hq0
        have hv := sig_quad (J.map τ) Q hQ (Pi.single (Sum.inr ⟨0, Nat.pos_of_ne_zero hq0⟩) 1)
        have := hpsd (Q *ᵥ Pi.single (Sum.inr ⟨0, Nat.pos_of_ne_zero hq0⟩) 1)
        rw [stdform_Q_dot, hv] at this
        simp [Pi.single_apply] at this
        norm_num at this
      subst hq
      have hp : p = Fintype.card n := by omega
      subst hp
      exact Or.inl hs
    · have hpsd := stdform_psd τ (J.map τ) hM (-1) (fun x hx => by
        obtain ⟨a, ha, hιa⟩ := hneg x hx
        rw [stdform_Q_eq σ τ hσ J ι hι x a ha]
        linarith)
      have hp : p = 0 := by
        by_contra hp0
        have hv := sig_quad (J.map τ) Q hQ (Pi.single (Sum.inl ⟨0, Nat.pos_of_ne_zero hp0⟩) 1)
        have := hpsd (Q *ᵥ Pi.single (Sum.inl ⟨0, Nat.pos_of_ne_zero hp0⟩) 1)
        rw [stdform_Q_dot, hv] at this
        simp [Pi.single_apply] at this
        norm_num at this
      subst hp
      have hq : q = Fintype.card n := by omega
      subst hq
      exact Or.inr hs
  · rintro (hs | hs)
    · left
      intro x hx
      obtain ⟨a, ha⟩ := hfixed x
      refine ⟨a, ha, ?_⟩
      rw [← stdform_Q_eq σ τ hσ J ι hι x a ha]
      exact stdform_sig_pos _ hs _ (hτx x hx)
    · right
      intro x hx
      obtain ⟨a, ha⟩ := hfixed x
      refine ⟨a, ha, ?_⟩
      rw [← stdform_Q_eq σ τ hσ J ι hι x a ha]
      exact stdform_sig_neg _ hs _ (hτx x hx)

theorem standard_hermitian_form_definite : Formalism.UG.StdFormDef := by
  intro F E _ _ _ _ _ n _ _ σ hσ hfix hF
  have hH1 : IsHerm (σ : E →+* E) (1 : Matrix n n E) := cT_one _
  have hHm : IsHerm (σ : E →+* E) (-1 : Matrix n n E) := by
    unfold IsHerm cT
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [one_apply, h, Ne.symm h]
  refine ⟨hH1, ⟨hF, fun ι => ?_⟩, ⟨hF, fun ι => ?_⟩⟩
  · obtain ⟨τ, hτ⟩ := stdform_ext (E := E) ι
    refine (definite_form_signature F E n σ 1 ι τ (hσ τ) hτ hfix hH1 (by simp)).mpr (Or.inl ?_)
    rw [Matrix.map_one _ (map_zero τ) (map_one τ)]
    exact stdform_sig_one
  · obtain ⟨τ, hτ⟩ := stdform_ext (E := E) ι
    refine (definite_form_signature F E n σ (-1) ι τ (hσ τ) hτ hfix hHm
      ((Matrix.isUnit_iff_isUnit_det _).mp isUnit_one.neg)).mpr (Or.inr ?_)
    have : (-1 : Matrix n n E).map τ = -1 := by
      rw [Matrix.map_neg _ (map_neg τ), Matrix.map_one _ (map_zero τ) (map_one τ)]
    rw [this]
    exact stdform_sig_neg_one

end Formalism.UG.P
