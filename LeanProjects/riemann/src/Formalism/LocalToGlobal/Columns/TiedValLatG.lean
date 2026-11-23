import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.Columns.LocWLemmas
import Formalism.LocalToGlobal.Columns.CoefficientsModP
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

def vlIntSpan {K : Type} [Field K] (s : K →+* ℂ) (Pl : Rows.Places K) (w : Pl.Pl) {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) : AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : K) (f : ι → MvPolynomial (Fin n × Fin n) ℤ),
    r ∈ intW Pl w ∧ (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = s r • Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

section Places

variable {K : Type} [Field K] [NumberField K] (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
  (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))

theorem vl_mem_iff_vAdd (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) : x ∈ w.asIdeal ↔ 0 < vAdd w (x : K) := by
  have hx' : w.valuation K (x : K) ≠ 0 := (map_ne_zero _).2 (by exact_mod_cast hx)
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
  unfold Formalism.BasicNotions.vAdd
  rw [neg_pos, ← WithZero.log_one, WithZero.log_lt_log hx' one_ne_zero]

include hval

theorem vl_mem_intW_iff (w : Pl.Pl) (r : K) :
    r ∈ intW Pl w ↔ r ∈ localization₂ (pw w).asIdeal (1 : Submodule (𝓞 K) K) := by
  rw [mem_localized_one_iff, mem_range_ow_iff]
  show (0 : WithTop ℤ) ≤ Pl.val w r ↔ _
  by_cases hr : r = 0
  · subst hr
    simp
  · rw [hval w r hr]
    have h0 : (pw w).valuation K r ≠ 0 := (map_ne_zero _).2 hr
    have e : ((0 : WithTop ℤ) ≤ ((vAdd (pw w) r : ℤ) : WithTop ℤ)) ↔ 0 ≤ vAdd (pw w) r := by
      exact_mod_cast Iff.rfl
    rw [e]
    unfold Formalism.BasicNotions.vAdd
    constructor
    · intro h
      have h1 : WithZero.log ((pw w).valuation K r) ≤ 0 := by omega
      rw [WithZero.log_le_iff_le_exp h0] at h1
      simpa using h1
    · intro h
      have h1 : WithZero.log ((pw w).valuation K r) ≤ 0 := by
        rw [WithZero.log_le_iff_le_exp h0]
        simpa using h
      omega

theorem vl_resChar_mem (w : Pl.Pl) : ((Pl.resChar w : ℕ) : 𝓞 K) ∈ (pw w).asIdeal := by
  have hl0 : ((Pl.resChar w : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 (Pl.resChar_prime w).ne_zero
  rw [vl_mem_iff_vAdd (pw w) _ hl0]
  have h1 := Pl.val_resChar w
  have hl1 : ((Pl.resChar w : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Pl.resChar_prime w).ne_zero
  rw [hval w _ hl1] at h1
  have h2 : vAdd (pw w) ((Pl.resChar w : ℕ) : K) = ((Pl.ramIdx w : ℕ) : ℤ) := by exact_mod_cast h1
  have h3 : ((((Pl.resChar w : ℕ) : 𝓞 K) : 𝓞 K) : K) = ((Pl.resChar w : ℕ) : K) := by simp
  rw [h3, h2]
  exact_mod_cast Pl.ramIdx_pos w

theorem vl_natCast_notMem (w : Pl.Pl) {s : ℕ} (hs : ¬ Pl.resChar w ∣ s) : (s : 𝓞 K) ∉ (pw w).asIdeal := by
  intro h
  have hcop : Nat.Coprime (Pl.resChar w) s := ((Pl.resChar_prime w).coprime_iff_not_dvd).2 hs
  obtain ⟨a, b, e⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 K))
  apply lc_one_notMem (pw w)
  rw [← e]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
  · simpa using vl_resChar_mem Pl pw hval w
  · simpa using h

theorem vl_algebraMap_mem_intW (w : Pl.Pl) (a : 𝓞 K) : algebraMap (𝓞 K) K a ∈ intW Pl w :=
  (vl_mem_intW_iff Pl pw hval w _).2 (lc_le_locP _ _ (Submodule.mem_one.2 ⟨a, rfl⟩))

theorem vl_inv_mem_intW (w : Pl.Pl) {t : 𝓞 K} (ht : t ∉ (pw w).asIdeal) : (algebraMap (𝓞 K) K t)⁻¹ ∈ intW Pl w := by
  rw [vl_mem_intW_iff Pl pw hval]
  refine ⟨t, ht, ?_⟩
  have h0 : algebraMap (𝓞 K) K t ≠ 0 := by
    intro h
    exact lc_ne_zero_of_notMem (pw w) ht (by exact_mod_cast (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h.trans (map_zero _).symm))
  rw [Algebra.smul_def, mul_inv_cancel₀ h0]
  exact Submodule.mem_one.2 ⟨1, map_one _⟩

end Places

section Int

variable {K : Type} [Field K] [NumberField K] (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
  (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))
  {ι : Type} [Fintype ι] {n : ℕ} (s : K →+* ℂ)

theorem vl_word_mem (lam lam' : DomWeight n) (h : lam.natW = lam'.natW) {f : MvPolynomial (Fin n × Fin n) K}
    (hf : f ∈ nbWord K lam.natW) : ∃ fZ ∈ delSq ℤ n lam', MvPolynomial.map (Int.castRingHom K) fZ = f := by
  obtain ⟨wd, rfl⟩ := hf
  refine ⟨Formalism.GradedWeylDivisibility.applyWord ℤ wd (Formalism.GradedWeylDivisibility.hw ℤ le_rfl lam'.natW), ?_, ?_⟩
  · unfold delSq Formalism.GradedWeylDivisibility.weyl
    exact Submodule.subset_span ⟨wd, rfl⟩
  · show _ = Formalism.GradedWeylDivisibility.applyWord K wd (Formalism.GradedWeylDivisibility.hw K le_rfl lam.natW)
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map, h]

theorem vl_map_smul_ten (r : K) (f : ι → MvPolynomial (Fin n × Fin n) ℤ) :
    MvPolynomial.map s (r • Formalism.L2.DIV.ten fun τ => MvPolynomial.map (Int.castRingHom K) (f τ)) =
      s r • Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
  congr 1
  show MvPolynomial.map s (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ _) = _
  rw [map_ten]
  congr 1
  funext τ
  have h : s.comp (Int.castRingHom K) = Int.castRingHom ℂ := RingHom.ext_int _ _
  rw [MvPolynomial.map_map, h]

include hval

theorem vl_map_mem_intSpan (w : Pl.Pl) (lam lam' : ι → DomWeight n) (hn : ∀ τ, (lam τ).natW = (lam' τ).natW)
    {G : Pol K ι n} (hG : G ∈ localization₂ (pw w).asIdeal (delStd K lam)) : MvPolynomial.map s G ∈ vlIntSpan s Pl w lam' := by
  obtain ⟨t, ht, htG⟩ := hG
  rw [nb_delStd_eq] at htG
  have key : ∀ H ∈ Submodule.span (𝓞 K) (nbGen fun τ => nbWord K (lam τ).natW), ∀ r ∈ intW Pl w,
      MvPolynomial.map s (r • H) ∈ vlIntSpan s Pl w lam' := by
    intro H hH
    induction hH using Submodule.span_induction with
    | mem H hH =>
      intro r hr
      obtain ⟨f, hf, rfl⟩ := hH
      choose fZ hfZ hfe using fun τ => vl_word_mem (lam τ) (lam' τ) (hn τ) (hf τ)
      refine AddSubgroup.subset_closure ⟨r, fZ, hr, hfZ, ?_⟩
      rw [← vl_map_smul_ten]
      congr 3
      funext τ
      exact (hfe τ).symm
    | zero =>
      intro r _
      rw [smul_zero, map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      intro r hr
      rw [smul_add, map_add]
      exact add_mem (hx r hr) (hy r hr)
    | smul a x _ hx =>
      intro r hr
      have e : r • a • x = (r * algebraMap (𝓞 K) K a) • x := by rw [mul_smul, nb_osmul]
      show MvPolynomial.map s (r • a • x) ∈ vlIntSpan s Pl w lam'
      rw [e]
      exact hx _ (mul_mem hr (vl_algebraMap_mem_intW Pl pw hval w a))
  have h0 : algebraMap (𝓞 K) K t ≠ 0 := by
    intro h
    exact lc_ne_zero_of_notMem (pw w) ht (by exact_mod_cast (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h.trans (map_zero _).symm))
  have e : G = (algebraMap (𝓞 K) K t)⁻¹ • (t • G) := by rw [nb_osmul, smul_smul, inv_mul_cancel₀ h0, one_smul]
  rw [e]
  exact key _ htG _ (vl_inv_mem_intW Pl pw hval w ht)

theorem vl_exists_of_mem_intSpan (w : Pl.Pl) (lam lam' : ι → DomWeight n) (hn : ∀ τ, (lam τ).natW = (lam' τ).natW)
    {P : MvPolynomial (ι × Fin n × Fin n) ℂ} (hP : P ∈ vlIntSpan s Pl w lam') :
    ∃ G ∈ localization₂ (pw w).asIdeal (delStd K lam), MvPolynomial.map s G = P := by
  induction hP using AddSubgroup.closure_induction with
  | mem P hP =>
    obtain ⟨r, f, hr, hf, rfl⟩ := hP
    refine ⟨r • Formalism.L2.DIV.ten fun τ => MvPolynomial.map (Int.castRingHom K) (f τ), ?_, vl_map_smul_ten s r f⟩
    have hT : (Formalism.L2.DIV.ten fun τ => MvPolynomial.map (Int.castRingHom K) (f τ)) ∈ delStd K lam := by
      rw [nb_delStd_eq, ← nb_tensorLat_span]
      refine Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩
      have h1 : MvPolynomial.map (Int.castRingHom K) (f τ) ∈
          (delSq ℤ n (lam' τ)).map (MvPolynomial.mapAlgHom (σ := Fin n × Fin n) (Algebra.ofId ℤ K)).toLinearMap :=
        ⟨f τ, hf τ, rfl⟩
      rw [nb_map_delSq ℤ, ← hn τ] at h1
      exact Submodule.span_le_restrictScalars ℤ (𝓞 K) _ h1
    obtain ⟨t, ht, hta⟩ := (vl_mem_intW_iff Pl pw hval w r).1 hr
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 hta
    refine ⟨t, ht, ?_⟩
    have e : t • r • (Formalism.L2.DIV.ten fun τ => MvPolynomial.map (Int.castRingHom K) (f τ)) =
        a • (Formalism.L2.DIV.ten fun τ => MvPolynomial.map (Int.castRingHom K) (f τ)) := by
      have h2 : algebraMap (𝓞 K) K t * r = algebraMap (𝓞 K) K a := by rw [ha, Algebra.smul_def]
      rw [nb_osmul t, smul_smul, h2, ← nb_osmul]
    show t • r • (Formalism.L2.DIV.ten fun τ => MvPolynomial.map (Int.castRingHom K) (f τ)) ∈ delStd K lam
    rw [e]
    exact Submodule.smul_mem _ _ hT
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨G, hG, rfl⟩ := hx
    obtain ⟨G', hG', rfl⟩ := hy
    exact ⟨G + G', add_mem hG hG', map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨G, hG, rfl⟩ := hx
    exact ⟨-G, neg_mem hG, map_neg _ _⟩

end Int

section Bases

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (Pl : Rows.Places K)
  (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
  (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))
  {ι : Type} {n : ℕ} (emb : ι → E →+* K)

theorem vl_bc_inv_mulVec (φ : E →+* K) (B : GL (Fin n) E) (x : Fin n → E) (a : Fin n) :
    ((((bc φ B)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ fun b => φ (x b)) a =
      φ ((((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x) a) := by
  rw [← map_inv, bc_coe, RingHom.map_mulVec]
  rfl

include hval

theorem vl_isBasisAt_tauLat (τ : ι) (w : Pl.Pl) (M : Submodule (𝓞 E) (Fin n → E)) (B : GL (Fin n) E)
    (hB : IsLocBasis (Pl.resChar w) (M : Set (Fin n → E)) B) : IsBasisAt (pw w) (tauLat emb τ M) (bc (emb τ) B) := by
  have h1 : ¬ Pl.resChar w ∣ 1 := fun h => (Pl.resChar_prime w).one_lt.ne' (Nat.dvd_one.1 h)
  unfold IsBasisAt
  apply le_antisymm
  · rw [← localized_localized (pw w) (colLat _)]
    refine localization_mono _ ?_
    unfold tauLat
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s', hs', hint⟩ := (hB x).1 ⟨1, h1, by simpa using hx⟩
    refine ⟨(s' : 𝓞 K), vl_natCast_notMem Pl pw hval w hs', ?_⟩
    rw [lc_mem_colLat]
    intro a
    have e : ((s' : 𝓞 K) • fun b => emb τ (x b)) = fun b => emb τ (((s' : E) • x) b) := by
      funext b
      simp [Algebra.smul_def]
    rw [e, vl_bc_inv_mulVec, Matrix.mulVec_smul]
    obtain ⟨r, hr⟩ := hint a
    exact du_map_mem_one (emb τ) (Submodule.mem_one.2 ⟨r, by rw [hr]; rfl⟩)
  · rw [← localized_localized (pw w) (tauLat emb τ M)]
    refine localization_mono _ ?_
    unfold colLat
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨s', hs', hmem⟩ := (hB (fun a => (B : Matrix (Fin n) (Fin n) E) a j)).2 ⟨1, h1, fun a => by
      have e : (((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ fun a => (B : Matrix (Fin n) (Fin n) E) a j) a =
          (1 : Matrix (Fin n) (Fin n) E) a j := by
        have h2 : ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * (B : Matrix (Fin n) (Fin n) E) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        rw [← h2]
        rfl
      rw [e, Matrix.one_apply]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩⟩
    refine ⟨(s' : 𝓞 K), vl_natCast_notMem Pl pw hval w hs', ?_⟩
    refine Submodule.subset_span ⟨_, hmem, ?_⟩
    funext b
    simp [Algebra.smul_def, bc_coe]

end Bases

section Dict

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (Pl : Rows.Places K)
  (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
  (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))
  {ι : Type} [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (s : K →+* ℂ)

def vlBd (B : GL (Fin n) E) : ι → GL (Fin n) K := fun τ => inside₂ K n (bc (emb τ) B)

theorem vl_coord (J : Matrix (Fin n) (Fin n) E) (lam : ι → DomWeight n) (B : GL (Fin n) E) (F : VV K lam) :
    evV emb J lam s F = fnOf _ (shiftOf lam) (atInf (embAt s emb) ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
      (MvPolynomial.map s (actP lam (vlBd emb B)⁻¹ F.1)) := by
  have h := evFr_coord (gramC J (embAt s emb)) s lam (vlBd emb B) F.1
  have e : (fun τ => (((vlBd emb B τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map s)ᵀ) =
      atInf (embAt s emb) ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
    funext τ
    show ((((bc (emb τ) B)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ.map s)ᵀ =
      ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (s.comp (emb τ))
    rw [← map_inv, bc_coe]
    refine Matrix.ext fun a b => ?_
    rfl
  rw [← e]
  exact h

include hval

theorem vl_mem_delAtr_iff (hpw : Function.Surjective pw) (J : Matrix (Fin n) (Fin n) E) (lam lam' : ι → DomWeight n)
    (hn : ∀ τ, (lam τ).natW = (lam' τ).natW) (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsLattice E M) (F : VV K lam) :
    F ∈ delAtr emb lam M ↔ ∀ (w : Pl.Pl) (B : GL (Fin n) E), IsLocBasis (Pl.resChar w) (M : Set (Fin n → E)) B →
      ∃ P ∈ vlIntSpan s Pl w lam', evV emb J lam s F =
        fnOf _ (shiftOf lam) (atInf (embAt s emb) ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) P := by
  have hbas : ∀ (w : Pl.Pl) (B : GL (Fin n) E), IsLocBasis (Pl.resChar w) (M : Set (Fin n → E)) B →
      ∀ τ, IsBasisAt (pw w) (dualFr (tauLat emb τ M)) (vlBd emb B τ) := fun w B hB τ =>
    pb_isBasisAt_dualFr (pw w) _ (tauLatticeLattice_holds E K ι n emb τ M hM).fg _ (vl_isBasisAt_tauLat Pl pw hval emb τ w M B hB)
  show F.1 ∈ transLat lam (delStd K lam) (fun τ => dualFr (tauLat emb τ M)) ↔ _
  rw [nb_mem_transLat]
  constructor
  · intro h w B hB
    exact ⟨_, vl_map_mem_intSpan Pl pw hval s w lam lam' hn (h (pw w) _ (hbas w B hB)), vl_coord emb s J lam B F⟩
  · intro h w' Bd hBd
    obtain ⟨w, rfl⟩ := hpw w'
    have : Fact (Pl.resChar w).Prime := ⟨Pl.resChar_prime w⟩
    obtain ⟨B, hB⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (Pl.resChar w) E M hM.fg hM.span_eq_top
    obtain ⟨P, hP, hPe⟩ := h w B hB
    obtain ⟨G, hG, rfl⟩ := vl_exists_of_mem_intSpan Pl pw hval s w lam lam' hn hP
    rw [vl_coord emb s J lam B F] at hPe
    have hinj := fnOf_injective (gramC J (embAt s emb)) (shiftOf lam)
      (atInf (embAt s emb) ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
      (fun τ => Matrix.isUnits_det_units (Matrix.GeneralLinearGroup.map (embAt s emb τ) B⁻¹)) ⟨fun _ => 1, fun _ => by simp⟩ hPe
    have hG' : actP lam (vlBd emb B)⁻¹ F.1 = G := MvPolynomial.map_injective s s.injective hinj
    rw [deltaIndependence_holds K ι n lam (pw w) _ Bd (vlBd emb B) hBd (hbas w B hB) F.1, hG']
    exact hG

end Dict

end Formalism.L2.Col
