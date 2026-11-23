import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.GoodNe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCMTypeEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLNeZeroNat

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.HeckeBridge GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
open GlobalTheory.CMVal (IsHeckeL IsCMType eulerFactor)

theorem exists_hchar_unitary (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) : IsCMExt F E σ → ∀ χ : Chr F E, IsHecke F E χ → ∃ H : Formalism.L2.Host.HChar E, H.IsUnitary ∧
      (∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ), H.loc W x = locChar χ W x) ∧
      ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (m : InfinitePlace F → ℤ), HasExp τ χ m →
        H.HasInf (fun w => (τ w).1) m := by
  intro hcm χ hχ
  obtain ⟨Φ, j, -, hΦc, hj, hΦ⟩ := exists_tensor_adele_equiv F E σ hcm
  have hfin : ∀ x : E, finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = algebraMap E (FiniteAdeleRing (𝓞 E) E) x := fun x => by
    rw [show finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from toFinAd_tmul 1 x, map_one, one_mul]
  let u : Neutral.B1.Ideles E →* (AF F ⊗[F] E)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦc
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  have hdiag : ∀ k : Eˣ, u (Neutral.B1.diagUnits E k) = Units.map (inclR (F := F) (AF F)).toMonoidHom k := fun k =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ]
      change (algebraMap E (InfiniteAdeleRing E) k, algebraMap E (FiniteAdeleRing (𝓞 E) E) k) = _
      refine Prod.ext (hj k).symm (hfin k).symm))
  have hloc : ∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ),
      u (Neutral.B1.localIdele E W x) = locIdele F W x := fun W x =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ, infTens_locIdele, map_one, finTens_locIdele]
      rfl))
  let H : Formalism.L2.Host.HChar E := ⟨Circle.toUnits.comp (χ.comp u), ht.comp (hχ.1.comp hu), fun k => by
    change Circle.toUnits (χ (u _)) = 1
    rw [hdiag, hχ.2, map_one]⟩
  refine ⟨H, fun x => Circle.norm_coe (χ (u x)), fun W x => ?_, fun τ m hm k => ?_⟩
  · change Circle.toUnits (χ (u _)) = Circle.toUnits (χ (locIdele F W x))
    rw [hloc]
  · set z := u (Formalism.L2.Host.infDiag k) with hz
    have hz1 : Φ (z : AF F ⊗[F] E) = (Formalism.L2.Host.infDiag k : AdeleRing (𝓞 E) E) := Φ.apply_symm_apply _
    rw [coe_infDiag, hΦ] at hz1
    have hinf : infTens F E z = (1 : Ainf F) ⊗ₜ[F] (k : E) :=
      j.injective ((congrArg Prod.fst hz1).trans (hj k).symm)
    have hfin1 : finTens F E z = 1 :=
      (finAdEquiv F E).injective ((congrArg Prod.snd hz1).trans (map_one _).symm)
    have hAt : At (evI F) ((z : AF F ⊗[F] E) - 1) := by
      intro a ha
      have ha1 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (ha.trans (map_zero _).symm)
      refine tens_ext ?_ ?_
      · rw [Algebra.smul_def, map_mul, map_zero]
        change (a.1 ⊗ₜ[F] (1 : E)) * _ = 0
        rw [ha1, TensorProduct.zero_tmul, zero_mul]
      · rw [Algebra.smul_def, map_mul, map_zero, map_sub, map_one, hfin1, sub_self, mul_zero]
    have hpi : ∀ w, piInf (τ w) z = (τ w).1 k := fun w => by
      change infEmb (τ w) (compInf F E w z) = _
      rw [compInf_eq_infTens, hinf, Algebra.TensorProduct.map_tmul, map_one, infEmb_tmul, map_one, one_mul]
      rfl
    change ((χ z : Circle) : ℂ) = _
    rw [hm z hAt]
    exact Finset.prod_congr rfl fun w _ => by rw [hpi w]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isCMType_emb (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) : IsCMType fun w => (τ w).1 := by
  haveI := h.1
  haveI := h.2.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  have real : ∀ φ : F →+* ℂ, ComplexEmbedding.conjugate φ = φ := fun φ => IsTotallyReal.complexEmbedding_isReal φ
  have emb : ∀ φ : F →+* ℂ, (InfinitePlace.mk φ).embedding = φ := fun φ =>
    (InfinitePlace.embedding_mk_eq φ).elim id fun e => e.trans (real φ)
  intro φ
  have cj : ∀ w, (ComplexEmbedding.conjugate (τ w).1).comp (algebraMap F E) = w.embedding := fun w =>
    (congrArg ComplexEmbedding.conjugate (τ w).2).trans (real _)
  refine ⟨InfinitePlace.mk (φ.comp (algebraMap F E)), ?_, fun w hw => ?_⟩
  · set w := InfinitePlace.mk (φ.comp (algebraMap F E))
    obtain ⟨g, hg⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) (τ w).1 φ ((τ w).2.trans (emb _))
    let s : E ≃ₐ[F] E := AlgEquiv.ofBijective σ σ.bijective
    have hs : s ≠ 1 := fun e => IsTotallyComplex.complexEmbedding_not_isReal φ (RingHom.ext fun x => by
      have e1 : σ x = x := congrArg (fun y : E ≃ₐ[F] E => y x) e
      have := h.2.2.2 φ x
      rw [e1] at this
      exact this.symm)
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 ((IsGalois.card_aut_eq_finrank F E).trans h.2.2.1)
    by_cases e : g.symm = 1
    · left; rw [← hg, e]; rfl
    · right
      rw [← hg, (hy _ e).trans (hy _ hs).symm]
      exact RingHom.ext fun x => h.2.2.2 _ x
  · rcases hw with rfl | rfl
    · rw [(τ w).2, InfinitePlace.mk_embedding]
    · rw [cj, InfinitePlace.mk_embedding]

variable {I : Type} [Fintype I]

theorem exists_isHeckeL_of_completed {χ : Formalism.L2.Host.HChar E} {n : I → ℤ} {Λ : ℂ → ℂ} (h : IsCompletedL χ n Λ) :
    ∃ L, IsHeckeL χ L := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hA : ∀ (z : ℂ) i, (2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2))) ≠ 0 := fun z i =>
    mul_ne_zero two_ne_zero (by rw [Ne, Complex.cpow_eq_zero_iff]; tauto)
  refine ⟨fun z => Λ z * ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
    (Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2))⁻¹), ?_, fun z hz => ?_⟩
  · refine h.1.mul (Differentiable.fun_finsetProd fun i _ => ?_)
    refine Differentiable.mul (fun z => ?_) ?_
    · refine DifferentiableAt.inv ?_ (hA z i)
      exact (((differentiableAt_id.add_const _).neg).const_cpow (Or.inl hpi)).const_mul 2
    · exact Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const _)
  · obtain ⟨L, h1, h2⟩ := h.2 z hz
    have hz' : ∀ i, Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => Complex.Gamma_ne_zero_of_re_pos (by
      have h2 : (0:ℝ) ≤ |(n i : ℝ)| := abs_nonneg _
      simp only [Complex.add_re, Complex.div_re, Complex.intCast_re, Complex.intCast_im]
      norm_num
      linarith)
    convert h1 using 1
    beta_reduce
    rw [h2, mul_comm _ L, mul_assoc, archFactor, ← Finset.prod_mul_distrib, Finset.prod_eq_one, mul_one]
    intro i _
    rw [mul_mul_mul_comm, mul_inv_cancel₀ (hA z i), mul_inv_cancel₀ (hz' i), one_mul]

theorem shift_ne {z k : ℤ} (h : 0 < 2 * z + |k|) (j : ℕ) : (z : ℂ) + ((|k| : ℤ) : ℂ) / 2 ≠ -j := fun e => by
  have : ((2 * z + |k| : ℤ) : ℂ) = ((-2 * j : ℤ) : ℂ) := by push_cast at e ⊢; linear_combination 2 * e
  have := Int.cast_injective this
  omega

theorem heckeL_ne_zero (hFE : GlobalTheory.Published.HeckeTateFunctionalEquation) [IsTotallyComplex E] {φ : I → E →+* ℂ} (hφ : IsCMType φ)
    {χ : Formalism.L2.Host.HChar E} {n : I → ℤ} (hu : χ.IsUnitary) (hn : χ.HasInf φ n) (h0 : ∃ i, n i ≠ 0) :
    ∃ L, IsHeckeL χ L ∧ ∀ z : ℤ, (∀ i, 0 < 2 * z + |n i|) → L z ≠ 0 := by
  have hu' := GlobalTheory.Published.HeckeFEModel.isUnitary_inv hu
  obtain ⟨a, ha⟩ := GlobalTheory.Published.HeckeFEModel.exists_exponents χ⁻¹
  obtain ⟨Λ', Λ, h', h, fe⟩ := hFE E I φ hφ χ⁻¹ (fun i => -n i) a hu' (GlobalTheory.Published.HeckeFEModel.hasInf_inv hn)
    (h0.imp fun i hi => neg_ne_zero.2 hi) ha
  simp only [inv_inv, neg_neg] at h
  obtain ⟨L, hL⟩ := exists_isHeckeL_of_completed h
  obtain ⟨L', hL'⟩ := exists_isHeckeL_of_completed h'
  refine ⟨L, hL, fun z hz => ?_⟩
  rcases le_or_gt 1 z with h1 | h1
  · have e : ((z.toNat : ℕ) : ℂ) = (z : ℂ) := by rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    exact e ▸ hL.ne_zero_nat hu (by omega)
  have e : (((1 - z).toNat : ℕ) : ℂ) = ((1 - z : ℤ) : ℂ) := by rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  have hL1 : L' ((1 - z : ℤ) : ℂ) ≠ 0 := e ▸ hL'.ne_zero_nat hu' (by omega)
  have g1 : ∀ i (j : ℕ), ((1 - z : ℤ) : ℂ) + ((|-n i| : ℤ) : ℂ) / 2 ≠ -j := fun i =>
    shift_ne (by have := abs_nonneg (-n i); omega)
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hΛ' : Λ' ((1 - z : ℤ) : ℂ) ≠ 0 := by
    rw [GlobalTheory.HeckeEps.completed_eq_mul h' hL' g1]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (mul_ne_zero two_ne_zero ?_)
      (Complex.Gamma_ne_zero (g1 i))) hL1
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  rw [fe, show 1 - ((1 - z : ℤ) : ℂ) = (z : ℂ) by push_cast; ring,
    GlobalTheory.HeckeEps.completed_eq_mul h hL fun i => shift_ne (hz i)] at hΛ'
  exact right_ne_zero_of_mul (right_ne_zero_of_mul hΛ')

theorem eq_charL {χ : Chr F E} {H : Formalism.L2.Host.HChar E} (hu : H.IsUnitary) (hloc : ∀ W x, H.loc W x = locChar χ W x)
    {L : ℂ → ℂ} (hL : IsHeckeL H L) {s : ℂ} (hs : 1 < s.re) : L s = charL χ (∅ : Set (Pl F)) s := by
  have e : charFam χ = heckeFam H := funext fun w => by
    have e1 : UnrAt χ w ↔ H.UnrAt w := forall₂_congr fun x _ => by rw [hloc]
    have e2 : val χ w = H.val w := (hloc _ _).symm
    by_cases hw : H.UnrAt w <;> simp [charFam, heckeFam, e1, e2, hw]
  have e0 : above E (∅ : Set (Pl F)) = ∅ := Set.eq_empty_of_forall_notMem fun _ h => h
  rw [charL, LS, e, e0]
  have h1 := (converges_heckeFam ∅ hu hs).hasProd
  simp only [locL_heckeFam] at h1
  exact (hL.2 s hs).unique ((Equiv.subtypeUnivEquiv (p := fun w => w ∉ (∅ : Set (HeightOneSpectrum (𝓞 E))))
    (fun _ => Set.notMem_empty _)).hasProd_iff.1 h1)

def LInt2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∀ χ ∈ ({X.ν, X.ν⁻¹} : Set (Chr F E)),
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ (∀ s : ℂ, 1 < s.re → Λ s = charL χ (∅ : Set (Pl F)) s) ∧
      ∀ z : ℤ, -((a + a' : ℕ) : ℤ) ≤ 2 * z → Λ z ≠ 0

end GlobalTheory.ThK.Dbl

end
