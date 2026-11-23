import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfUnimodular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearFormsBoundedRepresentativesStatement
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe

noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical nonZeroDivisors

namespace GlobalTheory.LoopC.Lifts

section General

variable {R K P : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup P] [Module R P]

theorem exists_gen_mod (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) {n : R} (hn : n ≠ 0) :
    ∃ t ∈ I, ∀ s ∈ I, ∃ a : R, ∃ s' ∈ I, s = a • t + n • s' := by
  have hn' : (FractionalIdeal.spanSingleton R⁰ (algebraMap R K n)) ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hn
  have hle : FractionalIdeal.spanSingleton R⁰ (algebraMap R K n) * I ≤ I :=
    FractionalIdeal.spanSingleton_mul_le_iff.2 fun z hz => by
      rw [← Algebra.smul_def]; exact (I : Submodule R K).smul_mem n hz
  obtain ⟨t, ht⟩ := IsDedekindDomain.exists_add_spanSingleton_mul_eq hle (mul_ne_zero hn' hI) one_ne_zero
  rw [mul_one] at ht
  refine ⟨t, ?_, fun s hs => ?_⟩
  · rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← ht, ← FractionalIdeal.sup_eq_add]
    exact le_sup_right
  · rw [← ht, FractionalIdeal.mem_add] at hs
    obtain ⟨i, hi, j, hj, rfl⟩ := hs
    obtain ⟨s', hs', rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hi
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hj
    exact ⟨a, s', hs', by rw [add_comm, Algebra.smul_def n]⟩

theorem exists_lift (φ : P →ₗ[R] K) (h : ∀ p, ∃ o : R, algebraMap R K o = φ p) :
    ∃ ψ : P →ₗ[R] R, Algebra.linearMap R K ∘ₗ ψ = φ := by
  choose f hf using h
  have hi := IsFractionRing.injective R K
  refine ⟨⟨⟨f, fun x y => hi ?_⟩, fun c x => hi ?_⟩, LinearMap.ext fun p => hf p⟩
  · simp [hf]
  · simp [hf, Algebra.smul_def]

theorem ideal_reps [CharZero R] (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) (B : AddSubgroup (P →ₗ[R] R))
    (S : Finset (P →ₗ[R] R)) (hS : ∀ ψ, ∃ ψ₀ ∈ S, ψ - ψ₀ ∈ B) :
    ∃ c ∈ I, ∀ G : AddSubmonoid (P →ₗ[R] K),
      (∀ x ∈ I, ∀ ψ ∈ B, x • (Algebra.linearMap R K ∘ₗ ψ) ∈ G) →
      ∀ φ : P →ₗ[R] K, (∀ p, φ p ∈ I) → ∃ ψ₀ ∈ S, φ - c • (Algebra.linearMap R K ∘ₗ ψ₀) ∈ G := by
  haveI : Finite ((P →ₗ[R] R) ⧸ B) := by
    refine Finite.of_surjective (fun s : S => (QuotientAddGroup.mk s.1 : (P →ₗ[R] R) ⧸ B)) ?_
    intro q
    obtain ⟨ψ, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨ψ₀, h0, h1⟩ := hS ψ
    refine ⟨⟨ψ₀, h0⟩, ?_⟩
    rw [QuotientAddGroup.eq]
    simpa [neg_add_eq_sub] using h1
  have hn : B.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  obtain ⟨c, hc, hgen⟩ := exists_gen_mod I hI (n := (B.index : R)) (by exact_mod_cast hn)
  refine ⟨c, hc, fun G hG φ hφ => ?_⟩
  have key : ∀ t ∈ I * I⁻¹, ∃ ψ : P →ₗ[R] R, t • φ - c • (Algebra.linearMap R K ∘ₗ ψ) ∈ G := by
    intro t ht
    refine FractionalIdeal.mul_induction_on ht
      (C := fun t => ∃ ψ : P →ₗ[R] R, t • φ - c • (Algebra.linearMap R K ∘ₗ ψ) ∈ G) ?_ ?_
    · intro a ha b hb
      obtain ⟨ψ, hψ⟩ := exists_lift (b • φ) (fun p => by
        have := FractionalIdeal.mul_mem_mul hb (hφ p)
        rw [inv_mul_cancel₀ hI] at this
        exact (FractionalIdeal.mem_one_iff _).1 this)
      obtain ⟨o, s', hs', rfl⟩ := hgen a ha
      refine ⟨o • ψ, ?_⟩
      have := hG s' hs' _ (B.nsmul_index_mem ψ)
      convert this using 1
      ext p
      have e := LinearMap.congr_fun hψ p
      simp only [LinearMap.comp_apply, Algebra.linearMap_apply, LinearMap.smul_apply, smul_eq_mul] at e
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, Algebra.linearMap_apply, LinearMap.smul_apply,
        smul_eq_mul, Algebra.smul_def, map_mul, e, map_natCast, nsmul_eq_mul, eq_natCast]
      ring
    · rintro x y ⟨ψ₁, h₁⟩ ⟨ψ₂, h₂⟩
      refine ⟨ψ₁ + ψ₂, ?_⟩
      convert G.add_mem h₁ h₂ using 1
      rw [LinearMap.comp_add, add_smul, smul_add]
      abel
  obtain ⟨ψ, hψ⟩ := key 1 (by rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _)
  obtain ⟨ψ₀, h0, h1⟩ := hS ψ
  refine ⟨ψ₀, h0, ?_⟩
  convert G.add_mem hψ (hG c hc _ h1) using 1
  rw [LinearMap.comp_sub, smul_sub, one_smul]
  abel

theorem restrict_reps (hR : ¬ IsField R) {M : Type} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] (N : Submodule R M) (hfin : Finite (M ⧸ N)) :
    ∃ S : Finset (N →ₗ[R] R), S.card ≤ Nat.card (M ⧸ N) ∧
      ∀ ψ : N →ₗ[R] R, ∃ ψ₀ ∈ S, ∃ χ : M →ₗ[R] R, ψ - ψ₀ = χ ∘ₗ N.subtype := by
  haveI : Module.Flat R M := inferInstance
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  haveI : Module.Projective R M := Module.Flat.projective_of_finitePresentation
  have h := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.homRestrictIndex R M R N hR hfin
  rw [Module.finrank_self, pow_one] at h
  have hpos : 0 < Nat.card (M ⧸ N) := Nat.card_pos
  haveI : Finite ((N →ₗ[R] R) ⧸ LinearMap.range (LinearMap.lcomp R R N.subtype)) :=
    Nat.finite_of_card_ne_zero (by omega)
  haveI := Fintype.ofFinite ((N →ₗ[R] R) ⧸ LinearMap.range (LinearMap.lcomp R R N.subtype))
  refine ⟨Finset.univ.image (fun q : ((N →ₗ[R] R) ⧸ LinearMap.range (LinearMap.lcomp R R N.subtype)) => q.out),
    ?_, fun ψ => ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, h]
  · refine ⟨(Submodule.Quotient.mk ψ : _ ⧸ LinearMap.range (LinearMap.lcomp R R N.subtype)).out,
      Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have : (Submodule.Quotient.mk ψ : _ ⧸ LinearMap.range (LinearMap.lcomp R R N.subtype)) =
        Submodule.Quotient.mk (Submodule.Quotient.mk ψ : _ ⧸ LinearMap.range (LinearMap.lcomp R R N.subtype)).out :=
      (Quotient.out_eq _).symm
    obtain ⟨χ, hχ⟩ := (Submodule.Quotient.eq _).1 this
    exact ⟨χ, hχ.symm⟩

end General

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem hT_zero_symm {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {x y : S.V}
    (h : S.hT x y = 0) : S.hT y x = 0 := by
  have := S.herm.eq x y
  rw [h] at this
  simpa using this.symm

theorem ddS_ne_zero : ddS D ≠ 0 := by
  rw [ddS, FractionalIdeal.coeIdeal_ne_zero, Ne,
    Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)]
  exact differentIdeal_ne_bot

theorem hyp_fe (a b : Fin D.R.rS) : (hS D).hT (D.sp.hypF a) (D.sp.hypE b) = if a = b then 1 else 0 := by
  have h1 := (D.sp.Y 0).herm.eq (D.sp.hypE b) (D.sp.hypF a)
  rw [D.sp.hyp_ef b a] at h1
  rw [← h1]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

theorem expand {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {r : ℕ} (e f : Fin r → S.V)
    (h : ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0) {x : S.V}
    (hx : x ∈ Submodule.span E (Set.range e)) : x = ∑ a, S.hT (f a) x • e a := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [map_sum, h]

theorem orth_span {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {s : Set S.V} {y : S.V}
    (h : ∀ x ∈ s, S.hT x y = 0) : y ∈ orth S (Submodule.span E s) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add y z _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

theorem orth_apply {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {U : Submodule E S.V}
    {x y : S.V} (hy : y ∈ orth S U) (hx : x ∈ U) : S.hT x y = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hy
  exact hy x hx

variable {D}

theorem XS_le {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : XS D F0 ≤ toO (hS D) F0.X := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, x, -, rfl⟩
  exact F0.X.smul_mem x (Submodule.subset_span ⟨a, rfl⟩)

theorem YS_le : YS D ≤ toO (hS D) (Submodule.span D.host.E (Set.range D.sp.hypF)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, x, -, rfl⟩
  exact (Submodule.span D.host.E (Set.range D.sp.hypF)).smul_mem x (Submodule.subset_span ⟨a, rfl⟩)

theorem iXY_mem_Wb (v : (D.sp.X 0).V) : D.sp.iXY 0 v ∈ Wb D := by
  refine orth_span _ ?_
  rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
  · exact hT_zero_symm _ (D.sp.hyp_orthX a v).1
  · exact hT_zero_symm _ (D.sp.hyp_orthX a v).2

theorem mem_of_split {u : D.what₂.Word} {F0 : Fb D u} {Λ : LatV D} (hB : IsBase D u F0) (hS' : IsSplit D F0 Λ)
    {v : (D.sp.X 0).V} (hv : v ∈ L0X D Λ (lf D F0)) : D.sp.iXY 0 v ∈ Λ := by
  have hX : F0.X = Submodule.span D.host.E (Set.range D.sp.hypE) := by rw [← hB.1]; rfl
  obtain ⟨l, hl, x, hx, e⟩ := Submodule.mem_sup.1 hv.1.1
  have hl1 := hl.1
  rw [hS'] at hl1
  obtain ⟨l', hl', y, hy, rfl⟩ := Submodule.mem_sup.1 hl1
  obtain ⟨x₁, hx₁, m, hm, rfl⟩ := Submodule.mem_sup.1 hl'
  have hx2 : x₁ + x ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := by
    rw [← hX]; exact F0.X.add_mem (XS_le F0 hx₁) hx
  have hy2 : y ∈ Submodule.span D.host.E (Set.range D.sp.hypF) := YS_le hy
  have e' : (x₁ + x) + y = D.sp.iXY 0 v - m := by
    have : D.sp.iXY 0 v = x₁ + m + y + x := e.symm
    rw [this]; abel
  have hw : (x₁ + x) + y ∈ Wb D := by rw [e']; exact (Wb D).sub_mem (iXY_mem_Wb v) hm.2
  have hy0 : y = 0 := by
    rw [expand (hS D) D.sp.hypF D.sp.hypE D.sp.hyp_ef hy2]
    refine Finset.sum_eq_zero fun a _ => ?_
    have h1 := orth_apply _ hw (Submodule.subset_span (Or.inl ⟨a, rfl⟩))
    have h2 : (hS D).hT (D.sp.hypE a) (x₁ + x) = 0 := by
      rw [expand (hS D) D.sp.hypE D.sp.hypF (hyp_fe D) hx2]
      simp [map_sum, D.sp.hyp_ee]
    rw [map_add, h2, zero_add] at h1
    rw [h1, zero_smul]
  rw [hy0, add_zero] at hw e'
  have hx0 : x₁ + x = 0 := by
    rw [expand (hS D) D.sp.hypE D.sp.hypF (hyp_fe D) hx2]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [orth_apply _ hw (Submodule.subset_span (Or.inr ⟨a, rfl⟩)), zero_smul]
  rw [hx0, eq_comm, sub_eq_zero] at e'
  rw [e']
  exact hm.1

theorem iXY_injective : Function.Injective (D.sp.iXY 0) := by
  have hm := D.R.two_le_m
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine (D.sp.X 0).nondeg.1 x fun y => ?_
  rw [← D.sp.iXY_isom 0 (by omega), hx, map_zero, LinearMap.zero_apply]

theorem sat_primitive {L P : LatW D} (h : P ≤ L) : IsPrimitiveSub (sat D L P) L := by
  refine ⟨inf_le_left, ?_⟩
  have : Submodule.span D.host.E ((sat D L P : LatW D) : Set (D.sp.X 0).V) =
      Submodule.span D.host.E (P : Set (D.sp.X 0).V) := by
    apply le_antisymm
    · exact Submodule.span_le.2 fun x hx => hx.2
    · exact Submodule.span_mono fun x hx => ⟨h hx, Submodule.subset_span hx⟩
  rw [this]; rfl

theorem fun_reps {u u' : D.what₂.Word} {F0 : Fb D u} {Λ : LatV D} (hSt : Stand D u u') (hB : IsBase D u F0)
    (hR : IsRowLat D F0 Λ) (hS' : IsSplit D F0 Λ) {P : LatW D} {s : ℕ} {Q : ℝ}
    (hP : SubOK D (L0X D Λ (lf D F0)) P s Q) :
    ∃ S : Finset (P →ₗ[𝓞 D.host.E] 𝓞 D.host.E), (S.card : ℝ) ≤ NT D u ^ 2 * Q ∧
      ∀ ψ : P →ₗ[𝓞 D.host.E] 𝓞 D.host.E, ∃ ψ₀ ∈ S, ∃ v ∈ L0X D Λ (lf D F0),
        ∀ p : P, (((ψ - ψ₀) p : 𝓞 D.host.E) : D.host.E) = (D.sp.X 0).hT v p := by
  obtain ⟨hPL, -, h1, hQ, -⟩ := hP
  set L := L0X D Λ (lf D F0) with hL
  set M := sat D L P with hM
  have hPM : P ≤ M := fun x hx => ⟨hPL hx, Submodule.subset_span hx⟩
  have hfg : M.FG := by
    apply Submodule.fg_of_fg_map_injective ((D.sp.iXY 0).restrictScalars (𝓞 D.host.E)) iXY_injective
    refine Submodule.FG.of_le hR.2.1.1.fg ?_
    rintro _ ⟨x, hx, rfl⟩
    exact mem_of_split hB hS' hx.1
  haveI : Module.Finite (𝓞 D.host.E) M := Module.Finite.iff_fg.2 hfg
  haveI : Module.IsTorsionFree (𝓞 D.host.E) (D.sp.X 0).V :=
    Module.IsTorsionFree.trans_faithfulSMul (𝓞 D.host.E) D.host.E _
  obtain ⟨S₁, hc₁, hS₁⟩ := restrict_reps (RingOfIntegers.not_isField D.host.E) (P.comap M.subtype)
    (Nat.finite_of_card_ne_zero (by unfold idxW at h1; omega))
  obtain ⟨S₂, hc₂, hS₂⟩ := GlobalTheory.T.linear_forms_bounded_representatives D u u' F0 Λ hSt hB hR M (sat_primitive hPL)
  let e := Submodule.comapSubtypeEquivOfLe hPM
  refine ⟨(S₂ ×ˢ S₁).image (fun q => q.2 ∘ₗ e.symm.toLinearMap + q.1 ∘ₗ Submodule.inclusion hPM), ?_, fun ψ => ?_⟩
  · have h2 : (S₁.card : ℝ) ≤ Q := le_trans (by exact_mod_cast hc₁) hQ
    refine le_trans (Nat.cast_le.2 Finset.card_image_le) ?_
    rw [Finset.card_product, Nat.cast_mul]
    exact mul_le_mul hc₂ h2 (Nat.cast_nonneg _) (sq_nonneg _)
  · obtain ⟨ψ₁, m₁, χ, hχ⟩ := hS₁ (ψ ∘ₗ e.toLinearMap)
    obtain ⟨ψ₂, m₂, v, hv, hv'⟩ := hS₂ χ
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mk_mem_product m₂ m₁), v, hv, fun p => ?_⟩
    have h3 := LinearMap.congr_fun hχ (e.symm p)
    have h4 := hv' (Submodule.inclusion hPM p)
    have h5 : ψ p - ψ₁ (e.symm p) = χ (Submodule.inclusion hPM p) := by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] at h3
      exact h3
    rw [← h5] at h4
    refine Eq.trans ?_ h4
    congr 1
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    ring

variable (D) in

abbrev coefI (a : Fin D.R.rS) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))

theorem coef_mem {u : D.what₂.Word} {F0 : Fb D u} (hB : IsBase D u F0) (a : Fin D.R.rS) {y : (hS D).V}
    (hy : y ∈ XS D F0) : (hS D).hT (D.sp.hypF a) y ∈ coefI D a := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, x, hx, rfl⟩ := hy
    rw [hB.1, map_smul, hyp_fe]
    split_ifs with h
    · subst h; rw [smul_eq_mul, mul_one]; exact hx
    · rw [smul_zero]; exact FractionalIdeal.zero_mem _
  | zero => rw [map_zero]; exact FractionalIdeal.zero_mem _
  | add y z _ _ h1 h2 =>
    rw [map_add]; exact (coefI D a : Submodule (𝓞 D.host.E) D.host.E).add_mem h1 h2
  | smul c y _ h =>
    rw [LinearMap.map_smul_of_tower]
    exact (coefI D a : Submodule (𝓞 D.host.E) D.host.E).smul_mem c h

theorem integralUnipotentFixingFrame_fixes_isotropic {T : D.host.E} {F : Fg D T} {Λ : LatV D} {n : (hS D).V ≃ₗ[D.host.E] (hS D).V}
    (hn : n ∈ N1 D Λ F) {x : (hS D).V} (hx : x ∈ Xsp F) : n x = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    have := hn.2 a.castSucc
    simpa [frame, FlagG.fvec] using this
  | zero => simp
  | add y z _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

def moved {T : D.host.E} (F : Fg D T) (Λ : LatV D) (P : LatW D) :
    AddSubmonoid (P →ₗ[𝓞 D.host.E] (hS D).V) where
  carrier := {χ | (∀ p, χ p ∈ Xsp F) ∧
    ∃ n ∈ N1 D Λ F, ∀ p : P, n (D.sp.iXY 0 (p : (D.sp.X 0).V)) = D.sp.iXY 0 (p : (D.sp.X 0).V) - χ p}
  zero_mem' := ⟨fun p => by simp, 1, ⟨FrEqv.one_mem_NLam, fun b => rfl⟩, fun p => by simp⟩
  add_mem' := by
    rintro χ₁ χ₂ ⟨h₁, n₁, m₁, e₁⟩ ⟨h₂, n₂, m₂, e₂⟩
    refine ⟨fun p => (Xsp F).add_mem (h₁ p) (h₂ p), n₂ * n₁, ⟨FrEqv.mul_mem_NLam m₁.1 m₂.1, fun b => ?_⟩,
      fun p => ?_⟩
    · change n₂ (n₁ _) = _
      rw [m₁.2, m₂.2]
    · change n₂ (n₁ _) = _
      rw [e₁, map_sub, e₂, integralUnipotentFixingFrame_fixes_isotropic m₂ (h₁ p), LinearMap.add_apply]
      abel

theorem eichler_moved {u : D.what₂.Word} {F0 : Fb D u} {Λ : LatV D} (hB : IsBase D u F0)
    (hR : IsRowLat D F0 Λ) (hS' : IsSplit D F0 Λ) {P : LatW D} {v : (D.sp.X 0).V}
    (hv : v ∈ L0X D Λ (lf D F0)) {w : (hS D).V} (hw : w ∈ XLam Λ (lf D F0))
    (χ : P →ₗ[𝓞 D.host.E] (hS D).V) (hχ : ∀ p : P, χ p = (D.sp.X 0).hT v p • w) :
    χ ∈ moved (lf D F0) Λ P := by
  have hm := D.R.two_le_m
  have horth : ∀ x, D.sp.iXY 0 x ∈ orth (hS D) (Xsp (lf D F0)) := by
    intro x
    refine orth_span _ ?_
    rintro _ ⟨a, rfl⟩
    change (hS D).hT (F0.e a) _ = 0
    rw [hB.1]
    exact hT_zero_symm _ (D.sp.hyp_orthX a x).1
  obtain ⟨n, hn, t, hfix, hform⟩ := GlobalTheory.EichlerUnip.eichler_mem_unipotent D _ (lf D F0) Λ hR.2.1.2.1
    (D.sp.iXY 0 v) ⟨mem_of_split hB hS' hv, horth v⟩ w hw
  refine ⟨fun p => by rw [hχ]; exact (Xsp (lf D F0)).smul_mem _ hw.2, n, ⟨hn, fun b => ?_⟩, fun p => ?_⟩
  · refine Fin.lastCases ?_ (fun a => ?_) b
    · have h1 : (hS D).hT (D.sp.iXY 0 v) F0.z = 0 := hT_zero_symm _ hv.2
      have h2 : (hS D).hT w F0.z = 0 := by
        refine orth_apply (hS D) (orth_span _ ?_) hw.2
        rintro _ ⟨a, rfl⟩
        exact F0.z_orth a
      have h3 : frame (lf D F0) (Fin.last _) = F0.z := by simp [frame, FlagG.fvec]
      rw [h3, hform, h1, h2]
      simp
    · apply hfix
      have h3 : frame (lf D F0) a.castSucc = F0.e a := by simp [frame, FlagG.fvec]
      rw [h3]
      exact Submodule.subset_span ⟨a, rfl⟩
  · rw [hform, orth_apply _ (horth p) hw.2, hχ, D.sp.iXY_isom 0 (by omega)]
    simp

theorem main : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → IsSplit D F0 Λ → ∀ (P : LatW D) (s : ℕ) (Q : ℝ), SubOK D (L0X D Λ (lf D F0)) P s Q → ∃ reps : Finset (P →ₗ[𝓞 D.host.E] (hS D).V), (reps.card : ℝ) ≤ NT D u ^ (2 * D.R.rS) * Q ^ D.R.rS ∧ (∀ φ ∈ reps, ∀ p, φ p ∈ XLam Λ (lf D F0)) ∧ ∀ φ : P →ₗ[𝓞 D.host.E] (hS D).V, (∀ p, φ p ∈ XLam Λ (lf D F0)) → ∃ φ₀ ∈ reps, ∃ n ∈ N1 D Λ (lf D F0), ∀ p : P, n (D.sp.iXY 0 (p : (D.sp.X 0).V) + φ p) = D.sp.iXY 0 (p : (D.sp.X 0).V) + φ₀ p := by
  intro D u u' F0 Λ hSt hB hR hS' P s Q hP
  obtain ⟨S, hc, hS₀⟩ := fun_reps hSt hB hR hS' hP
  let B : AddSubgroup (P →ₗ[𝓞 D.host.E] 𝓞 D.host.E) :=
    { carrier := {ψ | ∃ v ∈ L0X D Λ (lf D F0), ∀ p : P, ((ψ p : 𝓞 D.host.E) : D.host.E) = (D.sp.X 0).hT v p}
      zero_mem' := ⟨0, Submodule.zero_mem _, fun p => by simp⟩
      add_mem' := by
        rintro a b ⟨v, hv, e⟩ ⟨w, hw, e'⟩
        exact ⟨v + w, Submodule.add_mem _ hv hw, fun p => by simp [e, e']⟩
      neg_mem' := by
        rintro a ⟨v, hv, e⟩
        exact ⟨-v, Submodule.neg_mem _ hv, fun p => by simp [e]⟩ }
  have hI := fun a => ideal_reps (coefI D a) (zpow_ne_zero _ (ddS_ne_zero D)) B S hS₀
  choose c hcI hgen using hI
  let j : Fin D.R.rS → ((P →ₗ[𝓞 D.host.E] D.host.E) →ₗ[𝓞 D.host.E] (P →ₗ[𝓞 D.host.E] (hS D).V)) := fun a =>
    LinearMap.llcomp (𝓞 D.host.E) P D.host.E (hS D).V
      ((LinearMap.toSpanSingleton D.host.E (hS D).V (F0.e a)).restrictScalars (𝓞 D.host.E))
  have hj : ∀ a χ p, j a χ p = χ p • F0.e a := fun _ _ _ => rfl
  have hmem : ∀ a, ∀ x ∈ coefI D a, x • F0.e a ∈ XLam Λ (lf D F0) := by
    intro a x hx
    rw [hR.2.2]
    exact Submodule.subset_span ⟨a, x, hx, rfl⟩
  let rep : (Fin D.R.rS → (P →ₗ[𝓞 D.host.E] 𝓞 D.host.E)) → (P →ₗ[𝓞 D.host.E] (hS D).V) := fun g =>
    ∑ a, j a (c a • (Algebra.linearMap (𝓞 D.host.E) D.host.E ∘ₗ g a))
  refine ⟨(Fintype.piFinset fun _ => S).image rep, ?_, ?_, fun φ hφ => ?_⟩
  · refine le_trans (Nat.cast_le.2 Finset.card_image_le) ?_
    rw [Fintype.card_piFinset_const, Nat.cast_pow, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hc _
  · intro φ hφ p
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hφ
    simp only [rep, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [hj]
    apply hmem
    have := (coefI D a : Submodule (𝓞 D.host.E) D.host.E).smul_mem (g a p) (hcI a)
    rw [Algebra.smul_def, mul_comm] at this
    exact this
  · let co : Fin D.R.rS → (P →ₗ[𝓞 D.host.E] D.host.E) := fun a =>
      ((hS D).hT (D.sp.hypF a)).restrictScalars (𝓞 D.host.E) ∘ₗ φ
    have h1 := fun a => hgen a ((moved (lf D F0) Λ P).comap (j a).toAddMonoidHom) (by
      rintro x hx ψ ⟨v, hv, e⟩
      refine eichler_moved hB hR hS' hv (hmem a x hx) _ fun p => ?_
      change j a _ p = _
      rw [hj, smul_smul, ← e p, mul_comm]
      rfl) (co a) (fun p => coef_mem hB a (by rw [← hR.2.2]; exact hφ p))
    choose g hg hg' using h1
    have h2 : φ - rep g ∈ moved (lf D F0) Λ P := by
      have h3 : φ = ∑ a, j a (co a) := by
        ext p
        have hx : φ p ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := by
          rw [← hB.1]; exact (hφ p).2
        rw [LinearMap.sum_apply, expand (hS D) D.sp.hypE D.sp.hypF (hyp_fe D) hx]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hj, hB.1]
        rfl
      have h4 := (moved (lf D F0) Λ P).sum_mem (t := Finset.univ) fun a _ => hg' a
      convert h4 using 1
      conv_lhs => rw [h3]
      simp only [rep, ← Finset.sum_sub_distrib, ← map_sub]
      rfl
    obtain ⟨-, n, hn, e⟩ := h2
    refine ⟨rep g, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.2 hg), n, hn, fun p => ?_⟩
    rw [map_add, e, integralUnipotentFixingFrame_fixes_isotropic hn (hφ p).2, LinearMap.sub_apply]
    abel

end Record

end GlobalTheory.LoopC.Lifts

end
