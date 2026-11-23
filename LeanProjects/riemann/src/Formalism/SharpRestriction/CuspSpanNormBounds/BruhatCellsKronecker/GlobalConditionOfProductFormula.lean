import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped nonZeroDivisors
open Classical

section Diff

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} (A : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p) (δ : ∀ p, (A p).Fp)

structure DiffHyp : Prop where
  hinv : ∀ x, sig (sig x) = x
  hfix : ∀ x : E, sig x = x → ∃ a : F, algebraMap F E a = x
  hδ : ∀ p, δ p ≠ 0
  dual : ∀ p (w : (A p).Ep), (∀ y ∈ (A p).O, (A p).psiE (w * y) = 1) ↔ w * algebraMap _ _ (δ p) ∈ (A p).O
  opn : ∀ p, IsOpen ((A p).O : Set (A p).Ep)
  top : ∀ p, IsTopologicalRing (A p).Ep
  cjcj : ∀ p x, (A p).cj ((A p).cj x) = x
  cjfix : ∀ p x, (A p).cj x = x → ∃ b, algebraMap (A p).Fp (A p).Ep b = x
  sa : ∀ U : ∀ p, AddSubgroup (A p).Ep, (∀ p, IsOpen (U p : Set (A p).Ep)) →
    {p | (U p : Set (A p).Ep) ≠ ((A p).O : Set (A p).Ep)}.Finite →
    ∀ x : ∀ p, (A p).Ep, {p | x p ∉ (A p).O}.Finite → ∃ t : E, ∀ p, (A p).ιE t - x p ∈ U p
  pf : ∀ x : E, (Function.mulSupport fun p => (A p).psiE ((A p).ιE x)).Finite ∧
    ∏ᶠ p, (A p).psiE ((A p).ιE x) = Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ)))

def Uw (p : HeightOneSpectrum (𝓞 F)) (w : (A p).Ep) : AddSubgroup (A p).Ep :=
  (A p).O.toAddSubgroup ⊓ (A p).O.toAddSubgroup.comap (AddMonoidHom.mulLeft (w * algebraMap _ _ (δ p)))

variable {A δ}

theorem mem_Uw (p : HeightOneSpectrum (𝓞 F)) (w u : (A p).Ep) :
    u ∈ Uw A δ p w ↔ u ∈ (A p).O ∧ w * algebraMap _ _ (δ p) * u ∈ (A p).O := Iff.rfl

variable (H : DiffHyp A δ)
include H

theorem isOpen_Uw (p : HeightOneSpectrum (𝓞 F)) (w : (A p).Ep) : IsOpen (Uw A δ p w : Set (A p).Ep) := by
  have := H.top p
  exact (H.opn p).inter ((H.opn p).preimage (continuous_const_mul (w * algebraMap _ _ (δ p))))

theorem psi_Uw (p : HeightOneSpectrum (𝓞 F)) (w u : (A p).Ep) (hu : u ∈ Uw A δ p w) : (A p).psiE (w * u) = 1 := by
  have h1 : w * u * algebraMap _ _ (δ p) ∈ (A p).O := by
    have := hu.2
    have e : w * u * algebraMap _ _ (δ p) = w * algebraMap _ _ (δ p) * u := by ring
    rw [e]; exact this
  have := (H.dual p (w * u)).2 h1 1 (A p).O.one_mem
  rwa [mul_one] at this

omit H in
theorem Uw_eq (p : HeightOneSpectrum (𝓞 F)) (w : (A p).Ep) (hw : w * algebraMap _ _ (δ p) ∈ (A p).O) :
    (Uw A δ p w : Set (A p).Ep) = ((A p).O : Set (A p).Ep) := by
  ext u
  exact ⟨fun h => h.1, fun h => ⟨h, (A p).O.mul_mem hw h⟩⟩

theorem int_of_forall (z : E) (h : ∀ p, (A p).ιE z ∈ (A p).O) : ∃ z' : 𝓞 E, (z' : E) = z := by
  have : z ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) :=
    (mem_iff_forall_atP (F := F) 1 z).2 (fun p => (int_iff (A p) H.hinv H.hfix z).1 (h p))
  exact (FractionalIdeal.mem_one_iff _).1 this

theorem approx_gen (p : HeightOneSpectrum (𝓞 F)) (U : ∀ p, AddSubgroup (A p).Ep) (hU : ∀ p, IsOpen (U p : Set (A p).Ep))
    (hle : ∀ p, (U p : Set (A p).Ep) ⊆ (A p).O)
    (hfin : {p | (U p : Set (A p).Ep) ≠ ((A p).O : Set (A p).Ep)}.Finite) (y : (A p).Ep) (hy : y ∈ (A p).O) :
    ∃ z : 𝓞 E, (A p).ιE (z : E) - y ∈ U p ∧ ∀ p', p' ≠ p → (A p').ιE (z : E) ∈ U p' := by
  obtain ⟨t, ht⟩ := H.sa U hU hfin (Function.update (fun _ => 0) p y) (by
    refine (Set.finite_singleton p).subset ?_
    intro p' hp'
    by_contra hne
    apply hp'
    rw [Function.update_of_ne hne]
    exact (A p').O.zero_mem)
  have h1 : (A p).ιE t - y ∈ U p := by
    have := ht p
    rwa [Function.update_self] at this
  have h2 : ∀ p', p' ≠ p → (A p').ιE t ∈ U p' := by
    intro p' hne
    have := ht p'
    rwa [Function.update_of_ne hne, sub_zero] at this
  obtain ⟨z, hz⟩ := int_of_forall H t (by
    intro p'
    by_cases hne : p' = p
    · subst hne
      have := (A p').O.add_mem (hle p' h1) hy
      rwa [sub_add_cancel] at this
    · exact hle p' (h2 p' hne))
  exact ⟨z, by rw [hz]; exact h1, fun p' hne => by rw [hz]; exact h2 p' hne⟩

def chiX (A : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p) (p : HeightOneSpectrum (𝓞 F)) (x : E) : AddChar (𝓞 E) ℂ :=
  (A p).psiE.compAddMonoidHom
    (((A p).ιE.toAddMonoidHom.comp (AddMonoidHom.mulLeft x)).comp (algebraMap (𝓞 E) E).toAddMonoidHom)

omit H in
theorem chiX_apply (p : HeightOneSpectrum (𝓞 F)) (x : E) (z : 𝓞 E) :
    chiX A p x z = (A p).psiE ((A p).ιE (x * (z : E))) := rfl

theorem psi_of_approx (p : HeightOneSpectrum (𝓞 F)) (x : E) (y : (A p).Ep) (z : 𝓞 E)
    (h1 : (A p).ιE (z : E) - y ∈ Uw A δ p ((A p).ιE x)) (h2 : (A p).psiE ((A p).ιE (x * (z : E))) = 1) :
    (A p).psiE ((A p).ιE x * y) = 1 := by
  have e : (A p).ιE x * y = (A p).ιE (x * (z : E)) - (A p).ιE x * ((A p).ιE (z : E) - y) := by
    rw [map_mul]; ring
  rw [e, AddChar.map_sub_eq_div, h2, psi_Uw H p _ _ h1, div_one]

theorem bad_finite (x : E) : {p | (A p).ιE x * algebraMap _ _ (δ p) ∉ (A p).O}.Finite := by
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
  have hT : (⋃ z ∈ S, Function.mulSupport fun p => (A p).psiE ((A p).ιE (x * (z : E)))).Finite :=
    Set.Finite.biUnion S.finite_toSet (fun z _ => (H.pf _).1)
  refine hT.subset ?_
  intro p hp
  by_contra hnot
  apply hp
  have hS1 : ∀ z ∈ S, chiX A p x z = 1 := by
    intro z hz
    by_contra hne
    exact hnot (Set.mem_biUnion hz hne)
  have hall : ∀ z : 𝓞 E, chiX A p x z = 1 := by
    intro z
    have hz : z ∈ Submodule.span ℤ (S : Set (𝓞 E)) := by rw [hS]; trivial
    induction hz using Submodule.span_induction with
    | mem z hz => exact hS1 z hz
    | zero => exact AddChar.map_zero_eq_one _
    | add a b _ _ ha hb => rw [AddChar.map_add_eq_mul, ha, hb, one_mul]
    | smul n a _ ha => rw [AddChar.map_zsmul_eq_zpow, ha, one_zpow]
  refine (H.dual p _).1 fun y hy => ?_
  obtain ⟨z, hz, -⟩ := approx_gen H p
    (Function.update (fun p' => (A p').O.toAddSubgroup) p (Uw A δ p ((A p).ιE x)))
    (by
      intro p'
      by_cases hne : p' = p
      · subst hne; rw [Function.update_self]; exact isOpen_Uw H _ _
      · rw [Function.update_of_ne hne]; exact H.opn p')
    (by
      intro p'
      by_cases hne : p' = p
      · subst hne; rw [Function.update_self]; exact fun u hu => hu.1
      · rw [Function.update_of_ne hne]; exact fun u hu => hu)
    (by
      refine (Set.finite_singleton p).subset ?_
      intro p' hp'
      by_contra hne
      apply hp'
      rw [Function.update_of_ne hne]; rfl) y hy
  rw [Function.update_self] at hz
  exact psi_of_approx H p x y z hz (hall z)

theorem diff_fwd (x : E) (hx : ∀ z : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (x * (z : E)) = n) (p : HeightOneSpectrum (𝓞 F)) :
    (A p).ιE x * algebraMap _ _ (δ p) ∈ (A p).O := by
  refine (H.dual p _).1 fun y hy => ?_
  obtain ⟨z, hz, hz'⟩ := approx_gen H p (fun p' => Uw A δ p' ((A p').ιE x)) (fun p' => isOpen_Uw H _ _)
    (fun p' u hu => hu.1)
    ((bad_finite H x).subset (by
      intro p' hp' hmem
      exact hp' (Uw_eq p' _ hmem))) y hy
  refine psi_of_approx H p x y z hz ?_
  obtain ⟨n, hn⟩ := hx z
  have h1 := (H.pf (x * (z : E))).2
  rw [finprod_eq_single _ p (by
    intro p' hne
    rw [map_mul]
    exact psi_Uw H p' _ _ (hz' p' hne)), hn] at h1
  rw [h1]
  rw [Complex.exp_eq_one_iff]
  exact ⟨n, by push_cast; ring⟩

theorem diff_bwd (x : E) (h : ∀ p, (A p).ιE x * algebraMap _ _ (δ p) ∈ (A p).O) (z : 𝓞 E) :
    ∃ n : ℤ, Algebra.trace ℚ E (x * (z : E)) = n := by
  have h1 := (H.pf (x * (z : E))).2
  rw [finprod_eq_one_of_forall_eq_one (by
    intro p
    rw [map_mul]
    exact (H.dual p _).2 (h p) _ (ιE_int (A p) z))] at h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1.symm
  refine ⟨n, ?_⟩
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have h3 : (((Algebra.trace ℚ E (x * (z : E)) : ℚ) : ℂ)) = (n : ℂ) := by
    apply mul_left_cancel₀ h2
    rw [hn]; ring
  exact_mod_cast h3

omit H in
theorem exists_common (p : HeightOneSpectrum (𝓞 F)) (S : Finset E) (c : E)
    (h : ∀ x ∈ S, atP p (1 : FractionalIdeal (𝓞 E)⁰ E) (x * c)) :
    ∃ a : 𝓞 F, a ∉ p.asIdeal ∧ ∀ x ∈ S, algebraMap F E (a : F) * (x * c) ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_notMem p, by simp⟩
  | insert x S _ ih =>
    obtain ⟨a, ha, hS⟩ := ih (fun y hy => h y (Finset.mem_insert_of_mem hy))
    obtain ⟨b, hb, hx⟩ := h x (Finset.mem_insert_self _ _)
    refine ⟨a * b, mul_notMem ha hb, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · rw [cmul, map_mul, mul_assoc]; exact int_smul_mem _ a _ hx
    · rw [cmul, mul_comm (a : F), map_mul, mul_assoc]; exact int_smul_mem _ b _ (hS y hy)

omit H in

theorem memLocalizedAt_inv (p : HeightOneSpectrum (𝓞 F)) (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0) (c : E)
    (h : ∀ x ∈ I, atP p (1 : FractionalIdeal (𝓞 E)⁰ E) (x * c)) : atP p I⁻¹ c := by
  have hN : IsNoetherian (𝓞 E) (I : Submodule (𝓞 E) E) := FractionalIdeal.isNoetherian I
  obtain ⟨S, hS⟩ : (I : Submodule (𝓞 E) E).FG := (Submodule.fg_top _).1 (hN.noetherian ⊤)
  obtain ⟨a, ha, haS⟩ := exists_common p S c (fun x hx => h x (by
    have : x ∈ (I : Submodule (𝓞 E) E) := by rw [← hS]; exact Submodule.subset_span hx
    exact this))
  refine ⟨a, ha, ?_⟩
  rw [FractionalIdeal.mem_inv_iff hI]
  intro y hy
  have hy' : y ∈ Submodule.span (𝓞 E) (S : Set E) := by rw [hS]; exact hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem y hyS =>
    have := haS y hyS
    have e : algebraMap F E (a : F) * c * y = algebraMap F E (a : F) * (y * c) := by ring
    rw [e]; exact this
  | zero => rw [mul_zero]; exact ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E).zero_mem
  | add y y' hy1 hy2 ih1 ih2 =>
    rw [mul_add]
    exact ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E).add_mem ih1 ih2
  | smul r y hy1 ih1 =>
    rw [mul_smul_comm]
    exact ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E).smul_mem r ih1

omit H in

theorem exists_val_eq (p : HeightOneSpectrum (𝓞 F)) (hδ : δ p ≠ 0) :
    ∃ c : F, valuation (A p).Fp ((A p).ιF c) = valuation (A p).Fp (δ p) := by
  have := (A p).lf
  have hv0 : valuation (A p).Fp (δ p) ≠ 0 := (Valuation.ne_zero_iff _).2 hδ
  have hs : {y | valuation (A p).Fp (y - δ p) < valuation (A p).Fp (δ p)} ∈ nhds (δ p) := by
    rw [IsValuativeTopology.mem_nhds_iff]
    refine ⟨Units.mk0 _ hv0, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    show valuation (A p).Fp (δ p + z - δ p) < valuation (A p).Fp (δ p)
    rw [add_sub_cancel_left]
    exact hz
  obtain ⟨c, hc⟩ := (A p).dense.mem_nhds hs
  exact ⟨c, Valuation.map_eq_of_sub_lt _ hc⟩

theorem unit_of (p : HeightOneSpectrum (𝓞 F)) (ϖ : (A p).Fp) (hϖ0 : ϖ ≠ 0) (hϖ : valuation (A p).Fp ϖ < 1)
    (o : (A p).Ep) (ho : o ∈ (A p).O) :
    ∃ w' ∈ (A p).O, (1 + algebraMap _ _ ϖ * o) * w' = 1 := by
  set w : (A p).Ep := 1 + algebraMap _ _ ϖ * o with hw
  have hϖO : ϖ ∈ 𝒪[(A p).Fp] := by
    rw [Valuation.mem_integer_iff]; exact hϖ.le
  have hwO : w ∈ (A p).O := (A p).O.add_mem (A p).O.one_mem ((A p).O.mul_mem (alg_mem_O _ _ hϖO) ho)
  have hcw : (A p).cj w = 1 + algebraMap _ _ ϖ * (A p).cj o := by
    rw [hw, map_add, map_one, map_mul, AlgEquiv.commutes]
  obtain ⟨n, hn⟩ := H.cjfix p (w * (A p).cj w) (by rw [map_mul, H.cjcj]; ring)
  have hco := cj_mem (A p) o ho
  have h1 : algebraMap (A p).Fp (A p).Ep ((n - 1) * ϖ⁻¹) =
      o + (A p).cj o + algebraMap _ _ ϖ * (o * (A p).cj o) := by
    have h2 : algebraMap (A p).Fp (A p).Ep ϖ * algebraMap (A p).Fp (A p).Ep ϖ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hϖ0, map_one]
    rw [map_mul, map_sub, map_one, hn, hcw, hw]
    linear_combination (o + (A p).cj o + algebraMap _ _ ϖ * (o * (A p).cj o)) * h2
  have h3 : (n - 1) * ϖ⁻¹ ∈ 𝒪[(A p).Fp] := by
    apply mem_OF_of_alg (A p)
    rw [h1]
    exact (A p).O.add_mem ((A p).O.add_mem ho hco) ((A p).O.mul_mem (alg_mem_O _ _ hϖO) ((A p).O.mul_mem ho hco))
  have h4 : valuation (A p).Fp (n - 1) < 1 := by
    rw [Valuation.mem_integer_iff, map_mul, map_inv₀] at h3
    have hv0 : 0 < valuation (A p).Fp ϖ := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hϖ0)
    have := (mul_inv_le_iff₀ hv0).1 h3
    rw [one_mul] at this
    exact lt_of_le_of_lt this hϖ
  have h5 : valuation (A p).Fp n = 1 := by
    have := Valuation.map_eq_of_sub_lt (valuation (A p).Fp) (x := 1) (y := n) (by rw [map_one]; exact h4)
    rwa [map_one] at this
  have hn0 : n ≠ 0 := by
    intro h0; rw [h0, map_zero] at h5; exact zero_ne_one h5
  have hni : n⁻¹ ∈ 𝒪[(A p).Fp] := by
    rw [Valuation.mem_integer_iff, map_inv₀, h5, inv_one]
  refine ⟨(A p).cj w * algebraMap _ _ n⁻¹, (A p).O.mul_mem (cj_mem _ _ hwO) (alg_mem_O _ _ hni), ?_⟩
  rw [← mul_assoc, ← hn, ← map_mul, mul_inv_cancel₀ hn0, map_one]

omit H in
theorem mem_dual_iff (x : E) : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
    ∀ z : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (x * (z : E)) = n := by
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)]
  constructor
  · intro h z
    obtain ⟨n, hn⟩ := h (z : E) ((FractionalIdeal.mem_one_iff _).2 ⟨z, rfl⟩)
    exact ⟨n, by rw [Algebra.traceForm_apply] at hn; rw [← hn]; rfl⟩
  · intro h a ha
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨n, hn⟩ := h z
    exact ⟨n, by rw [Algebra.traceForm_apply]; rw [show algebraMap (𝓞 E) E z = (z : E) from rfl, hn]; rfl⟩

omit H in
theorem vlt_iff (p : HeightOneSpectrum (𝓞 F)) (a : F) :
    valuation (A p).Fp ((A p).ιF a) < 1 ↔ p.valuation F a < 1 := by
  have := val_iff (A p) 1 a
  rw [map_one, map_one, map_one] at this
  rw [← not_le, ← not_le, this]

theorem locGen_diff (p : HeightOneSpectrum (𝓞 F)) :
    ∃ c : F, valuation (A p).Fp ((A p).ιF c) = valuation (A p).Fp (δ p) ∧
      LocGen p ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) (algebraMap F E c) := by
  have hdd : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) =
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E))⁻¹ := coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)
  set I : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) with hIdef
  have hI0 : I ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)
  have hδ := H.hδ p
  have hvδ : valuation (A p).Fp (δ p) ≠ 0 := (Valuation.ne_zero_iff _).2 hδ
  obtain ⟨c, hc⟩ := exists_val_eq (A := A) (δ := δ) p hδ
  have hιc : (A p).ιF c ≠ 0 := by
    intro h0; rw [h0, map_zero] at hc; exact hvδ hc.symm
  have hc0 : c ≠ 0 := by
    rintro rfl; exact hιc (map_zero _)
  have hac : algebraMap F E c ≠ 0 := by
    rw [Ne, map_eq_zero]; exact hc0
  refine ⟨c, hc, ?_⟩

  have hb : atP p I⁻¹ (algebraMap F E c) := by
    refine memLocalizedAt_inv p I hI0 _ fun x hx => ?_
    rw [← int_iff (A p) H.hinv H.hfix, map_mul, ιE_alg, mul_comm]
    have h1 := diff_fwd H x ((mem_dual_iff x).1 hx) p
    rw [mul_comm] at h1
    exact (scal_iff (A p) ((A p).O : Set (A p).Ep) (O_scal _) _ _ hιc hδ hc _).2 h1

  have hcinv : atP p I (algebraMap F E c)⁻¹ := by
    obtain ⟨π0, hπ0, hπ00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot p.ne_bot
    set ϖ : (A p).Fp := (A p).ιF (π0 : F) with hϖdef
    have hϖ : valuation (A p).Fp ϖ < 1 := (vlt_iff p _).2 ((p.valuation_lt_one_iff_mem π0).2 hπ0)
    have hϖ0 : ϖ ≠ 0 := by
      rw [hϖdef, Ne, map_eq_zero]
      exact fun h => hπ00 (by exact_mod_cast h)
    have := H.top p
    obtain ⟨x0, hx0⟩ := H.sa
      (Function.update (fun p' => Uw A δ p' ((A p').ιE 1)) p
        ((A p).O.toAddSubgroup.comap (AddMonoidHom.mulLeft (algebraMap _ _ (δ p * ϖ⁻¹)))))
      (by
        intro p'
        by_cases hne : p' = p
        · subst hne; rw [Function.update_self]
          exact (H.opn p').preimage (continuous_const_mul _)
        · rw [Function.update_of_ne hne]; exact isOpen_Uw H _ _)
      (by
        refine ((bad_finite H 1).insert p).subset ?_
        intro p' hp'
        by_cases hne : p' = p
        · exact Set.mem_insert_iff.2 (Or.inl hne)
        · refine Set.mem_insert_iff.2 (Or.inr fun hmem => hp' ?_)
          rw [Function.update_of_ne hne]; exact Uw_eq p' _ hmem)
      (Function.update (fun _ => 0) p (algebraMap _ _ (δ p)⁻¹))
      (by
        refine (Set.finite_singleton p).subset ?_
        intro p' hp'
        by_contra hne
        apply hp'
        rw [Function.update_of_ne hne]
        exact (A p').O.zero_mem)
    have h1 : algebraMap _ _ (δ p * ϖ⁻¹) * ((A p).ιE x0 - algebraMap _ _ (δ p)⁻¹) ∈ (A p).O := by
      have := hx0 p
      rwa [Function.update_self, Function.update_self] at this
    set o := algebraMap (A p).Fp (A p).Ep (δ p * ϖ⁻¹) * ((A p).ιE x0 - algebraMap _ _ (δ p)⁻¹) with ho
    have e1 : algebraMap (A p).Fp (A p).Ep ϖ * algebraMap (A p).Fp (A p).Ep ϖ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hϖ0, map_one]
    have e2 : algebraMap (A p).Fp (A p).Ep (δ p) * algebraMap (A p).Fp (A p).Ep (δ p)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ, map_one]
    have hw : (A p).ιE x0 * algebraMap _ _ (δ p) = 1 + algebraMap _ _ ϖ * o := by
      rw [ho, map_mul]
      linear_combination (-(algebraMap (A p).Fp (A p).Ep (δ p) * ((A p).ιE x0 - algebraMap _ _ (δ p)⁻¹))) * e1 + e2
    have hall : ∀ p', (A p').ιE x0 * algebraMap _ _ (δ p') ∈ (A p').O := by
      intro p'
      by_cases hne : p' = p
      · subst hne
        rw [hw]
        refine (A p').O.add_mem (A p').O.one_mem ((A p').O.mul_mem (alg_mem_O _ _ ?_) h1)
        rw [Valuation.mem_integer_iff]; exact hϖ.le
      · have := hx0 p'
        rw [Function.update_of_ne hne, Function.update_of_ne hne, sub_zero] at this
        have h2 : (A p').ιE 1 * algebraMap _ _ (δ p') * (A p').ιE x0 ∈ (A p').O := this.2
        rw [map_one, one_mul, mul_comm] at h2
        exact h2
    have hx0I : x0 ∈ I := (mem_dual_iff x0).2 (diff_bwd H x0 hall)
    obtain ⟨w', hw'O, hw'⟩ := unit_of H p ϖ hϖ0 hϖ o h1
    rw [← hw] at hw'
    have hx00 : x0 ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul, zero_mul] at hw'
      exact zero_ne_one hw'
    have hinv : (A p).ιE x0⁻¹ = algebraMap _ _ (δ p) * w' := by
      have e3 : (A p).ιE x0⁻¹ * (A p).ιE x0 = 1 := by rw [← map_mul, inv_mul_cancel₀ hx00, map_one]
      linear_combination (-((A p).ιE x0⁻¹)) * hw' + (algebraMap _ _ (δ p) * w') * e3
    have h3 : atP p (1 : FractionalIdeal (𝓞 E)⁰ E) ((algebraMap F E c)⁻¹ * x0⁻¹) := by
      rw [← int_iff (A p) H.hinv H.hfix, map_mul, hinv, ← map_inv₀, ιE_alg, map_inv₀, ← mul_assoc, ← map_mul]
      refine (A p).O.mul_mem (alg_mem_O _ _ ?_) hw'O
      rw [Valuation.mem_integer_iff, map_mul, map_inv₀, hc, inv_mul_cancel₀ hvδ]
    have h4 := memLocalization_mul h3 (memLocalization_of_mem (p := p) hx0I)
    rwa [one_mul, mul_assoc, inv_mul_cancel₀ hx00, mul_one] at h4
  rw [hdd]
  refine ⟨hac, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have := memLocalization_mul hx hcinv
    rwa [inv_mul_cancel₀ hI0, ← div_eq_mul_inv] at this
  · have := memLocalization_mul hx hb
    rwa [one_mul, div_mul_cancel₀ _ hac] at this

omit H in

theorem LocGen.inv {p : HeightOneSpectrum (𝓞 F)} {I : FractionalIdeal (𝓞 E)⁰ E} {c : E} (hI : I ≠ 0) (h : LocGen p I c) :
    LocGen p I⁻¹ c⁻¹ := by
  refine ⟨inv_ne_zero h.1, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have := memLocalization_mul hx h.self
    rwa [inv_mul_cancel₀ hI, ← div_inv_eq_mul] at this
  · have h1 : atP p I⁻¹ c⁻¹ := memLocalizedAt_inv p I hI _ fun y hy => by
      rw [← div_eq_mul_inv]; exact (h.2 y).1 (memLocalization_of_mem hy)
    have := memLocalization_mul hx h1
    rwa [one_mul, div_inv_eq_mul, mul_assoc, mul_inv_cancel₀ h.1, mul_one] at this

end Diff

section RecD

open Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum Formalism.MainNotions.LocalModelPeriodLattices
open scoped ComplexOrder

variable {D : Formalism.BasicNotions.D7}

theorem dual_of_agree (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)
    (hA : Agree δ M p) (w : (D.s.atP p).Ep) :
    (∀ y ∈ (D.s.atP p).O, (D.s.atP p).psiE (w * y) = 1) ↔ w * algebraMap _ _ (δ p) ∈ (D.s.atP p).O := by
  obtain ⟨-, hδ, -, hO, hpsi, -⟩ := hA
  rw [← hO, ← (M p).L.additive_character_dual_ring]
  have e2 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hδ, map_one]
  refine forall₂_congr fun y _ => ?_
  have e : w * algebraMap _ _ (δ p) * y * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ = w * y := by
    linear_combination (w * y) * e2
  rw [hpsi, e, AddChar.map_neg_eq_inv, inv_eq_one]

theorem diffHyp_of (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (h6 : adm6 D) (h7 : adm7 D) : DiffHyp (fun p : PlF D => D.s.atP p) δ where
  hinv := conjF_inv
  hfix := conjF_fix
  hδ := fun p => (hA p).2.1
  dual := fun p w => dual_of_agree δ M p (hA p) w
  opn := fun p => by
    have := (hA p).1.loc
    have := (hA p).1.char0
    have := top_of_OK (M p) (hA p).1
    have h := (O_top (M p).L).1
    rwa [(hA p).2.2.2.1] at h
  top := fun p => top_of_OK (M p) (hA p).1
  cjcj := fun p x => by
    have := (M p).L.cj_cj x
    rwa [(hA p).2.2.1] at this
  cjfix := fun p x hx => by
    have := ((M p).L.cj_fix x).1 (by rw [(hA p).2.2.1]; exact hx)
    exact this
  sa := h6
  pf := h7.2

theorem isDiffGen_of_agree (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (h6 : adm6 D) (h7 : adm7 D) (p : PlF D) : IsDiffGen δ p :=
  locGen_diff (diffHyp_of δ M hA h6 h7) p

theorem laIsPeriod_of_adm (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (h6 : adm6 D) (h7 : adm7 D) (ν s : ℕ) : LaIsPeriod δ M ν s :=
  laIsPeriod_of δ M hA (isDiffGen_of_agree δ M hA h6 h7) ν s

theorem global_condition_of_product_formula (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (h6 : adm6 D) (h7 : adm7 D) (i : ℕ) (hi : i ≤ D.R.rS + 1) : G4 δ M i :=
  global_condition_of_local_agreement δ M hA (isDiffGen_of_agree δ M hA h6 h7) i hi

def LocalModelsAtRemainingPrimes (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (m s : ℕ) : Prop :=
  let ν := nu D.R.rS (m + 1) (m + s)
  let L := La M δ ν s
  ∀ (T T' : ℕ), 0 < T → 0 < T' → T ≡ T' [MOD (Lat.gS D) ^ 2] → Nat.Coprime T (Lat.gS D) → Nat.Coprime T' (Lat.gS D) →
  ∀ (hs : 1 ≤ s),
    Gfin δ M T T' ∧
    (∀ (h h' : Point D.host.E m) (t t' : D.host.E) (ht : t ≠ 0) (ht' : t' ≠ 0),
      Kglob δ M T T' (m + s) (ptApp h t ht s hs) (ptApp h' t' ht' s hs) ≠ 0 →
        t⁻¹ - t'⁻¹ ∈ LaP (D := D) ν s ∧ (m + s = D.R.rS + 1 → s = 1 → t = t')) ∧
    ∀ (ι : Type) [Fintype ι] (hd : ι → Point D.host.E m),
      (∀ x y p, detNrmP M δ T T' p (hd x) = detNrmP M δ T T' p (hd y)) →
      ∃ Th : D.host.E → Matrix ι ι ℂ,
        (∀ t, (Th t).PosSemidef) ∧ (∀ t, ∀ l ∈ L, Th (t + l) = Th t) ∧
        (∀ (t : D.host.E) (ht : t ≠ 0), (Th t - Matrix.of fun x y =>
          ∏ᶠ p, ((((M p).modK (blkMod δ T T' p (m + 1) s t * blkMod δ T T' p (m + 1) s t)) ^
            (s * (s - 1) / 2) : ℝ) : ℂ) *
            locK M δ T T' p (m + s) (ptApp (hd x) t ht s hs) (ptApp (hd y) t ht s hs)).PosSemidef) ∧
        ∃ S : Finset D.host.E, (∀ a ∈ S, ∀ b ∈ S, a - b ∈ L → a = b) ∧
          (∀ t, Th t ≠ 0 → ∃ a ∈ S, t - a ∈ L) ∧
          ∀ x0 : ι, ((((∏ᶠ p, (detNrmP M δ T T' p (hd x0)) ^ (-(2 * (s : ℤ)))) : ℝ) : ℂ) •
            (Matrix.of fun x y => ∏ᶠ p, locK M δ T T' p m (hd x) (hd y)) - ∑ a ∈ S, Th a).PosSemidef

theorem block_condition_iff_fourth_clause (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (h6 : adm6 D) (h7 : adm7 D) (m s : ℕ) : G3blk δ M m s ↔ LocalModelsAtRemainingPrimes δ M m s := by
  constructor
  · intro h; exact h.2.2.2
  · intro h
    have h1 := G3lat_of δ M hA (isDiffGen_of_agree δ M hA h6 h7) (nu D.R.rS (m + 1) (m + s)) s
    exact ⟨h1.1, h1.2.1, h1.2.2, h⟩

theorem statement_of_local_block_conditions {Y : TermTie D} (X : TermLocs D Y) (cN : D.what₂.Word → D.what₂.Word → ℝ)
    (h6 : adm6 D) (h7 : adm7 D)
    (h : 4 * D.R.rS + 8 ≤ D.R.k →
      ∃ (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
        (hA : ∀ p, Agree δ M p), G2 δ M (X δ M hA) cN ∧
        (∀ m s, 1 ≤ s → m + s ≤ D.R.rS + 1 → LocalModelsAtRemainingPrimes δ M m s)) : aux₃ D X cN := by
  refine lattice_statement_of_root_gram_blocks X cN fun hk => ?_
  obtain ⟨δ, M, hA, h2, h3⟩ := h hk
  exact ⟨δ, M, hA, G1root_of_agree δ M hA, h2, fun m s hs hm => (block_condition_iff_fourth_clause δ M hA h6 h7 m s).2 (h3 m s hs hm)⟩

end RecD

section LaPS

open Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum Formalism.MainNotions.LocalModelPeriodLattices

section G

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)

theorem cond_gen' (c : F) (ν gp ot : ℕ) (hg : ((gp : ℕ) : A.Fp) ≠ 0) (ho : ((ot : ℕ) : A.Fp) ≠ 0)
    (hvo : valuation A.Fp ((ot : ℕ) : A.Fp) = 1) (k : ℕ) (y : E) :
    A.ιE (y * algebraMap F E ((((gp * ot : ℕ)) : F) ^ k * c ^ ν)) ∈ A.O ↔
      algebraMap A.Fp A.Ep (((gp : ℕ) : A.Fp) ^ k) * (algebraMap A.Fp A.Ep ((A.ιF c) ^ ν) * A.ιE y) ∈ A.O := by
  have hgS : A.ιF (((gp * ot : ℕ)) : F) = ((gp : ℕ) : A.Fp) * ((ot : ℕ) : A.Fp) := by
    rw [map_natCast]; push_cast; rfl
  rw [map_mul, ιE_alg, map_mul, map_pow, map_pow, hgS, mul_comm, map_mul, mul_assoc]
  refine scal_iff A (A.O : Set A.Ep) (O_scal A) _ _ (pow_ne_zero _ (mul_ne_zero hg ho)) (pow_ne_zero _ hg) ?_ _
  rw [map_pow, map_pow, map_mul, hvo, mul_one]

variable {ell : ℕ} (sg : SplitAt A.Fp A.Ep A.cj ell)

theorem typed_iff' (s : ℕ) (X : A.Ep) :
    sg.e (sg.e.symm ((sg.e X).1, (-1) ^ s * (sg.e X).2) * algebraMap A.Fp A.Ep (sg.q : A.Fp)) ∈
        Formalism.FourierDecayAlt.I.orderR (𝒪[A.Fp]) (sg.q : A.Fp) ↔
      algebraMap A.Fp A.Ep (sg.q : A.Fp) * X ∈ A.O ∧ (X - (-1) ^ s * A.cj X) ∈ A.O := by
  have hq : (sg.q : A.Fp) ≠ 0 := fun h0 => sg.q_irr.ne_zero (Subtype.ext h0)
  rw [O_split A sg, O_split A sg]
  simp only [map_mul, map_sub, map_pow, map_neg, map_one, e_alg, AlgEquiv.apply_symm_apply, sg.e_cj,
    Formalism.FourierDecayAlt.I.orderR, Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul, Prod.fst_sub, Prod.snd_sub, Prod.fst_swap,
    Prod.snd_swap, Prod.pow_fst, Prod.pow_snd, Prod.fst_neg, Prod.snd_neg, Prod.fst_one, Prod.snd_one]
  set a := (sg.e X).1
  set b := (sg.e X).2
  set q := (sg.q : A.Fp)
  rcases neg_one_pow_eq_or A.Fp s with hs | hs <;> rw [hs]
  · constructor
    · rintro ⟨h1, h2, t, ht, h3⟩
      have e : a - 1 * b = t := by
        apply mul_left_cancel₀ hq
        linear_combination h3
      refine ⟨⟨by rwa [mul_comm], by rw [mul_comm]; simpa using h2⟩, by rw [e]; exact ht, ?_⟩
      have : b - 1 * a = -t := by rw [← e]; ring
      rw [this]; exact (𝒪[A.Fp]).neg_mem ht
    · rintro ⟨⟨h1, h2⟩, h3, _⟩
      exact ⟨by rwa [mul_comm], by rw [one_mul, mul_comm]; exact h2, _, h3, by ring⟩
  · constructor
    · rintro ⟨h1, h2, t, ht, h3⟩
      have e : a - -1 * b = t := by
        apply mul_left_cancel₀ hq
        linear_combination h3
      refine ⟨⟨by rwa [mul_comm], ?_⟩, by rw [e]; exact ht, ?_⟩
      · have : q * b = -(-1 * b * q) := by ring
        rw [this]; exact (𝒪[A.Fp]).neg_mem h2
      · have : b - -1 * a = t := by rw [← e]; ring
        rw [this]; exact ht
    · rintro ⟨⟨h1, h2⟩, h3, _⟩
      refine ⟨by rwa [mul_comm], ?_, _, h3, by ring⟩
      have : -1 * b * q = -(q * b) := by ring
      rw [this]; exact (𝒪[A.Fp]).neg_mem h2

end G

variable {D : Formalism.BasicNotions.D7}

theorem twist_membership_iff_integral_inv (p : PlF D) (Mp : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hO : Mp.L.O = (D.s.atP p).O)
    (hm : (Mp.split = none ∧ (D.s.atP p).split = none) ∨
      ∃ g sg, Mp.split = some g ∧ (D.s.atP p).split = some sg ∧ g.e = sg.e ∧ g.q = sg.q) (s : ℕ) (X : (D.s.atP p).Ep) :
    twist p s X * algebraMap _ _ ((gpart p : ℕ) : (D.s.atP p).Fp) ∈ Mp.R ↔
      algebraMap _ _ ((gpart p : ℕ) : (D.s.atP p).Fp) * X ∈ (D.s.atP p).O ∧
      (X - (-1) ^ s * (D.s.atP p).cj X) ∈ (D.s.atP p).O := by
  obtain ⟨L, sp, mu⟩ := Mp
  rcases hm with ⟨h1, h⟩ | ⟨g, sg, h1, h, he, hq⟩
  · obtain rfl : sp = none := h1
    rw [twist_none p s X h, gpart_none p h]
    have hR : ((⟨L, none, mu⟩ : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)).R = (D.s.atP p).O := hO
    rw [hR]
    simp only [Nat.cast_one, map_one, mul_one, one_mul]
    refine ⟨fun hX => ⟨hX, ?_⟩, fun hX => hX.1⟩
    refine (D.s.atP p).O.sub_mem hX ((D.s.atP p).O.mul_mem ?_ (cj_mem _ _ hX))
    exact (D.s.atP p).O.pow_mem ((D.s.atP p).O.neg_mem (D.s.atP p).O.one_mem) s
  · rcases sp with _ | g0
    · exact absurd h1 (by simp)
    · have hgg : g0 = g := Option.some.inj h1
      subst hgg
      rw [mem_R_split, he, hq, twist_some p s X sg h, gpart_some p sg h, ← sg.q_eq]
      exact typed_iff' (D.s.atP p) sg s X

def tModInv (δ : ∀ p, (D.s.atP p).Fp) (p : PlF D) (ν s : ℕ) (x : D.host.E) : (D.s.atP p).Ep :=
  algebraMap _ _ ((δ p * ((oth p : ℕ) : (D.s.atP p).Fp)⁻¹) ^ ν) *
    (twist p s ((D.s.atP p).ιE x) * algebraMap _ _ ((gpart p : ℕ) : (D.s.atP p).Fp))

theorem twist_mul (p : PlF D) (s : ℕ) (x y : (D.s.atP p).Ep) : twist p s x * twist p s y = x * y := by
  rcases h : (D.s.atP p).split with _ | sg
  · rw [twist_none p s _ h, twist_none p s _ h]
  · rw [twist_some p s _ sg h, twist_some p s _ sg h]
    apply sg.e.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, map_mul]
    have hs : ((-1 : (D.s.atP p).Fp) ^ s) * (-1) ^ s = 1 := by rw [← mul_pow]; simp
    ext
    · simp
    · simp only [Prod.snd_mul]
      linear_combination ((sg.e x).2 * (sg.e y).2) * hs

theorem tMod_mul_tModInv (δ : ∀ p, (D.s.atP p).Fp) (p : PlF D) (hδ : δ p ≠ 0) (ν s : ℕ) (t : D.host.E) (ht : t ≠ 0) :
    tMod δ p ν s t * tModInv δ p ν s t⁻¹ = 1 := by
  have ho := natFp_ne_zero p _ (oth_ne_zero p)
  have hg := natFp_ne_zero p _ (gpart_ne_zero p)
  have hb : (δ p * ((oth p : ℕ) : (D.s.atP p).Fp)⁻¹) ^ ν ≠ 0 := pow_ne_zero _ (mul_ne_zero hδ (inv_ne_zero ho))
  rw [tMod_eq δ p hδ, tModInv]
  have e1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (((δ p * ((oth p : ℕ) : (D.s.atP p).Fp)⁻¹) ^ ν)⁻¹) *
      algebraMap _ _ ((δ p * ((oth p : ℕ) : (D.s.atP p).Fp)⁻¹) ^ ν) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hb, map_one]
  have e2 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (((gpart p : ℕ) : (D.s.atP p).Fp)⁻¹) *
      algebraMap _ _ ((gpart p : ℕ) : (D.s.atP p).Fp) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hg, map_one]
  have e3 : twist p s ((D.s.atP p).ιE t) * twist p s ((D.s.atP p).ιE t⁻¹) = 1 := by
    rw [twist_mul, ← map_mul, mul_inv_cancel₀ ht, map_one]
  calc _ = (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (((δ p * ((oth p : ℕ) : (D.s.atP p).Fp)⁻¹) ^ ν)⁻¹) *
        algebraMap _ _ ((δ p * ((oth p : ℕ) : (D.s.atP p).Fp)⁻¹) ^ ν)) *
      (twist p s ((D.s.atP p).ιE t) * twist p s ((D.s.atP p).ιE t⁻¹)) *
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (((gpart p : ℕ) : (D.s.atP p).Fp)⁻¹) *
        algebraMap _ _ ((gpart p : ℕ) : (D.s.atP p).Fp)) := by ring
    _ = 1 := by rw [e1, e2, e3]; ring

theorem gdd_neg (a b : ℤ) : gdd (D := D) (-a) (-b) = (gdd (D := D) a b)⁻¹ := by
  unfold gdd
  rw [zpow_neg, zpow_neg, mul_inv, FractionalIdeal.spanSingleton_inv]

theorem gdd_ne_zero (a b : ℤ) : gdd (D := D) a b ≠ 0 := by
  let _ := cmE D
  rw [gdd_eq_idl]
  exact Formalism.FourierDecayAlt.P.S6x2.idl_ne_zero D.host.E _ a b (gS_pos D)

theorem locP_iff (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)
    (hA : Agree δ M p) (c : D.host.F) (hc : c ≠ 0)
    (hv : valuation (D.s.atP p).Fp ((D.s.atP p).ιF c) = valuation (D.s.atP p).Fp (δ p)) (ν s : ℕ) (x : D.host.E) :
    tModInv δ p ν s x ∈ (M p).R ↔
      (D.s.atP p).ιE (x * algebraMap D.host.F D.host.E (((Lat.gS D : ℕ) : D.host.F) ^ 1 * c ^ ν)) ∈ (D.s.atP p).O ∧
      (D.s.atP p).ιE ((x - (-1) ^ s * D.conjF x) *
        algebraMap D.host.F D.host.E (((Lat.gS D : ℕ) : D.host.F) ^ 0 * c ^ ν)) ∈ (D.s.atP p).O := by
  have ho := natFp_ne_zero p _ (oth_ne_zero p)
  have hg := natFp_ne_zero p _ (gpart_ne_zero p)
  have hvo := v_nat p _ (oth_not_dvd p)
  have hδ := hA.2.1
  have hιc : (D.s.atP p).ιF c ≠ 0 := by
    rw [Ne, map_eq_zero]; exact hc
  have e1 : tModInv δ p ν s x ∈ (M p).R ↔
      twist p s (algebraMap _ _ (((D.s.atP p).ιF c) ^ ν) * (D.s.atP p).ιE x) *
        algebraMap _ _ ((gpart p : ℕ) : (D.s.atP p).Fp) ∈ (M p).R := by
    rw [tModInv, twist_alg, mul_assoc]
    refine scal_iff (D.s.atP p) ((M p).R : Set (D.s.atP p).Ep) (R_scal (M p)) _ _
      (pow_ne_zero _ (mul_ne_zero hδ (inv_ne_zero ho))) (pow_ne_zero _ hιc) ?_ _
    rw [map_pow, map_pow, map_mul, map_inv₀, hvo, inv_one, mul_one, hv]
  rw [e1, ← gpart_mul_oth p,
    cond_gen' (D.s.atP p) c ν (gpart p) (oth p) hg ho hvo 1 x,
    cond_gen' (D.s.atP p) c ν (gpart p) (oth p) hg ho hvo 0 (x - (-1) ^ s * D.conjF x),
    tw_gen (D.s.atP p), pow_one, pow_zero, map_one, one_mul]
  exact twist_membership_iff_integral_inv p (M p) hA.2.2.2.1 (agree_split δ M p hA) s _

theorem localCondition_iff (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (hd : ∀ p, IsDiffGen δ p) (ν s : ℕ) (x : D.host.E) :
    x ∈ LaP (D := D) ν s ↔ ∀ p, tModInv δ p ν s x ∈ (M p).R := by
  show (x ∈ gdd (D := D) (-1) (-(ν : ℤ)) ∧ x - (-1) ^ s * D.conjF x ∈ gdd (D := D) 0 (-(ν : ℤ))) ↔ _
  rw [mem_iff_forall_atP (F := D.host.F) (gdd (D := D) (-1) (-(ν : ℤ))) x,
    mem_iff_forall_atP (F := D.host.F) (gdd (D := D) 0 (-(ν : ℤ))) (x - (-1) ^ s * D.conjF x), ← forall_and]
  refine forall_congr' fun p => ?_
  obtain ⟨c, hv, hg⟩ := hd p
  have hc : c ≠ 0 := by
    intro h0
    exact hg.1 (by rw [h0, map_zero])
  have h1 := ((locGen_gdd p c hg 1 ν).inv (gdd_ne_zero _ _)).2 x
  have h2 := ((locGen_gdd p c hg 0 ν).inv (gdd_ne_zero _ _)).2 (x - (-1) ^ s * D.conjF x)
  rw [← gdd_neg, div_inv_eq_mul, ← int_iff (D.s.atP p) conjF_inv conjF_fix] at h1 h2
  rw [locP_iff δ M p (hA p) c hc hv ν s x]
  refine and_congr ?_ ?_
  · exact h1
  · have e : (-((0 : ℕ) : ℤ)) = 0 := by simp
    rw [e] at h2
    exact h2

end LaPS

section Red

open Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum Formalism.MainNotions.LocalModelPeriodLattices Formalism.MainNotions Formalism.MainNotions.S

variable {D : Formalism.BasicNotions.D7}

def LocalGeneratorsModelsAgree (D : Formalism.BasicNotions.D7) {Y : TermTie D} (X : TermLocs D Y) (cN : D.what₂.Word → D.what₂.Word → ℝ) : Prop :=
  4 * D.R.rS + 8 ≤ D.R.k →
    ∃ (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
      (hA : ∀ p, Agree δ M p), G2 δ M (X δ M hA) cN ∧
      (∀ m s, 1 ≤ s → m + s ≤ D.R.rS + 1 → LocalModelsAtRemainingPrimes δ M m s)

theorem statement_iff_local_models {Y : TermTie D} (X : TermLocs D Y) (cN : D.what₂.Word → D.what₂.Word → ℝ)
    (h6 : adm6 D) (h7 : adm7 D) : aux₃ D X cN ↔ LocalGeneratorsModelsAgree D X cN := by
  constructor
  · intro h hk
    obtain ⟨δ, M, hA, -, h2, h3, -⟩ := h hk
    exact ⟨δ, M, hA, h2, fun m s hs hm => (h3 m s hs hm).2.2.2⟩
  · exact statement_of_local_block_conditions X cN h6 h7

theorem packet_iff_local_models {Y : TermTie D} (X : TermLocs D Y) (cN : D.what₂.Word → D.what₂.Word → ℝ) (C : ℝ) :
    Stmt D X cN C ↔ (admitted D X cN C → LocalGeneratorsModelsAgree D X cN) :=
  ⟨fun h hA => (statement_iff_local_models X cN hA.2.2.2.2.2.1 hA.2.2.2.2.2.2.1).1 (h hA),
    fun h hA => (statement_iff_local_models X cN hA.2.2.2.2.2.1 hA.2.2.2.2.2.2.1).2 (h hA)⟩

variable {eps : ℝ} (Fm : FamP eps) {Y : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)}

theorem family_statement_iff_local_models (X : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (Y x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ) (h6 : admF6 Fm) (h7 : admF7 Fm) :
    OrbitValuationBound Fm X cN ↔ OwnEv Fm fun _ _ x i => ∀ hx : Fm.x1 < x, LocalGeneratorsModelsAgree (Fm.D x i) (X x hx i) (cN x i) :=
  ⟨OwnEv.mono fun _ _ x i h hx => (statement_iff_local_models _ _ (h6 x i) (h7 x i)).1 (h hx),
    OwnEv.mono fun _ _ x i h hx => (statement_iff_local_models _ _ (h6 x i) (h7 x i)).2 (h hx)⟩

theorem family_packet_iff_local_models (X : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (Y x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ) :
    KudlaFamilyStatement Fm X cN ↔ (AdmF Fm X cN →
      OwnEv Fm fun _ _ x i => ∀ hx : Fm.x1 < x, LocalGeneratorsModelsAgree (Fm.D x i) (X x hx i) (cN x i)) :=
  ⟨fun h hA => (family_statement_iff_local_models Fm X cN hA.2.2.2.2.2.1 hA.2.2.2.2.2.2.1).1 (h hA),
    fun h hA => (family_statement_iff_local_models Fm X cN hA.2.2.2.2.2.1 hA.2.2.2.2.2.2.1).2 (h hA)⟩

end Red

end Formalism.MainNotions.BridgeLemma

end
