import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolHomog
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier

namespace GlobalTheory.HtSelfInter

variable {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}

theorem isClosed_of_ne_genericPoint [IsIntegral Z] (hd : topologicalKrullDim Z = 1) {z : Z}
    (hz : z ≠ genericPoint Z) : IsClosed ({z} : Set Z) := by
  rcases Order.krullDim_le_one_iff.1 (show Order.krullDim (IrreducibleCloseds Z) ≤ 1 from hd.le)
    ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ with h | h
  · refine isClosed_of_closure_subset fun w hw => ?_
    have h₁ : (⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩ : IrreducibleCloseds Z) ≤
        ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ :=
      closure_minimal (Set.singleton_subset_iff.2 hw) isClosed_closure
    have h₂ : z ∈ closure {w} := h h₁ (subset_closure rfl)
    exact ((specializes_iff_mem_closure.2 h₂).antisymm (specializes_iff_mem_closure.2 hw)).eq
  · exact absurd (IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@h
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _)))
      (genericPoint_spec Z)) hz

theorem charZero_residueField_genericPoint [IsIntegral Z] (hc : CharZero Γ(Z, ⊤)) :
    CharZero (Z.residueField (genericPoint Z)) := by
  have h₁ : CharZero Z.functionField :=
    charZero_of_injective_ringHom (fnOf_injective (⊤ : Z.Opens) (Opens.mem_top _))
  let f : Z.functionField →+* Z.residueField (genericPoint Z) := (Z.residue _).hom
  exact charZero_of_injective_ringHom f.injective

theorem eq_genericPoint [IsIntegral Z] {q : Z ⟶ Sp k} (hZ : IsArithVar q 0) {z : Z}
    (hz : CharZero (Z.residueField z)) : z = genericPoint Z := by
  by_contra h
  have := hZ.finite_residueField (isClosed_of_ne_genericPoint hZ.dim_eq h)
  exact not_finite (Z.residueField z)

theorem finite_ringHom [IsIntegral Z] {q : Z ⟶ Sp k} (hZ : IsArithVar q 0) :
    Finite (Z.residueField (genericPoint Z) →+* ℂ) := by
  have hc := charZero_residueField_genericPoint hZ.charZero
  obtain ⟨N, j, _, hj⟩ := hZ.isProjOver
  have := isProper_str k N
  have : IsProper q := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hZ.finite)
  let t := q ≫ spMap (Int.castRingHom k)
  have h₁ : t.QuasiFiniteAt (genericPoint Z) := by
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    have h0 : CharZero ((Sp ℤ).residueField (t (genericPoint Z))) :=
      (t.residueFieldMap (genericPoint Z)).hom.charZero
    have hs (w : t.fiber (t (genericPoint Z))) : t.fiberι _ w = genericPoint Z := by
      have e : t (t.fiberι _ w) = t (genericPoint Z) :=
        (t.range_fiberι (t (genericPoint Z))).le ⟨w, rfl⟩
      rw [← e] at h0
      exact eq_genericPoint hZ (charZero_of_injective_ringHom (t.residueFieldMap _).hom.injective)
    have : Subsingleton (t.fiber (t (genericPoint Z))) := ⟨fun a b =>
      (t.fiberι _).isEmbedding.injective ((hs a).trans (hs b).symm)⟩
    exact isOpen_discrete _
  have h₂ := Scheme.Hom.quasiFiniteAt_iff.1 h₁
  have h₃ : LocallyQuasiFinite (Z.fromSpecResidueField (genericPoint Z) ≫ t) := by
    rw [Scheme.fromSpecResidueField, Category.assoc]
    infer_instance
  rw [← Spec.map_preimage (Z.fromSpecResidueField (genericPoint Z) ≫ t),
    HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite),
    RingHom.ext_int (Spec.preimage (Z.fromSpecResidueField (genericPoint Z) ≫ t)).hom
      ((algebraMap ℚ (Z.residueField (genericPoint Z))).comp (Int.castRingHom ℚ))] at h₃
  have h₄ := RingHom.quasiFinite_algebraMap.1 (RingHom.QuasiFinite.of_comp h₃)
  have : Module.Finite ℚ (Z.residueField (genericPoint Z)) := .of_quasiFinite
  exact .of_equiv _ (RingHom.equivRatAlgHom _ ℂ).symm

theorem nonempty_equiv [IsIntegral Z] {q : Z ⟶ Sp k} (hZ : IsArithVar q 0) :
    Nonempty ((Σ σ : k →+* ℂ, CxPts q σ) ≃ (Z.residueField (genericPoint Z) →+* ℂ)) := by
  have h₁ : Function.Bijective fun y : (Σ σ : k →+* ℂ, CxPts q σ) => y.2.1 := by
    refine ⟨?_, fun y => ⟨⟨(Spec.preimage (y ≫ q)).hom, y, (Spec.map_preimage _).symm⟩, rfl⟩⟩
    rintro ⟨σ, y, hy⟩ ⟨σ', y', hy'⟩ (rfl : y = y')
    obtain rfl : σ = σ' := congrArg CommRingCat.Hom.hom (Spec.map_injective (hy.symm.trans hy'))
    rfl
  have h₂ : Function.Bijective fun φ : Z.residueField (genericPoint Z) →+* ℂ =>
      (Spec.map (CommRingCat.ofHom φ) ≫ Z.fromSpecResidueField (genericPoint Z) : Sp ℂ ⟶ Z) := by
    refine ⟨fun φ ψ h => congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h)),
      fun y => ?_⟩
    obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField ℂ Z).symm.surjective y
    obtain rfl := eq_genericPoint hZ (z := z) φ.hom.charZero
    exact ⟨φ.hom, rfl⟩
  exact ⟨(Equiv.ofBijective _ h₁).trans (Equiv.ofBijective _ h₂).symm⟩

theorem finsum_add_const [IsIntegral Z] {q : Z ⟶ Sp k} (hZ : IsArithVar q 0)
    (f : ∀ σ : k →+* ℂ, CxPts q σ → ℝ) (c : ℝ) :
    ∑ᶠ σ, ∑ᶠ y, (f σ y + c) =
      (∑ᶠ σ, ∑ᶠ y, f σ y) + c * Nat.card (Z.residueField (genericPoint Z) →+* ℂ) := by
  have := finite_ringHom hZ
  have := hZ.finite_emb
  obtain ⟨e⟩ := nonempty_equiv hZ
  have : Finite (Σ σ : k →+* ℂ, CxPts q σ) := .of_equiv _ e.symm
  have (σ : k →+* ℂ) : Finite (CxPts q σ) := .of_injective _ (sigma_mk_injective (i := σ))
  let := Fintype.ofFinite (k →+* ℂ)
  let (σ : k →+* ℂ) := Fintype.ofFinite (CxPts q σ)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [finsum_eq_sum_of_fintype, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_sum, Finset.mul_sum, mul_comm]

theorem card_ringHom_eq (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    Nat.card (X.residueField (i z) →+* ℂ) = Nat.card (Z.residueField z →+* ℂ) := by
  have hs : Function.Surjective (i.residueFieldMap z).hom := fun a => by
    obtain ⟨b, rfl⟩ := Z.residue_surjective z a
    obtain ⟨c, rfl⟩ := i.stalkMap_surjective z b
    exact ⟨X.residue _ c, congrArg (fun f => f.hom c) (Scheme.residue_residueFieldMap i z)⟩
  let e := RingEquiv.ofBijective _ ⟨(i.residueFieldMap z).hom.injective, hs⟩
  exact Nat.card_congr ⟨fun φ => φ.comp e.symm.toRingHom, fun φ => φ.comp e.toRingHom,
    fun φ => by ext; simp, fun φ => by ext; simp⟩

theorem curveDeg_shift (hX : IsArithVar p D) (L : HermLB p) (t : ℝ) (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] [IsLocallyNoetherian Z] (hc : CharZero Γ(Z, ⊤)) (hd : topologicalKrullDim Z = 1)
    {r : (L.restr i).B.ι → Z.functionFieldˣ} (hr : IsRatSec (L.restr i).B r) :
    ((L.shift (fun _ => t) fun _ => rfl).restr i).curveDeg (r := r) hr =
      (L.restr i).curveDeg hr + t * Nat.card (X.residueField (i (genericPoint Z)) →+* ℂ) := by
  have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc hd
  have e (σ : k →+* ℂ) (y : CxPts (i ≫ p) σ) :
      logNorm (((L.shift (fun _ => t) fun _ => rfl).restr i).φ σ) r y =
        logNorm ((L.restr i).φ σ) r y + -t := by
    have e₁ := ((L.shift (fun _ => t) fun _ => rfl).φ σ).pull_φ i rfl
      (CxPts.pick ((L.restr i).φ σ).isLB y) y
    have e₂ := (L.φ σ).pull_φ i rfl (CxPts.pick ((L.restr i).φ σ).isLB y) y
    have e₃ := e₁.trans (congrArg (· + 2 * t) e₂.symm)
    refine (congrArg (_ - · / 2) e₃).trans ?_
    unfold logNorm
    exact (fun a b : ℝ => (by ring : a - (b + 2 * t) / 2 = a - b / 2 + -t)) _ _
  unfold HermLB.curveDeg
  simp only [e]
  rw [finsum_add_const hZ, card_ringHom_eq]
  exact (fun a b c : ℝ => (by ring : a - (b + -t * c) = a - b + t * c)) _ _ _

theorem isAlgPt_genericPoint (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (hc : CharZero Γ(Z, ⊤))
    (hd : topologicalKrullDim Z = 1) : IsAlgPt (i (genericPoint Z)) := by
  have := charZero_residueField_genericPoint hc
  refine ⟨(i.residueFieldMap _).hom.charZero, ?_⟩
  have h₁ := (genericPoint_spec Z).image i.continuous
  rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
  rw [h₁.def, ← hd]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

theorem arVol_nonneg (L : HermLB p) (D : ℕ) : 0 ≤ arVol L D := by
  refine le_limsup_of_frequently_le (Frequently.of_forall fun m => mul_nonneg ?_ ?_)
  · rw [ENNReal.zero_le_log_iff]
    exact_mod_cast Set.one_le_encard_iff_nonempty.2 ⟨_, (L.pow m).zero_mem_smallSec⟩
  · exact EReal.coe_nonneg.2 (by positivity)

theorem isNef_shift (hX : IsArithVar p D) {L : HermLB p} {e : ℝ} (hs : L.SemiPos D) (hf : NefFib L)
    (hh : ∀ x, IsAlgPt x → ∃ b, IsPtHt L x b ∧ e ≤ b) :
    (L.shift (fun _ => -e) fun _ => rfl).IsNef D where
  semiPos := hs.shift _ _
  vertical := hf
  horizontal Z i _ _ _ hc hd := by
    obtain ⟨r, hr⟩ := exists_isRatSec (L.restr i).isLB
    obtain ⟨b, ⟨h, H, hb⟩, hle⟩ := hh _ (isAlgPt_genericPoint i hc hd)
    refine ⟨r, hr, ?_⟩
    rw [curveDeg_shift hX L (-e) i hc hd hr, ← H.point Z i hc hd r hr, hb, ← add_mul]
    exact mul_nonneg (by linarith) (Nat.cast_nonneg _)

theorem selfInter_ge_of_height_ge : GlobalTheory.Published.VolNef → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (a e : ℝ), L.SemiPos D → NefFib L →
    L.IsSelfInter a → (∀ x, IsAlgPt x → ∃ b, IsPtHt L x b ∧ e ≤ b) → ((D : ℝ) + 1) * e * gdeg L D ≤ a := by
  intro hV hA k _ X _ p D hX L a e hs hf ha hh
  have h₁ := hV k X p D hX _ _ (isNef_shift hX hs hf hh) (hA.arShift k X p D hX L a (-e) ha)
  have h₂ := EReal.coe_nonneg.1 ((arVol_nonneg _ D).trans_eq h₁)
  linarith

end GlobalTheory.HtSelfInter
