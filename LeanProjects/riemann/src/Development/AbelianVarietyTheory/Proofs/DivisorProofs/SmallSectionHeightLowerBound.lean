import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolHomog
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier

namespace GlobalTheory.SmallSecHeight

variable {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}

theorem isClosed_of_ne (hd : topologicalKrullDim Z = 1) {z : Z} (hz : z ≠ genericPoint Z) :
    IsClosed ({z} : Set Z) := by
  let C (w : Z) : IrreducibleCloseds Z := ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
  rcases Order.krullDim_le_one_iff.1 (show Order.krullDim (IrreducibleCloseds Z) ≤ 1 from hd.le) (C z) with h | h
  · rw [← closure_subset_iff_isClosed]
    intro w hw
    have h1 : C w ≤ C z := closure_minimal (singleton_subset_iff.2 hw) isClosed_closure
    have h2 : z ∈ closure ({w} : Set Z) := h h1 (subset_closure rfl)
    exact ((specializes_iff_mem_closure.2 h2).antisymm (specializes_iff_mem_closure.2 hw)).eq
  · exact absurd (IsGenericPoint.eq (eq_univ_of_univ_subset (@h
      ⟨univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (subset_univ _))) (genericPoint_spec Z)) hz

theorem eq_genericPoint (hZ : IsArithVar q 0) {z : Z} (h : CharZero (Z.residueField z)) :
    z = genericPoint Z := by
  by_contra hz
  have := hZ.finite_residueField (isClosed_of_ne hZ.dim_eq hz)
  exact not_finite (Z.residueField z)

theorem apply_closedPoint (hZ : IsArithVar q 0) (y : Sp ℂ ⟶ Z) :
    y (IsLocalRing.closedPoint ℂ) = genericPoint Z :=
  eq_genericPoint hZ (Scheme.SpecToEquivOfField ℂ Z y).2.hom.charZero

theorem numberField (hZ : IsArithVar q 0) (hc : CharZero (Z.residueField (genericPoint Z))) :
    NumberField (Z.residueField (genericPoint Z)) := by
  obtain ⟨N, j, _, hj⟩ := hZ.isProjOver
  have := isProper_str k N
  have : IsProper q := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hZ.finite)
  let t := q ≫ spMap (Int.castRingHom k)
  have h0 (z : Z) (n : ℤ) : n ∈ (t z).asIdeal ↔ (n : Z.residueField z) = 0 := by
    have e : Z.fromSpecResidueField z ≫ t = spMap (Int.castRingHom (Z.residueField z)) := by
      rw [← Spec.map_preimage (Z.fromSpecResidueField z ≫ t)]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext_int _ _)
    have e2 : t z = spMap (Int.castRingHom (Z.residueField z)) (IsLocalRing.closedPoint _) := by
      rw [← e]
      exact congrArg t (Scheme.fromSpecResidueField_apply _ _).symm
    rw [e2]
    change (n : Z.residueField z) ∈ IsLocalRing.maximalIdeal _ ↔ _
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]
  have h1 (z : Z) (hz : t z = t (genericPoint Z)) : z = genericPoint Z :=
    eq_genericPoint hZ (charZero_of_inj_zero fun n hn => by
      have := (h0 _ n).1 (hz ▸ (h0 z n).2 (by exact_mod_cast hn))
      exact_mod_cast this)
  have h2 : t.QuasiFiniteAt (genericPoint Z) := by
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    have : Subsingleton (t.fiber (t (genericPoint Z))) := ⟨fun a b =>
      (t.fiberHomeo _).injective (Subtype.ext ((h1 _ (t.fiberHomeo _ a).2).trans (h1 _ (t.fiberHomeo _ b).2).symm))⟩
    exact isOpen_discrete _
  rw [Scheme.Hom.quasiFiniteAt_iff] at h2
  have hf : LocallyQuasiFinite (Z.fromSpecResidueField (genericPoint Z) ≫ t) := by
    rw [Scheme.fromSpecResidueField, Category.assoc]
    infer_instance
  rw [← Spec.map_preimage (Z.fromSpecResidueField _ ≫ _), HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite),
    RingHom.ext_int (Spec.preimage (Z.fromSpecResidueField _ ≫ t)).hom
      ((algebraMap ℚ (Z.residueField (genericPoint Z))).comp (algebraMap ℤ ℚ))] at hf
  have := RingHom.quasiFinite_algebraMap.1 hf.of_comp
  exact { to_finiteDimensional := Module.Finite.of_quasiFinite }

def ptsEquiv (hZ : IsArithVar q 0) :
    (Σ σ : k →+* ℂ, CxPts q σ) ≃ (Z.residueField (genericPoint Z) →+* ℂ) := by
  refine (Equiv.ofBijective (fun y : Σ σ : k →+* ℂ, CxPts q σ => y.2.1) ⟨?_, fun y => ?_⟩).trans
    (Equiv.ofBijective (fun f : Z.residueField (genericPoint Z) →+* ℂ =>
      (Scheme.SpecToEquivOfField ℂ Z).symm ⟨_, CommRingCat.ofHom f⟩) ⟨fun f g h => ?_, fun y => ?_⟩).symm
  · rintro ⟨σ, y, hy⟩ ⟨σ', y', hy'⟩ (rfl : y = y')
    obtain rfl : σ = σ' := congrArg CommRingCat.Hom.hom (Spec.map_injective (hy.symm.trans hy'))
    rfl
  · exact ⟨⟨(Spec.preimage (y ≫ q)).hom, y, (Spec.map_preimage _).symm⟩, rfl⟩
  · exact congrArg CommRingCat.Hom.hom (eq_of_heq (Sigma.mk.inj ((Equiv.injective _) h)).2)
  · obtain ⟨⟨z, f⟩, rfl⟩ := (Scheme.SpecToEquivOfField ℂ Z).symm.surjective y
    obtain rfl := eq_genericPoint hZ f.hom.charZero
    exact ⟨f.hom, rfl⟩

theorem mult_nsmul [IsLocallyNoetherian Z] (D : CartierDiv Z) (n : ℕ) (z : Z) :
    (n • D).mult z = n * D.mult z := by
  induction n with
  | zero =>
    rw [zero_nsmul, (CartierDiv.isEqn_zero z).mult_eq, Units.val_one, (unitAt_one z).ord_eq_zero]
    simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem ratVal_pow {σ : k →+* ℂ} {y : CxPts q σ} (hy : under y = genericPoint Z)
    (f : Z.functionField) (n : ℕ) : ratVal (f ^ n) y = ratVal f y ^ n := by
  induction n with
  | zero =>
    have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial 1
    rw [map_one, ev_one mem_ptsIn_top] at e
    rw [pow_zero, pow_zero, e]
  | succ n ih =>
    rw [pow_succ, pow_succ, ratVal_mul (hy ▸ regAt_genericPoint _) (hy ▸ regAt_genericPoint _), ih]

theorem curveDeg_pow [IsLocallyNoetherian Z] (hZ : IsArithVar q 0)
    (hc : CharZero (Z.residueField (genericPoint Z))) (M N : HermLB q) (n : ℕ) (c d : ℝ)
    (a : M.B.ι → N.B.ι) (hU : ∀ j, M.B.U j ≤ N.B.U (a j))
    (hg : ∀ j j' h h', fnOf _ h' (N.B.g (a j) (a j')).val = fnOf _ h (M.B.g j j').val ^ (n + 1))
    (hφ : ∀ σ j y, (N.φ σ).φ (a j) y = (n + 1) * ((M.φ σ).φ j y - 2 * c))
    (hd : ∀ r (hr : IsRatSec M.B r), M.curveDeg hr = d)
    {t : N.B.ι → Z.functionFieldˣ} (ht : IsRatSec N.B t) :
    N.curveDeg ht = (n + 1) * (d - c * Nat.card (Z.residueField (genericPoint Z) →+* ℂ)) := by
  have := hZ.isNoetherian
  obtain ⟨r, hr⟩ := exists_isRatSec M.isLB
  obtain ⟨j₀, h₀⟩ := exists_chart M.isLB (genericPoint Z)
  let r' (j : M.B.ι) : Z.functionFieldˣ := t (a j₀) / r j₀ ^ (n + 1) * r j
  have hr' : IsRatSec M.B r' := fun i j h => by
    simp only [r', Units.val_mul, hr i j h]
    ring
  have key (j) (hj : genericPoint Z ∈ M.B.U j) : t (a j) = r' j * r j ^ n := by
    apply Units.ext
    have e₁ := hr j j₀ (memInf hj h₀)
    have := (r j₀).ne_zero
    rw [ht _ (a j₀) (memInf (hU _ hj) (hU _ h₀)), hg j j₀ (memInf hj h₀)]
    simp only [r', Units.val_mul, Units.val_pow_eq_pow_val, Units.val_div_eq_div_val, e₁]
    field_simp
    ring
  have h₁ (z : Z) : (N.div ht).mult z = (M.div hr').mult z + n * (M.div hr).mult z := by
    obtain ⟨j, hj⟩ := exists_chart M.isLB z
    rw [← mult_nsmul, ← CartierDiv.mult_add,
      ((presents_divOfRatSec N.isLB ht).isEqn _ z (hU _ hj)).mult_eq, key j (gen_mem hj),
      (((presents_divOfRatSec M.isLB hr').isEqn _ z hj).add
        (((presents_divOfRatSec M.isLB hr).isEqn _ z hj).nsmul n)).mult_eq]
  have h₂ (σ) (y : CxPts q σ) : logNorm (N.φ σ) t y =
      logNorm (M.φ σ) r' y + n * logNorm (M.φ σ) r y + (n + 1) * c := by
    have hy : under y = genericPoint Z := apply_closedPoint hZ y.1
    have ho (D : CartierDiv Z) : y ∈ offSupp q σ D := mem_offSupp.2 (hy ▸ D.genericPoint_notMem_supp)
    have hj := mem_pick (M.φ σ).isLB y
    have hu (g : Z.functionFieldˣ) : ‖ratVal (g : Z.functionField) y‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero (hy ▸ unitAt_genericPoint g.ne_zero))
    rw [logNorm_eq _ ht (ho _) (ptsIn_mono (hU _) hj), logNorm, logNorm, hφ,
      key _ (gen_mem (mem_ptsIn.1 hj)), Units.val_mul, Units.val_pow_eq_pow_val,
      ratVal_mul (hy ▸ regAt_genericPoint _) (hy ▸ regAt_genericPoint _), ratVal_pow hy, norm_mul,
      norm_pow, Real.log_mul (hu _) (pow_ne_zero _ (hu _)), Real.log_pow]
    ring
  have hfin (D : CartierDiv Z) : (Function.support fun z =>
      (D.mult z : ℝ) * Real.log (Nat.card (Z.residueField z))).Finite :=
    D.finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  have := numberField hZ hc
  have : Finite (Σ σ : k →+* ℂ, CxPts q σ) := .of_equiv _ (ptsEquiv hZ).symm
  have (σ : k →+* ℂ) : Finite (CxPts q σ) := .of_injective _ (sigma_mk_injective (i := σ))
  have := hZ.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have (σ : k →+* ℂ) := Fintype.ofFinite (CxPts q σ)
  have e := hd _ hr
  have e' := hd _ hr'
  have e₀ : ∑ᶠ z, ((N.div ht).mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) =
      ∑ᶠ z, ((M.div hr').mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) +
      n * ∑ᶠ z, ((M.div hr).mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) := by
    rw [mul_finsum, ← finsum_add_distrib (hfin _) ((hfin (M.div hr)).subset fun z hz h0 => hz (by
      simp only [h0, mul_zero]))]
    refine finsum_congr fun z => ?_
    rw [h₁]
    push_cast
    ring
  rw [HermLB.curveDeg, e₀, ← Nat.card_congr (ptsEquiv hZ), Nat.card_sigma]
  rw [HermLB.curveDeg] at e e'
  simp only [finsum_eq_sum_of_fintype, h₂, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul, Nat.card_eq_fintype_card, Nat.cast_sum] at e e' ⊢
  linear_combination e' + n * e

theorem le_ptHt : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (L : HermLB p) (m : ℕ) (c b : ℝ) (x : X) (s : ((L.shift (fun _ => -c) fun _ => rfl).pow m).B.Sec), 1 ≤ m →
    s ∈ ((L.shift (fun _ => -c) fun _ => rfl).pow m).smallSec → x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s →
    IsAlgPt x → IsPtHt L x b → c ≤ b := by
  intro k _ X _ p D hX L m c b x s hm hs hx ⟨hc, hd⟩ ⟨h, H, hb⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hm
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  have := hX.isNoetherian_sub i
  have hr : range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr] at hd
  have hbij : Function.Bijective (i.residueFieldMap (genericPoint Z)).hom := by
    refine ⟨RingHom.injective _, fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
    obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
    exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩
  let E := RingEquiv.ofBijective _ hbij
  have hc' : CharZero (Z.residueField (genericPoint Z)) := (RingHom.charZero_iff hbij.1).1 hc
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hcΓ hd
  have hcard : Nat.card (X.residueField (i (genericPoint Z)) →+* ℂ) =
      Nat.card (Z.residueField (genericPoint Z) →+* ℂ) :=
    Nat.card_congr ⟨fun f => f.comp E.symm.toRingHom, fun f => f.comp E.toRingHom,
      fun f => by ext; simp, fun f => by ext; simp⟩
  have := numberField hZ hc'
  have hpos : (0 : ℝ) < Nat.card (Z.residueField (genericPoint Z) →+* ℂ) := by
    exact_mod_cast Nat.card_pos
  let P := (L.shift (fun _ => -c) fun _ => rfl).pow (n + 1)
  have hu : genericPoint Z ∈ nonzeroLocus (GlobalTheory.secPull s i) := by
    rw [GlobalTheory.nonzeroLocus_secPull]; exact hx
  have key := curveDeg_pow hZ hc' (L.restr i) (P.restr i) n c (h (i (genericPoint Z))) (fun j _ => j)
    (fun j z hz => mem_iInter.2 fun _ => mem_iInter.2 fun u => mem_iInter.1 hz u)
    (fun j j' h h' => ?_) (fun σ j y => ?_) (fun r hr => (H.point Z i hcΓ hd r hr).symm)
    (isRatSec_ratOfSec _ hu)
  · have h0 : 0 ≤ (P.restr i).curveDeg (isRatSec_ratOfSec _ hu) := by
      refine le_of_le_of_eq ?_ (HermLB.curveDeg_sec (L := P) i s hu fun σ y =>
        mem_ptsIn.2 ((apply_closedPoint hZ y.1).symm ▸ hu)).symm
      refine sub_nonneg.2 (le_trans (b := 0) ?_ (finsum_nonneg fun z => mul_nonneg
        (Int.cast_nonneg (mult_divOfSec_nonneg z)) (Real.log_natCast_nonneg _)))
      have np {α : Type} {f : α → ℝ} (hf : ∀ a, f a ≤ 0) : ∑ᶠ a, f a ≤ 0 :=
        finsum_induction (· ≤ 0) le_rfl (fun _ _ => add_nonpos) hf
      refine np fun σ => np fun y => ?_
      exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (Weight.nsq_nonneg _ _ _) (hs σ _)) zero_le_two
    rw [key, hb, hcard, ← sub_mul] at h0
    exact sub_nonneg.1 (nonneg_of_mul_nonneg_left (nonneg_of_mul_nonneg_right h0 (by positivity)) hpos)
  · have e (u : PUnit → L.B.ι) (z : Z) (hz : z ∈ (P.restr i).B.U fun _ => u) : z ∈ i ⁻¹ᵁ L.B.U (u ⟨⟩) :=
      mem_iInter.1 (mem_iInter.1 hz ⟨⟩) ⟨⟩
    have e₁ : (P.restr i).B.g (fun _ => j) (fun _ => j') =
        res (X := Z) (U := i ⁻¹ᵁ (L.B.U (j ⟨⟩) ⊓ L.B.U (j' ⟨⟩)))
          (V := (P.restr i).B.U (fun _ => j) ⊓ (P.restr i).B.U fun _ => j') (fun z hz => ⟨e _ z hz.1, e _ z hz.2⟩)
          (pullU i _ (L.B.g (j ⟨⟩) (j' ⟨⟩))) ^ (n + 1) := by
      refine (pull_g _ i _ _).trans ?_
      have e₂ : P.B.g j j' = res (X := X) (U := L.B.U (j ⟨⟩) ⊓ L.B.U (j' ⟨⟩)) (V := P.B.U j ⊓ P.B.U j')
          (fun _ hz => ⟨mem_iInter.1 hz.1 ⟨⟩, mem_iInter.1 hz.2 ⟨⟩⟩) (L.B.g (j ⟨⟩) (j' ⟨⟩)) ^ (n + 1) := by
        change ∏ _k : PUnit, _ = _
        refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
        rfl
      refine (congrArg (fun u => res _ (pullU i _ u)) e₂).trans ?_
      rw [map_pow, map_pow]
      refine congrArg (· ^ (n + 1)) (Units.ext ?_)
      exact (congrArg (resG Z _) (app_resG _ _ _)).trans (resG_resG _ _ _)
    rw [e₁, Units.val_pow_eq_pow_val, map_pow]
    refine congrArg (· ^ (n + 1)) ?_
    exact (fnOf_resG _ h' _).trans ((congrArg (fun u : Γ(Z, _)ˣ => fnOf _ h u.val)
      (pull_g L.B i j j')).trans (fnOf_resG _ h _)).symm
  · refine ((P.φ σ).pull_φ i rfl _ y).trans ((Weight.zpow_φ _ _ _ _).trans ?_)
    rw [show ((L.restr i).φ σ).φ j y = _ from (L.φ σ).pull_φ i rfl j y]
    change _ * (_ + 2 * -c) = _
    push_cast
    ring

end GlobalTheory.SmallSecHeight
