import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailLast
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TrdegEqOfLeOfIsAlgebraic
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PModelGenericPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver chartRingOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

noncomputable section

namespace SpecialCurvesDim

section LocalRing

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem exists_mul_eq_of_mem_locIn (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] {v : Ω}
    (hv : v ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p) : ∃ a b : A, b ∉ p ∧ v * b = a := by
  have h1 : (1 : A) ∉ p := fun h => hp.ne_top ((Ideal.eq_top_iff_one p).2 h)
  unfold IndefiniteRowSideFullHecke.Kleiman2.locIn at hv
  induction hv using Subring.closure_induction with
  | mem u hu =>
    obtain ⟨a, b, hb, rfl⟩ := hu
    have hb0 : (b : Ω) ≠ 0 := fun h => hb (by rw [show b = 0 from Subtype.ext h]; exact p.zero_mem)
    exact ⟨a, b, hb, div_mul_cancel₀ _ hb0⟩
  | zero => exact ⟨0, 1, h1, by simp⟩
  | one => exact ⟨1, 1, h1, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, b, hb, hab⟩ := hu
    obtain ⟨a', b', hb', hab'⟩ := hv
    refine ⟨a * b' + a' * b, b * b', fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    push_cast
    rw [← hab, ← hab']
    ring
  | neg u _ hu =>
    obtain ⟨a, b, hb, hab⟩ := hu
    exact ⟨-a, b, hb, by push_cast; rw [← hab]; ring⟩
  | mul u v _ _ hu hv =>
    obtain ⟨a, b, hb, hab⟩ := hu
    obtain ⟨a', b', hb', hab'⟩ := hv
    refine ⟨a * a', b * b', fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    push_cast
    rw [← hab, ← hab']
    ring

theorem mul_ne_one_of_mem (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] {a : A} (ha : a ∈ p) {v : Ω}
    (hv : v ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p) : (a : Ω) * v ≠ 1 := by
  intro h
  obtain ⟨a', b', hb', hab'⟩ := exists_mul_eq_of_mem_locIn A p hv
  have hb : b' = a * a' := Subtype.ext (by
    push_cast
    rw [← hab', ← mul_assoc, h, one_mul])
  exact hb' (hb ▸ p.mul_mem_right _ ha)

theorem mem_locIn (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] {a : Ω} (ha : a ∈ A) :
    a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  Subring.subset_closure ⟨⟨a, ha⟩, 1, fun h => hp.ne_top ((Ideal.eq_top_iff_one p).2 h), by simp⟩

theorem inv_mem_locIn (A : Subalgebra S Ω) (p : Ideal A) [p.IsPrime] {b : A} (hb : b ∉ p) :
    (b : Ω)⁻¹ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  Subring.subset_closure ⟨1, b, hb, by simp⟩

end LocalRing

section Homogenize

variable {O : Type} [CommRing O] {K : Type} [Fintype K] {ι : K → Type}

theorem exists_clear_denominators (c : ∀ k, ι k) (f : MvPolynomial (Σ k, ι k) O) :
    ∃ (F : MvPolynomial (Σ k, ι k) O) (n : ℕ), ∀ (L : Type) [Field L] (χ : O →+* L) (v : (Σ k, ι k) → L),
      (∀ k, v ⟨k, c k⟩ ≠ 0) →
        eval₂ χ v F = (∏ k, v ⟨k, c k⟩) ^ n * eval₂ χ (fun p => v p / v ⟨p.1, c p.1⟩) f := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨C a, 0, fun L _ χ v _ => by simp⟩
  | add f g hf hg =>
    obtain ⟨F, n, hF⟩ := hf
    obtain ⟨G, m, hG⟩ := hg
    refine ⟨F * (∏ k, X ⟨k, c k⟩) ^ m + G * (∏ k, X ⟨k, c k⟩) ^ n, n + m, fun L _ χ v hv => ?_⟩
    simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_prod, eval₂_X, hF L χ v hv, hG L χ v hv]
    ring
  | mul_X f p hf =>
    obtain ⟨F, n, hF⟩ := hf
    refine ⟨F * X p * ∏ k ∈ Finset.univ.erase p.1, X ⟨k, c k⟩, n + 1, fun L _ χ v hv => ?_⟩
    simp only [eval₂_mul, eval₂_X, eval₂_prod, hF L χ v hv]
    rw [← Finset.mul_prod_erase Finset.univ (fun k => v ⟨k, c k⟩) (Finset.mem_univ p.1)]
    have h0 := hv p.1
    field_simp
    ring

end Homogenize

section Main

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Fintype K] {ι : K → Type}
  {Ω : Type} [Field Ω] [Algebra O Ω]

theorem eval₂_ratio_eq_zero (y : (Σ k, ι k) → Ω) (W : Ideal (NumbersDVR.MRing ι (IsLocalRing.ResidueField O)))
    [W.IsPrime] (hW : NumbersDVR.specialIdeal (mIdealOver O y) ≤ W) (c : ∀ k, ι k)
    (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hwc : ∀ k, ModelGenericPoint.genPt W ⟨k, c k⟩ ≠ 0)
    {f : MvPolynomial (Σ k, ι k) O} (hf : aeval (fun p => y p / y ⟨p.1, c p.1⟩) f = 0) :
    eval₂ ((algebraMap (IsLocalRing.ResidueField O) (FractionRing (NumbersDVR.MRing ι (IsLocalRing.ResidueField O) ⧸ W))).comp
      (IsLocalRing.residue O))
      (fun p => ModelGenericPoint.genPt W p / ModelGenericPoint.genPt W ⟨p.1, c p.1⟩) f = 0 := by
  obtain ⟨F, n, hF⟩ := exists_clear_denominators c f
  let χE : O →+* FractionRing (MvPolynomial K Ω) :=
    (algebraMap (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω))).comp
      ((algebraMap Ω (MvPolynomial K Ω)).comp (algebraMap O Ω))
  let vE : (Σ k, ι k) → FractionRing (MvPolynomial K Ω) := fun p =>
    algebraMap (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω)) (C (y p) * X p.1)
  have hinj : Function.Injective (algebraMap (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω))) :=
    IsFractionRing.injective _ _
  have hvE : ∀ k, vE ⟨k, c k⟩ ≠ 0 := fun k h =>
    mul_ne_zero (C_ne_zero.2 (hyc k)) (X_ne_zero _) ((map_eq_zero_iff _ hinj).1 h)
  have hcone : ∀ g, eval₂ χE vE g =
      algebraMap (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω)) (mConeMapOver O y g) := by
    intro g
    have : eval₂Hom χE vE =
        (algebraMap (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω))).comp (mConeMapOver O y).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_)
      · simp [χE, mConeMapOver, MvPolynomial.algebraMap_eq]
      · simp [vE, mConeMapOver]
    exact RingHom.congr_fun this g
  have hv : (fun p : Σ k, ι k => vE p / vE ⟨p.1, c p.1⟩) =
      fun p => algebraMap (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω)) (C (y p / y ⟨p.1, c p.1⟩)) := by
    funext p
    rw [div_eq_iff (hvE p.1)]
    show algebraMap (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω)) (C (y p) * X p.1) =
      algebraMap (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω)) (C (y p / y ⟨p.1, c p.1⟩)) *
        algebraMap (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω)) (C (y ⟨p.1, c p.1⟩) * X p.1)
    rw [← map_mul, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ (hyc p.1)]
  have hratio : ∀ g, eval₂ χE (fun p => vE p / vE ⟨p.1, c p.1⟩) g =
      algebraMap (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω))
        (C (aeval (fun p => y p / y ⟨p.1, c p.1⟩) g)) := by
    intro g
    rw [hv]
    have : eval₂Hom χE (fun p => algebraMap (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω))
        (C (y p / y ⟨p.1, c p.1⟩))) =
        ((algebraMap (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω))).comp C).comp
          (aeval (fun p => y p / y ⟨p.1, c p.1⟩)).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_)
      · simp [χE, MvPolynomial.algebraMap_eq]
      · simp
    exact RingHom.congr_fun this g
  have hFI : F ∈ mIdealOver O y := by
    have h := hF _ χE vE hvE
    rw [hratio, hf, map_zero, map_zero, mul_zero, hcone] at h
    exact (map_eq_zero_iff _ hinj).1 h
  have hFW : MvPolynomial.map (IsLocalRing.residue O) F ∈ W := hW (Ideal.mem_map_of_mem _ hFI)
  rw [← ModelGenericPoint.aeval_genPt_eq_zero, aeval_def, eval₂_map] at hFW
  have h := hF _ ((algebraMap (IsLocalRing.ResidueField O) _).comp (IsLocalRing.residue O))
    (ModelGenericPoint.genPt W) hwc
  rw [hFW] at h
  exact (mul_eq_zero.1 h.symm).resolve_left (pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun k _ => hwc k))

end Main

section Chart

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]

theorem exists_mul_pow_eq_aeval {ι₀ : Type} (x : ι₀ → Ω) (j : Unit → ι₀) (c₀ : ι₀) (hj : x (j ()) ≠ 0) {a : Ω}
    (ha : a ∈ chartRingOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) j) :
    ∃ (D : ℕ) (g : MvPolynomial ι₀ O), a * (x (j ()) / x c₀) ^ D = aeval (fun l => x l / x c₀) g := by
  unfold chartRingOver at ha
  induction ha using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ⟨⟨⟨⟩, l⟩, rfl⟩ := hu
    refine ⟨1, X l, ?_⟩
    simp only [IndefiniteRowSideFullHecke.Kleiman2.oneBlock, aeval_X, pow_one]
    rw [div_mul_div_comm, mul_comm (x l), mul_div_mul_left _ _ hj]
  | algebraMap r => exact ⟨0, C r, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨D₁, g₁, h₁⟩ := hu
    obtain ⟨D₂, g₂, h₂⟩ := hv
    refine ⟨D₁ + D₂, g₁ * X (j ()) ^ D₂ + g₂ * X (j ()) ^ D₁, ?_⟩
    simp only [map_add, map_mul, map_pow, aeval_X, ← h₁, ← h₂]
    ring
  | mul u v _ _ hu hv =>
    obtain ⟨D₁, g₁, h₁⟩ := hu
    obtain ⟨D₂, g₂, h₂⟩ := hv
    refine ⟨D₁ + D₂, g₁ * g₂, ?_⟩
    simp only [map_mul, ← h₁, ← h₂]
    ring

omit [Algebra O Ω] in

theorem eval₂_mem_adjoin [IsLocalRing O] {ι₀ L : Type} [Field L] [Algebra (IsLocalRing.ResidueField O) L] (s : ι₀ → L)
    (g : MvPolynomial ι₀ O) :
    eval₂ ((algebraMap (IsLocalRing.ResidueField O) L).comp (IsLocalRing.residue O)) s g ∈
      Algebra.adjoin (IsLocalRing.ResidueField O) (Set.range s) := by
  induction g using MvPolynomial.induction_on with
  | C a => rw [eval₂_C]; exact Subalgebra.algebraMap_mem _ _
  | add f g hf hg => rw [eval₂_add]; exact add_mem hf hg
  | mul_X f l hf => rw [eval₂_mul, eval₂_X]; exact mul_mem hf (Algebra.subset_adjoin ⟨l, rfl⟩)

end Chart

section Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Fintype K] {ι : K → Type}
  {Ω : Type} [Field Ω] [Algebra O Ω]

theorem exists_ratio_eq_div (y : (Σ k, ι k) → Ω) (k₀ : K) (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase O y k₀)
    (W : Ideal (NumbersDVR.MRing ι (IsLocalRing.ResidueField O))) [W.IsPrime]
    (hW : NumbersDVR.specialIdeal (mIdealOver O y) ≤ W) (c : ∀ k, ι k)
    (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hwc : ∀ k, ModelGenericPoint.genPt W ⟨k, c k⟩ ≠ 0) (p : Σ k, ι k) :
    ∃ a b : FractionRing (NumbersDVR.MRing ι (IsLocalRing.ResidueField O) ⧸ W),
      a ∈ Algebra.adjoin (IsLocalRing.ResidueField O)
        (Set.range fun l : ι k₀ => ModelGenericPoint.genPt W ⟨k₀, l⟩ / ModelGenericPoint.genPt W ⟨k₀, c k₀⟩) ∧
      b ∈ Algebra.adjoin (IsLocalRing.ResidueField O)
        (Set.range fun l : ι k₀ => ModelGenericPoint.genPt W ⟨k₀, l⟩ / ModelGenericPoint.genPt W ⟨k₀, c k₀⟩) ∧
      b ≠ 0 ∧ ModelGenericPoint.genPt W p / ModelGenericPoint.genPt W ⟨p.1, c p.1⟩ * b = a := by
  classical
  set w := ModelGenericPoint.genPt W
  set u : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩ with hu_def
  set χ : O →+* FractionRing (NumbersDVR.MRing ι (IsLocalRing.ResidueField O) ⧸ W) :=
    (algebraMap (IsLocalRing.ResidueField O) _).comp (IsLocalRing.residue O)
  set r := fun p : Σ k, ι k => w p / w ⟨p.1, c p.1⟩
  set A := chartRingOver O y c
  have hA : A = (aeval u).range := Algebra.adjoin_range_eq_range_aeval O u
  have hA' : ∀ f, aeval u f ∈ A := fun f => by rw [hA]; exact ⟨f, rfl⟩
  let ev : MvPolynomial (Σ k, ι k) O →+* A := ((aeval u).codRestrict A hA').toRingHom
  have hev : ∀ f, (ev f : Ω) = aeval u f := fun f => rfl
  have hsurj : Function.Surjective ev := by
    rintro ⟨a, ha⟩
    rw [hA] at ha
    obtain ⟨f, rfl⟩ := ha
    exact ⟨f, rfl⟩
  have hker : RingHom.ker ev ≤ RingHom.ker (eval₂Hom χ r) := by
    intro f hf
    rw [RingHom.mem_ker] at hf ⊢
    have h0 : aeval u f = 0 := by rw [← hev, hf]; rfl
    exact eval₂_ratio_eq_zero y W hW c hyc hwc h0
  have hker' : ∀ a ∈ RingHom.ker ev, eval₂Hom χ r a = 0 := fun a ha => hker ha
  let φ : A →+* FractionRing (NumbersDVR.MRing ι (IsLocalRing.ResidueField O) ⧸ W) :=
    (Ideal.Quotient.lift _ (eval₂Hom χ r) hker').comp (RingHom.quotientKerEquivOfSurjective hsurj).symm.toRingHom
  have hφ : ∀ f, φ (ev f) = eval₂ χ r f := by
    intro f
    have : (RingHom.quotientKerEquivOfSurjective hsurj).symm (ev f) = Ideal.Quotient.mk _ f := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.lift _ (eval₂Hom χ r) hker' ((RingHom.quotientKerEquivOfSurjective hsurj).symm (ev f)) = _
    rw [this, Ideal.Quotient.lift_mk, coe_eval₂Hom]
  have hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn A (RingHom.ker φ) ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts O y := ⟨c, hyc, _, hP, rfl⟩
  rw [hy.2] at hz
  obtain ⟨j, hj, q, hq, hzq⟩ := hz
  have hxj : y ⟨k₀, j ()⟩ ≠ 0 := hj ()
  set h : Ω := y ⟨k₀, j ()⟩ / y ⟨k₀, c k₀⟩ with hh
  have hh0 : h ≠ 0 := div_ne_zero hxj (hyc k₀)

  have hup : u p ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) j) q := by
    rw [← hzq]
    exact mem_locIn A _ (Algebra.subset_adjoin ⟨p, rfl⟩)
  obtain ⟨a, b, hb, hab⟩ := exists_mul_eq_of_mem_locIn (chartRingOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) j) q hup
  have hb0 : (b : Ω) ≠ 0 := fun h0 => hb (by rw [show b = 0 from Subtype.ext h0]; exact q.zero_mem)
  obtain ⟨Da, ga, hga⟩ := exists_mul_pow_eq_aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) j (c k₀) hxj a.2
  obtain ⟨Db, gb, hgb⟩ := exists_mul_pow_eq_aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) j (c k₀) hxj b.2
  set ρ : ι k₀ → Σ k, ι k := fun l => ⟨k₀, l⟩
  have hren : ∀ g : MvPolynomial (ι k₀) O, aeval u (rename ρ g) =
      aeval (fun l => IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ l / IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ (c k₀)) g := by
    intro g
    rw [aeval_rename]
    rfl
  have hφren : ∀ g : MvPolynomial (ι k₀) O, φ (ev (rename ρ g)) ∈ Algebra.adjoin (IsLocalRing.ResidueField O)
      (Set.range fun l : ι k₀ => w ⟨k₀, l⟩ / w ⟨k₀, c k₀⟩) := by
    intro g
    rw [hφ, eval₂_rename]
    exact eval₂_mem_adjoin _ g
  set Ga := rename ρ (ga * X (j ()) ^ Db)
  set Gb := rename ρ (gb * X (j ()) ^ Da)
  have hGa : (ev Ga : Ω) = a * h ^ (Da + Db) := by
    rw [hev, hren, map_mul, map_pow, aeval_X, ← hga, pow_add]
    simp only [IndefiniteRowSideFullHecke.Kleiman2.blockVec, hh]
    ring
  have hGb : (ev Gb : Ω) = b * h ^ (Da + Db) := by
    rw [hev, hren, map_mul, map_pow, aeval_X, ← hgb, pow_add]
    simp only [IndefiniteRowSideFullHecke.Kleiman2.blockVec, hh]
    ring
  refine ⟨φ (ev Ga), φ (ev Gb), hφren _, hφren _, ?_, ?_⟩
  ·
    intro h0
    have hmem : ev Gb ∈ RingHom.ker φ := h0
    have hinv : (b : Ω)⁻¹ * h⁻¹ ^ (Da + Db) ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A (RingHom.ker φ) := by
      rw [hzq]
      refine Subring.mul_mem _ (inv_mem_locIn (chartRingOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) j) q hb) (Subring.pow_mem _ (mem_locIn (chartRingOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) j) q ?_) _)
      refine Algebra.subset_adjoin ⟨⟨(), c k₀⟩, ?_⟩
      simp only [IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec, hh, inv_div]
    apply mul_ne_one_of_mem A _ hmem hinv
    rw [hGb, inv_pow, mul_mul_mul_comm, mul_inv_cancel₀ hb0, mul_inv_cancel₀ (pow_ne_zero _ hh0), one_mul]
  · have hrel : ev (X p) * ev Gb = ev Ga := by
      apply Subtype.ext
      push_cast
      rw [hGa, hGb, hev, aeval_X, ← hab]
      ring
    have := congrArg φ hrel
    rw [map_mul, hφ, eval₂_X] at this
    exact this

end Model

section Dim

theorem map_toENat_add_sub (n : Cardinal) (m : ℕ) :
    WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - m) d) (((n + m).toENat : ℕ∞) : WithBot ℕ∞) =
      WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ)) d) ((n.toENat : ℕ∞) : WithBot ℕ∞) := by
  rcases lt_or_ge n Cardinal.aleph0 with h | h
  · obtain ⟨k, rfl⟩ := Cardinal.lt_aleph0.1 h
    rw [← Nat.cast_add, Cardinal.toENat_nat, Cardinal.toENat_nat]
    show WithBot.some (WithTop.some (((k + m : ℕ) : ℤ) - m)) = WithBot.some (WithTop.some ((k : ℕ) : ℤ))
    rw [show (((k + m : ℕ) : ℤ) - m) = ((k : ℕ) : ℤ) by push_cast; ring]
  · rw [Cardinal.toENat_eq_top.2 h, Cardinal.toENat_eq_top.2 (h.trans le_self_add)]
    rfl

end Dim

theorem proof : SpecialCurvesDim.Statement := by
  intro O _ _ _ K _ _ ι _ Ω _ _ _ _ y k₀ N e hy W hW hyW
  classical
  haveI := hW.isPrime
  choose c hc using hW.relevant
  have hwc : ∀ k, ModelGenericPoint.genPt W ⟨k, c k⟩ ≠ 0 := fun k =>
    (ModelGenericPoint.genPt_ne_zero W _).2 (hc k)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h
    apply hc k
    apply hyW
    have hX : (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) O) ∈ mIdealOver O y := by
      show mConeMapOver O y (X _) = 0
      simp [mConeMapOver, h]
    have h' := Ideal.mem_map_of_mem (MvPolynomial.map (IsLocalRing.residue O)) hX
    rw [map_X] at h'
    exact h'
  set w := ModelGenericPoint.genPt W with hw_def
  set x' : Fin (N + 1) → FractionRing (NumbersDVR.MRing ι (IsLocalRing.ResidueField O) ⧸ W) :=
    IndefiniteRowSideFullHecke.Kleiman2.blockVec w k₀ ∘ e.symm
  set c' : Unit → Fin (N + 1) := fun _ => e (c k₀)
  have hxc' : ∀ k, IndefiniteRowSideFullHecke.Kleiman2.oneBlock x' ⟨k, c' k⟩ ≠ 0 := fun _ => by
    simpa [x', c', IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hwc k₀

  have hT₀ : Algebra.adjoin (IsLocalRing.ResidueField O)
      (Set.range fun l : ι k₀ => w ⟨k₀, l⟩ / w ⟨k₀, c k₀⟩) ≤
        chartRingOver (IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c' := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨l, rfl⟩
    exact Algebra.subset_adjoin ⟨⟨(), e l⟩, by simp [x', c', IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]⟩
  have hle : chartRingOver (IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c' ≤
      chartRingOver (IsLocalRing.ResidueField O) w c := by
    unfold chartRingOver
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨q, rfl⟩
    exact Algebra.subset_adjoin ⟨⟨k₀, e.symm q.2⟩, by simp [x', c', IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]⟩
  have halg : ∀ t ∈ chartRingOver (IsLocalRing.ResidueField O) w c,
      IsAlgebraic (chartRingOver (IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c') t := by
    intro t ht
    refine isAlgebraic_of_mem_adjoin _ (fun t' ht' => ?_) ht
    obtain ⟨p, rfl⟩ := ht'
    obtain ⟨a, b, ha, hb, hb0, hab⟩ := exists_ratio_eq_div y k₀ hy W hyW c hyc hwc p
    refine ⟨Polynomial.C ⟨b, hT₀ hb⟩ * Polynomial.X - Polynomial.C ⟨a, hT₀ ha⟩, fun h0 => hb0 ?_, ?_⟩
    · have h1 := congrArg (fun P => Polynomial.coeff P 1) h0
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_zero] at h1
      simpa using congrArg Subtype.val h1
    · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      show b * _ - a = 0
      rw [← hab]
      ring
  have htr := trdeg_eq_of_le_of_isAlgebraic hle halg

  have hWeq : W = mIdealOver (IsLocalRing.ResidueField O) w :=
    (ModelGenericPoint.mIdealOver_genPt W hW.multiHomog).symm
  have hW₀ : baseComap (IsLocalRing.ResidueField O) k₀ e W =
      mIdealOver (IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') := by
    have hcomp : (mConeMapOver (IsLocalRing.ResidueField O) w).comp
        (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) =
        ((rename (R := FractionRing (NumbersDVR.MRing ι (IsLocalRing.ResidueField O) ⧸ W))
          fun _ : Unit => k₀).restrictScalars (IsLocalRing.ResidueField O)).comp
          (mConeMapOver (IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')) := by
      apply MvPolynomial.algHom_ext
      intro p
      simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec, x']
    have hinj : Function.Injective (rename (R := FractionRing (NumbersDVR.MRing ι (IsLocalRing.ResidueField O) ⧸ W))
        fun _ : Unit => k₀) := rename_injective _ (fun _ _ _ => rfl)
    ext f
    rw [baseComap, Ideal.mem_comap]
    conv_lhs => rw [hWeq]
    show mConeMapOver _ w _ = 0 ↔ mConeMapOver _ (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') f = 0
    rw [← AlgHom.comp_apply, hcomp, AlgHom.comp_apply]
    exact map_eq_zero_iff _ hinj
  haveI : (mIdealOver (IsLocalRing.ResidueField O) w).IsPrime := RingHom.ker_isPrime _
  haveI : (mIdealOver (IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')).IsPrime := RingHom.ker_isPrime _
  haveI : Algebra.FiniteType (IsLocalRing.ResidueField O)
      (MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) ⧸ mIdealOver (IsLocalRing.ResidueField O) w) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ _ _) (Ideal.Quotient.mkₐ_surjective _ _)
  haveI : Algebra.FiniteType (IsLocalRing.ResidueField O)
      (MvPolynomial (Σ _ : Unit, Fin (N + 1)) (IsLocalRing.ResidueField O) ⧸
        mIdealOver (IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ _ _) (Ideal.Quotient.mkₐ_surjective _ _)
  have h1 := trdeg_quotient_mIdealOver (F := IsLocalRing.ResidueField O) w c hwc
  have h2 := trdeg_quotient_mIdealOver (F := IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c' hxc'
  rw [hW₀]
  conv_rhs => rw [hWeq]
  unfold relDim
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg (IsLocalRing.ResidueField O),
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg (IsLocalRing.ResidueField O), h1, h2, htr,
    Fintype.card_unit]
  rw [map_toENat_add_sub, map_toENat_add_sub]

end SpecialCurvesDim

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
