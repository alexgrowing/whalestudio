import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KltOfSncCoefficientsStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DiscrepancyFormulaDivisor
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FormOrderBirationalPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFunctionFieldPullbackPrimeDivisorOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverTargetBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorCentreThroughImage
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorCenterProperLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Discrepancy

private theorem isFormOrd_iff_isFormOrd_ratPull {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s]
    (hb : Function.Bijective (functionFieldMap s))
    {E' : DivOver (s ≫ p)} {E : DivOver p} (hE : DivOver.Over s E' E) {n : ℕ}
    (η : RatForms p n) (a : ℤ) :
    E.IsFormOrd η a ↔ E'.IsFormOrd (EtaleKlt.ratPull p s n η) a := by
  let ψ : E.ring →+* E'.ring :=
    ((functionFieldMap s).comp E.ring.subtype).codRestrict E'.ring (fun x => (hE x).1 x.2)
  have hψv : ∀ x : E.ring, (ψ x : Y.functionField) = functionFieldMap s x := fun x => rfl
  have hψc : ψ.comp E.const = E'.const := by
    ext c
    have := congrArg (fun f => f c) (EtaleKlt.functionFieldMap_comp_constFn p s)
    simpa [hψv, DivOver.const] using this
  have hψb : Function.Bijective ψ := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply hb.1
      have := congrArg Subtype.val hxy
      simpa [hψv] using this
    · intro y
      obtain ⟨f, hf⟩ := hb.2 y.1
      have hfm : f ∈ E.ring := (hE f).2 (hf ▸ y.2)
      exact ⟨⟨f, hfm⟩, Subtype.ext (by rw [hψv]; exact hf)⟩
  let F := TopForm.formMap n ψ hψc
  have hFb : Function.Bijective F := TopForm.bijective_formMap_of_bijective n ψ hψc hψb
  have hτ : ((functionFieldMap s).comp E.ring.subtype).comp E.const = Cartier.constFn (s ≫ p) := by
    rw [← EtaleKlt.functionFieldMap_comp_constFn p s]
    rfl
  have hrat : ∀ ω : Forms E.const n,
      E'.toRat n (F ω) = EtaleKlt.ratPull p s n (E.toRat n ω) := by
    intro ω
    exact (TopForm.formMap_formMap ψ E'.ring.subtype ((functionFieldMap s).comp E.ring.subtype)
      rfl hψc rfl hτ ω).trans
      (TopForm.formMap_formMap E.ring.subtype (functionFieldMap s)
        ((functionFieldMap s).comp E.ring.subtype) rfl rfl
        (EtaleKlt.functionFieldMap_comp_constFn p s) hτ ω).symm
  have hfree : ∀ ω : Forms E.const n,
      TopForm.IsFreeGen E.ring ω ↔ TopForm.IsFreeGen E'.ring (F ω) := by
    intro ω
    have hcomp : (fun b : E'.ring => b • F ω) ∘ ψ = F ∘ (fun a : E.ring => a • ω) := by
      funext x
      exact (LinearMap.map_smulₛₗ F x ω).symm
    unfold TopForm.IsFreeGen
    rw [← Function.Bijective.of_comp_iff _ hψb, hcomp, Function.Bijective.of_comp_iff' hFb]
  have hord := DivOver.Over.ord_fnPull_of_bijective k X Y p s hb E' E hE
  constructor
  · rintro ⟨ω, hω, f, rfl, rfl⟩
    refine ⟨F ω, (hfree ω).1 hω, fnPull s f, ?_, hord f⟩
    rw [hrat, LinearMap.map_smulₛₗ]
    rfl
  · rintro ⟨ω', hω', f', hη, hf'⟩
    obtain ⟨ω, rfl⟩ := hFb.2 ω'
    obtain ⟨c, hc⟩ := hb.2 (f' : Y.functionField)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact f'.ne_zero hc.symm
    have hff : fnPull s (Units.mk0 c hc0) = f' := Units.ext (by simpa using hc)
    refine ⟨ω, (hfree ω).2 hω', Units.mk0 c hc0, ?_, ?_⟩
    · apply (EtaleKlt.ratPull_bijective_of_birational k X Y p s hb n).1
      rw [hη, LinearMap.map_smulₛₗ, hrat, ← hff]
      rfl
    · rw [← hord, hff, hf']

theorem discrep_ratPull_fnPull {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s] (hb : Function.Bijective (functionFieldMap s))
    {E' : DivOver (s ≫ p)} {E : DivOver p} (hE : DivOver.Over s E' E) {n : ℕ} {η : RatForms p n}
    (hη : η ≠ 0) (m : ℕ) (g : X.functionFieldˣ) :
    discrep E' (EtaleKlt.ratPull p s n η) m (fnPull s g) = discrep E η m g := by
  have hη' : EtaleKlt.ratPull p s n η ≠ 0 := by
    intro h0
    apply hη
    apply (EtaleKlt.ratPull_bijective_of_birational k X Y p s hb n).1
    rw [h0, map_zero]
  have key : E'.formOrd (EtaleKlt.ratPull p s n η) = E.formOrd η := by
    unfold DivOver.formOrd
    by_cases h : ∃ a, E.IsFormOrd η a
    · have h' : ∃ a, E'.IsFormOrd (EtaleKlt.ratPull p s n η) a :=
        ⟨h.choose, (isFormOrd_iff_isFormOrd_ratPull s hb hE η _).1 h.choose_spec⟩
      rw [dif_pos h', dif_pos h]
      exact DivOver.IsFormOrd.unique hη' h'.choose_spec
        ((isFormOrd_iff_isFormOrd_ratPull s hb hE η _).1 h.choose_spec)
    · have h' : ¬ ∃ a, E'.IsFormOrd (EtaleKlt.ratPull p s n η) a :=
        fun ⟨a, ha⟩ => h ⟨a, (isFormOrd_iff_isFormOrd_ratPull s hb hE η a).2 ha⟩
      rw [dif_neg h', dif_neg h]
  unfold discrep
  rw [key, DivOver.Over.ord_fnPull_of_bijective k X Y p s hb E' E hE g]

theorem IsLogEqn.lcAt_iff {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] {p : X ⟶ Sp k} [LocallyOfFiniteType p] {n : ℕ}
    {Δ : X → ℚ} {η : RatForms p n} {x : X} {m : ℕ} {g : X.functionFieldˣ}
    (hn : topologicalKrullDim X = n) (hη : η ≠ 0) (hm : 0 < m) (h : IsLogEqn p Δ η x m g) :
    LcAt p n Δ x ↔ ∀ E : DivOver p, E.Through x → -1 ≤ discrep E η m g := by
  constructor
  · rintro ⟨η', m', g', hη', hm', h', hE⟩ E hx
    rw [discrep_eq hn hη hη' hm hm' h h' hx]
    exact hE E hx
  · intro hE
    exact ⟨η, m, g, hη, hm, h, hE⟩

private theorem toFunctionField_mem_divOver_ring {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (p : X ⟶ Sp k) (E : DivOver p) (a : k) : toFunctionField p a ∈ E.ring := by
  have : toFunctionField p a = Cartier.constFn p a := by
    simp [toFunctionField, Cartier.constFn, Cartier.fnOf, DVR.FlatBC.algX, Scheme.Hom.appLE,
      Scheme.Hom.appTop]
    rfl
  rw [this]
  exact E.const_mem a

private theorem divOver_through_of_dominatesStalk {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (E : DivOver p) {w : X} (h : DominatesStalk E.ring w) : E.Through w := by
  rintro f ⟨a, rfl⟩
  exact h.1 a

private theorem dominatesStalk_image_of_divOver_over {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s] {E' : DivOver (s ≫ p)} {E : DivOver p}
    (hE : DivOver.Over s E' E) {w : Y} (h : DominatesStalk E'.ring w) :
    DominatesStalk E.ring (s w) := by
  have hmem : ∀ a, algebraMap (X.presheaf.stalk (s w)) X.functionField a ∈ E.ring := by
    intro a
    rw [hE, functionFieldMap_algebraMap]
    exact h.1 _
  refine ⟨hmem, fun a ha => ?_⟩
  have hloc : (Scheme.Hom.stalkMap s w).hom a ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
    exact fun hu => ha (isUnit_of_map_unit _ _ hu)
  have h2 := h.2 _ hloc
  rw [← functionFieldMap_algebraMap] at h2
  rw [ValuationSubring.mem_nonunits_iff_or] at h2 ⊢
  rcases h2 with h0 | hinv
  · left
    exact (map_eq_zero_iff _ (functionFieldMap s).injective).1 h0
  · right
    intro hf
    apply hinv
    rw [← map_inv₀]
    exact (hE _).1 hf

private theorem specializes_of_through_dominatesStalk {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (p : X ⟶ Sp k) [IsSeparated p] (E : DivOver p) {x c : X} (hx : E.Through x)
    (hc : DominatesStalk E.ring c) : c ⤳ x := by
  obtain ⟨l, hl1, hl2⟩ := dominatesStalk_iff_exists_hom.1 hc
  let φ : X.presheaf.stalk x →+* E.ring :=
    (algebraMap (X.presheaf.stalk x) X.functionField).codRestrict E.ring (fun a => hx _ ⟨a, rfl⟩)
  let l' : Spec (CommRingCat.of E.ring) ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x
  have hl' : specAlgebraMap E.ring X.functionField ≫ l' = genericFieldPoint X := by
    rw [← specAlgebraMap_fromSpecStalk x, ← Category.assoc]
    congr 1
    simp only [specAlgebraMap, ← Spec.map_comp]
    congr 1
  have hp : l ≫ p = l' ≫ p := by
    obtain ⟨fa, hfa⟩ := Spec.map_surjective (l ≫ p)
    obtain ⟨fb, hfb⟩ := Spec.map_surjective (l' ≫ p)
    have h : specAlgebraMap E.ring X.functionField ≫ Spec.map fa =
        specAlgebraMap E.ring X.functionField ≫ Spec.map fb := by
      rw [hfa, hfb, ← Category.assoc, ← Category.assoc, hl1, hl']
    rw [specAlgebraMap, ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h
    rw [← hfa, ← hfb]
    congr 1
    ext a
    have := congrArg (fun ψ => ψ.hom a) h
    simpa using this
  have hsq : CommSq (genericFieldPoint X)
      (Spec.map (CommRingCat.ofHom (algebraMap E.ring X.functionField))) p (l' ≫ p) :=
    ⟨by rw [← hl', Category.assoc]⟩
  let S : ValuativeCommSq p := ⟨E.ring, X.functionField, genericFieldPoint X, l' ≫ p, hsq⟩
  have hsub := IsSeparated.valuativeCriterion p S
  let L1 : S.commSq.LiftStruct := ⟨l, hl1, hp⟩
  let L2 : S.commSq.LiftStruct := ⟨l', hl', rfl⟩
  have heq : l = l' := congrArg CommSq.LiftStruct.l (Subsingleton.elim L1 L2)
  rw [← hl2, heq]
  have hr : l' (IsLocalRing.closedPoint E.ring) ∈ Set.range (X.fromSpecStalk x) :=
    ⟨Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint E.ring), rfl⟩
  rw [Scheme.range_fromSpecStalk] at hr
  exact hr

private theorem exists_dominatesStalk_of_isProjOver {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y]
    (q : Y ⟶ Sp k) (hq : IsProjOver q) (E : DivOver q) : ∃ w, DominatesStalk E.ring w := by
  obtain ⟨N, i, hi, rfl⟩ := hq
  exact ⟨_, dominatesStalk_centre (i ≫ PSpace.str k N) E.ring
    (toFunctionField_mem_divOver_ring _ E)⟩

private theorem exists_unit_eq_smul_formOf_of_isFrame {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y]
    {q : Y ⟶ Sp k} {n : ℕ} {U : Y.Opens} (hg : genericPoint Y ∈ U) {ω : FormsOn q n U}
    (hω : IsFrame ω) (η : RatForms q n) (hη : η ≠ 0) :
    ∃ h : Y.functionFieldˣ, η = (h : Y.functionField) • formOf U hg ω := by
  obtain ⟨a, ha⟩ := (isFreeGen_formOf hg hω).2 η
  have ha' : a • formOf U hg ω = η := ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hη
    rw [← ha', zero_smul]
  exact ⟨Units.mk0 a ha0, ha'.symm⟩

private theorem discrep_eq_neg_mult_div {k : Type} [Field k] [PerfectField k]
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} [LocallyOfFiniteType q]
    {n : ℕ} (hdim : topologicalKrullDim Y = n) {E : DivOver q} {w : Y} (hE : E.IsAt w)
    {U : Y.Opens} (hw : w ∈ U) {ω : FormsOn q n U} (hω : IsFrame ω) {K P : CartierDiv Y}
    {η : RatForms q n} (hη : η ≠ 0) (hK : IsDivOfForm K η) {m : ℕ} (hm : 0 < m)
    {g : Y.functionFieldˣ} (hg : P.IsEqn w g) :
    discrep E η m g = -((P - m • K).mult w : ℚ) / m := by
  have hgen : genericPoint Y ∈ U := ((genericPoint_spec Y).mem_open_set_iff U.isOpen).2 ⟨w, trivial, hw⟩
  obtain ⟨h, hh⟩ := exists_unit_eq_smul_formOf_of_isFrame hgen hω η hη
  have hKe : K.IsEqn w h := hK U ω hω w hw h hh
  have hD : (P - m • K).IsEqn w (g / h ^ m) := hg.sub (hKe.nsmul m)
  have hf0 : formOf U hgen ω ≠ 0 := by
    intro h0
    apply hη
    rw [hh, h0, smul_zero]
  have hF : E.formOrd η = E.ord h + E.formOrd (formOf U hgen ω) := by
    rw [hh]
    exact E.formOrd_smul hdim hf0 h
  rw [DivOver.formOrd_formOf_eq_zero hw hE hω, add_zero] at hF
  rw [hD.mult_eq, ← hE.ord_eq]
  unfold discrep
  have ho : E.ord (g / h ^ m) = E.ord g - m * E.ord h := by
    rw [div_eq_mul_inv, E.ord_mul, E.ord_inv, E.ord_pow]
    ring
  rw [hF, ho]
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp
  ring

private theorem neg_one_lt_discrep_of_mult_lt_and_le {k : Type} [Field k] [CharZero k] {Y : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q]
    [LocallyOfFiniteType q] (hdim : topologicalKrullDim Y = n) (B : Closeds Y)
    (hB : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) {E : DivOver q} {w0 : Y}
    (hE : E.Through w0) {K P : CartierDiv Y} {η : RatForms q n} (hη : η ≠ 0)
    (hK : IsDivOfForm K η) {m : ℕ} (hm : 0 < m) (hsupp : (P - m • K).supp ≤ B)
    {g : Y.functionFieldˣ} (hg : P.IsEqn w0 g) :
    ((∀ w, w ⤳ w0 → (P - m • K).mult w < m) → -1 < discrep E η m g) ∧
      ((∀ w, w ⤳ w0 → (P - m • K).mult w ≤ m) → -1 ≤ discrep E η m g) := by
  obtain ⟨U, hy, z, J, w, u, hc⟩ := exists_isSncChart k Y q n B hB w0
  have hgen : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).2 ⟨w0, trivial, hy⟩
  obtain ⟨h, hh⟩ := exists_unit_eq_smul_formOf_of_isFrame hgen hc.frame η hη
  have hKe : K.IsEqn w0 h := hK U _ hc.frame w0 hy h hh
  have hD1 : (P - m • K).IsEqn w0 (g / h ^ m) := hg.sub (hKe.nsmul m)
  have hD2 := IsSncChart.isEqn_monomial k Y q n B w0 U hy z J w u hc (P - m • K) hsupp
  have hunit := (hD2.iff_unitAt).1 hD1
  have hord0 : E.ord ((g / h ^ m) / ∏ j ∈ J, u j ^ (P - m • K).mult (w j)) = 0 :=
    DivOver.ord_eq_zero_of_unitAt hE _ (by rwa [Units.val_div_eq_div_val])
  have hordg : E.ord g = m * E.ord h + ∑ j ∈ J, (P - m • K).mult (w j) * E.ord (u j) := by
    rw [div_eq_mul_inv, E.ord_mul, E.ord_inv, div_eq_mul_inv, E.ord_mul, E.ord_inv, E.ord_pow,
      E.ord_prod_zpow] at hord0
    linarith
  have hf0 : formOf U hgen (dOn q z) ≠ 0 := by
    intro h0
    apply hη
    rw [hh, h0, smul_zero]
  have hF : E.formOrd η = E.ord h + E.formOrd (formOf U hgen (dOn q z)) := by
    rw [hh]
    exact E.formOrd_smul hdim hf0 h
  have hFn : 0 ≤ E.formOrd (formOf U hgen (dOn q z)) :=
    DivOver.formOrd_formOf_nonneg hdim hy hE _ hf0
  have hFs : ∑ j ∈ J, E.ord (u j) - 1 ≤ E.formOrd (formOf U hgen (dOn q z)) := by
    have := DivOver.sum_ord_sub_one_le_formOrd_dOn hdim E hy hE z hf0 (J := J) (fun j => j.1)
      Subtype.val_injective (fun j => u j.1) (fun j => hc.val j.1 j.2)
    rwa [Finset.sum_coe_sort J (fun j => E.ord (u j))] at this
  have ho : ∀ j ∈ J, 0 ≤ E.ord (u j) := by
    intro j hj
    rw [DivOver.ord_nonneg_iff, hc.val j hj]
    exact hE _ (regAt_fnOf hy _ _)
  set F := E.formOrd (formOf U hgen (dOn q z))
  set d := fun j => (P - m • K).mult (w j)
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hdisc : discrep E η m g = (((m : ℤ) * F - ∑ j ∈ J, d j * E.ord (u j) : ℤ) : ℚ) / m := by
    unfold discrep
    rw [hF, hordg]
    push_cast
    field_simp
    ring
  have hC : ∑ j ∈ J, ((m : ℤ) - d j) * E.ord (u j) =
      (m : ℤ) * ∑ j ∈ J, E.ord (u j) - ∑ j ∈ J, d j * E.ord (u j) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hmF : (m : ℤ) * (∑ j ∈ J, E.ord (u j) - 1) ≤ (m : ℤ) * F :=
    mul_le_mul_of_nonneg_left hFs (by positivity)
  constructor
  · intro H
    have hd : ∀ j ∈ J, d j + 1 ≤ m := fun j hj => H (w j) (hc.spec j hj)
    have key : -(m : ℤ) < (m : ℤ) * F - ∑ j ∈ J, d j * E.ord (u j) := by
      by_cases hz : ∀ j ∈ J, E.ord (u j) = 0
      · have h0 : ∑ j ∈ J, d j * E.ord (u j) = 0 :=
          Finset.sum_eq_zero fun j hj => by rw [hz j hj, mul_zero]
        rw [h0]
        have : (0 : ℤ) ≤ (m : ℤ) * F := mul_nonneg (by positivity) hFn
        have : (0 : ℤ) < m := by exact_mod_cast hm
        linarith
      · push_neg at hz
        obtain ⟨j0, hj0, hne⟩ := hz
        have hpos : ∀ j ∈ J, 0 ≤ ((m : ℤ) - d j) * E.ord (u j) := fun j hj =>
          mul_nonneg (by linarith [hd j hj]) (ho j hj)
        have h1 : 1 ≤ ((m : ℤ) - d j0) * E.ord (u j0) := by
          have : 1 ≤ E.ord (u j0) := by
            have := ho j0 hj0
            omega
          have : 1 ≤ (m : ℤ) - d j0 := by linarith [hd j0 hj0]
          nlinarith
        have hS : 1 ≤ ∑ j ∈ J, ((m : ℤ) - d j) * E.ord (u j) :=
          h1.trans (Finset.single_le_sum hpos hj0)
        rw [hC] at hS
        linarith
    rw [hdisc, lt_div_iff₀ hm']
    have : ((-(m : ℤ) : ℤ) : ℚ) < (((m : ℤ) * F - ∑ j ∈ J, d j * E.ord (u j) : ℤ) : ℚ) := by
      exact_mod_cast key
    push_cast at this ⊢
    linarith
  · intro H
    have hd : ∀ j ∈ J, d j ≤ m := fun j hj => H (w j) (hc.spec j hj)
    have key : -(m : ℤ) ≤ (m : ℤ) * F - ∑ j ∈ J, d j * E.ord (u j) := by
      have hpos : ∀ j ∈ J, 0 ≤ ((m : ℤ) - d j) * E.ord (u j) := fun j hj =>
        mul_nonneg (by linarith [hd j hj]) (ho j hj)
      have hS : 0 ≤ ∑ j ∈ J, ((m : ℤ) - d j) * E.ord (u j) := Finset.sum_nonneg hpos
      rw [hC] at hS
      linarith
    rw [hdisc, le_div_iff₀ hm']
    have : ((-(m : ℤ) : ℤ) : ℚ) ≤ (((m : ℤ) * F - ∑ j ∈ J, d j * E.ord (u j) : ℤ) : ℚ) := by
      exact_mod_cast key
    push_cast at this ⊢
    linarith

theorem kltAt_lcAt_iff_of_isLogRes : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → ∀ x : X, (KltAt p n Δ x ↔ ∀ w : Y, s w ⤳ x → (pullCart s G - m • K).mult w < m) ∧ (LcAt p n Δ x ↔ ∀ w : Y, s w ⤳ x → (pullCart s G - m • K).mult w ≤ m) := by
  intro k _ _ X _ _ _ p n hproj hn Δ η m G Y _ _ s _ K B hlm hres x
  obtain ⟨N, i, hi, hpi⟩ := hproj
  haveI : IsSeparated p := hpi ▸ inferInstance
  haveI : LocallyOfFiniteType p := hpi ▸ inferInstance
  haveI := hres.smooth
  haveI : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth n _
  haveI : LocallyOfFiniteType (s ≫ p) := inferInstance
  haveI : IsNormalScheme Y := ModifSections.isNormalScheme_of_smooth (s ≫ p)
  have hdimY : topologicalKrullDim Y = n :=
    HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (s ≫ p) n hres.smooth
  have hη' : EtaleKlt.ratPull p s n η ≠ 0 := by
    intro h0
    apply hlm.ne_zero
    apply (EtaleKlt.ratPull_bijective_of_birational k X Y p s hres.bir n).1
    rw [h0, map_zero]
  obtain ⟨g, hg⟩ := G.exists_isEqn x
  have hL := hlm.eqn x g hg
  have hm' : (0 : ℚ) < m := by exact_mod_cast hlm.pos
  have hlow : ∀ E : DivOver p, E.Through x → ∃ w0 : Y, s w0 ⤳ x ∧
      ∃ (E' : DivOver (s ≫ p)) (g0 : Y.functionFieldˣ), E'.Through w0 ∧
        (pullCart s G).IsEqn w0 g0 ∧
        discrep E η m g = discrep E' (EtaleKlt.ratPull p s n η) m g0 := by
    intro E hEx
    obtain ⟨E', hE'⟩ := DivOver.exists_over k X Y p s hres.bir E
    obtain ⟨w0, hw0⟩ := exists_dominatesStalk_of_isProjOver (s ≫ p) hres.proj E'
    have hsw := specializes_of_through_dominatesStalk p E hEx (dominatesStalk_image_of_divOver_over s hE' hw0)
    obtain ⟨g0, hg0⟩ := G.exists_isEqn (s w0)
    have hL0 := hlm.eqn _ g0 hg0
    have hLx : IsLogEqn p Δ η (s w0) m g := fun z hz => hL z (hz.trans hsw)
    have hEs : E.Through (s w0) :=
      DivOver.Over.through_image k X Y p s E' E hE' w0 (divOver_through_of_dominatesStalk E' hw0)
    refine ⟨w0, hsw, E', fnPull s g0, divOver_through_of_dominatesStalk E' hw0,
      (GlobalTheory.Cartier.exists_pullback_cartierDiv X Y s G).choose_spec.2 w0 g0 hg0, ?_⟩
    rw [discrep_eq hn hlm.ne_zero hlm.ne_zero hlm.pos hlm.pos hLx hL0 hEs,
      discrep_ratPull_fnPull s hres.bir hE' hlm.ne_zero m g0]
  have hup : ∀ w : Y, s w ⤳ x → (pullCart s G - m • K).mult w ≠ 0 →
      ∃ E : DivOver p, E.Through x ∧
        discrep E η m g = -((pullCart s G - m • K).mult w : ℚ) / m := by
    intro w hw hne
    have hcoh := CartierDiv.coheight_eq_one_of_mult_ne_zero hne
    obtain ⟨E', hE'⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := s ≫ p) hcoh
    obtain ⟨E, hEo⟩ := DivOver.exists_over_of_bijective k X Y p s hres.bir E'
    have hEs : E.Through (s w) :=
      DivOver.Over.through_image k X Y p s E' E hEo w (hE'.through (specializes_refl w))
    obtain ⟨g1, hg1⟩ := G.exists_isEqn (s w)
    have hL1 := hlm.eqn _ g1 hg1
    have hLx : IsLogEqn p Δ η (s w) m g := fun z hz => hL z (hz.trans hw)
    obtain ⟨U, hy, z, J, w', u, hc⟩ := exists_isSncChart k Y (s ≫ p) n B hres.snc w
    refine ⟨E, hEs.of_specializes hw, ?_⟩
    rw [discrep_eq hn hlm.ne_zero hlm.ne_zero hlm.pos hlm.pos hLx hL1 hEs,
      ← discrep_ratPull_fnPull s hres.bir hEo hlm.ne_zero m g1]
    exact discrep_eq_neg_mult_div hdimY hE' hy hc.frame hη' hres.div hlm.pos
      ((GlobalTheory.Cartier.exists_pullback_cartierDiv X Y s G).choose_spec.2 w g1 hg1)
  constructor
  · rw [IsLogEqn.kltAt_iff hn hlm.ne_zero hlm.pos hL]
    constructor
    · intro H w hw
      by_contra hlt
      push_neg at hlt
      have hne : (pullCart s G - m • K).mult w ≠ 0 := by
        have : (0 : ℤ) < m := by exact_mod_cast hlm.pos
        omega
      obtain ⟨E, hEx, hd⟩ := hup w hw hne
      have h1 := H E hEx
      rw [hd] at h1
      have hM : (m : ℚ) ≤ ((pullCart s G - m • K).mult w : ℚ) := by exact_mod_cast hlt
      rw [neg_div, neg_lt_neg_iff, div_lt_one hm'] at h1
      linarith
    · intro H E hEx
      obtain ⟨w0, hsw, E', g0, hE't, hg0, hd⟩ := hlow E hEx
      rw [hd]
      exact (neg_one_lt_discrep_of_mult_lt_and_le (s ≫ p) n hdimY B hres.snc hE't hη' hres.div hlm.pos
        hres.supp hg0).1 (fun w hw => H w ((hw.map s.continuous).trans hsw))
  · rw [IsLogEqn.lcAt_iff hn hlm.ne_zero hlm.pos hL]
    constructor
    · intro H w hw
      by_contra hlt
      push_neg at hlt
      have hne : (pullCart s G - m • K).mult w ≠ 0 := by
        have : (0 : ℤ) < m := by exact_mod_cast hlm.pos
        omega
      obtain ⟨E, hEx, hd⟩ := hup w hw hne
      have h1 := H E hEx
      rw [hd] at h1
      have hM : (m : ℚ) < ((pullCart s G - m • K).mult w : ℚ) := by exact_mod_cast hlt
      rw [neg_div, neg_le_neg_iff, div_le_one hm'] at h1
      linarith
    · intro H E hEx
      obtain ⟨w0, hsw, E', g0, hE't, hg0, hd⟩ := hlow E hEx
      rw [hd]
      exact (neg_one_lt_discrep_of_mult_lt_and_le (s ≫ p) n hdimY B hres.snc hE't hη' hres.div hlm.pos
        hres.supp hg0).2 (fun w hw => H w ((hw.map s.continuous).trans hsw))

end GlobalTheory.Discrepancy
