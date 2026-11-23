import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInjectiveModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompIncAAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAtTypeAndOrd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponen
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPatternStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFramePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasisStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReductionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesMemCompletedHermitianLaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLattiStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.PinEx
open GlobalTheory.FinPl (SplitPt latV idAt intAt grpAt MxAt)
open Formalism.L2.NTheta (IsIdemAt)
open Formalism.L2.Col (IntAt)

section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem sec_one : q.sec 1 = q.e := by
  have := q.sec_pr 1
  rwa [map_one, mul_one] at this

theorem pr_e : q.pr q.e = 1 := by rw [← sec_one, q.pr_sec]

theorem pr_e_mul (x : AE D) : q.pr (q.e * x) = q.pr x := by rw [map_mul, pr_e, one_mul]

theorem idAt_mono {P P' : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, P v → P' v) : idAt D P ≤ idAt D P' :=
  inf_le_inf_left _ (le_iInf fun w => iInf_le_of_le ⟨w.1, fun hw => w.2 (h _ hw)⟩ le_rfl)

theorem add_mul_e : (q.e + cA D q.e) * q.e = q.e := by
  obtain ⟨h1, h2, -⟩ := q.split
  rw [add_mul, h1, mul_comm (cA D q.e), h2, add_zero]

theorem mem_idAt_of_supp {a : AE D} (h : (q.e + cA D q.e) * a = a) : a ∈ idAt D (· = q.v) := by
  obtain ⟨ε, hε, hs⟩ := q.above
  exact ((GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D q.v ε hε).1 a).2 (hs ▸ h)

theorem place_facts {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) :
    q.v = PP.under (𝓞 D.host.F) ∧ (∀ a, (ofSplit q).pr a ∈ 𝒪[k] ↔ IntAt PP a) ∧ DenseRange (ofSplit q).pr := by
  obtain ⟨k₀, _, _, _, _, q₀, he, hv, hi, hd⟩ := GlobalTheory.LocMod.SplitCompl.exists_place D PP q.e h
  refine ⟨?_, fun a => ?_, ?_⟩
  · rw [← hv]
    by_contra hne
    obtain ⟨ε, hε, hs⟩ := q₀.above
    have h0 := (GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D q₀.v ε hε).2 q.e
      (idAt_mono (fun v (hv : v = q.v) => hv ▸ hne) (GlobalTheory.FrameGlob.e_mem_idAt q))
    rw [← hs, he, add_mul_e] at h0
    have := pr_e q
    rw [h0, map_zero] at this
    exact zero_ne_one this
  · rw [← hi, q.int_iff, q₀.int_iff]
    change finPart D (q.sec (q.pr _)) ∈ _ ↔ finPart D (q₀.sec (q₀.pr _)) ∈ _
    rw [q.sec_pr, q₀.sec_pr, he]
  · have hs : Function.Surjective (fun x => q.pr (q₀.sec x)) := fun y =>
      ⟨q₀.pr (q.sec y), by simp only [q₀.sec_pr, he, pr_e_mul, q.pr_sec]⟩
    have := hs.denseRange.comp hd (q.cont_pr.comp q₀.cont_sec)
    convert this using 1
    funext a
    change q.pr _ = q.pr (q₀.sec (q₀.pr _))
    rw [q₀.sec_pr, he, pr_e_mul]

def prO : 𝓞 D.host.E →+* k := (q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem prO_apply (z : 𝓞 D.host.E) : prO q z = (ofSplit q).pr (z : D.host.E) := rfl

theorem prO_le {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) (z : 𝓞 D.host.E) : valuation k (prO q z) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (((place_facts q h).2.1 _).2
    ⟨z, 1, (Ideal.ne_top_iff_one _).1 PP.isPrime.ne_top, by simp⟩)

theorem prO_lt {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) (z : 𝓞 D.host.E) :
    z ∈ PP.asIdeal ↔ valuation k (prO q z) < 1 := by
  by_cases hz : z = 0
  · subst hz; simp
  have h0 : prO q z ≠ 0 := (map_ne_zero (q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 hz)
  rw [h.2 z hz, ← q.sec_pr, ← q.int_iff]
  change (q.pr.comp (incA D)) _ ∉ _ ↔ _
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le]
  exact one_lt_inv₀ (a := valuation k (prO q z)) (zero_lt_iff.2 ((map_ne_zero _).2 h0))

theorem prO_eq_one {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) {z : 𝓞 D.host.E} (hz : z ∉ PP.asIdeal) :
    valuation k (prO q z) = 1 := le_antisymm (prO_le q h z) (not_lt.1 (mt (prO_lt q h z).2 hz))

theorem xi_unit (hu : q.UnitAA) (h0 : (ofSplit q).xi ≠ 0) : valuation k (ofSplit q).xi = 1 := by
  have he : q.e ∈ intAt D (· = q.v) := ⟨GlobalTheory.FrameGlob.e_mem_idAt q, by rw [← sec_one]; exact (q.int_iff 1).1 (one_mem _)⟩
  obtain ⟨h1, h2⟩ := hu.1 q.e he
  have h3 := h1.2
  have h4 := h2.2
  rw [mul_comm, ← q.sec_pr, ← q.int_iff, Valuation.mem_integer_iff] at h3 h4
  change valuation k ((q.pr.comp (incA D)) _) ≤ 1 at h4
  rw [map_inv₀, map_inv₀] at h4
  exact le_antisymm h3 ((inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))).1 h4)

theorem sec_mul (x y : k) : q.sec x * q.sec y = q.sec (x * y) := by
  have h := q.sec_pr (q.sec x * q.sec y)
  rw [map_mul, q.pr_sec, q.pr_sec, ← mul_assoc, ← GlobalTheory.FrameGlob.sec_eq_mul] at h
  exact h.symm

theorem idl_mul (x y : k) (h : x * y = 1) : (q.sec x + (1 - q.e)) * (q.sec y + (1 - q.e)) = 1 := by
  have h1 := sec_mul q x y
  rw [h, sec_one] at h1
  have h2 := GlobalTheory.FrameGlob.sec_eq_mul q x
  have h3 := GlobalTheory.FrameGlob.sec_eq_mul q y
  have h4 := q.split.1
  linear_combination h1 + h2 + h3 + h4

def idl (x : kˣ) : (AE D)ˣ :=
  ⟨q.sec x + (1 - q.e), q.sec (x⁻¹ : kˣ) + (1 - q.e), idl_mul q _ _ x.mul_inv, idl_mul q _ _ x.inv_mul⟩

theorem continuous_idl : Continuous (idl q) :=
  Units.continuous_iff.2 ⟨(q.cont_sec.comp Units.continuous_val).add continuous_const,
    (q.cont_sec.comp Units.continuous_coe_inv).add continuous_const⟩

theorem unram_idl {χ : (AE D)ˣ →* Circle} (hχ : UnramEverywhere D χ) (x : kˣ) (hx : valuation k (x : k) = 1) : χ (idl q x) = 1 := by
  have one : finPart D 1 ∈ intAE D := by
    rw [map_one]
    exact AddSubgroup.subset_closure ⟨1, fun v => by simp, 1, rfl⟩
  have key : ∀ y : k, valuation k y ≤ 1 → finPart D (q.sec y + (1 - q.e)) ∈ intAE D := fun y hy => by
    rw [RingHom.map_add, RingHom.map_sub, ← sec_one]
    exact add_mem ((q.int_iff y).1 hy) (sub_mem one ((q.int_iff 1).1 (one_mem _)))
  refine hχ _ ?_ (key _ hx.le) (key _ (by simp [hx]))
  have h1 : infPart D (q.sec x) = 0 := (GlobalTheory.FrameGlob.sec_mem_idAt q x).1
  have h2 : infPart D q.e = 0 := (GlobalTheory.FrameGlob.e_mem_idAt q).1
  change infPart D (q.sec x + (1 - q.e)) = 1
  rw [RingHom.map_add, RingHom.map_sub, h1, h2, RingHom.map_one, zero_add, sub_zero]

theorem res_idl {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) {χ : (AE D)ˣ →* Circle} {H : Formalism.L2.Host.HChar D.host.E}
    {c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} (hχ : Formalism.IndefR.Links.ChrEq χ H) (hr : Formalism.IndefR.Links.IsRes H PP c) (x : kˣ)
    (hx : valuation k ((x : k) - 1) < 1) : χ (idl q x) = 1 := by
  obtain ⟨-, hi, hd⟩ := place_facts q h
  have rat : ∀ (a : D.host.E) (y : kˣ), (y : k) = (ofSplit q).pr a → valuation k ((y : k) - 1) < 1 → χ (idl q y) = 1 := by
    intro a y hy hy1
    have hv : valuation k (y : k) = 1 := by simpa using Valuation.map_one_add_of_lt (valuation k) hy1
    obtain ⟨r, s, hs, e⟩ := (hi a).1 (by rw [← hy, Valuation.mem_integer_iff, hv])
    have e' : prO q s * y = prO q r := by
      rw [hy]
      exact ((q.pr.comp (incA D)).map_mul _ _).symm.trans (congrArg (q.pr.comp (incA D)) e)
    have hrs : r - s ∈ PP.asIdeal := by
      rw [prO_lt q h, map_sub, ← e', ← mul_sub_one, map_mul, prO_eq_one q h hs, one_mul]
      exact hy1
    have hs0 : (s : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 (by rintro rfl; exact hs (zero_mem _))
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact y.ne_zero (hy.trans (q.pr.comp (incA D)).map_zero)
    haveI := PP.isMaximal
    letI := Ideal.Quotient.field PP.asIdeal
    have hu : Ideal.Quotient.mk PP.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have h1 := hr s (Units.mk0 _ hs0) (Units.mk0 _ hu) rfl rfl
    have h2 := hr r (Units.mk0 _ hs0 * Units.mk0 _ ha0) (Units.mk0 _ hu) e (Ideal.Quotient.eq.2 hrs).symm
    rw [map_mul, ← h1, left_eq_mul] at h2
    have h3 := hχ.2 PP q.e ⟨h.1.1, by
      obtain ⟨ε, hε, hs⟩ := q.above
      exact ⟨q.v, ε, hε, Or.inl ⟨h.1.2.1, hs⟩⟩, h.2⟩ (Units.mk0 _ ha0) (idl q y) (by
        change q.sec y + (1 - q.e) = 1 + q.e * (incA D a - 1)
        rw [hy]
        change q.sec (q.pr _) + _ = _
        rw [q.sec_pr]
        ring)
    rw [h2] at h3
    exact Circle.coe_injective h3
  by_contra hne
  have hc : Continuous fun y => χ (idl q y) := hχ.1.1.comp (continuous_idl q)
  have h1 : {y : kˣ | χ (idl q y) ≠ 1} ∈ nhds x := (isOpen_ne_fun hc continuous_const).mem_nhds hne
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at h1
  obtain ⟨W, hW, hW'⟩ := h1
  have h2 : {y : k | valuation k (y - x) < 1} ∈ nhds (x : k) := by
    rw [IsValuativeTopology.mem_nhds_iff']
    exact ⟨1, by simp⟩
  obtain ⟨a, ha1, ha2, ha3⟩ := hd.mem_nhds (Filter.inter_mem hW (Filter.inter_mem h2 (isOpen_ne.mem_nhds x.ne_zero)))
  refine hW' (a := Units.mk0 _ ha3) ha1 (rat a _ rfl ?_)
  have := Valuation.map_add_lt (valuation k) ha2 hx
  simpa using this

theorem tame_comp {c : GlobalTheory.ChainOnto.Com D} (hc : c.Is) {PP : Formalism.L2.DIV.Pl D.host.E} (hP : PP ∈ c.Pg) (h : IsIdemAt q.e PP)
    {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {μ : kˣ →* ℂˣ} (hμ : (ofSplit q).IsComp (c.chS j)⁻¹ μ) : IsTame μ := by
  intro x hx
  have hv : valuation k (x : k) = 1 := by simpa using Valuation.map_one_add_of_lt (valuation k) hx
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  obtain ⟨H, hH, hr⟩ := hc.res ⟨i, h2⟩
  have e1 := res_idl q h hH (hr PP hP) x hx
  have e2 := unram_idl q hc.chars.2.1 x hv
  have e3 : c.chS (i + 1) (idl q x) = 1 := by
    unfold GlobalTheory.ChainOnto.Com.chS Formalism.IndefR.Lift.chrStep
    split_ifs
    · change c.μ (i + 1) (idl q x) * (c.η (idl q x))⁻¹ = 1
      rw [e2, inv_one, mul_one]
      exact e1
    · exact e1
  refine Units.ext ((hμ x (idl q x) rfl).trans ?_)
  rw [MonoidHom.inv_apply, e3]
  simp

theorem exists_unif {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {ψ₀ : AddChar (Formalism.L2.DIV.kP PP) ℂ} (h₀ : ψ₀ ≠ 1) : ∃ ϖ : kˣ, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ ∧
      ∀ z : 𝓞 D.host.E, (ψ (((ϖ⁻¹ : kˣ) : k) * prO q z) : ℂ) = ψ₀ (Ideal.Quotient.mk _ z) := by
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (uniformizer k)
  have t0 : t ≠ 0 := by
    rintro rfl
    exact (uniformizer_pos (R := k)).ne (by simpa using ht)
  have hu : ∀ x : k, valuation k x < 1 ↔ valuation k x ≤ valuation k t := fun x => by rw [ht, le_uniformizer_iff]
  have tp : 0 < valuation k t := zero_lt_iff.2 ((map_ne_zero _).2 t0)
  have triv : ∀ y : k, valuation k y < 1 → ψ (t⁻¹ * y) = 1 := fun y hy =>
    (hψ 1).2 (by simp) _ (by
      rw [map_mul, map_inv₀, map_one, inv_mul_le_one₀ tp]
      exact (hu y).1 hy)
  have near : ∀ y y' : k, valuation k (y - y') < 1 → ψ (t⁻¹ * y) = ψ (t⁻¹ * y') := fun y y' hy => by
    rw [show t⁻¹ * y = t⁻¹ * (y - y') + t⁻¹ * y' by ring, AddChar.map_add_eq_mul, triv _ hy, one_mul]
  have wd : ∀ z z' : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = Ideal.Quotient.mk PP.asIdeal z' →
      ψ (t⁻¹ * prO q z) = ψ (t⁻¹ * prO q z') := fun z z' e =>
    near _ _ (by rw [← map_sub, ← prO_lt q h]; exact Ideal.Quotient.eq.1 e)
  choose l hl using Ideal.Quotient.mk_surjective (I := PP.asIdeal)
  let α : AddChar (Formalism.L2.DIV.kP PP) ℂ :=
    { toFun := fun u => ψ (t⁻¹ * prO q (l u))
      map_zero_eq_one' := by rw [wd _ 0 (by rw [hl, map_zero])]; simp
      map_add_eq_mul' := fun a b => by
        rw [wd _ (l a + l b) (by rw [map_add, hl, hl, hl]), map_add, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul] }
  have hα : ∀ z, α (Ideal.Quotient.mk _ z) = ψ (t⁻¹ * prO q z) := fun z => congrArg (fun c : Circle => (c : ℂ)) (wd _ z (hl _))
  haveI := PP.isMaximal
  letI := Ideal.Quotient.field PP.asIdeal
  haveI : Finite (𝓞 D.host.E ⧸ PP.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
  have hα1 : α ≠ 1 := by
    intro e
    obtain ⟨-, hi, hd⟩ := place_facts q h
    obtain ⟨r, -, hr0, hr⟩ := GlobalTheory.SymTieExists.exists_residue PP (q.pr.comp (incA D)) hi hd
    have h1 := (hψ t⁻¹).1 fun y hy => by
      have hy' : valuation k (t * y) ≤ 1 := by
        rw [map_mul]
        rw [map_inv₀] at hy
        exact (mul_le_mul_right hy _).trans (mul_inv_cancel₀ tp.ne').le
      let z := l (r ⟨_, hy'⟩)
      have hz : r ⟨prO q z, prO_le q h z⟩ = Ideal.Quotient.mk _ z := by
        obtain ⟨r', s, hs, e1, e2⟩ := GlobalTheory.SymTieExists.reduction_spec PP ((hi z).1 (prO_le q h z))
        have e3 : s * z = r' := IsFractionRing.injective (𝓞 D.host.E) D.host.E (by rw [map_mul]; exact e1)
        refine (hr _ _).trans (mul_left_cancel₀ (a := Ideal.Quotient.mk PP.asIdeal s)
          (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]) ?_)
        rw [e2, ← map_mul, e3]
      have h2 := (hr0 (⟨_, hy'⟩ - ⟨prO q z, prO_le q h z⟩)).1 (by rw [map_sub, hz, hl, sub_self])
      have h3 := near _ _ h2
      rw [inv_mul_cancel_left₀ t0] at h3
      have h4 := hα z
      rw [e, ← h3] at h4
      exact Circle.coe_injective h4.symm
    rw [map_inv₀, Units.val_one, map_one, inv_le_one₀ tp] at h1
    exact absurd ((hu t).2 le_rfl) (not_lt.2 h1)
  letI := Fintype.ofFinite (𝓞 D.host.E ⧸ PP.asIdeal)
  have hb : Function.Bijective α.mulShift :=
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hα1), AddChar.card_eq.symm⟩
  obtain ⟨c, rfl⟩ := hb.2 ψ₀
  have hw : l c ∉ PP.asIdeal := fun hw => h₀ (by
    rw [← hl c, Ideal.Quotient.eq_zero_iff_mem.2 hw, AddChar.mulShift_zero])
  have hw1 := prO_eq_one q h hw
  have hw0 : prO q (l c) ≠ 0 := fun e => by simp [e] at hw1
  refine ⟨Units.mk0 t t0 * (Units.mk0 _ hw0)⁻¹, fun x => ?_, fun z => ?_⟩
  · simpa [hw1] using hu x
  · rw [AddChar.mulShift_apply, show c * Ideal.Quotient.mk _ z = Ideal.Quotient.mk _ (l c * z) by rw [map_mul, hl], hα, (prO q).map_mul]
    refine congrArg (fun c => (ψ c : ℂ)) ?_
    simp
    ring

theorem exists_latFrame (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (hL : IsSelfDualC S L) (Y : Type) [Fintype Y] [DecidableEq Y]
    (e : Y ≃ Fin S.rank) : ∃ F : GlobalTheory.LocMod.Frame k S.rank Y, ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔
      (fun i => q.sec ((F.β *ᵥ y) i)) ∈ latV S L (· = q.v) := by
  obtain ⟨gl, h1, h2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D k q S (Fin S.rank) 1 1 (mul_one _) (mul_one _)
  obtain ⟨Λ, hΛ, hl, -⟩ := (GlobalTheory.T.splitPlaceHermitianFrame_properties D k q S _ ⟨1, 1, mul_one _, mul_one _, gl, h1, h2⟩).2.2.2.1 L hL
  let b := (Module.finBasisOfFinrankEq 𝒪[k] Λ (Submodule.IsLattice.finrank_of_pi k Λ)).reindex
    ((finCongr (Fintype.card_fin _)).trans e.symm)
  let b' := b.extendOfIsLattice k
  have hkey : ∀ c : Y → 𝒪[k], b'.equivFun.symm (fun i => (c i : k)) = ((∑ i, c i • b i : Λ) : _ → k) := by
    intro c
    rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.Basis.extendOfIsLattice_apply]
    rfl
  refine ⟨⟨LinearMap.toMatrix' b'.equivFun.symm.toLinearMap, LinearMap.toMatrix' b'.equivFun.toLinearMap, ?_, ?_⟩, fun y => ?_⟩
  · rw [← LinearMap.toMatrix'_comp]; simp
  · rw [← LinearMap.toMatrix'_comp]; simp
  have h3 := hl (b'.equivFun.symm y)
  simp only [one_mulVec] at h3
  simp only [LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]
  rw [← h3]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 : b'.equivFun.symm y = _ := hkey fun i => ⟨y i, h i⟩
    rw [h2]
    exact Subtype.property _
  · have h1 := hkey (b.repr ⟨_, h⟩)
    rw [b.sum_repr] at h1
    rw [← b'.equivFun.symm.injective h1]
    exact fun i => (b.repr ⟨_, h⟩ i).2

theorem exists_topFrame {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) (S : HSp D) (L : GlobalTheory.FinPl.Lat S)
    (β : GL (Fin S.rank) (Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β L) : ∃ B : GL (Fin S.rank) k, MovedTo (ofSplit q) S 1 β B.val ∧
      ∀ y : Fin S.rank → k, (fun i => q.sec (y i)) ∈ latV S L (· = q.v) ↔ ∀ i, ((B⁻¹).val *ᵥ y) i ∈ 𝒪[k] := by
  obtain ⟨π, h1, -, h2, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D k q PP h
  refine ⟨Matrix.GeneralLinearGroup.map π β, fun b hb => ?_, fun y => ?_⟩
  · ext i j
    change q.pr (((matHom S 1).val * b) i j) = π (β.val i j)
    rw [map_one, Units.val_one, Matrix.one_mul, ← hb, ← h1]
    rfl
  have h3 : (fun i => q.sec (y i)) ∈ latV S L (· = q.v) ↔ (fun i => toEAf D (q.sec (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L :=
    ⟨GlobalTheory.T.latticeCompletionAtPlaces_mem_completedHermitianLattice D S L _ _, GlobalTheory.T.mem_latticeCompletionAtPlaces_of_finPart_mem_hatLattice D S L _ _ fun i => GlobalTheory.FrameGlob.sec_mem_idAt q _⟩
  rw [h3, hβ]
  refine forall_congr' fun i => ?_
  have h4 : ∀ j, (1 - toEAf D q.e) * toEAf D (q.sec (y j)) = 0 := fun j => by
    rw [sub_mul, one_mul, ← map_mul, ← GlobalTheory.FrameGlob.sec_eq_mul, sub_self]
  rw [h2, ← map_inv]
  simp only [mulVec, dotProduct, Finset.mul_sum, mul_left_comm (1 - toEAf D q.e), h4, mul_zero, Finset.sum_const_zero, zero_mem,
    true_and, map_sum, map_mul, h1, q.pr_sec]
  rfl

end Place
end GlobalTheory.LocMod.PinEx

namespace GlobalTheory.LocMod.PinEx
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum Formalism.L2.DIV Formalism.IndefR.Links

section Sym
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ r : ℕ}

def Edge {l : ℕ} : Fin κ ⊕ Fin l → Fin κ ⊕ Fin l → Prop
  | .inl i, .inl j => j.val = i.val + 1
  | .inr i, .inr j => j.val = i.val + 1
  | _, _ => False

theorem sym_order {ρ : ℕ} (hρ : s + 1 = 2 * ρ + 1) (e : Fin κ ⊕ Fin (s + 1) ≃ Fin r) (he : ∀ a, (e a).val = framePos _ _ a)
    {π : Equiv.Perm (Fin r)} (hπ : IsSymOrd ρ κ π) (a b : Fin κ ⊕ Fin (s + 1)) :
    (¬ FreeTop ρ a b ↔ (π.symm (e b)).val ≤ (π.symm (e a)).val ∨
      (ρ ≤ (π.symm (e a)).val ∧ (π.symm (e a)).val < ρ + κ ∧ (π.symm (e b)).val = ρ + κ)) ∧
    (symEdge ρ κ (π.symm (e a)) (π.symm (e b)) ↔ Edge a b) := by
  have ha := hπ (π.symm (e a))
  have hb := hπ (π.symm (e b))
  rw [Equiv.apply_symm_apply, he] at ha hb
  unfold symEdge
  generalize (π.symm (e a)).val = x at ha ⊢
  generalize (π.symm (e b)).val = y at hb ⊢
  rcases a with ⟨a, h1⟩ | ⟨a, h1⟩ <;> rcases b with ⟨b, h2⟩ | ⟨b, h2⟩ <;>
    simp only [framePos, Sum.elim_inl, Sum.elim_inr, FreeTop, Edge, Fin.lt_def] at ha hb ⊢ <;>
    split_ifs at ha hb <;> (try simp only [iff_false]) <;> omega

theorem mem_unipSym {F : Type} [CommRing F] {ρ : ℕ} (g : GL (Fin r) F) : g ∈ unipSym F r ρ κ ↔
    ∀ i j : Fin r, (j.val ≤ i.val ∨ (ρ ≤ i.val ∧ i.val < ρ + κ ∧ j.val = ρ + κ)) → g.val i j = (1 : Matrix _ _ F) i j := by
  constructor
  · rintro ⟨h1, h2⟩ i j (h | ⟨h3, h4, h5⟩)
    · rcases h.lt_or_eq with h | h
      · rw [unip_lower h1 h, one_apply_ne (fun e => by rw [e] at h; omega)]
      · obtain rfl := Fin.ext h
        rw [unip_diag h1, one_apply_eq]
    · rw [h2 i j h3 h4 h5, one_apply_ne (fun e => by rw [e] at h4; omega)]
  · intro h
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j h3 h4 h5 => ?_⟩
    · rw [h i j (Or.inl (le_of_lt hij)), one_apply_ne (fun e => by rw [e] at hij; exact lt_irrefl _ hij)]
    · rw [h i i (Or.inl le_rfl), one_apply_eq]
    · rw [h i j (Or.inr ⟨h3, h4, h5⟩), one_apply_ne (fun e => by rw [e] at h4; omega)]

variable (S : SymData k s κ) {O : Type} [CommRing O] {I : Ideal O} (pr : O →+* k)
  (h1 : ∀ z, valuation k (pr z) ≤ 1) (h2 : ∀ z, z ∈ I ↔ valuation k (pr z) < 1)
  (e : Fin κ ⊕ Fin (s + 1) ≃ Fin r) (he : ∀ a, (e a).val = framePos _ _ a) {π : Equiv.Perm (Fin r)} (hπ : IsSymOrd S.ρ κ π)
  (g g' : GL (Fin r) (O ⧸ I)) (hg : ∀ i j, g'.val i j = g.val (π i) (π j))

include h1 h2 he hπ hg in

theorem sym_grp : (∃ x : S.P.J, ∀ a b z, Ideal.Quotient.mk I z = g.val (e a) (e b) →
    valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val a b - pr z) < 1) ↔ g' ∈ unipSym (O ⧸ I) r S.ρ κ := by
  choose l hl using Ideal.Quotient.mk_surjective (I := I)
  have one : ∀ a b, (1 : Matrix _ _ k) a b = pr ((1 : Matrix _ _ O) a b) ∧
      (1 : Matrix _ _ (O ⧸ I)) (π.symm (e a)) (π.symm (e b)) = Ideal.Quotient.mk I ((1 : Matrix _ _ O) a b) := fun a b => by
    by_cases h : a = b <;> simp [one_apply, h]
  rw [mem_unipSym]
  constructor
  · rintro ⟨x, hx⟩ i j hij
    obtain ⟨a, rfl⟩ := (e.trans π.symm).surjective i
    obtain ⟨b, rfl⟩ := (e.trans π.symm).surjective j
    have h3 := ((GlobalTheory.T.mem_level_iff_symmetricPosition_entry_pattern k s κ S x).1 x.2).2 a b ((sym_order S.odd e he hπ a b).1.2 hij)
    have h4 := Valuation.map_sub_lt _ h3 (hx a b _ (hl _))
    rw [(one a b).1, sub_sub_sub_cancel_left, ← map_sub, ← h2, ← Ideal.Quotient.eq, hl] at h4
    refine (hg _ _).trans (Eq.trans ?_ (one a b).2.symm)
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    exact h4
  · intro h
    let Z : Matrix (Fin κ ⊕ Fin (s + 1)) (Fin κ ⊕ Fin (s + 1)) O := fun a b => l (g.val (e a) (e b))
    let p : O →+* 𝒪[k] := pr.codRestrict _ h1
    have hd : IsUnit (p.mapMatrix Z).det := by
      by_contra hn
      have h3 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hn
      rw [← RingHom.map_det] at h3
      have h4 := Ideal.Quotient.eq_zero_iff_mem.2 ((h2 _).2 h3)
      have h5 : (Ideal.Quotient.mk I).mapMatrix Z = g.val.submatrix e e := Matrix.ext fun a b => hl _
      rw [RingHom.map_det, h5, det_submatrix_equiv_self] at h4
      have h6 := (g.det).isUnit
      rw [GeneralLinearGroup.val_det_apply, h4, isUnit_zero_iff] at h6
      have h7 := (h2 1).1 (Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_one, ← h6]))
      simp at h7
    let x₀ : GL (Fin κ ⊕ Fin (s + 1)) 𝒪[k] := ((isUnit_iff_isUnit_det _).2 hd).unit
    have hx : ∀ a b z, Ideal.Quotient.mk I z = g.val (e a) (e b) →
        valuation k ((GeneralLinearGroup.map (algebraMap 𝒪[k] k) x₀).val a b - pr z) < 1 := fun a b z hz => by
      change valuation k (pr (Z a b) - pr z) < 1
      rw [← map_sub, ← h2, ← Ideal.Quotient.eq, hl, hz]
    refine ⟨⟨_, (GlobalTheory.T.mem_level_iff_symmetricPosition_entry_pattern k s κ S _).2 ⟨⟨x₀, rfl⟩, fun a b hab => ?_⟩⟩, hx⟩
    rw [(one a b).1]
    refine hx a b _ ?_
    rw [← (one a b).2, ← h _ _ ((sym_order S.odd e he hπ a b).1.1 hab), hg, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

include he hπ hg in

theorem sym_chr (ψ₀ : AddChar (O ⧸ I) ℂ) (hψ : ∀ z, (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * pr z) : ℂ) = ψ₀ (Ideal.Quotient.mk _ z))
    (x : S.P.J) (hx : ∀ a b z, Ideal.Quotient.mk I z = g.val (e a) (e b) →
      valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val a b - pr z) < 1) :
    (S.P.lam x : ℂ) = ψ₀ (edgeSum (symEdge S.ρ κ) g') := by
  classical
  choose l hl using Ideal.Quotient.mk_surjective (I := I)
  have h3 : edgeSum (symEdge S.ρ κ) g' = Ideal.Quotient.mk I (∑ a, ∑ b, if Edge a b then l (g.val (e a) (e b)) else 0) := by
    rw [edgeSum, ← (e.trans π.symm).sum_comp, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← (e.trans π.symm).sum_comp, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Equiv.trans_apply, (sym_order S.odd e he hπ a b).2, hg, Equiv.apply_symm_apply]
    split_ifs
    · rw [hl]
    · rw [map_zero]
  have h4 : GlobalTheory.RootEx.simpleSum (x : GL (Fin κ ⊕ Fin (s + 1)) k) + superSum Fin.val (x : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁ =
      ∑ a, ∑ b, if Edge a b then (x : GL (Fin κ ⊕ Fin (s + 1)) k).val a b else 0 := by
    simp [GlobalTheory.RootEx.simpleSum, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum, Fintype.sum_sum_type, Edge, add_comm, toBlocks₁₁]
    congr 1 <;> refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_ <;> exact @if_congr _ _ _ _ (_) _ _ _ _ Iff.rfl rfl rfl
  rw [S.sym.2 x, h3, ← hψ, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← mul_add, h4]
  refine congrArg (fun c : Circle => (c : ℂ)) ?_
  rw [← mul_inv_eq_one, ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← mul_sub]
  refine (S.cond 1).2 (by simp) _ ?_
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, map_one, inv_mul_le_one₀ (by simp [zero_lt_iff]), ← S.unif, map_sum,
    ← Finset.sum_sub_distrib]
  refine Valuation.map_sum_lt _ one_ne_zero fun a _ => ?_
  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Valuation.map_sum_lt _ one_ne_zero fun b _ => ?_
  split_ifs
  · exact hx a b _ (hl _)
  · simp

end Sym
end GlobalTheory.LocMod.PinEx

end
