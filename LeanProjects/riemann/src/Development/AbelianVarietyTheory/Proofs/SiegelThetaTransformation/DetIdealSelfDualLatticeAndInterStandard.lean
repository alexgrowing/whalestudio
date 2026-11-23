import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DetIdeal

open NumberField Formalism.L2.Pj GlobalTheory.BetaEx

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_index_ideal_pair (A B : Submodule (𝓞 E) (Fin n → E)) (hA : A.FG) (hb : Bdd (B ⊔ A))
    (ht : ∀ m ∈ A, ∃ a : 𝓞 E, a ≠ 0 ∧ a • m ∈ B) :
    ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ detSpan (A ⊓ B) = 𝔞 • detSpan A ∧ detSpan B = 𝔞 • detSpan (B ⊔ A) ∧
      Ideal.absNorm 𝔞 = (A ⊓ B).toAddSubgroup.relIndex A.toAddSubgroup := by
  classical
  have key : ∀ s : Finset (Fin n → E), (∀ x ∈ s, x ∈ A) →
      ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧
        detSpan (A ⊓ B) = 𝔞 • detSpan (A ⊓ B ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))) ∧
        detSpan B = 𝔞 • detSpan (B ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))) ∧
        Ideal.absNorm 𝔞 = (A ⊓ B).toAddSubgroup.relIndex
          (A ⊓ B ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))).toAddSubgroup := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨⊤, by simp, by simp, by simp, by simp⟩
    | insert m s _ ih =>
      intro hs
      obtain ⟨𝔞, h0, h1, h1', h2⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
      have hsA : Submodule.span (𝓞 E) (s : Set (Fin n → E)) ≤ A :=
        Submodule.span_le.2 fun x hx => hs x (Finset.mem_insert_of_mem hx)
      have hm : m ∈ A := hs m (Finset.mem_insert_self _ _)
      have hmA : Submodule.span (𝓞 E) {m} ≤ A := (Submodule.span_singleton_le_iff_mem _ _).2 hm
      have e : ∀ X : Submodule (𝓞 E) (Fin n → E),
          X ⊔ Submodule.span (𝓞 E) ((insert m s : Finset (Fin n → E)) : Set (Fin n → E)) =
          (X ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))) ⊔ Submodule.span (𝓞 E) {m} := fun X => by
        rw [Finset.coe_insert, Submodule.span_insert, sup_assoc, sup_comm (Submodule.span _ {m})]
      rw [e, e]
      generalize Submodule.span (𝓞 E) (s : Set (Fin n → E)) = T at *
      have hmod : A ⊓ B ⊔ T = A ⊓ (B ⊔ T) := by
        rw [sup_comm B T, inf_comm A (T ⊔ B), sup_inf_assoc_of_le B hsA, sup_comm, inf_comm]
      have hc : ((B ⊔ T).comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) =
          (A ⊓ B ⊔ T).comap (LinearMap.toSpanSingleton (𝓞 E) _ m) := by
        rw [hmod]
        ext a
        exact ⟨fun h => ⟨A.smul_mem a hm, h⟩, fun h => h.2⟩
      obtain ⟨k, hk, h⟩ := hb
      have hb1 : Bdd ((A ⊓ B ⊔ T) ⊔ Submodule.span (𝓞 E) {m}) :=
        ⟨k, hk, fun v hv => h v (((sup_le (sup_le inf_le_left hsA) hmA).trans le_sup_right) hv)⟩
      have hb2 : Bdd ((B ⊔ T) ⊔ Submodule.span (𝓞 E) {m}) :=
        ⟨k, hk, fun v hv => h v ((sup_le (sup_le_sup_left hsA B) (hmA.trans le_sup_right)) hv)⟩
      refine ⟨𝔞 * ((A ⊓ B ⊔ T).comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)), ?_, ?_, ?_, ?_⟩
      · refine mul_ne_zero h0 ?_
        obtain ⟨a, ha, ham⟩ := ht m hm
        exact (Submodule.ne_bot_iff _).2 ⟨a, (le_sup_left : A ⊓ B ≤ A ⊓ B ⊔ T) ⟨A.smul_mem a hm, ham⟩, ha⟩
      · rw [h1, Submodule.mul_smul, ← detSpan_cyclic _ m hb1]
      · rw [h1', Submodule.mul_smul, ← hc, ← detSpan_cyclic _ m hb2]
      · rw [map_mul, h2, index_cyclic]
        exact AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono le_sup_left)
          (Submodule.toAddSubgroup_mono le_sup_left)
  obtain ⟨s, rfl⟩ := hA
  have := key s fun x hx => Submodule.subset_span hx
  rwa [sup_eq_right.2 inf_le_left] at this

theorem fg_of_bdd {M : Submodule (𝓞 E) (Fin n → E)} (hb : Bdd M) : M.FG := by
  obtain ⟨k, hk, h⟩ := hb
  have hs : (stdLat E n).FG := Submodule.fg_pi fun _ => by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  apply Submodule.fg_of_fg_map_injective (LinearMap.lsmul (𝓞 E) (Fin n → E) k)
    (fun x y hxy => smul_right_injective _ hk hxy)
  exact hs.of_le (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)

omit [NumberField E] in
theorem det_mem_one (v : Matrix (Fin n) (Fin n) E) (hv : ∀ i j, v i j ∈ (1 : Submodule (𝓞 E) E)) :
    v.det ∈ (1 : Submodule (𝓞 E) E) := by
  choose b hb using fun i j => Submodule.mem_one.1 (hv i j)
  refine Submodule.mem_one.2 ⟨(Matrix.of b).det, ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact hb i j

omit [NumberField E] in
theorem single_mem_std (i : Fin n) : (Pi.single i 1 : Fin n → E) ∈ stdLat E n := (mem_std _).2 fun j => by
  by_cases h : j = i
  · exact ⟨1, by simp [h]⟩
  · exact ⟨0, by simp [h]⟩

omit [NumberField E] in
theorem detSpan_std : detSpan (stdLat E n) = 1 := by
  apply le_antisymm
  · refine Submodule.span_le.2 fun d hd => ?_
    obtain ⟨v, hv, rfl⟩ := (mem_detSet _ d).1 hd
    exact det_mem_one v fun i j => hv i j trivial
  · rw [Submodule.one_le, ← Matrix.det_one (n := Fin n)]
    refine det_mem _ fun i => ?_
    convert single_mem_std (E := E) i using 1
    ext j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]

def bdual (S : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {w | ∀ v ∈ S, w ⬝ᵥ v ∈ (1 : Submodule (𝓞 E) E)}
  zero_mem' := fun v _ => by simp
  add_mem' := fun ha hb v hv => by rw [add_dotProduct]; exact add_mem (ha v hv) (hb v hv)
  smul_mem' := fun c w hw v hv => by rw [smul_dotProduct]; exact Submodule.smul_mem _ c (hw v hv)

omit [NumberField E] in
theorem detSpan_bdual_mul_le (S : Submodule (𝓞 E) (Fin n → E)) : detSpan (bdual S) * detSpan S ≤ 1 := by
  rw [detSpan, detSpan, Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  obtain ⟨w, hw, rfl⟩ := (mem_detSet _ _).1 hx
  obtain ⟨v, hv, rfl⟩ := (mem_detSet _ _).1 hy
  change w.det * v.det ∈ (1 : Submodule (𝓞 E) E)
  rw [← Matrix.det_transpose v, ← Matrix.det_mul]
  exact det_mem_one _ fun i j => hw i _ (hv j)

omit [NumberField E] in

theorem detSpan_bdual (S : Submodule (𝓞 E) (Fin n → E)) (J : Ideal (𝓞 E)) (hJ : J • detSpan S = 1) :
    detSpan (bdual S) = Submodule.map (Algebra.linearMap (𝓞 E) E) J := by
  classical
  have h1 : (1 : E) ∈ J • detSpan S := by rw [hJ]; exact Submodule.one_le.1 le_rfl
  have hint : ∀ y ∈ J, ∀ d ∈ detSpan S, y • d ∈ (1 : Submodule (𝓞 E) E) := fun y hy d hd =>
    hJ ▸ Submodule.smul_mem_smul hy hd
  apply le_antisymm
  · intro x hx
    have : ∀ z ∈ J • detSpan S, x * z ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) J := by
      intro z hz
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro y hy d hd
        obtain ⟨b, hb⟩ := Submodule.mem_one.1 (detSpan_bdual_mul_le S (Submodule.mul_mem_mul hx hd))
        refine ⟨y * b, J.mul_mem_right b hy, ?_⟩
        rw [Algebra.linearMap_apply, map_mul, hb, mul_smul_comm, Algebra.smul_def]
      · intro a b ha hb
        rw [mul_add]; exact add_mem ha hb
    simpa using this 1 h1
  · let K : Ideal (𝓞 E) := (detSpan S * detSpan (bdual S)).comap (Algebra.linearMap (𝓞 E) E)
    have h2 : J • detSpan S ≤ Submodule.map (Algebra.linearMap (𝓞 E) E) K.radical := by
      refine Submodule.smul_le.2 fun y hy d hd => ?_
      have : detSpan S ≤ (Submodule.map (Algebra.linearMap (𝓞 E) E) K.radical).comap
          (LinearMap.lsmul (𝓞 E) E y) := by
        refine Submodule.span_le.2 fun d hd => ?_
        obtain ⟨v, hv, rfl⟩ := (mem_detSet _ d).1 hd
        obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hint y hy _ (det_mem v hv))
        refine ⟨b, ⟨n, ?_⟩, hb⟩
        have hw : ∀ i, ((y : E) • v.adjugate.transpose) i ∈ bdual S := by
          intro i m hm
          have e : ((y : E) • v.adjugate.transpose) i ⬝ᵥ m = y • (v.updateRow i m).det := by
            rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec, ← Matrix.adjugate_transpose]
            change ((y : E) • v.adjugate.transpose i) ⬝ᵥ m = _
            rw [smul_dotProduct]
            rfl
          rw [e]
          exact hint y hy _ (det_mem _ (row_update_mem v hv i m hm))
        have h3 := Submodule.mul_mem_mul (det_mem v hv) (det_mem _ hw)
        change algebraMap (𝓞 E) E (b ^ n) ∈ detSpan S * detSpan (bdual S)
        convert h3 using 1
        rw [map_pow, hb, Matrix.det_smul, Matrix.det_transpose, mul_left_comm, ← Matrix.det_mul,
          Matrix.mul_adjugate, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← mul_pow]
        rfl
      exact this hd
    obtain ⟨b, hb, hb1⟩ := h2 h1
    obtain rfl : b = 1 := RingOfIntegers.ext (by simpa using hb1)
    obtain ⟨k, hk⟩ := hb
    have h4 : (1 : E) ∈ detSpan S * detSpan (bdual S) := by simpa [K] using hk
    rintro _ ⟨y, hy, rfl⟩
    have : ∀ z ∈ detSpan S * detSpan (bdual S), y • z ∈ detSpan (bdual S) := by
      intro z hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro d hd c hc
        obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hint y hy d hd)
        rw [← smul_mul_assoc, ← hb, ← Algebra.smul_def]
        exact Submodule.smul_mem _ b hc
      · intro a b ha hb
        rw [smul_add]; exact add_mem ha hb
    simpa [Algebra.smul_def] using this 1 h4

omit [NumberField E] in
theorem detSpan_map (h : Matrix (Fin n) (Fin n) E) (M : Submodule (𝓞 E) (Fin n → E)) :
    detSpan (M.map ((Matrix.mulVecLin h).restrictScalars (𝓞 E))) =
      Submodule.map (LinearMap.mulLeft (𝓞 E) h.det) (detSpan M) := by
  have e : ∀ v : Matrix (Fin n) (Fin n) E, (Matrix.of fun i => h.mulVec (v i)).det = h.det * v.det := fun v => by
    have : (Matrix.of fun i => h.mulVec (v i)) = v * h.transpose := by
      ext i j
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
    rw [this, Matrix.det_mul, Matrix.det_transpose, mul_comm]
  rw [detSpan, detSpan, Submodule.map_span]
  congr 1
  ext d
  constructor
  · intro hd
    obtain ⟨w, hw, rfl⟩ := (mem_detSet _ d).1 hd
    choose v hv hvw using hw
    refine ⟨(Matrix.of v).det, (mem_detSet _ _).2 ⟨_, hv, rfl⟩, ?_⟩
    change h.det * _ = _
    rw [← e]
    congr 1
    ext i j
    exact congrFun (hvw i) j
  · rintro ⟨_, hd, rfl⟩
    obtain ⟨v, hv, rfl⟩ := (mem_detSet _ _).1 hd
    exact (mem_detSet _ _).2 ⟨Matrix.of fun i => h.mulVec (v i), fun i => ⟨v i, hv i, rfl⟩, (e v).symm⟩

variable [IsCMField E]

theorem conj_mem_detSpan {M M' : Submodule (𝓞 E) (Fin n → E)}
    (h : ∀ v ∈ M, (fun j => IsCMField.complexConj E (v j)) ∈ M') {x : E} (hx : x ∈ detSpan M) :
    IsCMField.complexConj E x ∈ detSpan M' := by
  induction hx using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨v, hv, rfl⟩ := (mem_detSet _ d).1 hd
    rw [AlgEquiv.map_det]
    exact det_mem _ fun i => h _ (hv i)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul b x _ hx =>
    have : IsCMField.complexConj E (b • x) = IsCMField.ringOfIntegersComplexConj E b • IsCMField.complexConj E x := by
      change IsCMField.complexConj E ((b : E) * x) = (IsCMField.ringOfIntegersComplexConj E b : E) * _
      rw [map_mul, IsCMField.coe_ringOfIntegersComplexConj]
    rw [this]; exact Submodule.smul_mem _ _ hx

theorem mem_Ln_iff (Λ : GenLat E n) (hΛ : Λ.Unimod) (v : Fin n → E) :
    v ∈ Λ.Ln ↔ (fun j => IsCMField.complexConj E (v j)) ∈ bdual (stdLat E n ⊔ Λ.La) := by
  constructor
  · rintro ⟨h1, h2⟩ w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
    rw [dotProduct_add]
    refine add_mem (Submodule.sum_mem _ fun j _ => ?_) (Submodule.mem_one.2 ((hΛ v).1 h1 b hb))
    obtain ⟨x, hx⟩ := (mem_std _).1 h2 j
    obtain ⟨y, hy⟩ := (mem_std _).1 ha j
    refine Submodule.mem_one.2 ⟨IsCMField.ringOfIntegersComplexConj E x * y, ?_⟩
    change _ = IsCMField.complexConj E (v j) * a j
    rw [← hx, ← hy, ← IsCMField.coe_ringOfIntegersComplexConj, map_mul]
  · intro h
    refine ⟨(hΛ v).2 fun w hw => Submodule.mem_one.1 (h w (Submodule.mem_sup_right hw)), (mem_std _).2 fun j => ?_⟩
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (h _ (Submodule.mem_sup_left (single_mem_std j)))
    rw [dotProduct_single, mul_one] at hb
    refine ⟨IsCMField.ringOfIntegersComplexConj E b, ?_⟩
    rw [IsCMField.coe_ringOfIntegersComplexConj]
    change IsCMField.complexConj E (algebraMap (𝓞 E) E b) = _
    rw [hb, IsCMField.complexConj_apply_apply]

theorem mem_map_conjI (J : Ideal (𝓞 E)) (x : E) :
    x ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) (GlobalTheory.SW.conjI J) ↔
      IsCMField.complexConj E x ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) J := by
  have hc : ∀ a : 𝓞 E, a ∈ GlobalTheory.SW.conjI J ↔ IsCMField.ringOfIntegersComplexConj E a ∈ J := by
    intro a
    constructor
    · intro ha
      have : GlobalTheory.SW.conjI J ≤ J.comap (IsCMField.ringOfIntegersComplexConj E) := by
        refine Ideal.span_le.2 ?_
        rintro a ⟨b, hb, e⟩
        have : IsCMField.ringOfIntegersComplexConj E a = b := RingOfIntegers.ext (by
          rw [IsCMField.coe_ringOfIntegersComplexConj, e]
          exact IsCMField.complexConj_apply_apply E _)
        change IsCMField.ringOfIntegersComplexConj E a ∈ J
        rwa [this]
      exact this ha
    · intro ha
      refine Ideal.subset_span ⟨_, ha, ?_⟩
      rw [IsCMField.coe_ringOfIntegersComplexConj]
      exact (IsCMField.complexConj_apply_apply E _).symm
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, (hc a).1 ha, IsCMField.coe_ringOfIntegersComplexConj E a⟩
  · rintro ⟨b, hb, e⟩
    have e' : ((IsCMField.ringOfIntegersComplexConj E b : 𝓞 E) : E) = x := by
      rw [IsCMField.coe_ringOfIntegersComplexConj]
      change IsCMField.complexConj E (Algebra.linearMap (𝓞 E) E b) = _
      rw [e, IsCMField.complexConj_apply_apply]
    refine ⟨IsCMField.ringOfIntegersComplexConj E b, Ideal.subset_span ⟨b, hb, ?_⟩, e'⟩
    exact IsCMField.coe_ringOfIntegersComplexConj E b

theorem exists_detIdeal (Λ : GenLat E n) (hΛ : Λ.Unimod) :
    ∃ J : Ideal (𝓞 E), J ≠ ⊥ ∧
      Ideal.absNorm J = (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ∧
      detSpan Λ.Ln = J • detSpan Λ.La ∧
      detSpan Λ.Ln = Submodule.map (Algebra.linearMap (𝓞 E) E) (GlobalTheory.SW.conjI J) := by
  have hb := bdd_of_unimod Λ hΛ
  have hb' : Bdd (stdLat E n ⊔ Λ.La) := by
    obtain ⟨k, hk, h⟩ := hb
    refine ⟨k, hk, fun v hv => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [smul_add]
    exact add_mem (Submodule.smul_mem _ k ha) (h b hb)
  obtain ⟨J, h0, h1, h2, h3⟩ :=
    exists_index_ideal_pair Λ.La (stdLat E n) (fg_of_bdd hb) hb' fun m _ => exists_smul_std m
  refine ⟨J, h0, h3, h1, ?_⟩
  have h4 := detSpan_bdual _ J (h2.symm.trans detSpan_std)
  ext x
  rw [mem_map_conjI, ← h4]
  refine ⟨conj_mem_detSpan fun v hv => (mem_Ln_iff Λ hΛ v).1 hv, fun hx => ?_⟩
  rw [← IsCMField.complexConj_apply_apply E x]
  refine conj_mem_detSpan (fun v hv => (mem_Ln_iff Λ hΛ _).2 ?_) hx
  simpa only [IsCMField.complexConj_apply_apply] using hv

end GlobalTheory.DetIdeal

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

theorem GlobalTheory.DetIdeal.detIdeal_selfDual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Λ : GenLat E n), Λ.Unimod → ∃ J : Ideal (𝓞 E), J ≠ ⊥ ∧ Ideal.absNorm J = (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ∧ Submodule.span (𝓞 E) (detSet Λ.Ln) = J • Submodule.span (𝓞 E) (detSet Λ.La) ∧ Submodule.span (𝓞 E) (detSet Λ.Ln) = Submodule.map (Algebra.linearMap (𝓞 E) E) (conjI J) ∧ ∀ h : Matrix (Fin n) (Fin n) E, Submodule.span (𝓞 E) (detSet (actLat h Λ).La) = Submodule.map (LinearMap.mulLeft (𝓞 E) h.det) (Submodule.span (𝓞 E) (detSet Λ.La)) := by
  intro E _ _ _ n Λ hΛ
  obtain ⟨J, h0, h1, h2, h3⟩ := GlobalTheory.DetIdeal.exists_detIdeal Λ hΛ
  exact ⟨J, h0, h1, h2, h3, fun h => GlobalTheory.DetIdeal.detSpan_map h Λ.La⟩
