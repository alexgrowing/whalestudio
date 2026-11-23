import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFrameClassProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeGramDetAndMinorsOrbitInvariantStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.UnimodTerm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem _root_.GlobalTheory.HL.UnimodTerm.hf_sum_left {ι : Type} [Fintype ι] (c : ι → E) (g : ι → S.V) (y : S.V) :
    _root_.GlobalTheory.HL.hf L S.Hm (∑ b, c b • g b) y =
      ∑ b, _root_.GlobalTheory.HL.hf L S.Hm (g b) y * c b := by
  simp only [_root_.GlobalTheory.HL.hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm (s := (Finset.univ : Finset ι))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset ι))]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
omit [IsNonarchimedeanLocalField F] [CharZero F] in
private lemma hf_Hm_sub_left (x m y : S.V) :
    _root_.GlobalTheory.HL.hf L S.Hm (x - m) y =
      _root_.GlobalTheory.HL.hf L S.Hm x y -
        _root_.GlobalTheory.HL.hf L S.Hm m y := by
  simp only [_root_.GlobalTheory.HL.hf, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in

theorem _root_.GlobalTheory.HL.UnimodTerm.proj_mem {d : S.Datum}
    {Λ : Submodule L.O S.V} (hT : S.IsTerm d Λ) (ha : S.a = 0)
    {x m : S.V} (hx : x ∈ Λ) (hm : m ∈ S.ME)
    (hw : x - m ∈ S.W0) : m ∈ S.M d Λ := by
  obtain ⟨hsd, hW, -, hfr, -, -, -, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, hp, hq, -, -, hth, -⟩ := hW
  obtain ⟨-, -, -, -, -, hth0, -, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  obtain ⟨⟨c, hc0, hcv, hdet⟩, -, hspan⟩ :=
    _root_.GlobalTheory.FrameGram.main L r k S _ hp _ hq
  set p := (S.wit d Λ).1
  set q := (S.wit d Λ).2
  set e : Fin (r + 1) ⊕ Fin (r + 1) → S.V := Sum.elim (fun i => p (S.f i))
    (fun i => algebraMap F E S.th⁻¹ • (q (S.f' i) - p (S.f i))) with he_def

  obtain ⟨k', u, rfl⟩ := _root_.GlobalTheory.UnramVal.exists_eq_zpow_mul_unit S.ϖ_irr hc0
  rw [_root_.GlobalTheory.UnramVal.vE_zpow_mul_unit L S.ϖ_irr, ha] at hcv
  subst hcv
  simp only [zpow_zero, one_mul] at hdet
  have hu : algebraMap F E (u : F) ∈ L.O :=
    (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L _).mpr (u : (ValuativeRel.valuation F).integer).2
  have hu' : algebraMap F E ((u⁻¹ : (ValuativeRel.valuation F).integer ˣ) : F) ∈ L.O :=
    (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L _).mpr ((u⁻¹ : (ValuativeRel.valuation F).integer ˣ) : (ValuativeRel.valuation F).integer).2
  have huu : algebraMap F E ((u⁻¹ : (ValuativeRel.valuation F).integer ˣ) : F) * algebraMap F E (u : F) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Subring.coe_one, map_one]

  have he : ∀ a, e a ∈ Λ := by
    rintro (i | i)
    · exact ((hfr (r + 1) le_rfl (p (S.f i))).mpr (Submodule.subset_span ⟨i, i.isLt, rfl⟩)).1
    · obtain ⟨y, hy, hxy⟩ := hth i
      simp only [he_def, Sum.elim_inr]
      rw [hxy, smul_smul, ← map_mul, inv_mul_cancel₀ hth0, map_one, one_smul]
      exact hy
  have hG : ∀ a b, _root_.GlobalTheory.HL.hf L S.Hm (e b) (e a) ∈ L.O :=
    fun a b => (hsd.2 (e a)).mpr (he a) (e b) (he b)

  rw [← hspan] at hm
  unfold _root_.GlobalTheory.HL.Frames.W0 at hw
  rw [← hspan] at hw
  obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hm
  rw [_root_.GlobalTheory.HL.StdLat.mem_perp_span] at hw
  set G : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
    Matrix.of fun a b => _root_.GlobalTheory.HL.hf L S.Hm (e b) (e a) with hG_def
  set v : Fin (r + 1) ⊕ Fin (r + 1) → E := fun a => _root_.GlobalTheory.HL.hf L S.Hm x (e a)
  have hGμ : G.mulVec μ = v := by
    funext a
    have h1 := hw a
    rw [hf_Hm_sub_left, sub_eq_zero, ← hμ,
      _root_.GlobalTheory.HL.UnimodTerm.hf_sum_left] at h1
    simp only [Matrix.mulVec, dotProduct, hG_def, Matrix.of_apply, v, h1]
  have hdetG : G.det = algebraMap F E (u : F) := hdet
  have hadj : G.det • μ = G.adjugate.mulVec v := by
    rw [← hGμ, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  set GO : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) L.O := fun a b => ⟨G a b, hG a b⟩
  have hGO : L.O.subtype.mapMatrix GO = G := by
    ext a b
    rfl
  have hadjO : ∀ a b, G.adjugate a b ∈ L.O := by
    intro a b
    rw [← hGO, ← RingHom.map_adjugate]
    exact (GO.adjugate a b).2
  have hvO : ∀ a, v a ∈ L.O := fun a => (hsd.2 (e a)).mpr (he a) x hx
  have hμO : ∀ b, μ b ∈ L.O := by
    intro b
    have h2 := congrFun hadj b
    simp only [Pi.smul_apply, smul_eq_mul, hdetG] at h2
    have h3 : μ b = algebraMap F E ((u⁻¹ : (ValuativeRel.valuation F).integer ˣ) : F) * (G.adjugate.mulVec v) b := by
      rw [← h2, ← mul_assoc, huu, one_mul]
    rw [h3]
    refine L.O.mul_mem hu' ?_
    simp only [Matrix.mulVec, dotProduct]
    exact L.O.sum_mem fun a _ => L.O.mul_mem (hadjO b a) (hvO a)

  rw [← hμ]
  refine Submodule.sum_mem _ fun b _ => ?_
  have hmem : e b ∈ S.M d Λ := by
    apply Submodule.subset_span
    rcases b with i | i
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨i, rfl⟩
  exact Submodule.smul_mem _ (⟨μ b, hμO b⟩ : L.O) hmem

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in

theorem _root_.GlobalTheory.HL.UnimodTerm.mem_iff_graph {d : S.Datum} {Λ : Submodule L.O S.V}
    (hT : S.IsTerm d Λ) (ha : S.a = 0) {w : S.V}
    (hw : w ∈ S.W0) : w ∈ Λ ↔ (w, w) ∈ d.2.2 := by
  obtain ⟨-, hW, hMs, -, -, -, -, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, -, -, -, -, -, hgraph⟩ := hW
  have hXME : S.X ≤ S.ME :=
    (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f (Nat.le_succ r)).trans le_sup_left
  have hX'ME : S.X' ≤ S.ME :=
    (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f' (Nat.le_succ r)).trans le_sup_right
  have hworth : ∀ y ∈ S.ME, _root_.GlobalTheory.HL.hf L S.Hm w y = 0 := hw
  rw [hgraph]
  unfold _root_.GlobalTheory.HL.Frames.graphOf
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hwΛ
    exact ⟨w, hwΛ, w, hwΛ, fun y hy => hworth y (hX'ME hy), fun y hy => hworth y (hXME hy),
      by simp, by simp, ⟨0, Λ.zero_mem, by simp⟩⟩
  · rintro ⟨y', hy', y, hy, -, -, -, hyw, -⟩
    have hproj := _root_.GlobalTheory.HL.UnimodTerm.proj_mem S hT ha hy (hXME hyw)
      (by rw [sub_sub_cancel]; exact hw)
    have h1 : y - w ∈ Λ ⊓ Submodule.restrictScalars L.O S.ME := hMs hproj
    have h2 := Λ.sub_mem hy (Submodule.mem_inf.mp h1).1
    rwa [sub_sub_cancel] at h2

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
theorem _root_.GlobalTheory.HL.UnimodTerm.le_of_M_eq {d : S.Datum} {Λ Λ' : Submodule L.O S.V}
    (hT : S.IsTerm d Λ) (hT' : S.IsTerm d Λ') (ha : S.a = 0)
    (hM : S.M d Λ' = S.M d Λ) : Λ' ≤ Λ := by
  obtain ⟨-, -, hMs, -, -, -, -, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, hMs', -, -, -, -, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ' hT'
  obtain ⟨-, hc, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  intro x hx
  have hxtop : x ∈ S.ME ⊔ S.W0 := by
    rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.mp hxtop
  have hm' : m ∈ S.M d Λ' :=
    _root_.GlobalTheory.HL.UnimodTerm.proj_mem S hT' ha hx hm (by simpa using hw)
  have hmΛ' : m ∈ Λ' := (Submodule.mem_inf.mp
    (show m ∈ Λ' ⊓ Submodule.restrictScalars L.O S.ME from hMs' hm')).1
  rw [hM] at hm'
  have hmΛ : m ∈ Λ := (Submodule.mem_inf.mp
    (show m ∈ Λ ⊓ Submodule.restrictScalars L.O S.ME from hMs hm')).1
  have hwΛ' : w ∈ Λ' := by simpa using Λ'.sub_mem hx hmΛ'
  have hwΛ : w ∈ Λ := (_root_.GlobalTheory.HL.UnimodTerm.mem_iff_graph S hT ha hw).mpr
    ((_root_.GlobalTheory.HL.UnimodTerm.mem_iff_graph S hT' ha hw).mp hwΛ')
  exact Λ.add_mem hmΛ hwΛ

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma mem_frameCls_self (g h : Fin (r + 1) → S.V) : (g, h) ∈ S.frameCls g h := by
  unfold _root_.GlobalTheory.HL.Frames.frameCls
  have hint : _root_.GlobalTheory.HL.IsIntM L (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) := by
    unfold _root_.GlobalTheory.HL.IsIntM
    intro i j
    by_cases hij : i = j
    · subst hij; simp [L.O.one_mem]
    · simp [Matrix.one_apply_ne hij, L.O.zero_mem]
  refine ⟨1, 1, hint, hint, fun i j hji => ⟨Matrix.one_apply_ne (ne_of_gt hji), Matrix.one_apply_ne (ne_of_gt hji)⟩,
    fun i => ⟨Matrix.one_apply_eq i, Matrix.one_apply_eq i⟩, fun i j => ⟨0, L.O.zero_mem, by simp⟩, ?_, ?_⟩
  · intro j; simp [Matrix.one_apply]
  · intro j; simp [Matrix.one_apply]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma Mof_le_of_mem_frameCls {g h g' h' : Fin (r + 1) → S.V}
    (hP : (g', h') ∈ S.frameCls g h) : S.Mof g' h' ≤ S.Mof g h := by
  obtain ⟨A, A', hA, hA', -, -, hdiff, h1, h2⟩ := hP
  dsimp only at h1 h2
  obtain ⟨-, -, -, -, -, hth0, -, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  have hθ : algebraMap F E S.th⁻¹ * algebraMap F E S.th = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hth0, map_one]
  choose c hc hcdef using hdiff
  unfold _root_.GlobalTheory.HL.Frames.Mof
  rw [Submodule.span_le]
  rintro v (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · rw [h1 j]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ (⟨A i j, hA i j⟩ : L.O) (Submodule.subset_span (Or.inl ⟨i, rfl⟩))
  · have hsplit : algebraMap F E S.th⁻¹ • (h' j - g' j) =
        ∑ i, A' i j • (algebraMap F E S.th⁻¹ • (h i - g i)) + ∑ i, c i j • g i := by
      rw [h1 j, h2 j, ← Finset.sum_sub_distrib, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hci : c i j = algebraMap F E S.th⁻¹ * (A' i j - A i j) := by
        rw [hcdef, ← mul_assoc, hθ, one_mul]
      rw [hci]
      module
    show algebraMap F E S.th⁻¹ • (h' j - g' j) ∈ _
    rw [hsplit]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => ?_) (Submodule.sum_mem _ fun i _ => ?_)
    · exact Submodule.smul_mem _ (⟨A' i j, hA' i j⟩ : L.O) (Submodule.subset_span (Or.inr ⟨i, rfl⟩))
    · exact Submodule.smul_mem _ (⟨c i j, hc i j⟩ : L.O) (Submodule.subset_span (Or.inl ⟨i, rfl⟩))

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in

theorem _root_.GlobalTheory.HL.UnimodTerm.term_unique : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.a = 0 → S.BBzero d Λ ∧ ∀ Λ', S.IsTerm d Λ' → S.Fr d Λ' = S.Fr d Λ → Λ' = Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT ha
  obtain ⟨-, -, hMs, -, -, -, -, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  refine ⟨?_, fun Λ' hT' hFr => ?_⟩
  · unfold _root_.GlobalTheory.HL.Frames.BBzero
    refine le_antisymm hMs fun x hx => ?_
    have hx' : x ∈ Λ ⊓ Submodule.restrictScalars L.O S.ME := hx
    exact _root_.GlobalTheory.HL.UnimodTerm.proj_mem S hT ha (Submodule.mem_inf.mp hx').1
      (Submodule.mem_inf.mp hx').2 (by simp)
  · have hM : S.M d Λ' = S.M d Λ := by
      unfold _root_.GlobalTheory.HL.Frames.Fr at hFr
      unfold _root_.GlobalTheory.HL.Frames.M
      apply le_antisymm
      · have hmem := mem_frameCls_self S (S.fr d Λ') (S.fr' d Λ')
        rw [hFr] at hmem
        exact Mof_le_of_mem_frameCls S hmem
      · have hmem := mem_frameCls_self S (S.fr d Λ) (S.fr' d Λ)
        rw [← hFr] at hmem
        exact Mof_le_of_mem_frameCls S hmem
    exact le_antisymm (_root_.GlobalTheory.HL.UnimodTerm.le_of_M_eq S hT hT' ha hM)
      (_root_.GlobalTheory.HL.UnimodTerm.le_of_M_eq S hT' hT ha hM.symm)

end GlobalTheory.HL.UnimodTerm
