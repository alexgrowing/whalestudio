import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ContModel

theorem ncard_image_of_le {W : Type} [AddCommGroup W] {A B : AddSubgroup W} (h : B ≤ A) (S : Set W)
    (hS : ∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) :
    ((QuotientAddGroup.mk : W → W ⧸ B) '' S).ncard
      = ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard * B.relIndex A := by
  have e := AddSubgroup.quotientEquivProdOfLE h
  have key : (AddSubgroup.quotientEquivProdOfLE h) '' ((QuotientAddGroup.mk : W → W ⧸ B) '' S)
      = ((QuotientAddGroup.mk : W → W ⧸ A) '' S) ×ˢ Set.univ := by
    ext ⟨u, v⟩
    simp only [Set.mem_prod, Set.mem_univ, and_true]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
      refine ⟨x, hx, ?_⟩
      have := congrArg Prod.fst hxy
      exact this
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz⟩ := (AddSubgroup.quotientEquivProdOfLE h).surjective
        ((QuotientAddGroup.mk x : W ⧸ A), v)
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
      refine ⟨_, ⟨y, ?_, rfl⟩, hz⟩
      have h1 : (QuotientAddGroup.mk y : W ⧸ A) = QuotientAddGroup.mk x := congrArg Prod.fst hz
      have h2 := QuotientAddGroup.eq.1 h1.symm
      have := hS x hx _ h2
      simpa using this
  rw [← Set.ncard_image_of_injective _ (AddSubgroup.quotientEquivProdOfLE h).injective, key,
    Set.ncard_prod, Set.ncard_univ]
  rfl

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.ContModel.relVol_of_le {W : Type} [AddCommGroup W]
    {W0 A B : AddSubgroup W} (h : B ≤ A) (hB : B.relIndex W0 ≠ 0) :
    _root_.GlobalTheory.HL.relVol W0 A = B.relIndex A * _root_.GlobalTheory.HL.relVol W0 B := by
  unfold _root_.GlobalTheory.HL.relVol
  have h1 := AddSubgroup.relIndex_inf_mul_relIndex W0 B A
  have h2 := AddSubgroup.relIndex_inf_mul_relIndex B W0 A
  have h3 := AddSubgroup.relIndex_inf_mul_relIndex B A W0
  rw [inf_eq_left.mpr h] at h1 h3
  rw [inf_comm W0 B] at h1
  rw [inf_comm W0 A] at h2
  rw [← h3] at hB ⊢
  have hd : (B.relIndex (A ⊓ W0) : ℝ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hB
  have hα : (A.relIndex W0 : ℝ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hB
  have key : (W0.relIndex B : ℝ) * B.relIndex A = B.relIndex (A ⊓ W0) * W0.relIndex A := by
    exact_mod_cast h1.trans h2.symm
  push_cast
  field_simp
  linear_combination (-1 : ℝ) * key

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
private theorem ncard_image_mk_eq_mul_relIndex_of_le {W : Type} [AddCommGroup W] {A B : AddSubgroup W} (h : B ≤ A)
    {S : Set W} (hS : ∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) :
    ((QuotientAddGroup.mk : W → W ⧸ B) '' S).ncard =
      ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard * B.relIndex A := by
  set Ab : AddSubgroup (W ⧸ B) := A.map (QuotientAddGroup.mk' B) with hAb
  set T : Set ((W ⧸ B) ⧸ Ab) :=
    (QuotientAddGroup.mk : W ⧸ B → (W ⧸ B) ⧸ Ab) '' ((QuotientAddGroup.mk : W → W ⧸ B) '' S) with hT
  have hpre : (QuotientAddGroup.mk : W ⧸ B → (W ⧸ B) ⧸ Ab) ⁻¹' T =
      (QuotientAddGroup.mk : W → W ⧸ B) '' S := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, hz⟩
      induction y using QuotientAddGroup.induction_on with
      | H w =>
        rw [QuotientAddGroup.eq, hAb, AddSubgroup.mem_map] at hz
        obtain ⟨a, ha, hax⟩ := hz
        have hax' : ((a : W) : W ⧸ B) = -((x : W) : W ⧸ B) + (w : W ⧸ B) := hax
        refine ⟨x + a, hS x hx a ha, ?_⟩
        rw [QuotientAddGroup.mk_add, hax']
        abel
    · intro hy
      exact ⟨y, hy, rfl⟩
  have e1 : Nat.card ((QuotientAddGroup.mk : W ⧸ B → (W ⧸ B) ⧸ Ab) ⁻¹' T) = Nat.card Ab * Nat.card T :=
    (Nat.card_congr (QuotientAddGroup.preimageMkEquivAddSubgroupProdSet Ab T)).trans (Nat.card_prod _ _)
  have e2 : Nat.card Ab = B.relIndex A := by
    rw [hAb, ← AddSubgroup.relIndex_bot_left, ← AddSubgroup.relIndex_comap, AddMonoidHom.comap_bot,
      QuotientAddGroup.ker_mk']
  have e3 : ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard = T.ncard := by
    rw [← Set.ncard_image_of_injective T (QuotientAddGroup.quotientQuotientEquivQuotient B A h).injective]
    congr 1
    rw [hT, Set.image_image, Set.image_image]
    rfl
  rw [← hpre, ← Nat.card_coe_set_eq, e1, e2, e3, Nat.card_coe_set_eq, mul_comm]

open ValuativeRel in
open scoped Pointwise ENNReal Classical in

theorem _root_.GlobalTheory.HL.ContModel.cont_eq {W : Type} [AddCommGroup W]
    {W0 A : AddSubgroup W} {S : Set W} (hA : _root_.GlobalTheory.HL.GoodSub W0 A S) :
    _root_.GlobalTheory.HL.cont W0 S =
      (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * _root_.GlobalTheory.HL.relVol W0 A := by
  have hS : _root_.GlobalTheory.HL.IsCO W0 S := ⟨A, hA⟩
  rw [_root_.GlobalTheory.HL.cont, dif_pos hS]
  have hA' : _root_.GlobalTheory.HL.GoodSub W0 hS.choose S := hS.choose_spec
  have hB : (A ⊓ hS.choose).relIndex W0 ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hA.1 hA'.1
  rw [_root_.GlobalTheory.HL.ContModel.relVol_of_le (inf_le_right : A ⊓ hS.choose ≤ hS.choose) hB,
    _root_.GlobalTheory.HL.ContModel.relVol_of_le (inf_le_left : A ⊓ hS.choose ≤ A) hB,
    ← mul_assoc, ← mul_assoc]
  congr 1
  exact_mod_cast (ncard_image_mk_eq_mul_relIndex_of_le (inf_le_right : A ⊓ hS.choose ≤ hS.choose) hA'.2.2.1).symm.trans
    (ncard_image_mk_eq_mul_relIndex_of_le (inf_le_left : A ⊓ hS.choose ≤ A) hA.2.2.1)

theorem cont_subgroup {W : Type} [AddCommGroup W] {W0 A : AddSubgroup W}
    (h1 : A.relIndex W0 ≠ 0) (h2 : W0.relIndex A ≠ 0) : cont W0 (A : Set W) = relVol W0 A := by
  have him : (QuotientAddGroup.mk : W → W ⧸ A) '' (A : Set W) = {0} := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (QuotientAddGroup.eq_zero_iff x).2 hx
    · rintro rfl
      exact ⟨0, A.zero_mem, rfl⟩
  have hg : GoodSub W0 A (A : Set W) :=
    ⟨h1, h2, fun x hx a ha => A.add_mem hx ha, by rw [him]; exact Set.finite_singleton _⟩
  rw [cont_eq hg, him]
  simp

theorem cont_self {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) : cont W0 (W0 : Set W) = 1 := by
  rw [cont_subgroup (by simp) (by simp)]
  simp [relVol]

theorem cont_even : cont (⊤ : AddSubgroup ℤ) (AddSubgroup.zmultiples (2 : ℤ) : Set ℤ) = 1 / 2 := by
  have h : (AddSubgroup.zmultiples (2 : ℤ)).relIndex ⊤ = 2 := by
    rw [AddSubgroup.relIndex_top_right, Int.index_zmultiples]; rfl
  rw [cont_subgroup (by rw [h]; norm_num) (by simp)]
  simp [relVol, h]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_sum_smul (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x : Fin m → Fin n → E)
    (c d : Fin m → E) :
    hf L Hm (∑ i, c i • x i) (∑ k, d k • x k) = ∑ i, ∑ k, L.cj (d k) * hf L Hm (x i) (x k) * c i := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  calc _ = ∑ a, ∑ b, ∑ i, ∑ k, c i * x i a * Hm a b * (L.cj (d k) * L.cj (x k b)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        first | rfl | exact Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ k, c i * x i a * Hm a b * (L.cj (d k) * L.cj (x k b)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, ∑ k, c i * x i a * Hm a b * (L.cj (d k) * L.cj (x k b)) := Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ k, ∑ b, c i * x i a * Hm a b * (L.cj (d k) * L.cj (x k b)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ a, ∑ b, c i * x i a * Hm a b * (L.cj (d k) * L.cj (x k b)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in

theorem _root_.GlobalTheory.HL.ContModel.gramT_rmul (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n m : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    _root_.GlobalTheory.HL.gramT L Hm (_root_.GlobalTheory.HL.rmul x A) =
      _root_.GlobalTheory.HL.cT L A * _root_.GlobalTheory.HL.gramT L Hm x * A := by
  ext a b
  simp only [_root_.GlobalTheory.HL.gramT, _root_.GlobalTheory.HL.rmul, _root_.GlobalTheory.HL.hf,
    _root_.GlobalTheory.HL.cT, Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun l _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem smul_inf_of_fix (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (Y : Submodule E (Fin n → E)) (g : fixG L Hm Y) (Λ : Submodule L.O (Fin n → E)) :
    (g • Λ) ⊓ Y.restrictScalars L.O = Λ ⊓ Y.restrictScalars L.O := by
  obtain ⟨g, hg⟩ := g
  obtain ⟨_, h1, h2⟩ := hg
  have h3 : ∀ v ∈ Y, g v = v := fun v hv => sub_eq_zero.1 (by simpa using h2 v hv)
  ext v
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hv⟩
    have hw' : w ∈ Y := (h1 w).1 hv
    refine ⟨?_, hv⟩
    change g w ∈ Λ
    rw [h3 w hw']; exact hw
  · rintro ⟨hv, hY⟩
    exact ⟨⟨v, hv, h3 v hY⟩, hY⟩

theorem sigMass_top (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (Λ0 Mh : Submodule L.O (Fin n → E)) :
    sigMass L Hm ⊤ Λ0 Mh = if IsSD L Hm Mh then 1 else 0 := by
  have hb : fixG L Hm ⊤ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨_, _, h2⟩
    rw [Subgroup.mem_bot]
    ext v i
    have : g v = v := sub_eq_zero.1 (by simpa using h2 v trivial)
    simp [this]
  have hv : ∀ Λ, invVol (fixG L Hm ⊤ ⊓ stabL L Λ0) (fixG L Hm ⊤ ⊓ stabL L Λ) = 1 := by
    intro Λ
    rw [hb]; simp [invVol]
  have hout : ∀ Λ : Submodule L.O (Fin n → E),
      (Quotient.mk _ Λ : MulAction.orbitRel.Quotient (fixG L Hm ⊤) (Submodule L.O (Fin n → E))).out = Λ := by
    intro Λ
    have h := Quotient.mk_out (s := MulAction.orbitRel (fixG L Hm ⊤) (Submodule L.O (Fin n → E))) Λ
    obtain ⟨g, hg⟩ := h
    have := smul_inf_of_fix L Hm ⊤ g Λ
    simp only [Submodule.restrictScalars_top, inf_top_eq] at this
    exact hg.symm.trans this
  unfold sigMass
  rw [tsum_eq_single (Quotient.mk _ Mh)]
  · rw [hout, hv]; simp
  · intro o ho
    rw [if_neg]
    rintro ⟨_, h⟩
    apply ho
    simp only [Submodule.restrictScalars_top, inf_top_eq] at h
    rw [← h, Quotient.out_eq]

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.ContModel.cj_mem (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [_root_.Formalism.MainNotions.S.Loc.LocE.O_def] at *
  exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])

theorem mem_hermLat (L : LocE F E) (m : ℕ) (X : Matrix (Fin m) (Fin m) E) :
    X ∈ hermLat L m ↔ IsHerm L X ∧ IsIntM L X := by
  refine ⟨fun h => ?_, fun h => AddSubgroup.subset_closure h⟩
  induction h using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨by ext i j; simp [cT], fun i j => L.O.zero_mem⟩
  | add x y _ _ hx hy =>
    refine ⟨?_, fun i j => L.O.add_mem (hx.2 i j) (hy.2 i j)⟩
    ext i j
    have h1 := congrFun (congrFun hx.1 i) j
    have h2 := congrFun (congrFun hy.1 i) j
    simp only [cT] at h1 h2
    simp [cT, h1, h2]
  | neg x _ hx =>
    refine ⟨?_, fun i j => L.O.neg_mem (hx.2 i j)⟩
    ext i j
    have h1 := congrFun (congrFun hx.1 i) j
    simp only [cT] at h1
    simp [cT, h1]

theorem hf_single (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b : Fin n) :
    hf L Hm (Pi.single a 1) (Pi.single b 1) = Hm a b := by
  simp [hf, Pi.single_apply, apply_ite L.cj]

theorem gramT_std (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) :
    gramT L Hm (fun a => Pi.single a 1) = Hm.transpose := by
  ext a b
  simp [gramT, hf_single]

theorem isPrimT_std (L : LocE F E) {n : ℕ} (Λ : Submodule L.O (Fin n → E))
    (h : ∀ a, (Pi.single a 1 : Fin n → E) ∈ Λ) : IsPrimT L 1 Λ (fun a => Pi.single a 1) :=
  ⟨h, _, h, fun a b => by rw [hf_single, Matrix.one_apply]⟩

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in

theorem _root_.GlobalTheory.HL.ContModel.gramT_thick (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (ϖ : 𝒪[F]) {n m : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (Ω : Set (Fin m → Fin n → E)) (Γ : Matrix (Fin m) (Fin m) E)
    (i : ℕ) (hΩ : ∀ y ∈ Ω, _root_.GlobalTheory.HL.gramT L Hm y = Γ) :
    ∀ x ∈ _root_.GlobalTheory.HL.thick L ϖ Ω i,
      _root_.GlobalTheory.HL.gramT L Hm x ∈ _root_.GlobalTheory.HL.horb L ϖ Γ i := by
  rintro x ⟨y, hy, A, hA, rfl⟩
  exact ⟨A, hA, by rw [_root_.GlobalTheory.HL.ContModel.gramT_rmul, hΩ y hy]⟩

theorem primCnt_zero (L : LocE F E) (ϖ : 𝒪[F]) (n j : ℕ) (Gm : Matrix (Fin 0) (Fin 0) E) :
    primCnt L ϖ n j Gm = 1 := by
  unfold primCnt
  rw [Set.ncard_eq_one]
  refine ⟨Set.univ, ?_⟩
  ext C
  simp

end GlobalTheory.HL.ContModel
