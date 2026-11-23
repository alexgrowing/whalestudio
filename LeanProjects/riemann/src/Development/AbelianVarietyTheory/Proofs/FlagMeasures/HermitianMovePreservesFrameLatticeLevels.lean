import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MoveLatticeIsTermSameDatumWithWitnessesStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MoveSame
open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem transfer {V : Type} [AddCommGroup V] [Module E V] {m : ℕ} {g g' h h' : Fin m → V}
    (hli : LinearIndependent E (Sum.elim g g')) {y : V} {al al' : Fin m → E}
    (e1 : y = ∑ i, al i • g i + ∑ i, al' i • g' i) (e2 : y = ∑ i, al i • h i + ∑ i, al' i • h' i)
    (P : (Fin m → E) → (Fin m → E) → Prop)
    (H : ∃ be be' : Fin m → E, y = ∑ i, be i • g i + ∑ i, be' i • g' i ∧ P be be') :
    ∃ be be' : Fin m → E, y = ∑ i, be i • h i + ∑ i, be' i • h' i ∧ P be be' := by
  obtain ⟨be, be', e3, hP⟩ := H
  have h0 := Fintype.linearIndependent_iff.1 hli (Sum.elim (al - be) (al' - be')) (by
    have := e1.symm.trans e3
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, sub_smul,
      Finset.sum_sub_distrib]
    rw [sub_add_sub_comm, this, sub_self])
  have a1 : al = be := funext fun i => sub_eq_zero.1 (h0 (Sum.inl i))
  have a2 : al' = be' := funext fun i => sub_eq_zero.1 (h0 (Sum.inr i))
  subst a1 a2
  exact ⟨_, _, e2, hP⟩

theorem mem_Mof (g g' : Fin (r + 1) → S.V) (y : S.V) :
    y ∈ S.Mof g g' ↔ ∃ al al' : Fin (r + 1) → E, y = ∑ i, al i • g i + ∑ i, al' i • g' i ∧
      ∀ i, algebraMap F E S.th * al' i ∈ L.O ∧ al i + al' i ∈ L.O := by
  have ht := WitIndep.th_mul S
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · refine ⟨Pi.single b 1, 0, by simp [Pi.single_apply], fun i => ⟨by simp, ?_⟩⟩
        by_cases h : i = b
        · subst h; simp
        · simp [h]
      · refine ⟨Pi.single b (-algebraMap F E S.th⁻¹), Pi.single b (algebraMap F E S.th⁻¹), ?_,
          fun i => ?_⟩
        · simp only [Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
            if_true, smul_sub, neg_smul]
          abel
        · by_cases h : i = b
          · subst h
            simp only [Pi.single_eq_same, neg_add_cancel, mul_comm (algebraMap F E S.th), ht]
            exact ⟨L.O.one_mem, L.O.zero_mem⟩
          · simp [h]
    | zero => exact ⟨0, 0, by simp, fun i => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, a', rfl, ha⟩ := hx
      obtain ⟨b, b', rfl, hb⟩ := hy
      refine ⟨a + b, a' + b', ?_, fun i => ⟨?_, ?_⟩⟩
      · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel
      · simpa [mul_add] using L.O.add_mem (ha i).1 (hb i).1
      · have := L.O.add_mem (ha i).2 (hb i).2
        rw [add_add_add_comm] at this
        exact this
    | smul c x _ hx =>
      obtain ⟨a, a', rfl, ha⟩ := hx
      refine ⟨fun i => c * a i, fun i => c * a' i, ?_, fun i => ⟨?_, ?_⟩⟩
      · rw [Subring.smul_def]
        simp only [smul_add, Finset.smul_sum, smul_smul]
      · have := L.O.mul_mem c.2 (ha i).1
        rw [mul_left_comm] at this
        exact this
      · have := L.O.mul_mem c.2 (ha i).2
        rw [mul_add] at this
        exact this
  · rintro ⟨al, al', rfl, h⟩
    rw [← Finset.sum_add_distrib]
    refine Submodule.sum_mem _ fun i _ => ?_
    have e : al i • g i + al' i • g' i = (al i + al' i) • g i +
        (algebraMap F E S.th * al' i) • (algebraMap F E S.th⁻¹ • (g' i - g i)) := by
      rw [smul_smul, mul_right_comm, mul_comm (algebraMap F E S.th), ht, one_mul, add_smul, smul_sub]
      abel
    rw [e]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ (⟨_, (h i).2⟩ : L.O) (Submodule.subset_span (Or.inl ⟨i, rfl⟩)))
      (Submodule.smul_mem _ (⟨_, (h i).1⟩ : L.O) (Submodule.subset_span (Or.inr ⟨i, rfl⟩)))

theorem exists_coef_map {g : Fin (r + 1) → S.V}
    (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0) {n : S.GLV} (hn : n ∈ S.Nof g)
    {J : ℕ} {y : S.V} (hy : y ∈ S.spanTo g J) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), ¬ (i : ℕ) < J → c i = 0) ∧ y = ∑ i, c i • n (g i) := by
  obtain ⟨c, hc, e⟩ := StdLat.exists_coef g _ (TermBasic.map_mem hg ((S.Nof g).inv_mem hn) J hy)
  refine ⟨c, hc, ?_⟩
  have e2 : n (n⁻¹ y) = y := n.apply_symm_apply y
  rw [← e2, e]
  simp only [map_sum, map_smul]

theorem iso_span {g : Fin (r + 1) → S.V}
    (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0) {J : ℕ} {v : S.V}
    (hv : v ∈ S.spanTo g J) : v ∈ perp L S.Hm (S.spanTo g r) := by
  refine (Submodule.span_le.2 ?_ : S.spanTo g J ≤ _) hv
  rintro _ ⟨i, -, rfl⟩
  rw [SetLike.mem_coe, Frames.spanTo, StdLat.image_lt, StdLat.mem_perp_span]
  exact hg _

variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem indep {n n' : S.GLV} (hn : n ∈ S.N) (hn' : n' ∈ S.N') :
    LinearIndependent E (Sum.elim (fun b => n (S.f b)) (fun b => n' (S.f' b))) := by
  have hg : ∀ a (j : Fin r), hf L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    simp [S.gram, Fin.castSucc_ne_last]
  have hg' : ∀ a (j : Fin r), hf L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    simp [S.gram', Fin.castSucc_ne_last]
  obtain ⟨hli, -⟩ := FrameBasic.main L r k S
  obtain ⟨l1, l2, l3⟩ := linearIndependent_sum.1 hli
  refine LinearIndependent.sum_type (l1.map' n.toLinearMap (LinearEquiv.ker _))
    (l2.map' n'.toLinearMap (LinearEquiv.ker _)) (l3.mono ?_ ?_)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, rfl⟩
    have := TermBasic.map_mem hg hn (r + 1) (TermBasic.self_mem S S.f b.2)
    rw [TermBasic.spanTo_top] at this
    exact this
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, rfl⟩
    have := TermBasic.map_mem hg' hn' (r + 1) (TermBasic.self_mem S S.f' b.2)
    rw [TermBasic.spanTo_top] at this
    exact this

end

theorem move_same : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → ∀ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s → S.IsTerm d Λ₁ ∧ ∀ y ∈ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)), (y ∈ Λ → y ∈ Λ₁) ∧ (y ∈ S.M d Λ₁ ↔ y ∈ S.M d Λ) ∧ S.lev (S.fr d Λ₁) (S.fr' d Λ₁) y = S.lev (S.fr d Λ) (S.fr' d Λ) y := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF x x' u s hM Λ₁ hΛ₁
  obtain ⟨n₀, hn₀, n₀', hn₀', n'', hn'', -, e0i, e0', e'', emv, hW₁⟩ :=
    GlobalTheory.T.move_lattice_isTerm_same_datum_with_witnesses L r k S j β βJ d Λ hT hF x x' u s hM
  obtain ⟨hsx, -, -, -, -, -, -, -, -, hxX, hxX'⟩ :=
    GlobalTheory.T.hermitianDoubleCosetFrames_datum_move_properties L r k S j β βJ d Λ hT hF x x' u s hM
  have eΛ : n₀⁻¹ • Λ = Λ₁ := SetLike.coe_injective (emv.trans hΛ₁.symm)
  rw [eΛ] at hW₁
  obtain ⟨-, hW, -, -, -, hli, -⟩ := TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, eM, -, eL, -⟩ := WitIndep.witness_independence L r k S d Λ₁ _ _ hW₁
  have hli₁ := indep S hW₁.2.2.1 hW₁.2.2.2.1
  have hg : ∀ a (j : Fin r), hf L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    simp [S.gram, Fin.castSucc_ne_last]
  have hg' : ∀ a (j : Fin r), hf L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    simp [S.gram', Fin.castSucc_ne_last]
  obtain ⟨-, -, hb, -, huΛ, hu, -, -⟩ := hM
  have hH := S.herm.1
  have hyu : ∀ y ∈ S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1), hf L S.Hm y u = 0 := fun y hy => by
    rw [← hf_cj L hH, hu y hy, map_zero]
  have hJ : (j : ℕ) + 1 ≤ r := j.2
  have hn := hW.2.2.1
  have hn' := hW.2.2.2.1
  have f1 : ∀ i : Fin (r + 1), (i : ℕ) < j + 1 → (n₀⁻¹ * (S.wit d Λ).1) (S.f i) = S.fr d Λ i := by
    intro i hi
    have hm : S.fr d Λ i ∈ S.spanTo S.f (j + 1) :=
      TermBasic.map_mem hg hn _ (TermBasic.self_mem S S.f hi)
    show n₀⁻¹ (S.fr d Λ i) = _
    rw [e0i, eich, hf_neg_r, hyu _ (Submodule.mem_sup_left hm), iso_span S hg hm x hxX]
    simp
  have f2 : ∀ i : Fin (r + 1), (i : ℕ) < j + 1 →
      (n'' * n₀' * (S.wit d Λ).2) (S.f' i) = S.fr' d Λ i := by
    intro i hi
    have hm : S.fr' d Λ i ∈ S.spanTo S.f' (j + 1) :=
      TermBasic.map_mem hg' hn' _ (TermBasic.self_mem S S.f' hi)
    show n'' (n₀' (S.fr' d Λ i)) = _
    rw [e0', eich, hyu _ (Submodule.mem_sup_right hm), iso_span S hg' hm x' hxX']
    simp only [zero_smul, add_zero, sub_zero]
    exact e'' _ (iso_span S hg' hm)
  refine ⟨⟨(_, _), hW₁⟩, fun y hy => ?_⟩
  have hyu0 := hyu y hy
  obtain ⟨v, hv, v', hv', rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨c, hc, ec⟩ := exists_coef_map S hg hn hv
  obtain ⟨c', hc', ec'⟩ := exists_coef_map S hg' hn' hv'
  have e1 : v + v' = ∑ i, c i • S.fr d Λ i + ∑ i, c' i • S.fr' d Λ i := by
    rw [ec, ec']; rfl
  have e2 : v + v' = ∑ i, c i • (n₀⁻¹ * (S.wit d Λ).1) (S.f i) +
      ∑ i, c' i • (n'' * n₀' * (S.wit d Λ).2) (S.f' i) := by
    rw [e1]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
    · by_cases hi : (i : ℕ) < j + 1
      · rw [f1 i hi]
      · rw [hc i hi, zero_smul, zero_smul]
    · by_cases hi : (i : ℕ) < j + 1
      · rw [f2 i hi]
      · rw [hc' i hi, zero_smul, zero_smul]
  refine ⟨fun hyΛ => ?_, ?_, ?_⟩
  · have hvX : v ∈ S.X := TermBasic.spanTo_mono S S.f hJ hv
    have hvX' : v' ∈ S.X' := TermBasic.spanTo_mono S S.f' hJ hv'
    obtain ⟨a, ha, ea⟩ := hF.1.2.2 x hxX x' hxX' _ (S.X.smul_mem (algebraMap F E S.th) hvX) _
      (S.X'.smul_mem (algebraMap F E S.th) hvX') hb ⟨_, hyΛ, (smul_add _ _ _).symm⟩
    rw [Frames.h, hf_smul_r, AlgEquiv.commutes] at ea
    have ea2 : hf L S.Hm x v' = a := by
      have := congrArg (algebraMap F E S.th⁻¹ * ·) ea
      simpa only [← mul_assoc, WitIndep.th_mul S, one_mul] using this
    have ea3 : hf L S.Hm (v + v') x = L.cj a := by
      rw [hf_add_l, iso_span S hg hv x hxX, zero_add, ← ea2, hf_cj L hH]
    rw [← SetLike.mem_coe, hΛ₁]
    show eich L S.Hm x u s (v + v') ∈ Λ
    rw [eich, hyu0, ea3, zero_smul, add_zero]
    exact Λ.sub_mem hyΛ (Λ.smul_mem (⟨_, UnramOrder.cj_mem L ha⟩ : L.O) (Λ.add_mem huΛ hsx))
  · rw [eM, Frames.M, mem_Mof, mem_Mof]
    exact ⟨transfer hli₁ e2 e1 _, transfer hli e1 e2 _⟩
  · rw [eL, Frames.lev, Frames.lev]
    congr 1
    ext t
    exact ⟨transfer hli₁ e2 e1 _, transfer hli e1 e2 _⟩

end GlobalTheory.HL.MoveSame
