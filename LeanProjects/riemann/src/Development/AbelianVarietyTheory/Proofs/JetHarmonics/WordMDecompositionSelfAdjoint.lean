import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LetterLiftOfParts
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersPassDiGIBoundedFactorsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameStartConstantsNormalFormEmptyWordStatement

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.MShapeNF

open Formalism.FourierDecayAlt.P.TLA.M2

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

def bAlg (d : Q.NFData P A) : Subalgebra ℂ A :=
  (Submodule.span ℂ (bmon d : Set A)).toSubalgebra (Submodule.subset_span (bmon d).one_mem) (by
    intro x y hx hy
    have h := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact (bmon d).mul_mem ha hb)

variable {S : Type} [Fintype S] [DecidableEq S]

def EM (B : Subalgebra ℂ A) (E : SlopeTestRemainingChoices S A) : Prop := ∀ e e', E e e' ∈ B

theorem EM.add {B : Subalgebra ℂ A} {E F : SlopeTestRemainingChoices S A} (hE : EM B E) (hF : EM B F) : EM B (E + F) := fun i j =>
  B.add_mem (hE i j) (hF i j)

theorem EM.smul {B : Subalgebra ℂ A} {E : SlopeTestRemainingChoices S A} (z : ℂ) (hE : EM B E) : EM B (z • E) := fun i j =>
  B.smul_mem (hE i j) z

theorem EM.io {B : Subalgebra ℂ A} {a : A} (ha : a ∈ B) : EM B (io a : SlopeTestRemainingChoices S A) := fun i j => by
  simp only [Wd.io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact ha
  · exact B.zero_mem

variable [StarModule ℂ A]

open MeasureTheory in
private lemma mem_inv_of_mem_ofWord_inv {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A]
    [Fintype S] [DecidableEq S] {r : ℕ} (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) (st : _root_.Formalism.FourierDecayAlt.Fr.Start A) :
    ∀ (w : List (_root_.Formalism.FourierDecayAlt.Wd.Letter ℂ S)) (Z : ℂ), Z ∈ (_root_.Formalism.FourierDecayAlt.Fr.ofWord L st w).inv → Z ∈ st.inv := by
  intro w
  induction w with
  | nil => intro Z hZ; exact hZ
  | cons l w ih =>
    intro Z hZ
    simp only [_root_.Formalism.FourierDecayAlt.Fr.ofWord] at hZ
    by_cases hl : l.plus = true
    · rw [if_pos hl] at hZ
      unfold _root_.Formalism.FourierDecayAlt.Fr.FrameData.plus at hZ
      exact ih Z (Set.mem_of_mem_inter_left hZ)
    · rw [if_neg hl] at hZ
      unfold _root_.Formalism.FourierDecayAlt.Fr.FrameData.minus at hZ
      exact ih Z (Set.mem_of_mem_inter_left hZ)

open MeasureTheory in
private lemma star_l0_sub_one_add_eq_m0_add {P : _root_.Formalism.FourierDecayAlt.M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] (d : _root_.Formalism.FourierDecayAlt.Q.NFData P A) (E : A) (Y : ℂ) (hYr : star Y = Y)
    (hstarD : _root_.Formalism.FourierDecayAlt.Fr.IsStarLevel d.L) (hsnab : star d.L.nab = d.L.nabs)
    (hcE : Commute (star E) (d.L.ζ * d.L.ζbi * d.L.GGi)) :
    star (d.L.l0 (Y - 1) + d.L.ζb * d.L.ζi * d.L.GGi * E) =
      d.L.m0 Y + d.L.ζ * d.L.ζbi * d.L.GGi * star E := by
  obtain ⟨-, hsζb, hsζi, -, -, hsGGi⟩ := _root_.Formalism.FourierDecayAlt.P.TLA.M2.star_fns d.L hstarD
  have hm0 : d.L.m0 Y = -d.L.nabs - algebraMap ℂ A (Y - 1 / 2) * (d.L.ζ * d.L.GGi) := rfl
  have hl0 : d.L.l0 (Y - 1) = -d.L.nab - algebraMap ℂ A (Y - 1 / 2) * (d.L.ζb * d.L.GGi) := by
    show -d.L.nab - algebraMap ℂ A (Y - 1 + 1 / 2) * (d.L.ζb * d.L.GGi) = _
    rw [show Y - 1 + 1 / 2 = Y - 1 / 2 by ring]
  have hsc : star (algebraMap ℂ A (Y - 1 / 2)) = algebraMap ℂ A (Y - 1 / 2) := by
    rw [← algebraMap_star_comm, star_sub, hYr]
    norm_num
  have hperm : d.L.GGi * d.L.ζbi * d.L.ζ = d.L.ζ * d.L.ζbi * d.L.GGi := by
    rw [_root_.Formalism.FourierDecayAlt.P.RuleGD.fc d.L (_root_.Formalism.FourierDecayAlt.P.RuleGD.m_GGi d.L) (_root_.Formalism.FourierDecayAlt.P.RuleGD.m_ζbi d.L), mul_assoc, _root_.Formalism.FourierDecayAlt.P.RuleGD.fc d.L (_root_.Formalism.FourierDecayAlt.P.RuleGD.m_GGi d.L) (_root_.Formalism.FourierDecayAlt.P.RuleGD.m_ζ d.L),
      ← mul_assoc, _root_.Formalism.FourierDecayAlt.P.RuleGD.fc d.L (_root_.Formalism.FourierDecayAlt.P.RuleGD.m_ζbi d.L) (_root_.Formalism.FourierDecayAlt.P.RuleGD.m_ζ d.L)]
  rw [hl0, hm0]
  simp only [star_add, star_sub, star_neg, star_mul, hsnab, hsζb, hsζi, hsGGi, hsc]
  congr 1
  · congr 1
    rw [_root_.Formalism.FourierDecayAlt.P.RuleGD.fc d.L (_root_.Formalism.FourierDecayAlt.P.RuleGD.m_GGi d.L) (_root_.Formalism.FourierDecayAlt.P.RuleGD.m_ζ d.L)]
    exact (Algebra.commutes _ _).symm
  · rw [← mul_assoc d.L.GGi, hperm]
    exact hcE.eq

open MeasureTheory in
variable {P : _root_.Formalism.FourierDecayAlt.M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] in
variable {S : Type} [Fintype S] [DecidableEq S] in
variable [StarModule ℂ A] in

theorem _root_.GlobalTheory.HatNF.MShapeNF.mshape : ∀ (P : _root_.Formalism.FourierDecayAlt.M.Par) (A : Type) [Ring A] [StarRing A]
    [Algebra ℂ A] [StarModule ℂ A] (d : _root_.Formalism.FourierDecayAlt.Q.NFData P A), _root_.GlobalTheory.HatNF.HatHyp d →
    ∀ (L : _root_.Formalism.FourierDecayAlt.R.LevelData A P.r) (st : _root_.Formalism.FourierDecayAlt.Fr.Start A) (s : ℂ), _root_.GlobalTheory.HatNF.Comparison₂ d L st s →
    ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (_root_.Formalism.FourierDecayAlt.Wd.Letter ℂ S), _root_.Formalism.FourierDecayAlt.Fr.admitted st w →
    ∀ Y ∈ (_root_.Formalism.FourierDecayAlt.Fr.ofWord L st w).inv, star Y = Y → Y - 1 ∈ (_root_.Formalism.FourierDecayAlt.Fr.ofWord L st w).inv →
    ∃ E : _root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A, (∀ e e', E e e' ∈ _root_.GlobalTheory.HatNF.nfSpan d ∅ 0 0 0) ∧
      (_root_.Formalism.FourierDecayAlt.Fr.ofWord L st w).m L Y = _root_.Formalism.FourierDecayAlt.Wd.io (d.L.m0 Y) + _root_.Formalism.FourierDecayAlt.Wd.io (d.L.ζ * d.L.ζbi * d.L.GGi) * E := by
  intro P A _ _ _ _ d hd L st s ht S _ _ w hw Y hY hYr hY1
  obtain ⟨hκ, hE⟩ := _root_.GlobalTheory.HatNF.start_normalForm P A d hd L st s ht
  have hA : _root_.Formalism.FourierDecayAlt.TL.AHyp L st := ht.1
  have hst : _root_.Formalism.FourierDecayAlt.Fr.IsLevelStart L st := hA.start
  have hsame : _root_.GlobalTheory.HatNF.SameFns L d.L := ht.2.1
  obtain ⟨-, -, -, -, -, -, hζ, hζi, hζb, hζbi, hGG, hGGi, hTT⟩ := hsame
  have hstarD : _root_.Formalism.FourierDecayAlt.Fr.IsStarLevel d.L := hd.2.1
  have hsnab : star d.L.nab = d.L.nabs := by
    unfold _root_.Formalism.FourierDecayAlt.Fr.IsStarLevel at hstarD
    exact hstarD.2.1
  have hrel : d.Rel := hd.2.2.1
  unfold _root_.Formalism.FourierDecayAlt.Q.NFData.Rel at hrel
  obtain ⟨-, hbm, -⟩ := _root_.GlobalTheory.HatNF.Den.hat_den P A d hd
  set B := _root_.GlobalTheory.HatNF.MShapeNF.bAlg d with hBdef
  have hBmem : ∀ x, x ∈ B ↔ x ∈ Submodule.span ℂ (_root_.GlobalTheory.HatNF.bmon d : Set A) := fun x => Iff.rfl
  have hB : ∀ x, x ∈ _root_.GlobalTheory.HatNF.nfSpan d ∅ 0 0 0 ↔ x ∈ B := by
    intro x
    have hset : {x | ∃ b ∈ _root_.GlobalTheory.HatNF.bmon d, ∃ H : List A, H.length = 0 ∧ (∀ h ∈ H, h ∈ (∅ : Set A)) ∧
        x = b * d.L.Di ^ 0 * _root_.Formalism.FourierDecayAlt.TL.gI d.L ^ 0 * H.prod} = (_root_.GlobalTheory.HatNF.bmon d : Set A) := by
      ext x
      constructor
      · rintro ⟨b, hb, H, hH, -, rfl⟩
        rw [List.length_eq_zero_iff] at hH
        subst hH
        simpa using hb
      · intro hx
        exact ⟨x, hx, [], rfl, by simp, by simp⟩
    unfold _root_.GlobalTheory.HatNF.nfSpan
    rw [hset, hBmem]
  have hgen : ∀ x ∈ _root_.GlobalTheory.HatNF.bset d, x ∈ B := by
    intro x hx
    apply Submodule.subset_span
    unfold _root_.GlobalTheory.HatNF.bmon
    exact Submonoid.subset_closure hx
  have hκB : ∀ f, d.κ f ∈ B := by
    intro f
    apply hgen
    unfold _root_.GlobalTheory.HatNF.bset
    exact Or.inl (Or.inl (Or.inr ⟨f, rfl⟩))
  have hζiB : d.L.ζi ∈ B := by
    apply hgen
    unfold _root_.GlobalTheory.HatNF.bset
    exact Or.inl (Or.inl (Or.inl (Or.inl (by simp))))
  have hstarB : ∀ x ∈ B, star x ∈ B := by
    intro x hx
    rw [hBmem] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ((hbm y hy).2.2.2)
    | zero => simp
    | add y z _ _ hy hz => rw [star_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [star_smul]; exact Submodule.smul_mem _ _ hy
  have hcommB : ∀ x ∈ B, ∀ f ∈ d.L.fns, Commute x f := by
    intro x hx f hf
    rw [hBmem] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact (hbm y hy).1 f hf
    | zero => exact Commute.zero_left f
    | add y z _ _ hy hz => exact hy.add_left hz
    | smul r y _ hy => exact hy.smul_left r
  have hEMmul : ∀ X Z : _root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A, (∀ i j, X i j ∈ B) → (∀ i j, Z i j ∈ B) → ∀ i j, (X * Z) i j ∈ B := by
    intro X Z hX hZ i j
    rw [Matrix.mul_apply]
    exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (hX i k) (hZ k j)
  have hEMsub : ∀ X Z : _root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A, (∀ i j, X i j ∈ B) → (∀ i j, Z i j ∈ B) → ∀ i j, (X - Z) i j ∈ B := by
    intro X Z hX hZ i j
    rw [Matrix.sub_apply]
    exact Subalgebra.sub_mem _ (hX i j) (hZ i j)
  have hEMio : ∀ a ∈ B, ∀ i j, (_root_.Formalism.FourierDecayAlt.Wd.io a : _root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A) i j ∈ B := by
    intro a ha i j
    by_cases h : i = j
    · subst h
      simpa [_root_.Formalism.FourierDecayAlt.Wd.io] using ha
    · simp [_root_.Formalism.FourierDecayAlt.Wd.io, Matrix.diagonal_apply_ne _ h]
  have hkκ : ∀ γ : _root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A, _root_.Formalism.FourierDecayAlt.TL.kMat st γ → ∀ i j, ∃ f, d.κ f = γ i j := by
    intro γ hγ i j
    unfold _root_.Formalism.FourierDecayAlt.TL.kMat at hγ
    exact hκ _ (hγ i j)
  have hkB : ∀ γ : _root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A, _root_.Formalism.FourierDecayAlt.TL.kMat st γ → ∀ i j, γ i j ∈ B := by
    intro γ hγ i j
    obtain ⟨f, hf⟩ := hkκ γ hγ i j
    rw [← hf]
    exact hκB f
  have hζf := _root_.Formalism.FourierDecayAlt.P.RuleGD.m_ζ d.L
  have hζbif := _root_.Formalism.FourierDecayAlt.P.RuleGD.m_ζbi d.L
  have hGGif := _root_.Formalism.FourierDecayAlt.P.RuleGD.m_GGi d.L
  have hfns : ∀ x ∈ d.L.fns, ∀ f, Commute (d.κ f) x := fun x hx f => hrel.2.1 f x (Or.inl hx)
  set c := d.L.ζ * d.L.ζbi * d.L.GGi with hc
  have hcκ : ∀ f, Commute (d.κ f) c := fun f =>
    ((hfns _ hζf f).mul_right (hfns _ hζbif f)).mul_right (hfns _ hGGif f)
  have hm0 : d.L.m0 Y = -d.L.nabs - algebraMap ℂ A (Y - 1 / 2) * (d.L.ζ * d.L.GGi) := rfl
  have hmκ : ∀ f, Commute (d.κ f) (d.L.m0 Y) := by
    intro f
    rw [hm0]
    exact (hrel.2.1 f _ (Or.inr (by simp))).neg_right.sub_right
      ((Algebra.commute_algebraMap_right _ _).mul_right ((hfns _ hζf f).mul_right (hfns _ hGGif f)))
  have hinv := mem_inv_of_mem_ofWord_inv (S := S) L st
  obtain ⟨E, hEmem, hEeq⟩ := hE (Y - 1) (hinv w _ hY1)
  have hEB : E ∈ B := (hB E).1 hEmem
  have hsEB : star E ∈ B := hstarB E hEB
  have hcE : Commute (star E) c := ((hcommB _ hsEB _ hζf).mul_right (hcommB _ hsEB _ hζbif)).mul_right
    (hcommB _ hsEB _ hGGif)
  have hs := star_l0_sub_one_add_eq_m0_add d E Y hYr hstarD hsnab hcE
  have hM0 : _root_.Formalism.FourierDecayAlt.Fr.FrameData.m L (st.frame : _root_.Formalism.FourierDecayAlt.Fr.FrameData S A) Y =
      _root_.Formalism.FourierDecayAlt.Wd.io (d.L.m0 Y) + _root_.Formalism.FourierDecayAlt.Wd.io c * _root_.Formalism.FourierDecayAlt.Wd.io (star E) := by
    rw [_root_.Formalism.FourierDecayAlt.P.TLA.M2.frame_m L st Y, _root_.Formalism.FourierDecayAlt.P.TLA.M2.frame_l L st (Y - 1), _root_.Formalism.FourierDecayAlt.P.TLA.M2.io_star, hEeq, hs, _root_.Formalism.FourierDecayAlt.P.TLA.M2.io_add, _root_.Formalism.FourierDecayAlt.P.TLA.M2.io_mul]
  have hJ := _root_.Formalism.FourierDecayAlt.P.m_shape_of_l_shape A S P.r L st w hA.starLev hst hw Y hY hYr hY1
  rw [hζ, hζbi, hGGi, hTT, hζi] at hJ
  let W : Submodule ℂ (_root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A) :=
    { carrier := {Z | ∃ X : _root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A, (∀ i j, X i j ∈ B) ∧ Z = _root_.Formalism.FourierDecayAlt.Wd.io c * X}
      add_mem' := by
        rintro _ _ ⟨X, hX, rfl⟩ ⟨Z, hZ, rfl⟩
        exact ⟨X + Z, fun i j => Subalgebra.add_mem _ (hX i j) (hZ i j), (Matrix.mul_add _ _ _).symm⟩
      zero_mem' := ⟨0, fun i j => Subalgebra.zero_mem _, (Matrix.mul_zero _).symm⟩
      smul_mem' := by
        rintro r _ ⟨X, hX, rfl⟩
        exact ⟨r • X, fun i j => Subalgebra.smul_mem _ (hX i j) r, (Matrix.mul_smul _ r X).symm⟩ }
  have hcomm : ∀ (a : A), (∀ f, Commute (d.κ f) a) → ∀ γ : _root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A, _root_.Formalism.FourierDecayAlt.TL.kMat st γ →
      Commute (_root_.Formalism.FourierDecayAlt.Wd.io a) γ := by
    intro a ha γ hγ
    apply _root_.Formalism.FourierDecayAlt.P.TLA.M2.io_comm
    intro i j
    obtain ⟨f, hf⟩ := hkκ γ hγ i j
    rw [← hf]
    exact (ha f).symm
  have hW : _root_.Formalism.FourierDecayAlt.TL.dSpan st (_root_.Formalism.FourierDecayAlt.Fr.FrameData.m L (st.frame : _root_.Formalism.FourierDecayAlt.Fr.FrameData S A) Y) (_root_.Formalism.FourierDecayAlt.Wd.io c)
      (_root_.Formalism.FourierDecayAlt.Wd.io (d.L.TT • d.L.ζi)) ≤ W := by
    unfold _root_.Formalism.FourierDecayAlt.TL.dSpan
    rw [Submodule.span_le]
    rintro Z (⟨α, β, γ, hα, hβ, hγ, rfl⟩ | ⟨γ, hγ, rfl | rfl⟩)
    · have hcβ := hcomm c hcκ β hβ
      have hcα := hcomm c hcκ α hα
      have hmβ := hcomm _ hmκ β hβ
      refine ⟨α * (_root_.Formalism.FourierDecayAlt.Wd.io (star E) * β - β * _root_.Formalism.FourierDecayAlt.Wd.io (star E)) * γ,
        hEMmul _ _ (hEMmul _ _ (hkB α hα) (hEMsub _ _ (hEMmul _ _ (hEMio _ hsEB) (hkB β hβ))
          (hEMmul _ _ (hkB β hβ) (hEMio _ hsEB)))) (hkB γ hγ), ?_⟩
      have h1 : (_root_.Formalism.FourierDecayAlt.Wd.io (d.L.m0 Y) + _root_.Formalism.FourierDecayAlt.Wd.io c * _root_.Formalism.FourierDecayAlt.Wd.io (star E)) * β -
          β * (_root_.Formalism.FourierDecayAlt.Wd.io (d.L.m0 Y) + _root_.Formalism.FourierDecayAlt.Wd.io c * _root_.Formalism.FourierDecayAlt.Wd.io (star E)) =
          _root_.Formalism.FourierDecayAlt.Wd.io c * (_root_.Formalism.FourierDecayAlt.Wd.io (star E) * β - β * _root_.Formalism.FourierDecayAlt.Wd.io (star E)) := by
        rw [add_mul, mul_add, hmβ.eq, ← mul_assoc β, ← hcβ.eq]
        simp only [mul_sub, mul_assoc]
        abel
      rw [hM0, h1, ← mul_assoc α, ← hcα.eq]
      simp only [mul_assoc]
    · exact ⟨γ, hkB γ hγ, rfl⟩
    · exact ⟨_root_.Formalism.FourierDecayAlt.Wd.io (d.L.TT • d.L.ζi) * γ,
        hEMmul _ _ (hEMio _ (Subalgebra.smul_mem _ hζiB _)) (hkB γ hγ), mul_assoc _ _ _⟩
  obtain ⟨X, hX, hXeq⟩ := hW hJ
  refine ⟨_root_.Formalism.FourierDecayAlt.Wd.io (star E) + X,
    fun i j => (hB _).2 (Subalgebra.add_mem _ (hEMio _ hsEB i j) (hX i j)), ?_⟩
  rw [mul_add, ← add_assoc, ← hM0, ← hXeq]
  abel

end GlobalTheory.HatNF.MShapeNF
