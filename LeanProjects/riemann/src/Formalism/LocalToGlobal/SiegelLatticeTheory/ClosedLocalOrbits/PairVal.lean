import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal
import Formalism.LocalRingCardinality.DataTies
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
import Formalism.HermitianCurvature.StatementPB
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex
import Formalism.SharpRestriction.CuspSpanNormBounds.FrameFixingOrbitRelation

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.PairVal

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mass

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def AutFin : Prop := ∀ Λ ∈ what₂, (autLz D F0 Λ).Finite

def massRow (Λ : Submodule (𝓞 D.host.E) (VS D).V) : ℝ := wRow D F0 Λ / Cnt.massRows D F0 what₂

theorem one_mem_autLz (Λ : Submodule (𝓞 D.host.E) (VS D).V) : (id : WbQ D F0 → WbQ D F0) ∈ autLz D F0 Λ := by
  unfold autLz
  rw [Set.mem_setOf_eq]
  refine ⟨1, ?_, ?_, fun x hx => rfl⟩
  · first
      | exact Subgroup.one_mem _
      | exact one_mem _
      | (unfold stabF; simp)
  · first
      | simp [Formalism.HermitianLatticesTheory.gmap]
      | rfl

theorem wRow_pos {Λ : Submodule (𝓞 D.host.E) (VS D).V} (h : (autLz D F0 Λ).Finite) : 0 < wRow D F0 Λ := by
  unfold wRow
  have hne : (autLz D F0 Λ).Nonempty := ⟨_, one_mem_autLz D F0 Λ⟩
  have hc : 0 < Nat.card (autLz D F0 Λ) := Nat.card_pos_iff.mpr ⟨hne.to_subtype, h.to_subtype⟩
  exact inv_pos.mpr (Nat.cast_pos.mpr hc)

theorem massRows_pos (hA : AutFin D F0 what₂) (hne : what₂.Nonempty) : 0 < Cnt.massRows D F0 what₂ := by
  unfold Cnt.massRows
  exact Finset.sum_pos (fun Λ hΛ => wRow_pos D F0 (hA Λ hΛ)) hne

theorem sum_massRow (hA : AutFin D F0 what₂) (hne : what₂.Nonempty) : ∑ Λ ∈ what₂, massRow D F0 what₂ Λ = 1 := by
  have hpos := massRows_pos D F0 what₂ hA hne
  have hm : ∑ Λ ∈ what₂, wRow D F0 Λ = Cnt.massRows D F0 what₂ := rfl
  unfold massRow
  rw [← Finset.sum_div, hm, div_self hpos.ne']

end Mass

section TermMass

variable {D : D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def massTerm (t : Term D u u' F0 what₂) : ℝ := massRow D F0 what₂ t.lam

theorem term_mass_eq_weight_ratio (t : Term D u u' F0 what₂) : massTerm t = wRow D F0 t.lam / Cnt.massRows D F0 what₂ := rfl

theorem massTerm_pos (hA : AutFin D F0 what₂) (t : Term D u u' F0 what₂) : 0 < massTerm t :=
  div_pos (wRow_pos D F0 (hA _ t.mem)) (massRows_pos D F0 what₂ hA ⟨_, t.mem⟩)

end TermMass

section Phase

variable {E : Type} [Field E] [NumberField E]

def psiInf (g : ℕ) (x : E) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ) / (g : ℂ)))

def sgUp {N : ℕ} (U : Matrix (Fin N) (Fin N) E) : E :=
  ∑ a : Fin N, if h : a.val + 1 < N then U a ⟨a.val + 1, h⟩ else 0

def sgLo {N : ℕ} (L : Matrix (Fin N) (Fin N) E) : E :=
  ∑ a : Fin N, if h : a.val + 1 < N then L ⟨a.val + 1, h⟩ a else 0

def phasePair {N : ℕ} (g : ℕ) (L U : Matrix (Fin N) (Fin N) E) : ℂ :=
  (psiInf g (sgLo L))⁻¹ * (psiInf g (sgUp U))⁻¹

theorem norm_psiInf (g : ℕ) (x : E) : ‖psiInf g x‖ = 1 := by
  unfold psiInf
  first
    | (rw [Complex.norm_exp]; simp)
    | (rw [Complex.abs_exp]; simp)
    | simp [Complex.norm_exp]

theorem norm_phasePair {N : ℕ} (g : ℕ) (L U : Matrix (Fin N) (Fin N) E) : ‖phasePair g L U‖ = 1 := by
  unfold phasePair
  rw [norm_mul, norm_inv, norm_inv, norm_psiInf, norm_psiInf]
  norm_num

end Phase

section Coef

variable {D : D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

abbrev MatR (D : D7) : Type := Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E

def NormRep (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D) : Prop :=
  Rep t.lam (lf D F0) (PD D t.lam (lf D F0) u') t.cls F' ∧ AdmWit t.lam (gS D) (lf D F0) F' 1 ∧
    IsLoUni L ∧ IsUpUni U ∧ ZhatOM (ZhatL (lf D F0) F') = L * ptMat w * U

def phaseAt (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) : ℂ :=
  if h : ∃ x : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × MatR D × MatR D, NormRep t w x.1 x.2.1 x.2.2 then
    phasePair (gS D) h.choose.2.1 h.choose.2.2
  else 0

theorem norm_phaseAt_le (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) : ‖phaseAt t w‖ ≤ 1 := by
  unfold phaseAt
  split_ifs
  · rw [norm_phasePair]
  · simp

def cAt (vR : Term D u u' F0 what₂ → ℝ) (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) : ℂ :=
  phaseAt t w * (vR t : ℂ)

def BigCell {i : ℕ} (w : Point D.host.E i) : Prop := ∀ b ∈ w.1, b.2 = 1

variable (D u u' F0 what₂)

def NormRepExists : Prop :=
  ∀ (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), t.atPt w → t.relevant → t.generic →
    ∃ x : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × MatR D × MatR D, NormRep t w x.1 x.2.1 x.2.2

def PhaseWellDef : Prop :=
  ∀ (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), t.relevant →
    ∀ (F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L₁ U₁ L₂ U₂ : MatR D),
      NormRep t w F₁ L₁ U₁ → NormRep t w F₂ L₂ U₂ → phasePair (gS D) L₁ U₁ = phasePair (gS D) L₂ U₂

def orbT (t : Term D u u' F0 what₂) (Z : MatR D) : Set (Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))) :=
  {O | ∃ F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 t.lam Z,
    Rep t.lam (lf D F0) (PD D t.lam (lf D F0) u') t.cls F' ∧
    O = {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 t.lam Z ∧ CntLocal.NilradicalFlagMoved F0 t.lam F' F''}}

def VolOK (vR : Term D u u' F0 what₂ → ℝ) : Prop :=
  (∀ t, 0 < vR t) ∧
  (∀ (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), t.atPt w → BigCell w → vR t = 1) ∧
  ∃ wt : MatR D → ℝ, ∀ (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D),
    t.relevant → t.generic → NormRep t w F' L U →
      vR t = ((orbT D u u' F0 what₂ t (ZhatL (lf D F0) F')).ncard : ℝ) * wt (ZhatL (lf D F0) F')

end Coef

section VolDef

variable (D u u' F0 what₂)

abbrev GLR (D : D7) : Type := Matrix.GeneralLinearGroup (Fin (D.R.rS + 1)) D.host.E

def stabIntSet (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (w : Point D.host.E (D.R.rS + 1)) : Set (GLR D) :=
  {a | IsLoUni (a : MatR D) ∧ ∃ b : MatR D, IsUpUni b ∧ (a : MatR D) * ptMat w * b = ptMat w ∧
    ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, ∃ l ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      Formalism.MainNotions.S.TieN.IntLow (M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (M p) ρ ∧
      ∀ Z : MatR D, CntLocal.ZZP (M := M) δ u u' p (ZhatOM ((a : MatR D) * ZhatOM Z * b)) =
        l * CntLocal.ZZP (M := M) δ u u' p Z * ρ}

def stabInt (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (w : Point D.host.E (D.R.rS + 1)) : Subgroup (GLR D) :=
  Subgroup.closure (stabIntSet D u u' δ M w)

def stabAutSet (t : Term D u u' F0 what₂) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L : MatR D) :
    Set (GLR D) :=
  {a | ∃ s ∈ NLam t.lam (lf D F0) ∩ NLam t.lam F', ∃ uu : MatR D,
    (∀ b, s (frame (lf D F0) b) = ∑ c, uu c b • frame (lf D F0) c) ∧ (a : MatR D) = L⁻¹ * uu.conjTranspose * L}

def stabAut (t : Term D u u' F0 what₂) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L : MatR D) :
    Subgroup (GLR D) :=
  Subgroup.closure (stabAutSet D u u' F0 what₂ t F' L)

def volIdx (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L : MatR D) : ℝ :=
  ((stabAut D u u' F0 what₂ t F' L).relIndex (stabInt D u u' δ M w) : ℝ) /
    ((stabInt D u u' δ M w).relIndex (stabAut D u u' F0 what₂ t F' L) : ℝ)

def vRdef (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (t : Term D u u' F0 what₂) : ℝ :=
  if h : t.relevant ∧ t.generic ∧
      ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × MatR D × MatR D,
        NormRep t x.1 x.2.1 x.2.2.1 x.2.2.2 then
    volIdx D u u' F0 what₂ δ M t h.2.2.choose.1 h.2.2.choose.2.1 h.2.2.choose.2.2.1
  else 1

def VolIdxFin (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) : Prop :=
  (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) → ∀ (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D),
    t.relevant → t.generic → NormRep t w F' L U →
      (stabAut D u u' F0 what₂ t F' L).relIndex (stabInt D u u' δ M w) ≠ 0 ∧
      (stabInt D u u' δ M w).relIndex (stabAut D u u' F0 what₂ t F' L) ≠ 0

def VolIdxWellDef (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) : Prop :=
  (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) → ∀ (t : Term D u u' F0 what₂) (w₁ w₂ : Point D.host.E (D.R.rS + 1))
    (F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L₁ U₁ L₂ U₂ : MatR D),
    t.relevant → t.generic → NormRep t w₁ F₁ L₁ U₁ → NormRep t w₂ F₂ L₂ U₂ →
      volIdx D u u' F0 what₂ δ M t w₁ F₁ L₁ = volIdx D u u' F0 what₂ δ M t w₂ F₂ L₂

def VolDefOK (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) : Prop :=
  (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) → VolOK D u u' F0 what₂ (vRdef D u u' F0 what₂ δ M)

end VolDef

section Pt

variable {D : D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def junkPoint (D : D7) (u u' : D.what₂.Word) : Point D.host.E (D.R.rS + 1) :=
  (Formalism.MainNotions.S.Inh.zero_of_gram_point_exists D u u').choose

theorem Gpt_junkPoint_eq_zero (D : D7) (u u' : D.what₂.Word) :
    Formalism.MainNotions.S.LocalSplitGroups.Gpt (D.mem u).A.T (D.mem u').A.T (junkPoint D u u') = 0 := by
  exact (Formalism.MainNotions.S.Inh.zero_of_gram_point_exists D u u').choose_spec

def ptOf (t : Term D u u' F0 what₂) : Point D.host.E (D.R.rS + 1) :=
  if h : ∃ w, t.atPt w ∧ t.relevant then h.choose else junkPoint D u u'

theorem ptOf_spec (t : Term D u u' F0 what₂) (h : ∃ w, t.atPt w ∧ t.relevant) : t.atPt (ptOf t) := by
  unfold ptOf
  rw [dif_pos h]
  exact h.choose_spec.1

theorem ptOf_GPoint_iff (hA : ∀ t : Term D u u' F0 what₂, t.G ≠ 0 → t.relevant → ∃ w, t.atPt w)
    (hB : ∀ (t : Term D u u' F0 what₂) w, t.atPt w → Formalism.MainNotions.S.LocalSplitGroups.Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0)
    (hC : ∀ (t : Term D u u' F0 what₂) w, t.atPt w → t.G ≠ 0) (t : Term D u u' F0 what₂) :
    (t.G ≠ 0 ∧ t.relevant) ↔ Formalism.MainNotions.S.LocalSplitGroups.Gpt (D.mem u).A.T (D.mem u').A.T (ptOf t) ≠ 0 := by
  constructor
  · rintro ⟨hG, hr⟩
    obtain ⟨w, hw⟩ := hA t hG hr
    exact hB t _ (ptOf_spec t ⟨w, hw, hr⟩)
  · intro hne
    by_cases h : ∃ w, t.atPt w ∧ t.relevant
    · exact ⟨hC t _ (ptOf_spec t h), h.choose_spec.2⟩
    · exfalso
      apply hne
      unfold ptOf
      rw [dif_neg h]
      exact Gpt_junkPoint_eq_zero D u u'

def cTerm (vR : Term D u u' F0 what₂ → ℝ) (t : Term D u u' F0 what₂) : ℂ :=
  if h : ∃ w, t.atPt w then cAt vR t h.choose else 0

theorem cTerm_of_atPt (vR : Term D u u' F0 what₂ → ℝ) (t : Term D u u' F0 what₂) {w : Point D.host.E (D.R.rS + 1)}
    (hw : t.atPt w) (hU : ∀ w', t.atPt w' → w' = w) : cTerm vR t = cAt vR t w := by
  have h : ∃ w, t.atPt w := ⟨w, hw⟩
  unfold cTerm
  rw [dif_pos h, hU _ h.choose_spec]

variable (D u u' F0 what₂)

def CellPtUnique : Prop :=
  ∀ (t : Term D u u' F0 what₂) (w w' : Point D.host.E (D.R.rS + 1)), t.atPt w → t.atPt w' → w = w'

end Pt

section Count

variable (D : D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def meanCount (w : Point D.host.E (D.R.rS + 1)) : ℝ :=
  CntLocal.nu (D := D) (CntLocal.Tn u') F0 what₂ (ZhatOM (ptMat w))

end Count

section Vol

def volHOf {X : Type*} [MeasurableSpace X] (μ : Measure X) : ℝ := (μ Set.univ).toReal

def volNOf {X : Type*} [MeasurableSpace X] (μ : Measure X) (NO : Set X) : ℝ := ((μ NO).toReal)⁻¹

variable (D : D7)

def CdTieAt (n : ℕ) (ε : Fin n → Bool) (c : NNReal) : Prop :=
  ∀ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
      ((c : ENNReal) • Formalism.REAL.muG ε) A =
        D.cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}

def cdScaleOf (n : ℕ) (ε : Fin n → Bool) : NNReal :=
  if h : ∃ c : NNReal, 0 < c ∧ CdTieAt D n ε c then h.choose else 1

def CdScaleExists : Prop := ∀ n (ε : Fin n → Bool), ∃ c : NNReal, 0 < c ∧ CdTieAt D n ε c

theorem cdScaleOf_tie (h : CdScaleExists D) (n : ℕ) (ε : Fin n → Bool) :
    0 < cdScaleOf D n ε ∧ CdTieAt D n ε (cdScaleOf D n ε) := by
  unfold cdScaleOf
  rw [dif_pos (h n ε)]
  exact (h n ε).choose_spec

theorem cdScaleExists_of_tie (h : Formalism.BasicNotions.cdScaleTie D) : CdScaleExists D := by
  unfold Formalism.BasicNotions.cdScaleTie at h
  intro n ε
  exact ⟨D.s.cdScale n ε, D.s.cdScale_pos n ε, fun P Q e h1 h2 A hA => h n ε P Q e h1 h2 A hA⟩

end Vol

section Pairs

variable {D : D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (D u u' F0 what₂) in

structure PairSys : Type 1 where
  P : Type
  fst : P → Term D u u' F0 what₂
  snd : P → Term D u u' F0 what₂
  row : ∀ p, (fst p).lam = (snd p).lam
  inj : Function.Injective (fun p => (fst p, snd p))
  gscal : P → Prop

def gsAt (Q : PairSys D u u' F0 what₂) (w w' : Point D.host.E (D.R.rS + 1)) : Set Q.P :=
  {p | Q.gscal p ∧ (Q.fst p).atPt w ∧ (Q.snd p).atPt w'}

def KgsOf (vR : Term D u u' F0 what₂ → ℝ) (Q : PairSys D u u' F0 what₂) (w w' : Point D.host.E (D.R.rS + 1)) : ℂ :=
  ∑' p : gsAt Q w w', (massTerm (Q.fst p.1) : ℂ) * cAt vR (Q.fst p.1) w * star (cAt vR (Q.snd p.1) w')

variable (Q : PairSys D u u' F0 what₂)

theorem massTerm_pair (p : Q.P) : massTerm (Q.fst p) = massTerm (Q.snd p) := by
  unfold massTerm
  rw [Q.row p]

def KgsFinite : Prop := ∀ w w' : Point D.host.E (D.R.rS + 1), (gsAt Q w w').Finite

theorem Kgs_fin (vR : Term D u u' F0 what₂ → ℝ) (hF : KgsFinite Q) (w w' : Point D.host.E (D.R.rS + 1)) :
    KgsOf vR Q w w' = ∑ p ∈ (hF w w').toFinset,
      (massTerm (Q.fst p) : ℂ) * cAt vR (Q.fst p) w * star (cAt vR (Q.snd p) w') := by
  unfold KgsOf
  rw [← Finset.tsum_subtype', Set.Finite.coe_toFinset]

variable {H₁ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [FiniteDimensional ℂ H₁]
  {H₂ : Type} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

def pvalOf (vR : Term D u u' F0 what₂ → ℝ) (A : Term D u u' F0 what₂ → (H₁ →L[ℂ] H₂)) (p : Q.P) : ℂ :=
  (wRow D F0 (Q.fst p).lam : ℂ) * cTerm vR (Q.fst p) * star (cTerm vR (Q.snd p)) *
    hsInner (A (Q.fst p)) (A (Q.snd p))

def FormGS (vR : Term D u u' F0 what₂ → ℝ) (A : Term D u u' F0 what₂ → (H₁ →L[ℂ] H₂))
    (V : Point D.host.E (D.R.rS + 1) → (H₁ →L[ℂ] H₂)) (Gam1 : ℝ) : Prop :=
  CellPtUnique D u u' F0 what₂ → (∀ t w, t.atPt w → A t = V w) →
    Summable (fun p : {p : Q.P // Q.gscal p} => ‖pvalOf Q vR A p.1‖) ∧
    Summable (fun ww : Point D.host.E (D.R.rS + 1) × Point D.host.E (D.R.rS + 1) =>
      KgsOf vR Q ww.1 ww.2 * hsInner (V ww.1) (V ww.2)) ∧
    ((Gam1 : ℂ) * ∑' p : {p : Q.P // Q.gscal p}, pvalOf Q vR A p.1) =
      ((Gam1 * Cnt.massRows D F0 what₂ : ℝ) : ℂ) *
        ∑' ww : Point D.host.E (D.R.rS + 1) × Point D.host.E (D.R.rS + 1),
          KgsOf vR Q ww.1 ww.2 * hsInner (V ww.1) (V ww.2)

def PairSumJoint {τ Rw I K₁ K₂ : Type} [Fintype I] [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁]
    [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I K₁ K₂) (Qτ : Set (τ × τ))
    (vR : Term D u u' F0 what₂ → ℝ) (A : Term D u u' F0 what₂ → (H₁ →L[ℂ] H₂)) : Prop :=
  X.pairSum Qτ = X.Gam1 * ∑' p : {p : Q.P // Q.gscal p}, (pvalOf Q vR A p.1).re ∧
  X.pairAbs Qτ = X.Gam1 * ∑' p : {p : Q.P // Q.gscal p}, ‖pvalOf Q vR A p.1‖

end Pairs

end Formalism.L2.SG.PairVal
