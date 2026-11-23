import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SupportDatum.DeterminantFormIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalOrbitGerms
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelNonzeroModulusDeterminantEq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ProdFormulaE
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfProductFormula
import Development.AutomorphicArithmetic.BlochKatoExtensions.FundamentalExactSequenceContinuityAllTheories
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtB

noncomputable section

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.FourierDecayAlt Formalism.L2.SG.DataInst
open Classical ValuativeRel

namespace Formalism.L2.SG.Pf.LMK

section Lists

theorem signFlip_append {K : Type} [Field K] (r : ℕ) : ∀ (b : ℕ) (l1 l2 : TB.Pt K),
    signAux r b (l1 ++ l2) = signAux r b l1 ++ signAux r (b + TB.level l1) l2
  | b, [], l2 => by simp [signAux, TB.level]
  | b, (s, t) :: rest, l2 => by
    rw [List.cons_append, signAux, signAux, signFlip_append r (b + s) rest l2]
    simp [TB.level, add_assoc]

theorem signPt_join {K : Type} [Field K] (r : ℕ) (h : TB.Pt K) (s : ℕ) (t : K) :
    signPt r (TB.join h s t) = signPt r h ++ [(s, (-1) ^ (r + 1 - (1 + TB.level h + s - 1)) * t)] := by
  unfold signPt TB.join
  rw [signFlip_append]
  simp [signAux]

theorem isPtL_append {K : Type} [Field K] (l : List (ℕ × K)) (s : ℕ) (t : K) (m : ℕ)
    (hl : (l.map Prod.fst).sum = m) :
    Formalism.L2.S.IsPtL (l ++ [(s, t)]) (m + s) ↔ Formalism.L2.S.IsPtL l m ∧ 1 ≤ s ∧ t ≠ 0 := by
  unfold Formalism.L2.S.IsPtL
  constructor
  · rintro ⟨-, h2⟩
    exact ⟨⟨hl, fun b hb => h2 b (List.mem_append_left _ hb)⟩, (h2 (s, t) (by simp)).1, (h2 (s, t) (by simp)).2⟩
  · rintro ⟨⟨-, h2⟩, hs, ht⟩
    refine ⟨by simp [hl], fun b hb => ?_⟩
    rcases List.mem_append.1 hb with hb | hb
    · exact h2 b hb
    · simp only [List.mem_singleton] at hb
      subst hb
      exact ⟨hs, ht⟩

variable {D : Formalism.BasicNotions.D7}

theorem ptOfList_some {i : ℕ} {x : TB.Pt D.host.E} {w : Point D.host.E i} (h : ptOfList i x = some w) :
    Formalism.L2.S.IsPtL (signPt D.R.rS x) i ∧ w.1 = (signPt D.R.rS x).map Prod.swap := by
  unfold ptOfList at h
  split_ifs at h with hx
  simp only [Option.some.injEq] at h
  subst h
  exact ⟨hx, rfl⟩

theorem ptOfList_of {i : ℕ} {x : TB.Pt D.host.E} (hx : Formalism.L2.S.IsPtL (signPt D.R.rS x) i) :
    ∃ w, ptOfList i x = some w ∧ w.1 = (signPt D.R.rS x).map Prod.swap := by
  refine ⟨(Formalism.L2.S.ptEquiv D.host.E i).symm ⟨signPt D.R.rS x, hx⟩, ?_, rfl⟩
  unfold ptOfList
  rw [dif_pos hx]

theorem ptOfList_none {i : ℕ} {x : TB.Pt D.host.E} (hx : ¬ Formalism.L2.S.IsPtL (signPt D.R.rS x) i) :
    ptOfList i x = none := by
  unfold ptOfList
  rw [dif_neg hx]

def sgn (D : Formalism.BasicNotions.D7) (i : ℕ) : D.host.E := (-1) ^ (D.R.rS + 1 - i)

theorem sgn_ne (i : ℕ) : sgn D i ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)

theorem ptOfList_join {m s : ℕ} {h : TB.Pt D.host.E} (hl : TB.level h = m) {w : Point D.host.E m}
    (hw : ptOfList m h = some w) (hs : 1 ≤ s) {t : D.host.E} (ht : t ≠ 0) :
    ∃ W : Point D.host.E (m + s), ptOfList (m + s) (TB.join h s t) = some W ∧
      W.1 = w.1 ++ [(sgn D (m + s) * t, s)] := by
  obtain ⟨hp, hw1⟩ := ptOfList_some hw
  have hfst : ((signPt D.R.rS h).map Prod.fst).sum = m := by
    unfold signPt; rw [sign_list_fst]; exact hl
  have hsg : sgn D (m + s) * t ≠ 0 := mul_ne_zero (sgn_ne _) ht
  have e1 : D.R.rS + 1 - (1 + TB.level h + s - 1) = D.R.rS + 1 - (m + s) := by rw [hl]; congr 1; omega
  have hP : Formalism.L2.S.IsPtL (signPt D.R.rS (TB.join h s t)) (m + s) := by
    rw [signPt_join, e1]
    exact (isPtL_append _ s _ m hfst).2 ⟨hp, hs, hsg⟩
  obtain ⟨W, hW, hW1⟩ := ptOfList_of hP
  refine ⟨W, hW, ?_⟩
  rw [hW1, signPt_join, e1, List.map_append, ← hw1]
  rfl

theorem ptOfList_join_none {m s : ℕ} {h : TB.Pt D.host.E} (hl : TB.level h = m)
    (hw : ptOfList m h = none) (t : D.host.E) : ptOfList (m + s) (TB.join h s t) = none := by
  apply ptOfList_none
  intro hP
  have hfst : ((signPt D.R.rS h).map Prod.fst).sum = m := by
    unfold signPt; rw [sign_list_fst]; exact hl
  have e1 : D.R.rS + 1 - (1 + TB.level h + s - 1) = D.R.rS + 1 - (m + s) := by rw [hl]; congr 1; omega
  rw [signPt_join, e1] at hP
  obtain ⟨w, hw', -⟩ := ptOfList_of ((isPtL_append _ s _ m hfst).1 hP).1
  rw [hw] at hw'
  cases hw'

theorem blockProduct_append (i : ℕ) : ∀ (b : ℕ) (l1 l2 : TB.Pt D.host.E),
    blockWeightPhi (D := D) i b (l1 ++ l2) = blockWeightPhi i b l1 * blockWeightPhi i (b + TB.level l1) l2
  | b, [], l2 => by simp [blockWeightPhi, TB.level]
  | b, (s, t) :: rest, l2 => by
    rw [List.cons_append, blockWeightPhi, blockWeightPhi, blockProduct_append i (b + s) rest l2]
    simp only [TB.level, List.map_cons, List.sum_cons, add_assoc, mul_assoc]

def blkN (D : Formalism.BasicNotions.D7) : ℕ → TB.Pt D.host.E → ℝ
  | _, [] => 1
  | b, (s, t) :: rest => nrm (D := D) (nu D.R.rS b (b + s - 1)) t ^ s * blkN D (b + s) rest

theorem blockProduct_shift (m k : ℕ) : ∀ (b : ℕ) (l : TB.Pt D.host.E), b + TB.level l ≤ m + 1 →
    blockWeightPhi (D := D) (m + k) b l = blockWeightPhi m b l * blkN D b l ^ k
  | b, [], _ => by simp [blockWeightPhi, blkN]
  | b, (s, t) :: rest, hle => by
    simp only [TB.level, List.map_cons, List.sum_cons] at hle
    have ih := blockProduct_shift m k (b + s) rest (by simp only [TB.level]; omega)
    rw [blockWeightPhi, blockWeightPhi, blkN, ih]
    have hj : m + k - (b + s - 1) = (m - (b + s - 1)) + k := by omega
    rw [hj]
    have e : s * (m - (b + s - 1) + k) + s * (s - 1) / 2 = (s * (m - (b + s - 1)) + s * (s - 1) / 2) + s * k := by
      ring
    rw [e, pow_add, pow_mul, mul_pow]
    ring

theorem modBlocks_append {A B : Type} [Monoid B] (f : ℕ → ℕ → A → B) : ∀ (a : ℕ) (l1 l2 : List (A × ℕ)),
    modBlocks f a (l1 ++ l2) =
      (modBlocks f a l1).bind (fun x => (modBlocks f (a + (l1.map Prod.snd).sum) l2).map (fun y => x ++ y))
  | a, [], l2 => by simp [modBlocks]
  | a, (t, s) :: rest, l2 => by
    simp only [List.cons_append, modBlocks]
    split_ifs with h
    · rw [modBlocks_append f (a + s) rest l2]
      simp only [List.map_cons, List.sum_cons, ← add_assoc]
      cases h2 : modBlocks f (a + s) rest with
      | none => simp
      | some x =>
        cases h3 : modBlocks f (a + s + (rest.map Prod.snd).sum) l2 with
        | none => simp
        | some y => simp
    · simp

theorem modPt_blocks {δ : ∀ p : PlF D, (D.s.atP p).Fp} {T T' : ℕ} {p : PlF D} {n : ℕ} {w : Point D.host.E n}
    {a : Loc.Pt (D.s.atP p).Ep n} (ha : modPt δ T T' p w = some a) :
    modBlocks (blkTop δ T T' p) 1 w.1 = some a.blocks := by
  unfold modPt at ha
  rcases hm : modBlocks (blkTop δ T T' p) 1 w.1 with _ | l
  · rw [hm] at ha; simp at ha
  · rw [hm] at ha
    simp only at ha
    split_ifs at ha with hs
    simp only [Option.some.injEq] at ha
    subst ha
    rfl

theorem modPt_of_blocks {δ : ∀ p : PlF D, (D.s.atP p).Fp} {T T' : ℕ} {p : PlF D} {n : ℕ} {w : Point D.host.E n}
    {l : List ((D.s.atP p).Epˣ × ℕ+)} (hl : modBlocks (blkTop δ T T' p) 1 w.1 = some l)
    (hs : (l.map (fun b => (b.2 : ℕ))).sum = n) : modPt δ T T' p w = some ⟨l, hs⟩ := by
  unfold modPt
  rw [hl]
  simp only
  rw [dif_pos hs]

theorem modPt_snoc {δ : ∀ p : PlF D, (D.s.atP p).Fp} {T T' : ℕ} {p : PlF D} {m s : ℕ}
    {w : Point D.host.E m} {W : Point D.host.E (m + s)} {x : D.host.E} (hW : W.1 = w.1 ++ [(x, s)]) (hs : 0 < s)
    {a : Loc.Pt (D.s.atP p).Ep m} (ha : modPt δ T T' p w = some a)
    (hu : IsUnit (blkTop δ T T' p (m + 1) s x)) :
    modPt δ T T' p W = some (a.snoc hu.unit (⟨s, hs⟩ : ℕ+)) := by
  have hb := modPt_blocks ha
  have hsum : (w.1.map Prod.snd).sum = m := w.2.2
  have hl : modBlocks (blkTop δ T T' p) 1 W.1 = some (a.blocks ++ [(hu.unit, ⟨s, hs⟩)]) := by
    rw [hW, modBlocks_append, hb, hsum]
    simp only [Option.bind_some, modBlocks]
    rw [add_comm 1 m, dif_pos ⟨hu, hs⟩]
    simp
  exact modPt_of_blocks hl _

theorem tMod_eq (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (a s : ℕ) (x : D.host.E) :
    tMod δ p (nu D.R.rS a (a + s - 1)) s x = (D.s.atP p).ιE x * PI.SupportDatumW.hF D δ p a s := by
  unfold tMod PI.SupportDatumW.hF
  rw [PI.SupportDatumW.twist_mul]
  ring

theorem blkTop_nonTop (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) {a s : ℕ}
    (h : ¬ (a + s - 1 = D.R.rS + 1 ∧ s = 1)) (x : D.host.E) :
    blkTop δ T T' p a s x = (D.s.atP p).ιE x * PI.SupportDatumW.hF D δ p a s := by
  unfold blkTop blkMod
  rw [if_neg h, if_neg h, sub_zero, tMod_eq]

end Lists

section Local

variable {D : Formalism.BasicNotions.D7}

theorem isUnit_rinv {B : Type} [CommRing B] {x : B} (hx : IsUnit x) : IsUnit (Ring.inverse x) := by
  obtain ⟨u, rfl⟩ := hx
  rw [Ring.inverse_unit]
  exact Units.isUnit _

theorem isUnit_twist (p : PlF D) (s : ℕ) : IsUnit (twist p s (1 : (D.s.atP p).Ep)) := by
  rw [PI.SupportDatumW.twist_one_pow]
  refine IsUnit.pow _ (IsUnit.of_mul_eq_one (twist p 1 (1 : (D.s.atP p).Ep)) ?_)
  rw [← sq]
  exact PI.SupportDatumW.twist_sq p

theorem isUnit_qE (p : PlF D) : IsUnit (qE p) := by
  unfold qE
  split
  · rename_i sg _
    have hq : ((sg.q : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) ≠ 0 := by
      intro h0
      exact sg.q_irr.ne_zero (Subtype.ext h0)
    exact (isUnit_iff_ne_zero.2 hq).map _
  · exact isUnit_one

theorem unitAt_ne (p : PlF D) : uP p ≠ 0 := by
  have h0 := (D.host.g_prime 0).ne_zero
  have h1 := (D.host.g_prime 1).ne_zero
  have hg : (Lat.gS D : ℚ) ≠ 0 := by exact_mod_cast (Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D).ne'
  unfold uP gpart
  split_ifs <;> simp [hg, h0, h1]

theorem isUnit_ιE (p : PlF D) {x : D.host.E} (hx : x ≠ 0) : IsUnit ((D.s.atP p).ιE x) :=
  (isUnit_iff_ne_zero.2 hx).map _

theorem isUnit_hF {δ : ∀ p : PlF D, (D.s.atP p).Fp} (p : PlF D) (hδ : δ p ≠ 0) (a s : ℕ) :
    IsUnit (PI.SupportDatumW.hF D δ p a s) := by
  unfold PI.SupportDatumW.hF
  refine ((isUnit_rinv (IsUnit.pow _ ?_)).mul (isUnit_twist p s)).mul (isUnit_rinv (isUnit_qE p))
  exact ((isUnit_iff_ne_zero.2 hδ).map _).mul (isUnit_ιE p (by exact_mod_cast unitAt_ne p))

def uS (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (i s : ℕ) : (D.s.atP p).Ep :=
  (D.s.atP p).ιE (sgn D i) * PI.SupportDatumW.hF D δ p (i - s + 1) s

theorem isUnit_uS {δ : ∀ p : PlF D, (D.s.atP p).Fp} (p : PlF D) (hδ : δ p ≠ 0) (i s : ℕ) :
    IsUnit (uS δ p i s) :=
  (isUnit_ιE p (sgn_ne i)).mul (isUnit_hF p hδ _ _)

theorem blkTop_join (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) {m s : ℕ}
    (hnt : ¬ (m + s = D.R.rS + 1 ∧ s = 1)) (t : D.host.E) :
    blkTop δ T T' p (m + 1) s (sgn D (m + s) * t) = uS δ p (m + s) s * (D.s.atP p).ιE t := by
  have h : ¬ (m + 1 + s - 1 = D.R.rS + 1 ∧ s = 1) := by
    intro h; apply hnt; constructor
    · omega
    · exact h.2
  rw [blkTop_nonTop δ T T' p h, uS, map_mul]
  have e : m + s - s + 1 = m + 1 := by omega
  rw [e]
  ring

def uT (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (hδ : δ p ≠ 0) (i s : ℕ) (t : D.host.E) (ht : t ≠ 0) :
    (D.s.atP p).Epˣ :=
  (isUnit_uS p hδ i s).unit * Units.map ((D.s.atP p).ιE : D.host.E →* (D.s.atP p).Ep) (Units.mk0 t ht)

theorem uT_val (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (hδ : δ p ≠ 0) (i s : ℕ) (t : D.host.E)
    (ht : t ≠ 0) : ((uT δ p hδ i s t ht : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) = uS δ p i s * (D.s.atP p).ιE t := by
  simp [uT]

theorem locK_join {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (T T' : ℕ) (p : PlF D) {m s : ℕ} (hs : 1 ≤ s)
    (hnt : ¬ (m + s = D.R.rS + 1 ∧ s = 1)) {w w' : Point D.host.E m} {W W' : Point D.host.E (m + s)}
    {t t' : D.host.E} (ht : t ≠ 0) (ht' : t' ≠ 0)
    (hW : W.1 = w.1 ++ [(sgn D (m + s) * t, s)]) (hW' : W'.1 = w'.1 ++ [(sgn D (m + s) * t', s)])
    {a a' : Loc.Pt (D.s.atP p).Ep m} (ha : modPt δ T T' p w = some a) (ha' : modPt δ T T' p w' = some a') :
    locK M δ T T' p (m + s) W W' =
      A5.Kp (M p).R (M p).psiR (A5.addBlock (Formalism.MainNotions.LocalModelPeriodLattices.tr a) s (uT δ p (hA p).2.1 (m + s) s t ht))
        (A5.addBlock (Formalism.MainNotions.LocalModelPeriodLattices.tr a') s (uT δ p (hA p).2.1 (m + s) s t' ht')) := by
  have hu : IsUnit (blkTop δ T T' p (m + 1) s (sgn D (m + s) * t)) := by
    rw [blkTop_join δ T T' p hnt t, ← uT_val δ p (hA p).2.1 _ _ t ht]
    exact Units.isUnit _
  have hu' : IsUnit (blkTop δ T T' p (m + 1) s (sgn D (m + s) * t')) := by
    rw [blkTop_join δ T T' p hnt t', ← uT_val δ p (hA p).2.1 _ _ t' ht']
    exact Units.isUnit _
  have e1 : hu.unit = uT δ p (hA p).2.1 (m + s) s t ht := by
    ext; rw [IsUnit.unit_spec, uT_val, blkTop_join δ T T' p hnt t]
  have e2 : hu'.unit = uT δ p (hA p).2.1 (m + s) s t' ht' := by
    ext; rw [IsUnit.unit_spec, uT_val, blkTop_join δ T T' p hnt t']
  unfold locK
  rw [modPt_snoc hW (by omega) ha hu, modPt_snoc hW' (by omega) ha' hu']
  simp only
  refine (Formalism.MainNotions.LocalOrbitGerms.KKAll_proved _ _ (M p) (hA p).1 _ _ _).trans ?_
  exact congrArg₂ (A5.Kp (M p).R (M p).psiR)
    ((Formalism.MainNotions.LocalModelPeriodLattices.tr_snoc a hu.unit _).trans (by rw [e1]; rfl))
    ((Formalism.MainNotions.LocalModelPeriodLattices.tr_snoc a' hu'.unit _).trans (by rw [e2]; rfl))

end Local

section Good

variable {D : Formalism.BasicNotions.D7}

def onesPt (D : Formalism.BasicNotions.D7) (m : ℕ) : Point D.host.E m :=
  ⟨List.replicate m (1, 1), fun b hb => by
    rw [List.mem_replicate] at hb
    rw [hb.2]
    exact ⟨one_ne_zero, le_refl 1⟩, by simp⟩

def hpt (D : Formalism.BasicNotions.D7) (m : ℕ) (h : TB.Pt D.host.E) : Point D.host.E m := (ptOfList m h).getD (onesPt D m)

theorem hpt_of {m : ℕ} {h : TB.Pt D.host.E} {w : Point D.host.E m} (hw : ptOfList m h = some w) : hpt D m h = w := by
  simp [hpt, hw]

def etaW (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) {n : ℕ} (w : Point D.host.E n) :
    A5.Point (D.s.atP p).Ep :=
  match modPt δ T T' p w with
  | some a => Formalism.MainNotions.LocalModelPeriodLattices.tr a
  | none => LocModel.ePt _

theorem etaW_of {δ : ∀ p : PlF D, (D.s.atP p).Fp} {T T' : ℕ} {p : PlF D} {n : ℕ} {w : Point D.host.E n}
    {a : Loc.Pt (D.s.atP p).Ep n} (ha : modPt δ T T' p w = some a) : etaW δ T T' p w = Formalism.MainNotions.LocalModelPeriodLattices.tr a := by
  simp [etaW, ha]

def scal {n : ℕ} (w : Point D.host.E n) : Finset D.host.E := (w.1.map Prod.fst).toFinset

def Gd (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)
    (X : Finset D.host.E) : Prop :=
  (M p).split = none ∧ (δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]) ∧
    ((D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O) ∧
    ∀ t ∈ X, ∀ k : Fin 3, t + ((k : ℕ) : D.host.E) ≠ 0 →
      (D.s.atP p).ιE (t + ((k : ℕ) : D.host.E)) ∈ (D.s.atP p).O ∧
        (D.s.atP p).ιE ((t + ((k : ℕ) : D.host.E))⁻¹) ∈ (D.s.atP p).O

theorem gd_finite (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (X : Finset D.host.E) : {p | ¬ Gd δ M p X}.Finite := by
  have h := LocModel.good_cofinite δ M hA X
  rw [Filter.eventually_cofinite] at h
  exact h

theorem gd_place {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (T T' : ℕ) {p : PlF D} {X : Finset D.host.E} (h : Gd δ M p X) {n : ℕ}
    (w : Point D.host.E n) (hw : scal w ⊆ X) :
    (∀ x ∈ (M p).R, (M p).psiR x = 1) ∧ ∃ a, modPt δ T T' p w = some a ∧ (M p).InGLR a :=
  LocModel.good_place T T' w p (hA p) h.1 h.2.1.1 h.2.1.2 h.2.2.1 fun b hb k hk =>
    h.2.2.2 b.1 (hw (List.mem_toFinset.2 (List.mem_map.2 ⟨b, hb, rfl⟩))) k hk

theorem gd_notBad {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (T T' : ℕ) {p : PlF D} {X : Finset D.host.E} (h : Gd δ M p X) {n : ℕ}
    (w : Point D.host.E n) (hw : scal w ⊆ X) : p ∉ Formalism.L2.SG.DataCut.badSet δ M T T' n w := by
  simp only [Formalism.L2.SG.DataCut.badSet, Set.mem_ofPred_eq, not_not]
  exact ⟨h.1, gd_place hA T T' h w hw⟩

theorem R_eq_O {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {p : PlF D} (hA : Agree δ M p) (hs : (M p).split = none) : (M p).R = (D.s.atP p).O := by
  have hRL : (M p).R = (M p).L.O := by simp only [Loc.Model.R, hs]
  exact hRL.trans hA.2.2.2.1

theorem hF_good {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) {p : PlF D} {X : Finset D.host.E} (h : Gd δ M p X) (a s : ℕ) :
    LocModel.UnitIn (D.s.atP p).O (PI.SupportDatumW.hF D δ p a s) := by
  have hsD : (D.s.atP p).split = none := LocModel.split_none_of_agree (hA p) h.1
  set w0 : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)
    with hw0
  set w1 : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ *
    (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) with hw1
  have hw01 : w0 * w1 = 1 := by
    rw [hw0, hw1, mul_mul_mul_comm, ← map_mul, ← map_mul, mul_inv_cancel₀ (hA p).2.1,
      mul_inv_cancel₀ (by exact_mod_cast unitAt_ne p), map_one, map_one, one_mul]
  have hw0O : w0 ∈ (D.s.atP p).O := Subring.mul_mem _ (LocModel.LM.algebraMap_mem_O p h.2.1.1) h.2.2.1.1
  have hw1O : w1 ∈ (D.s.atP p).O := Subring.mul_mem _ (LocModel.LM.algebraMap_mem_O p h.2.1.2) h.2.2.1.2
  have e : PI.SupportDatumW.hF D δ p a s = w1 ^ nu D.R.rS a (a + s - 1) := by
    simp only [PI.SupportDatumW.hF, twist, qE, hsD, Ring.inverse_one, mul_one]
    rw [LocModel.ring_inverse_pow_eq hw01]
  rw [e]
  refine ⟨Subring.pow_mem _ hw1O _, w0 ^ nu D.R.rS a (a + s - 1), Subring.pow_mem _ hw0O _, ?_⟩
  rw [← mul_pow, mul_comm, hw01, one_pow]

theorem unitIn_mul {B : Type} [CommRing B] {O : Subring B} {x y : B} (hx : LocModel.UnitIn O x)
    (hy : LocModel.UnitIn O y) : LocModel.UnitIn O (x * y) := by
  obtain ⟨hx1, x', hx2, hx3⟩ := hx
  obtain ⟨hy1, y', hy2, hy3⟩ := hy
  exact ⟨O.mul_mem hx1 hy1, x' * y', O.mul_mem hx2 hy2, by
    calc x * y * (x' * y') = (x * x') * (y * y') := by ring
      _ = 1 := by rw [hx3, hy3, one_mul]⟩

theorem gd_elt {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {p : PlF D} {X : Finset D.host.E} (h : Gd δ M p X) {x : D.host.E} (hx : x ∈ X) (h0 : x ≠ 0) :
    LocModel.UnitIn (D.s.atP p).O ((D.s.atP p).ιE x) := by
  have h1 := h.2.2.2 x hx 0 (by simpa using h0)
  simp only [Fin.val_zero, Nat.cast_zero, add_zero] at h1
  exact ⟨h1.1, _, h1.2, by rw [← map_mul, mul_inv_cancel₀ h0, map_one]⟩

theorem modBlocks_low {δ : ∀ p : PlF D, (D.s.atP p).Fp} (T T' : ℕ) (p : PlF D) (hδ : δ p ≠ 0) :
    ∀ (a : ℕ) (l : List (D.host.E × ℕ)), a + (l.map Prod.snd).sum ≤ D.R.rS + 1 →
      (∀ b ∈ l, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∃ l', modBlocks (blkTop δ T T' p) a l = some l'
  | a, [], _, _ => ⟨[], rfl⟩
  | a, (t, s) :: rest, hle, hb => by
    simp only [List.map_cons, List.sum_cons] at hle
    have h1 := hb (t, s) List.mem_cons_self
    have hnt : ¬ (a + s - 1 = D.R.rS + 1 ∧ s = 1) := by omega
    have hu : IsUnit (blkTop δ T T' p a s t) := by
      rw [blkTop_nonTop δ T T' p hnt]
      exact (isUnit_ιE p h1.1).mul (isUnit_hF p hδ _ _)
    obtain ⟨l', hl'⟩ := modBlocks_low T T' p hδ (a + s) rest (by omega) fun b hb' => hb b (List.mem_cons_of_mem _ hb')
    have hs0 : 0 < s := by omega
    have e : modBlocks (blkTop δ T T' p) a ((t, s) :: rest) = some ((hu.unit, ⟨s, hs0⟩) :: l') := by
      simp only [modBlocks]
      rw [dif_pos ⟨hu, hs0⟩, hl']
      rfl
    exact ⟨_, e⟩

theorem modPt_low {δ : ∀ p : PlF D, (D.s.atP p).Fp} (T T' : ℕ) (p : PlF D) (hδ : δ p ≠ 0) {n : ℕ}
    (hn : n ≤ D.R.rS) (w : Point D.host.E n) : ∃ a, modPt δ T T' p w = some a := by
  obtain ⟨l, hl⟩ := modBlocks_low T T' p hδ 1 w.1 (by rw [w.2.2]; omega) w.2.1
  have hs : (l.map (fun b => (b.2 : ℕ))).sum = n := by
    have h1 := PI.SupportDatumW.modBlocks_some _ _ _ _ hl
    have h2 : l.map (fun b => (b.2 : ℕ)) = (l.map (fun x => ((x.1 : (D.s.atP p).Ep), (x.2 : ℕ)))).map Prod.snd := by
      simp
    rw [h2, h1, PI.SupportDatumW.mapBlocks_snd]
    exact w.2.2
  exact ⟨_, modPt_of_blocks hl hs⟩

end Good

section PF

variable {D : Formalism.BasicNotions.D7}

theorem absNorm_negOnePow (k : ℕ) (t : D.host.E) :
    |Algebra.norm ℚ ((-1 : D.host.E) ^ k * t)| = |Algebra.norm ℚ t| := by
  have h1 : (Algebra.norm ℚ (-1 : D.host.E)) ^ 2 = 1 := by
    rw [← map_pow]; simp
  have h2 : |Algebra.norm ℚ (-1 : D.host.E)| = 1 := by
    have h3 : |Algebra.norm ℚ (-1 : D.host.E)| ^ 2 = 1 := by rw [sq_abs]; exact h1
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).1 h3
  rw [map_mul, map_pow, abs_mul, abs_pow, h2, one_pow, one_mul]

theorem nrm_negOnePow (ν k : ℕ) (t : D.host.E) : nrm (D := D) ν ((-1) ^ k * t) = nrm (D := D) ν t := by
  unfold nrm
  rw [absNorm_negOnePow]

theorem modK_negOnePow {K : Type} [CommRing K] (R : Subring K) (k : ℕ) (x : K) :
    A5.modK R ((-1) ^ k * x) = A5.modK R x := by
  rcases neg_one_pow_eq_or K k with h | h
  · rw [h, one_mul]
  · rw [h, neg_one_mul, Formalism.FourierDecayAlt.P.A5x5.modK_neg]

theorem ιE_sgn (p : PlF D) (i : ℕ) : (D.s.atP p).ιE (sgn D i) = (-1) ^ (D.R.rS + 1 - i) := by
  simp [sgn]

def ModNorm (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (ν s : ℕ) (t : D.host.E), t ≠ 0 →
      (Function.mulSupport fun p => A5.modK (M p).R (tMod δ p ν s t)).Finite ∧
      ∏ᶠ p, A5.modK (M p).R (tMod δ p ν s t) = (nrm (D := D) ν t)⁻¹

theorem pf_blk (hMN : ModNorm D) {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) (a s : ℕ)
    {x : D.host.E} (hx : x ≠ 0) :
    (Function.mulSupport fun p => A5.modK (M p).R ((D.s.atP p).ιE x * PI.SupportDatumW.hF D δ p a s)).Finite ∧
      ∏ᶠ p, A5.modK (M p).R ((D.s.atP p).ιE x * PI.SupportDatumW.hF D δ p a s) =
        (nrm (D := D) (nu D.R.rS a (a + s - 1)) x)⁻¹ := by
  have h := hMN δ M hA (nu D.R.rS a (a + s - 1)) s x hx
  simp only [tMod_eq] at h
  exact h

theorem uS_mul (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (i s : ℕ) (t : D.host.E) :
    uS δ p i s * (D.s.atP p).ιE t = (D.s.atP p).ιE (sgn D i * t) * PI.SupportDatumW.hF D δ p (i - s + 1) s := by
  unfold uS; rw [map_mul]; ring

theorem pf_uS (hMN : ModNorm D) {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) (i s : ℕ)
    {t : D.host.E} (ht : t ≠ 0) :
    (Function.mulSupport fun p => A5.modK (M p).R (uS δ p i s * (D.s.atP p).ιE t)).Finite ∧
      ∏ᶠ p, A5.modK (M p).R (uS δ p i s * (D.s.atP p).ιE t) =
        (nrm (D := D) (nu D.R.rS (i - s + 1) (i - s + 1 + s - 1)) t)⁻¹ := by
  have h := pf_blk hMN hA (i - s + 1) s (mul_ne_zero (sgn_ne i) ht)
  simp only [← uS_mul] at h
  rw [sgn, nrm_negOnePow] at h
  exact h

def blkNr (D : Formalism.BasicNotions.D7) : ℕ → List (D.host.E × ℕ) → ℝ
  | _, [] => 1
  | b, (t, s) :: rest => nrm (D := D) (nu D.R.rS b (b + s - 1)) t ^ s * blkNr D (b + s) rest

theorem blkN_sign : ∀ (b : ℕ) (l : TB.Pt D.host.E),
    blkNr D b ((signAux D.R.rS b l).map Prod.swap) = blkN D b l
  | _, [] => by simp [signAux, blkNr, blkN]
  | b, (s, t) :: rest => by
    simp only [signAux, List.map_cons, Prod.swap_prod_mk, blkNr, blkN, blkN_sign (b + s) rest, nrm_negOnePow]

theorem blkN_hpt {m : ℕ} {h : TB.Pt D.host.E} {w : Point D.host.E m} (hw : ptOfList m h = some w) :
    blkNr D 1 w.1 = blkN D 1 h := by
  rw [(ptOfList_some hw).2]
  exact blkN_sign 1 h

theorem modK_pow {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
    {ψ : AddChar K ℂ} (hd : A5.LocalDatum K R ψ) {x : K} (hx : IsUnit x) : ∀ n : ℕ,
    A5.modK R (x ^ n) = A5.modK R x ^ n
  | 0 => by simp [Formalism.FourierDecayAlt.P.A5x5.modK_one]
  | n + 1 => by
    rw [pow_succ, Formalism.FourierDecayAlt.P.A5x5.modK_mul' hd (hx.pow n) hx, modK_pow hd hx n, pow_succ]

theorem det_modPt {δ : ∀ p : PlF D, (D.s.atP p).Fp} {T T' : ℕ} {p : PlF D} {n : ℕ} (w : Point D.host.E n)
    (a : Loc.Pt (D.s.atP p).Ep n) (ha : modPt δ T T' p w = some a) :
    a.mat.det = PI.SupportDatumW.blkDet (mapBlocks (blkTop δ T T' p) 1 w.1) := by
  unfold modPt at ha
  rcases hm : modBlocks (blkTop δ T T' p) 1 w.1 with _ | l
  · rw [hm] at ha
    simp at ha
  · rw [hm] at ha
    simp only at ha
    split_ifs at ha with hs
    simp only [Option.some.injEq] at ha
    subst ha
    have hl := PI.SupportDatumW.modBlocks_some _ _ _ _ hm
    have hsum : ((mapBlocks (blkTop δ T T' p) 1 w.1).map Prod.snd).sum = n := by
      rw [PI.SupportDatumW.mapBlocks_snd]
      exact w.2.2
    rw [← PI.SupportDatumW.ptEntry_det _ _ hsum, ← hl]
    congr 1
    ext i j
    simp [Loc.Pt.mat, PI.SupportDatumW.ptEntryL_eq]

theorem pf_det (hMN : ModNorm D) {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) (T T' : ℕ) :
    ∀ (b : ℕ) (l : List (D.host.E × ℕ)), b + (l.map Prod.snd).sum ≤ D.R.rS + 1 →
      (∀ x ∈ l, x.1 ≠ 0 ∧ 1 ≤ x.2) →
      (∀ p, IsUnit (PI.SupportDatumW.blkDet (mapBlocks (blkTop δ T T' p) b l))) ∧
      (Function.mulSupport fun p =>
        A5.modK (M p).R (PI.SupportDatumW.blkDet (mapBlocks (blkTop δ T T' p) b l))).Finite ∧
      ∏ᶠ p, A5.modK (M p).R (PI.SupportDatumW.blkDet (mapBlocks (blkTop δ T T' p) b l)) = (blkNr D b l)⁻¹
  | b, [], _, _ => by
    simp [mapBlocks, PI.SupportDatumW.blkDet, blkNr, Formalism.FourierDecayAlt.P.A5x5.modK_one]
  | b, (t, s) :: rest, hle, hb => by
    simp only [List.map_cons, List.sum_cons] at hle
    have h1 := hb (t, s) List.mem_cons_self
    obtain ⟨hu, hf, hp⟩ := pf_det hMN hA T T' (b + s) rest (by omega) fun x hx => hb x (List.mem_cons_of_mem _ hx)
    have hnt : ¬ (b + s - 1 = D.R.rS + 1 ∧ s = 1) := by omega
    have hc : ∀ p, blkTop δ T T' p b s t = (D.s.atP p).ιE t * PI.SupportDatumW.hF D δ p b s :=
      fun p => blkTop_nonTop δ T T' p hnt t
    have hcu : ∀ p, IsUnit ((D.s.atP p).ιE t * PI.SupportDatumW.hF D δ p b s) :=
      fun p => (isUnit_ιE p h1.1).mul (isUnit_hF p (hA p).2.1 _ _)
    obtain ⟨hf1, hp1⟩ := pf_blk hMN hA b s h1.1
    have e : ∀ p, A5.modK (M p).R (PI.SupportDatumW.blkDet (mapBlocks (blkTop δ T T' p) b ((t, s) :: rest))) =
        A5.modK (M p).R ((D.s.atP p).ιE t * PI.SupportDatumW.hF D δ p b s) ^ s *
          A5.modK (M p).R (PI.SupportDatumW.blkDet (mapBlocks (blkTop δ T T' p) (b + s) rest)) := by
      intro p
      have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) (hA p).1
      have hd := Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK (M p) (hA p).1
      simp only [mapBlocks, PI.SupportDatumW.blkDet, hc p]
      rw [mul_assoc, modK_negOnePow, Formalism.FourierDecayAlt.P.A5x5.modK_mul' hd ((hcu p).pow s) (hu p), modK_pow hd (hcu p)]
    refine ⟨fun p => ?_, ?_, ?_⟩
    · simp only [mapBlocks, PI.SupportDatumW.blkDet, hc p]
      exact (((isUnit_one.neg).pow _).mul ((hcu p).pow s)).mul (hu p)
    · simp only [e]
      refine ((hf1.union hf).subset ?_)
      intro p hp
      by_contra hn
      simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hn
      apply hp
      simp only [hn.1, hn.2, one_pow, one_mul]
    · simp only [e]
      rw [finprod_mul_distrib (Set.Finite.subset hf1 (Function.mulSupport_pow _ _)) hf, ← finprod_pow hf1, hp1, hp,
        blkNr, inv_pow, mul_inv]

end PF

section Sys

variable {D : Formalism.BasicNotions.D7}

def uU (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (i s : ℕ) : (D.s.atP p).Epˣ :=
  if h : IsUnit (uS δ p i s) then h.unit else 1

theorem uU_val {δ : ∀ p : PlF D, (D.s.atP p).Fp} {p : PlF D} (hδ : δ p ≠ 0) (i s : ℕ) :
    ((uU δ p i s : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) = uS δ p i s := by
  rw [uU, dif_pos (isUnit_uS p hδ i s)]
  rfl

theorem uT_eq {δ : ∀ p : PlF D, (D.s.atP p).Fp} {p : PlF D} (hδ : δ p ≠ 0) (i s : ℕ) (t : D.host.E) (ht : t ≠ 0) :
    uT δ p hδ i s t ht = uU δ p i s * Units.map ((D.s.atP p).ιE : D.host.E →* (D.s.atP p).Ep) (Units.mk0 t ht) := by
  ext
  rw [uT_val, Units.val_mul, uU_val hδ]
  rfl

def dph (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' i s : ℕ)
    (p : PlF D) (t : D.host.E) : ℂ :=
  if i = D.R.rS + 1 ∧ s = 2 then
    (match (D.s.atP p).split with
      | some _ => (M p).psiR (tau0 p T T' * Ring.inverse (blkMod δ T T' p D.R.rS 2 (sgn D i * t)))
      | none => 1)
  else 1

theorem dph_none {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {p : PlF D} (hA : Agree δ M p) (hs : (M p).split = none) (T T' i s : ℕ) (t : D.host.E) :
    dph M δ T T' i s p t = 1 := by
  have hsD := LocModel.split_none_of_agree hA hs
  unfold dph
  split_ifs
  · rw [hsD]
  · rfl

theorem norm_dph {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {p : PlF D} (hA : Agree δ M p) (T T' i s : ℕ) (t : D.host.E) : ‖dph M δ T T' i s p t‖ = 1 := by
  unfold dph
  split_ifs
  · split
    · have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hA.1
      have hd := Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK (M p) hA.1
      set x := tau0 p T T' * Ring.inverse (blkMod δ T T' p D.R.rS 2 (sgn D i * t))
      have h1 : (M p).psiR x * (starRingEnd ℂ) ((M p).psiR x) = 1 := by
        rw [hd.unitary, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
      have h2 : Complex.normSq ((M p).psiR x) = 1 := by
        rw [Complex.mul_conj] at h1
        exact_mod_cast h1
      have h3 : ‖(M p).psiR x‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h2
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
    · simp
  · simp

def etaH (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' m : ℕ) (p : PlF D) (h : TB.Pt D.host.E) : A5.Point (D.s.atP p).Ep :=
  etaW δ T T' p (hpt D m h)

def pullS (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (T T' i s : ℕ) (p : PlF D) : J.LocSys D.host.E (TB.Pt D.host.E) :=
  J.phaseSys (dph M δ T T' i s p)
    (J.pullSys (M p).R (M p).psiR s (D.s.atP p).ιE (uU δ p i s) (etaH δ T T' (i - s) p) fun _ _ _ => 0)

theorem pullS_N {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    (hA : ∀ p, Agree δ M p) (T T' : ℕ) (p : PlF D) {m s : ℕ} (hs : 1 ≤ s) (hm : m + s ≤ D.R.rS + 1)
    (hnt : ¬ (m + s = D.R.rS + 1 ∧ s = 1)) {h h' : TB.Pt D.host.E} {w w' : Point D.host.E m}
    (hw : ptOfList m h = some w) (hw' : ptOfList m h' = some w') {W W' : Point D.host.E (m + s)}
    {t t' : D.host.E} (ht : t ≠ 0) (ht' : t' ≠ 0)
    (hW : W.1 = w.1 ++ [(sgn D (m + s) * t, s)]) (hW' : W'.1 = w'.1 ++ [(sgn D (m + s) * t', s)]) :
    (pullS M δ T T' (m + s) s p).N t t' h h' =
      (A5.modK (M p).R (uS δ p (m + s) s * (D.s.atP p).ιE t) *
        A5.modK (M p).R (uS δ p (m + s) s * (D.s.atP p).ιE t')) ^ (s * (s - 1) / 2) *
      (dph M δ T T' (m + s) s p t * (starRingEnd ℂ) (dph M δ T T' (m + s) s p t') *
        locK M δ T T' p (m + s) W W') := by
  have hmr : m ≤ D.R.rS := by omega
  obtain ⟨a, ha⟩ := modPt_low T T' p (hA p).2.1 hmr w
  obtain ⟨a', ha'⟩ := modPt_low T T' p (hA p).2.1 hmr w'
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) (hA p).1
  have hd := Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK (M p) (hA p).1
  have e1 : etaH δ T T' (m + s - s) p h = Formalism.MainNotions.LocalModelPeriodLattices.tr a := by
    rw [Nat.add_sub_cancel, etaH, hpt_of hw, etaW_of ha]
  have e2 : etaH δ T T' (m + s - s) p h' = Formalism.MainNotions.LocalModelPeriodLattices.tr a' := by
    rw [Nat.add_sub_cancel, etaH, hpt_of hw', etaW_of ha']
  rw [locK_join hA T T' p hs hnt ht ht' hW hW' ha ha', uT_eq, uT_eq]
  simp only [pullS, J.phaseSys, J.pullSys, dif_pos (And.intro ht ht'), A5.Ns, e1, e2]
  have hu1 : IsUnit (uS δ p (m + s) s * (D.s.atP p).ιE t) := (isUnit_uS p (hA p).2.1 _ _).mul (isUnit_ιE p ht)
  have hu2 : IsUnit (uS δ p (m + s) s * (D.s.atP p).ιE t') := (isUnit_uS p (hA p).2.1 _ _).mul (isUnit_ιE p ht')
  have ev : ∀ x (hx : x ≠ 0), ((uU δ p (m + s) s * Units.map ((D.s.atP p).ιE : D.host.E →* (D.s.atP p).Ep)
      (Units.mk0 x hx) : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) = uS δ p (m + s) s * (D.s.atP p).ιE x := by
    intro x hx
    rw [Units.val_mul, uU_val (hA p).2.1]
    rfl
  rw [ev t ht, ev t' ht', Formalism.FourierDecayAlt.P.A5x5.modK_mul' hd hu1 hu2]
  push_cast
  ring

theorem cast_val {n n' : ℕ} (h : n = n') (W : Point D.host.E n) : (h ▸ W).1 = W.1 := by
  subst h; rfl

theorem locK_cast (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (T T' : ℕ) (p : PlF D) {n n' : ℕ} (h : n = n') (W W' : Point D.host.E n) :
    locK M δ T T' p n' (h ▸ W) (h ▸ W') = locK M δ T T' p n W W' := by
  subst h; rfl

theorem dfac_join (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (T T' : ℕ) (p : PlF D) {m s : ℕ} (hi : m + s = D.R.rS + 1) (hs2 : 2 ≤ s) (V : Point D.host.E (D.R.rS + 1))
    (v : List (D.host.E × ℕ)) (x : D.host.E) (hV : V.1 = v ++ [(sgn D (m + s) * x, s)]) :
    dfac M δ T T' p V = dph M δ T T' (m + s) s p x := by
  have hl : V.1.getLast? = some (sgn D (m + s) * x, s) := by
    rw [hV, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
    rfl
  unfold dfac dph
  rw [hl]
  rcases Nat.lt_or_ge s 3 with h3 | h3
  · obtain rfl : s = 2 := by omega
    rw [if_pos (show m + 2 = D.R.rS + 1 ∧ 2 = 2 from ⟨hi, rfl⟩)]
    rcases (D.s.atP p).split with _ | sg
    · rfl
    · rfl
  · obtain ⟨k, rfl⟩ : ∃ k, s = k + 3 := ⟨s - 3, by omega⟩
    rw [if_neg (show ¬ (m + (k + 3) = D.R.rS + 1 ∧ k + 3 = 2) by omega)]
    rcases (D.s.atP p).split with _ | sg
    · rfl
    · rfl

theorem kglob_join {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    (T T' : ℕ) {m s : ℕ} (hs : 1 ≤ s) (hnt : ¬ (m + s = D.R.rS + 1 ∧ s = 1)) {w w' : Point D.host.E m}
    {W W' : Point D.host.E (m + s)} (t t' : D.host.E)
    (hW : W.1 = w.1 ++ [(sgn D (m + s) * t, s)]) (hW' : W'.1 = w'.1 ++ [(sgn D (m + s) * t', s)]) :
    Kglob δ M T T' (m + s) W W' =
      ∏ᶠ p, dph M δ T T' (m + s) s p t * (starRingEnd ℂ) (dph M δ T T' (m + s) s p t') *
        locK M δ T T' p (m + s) W W' := by
  unfold Kglob
  by_cases hi : m + s = D.R.rS + 1
  · rw [dif_pos hi]
    have hs2 : 2 ≤ s := by
      rcases Nat.lt_or_ge s 2 with h | h
      · exact absurd ⟨hi, by omega⟩ hnt
      · exact h
    have hc : (hi ▸ W).1 = w.1 ++ [(sgn D (m + s) * t, s)] := (cast_val hi W).trans hW
    have hc' : (hi ▸ W').1 = w'.1 ++ [(sgn D (m + s) * t', s)] := (cast_val hi W').trans hW'
    have hk : kind (hi ▸ W) = none := by
      unfold kind
      rw [if_pos (PI.SupportDatumW.dmin_last_big D _ _ _ _ hc hs2)]
    have hk' : kind (hi ▸ W') = none := by
      unfold kind
      rw [if_pos (PI.SupportDatumW.dmin_last_big D _ _ _ _ hc' hs2)]
    unfold KtopG
    rw [if_pos (hk.trans hk'.symm)]
    refine finprod_congr fun p => ?_
    unfold KtopP
    rw [locK_cast M δ T T' p hi W W']
    rw [dfac_join M δ T T' p hi hs2 _ w.1 t hc, dfac_join M δ T T' p hi hs2 _ w'.1 t' hc']
    ring
  · rw [dif_neg hi]
    refine finprod_congr fun p => ?_
    simp only [dph, show ¬ (m + s = D.R.rS + 1 ∧ s = 2) from fun h => hi h.1, if_false, map_one, one_mul]

end Sys

section Kern

variable {D : Formalism.BasicNotions.D7}

theorem head_prod (hMN : ModNorm D) {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) (T T' : ℕ) {m : ℕ}
    (hm : m ≤ D.R.rS) (w : Point D.host.E m) (P0 : Finset (PlF D)) {X : Finset D.host.E} (hX : scal w ⊆ X)
    (hP0 : ∀ p, p ∉ P0 → Gd δ M p X) :
    ∏ p ∈ P0, A5.cSize (M p).R (etaW δ T T' p w) = blkNr D 1 w.1 := by
  obtain ⟨-, -, hp⟩ := pf_det hMN hA T T' 1 w.1 (by rw [w.2.2]; omega) w.2.1
  have key : ∀ p, A5.cSize (M p).R (etaW δ T T' p w) =
      (A5.modK (M p).R (PI.SupportDatumW.blkDet (mapBlocks (blkTop δ T T' p) 1 w.1)))⁻¹ := by
    intro p
    obtain ⟨a, ha⟩ := modPt_low T T' p (hA p).2.1 hm w
    rw [etaW_of ha, A5.cSize, ← Formalism.MainNotions.LocalModelPeriodLattices.det_eq, det_modPt w a ha]
  have hsub : (Function.mulSupport fun p =>
      (A5.modK (M p).R (PI.SupportDatumW.blkDet (mapBlocks (blkTop δ T T' p) 1 w.1)))⁻¹) ⊆ (P0 : Set (PlF D)) := by
    intro p hp
    by_contra hpP
    apply hp
    have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) (hA p).1
    obtain ⟨-, a, ha, hG⟩ := gd_place hA T T' (hP0 p hpP) w hX
    show (A5.modK _ _)⁻¹ = 1
    rw [← det_modPt w a ha]
    obtain ⟨hent, v, hv, hdv⟩ := hG
    rw [Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.modK_unitR (LocModel.det_mem_of _ _ hent) hv hdv, inv_one]
  rw [Finset.prod_congr rfl (fun p _ => key p), ← finprod_eq_prod_of_mulSupport_subset _ hsub,
    finprod_inv_distrib, hp, inv_inv]

theorem scal_join {m s : ℕ} {w : Point D.host.E m} {W : Point D.host.E (m + s)} {x : D.host.E}
    (hW : W.1 = w.1 ++ [(x, s)]) : scal W = scal w ∪ {x} := by
  unfold scal
  rw [hW]
  ext y
  simp

theorem blkN_pos : ∀ (b : ℕ) (l : TB.Pt D.host.E), (∀ c ∈ l, c.2 ≠ 0) → 0 < blkN D b l
  | _, [], _ => by simp [blkN]
  | b, (s, t) :: rest, h => by
    simp only [blkN]
    exact mul_pos (pow_pos (nrm_pos (h (s, t) List.mem_cons_self) _) _)
      (blkN_pos (b + s) rest fun c hc => h c (List.mem_cons_of_mem _ hc))

theorem isPtL_of_ptOfList {m : ℕ} {h : TB.Pt D.host.E} {w : Point D.host.E m} (hw : ptOfList m h = some w) :
    Formalism.L2.S.IsPtL h m :=
  (isPtL_signPt D.R.rS h m).1 (ptOfList_some hw).1

def wt (D : Formalism.BasicNotions.D7) (m s : ℕ) (h : TB.Pt D.host.E) : ℝ :=
  match ptOfList m h with
  | some _ => (phi m h * blkN D 1 h ^ s)⁻¹
  | none => 0

theorem krOf_join (hMN : ModNorm D) {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) (T T' : ℕ) {m s : ℕ}
    (hs : 1 ≤ s) (hm : m + s ≤ D.R.rS + 1) (hnt : ¬ (m + s = D.R.rS + 1 ∧ s = 1))
    {h h' : TB.Pt D.host.E} (hl : TB.level h = m) (hl' : TB.level h' = m) {w w' : Point D.host.E m}
    (hw : ptOfList m h = some w) (hw' : ptOfList m h' = some w') {t t' : D.host.E} (ht : t ≠ 0) (ht' : t' ≠ 0)
    (P : Finset (PlF D)) {X : Finset D.host.E} (hX : scal w ⊆ X) (hX' : scal w' ⊆ X)
    (htX : sgn D (m + s) * t ∈ X) (htX' : sgn D (m + s) * t' ∈ X) (hP : ∀ p, p ∉ P → Gd δ M p X) :
    KrOf δ M T T' (m + s) (TB.join h s t) (TB.join h' s t') =
      (((phi m h * blkN D 1 h ^ s : ℝ) : ℂ))⁻¹ * (((phi m h' * blkN D 1 h' ^ s : ℝ) : ℂ))⁻¹ *
        ∏ p ∈ P, (pullS M δ T T' (m + s) s p).N t t' h h' := by
  obtain ⟨W, hWo, hW⟩ := ptOfList_join hl hw hs ht
  obtain ⟨W', hWo', hW'⟩ := ptOfList_join hl' hw' hs ht'
  have hK : KrOf δ M T T' (m + s) (TB.join h s t) (TB.join h' s t') =
      Kglob δ M T T' (m + s) W W' /
        ((phi (m + s) (TB.join h s t) : ℂ) * (phi (m + s) (TB.join h' s t') : ℂ)) := by
    unfold KrOf
    rw [if_neg (by omega), if_neg (by omega), hWo, hWo']
  have hphi : ∀ (g : TB.Pt D.host.E) (x : D.host.E), TB.level g = m →
      phi (m + s) (TB.join g s x) = phi m g * blkN D 1 g ^ s *
        nrm (D := D) (nu D.R.rS (m + 1) (m + s)) x ^ (s * (s - 1) / 2) := by
    intro g x hg
    unfold phi TB.join
    rw [blockProduct_append, blockProduct_shift m s 1 g (by omega), hg]
    simp only [blockWeightPhi]
    have e1 : 1 + m = m + 1 := by ring
    have e2 : m + 1 + s - 1 = m + s := by omega
    have e3 : m + s - (m + s) = 0 := by omega
    rw [e1, e2, e3]
    ring
  have hWX : scal W ⊆ X := by rw [scal_join hW]; exact Finset.union_subset hX (by simpa using htX)
  have hWX' : scal W' ⊆ X := by rw [scal_join hW']; exact Finset.union_subset hX' (by simpa using htX')

  have hC : ∀ x ∈ X, x ≠ 0 → ∀ p, p ∉ P →
      A5.modK (M p).R (uS δ p (m + s) s * (D.s.atP p).ιE ((sgn D (m + s))⁻¹ * x)) = 1 := by
    intro x hx hx0 p hp
    have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) (hA p).1
    have hG := hP p hp
    have e : uS δ p (m + s) s * (D.s.atP p).ιE ((sgn D (m + s))⁻¹ * x) =
        (D.s.atP p).ιE x * PI.SupportDatumW.hF D δ p (m + s - s + 1) s := by
      rw [uS_mul, ← mul_assoc, mul_inv_cancel₀ (sgn_ne _), one_mul]
    rw [e]
    obtain ⟨h1, v, h2, h3⟩ := unitIn_mul (gd_elt hG hx hx0) (hF_good hA hG _ _)
    rw [R_eq_O (hA p) hG.1] at *
    exact Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.modK_unitR h1 h2 h3
  have hinv : ∀ x : D.host.E, (sgn D (m + s))⁻¹ * (sgn D (m + s) * x) = x := fun x => by
    rw [← mul_assoc, inv_mul_cancel₀ (sgn_ne _), one_mul]
  have hCt : ∀ p, p ∉ P → A5.modK (M p).R (uS δ p (m + s) s * (D.s.atP p).ιE t) = 1 := fun p hp => by
    simpa [hinv] using hC _ htX (mul_ne_zero (sgn_ne _) ht) p hp
  have hCt' : ∀ p, p ∉ P → A5.modK (M p).R (uS δ p (m + s) s * (D.s.atP p).ιE t') = 1 := fun p hp => by
    simpa [hinv] using hC _ htX' (mul_ne_zero (sgn_ne _) ht') p hp
  have hGp : ∀ p, p ∉ P → dph M δ T T' (m + s) s p t * (starRingEnd ℂ) (dph M δ T T' (m + s) s p t') *
      locK M δ T T' p (m + s) W W' = 1 := by
    intro p hp
    have hG := hP p hp
    rw [dph_none (hA p) hG.1, dph_none (hA p) hG.1,
      Formalism.L2.SG.DataCut.locK_eq_one Formalism.MainNotions.LocalOrbitGerms.KKAll_proved hA (gd_notBad hA T T' hG W hWX)
        (gd_notBad hA T T' hG W' hWX')]
    simp
  have pf1 := pf_uS hMN hA (m + s) s ht
  have pf2 := pf_uS hMN hA (m + s) s ht'
  have e4 : m + s - s + 1 = m + 1 := by omega
  have e5 : m + 1 + s - 1 = m + s := by omega
  rw [e4, e5] at pf1 pf2
  have f1 : ∏ p ∈ P, A5.modK (M p).R (uS δ p (m + s) s * (D.s.atP p).ιE t) =
      (nrm (D := D) (nu D.R.rS (m + 1) (m + s)) t)⁻¹ := by
    rw [← pf1.2, finprod_eq_prod_of_mulSupport_subset]
    intro p hp; by_contra hpP; exact hp (hCt p hpP)
  have f2 : ∏ p ∈ P, A5.modK (M p).R (uS δ p (m + s) s * (D.s.atP p).ιE t') =
      (nrm (D := D) (nu D.R.rS (m + 1) (m + s)) t')⁻¹ := by
    rw [← pf2.2, finprod_eq_prod_of_mulSupport_subset]
    intro p hp; by_contra hpP; exact hp (hCt' p hpP)
  have f3 : ∏ p ∈ P, dph M δ T T' (m + s) s p t * (starRingEnd ℂ) (dph M δ T T' (m + s) s p t') *
      locK M δ T T' p (m + s) W W' = Kglob δ M T T' (m + s) W W' := by
    rw [kglob_join T T' hs hnt t t' hW hW', finprod_eq_prod_of_mulSupport_subset]
    intro p hp; by_contra hpP; exact hp (hGp p hpP)
  rw [Finset.prod_congr rfl (fun p _ => pullS_N hA T T' p hs hm hnt hw hw' ht ht' hW hW'),
    Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_mul_distrib]
  have f1c : ∏ p ∈ P, ((A5.modK (M p).R (uS δ p (m + s) s * (D.s.atP p).ιE t) : ℝ) : ℂ) =
      (((nrm (D := D) (nu D.R.rS (m + 1) (m + s)) t)⁻¹ : ℝ) : ℂ) := by rw [← f1]; push_cast; rfl
  have f2c : ∏ p ∈ P, ((A5.modK (M p).R (uS δ p (m + s) s * (D.s.atP p).ιE t') : ℝ) : ℂ) =
      (((nrm (D := D) (nu D.R.rS (m + 1) (m + s)) t')⁻¹ : ℝ) : ℂ) := by rw [← f2]; push_cast; rfl
  rw [f1c, f2c, f3, hK, hphi h t hl, hphi h' t' hl']
  push_cast
  ring

theorem krOf_head {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) (T T' : ℕ) {m : ℕ}
    (hm : m ≤ D.R.rS) {h h' : TB.Pt D.host.E} {w w' : Point D.host.E m}
    (hw : ptOfList m h = some w) (hw' : ptOfList m h' = some w') (P : Finset (PlF D)) {X : Finset D.host.E}
    (hX : scal w ⊆ X) (hX' : scal w' ⊆ X) (hP : ∀ p, p ∉ P → Gd δ M p X) :
    KrOf δ M T T' m h h' * ((phi m h : ℂ) * (phi m h' : ℂ)) =
      ∏ p ∈ P, A5.Kp (M p).R (M p).psiR (etaW δ T T' p w) (etaW δ T T' p w') := by
  have hloc : ∀ p, locK M δ T T' p m w w' = A5.Kp (M p).R (M p).psiR (etaW δ T T' p w) (etaW δ T T' p w') := by
    intro p
    obtain ⟨a, ha⟩ := modPt_low T T' p (hA p).2.1 hm w
    obtain ⟨a', ha'⟩ := modPt_low T T' p (hA p).2.1 hm w'
    unfold locK
    rw [ha, ha', etaW_of ha, etaW_of ha']
    exact Formalism.MainNotions.LocalOrbitGerms.KKAll_proved _ _ (M p) (hA p).1 m a a'
  have hsub : (Function.mulSupport fun p => locK M δ T T' p m w w') ⊆ (P : Set (PlF D)) := by
    intro p hp; by_contra hpP
    exact hp (Formalism.L2.SG.DataCut.locK_eq_one Formalism.MainNotions.LocalOrbitGerms.KKAll_proved hA (gd_notBad hA T T' (hP p hpP) w hX)
      (gd_notBad hA T T' (hP p hpP) w' hX'))
  rw [← Finset.prod_congr rfl (fun p _ => hloc p), ← finprod_eq_prod_of_mulSupport_subset _ hsub]
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    have hh : ∀ {g : TB.Pt D.host.E} {v : Point D.host.E 0}, ptOfList 0 g = some v → g = [] := by
      intro g v hv
      have h1 := isPtL_of_ptOfList hv
      rcases g with _ | ⟨c, g⟩
      · rfl
      · exfalso
        have h2 := h1.1
        have h3 := (h1.2 c List.mem_cons_self).1
        simp only [List.map_cons, List.sum_cons] at h2
        omega
    obtain rfl := hh hw
    obtain rfl := hh hw'
    have h1 : ∀ p, locK M δ T T' p 0 w w' = 1 := by
      intro p
      unfold locK
      obtain ⟨a, ha⟩ := modPt_low T T' p (hA p).2.1 (Nat.zero_le _) w
      obtain ⟨a', ha'⟩ := modPt_low T T' p (hA p).2.1 (Nat.zero_le _) w'
      rw [ha, ha']
      rfl
    simp [h1, KrOf, phi, blockWeightPhi]
  · have hK : KrOf δ M T T' m h h' = Kglob δ M T T' m w w' / ((phi m h : ℂ) * (phi m h' : ℂ)) := by
      unfold KrOf
      rw [if_neg (by omega), if_neg (by omega), hw, hw']
    have hpos : ((phi m h : ℂ) * (phi m h' : ℂ)) ≠ 0 := by
      have a1 := phi_pos (isPtL_of_ptOfList hw)
      have a2 := phi_pos (isPtL_of_ptOfList hw')
      exact mul_ne_zero (by exact_mod_cast a1.ne') (by exact_mod_cast a2.ne')
    rw [hK, div_mul_cancel₀ _ hpos, Kglob, dif_neg (by omega)]

end Kern

section Pull

variable {D : Formalism.BasicNotions.D7}

def X1 (X0 : Finset D.host.E) (c t t' : D.host.E) : Finset D.host.E := X0 ∪ {c * t, c * t', t⁻¹ - t'⁻¹}

def Qf (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (X0 : Finset D.host.E) (c : D.host.E) (P : Finset (PlF D)) (t t' : D.host.E) :
    Finset (PlF D) :=
  (gd_finite δ M hA (X1 X0 c t t')).toFinset \ P

theorem qf_gd {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (X0 : Finset D.host.E) (c : D.host.E) (P : Finset (PlF D)) (t t' : D.host.E)
    (p : PlF D) (hp : p ∉ P) (hq : p ∉ Qf δ M hA X0 c P t t') : Gd δ M p (X1 X0 c t t') := by
  by_contra hn
  exact hq (Finset.mem_sdiff.2 ⟨(Set.Finite.mem_toFinset _).2 hn, hp⟩)

def outS (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (T T' i s : ℕ) (P : Finset (PlF D)) (Q : D.host.E → D.host.E → Finset (PlF D)) :
    J.LocSys D.host.E (TB.Pt D.host.E) where
  N := fun t t' h h' => ∏ q ∈ Q t t', (pullS M δ T T' i s q).N t t' h h'
  Th := fun _ _ _ => 0
  B := fun _ _ => 1
  L := ⨅ p : {p // p ∉ P}, (pullS M δ T T' i s p.1).L
  L' := ⨅ p : {p // p ∉ P}, (pullS M δ T T' i s p.1).L'

def sysP (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (T T' i s : ℕ) (P : Finset (PlF D)) (Q : D.host.E → D.host.E → Finset (PlF D)) :
    Option {p // p ∈ P} → J.LocSys D.host.E (TB.Pt D.host.E)
  | none => outS M δ T T' i s P Q
  | some p => pullS M δ T T' i s p.1

theorem etaH_sum {δ : ∀ p : PlF D, (D.s.atP p).Fp} (T T' : ℕ) (p : PlF D) (hδ : δ p ≠ 0) {m : ℕ} (hm : m ≤ D.R.rS)
    (h : TB.Pt D.host.E) : (etaH δ T T' m p h).1.sum = m := by
  obtain ⟨a, ha⟩ := modPt_low T T' p hδ hm (hpt D m h)
  rw [etaH, etaW_of ha, Formalism.MainNotions.LocalModelPeriodLattices.tr_sum]

theorem etaH_glr {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (T T' : ℕ) {p : PlF D} {X : Finset D.host.E} (hG : Gd δ M p X) {m : ℕ}
    (h : TB.Pt D.host.E) (hX : scal (hpt D m h) ⊆ X) : A5.InGLR (M p).R (etaH δ T T' m p h) := by
  obtain ⟨-, a, ha, hGa⟩ := gd_place hA T T' hG (hpt D m h) hX
  rw [etaH, etaW_of ha]
  exact Formalism.MainNotions.LocalModelPeriodLattices.inGLR_tr a hGa

theorem isPull_pullS {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (T T' i s : ℕ) (hm : i - s ≤ D.R.rS) (p : PlF D) (Y : Finset (TB.Pt D.host.E))
    (un : Bool) (hun : un = true → ∀ h ∈ Y, A5.InGLR (M p).R (etaH δ T T' (i - s) p h)) :
    PB.IsPull (pullS M δ T T' i s p) Y s un :=
  ⟨LocModel.placeOf M (fun q => (hA q).1) p, uU δ p i s, etaH δ T T' (i - s) p, i - s, dph M δ T T' i s p,
    fun h _ => etaH_sum T T' p (hA p).2.1 hm h, fun t => norm_dph (hA p) T T' i s t, hun,
    ⟨fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl⟩⟩

theorem unitIn_sgn (p : PlF D) (i : ℕ) : LocModel.UnitIn (D.s.atP p).O ((D.s.atP p).ιE (sgn D i)) := by
  rw [ιE_sgn]
  refine ⟨Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _, (-1) ^ (D.R.rS + 1 - i),
    Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _, ?_⟩
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem uS_good {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) {p : PlF D} {X : Finset D.host.E} (hG : Gd δ M p X) (i s : ℕ) :
    LocModel.UnitIn (D.s.atP p).O (uS δ p i s) :=
  unitIn_mul (unitIn_sgn p i) (hF_good hA hG _ _)

theorem mem_pullL {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    (hA : ∀ p, Agree δ M p) (T T' i s : ℕ) (p : PlF D) (t : D.host.E) :
    t ∈ (pullS M δ T T' i s p).L ↔ uS δ p i s * (D.s.atP p).ιE t ∈ (M p).R := by
  simp only [pullS, J.phaseSys, J.pullSys, AddSubgroup.mem_comap, AddMonoidHom.coe_comp,
    Function.comp_apply, AddMonoidHom.coe_mulLeft, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
    Subring.mem_toAddSubgroup]
  rw [uU_val (hA p).2.1]

theorem uU_inv {δ : ∀ p : PlF D, (D.s.atP p).Fp} {p : PlF D} (hδ : δ p ≠ 0) (i s : ℕ) {v : (D.s.atP p).Ep}
    (hv : uS δ p i s * v = 1) : (((uU δ p i s)⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) = v := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [uU_val hδ]
  exact hv

theorem mem_pullL' {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    (T T' i s : ℕ) (p : PlF D) (x : D.host.E) :
    x ∈ (pullS M δ T T' i s p).L' ↔
      (((uU δ p i s)⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) * (D.s.atP p).ιE x ∈ (M p).R := by
  simp only [pullS, J.phaseSys, J.pullSys, AddSubgroup.mem_comap, AddMonoidHom.coe_comp,
    Function.comp_apply, AddMonoidHom.coe_mulLeft, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
    Subring.mem_toAddSubgroup]

theorem isOut_outS {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (T T' : ℕ) {m s : ℕ} (hm : m ≤ D.R.rS) (Y : Finset (TB.Pt D.host.E))
    (X0 : Finset D.host.E) (hX0 : ∀ h ∈ Y, scal (hpt D m h) ⊆ X0) (P : Finset (PlF D))
    (hP : ∀ p, p ∉ P → Gd δ M p X0) (tp : Prop) (htp : ¬ tp) :
    PB.IsOut (outS M δ T T' (m + s) s P (Qf δ M hA X0 (sgn D (m + s)) P)) Y s tp := by
  have hms : m + s - s = m := Nat.add_sub_cancel _ _
  refine ⟨fun _ _ _ _ => rfl, fun t t' ht ht' => ⟨{q // q ∈ Qf δ M hA X0 (sgn D (m + s)) P t t'}, inferInstance,
    fun q => pullS M δ T T' (m + s) s q.1, fun q => Or.inr ⟨htp, ?_⟩, fun h _ h' _ => ?_, fun hq => ?_, fun hq => ?_⟩⟩
  · refine isPull_pullS hA T T' (m + s) s (by omega) q.1 Y true fun _ h hh => ?_
    have hqP : q.1 ∉ P := (Finset.mem_sdiff.1 q.2).2
    rw [hms]
    exact etaH_glr hA T T' (hP q.1 hqP) h (hX0 h hh)
  · exact (Finset.prod_coe_sort _ (fun q => (pullS M δ T T' (m + s) s q).N t t' h h')).symm
  · show t ∈ ⨅ p : {p // p ∉ P}, (pullS M δ T T' (m + s) s p.1).L
    rw [AddSubgroup.mem_iInf]
    intro p
    by_cases hpq : p.1 ∈ Qf δ M hA X0 (sgn D (m + s)) P t t'
    · exact hq ⟨p.1, hpq⟩
    · have hG := qf_gd hA X0 _ P t t' p.1 p.2 hpq
      rw [mem_pullL hA, uS_mul, R_eq_O (hA _) hG.1]
      exact (unitIn_mul (gd_elt hG (by simp [X1]) (mul_ne_zero (sgn_ne _) ht)) (hF_good hA hG _ _)).1
  · show t⁻¹ - t'⁻¹ ∈ ⨅ p : {p // p ∉ P}, (pullS M δ T T' (m + s) s p.1).L'
    rw [AddSubgroup.mem_iInf]
    intro p
    by_cases hpq : p.1 ∈ Qf δ M hA X0 (sgn D (m + s)) P t t'
    · exact hq ⟨p.1, hpq⟩
    · have hG := qf_gd hA X0 _ P t t' p.1 p.2 hpq
      rw [mem_pullL', R_eq_O (hA _) hG.1]
      obtain ⟨-, v, hv, huv⟩ := uS_good hA hG (m + s) s
      rw [uU_inv (hA _).2.1 _ _ huv]
      by_cases hy : t⁻¹ - t'⁻¹ = 0
      · rw [hy, map_zero, mul_zero]; exact Subring.zero_mem _
      · exact Subring.mul_mem _ hv (gd_elt hG (by simp [X1]) hy).1

end Pull

section Lat

variable {D : Formalism.BasicNotions.D7}

theorem explicit_formula_bound_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum.adm7 D :=
  product_formula_e _ _ _ (Formalism.BasicNotions.Examples₂.finrank_FE D.host) D.s.atP

theorem negOnePow_mem {B : Type} [CommRing B] (R : Subring B) (k : ℕ) (x : B) :
    (-1) ^ k * x ∈ R ↔ x ∈ R := by
  rcases neg_one_pow_eq_or B k with h | h
  · rw [h, one_mul]
  · rw [h, neg_one_mul, neg_mem_iff]

theorem nuB_eq (r m s : ℕ) (hs : 1 ≤ s) (hm : m + s ≤ r + 1) :
    Formalism.FourierDecayAlt.S6.nuBlock (r : ℤ) ((m + s - s + 1 : ℕ) : ℤ) (s : ℤ) = ((nu r (m + 1) (m + s) : ℕ) : ℤ) := by
  have e1 : m + s - s + 1 = m + 1 := by omega
  have e2 : nu r (m + 1) (m + s) + (m + 1) + (m + s) = 2 * (r + 1) := by unfold nu; omega
  rw [e1, Formalism.FourierDecayAlt.S6.nuBlock]
  have e3 : ((nu r (m + 1) (m + s) : ℕ) : ℤ) = 2 * ((r : ℤ) + 1) - ((m : ℤ) + 1) - ((m : ℤ) + s) := by
    have : ((nu r (m + 1) (m + s) + (m + 1) + (m + s) : ℕ) : ℤ) = ((2 * (r + 1) : ℕ) : ℤ) := by rw [e2]
    push_cast at this
    linarith
  rw [e3]
  push_cast
  ring

theorem all_of_sysP {E ι : Type} [Field E] {P0 : Finset ι} {f : Option {p // p ∈ P0} → AddSubgroup E}
    {g : ι → AddSubgroup E} (hn : f none = ⨅ p : {p // p ∉ P0}, g p.1) (hs : ∀ p, f (some p) = g p.1)
    (t : E) : t ∈ ⨅ j, f j ↔ ∀ p, t ∈ g p := by
  rw [AddSubgroup.mem_iInf]
  constructor
  · intro h p
    by_cases hp : p ∈ P0
    · rw [← hs ⟨p, hp⟩]; exact h (some ⟨p, hp⟩)
    · have := h none
      rw [hn, AddSubgroup.mem_iInf] at this
      exact this ⟨p, hp⟩
  · intro h j
    cases j with
    | none => rw [hn, AddSubgroup.mem_iInf]; exact fun p => h p.1
    | some p => rw [hs]; exact h p.1

variable {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)]
    [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem lat_L_mem {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (S : C.HidaSetting D.host.E Wp Wq) (hr : S.G.r = D.R.rS) (hg : S.g = Lat.gS D)
    (T T' : ℕ) {m s : ℕ} (hs : 1 ≤ s) (hm : m + s ≤ D.R.rS + 1) (t : D.host.E) :
    t ∈ J.LaB D.host.E S.g S.G.r (m + s - s + 1) s ↔ ∀ p, t ∈ (pullS M δ T T' (m + s) s p).L := by
  have e : ∀ p, uS δ p (m + s) s * (D.s.atP p).ιE t =
      (-1) ^ (D.R.rS + 1 - (m + s)) * tMod δ p (nu D.R.rS (m + 1) (m + s)) s t := by
    intro p
    have h1 := tMod_eq δ p (m + 1) s t
    have e5 : m + 1 + s - 1 = m + s := by omega
    rw [e5] at h1
    rw [h1, uS_mul, map_mul, ιE_sgn]
    have e4 : m + s - s + 1 = m + 1 := by omega
    rw [e4]
    ring
  have h1 : (∀ p, t ∈ (pullS M δ T T' (m + s) s p).L) ↔ t ∈ La M δ (nu D.R.rS (m + 1) (m + s)) s := by
    simp only [mem_pullL hA, e, negOnePow_mem]
    rfl
  have h2 := Formalism.MainNotions.LocalModelPeriodLattices.mem_perLat_iff δ M (nu D.R.rS (m + 1) (m + s)) s
    (Formalism.MainNotions.BridgeLemma.laIsPeriod_of_adm δ M hA (UpperTheory.Prune.fundamentalExactSequence_continuity_all_theories D) (explicit_formula_bound_holds D) _ s) t
  refine Iff.trans ?_ (h2.trans h1.symm)
  unfold J.LaB
  rw [hg, hr, nuB_eq _ _ _ hs hm]
  exact Submodule.mem_toAddSubgroup _

theorem lat_L'_mem {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (S : C.HidaSetting D.host.E Wp Wq) (hr : S.G.r = D.R.rS) (hg : S.g = Lat.gS D)
    (T T' : ℕ) {m s : ℕ} (hs : 1 ≤ s) (hm : m + s ≤ D.R.rS + 1) (x : D.host.E)
    (hx : ∀ p, x ∈ (pullS M δ T T' (m + s) s p).L') : x ∈ J.LapB D.host.E S.g S.G.r (m + s - s + 1) s := by
  set ν := nu D.R.rS (m + 1) (m + s) with hν
  have h2 : ∀ p, Formalism.MainNotions.BridgeLemma.tModInv δ p ν s x ∈ (M p).R := by
    intro p
    have h1 := (mem_pullL' T T' (m + s) s p x).1 (hx p)
    have hδ := (hA p).2.1
    have htm := tMod_eq δ p (m + 1) s 1
    have e5 : m + 1 + s - 1 = m + s := by omega
    rw [e5, map_one, one_mul] at htm
    have hmi := Formalism.MainNotions.BridgeLemma.tMod_mul_tModInv δ p hδ ν s 1 one_ne_zero
    rw [inv_one, htm] at hmi
    have hinv : uS δ p (m + s) s * ((D.s.atP p).ιE (sgn D (m + s)) * Formalism.MainNotions.BridgeLemma.tModInv δ p ν s 1) = 1 := by
      have e4 : m + s - s + 1 = m + 1 := by omega
      unfold uS
      rw [e4]
      calc (D.s.atP p).ιE (sgn D (m + s)) * PI.SupportDatumW.hF D δ p (m + 1) s *
            ((D.s.atP p).ιE (sgn D (m + s)) * Formalism.MainNotions.BridgeLemma.tModInv δ p ν s 1)
          = ((D.s.atP p).ιE (sgn D (m + s)) * (D.s.atP p).ιE (sgn D (m + s))) *
            (PI.SupportDatumW.hF D δ p (m + 1) s * Formalism.MainNotions.BridgeLemma.tModInv δ p ν s 1) := by ring
        _ = 1 := by rw [hmi, ← map_mul, sgn, ← pow_add, ← two_mul, pow_mul]; simp
    rw [uU_inv hδ _ _ hinv] at h1
    have htmi : Formalism.MainNotions.BridgeLemma.tModInv δ p ν s x =
        Formalism.MainNotions.BridgeLemma.tModInv δ p ν s 1 * (D.s.atP p).ιE x := by
      unfold Formalism.MainNotions.BridgeLemma.tModInv
      rw [PI.SupportDatumW.twist_mul p s ((D.s.atP p).ιE x), map_one]
      ring
    rw [htmi]
    rw [mul_assoc, ιE_sgn, negOnePow_mem] at h1
    exact h1
  have h3 := (Formalism.MainNotions.BridgeLemma.localCondition_iff δ M hA
    (Formalism.MainNotions.BridgeLemma.isDiffGen_of_agree δ M hA (UpperTheory.Prune.fundamentalExactSequence_continuity_all_theories D) (explicit_formula_bound_holds D)) ν s x).2 h2
  have := Formalism.MainNotions.LocalModelPeriodLattices.cmE D
  unfold J.LapB
  rw [hg, hr, nuB_eq _ _ _ hs hm]
  refine (Submodule.mem_toAddSubgroup _).2 ?_
  rw [Formalism.FourierDecayAlt.S6.liftLat, Formalism.FourierDecayAlt.P.S6x1.mem_twLat, ← Formalism.MainNotions.LocalModelPeriodLattices.gdd_eq_idl, ← Formalism.MainNotions.LocalModelPeriodLattices.gdd_eq_idl,
    ← Formalism.MainNotions.LocalModelPeriodLattices.conjF_eq_complexConj]
  exact h3

end Lat

section AssemblyPull

variable {D : Formalism.BasicNotions.D7} {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)]
    [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem krOf_none {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (T T' : ℕ) {i : ℕ} (hi : i ≠ 0) {x y : TB.Pt D.host.E} (h : ptOfList i x = none ∨ ptOfList i y = none) :
    KrOf δ M T T' i x y = 0 := by
  unfold KrOf
  rw [if_neg hi]
  split_ifs
  · rfl
  · rcases h with h | h
    · rw [h]
    · rw [h]; rcases ptOfList i x <;> rfl

theorem krOf_zero_none {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (T T' : ℕ) {x y : TB.Pt D.host.E} (h : ptOfList 0 x = none ∨ ptOfList 0 y = none) :
    KrOf δ M T T' 0 x y = 0 := by
  have hn : ptOfList (D := D) 0 [] ≠ none := by
    obtain ⟨w, hw, -⟩ := ptOfList_of (D := D) (i := 0) (x := []) ⟨by simp [signPt, signAux], by simp [signPt, signAux]⟩
    rw [hw]; exact Option.some_ne_none _
  unfold KrOf
  rw [if_pos rfl, if_neg]
  rintro ⟨rfl, rfl⟩
  rcases h with h | h <;> exact hn h

theorem krOf_head_none {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (T T' m : ℕ) {x y : TB.Pt D.host.E}
    (h : ptOfList m x = none ∨ ptOfList m y = none) : KrOf δ M T T' m x y = 0 := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; exact krOf_zero_none T T' h
  · exact krOf_none T T' (by omega) h

theorem wt_none {m s : ℕ} {h : TB.Pt D.host.E} (hw : ptOfList m h = none) : wt D m s h = 0 := by
  simp [wt, hw]

theorem wt_some {m s : ℕ} {h : TB.Pt D.host.E} {w : Point D.host.E m} (hw : ptOfList m h = some w) :
    wt D m s h = (phi m h * blkN D 1 h ^ s)⁻¹ := by
  simp [wt, hw]

theorem prod_P_Q {P Q : Finset (PlF D)} (hQ : Disjoint Q P) (f : PlF D → ℂ) :
    (∏ q ∈ Q, f q) * ∏ x : {p // p ∈ P}, f x.1 = ∏ p ∈ P ∪ Q, f p := by
  rw [Finset.prod_coe_sort P f, Finset.prod_union hQ.symm, mul_comm]

theorem clS_pull (hMN : ModNorm D) {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p)
    (S : C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word) (hr : S.G.r = D.R.rS) (hg : S.g = Lat.gS D) {i s : ℕ}
    (hs1 : 1 ≤ s) (hsi : s ≤ i) (hir : i ≤ D.R.rS + 1) (hnt : ¬ (i = D.R.rS + 1 ∧ s = 1))
    (Y : Finset (TB.Pt D.host.E)) (hY : ∀ h ∈ Y, TB.level h = i - s) :
    ∃ (P : Type) (_ : Fintype P) (Sy : P → J.LocSys D.host.E (TB.Pt D.host.E)) (a : TB.Pt D.host.E → ℝ),
      (∀ p, ((i = D.R.rS + 1 ∧ s = 1) ∧ PB.IsTopSys (Sy p) Y false) ∨
        (¬ (i = D.R.rS + 1 ∧ s = 1) ∧ PB.IsPull (Sy p) Y s false) ∨ PB.IsOut (Sy p) Y s (i = D.R.rS + 1 ∧ s = 1)) ∧
      (∀ t t', t ≠ 0 → t' ≠ 0 → ∀ h ∈ Y, ∀ h' ∈ Y,
        (J.sysOf (dOf S δ M u u') i s).N t t' h h' = (J.scaleSys a (J.prodSys Sy)).N t t' h h') ∧
      (∀ h ∈ Y, ∀ h' ∈ Y, (J.sysOf (dOf S δ M u u') i s).B h h' = (J.scaleSys a (J.prodSys Sy)).B h h') ∧
      (J.sysOf (dOf S δ M u u') i s).L = ⨅ p, (Sy p).L ∧ (⨅ p, (Sy p).L') ≤ (J.sysOf (dOf S δ M u u') i s).L' := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + s := ⟨i - s, by omega⟩
  have hms : m + s - s = m := Nat.add_sub_cancel m s
  have hmr : m ≤ D.R.rS := by omega
  have hY' : ∀ h ∈ Y, TB.level h = m := fun h hh => (hY h hh).trans hms
  set T := (D.mem u).A.T with hT
  set T' := (D.mem u').A.T with hT'
  set X0 : Finset D.host.E := Y.biUnion fun h => scal (hpt D m h) with hX0
  have hX0' : ∀ h ∈ Y, scal (hpt D m h) ⊆ X0 := fun h hh =>
    Finset.subset_biUnion_of_mem (fun h => scal (hpt D m h)) hh
  obtain ⟨p0⟩ := LocModel.plF_nonempty D
  set P : Finset (PlF D) := insert p0 (gd_finite δ M hA X0).toFinset with hPdef
  have hP : ∀ p, p ∉ P → Gd δ M p X0 := fun p hp => by
    by_contra hn
    exact hp (Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).2 hn))
  set Q := Qf δ M hA X0 (sgn D (m + s)) P with hQ
  have hQP : ∀ t t', Disjoint (Q t t') P := fun t t' => Finset.sdiff_disjoint
  have hPQ : ∀ t t' p, p ∉ P ∪ Q t t' → Gd δ M p (X1 X0 (sgn D (m + s)) t t') := by
    intro t t' p hp
    rw [Finset.mem_union, not_or] at hp
    exact qf_gd hA X0 _ P t t' p hp.1 hp.2
  have hX1 : ∀ t t', X0 ⊆ X1 X0 (sgn D (m + s)) t t' := fun t t' => Finset.subset_union_left
  refine ⟨Option {p // p ∈ P}, inferInstance, sysP M δ T T' (m + s) s P Q, wt D m s, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    cases j with
    | none => exact Or.inr (Or.inr (isOut_outS hA T T' hmr Y X0 hX0' P hP _ hnt))
    | some p =>
      exact Or.inr (Or.inl ⟨hnt, isPull_pullS hA T T' (m + s) s (by omega) p.1 Y false (fun h => by simp at h)⟩)
  · intro t t' ht ht' h hh h' hh'
    simp only [J.sysOf, J.scaleSys, J.prodSys, Fintype.prod_option, dOf_Kr]
    change KrOf δ M T T' (m + s) (TB.join h s t) (TB.join h' s t') = (wt D m s h : ℂ) * (wt D m s h' : ℂ) *
      ((∏ q ∈ Q t t', (pullS M δ T T' (m + s) s q).N t t' h h') *
        ∏ x : {p // p ∈ P}, (pullS M δ T T' (m + s) s x.1).N t t' h h')
    rw [prod_P_Q (hQP t t')]
    rcases hw : ptOfList m h with _ | w
    · rw [wt_none hw, krOf_none T T' (by omega) (Or.inl (ptOfList_join_none (hY' h hh) hw t))]
      simp
    rcases hw' : ptOfList m h' with _ | w'
    · rw [wt_none hw', krOf_none T T' (by omega) (Or.inr (ptOfList_join_none (hY' h' hh') hw' t'))]
      simp
    have hXw : scal w ⊆ X1 X0 (sgn D (m + s)) t t' := by
      rw [← hpt_of hw]; exact (hX0' h hh).trans (hX1 t t')
    have hXw' : scal w' ⊆ X1 X0 (sgn D (m + s)) t t' := by
      rw [← hpt_of hw']; exact (hX0' h' hh').trans (hX1 t t')
    rw [krOf_join hMN hA T T' hs1 (by omega) hnt (hY' h hh) (hY' h' hh') hw hw' ht ht' (P ∪ Q t t') hXw hXw'
      (by simp [X1]) (by simp [X1]) (hPQ t t'), wt_some hw, wt_some hw']
    push_cast
    ring
  · intro h hh h' hh'
    simp only [J.sysOf, J.scaleSys, J.prodSys, Fintype.prod_option, dOf_Kr, dOf_e]
    change (1 + ((0 : ℝ) : ℂ)) * KrOf δ M T T' (m + s - s) h h' = (wt D m s h : ℂ) * (wt D m s h' : ℂ) *
      (1 * ∏ x : {p // p ∈ P}, (pullS M δ T T' (m + s) s x.1).B h h')
    rw [hms, Finset.prod_coe_sort P (fun p => (pullS M δ T T' (m + s) s p).B h h')]
    rcases hw : ptOfList m h with _ | w
    · rw [wt_none hw, krOf_head_none T T' m (Or.inl hw)]
      simp
    rcases hw' : ptOfList m h' with _ | w'
    · rw [wt_none hw', krOf_head_none T T' m (Or.inr hw')]
      simp
    have hXw : scal w ⊆ X0 := by rw [← hpt_of hw]; exact hX0' h hh
    have hXw' : scal w' ⊆ X0 := by rw [← hpt_of hw']; exact hX0' h' hh'
    have hB : ∀ p, (pullS M δ T T' (m + s) s p).B h h' =
        ((A5.cSize (M p).R (etaW δ T T' p w) ^ s * A5.cSize (M p).R (etaW δ T T' p w') ^ s : ℝ) : ℂ) *
          A5.Kp (M p).R (M p).psiR (etaW δ T T' p w) (etaW δ T T' p w') := by
      intro p
      simp only [pullS, J.phaseSys, J.pullSys, etaH, A5.N0]
      rw [hms, hpt_of hw, hpt_of hw']
    rw [Finset.prod_congr rfl (fun p _ => hB p), Finset.prod_mul_distrib, ← krOf_head hA T T' hmr hw hw' P hXw hXw' hP]
    have hc : ∏ p ∈ P, ((A5.cSize (M p).R (etaW δ T T' p w) ^ s * A5.cSize (M p).R (etaW δ T T' p w') ^ s : ℝ) : ℂ) =
        (((blkN D 1 h) ^ s * (blkN D 1 h') ^ s : ℝ) : ℂ) := by
      rw [← Complex.ofReal_prod, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow,
        head_prod hMN hA T T' hmr w P hXw hP, head_prod hMN hA T T' hmr w' P hXw' hP, blkN_hpt hw, blkN_hpt hw']
    rw [hc, wt_some hw, wt_some hw']
    have p1 := phi_pos (isPtL_of_ptOfList hw)
    have p2 := phi_pos (isPtL_of_ptOfList hw')
    have b1 := blkN_pos (D := D) 1 h (fun c hc => ((isPtL_of_ptOfList hw).2 c hc).2)
    have b2 := blkN_pos (D := D) 1 h' (fun c hc => ((isPtL_of_ptOfList hw').2 c hc).2)
    have q1 : ((phi m h : ℝ) : ℂ) ≠ 0 := by exact_mod_cast p1.ne'
    have q2 : ((phi m h' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast p2.ne'
    have q3 : ((blkN D 1 h : ℝ) : ℂ) ≠ 0 := by exact_mod_cast b1.ne'
    have q4 : ((blkN D 1 h' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast b2.ne'
    push_cast
    field_simp
    ring
  · have eL : (J.sysOf (dOf S δ M u u') (m + s) s).L = J.LaB D.host.E S.g S.G.r (m + s - s + 1) s := rfl
    rw [eL]
    refine AddSubgroup.ext fun t => ?_
    exact (lat_L_mem hA S hr hg T T' hs1 (by omega) t).trans
      (all_of_sysP (f := fun j => (sysP M δ T T' (m + s) s P Q j).L)
        (g := fun p => (pullS M δ T T' (m + s) s p).L) rfl (fun _ => rfl) t).symm
  · have eL' : (J.sysOf (dOf S δ M u u') (m + s) s).L' = J.LapB D.host.E S.g S.G.r (m + s - s + 1) s := rfl
    rw [eL']
    intro x hx0
    have hx := (all_of_sysP (f := fun j => (sysP M δ T T' (m + s) s P Q j).L')
      (g := fun p => (pullS M δ T T' (m + s) s p).L') rfl (fun _ => rfl) x).1 hx0
    exact lat_L'_mem hA S hr hg T T' hs1 (by omega) x hx

end AssemblyPull

section Top

variable {D : Formalism.BasicNotions.D7}

theorem nSh_unit {A : Type} [CommRing A] {c : A} (h : ∃ n : Fin 3, IsUnit (c + (((n : Fin 3) : ℕ) : A))) :
    IsUnit (c + ((nSh c : ℕ) : A)) := by
  unfold nSh
  rw [dif_pos h]
  exact h.choose_spec

theorem tauZero_of_not_split {p : PlF D} (h : (D.s.atP p).split = none) (T T' : ℕ) : tau0 p T T' = 0 := by
  simp [tau0, h]

theorem exists_shift {δ : ∀ p : PlF D, (D.s.atP p).Fp} (p : PlF D) (hδ : δ p ≠ 0) (T T' i s : ℕ) {t : D.host.E}
    (ht : t ≠ 0) : ∃ n : Fin 3, IsUnit ((uS δ p i s * (D.s.atP p).ιE t - tau0 p T T') +
      (((n : Fin 3) : ℕ) : (D.s.atP p).Ep)) := by
  rcases hs : (D.s.atP p).split with _ | sg
  · refine ⟨0, ?_⟩
    rw [tauZero_of_not_split hs]
    simpa using (isUnit_uS p hδ i s).mul (isUnit_ιE p ht)
  · have := (D.s.atP p).char0
    set c := uS δ p i s * (D.s.atP p).ιE t - tau0 p T T'
    by_contra H
    push Not at H
    have key : ∀ n : ℕ, n < 3 → (sg.e c).1 + n = 0 ∨ (sg.e c).2 + n = 0 := by
      intro n hn
      have h1 := H ⟨n, hn⟩
      simp only at h1
      rw [← MulEquiv.isUnit_map sg.e.toRingEquiv.toMulEquiv] at h1
      simp only [RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_toMulEquiv, AlgEquiv.coe_ringEquiv, map_add, map_natCast, Prod.isUnit_iff, Prod.fst_add, Prod.snd_add,
        Prod.fst_natCast, Prod.snd_natCast, isUnit_iff_ne_zero, not_and_or, not_not] at h1
      exact h1
    have h0 := key 0 (by norm_num)
    have h1 := key 1 (by norm_num)
    have h2 := key 2 (by norm_num)
    push_cast at h0 h1 h2
    have o1 : (1 : (D.s.atP p).Fp) ≠ 0 := one_ne_zero
    have o2 : (2 : (D.s.atP p).Fp) ≠ 0 := two_ne_zero
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    all_goals first
      | exact o1 (by linear_combination h1 - h0)
      | exact o2 (by linear_combination h2 - h0)
      | exact o1 (by linear_combination h2 - h1)

def thetaT {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (c : K) (h h' : A5.Point K) : ℂ :=
  if hu : IsUnit (c + ((nSh c : ℕ) : K)) then A5.Ns R ψ 1 h h' hu.unit hu.unit else 0

def topS (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (T T' : ℕ) (p : PlF D) : J.LocSys D.host.E (TB.Pt D.host.E) :=
  J.topSys (M p).R (M p).psiR (D.s.atP p).ιE (uU δ p (D.R.rS + 1) 1) (tau0 p T T')
    (etaH δ T T' (D.R.rS + 1 - 1) p) (thetaT (M p).R (M p).psiR)

theorem topS_L (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (T T' : ℕ) (p : PlF D) : (topS M δ T T' p).L = (pullS M δ T T' (D.R.rS + 1) 1 p).L := rfl

theorem top_same {E K α : Type} [Field E] [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (σ : E →+* K) (u : Kˣ)
    (τ₀ : K) (η : α → A5.Point K) (m : ℕ) (hη : ∀ h, (η h).1.sum = m) (Θ : K → A5.Point K → A5.Point K → ℂ)
    (hper : ∀ x, ∀ r ∈ R, Θ (x + r) = Θ x)
    (hag : ∀ (c : Kˣ) (h h' : A5.Point K), h.1.sum = m → h'.1.sum = m → Θ (c : K) h h' = A5.Ns R ψ 1 h h' c c)
    (hex : ∀ t : E, t ≠ 0 → ∃ n : Fin 3, IsUnit ((u : K) * σ t - τ₀ + (((n : Fin 3) : ℕ) : K)))
    (t t' : E) (ht : t ≠ 0) (h h' : α) :
    (J.topSys R ψ σ u τ₀ η (thetaT R ψ)).N t t' h h' = (J.topSys R ψ σ u τ₀ η Θ).N t t' h h' := by
  simp only [J.topSys]
  split_ifs with htt
  · have hu := nSh_unit (hex t ht)
    rw [thetaT, dif_pos hu, ← hper _ _ (natCast_mem R _)]
    conv_rhs => rw [← IsUnit.unit_spec hu]
    exact (hag _ _ _ (hη h) (hη h')).symm
  · rfl

theorem isTopSys_topS {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (T T' : ℕ) (p : PlF D) (Y : Finset (TB.Pt D.host.E)) (un : Bool)
    (hun : un = true → (∀ h ∈ Y, A5.InGLR (M p).R (etaH δ T T' (D.R.rS + 1 - 1) p h)) ∧ tau0 p T T' ∈ (M p).R) :
    PB.IsTopSys (topS M δ T T' p) Y un := by
  have hm : D.R.rS + 1 - 1 ≤ D.R.rS := by omega
  refine ⟨LocModel.placeOf M (fun q => (hA q).1) p, uU δ p (D.R.rS + 1) 1, tau0 p T T',
    etaH δ T T' (D.R.rS + 1 - 1) p, D.R.rS + 1 - 1, fun h _ => etaH_sum T T' p (hA p).2.1 hm h, hun,
    fun Θ hper hag => ⟨fun t t' ht _ h _ h' _ => top_same (M p).R (M p).psiR (D.s.atP p).ιE (uU δ p (D.R.rS + 1) 1)
      (tau0 p T T') (etaH δ T T' (D.R.rS + 1 - 1) p) _ (fun h => etaH_sum T T' p (hA p).2.1 hm h) Θ hper hag
      (fun t ht => by rw [uU_val (hA p).2.1]; exact exists_shift p (hA p).2.1 T T' _ _ ht) t t' ht h h',
      fun _ _ _ _ => rfl, rfl, rfl⟩⟩

def outT (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (T T' : ℕ) (P : Finset (PlF D)) (Q : D.host.E → D.host.E → Finset (PlF D)) :
    J.LocSys D.host.E (TB.Pt D.host.E) where
  N := fun t t' h h' => ∏ q ∈ Q t t', (topS M δ T T' q).N t t' h h'
  Th := fun _ _ _ => 0
  B := fun _ _ => 1
  L := ⨅ p : {p // p ∉ P}, (topS M δ T T' p.1).L
  L' := ⊤

def sysT (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (T T' : ℕ) (P : Finset (PlF D)) (Q : D.host.E → D.host.E → Finset (PlF D)) :
    Option {p // p ∈ P} → J.LocSys D.host.E (TB.Pt D.host.E)
  | none => outT M δ T T' P Q
  | some p => topS M δ T T' p.1

theorem isOut_outT {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (T T' : ℕ) (Y : Finset (TB.Pt D.host.E))
    (X0 : Finset D.host.E) (hX0 : ∀ h ∈ Y, scal (hpt D D.R.rS h) ⊆ X0) (P : Finset (PlF D))
    (hP : ∀ p, p ∉ P → Gd δ M p X0) :
    PB.IsOut (outT M δ T T' P (Qf δ M hA X0 (sgn D (D.R.rS + 1)) P)) Y 1 (D.R.rS + 1 = D.R.rS + 1 ∧ 1 = 1) := by
  have hr1 : D.R.rS + 1 - 1 = D.R.rS := Nat.add_sub_cancel _ _
  refine ⟨fun _ _ _ _ => rfl, fun t t' ht ht' => ⟨{q // q ∈ Qf δ M hA X0 (sgn D (D.R.rS + 1)) P t t'},
    Finset.fintypeCoeSort _, fun q => topS M δ T T' q.1, fun q => Or.inl ⟨⟨rfl, rfl⟩, ?_⟩, fun h _ h' _ => ?_, fun hq => ?_, fun _ => trivial⟩⟩
  · have hqP : q.1 ∉ P := (Finset.mem_sdiff.1 q.2).2
    have hG := hP q.1 hqP
    refine isTopSys_topS hA T T' q.1 Y true fun _ => ⟨fun h hh => ?_, ?_⟩
    · rw [hr1]
      exact etaH_glr hA T T' hG h (hX0 h hh)
    · rw [tauZero_of_not_split (LocModel.split_none_of_agree (hA _) hG.1)]
      exact Subring.zero_mem _
  · exact (Finset.prod_coe_sort _ (fun q => (topS M δ T T' q).N t t' h h')).symm
  · show t ∈ ⨅ p : {p // p ∉ P}, (topS M δ T T' p.1).L
    rw [AddSubgroup.mem_iInf]
    intro p
    by_cases hpq : p.1 ∈ Qf δ M hA X0 (sgn D (D.R.rS + 1)) P t t'
    · exact hq ⟨p.1, hpq⟩
    · have hG := qf_gd hA X0 _ P t t' p.1 p.2 hpq
      rw [topS_L, mem_pullL hA, uS_mul, R_eq_O (hA _) hG.1]
      exact (unitIn_mul (gd_elt hG (by simp [X1]) (mul_ne_zero (sgn_ne _) ht)) (hF_good hA hG _ _)).1

end Top

section AssemblyTop

variable {D : Formalism.BasicNotions.D7} {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)]
    [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem phi_join {m s : ℕ} (g : TB.Pt D.host.E) (x : D.host.E) (hg : TB.level g = m) :
    phi (m + s) (TB.join g s x) = phi m g * blkN D 1 g ^ s *
      nrm (D := D) (nu D.R.rS (m + 1) (m + s)) x ^ (s * (s - 1) / 2) := by
  unfold phi TB.join
  rw [blockProduct_append, blockProduct_shift m s 1 g (by omega), hg]
  simp only [blockWeightPhi]
  have e1 : 1 + m = m + 1 := by ring
  have e2 : m + 1 + s - 1 = m + s := by omega
  have e3 : m + s - (m + s) = 0 := by omega
  rw [e1, e2, e3]
  ring

theorem kind_top {w : Point D.host.E D.R.rS} {W : Point D.host.E (D.R.rS + 1)} {x : D.host.E}
    (hW : W.1 = w.1 ++ [(x, 1)]) : kind W = some x := by
  have h1 := PI.SupportDatumW.dmin_last_one D W w.1 x hW
  have h2 : PI.SupportDatumW.blkDet w.1 ≠ 0 := PI.SupportDatumW.blkDet_ne_zero w.1 fun b hb => (w.2.1 b hb).1
  unfold kind zetaOf
  rw [if_neg (by rw [h1]; exact h2), h1, PI.SupportDatumW.dmin_top, hW, PI.SupportDatumW.blkDet_append]
  simp [PI.SupportDatumW.blkDet, h2]

theorem dfac_top (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (T T' : ℕ) (p : PlF D) {w : Point D.host.E D.R.rS} {W : Point D.host.E (D.R.rS + 1)} {x : D.host.E}
    (hW : W.1 = w.1 ++ [(x, 1)]) : dfac M δ T T' p W = 1 := by
  have hl : W.1.getLast? = some (x, 1) := by
    rw [hW, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
    rfl
  unfold dfac
  rw [hl]
  rcases (D.s.atP p).split with _ | sg <;> rfl

theorem locK_top {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (T T' : ℕ) (p : PlF D) {w w' : Point D.host.E D.R.rS}
    {W W' : Point D.host.E (D.R.rS + 1)} {t : D.host.E} (ht : t ≠ 0)
    (hW : W.1 = w.1 ++ [(sgn D (D.R.rS + 1) * t, 1)]) (hW' : W'.1 = w'.1 ++ [(sgn D (D.R.rS + 1) * t, 1)])
    {a a' : Loc.Pt (D.s.atP p).Ep D.R.rS} (ha : modPt δ T T' p w = some a) (ha' : modPt δ T T' p w' = some a') :
    locK M δ T T' p (D.R.rS + 1) W W' =
      thetaT (M p).R (M p).psiR (uS δ p (D.R.rS + 1) 1 * (D.s.atP p).ιE t - tau0 p T T')
        (Formalism.MainNotions.LocalModelPeriodLattices.tr a) (Formalism.MainNotions.LocalModelPeriodLattices.tr a') := by
  have hc : blkTop δ T T' p (D.R.rS + 1) 1 (sgn D (D.R.rS + 1) * t) =
      (uS δ p (D.R.rS + 1) 1 * (D.s.atP p).ιE t - tau0 p T T') +
        ((nSh (uS δ p (D.R.rS + 1) 1 * (D.s.atP p).ιE t - tau0 p T T') : ℕ) : (D.s.atP p).Ep) := by
    have htop : D.R.rS + 1 + 1 - 1 = D.R.rS + 1 ∧ 1 = 1 := ⟨by omega, rfl⟩
    have hm : blkMod δ T T' p (D.R.rS + 1) 1 (sgn D (D.R.rS + 1) * t) =
        uS δ p (D.R.rS + 1) 1 * (D.s.atP p).ιE t - tau0 p T T' := by
      unfold blkMod
      rw [if_pos htop, tMod_eq, uS_mul]
      rfl
    unfold blkTop
    rw [if_pos htop, hm]
  have hu := nSh_unit (exists_shift p (hA p).2.1 T T' (D.R.rS + 1) 1 ht)
  have hu' : IsUnit (blkTop δ T T' p (D.R.rS + 1) 1 (sgn D (D.R.rS + 1) * t)) := by rw [hc]; exact hu
  have e1 : hu'.unit = hu.unit := by ext; rw [IsUnit.unit_spec, IsUnit.unit_spec, hc]
  unfold locK
  rw [modPt_snoc hW (by omega) ha hu', modPt_snoc hW' (by omega) ha' hu']
  simp only
  refine (Formalism.MainNotions.LocalOrbitGerms.KKAll_proved _ _ (M p) (hA p).1 _ _ _).trans ?_
  rw [thetaT, dif_pos hu, A5.Ns]
  simp only [Nat.sub_self, mul_zero, Nat.zero_div, pow_zero, Complex.ofReal_one, one_mul]
  exact congrArg₂ (A5.Kp (M p).R (M p).psiR)
    ((Formalism.MainNotions.LocalModelPeriodLattices.tr_snoc a hu'.unit _).trans (by rw [e1]; rfl))
    ((Formalism.MainNotions.LocalModelPeriodLattices.tr_snoc a' hu'.unit _).trans (by rw [e1]; rfl))

theorem topS_N {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) (T T' : ℕ) (p : PlF D) (t : D.host.E) (h h' : TB.Pt D.host.E) :
    (topS M δ T T' p).N t t h h' = thetaT (M p).R (M p).psiR (uS δ p (D.R.rS + 1) 1 * (D.s.atP p).ιE t - tau0 p T T')
      (etaH δ T T' (D.R.rS + 1 - 1) p h) (etaH δ T T' (D.R.rS + 1 - 1) p h') := by
  simp only [topS, J.topSys]
  rw [if_pos trivial, uU_val (hA p).2.1]

theorem krOf_top {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) (T T' : ℕ)
    {h h' : TB.Pt D.host.E} (hl : TB.level h = D.R.rS) (hl' : TB.level h' = D.R.rS) {w w' : Point D.host.E D.R.rS}
    (hw : ptOfList D.R.rS h = some w) (hw' : ptOfList D.R.rS h' = some w') {t : D.host.E} (ht : t ≠ 0)
    (P : Finset (PlF D)) {X : Finset D.host.E} (hX : scal w ⊆ X) (hX' : scal w' ⊆ X)
    (htX : sgn D (D.R.rS + 1) * t ∈ X) (hP : ∀ p, p ∉ P → Gd δ M p X) :
    KrOf δ M T T' (D.R.rS + 1) (TB.join h 1 t) (TB.join h' 1 t) =
      (((phi D.R.rS h * blkN D 1 h ^ 1 : ℝ) : ℂ))⁻¹ * (((phi D.R.rS h' * blkN D 1 h' ^ 1 : ℝ) : ℂ))⁻¹ *
        ∏ p ∈ P, (topS M δ T T' p).N t t h h' := by
  obtain ⟨W, hWo, hW⟩ := ptOfList_join hl hw (le_refl 1) ht
  obtain ⟨W', hWo', hW'⟩ := ptOfList_join hl' hw' (le_refl 1) ht
  have hK : KrOf δ M T T' (D.R.rS + 1) (TB.join h 1 t) (TB.join h' 1 t) =
      KtopG M δ T T' W W' / ((phi (D.R.rS + 1) (TB.join h 1 t) : ℂ) * (phi (D.R.rS + 1) (TB.join h' 1 t) : ℂ)) := by
    unfold KrOf
    rw [if_neg (by omega), if_neg (by omega), hWo, hWo']
    simp [Kglob]
  have hloc : ∀ p, locK M δ T T' p (D.R.rS + 1) W W' = (topS M δ T T' p).N t t h h' := by
    intro p
    obtain ⟨a, ha⟩ := modPt_low T T' p (hA p).2.1 (le_refl _) w
    obtain ⟨a', ha'⟩ := modPt_low T T' p (hA p).2.1 (le_refl _) w'
    rw [locK_top hA T T' p ht hW hW' ha ha', topS_N hA]
    have e : D.R.rS + 1 - 1 = D.R.rS := rfl
    unfold etaH
    rw [e, hpt_of hw, hpt_of hw', etaW_of ha, etaW_of ha']
  have hWX : scal W ⊆ X := by rw [scal_join hW]; exact Finset.union_subset hX (by simpa using htX)
  have hWX' : scal W' ⊆ X := by rw [scal_join hW']; exact Finset.union_subset hX' (by simpa using htX)
  have hG : KtopG M δ T T' W W' = ∏ p ∈ P, locK M δ T T' p (D.R.rS + 1) W W' := by
    unfold KtopG
    rw [if_pos ((kind_top hW).trans (kind_top hW').symm)]
    have e : ∀ p, KtopP M δ T T' p W W' = locK M δ T T' p (D.R.rS + 1) W W' := by
      intro p
      unfold KtopP
      rw [dfac_top M δ T T' p hW, dfac_top M δ T T' p hW']
      simp
    simp only [e]
    refine finprod_eq_prod_of_mulSupport_subset _ fun p hp => ?_
    by_contra hpP
    exact hp (Formalism.L2.SG.DataCut.locK_eq_one Formalism.MainNotions.LocalOrbitGerms.KKAll_proved hA
      (gd_notBad hA T T' (hP p hpP) W hWX) (gd_notBad hA T T' (hP p hpP) W' hWX'))
  rw [hK, hG, Finset.prod_congr rfl (fun p _ => hloc p), phi_join h t hl, phi_join h' t hl']
  simp only [Nat.sub_self, mul_zero, Nat.zero_div, pow_zero, mul_one]
  push_cast
  ring

theorem B_eq (hMN : ModNorm D) {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p)
    (S : C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word) {m s : ℕ} (hmr : m ≤ D.R.rS)
    (Y : Finset (TB.Pt D.host.E)) (X0 : Finset D.host.E) (hX0' : ∀ h ∈ Y, scal (hpt D m h) ⊆ X0) (P : Finset (PlF D))
    (hP : ∀ p, p ∉ P → Gd δ M p X0) (Sy : Option {p // p ∈ P} → J.LocSys D.host.E (TB.Pt D.host.E))
    (hn : ∀ h h', (Sy none).B h h' = 1)
    (hsm : ∀ p h h', (Sy (some p)).B h h' = (pullS M δ (D.mem u).A.T (D.mem u').A.T (m + s) s p.1).B h h') :
    ∀ h ∈ Y, ∀ h' ∈ Y, (J.sysOf (dOf S δ M u u') (m + s) s).B h h' = (J.scaleSys (wt D m s) (J.prodSys Sy)).B h h' := by
  have hms : m + s - s = m := Nat.add_sub_cancel m s
  set T := (D.mem u).A.T
  set T' := (D.mem u').A.T
  intro h hh h' hh'
  simp only [J.sysOf, J.scaleSys, J.prodSys, Fintype.prod_option, dOf_Kr, dOf_e, hn, hsm]
  change (1 + ((0 : ℝ) : ℂ)) * KrOf δ M T T' (m + s - s) h h' = (wt D m s h : ℂ) * (wt D m s h' : ℂ) *
    (1 * ∏ x : {p // p ∈ P}, (pullS M δ T T' (m + s) s x.1).B h h')
  rw [hms, Finset.prod_coe_sort P (fun p => (pullS M δ T T' (m + s) s p).B h h')]
  rcases hw : ptOfList m h with _ | w
  · rw [wt_none hw, krOf_head_none T T' m (Or.inl hw)]
    simp
  rcases hw' : ptOfList m h' with _ | w'
  · rw [wt_none hw', krOf_head_none T T' m (Or.inr hw')]
    simp
  have hXw : scal w ⊆ X0 := by rw [← hpt_of hw]; exact hX0' h hh
  have hXw' : scal w' ⊆ X0 := by rw [← hpt_of hw']; exact hX0' h' hh'
  have hB : ∀ p, (pullS M δ T T' (m + s) s p).B h h' =
      ((A5.cSize (M p).R (etaW δ T T' p w) ^ s * A5.cSize (M p).R (etaW δ T T' p w') ^ s : ℝ) : ℂ) *
        A5.Kp (M p).R (M p).psiR (etaW δ T T' p w) (etaW δ T T' p w') := by
    intro p
    simp only [pullS, J.phaseSys, J.pullSys, etaH, A5.N0]
    rw [hms, hpt_of hw, hpt_of hw']
  rw [Finset.prod_congr rfl (fun p _ => hB p), Finset.prod_mul_distrib, ← krOf_head hA T T' hmr hw hw' P hXw hXw' hP]
  have hc : ∏ p ∈ P, ((A5.cSize (M p).R (etaW δ T T' p w) ^ s * A5.cSize (M p).R (etaW δ T T' p w') ^ s : ℝ) : ℂ) =
      (((blkN D 1 h) ^ s * (blkN D 1 h') ^ s : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow,
      head_prod hMN hA T T' hmr w P hXw hP, head_prod hMN hA T T' hmr w' P hXw' hP, blkN_hpt hw, blkN_hpt hw']
  rw [hc, wt_some hw, wt_some hw']
  have p1 := phi_pos (isPtL_of_ptOfList hw)
  have p2 := phi_pos (isPtL_of_ptOfList hw')
  have b1 := blkN_pos (D := D) 1 h (fun c hc => ((isPtL_of_ptOfList hw).2 c hc).2)
  have b2 := blkN_pos (D := D) 1 h' (fun c hc => ((isPtL_of_ptOfList hw').2 c hc).2)
  have q1 : ((phi m h : ℝ) : ℂ) ≠ 0 := by exact_mod_cast p1.ne'
  have q2 : ((phi m h' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast p2.ne'
  have q3 : ((blkN D 1 h : ℝ) : ℂ) ≠ 0 := by exact_mod_cast b1.ne'
  have q4 : ((blkN D 1 h' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast b2.ne'
  push_cast
  field_simp
  ring

theorem clS_top (hMN : ModNorm D) {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p)
    (S : C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word) (hr : S.G.r = D.R.rS) (hg : S.g = Lat.gS D)
    (Y : Finset (TB.Pt D.host.E)) (hY : ∀ h ∈ Y, TB.level h = D.R.rS + 1 - 1) :
    ∃ (P : Type) (_ : Fintype P) (Sy : P → J.LocSys D.host.E (TB.Pt D.host.E)) (a : TB.Pt D.host.E → ℝ),
      (∀ p, ((D.R.rS + 1 = D.R.rS + 1 ∧ 1 = 1) ∧ PB.IsTopSys (Sy p) Y false) ∨
        (¬ (D.R.rS + 1 = D.R.rS + 1 ∧ 1 = 1) ∧ PB.IsPull (Sy p) Y 1 false) ∨
          PB.IsOut (Sy p) Y 1 (D.R.rS + 1 = D.R.rS + 1 ∧ 1 = 1)) ∧
      (∀ t t', t ≠ 0 → t' ≠ 0 → ∀ h ∈ Y, ∀ h' ∈ Y,
        (J.sysOf (dOf S δ M u u') (D.R.rS + 1) 1).N t t' h h' = (J.scaleSys a (J.prodSys Sy)).N t t' h h') ∧
      (∀ h ∈ Y, ∀ h' ∈ Y, (J.sysOf (dOf S δ M u u') (D.R.rS + 1) 1).B h h' = (J.scaleSys a (J.prodSys Sy)).B h h') ∧
      (J.sysOf (dOf S δ M u u') (D.R.rS + 1) 1).L = ⨅ p, (Sy p).L ∧
        (⨅ p, (Sy p).L') ≤ (J.sysOf (dOf S δ M u u') (D.R.rS + 1) 1).L' := by
  have hY' : ∀ h ∈ Y, TB.level h = D.R.rS := fun h hh => hY h hh
  set T := (D.mem u).A.T with hT
  set T' := (D.mem u').A.T with hT'
  set X0 : Finset D.host.E := Y.biUnion fun h => scal (hpt D D.R.rS h) with hX0
  have hX0' : ∀ h ∈ Y, scal (hpt D D.R.rS h) ⊆ X0 := fun h hh =>
    Finset.subset_biUnion_of_mem (fun h => scal (hpt D D.R.rS h)) hh
  obtain ⟨p0⟩ := LocModel.plF_nonempty D
  set P : Finset (PlF D) := insert p0 (gd_finite δ M hA X0).toFinset with hPdef
  have hp0 : p0 ∈ P := Finset.mem_insert_self _ _
  have hP : ∀ p, p ∉ P → Gd δ M p X0 := fun p hp => by
    by_contra hn
    exact hp (Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).2 hn))
  set Q := Qf δ M hA X0 (sgn D (D.R.rS + 1)) P with hQ
  have hQP : ∀ t t', Disjoint (Q t t') P := fun t t' => Finset.sdiff_disjoint
  have hPQ : ∀ t t' p, p ∉ P ∪ Q t t' → Gd δ M p (X1 X0 (sgn D (D.R.rS + 1)) t t') := by
    intro t t' p hp
    rw [Finset.mem_union, not_or] at hp
    exact qf_gd hA X0 _ P t t' p hp.1 hp.2
  have hX1 : ∀ t t', X0 ⊆ X1 X0 (sgn D (D.R.rS + 1)) t t' := fun t t' => Finset.subset_union_left
  refine ⟨Option {p // p ∈ P}, inferInstance, sysT M δ T T' P Q, wt D D.R.rS 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    cases j with
    | none => exact Or.inr (Or.inr (isOut_outT hA T T' Y X0 hX0' P hP))
    | some p => exact Or.inl ⟨⟨rfl, rfl⟩, isTopSys_topS hA T T' p.1 Y false (fun h => by simp at h)⟩
  · intro t t' ht ht' h hh h' hh'
    simp only [J.sysOf, J.scaleSys, J.prodSys, Fintype.prod_option, dOf_Kr]
    change KrOf δ M T T' (D.R.rS + 1) (TB.join h 1 t) (TB.join h' 1 t') = (wt D D.R.rS 1 h : ℂ) *
      (wt D D.R.rS 1 h' : ℂ) * ((∏ q ∈ Q t t', (topS M δ T T' q).N t t' h h') *
        ∏ x : {p // p ∈ P}, (topS M δ T T' x.1).N t t' h h')
    rw [prod_P_Q (hQP t t')]
    rcases hw : ptOfList D.R.rS h with _ | w
    · rw [wt_none hw, krOf_none T T' (by omega) (Or.inl (ptOfList_join_none (hY' h hh) hw t))]
      simp
    rcases hw' : ptOfList D.R.rS h' with _ | w'
    · rw [wt_none hw', krOf_none T T' (by omega) (Or.inr (ptOfList_join_none (hY' h' hh') hw' t'))]
      simp
    by_cases htt : t = t'
    · subst htt
      have hXw : scal w ⊆ X1 X0 (sgn D (D.R.rS + 1)) t t := by
        rw [← hpt_of hw]; exact (hX0' h hh).trans (hX1 t t)
      have hXw' : scal w' ⊆ X1 X0 (sgn D (D.R.rS + 1)) t t := by
        rw [← hpt_of hw']; exact (hX0' h' hh').trans (hX1 t t)
      rw [krOf_top hA T T' (hY' h hh) (hY' h' hh') hw hw' ht (P ∪ Q t t) hXw hXw' (by simp [X1]) (hPQ t t),
        wt_some hw, wt_some hw']
      push_cast
      ring
    · have hz : ∏ p ∈ P ∪ Q t t', (topS M δ T T' p).N t t' h h' = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_union_left _ hp0) ?_
        simp only [topS, J.topSys, if_neg htt]
      obtain ⟨W, hWo, hW⟩ := ptOfList_join (hY' h hh) hw (le_refl 1) ht
      obtain ⟨W', hWo', hW'⟩ := ptOfList_join (hY' h' hh') hw' (le_refl 1) ht'
      have hk : kind W ≠ kind W' := by
        rw [kind_top hW, kind_top hW']
        intro he
        apply htt
        have := Option.some.inj he
        exact mul_left_cancel₀ (sgn_ne _) this
      have hK : KrOf δ M T T' (D.R.rS + 1) (TB.join h 1 t) (TB.join h' 1 t') = 0 := by
        unfold KrOf
        rw [if_neg (by omega), if_neg (by omega), hWo, hWo']
        simp [Kglob, KtopG, hk]
      rw [hK, hz, mul_zero]
  · exact B_eq hMN hA S u u' (le_refl _) Y X0 hX0' P hP _ (fun _ _ => rfl) (fun _ _ _ => rfl)
  · have eL : (J.sysOf (dOf S δ M u u') (D.R.rS + 1) 1).L = J.LaB D.host.E S.g S.G.r (D.R.rS + 1 - 1 + 1) 1 := rfl
    rw [eL]
    refine AddSubgroup.ext fun t => ?_
    exact (lat_L_mem (m := D.R.rS) (s := 1) hA S hr hg T T' (le_refl 1) (le_refl _) t).trans
      (all_of_sysP (f := fun j => (sysT M δ T T' P Q j).L)
        (g := fun p => (pullS M δ T T' (D.R.rS + 1) 1 p).L) rfl (fun _ => rfl) t).symm
  · exact le_trans (iInf_le _ (some ⟨p0, hp0⟩)) bot_le

end AssemblyTop

end Formalism.L2.SG.Pf.LMK

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.LMK

theorem localModelS_of {D : Formalism.BasicNotions.D7} (hMN : ModNorm D) : Formalism.L2.SG.DataCut.LocalModelS D := by
  intro Wp Wq _ _ _ _ S δ M hA u u' hC i s hs1 hsi hir Y hY
  have hr : S.G.r = D.R.rS := hC.1
  have hg : S.g = Lat.gS D := by
    show S.G.g1 * S.G.g2 = D.host.g 0 * D.host.g 1
    rw [hC.2.2.1, hC.2.2.2.1]
  have hDr : (dOf S δ M u u').r = D.R.rS := hr
  rw [hDr] at hir ⊢
  by_cases htop : i = D.R.rS + 1 ∧ s = 1
  · obtain ⟨rfl, rfl⟩ := htop
    exact LMK.clS_top hMN hA S u u' hr hg Y hY
  · exact LMK.clS_pull hMN hA S u u' hr hg hs1 hsi hir htop Y hY

end Formalism.L2.SG.Pf
