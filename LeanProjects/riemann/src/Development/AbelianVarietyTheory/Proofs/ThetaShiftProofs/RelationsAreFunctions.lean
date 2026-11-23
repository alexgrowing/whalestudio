import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul

noncomputable section

namespace GlobalTheory.TorusExt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

attribute [local instance] gtGroup

theorem qk_ext {k : ℕ} {p p' : QkPt D F k} (hy : p.y = p'.y) (hg : p.g = p'.g) : p = p' := by
  obtain ⟨y, g, e⟩ := p
  obtain ⟨y', g', e'⟩ := p'
  obtain rfl : y = y' := hy
  obtain rfl : g = g' := hg
  rfl

variable (hB : D.TauBimult) {k : ℕ}

theorem qk_nsmul (p : QkPt D F k) : k • p.g = iota hB F p.y := by
  obtain ⟨h, h₁, h₂⟩ := p.eq
  exact ((isNsmul_iff_eq _ _ _).1 h₁).symm.trans ((isIota_iff_eq hB _ _).1 h₂)

def qkMk (y : D.X) (g : GtPtF D F) (h : k • g = iota hB F y) : QkPt D F k :=
  ⟨y, g, k • g, (isNsmul_iff_eq _ _ _).2 rfl, (isIota_iff_eq hB _ _).2 h⟩

@[simp] theorem qkMk_y (y : D.X) (g : GtPtF D F) (h : k • g = iota hB F y) : (qkMk hB y g h).y = y := rfl

@[simp] theorem qkMk_g (y : D.X) (g : GtPtF D F) (h : k • g = iota hB F y) : (qkMk hB y g h).g = g := rfl

theorem equiv_iff (p p' : QkPt D F k) :
    QkPt.Equiv D F p p' ↔ ∃ z : D.X, p'.y = p.y + k • z ∧ p'.g = p.g + iota hB F z :=
  exists_congr fun z => and_congr Iff.rfl
    ⟨fun ⟨_, h₁, h₂⟩ => ((isAdd_iff_eq _ _ _).1 h₂).trans (congrArg (p.g + ·) ((isIota_iff_eq hB _ _).1 h₁)),
      fun h => ⟨_, isIota_iota hB z, (isAdd_iff_eq _ _ _).2 h⟩⟩

include hB in
theorem equiv_symm {p p' : QkPt D F k} (h : QkPt.Equiv D F p p') : QkPt.Equiv D F p' p := by
  obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 h
  exact (equiv_iff hB _ _).2 ⟨-z, by rw [hy, smul_neg, add_neg_cancel_right], by rw [hg, map_neg, add_neg_cancel_right]⟩

include hB in
theorem equiv_trans {p p' p'' : QkPt D F k} (h : QkPt.Equiv D F p p') (h' : QkPt.Equiv D F p' p'') :
    QkPt.Equiv D F p p'' := by
  obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 h
  obtain ⟨z', hy', hg'⟩ := (equiv_iff hB _ _).1 h'
  exact (equiv_iff hB _ _).2 ⟨z + z', by rw [hy', hy, smul_add, add_assoc], by rw [hg', hg, map_add, add_assoc]⟩

include hB in
theorem equiv_equivalence : Equivalence (QkPt.Equiv D F (k := k)) :=
  ⟨qk_equiv_refl hB, equiv_symm hB, equiv_trans hB⟩

def qkSetoid (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) : Setoid (QkPt D F k) :=
  ⟨QkPt.Equiv D F, equiv_equivalence hB⟩

def qkZero (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) : QkPt D F k :=
  qkMk hB 0 0 (by rw [nsmul_zero, map_zero])

def qkAdd (p p' : QkPt D F k) : QkPt D F k :=
  qkMk hB (p.y + p'.y) (p.g + p'.g) (by rw [nsmul_add, qk_nsmul hB, qk_nsmul hB, map_add])

def qkNeg (p : QkPt D F k) : QkPt D F k :=
  qkMk hB (-p.y) (-p.g) (by rw [smul_neg, qk_nsmul hB, map_neg])

def qkShift (p : QkPt D F k) (z : D.X) : QkPt D F k :=
  qkMk hB (p.y + k • z) (p.g + iota hB F z) (by rw [nsmul_add, qk_nsmul hB, map_add, map_nsmul])

theorem equiv_qkShift (p : QkPt D F k) (z : D.X) : QkPt.Equiv D F p (qkShift hB p z) :=
  (equiv_iff hB _ _).2 ⟨z, rfl, rfl⟩

theorem qkAdd_iff (p p' p'' : QkPt D F k) : QkAdd p p' p'' ↔ QkPt.Equiv D F (qkAdd hB p p') p'' :=
  ⟨fun ⟨q, hy, hg, he⟩ => (qk_ext hy ((isAdd_iff_eq _ _ _).1 hg) : q = qkAdd hB p p') ▸ he,
    fun h => ⟨_, rfl, (isAdd_iff_eq _ _ _).2 rfl, h⟩⟩

theorem qkAdd_qkAdd (p p' : QkPt D F k) : QkAdd p p' (qkAdd hB p p') := (qkAdd_iff hB _ _ _).2 (qk_equiv_refl hB _)

theorem qkAdd_congr {p p' q q' : QkPt D F k} (h : QkPt.Equiv D F p q) (h' : QkPt.Equiv D F p' q') :
    QkPt.Equiv D F (qkAdd hB p p') (qkAdd hB q q') := by
  obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 h
  obtain ⟨z', hy', hg'⟩ := (equiv_iff hB _ _).1 h'
  refine (equiv_iff hB _ _).2 ⟨z + z', ?_, ?_⟩
  · show q.y + q'.y = p.y + p'.y + k • (z + z')
    rw [hy, hy', smul_add, add_add_add_comm]
  · show q.g + q'.g = p.g + p'.g + iota hB F (z + z')
    rw [hg, hg', map_add, add_add_add_comm]

include hB in

theorem qkAdd_iff_of_equiv {p p' q q' r r' : QkPt D F k} (h : QkPt.Equiv D F p q) (h' : QkPt.Equiv D F p' q')
    (e : QkAdd p p' r) : QkAdd q q' r' ↔ QkPt.Equiv D F r r' := by
  have a := (qkAdd_iff hB _ _ _).1 e
  have c := qkAdd_congr hB h h'
  rw [qkAdd_iff hB]
  exact ⟨fun b => equiv_trans hB (equiv_symm hB a) (equiv_trans hB c b),
    fun b => equiv_trans hB (equiv_symm hB c) (equiv_trans hB a b)⟩

section Action

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X] (hG : GlobalFnsSt) (oa : D.OAct O)

def qkSmul (a : O) (p : QkPt D F k) : QkPt D F k :=
  qkMk hB (a • p.y) (gtSmul hG oa a p.g) (by
    rw [iota_smul hG oa, ← qk_nsmul hB]; exact (map_nsmul (gtSmulHom hG oa F a) k p.g).symm)

theorem qkAct_iff (a : O) (p p' : QkPt D F k) : QkAct oa a p p' ↔ QkPt.Equiv D F (qkSmul hB hG oa a p) p' :=
  ⟨fun ⟨q, hy, hg, he⟩ => (qk_ext hy ((gtAct_iff_eq_gtSmul hG oa _ _ _).1 hg) : q = qkSmul hB hG oa a p) ▸ he,
    fun h => ⟨_, rfl, gtAct_gtSmul hG oa _ _, h⟩⟩

theorem qkAct_qkSmul (a : O) (p : QkPt D F k) : QkAct oa a p (qkSmul hB hG oa a p) :=
  (qkAct_iff hB hG oa _ _ _).2 (qk_equiv_refl hB _)

theorem qkSmul_congr (a : O) {p q : QkPt D F k} (h : QkPt.Equiv D F p q) :
    QkPt.Equiv D F (qkSmul hB hG oa a p) (qkSmul hB hG oa a q) := by
  obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 h
  refine (equiv_iff hB _ _).2 ⟨a • z, ?_, ?_⟩
  · show a • q.y = a • p.y + k • a • z
    rw [hy, smul_add, smul_comm a k z]
  · show gtSmul hG oa a q.g = gtSmul hG oa a p.g + iota hB F (a • z)
    rw [hg, gtSmul_add, iota_smul hG oa]

include hB hG in

theorem qkAct_iff_of_equiv {a : O} {p q r r' : QkPt D F k} (h : QkPt.Equiv D F p q) (e : QkAct oa a p r) :
    QkAct oa a q r' ↔ QkPt.Equiv D F r r' := by
  have a₁ := (qkAct_iff hB hG oa _ _ _).1 e
  have c := qkSmul_congr hB hG oa a h
  rw [qkAct_iff hB hG]
  exact ⟨fun b => equiv_trans hB (equiv_symm hB a₁) (equiv_trans hB c b),
    fun b => equiv_trans hB (equiv_symm hB c) (equiv_trans hB a₁ b)⟩

end Action

section Extension

variable {F' : Type} [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
  (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

def qkExt (p : QkPt D F k) : QkPt D F' k :=
  qkMk hB p.y (gtExt D f hf p.g) (by rw [← map_nsmul, qk_nsmul hB, gtExt_iota])

theorem qkExt_iff (p : QkPt D F k) (p' : QkPt D F' k) : QkExt f p p' ↔ p' = qkExt hB f hf p :=
  ⟨fun h => qk_ext h.1 ((eq_gtExt_iff f hf _ _).2 h.2), fun h => h ▸ ⟨rfl, (eq_gtExt_iff f hf _ _).1 rfl⟩⟩

include hB hf in
theorem existsUnique_qkExt (p : QkPt D F k) : ∃! p' : QkPt D F' k, QkExt f p p' :=
  ⟨_, (qkExt_iff hB f hf _ _).2 rfl, fun _ h => (qkExt_iff hB f hf _ _).1 h⟩

theorem qkExt_congr {p q : QkPt D F k} (h : QkPt.Equiv D F p q) :
    QkPt.Equiv D F' (qkExt hB f hf p) (qkExt hB f hf q) := by
  obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 h
  refine (equiv_iff hB _ _).2 ⟨z, hy, ?_⟩
  show gtExt D f hf q.g = gtExt D f hf p.g + iota hB F' z
  rw [hg, map_add, gtExt_iota]

theorem qkExt_qkAdd (p q : QkPt D F k) :
    qkExt hB f hf (qkAdd hB p q) = qkAdd hB (qkExt hB f hf p) (qkExt hB f hf q) :=
  qk_ext rfl (map_add (gtExt D f hf) p.g q.g)

include hB hf in
theorem equiv_of_qkExt {p q : QkPt D F k} {p' q' : QkPt D F' k} (hp : QkExt f p p') (hq : QkExt f q q')
    (h : QkPt.Equiv D F p q) : QkPt.Equiv D F' p' q' := by
  rw [(qkExt_iff hB f hf _ _).1 hp, (qkExt_iff hB f hf _ _).1 hq]
  exact qkExt_congr hB f hf h

include hB hf in
theorem qkAdd_of_qkExt {p q r : QkPt D F k} {p' q' r' : QkPt D F' k} (hp : QkExt f p p') (hq : QkExt f q q')
    (hr : QkExt f r r') (h : QkAdd p q r) : QkAdd p' q' r' := by
  rw [(qkExt_iff hB f hf _ _).1 hp, (qkExt_iff hB f hf _ _).1 hq, (qkExt_iff hB f hf _ _).1 hr, qkAdd_iff hB,
    ← qkExt_qkAdd]
  exact qkExt_congr hB f hf ((qkAdd_iff hB _ _ _).1 h)

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X] (hG : GlobalFnsSt) (oa : D.OAct O)

theorem qkExt_qkSmul (a : O) (p : QkPt D F k) :
    qkExt hB f hf (qkSmul hB hG oa a p) = qkSmul hB hG oa a (qkExt hB f hf p) :=
  qk_ext rfl (gtExt_gtSmul f hf hG oa a p.g)

include hB hf hG in
theorem qkAct_of_qkExt {a : O} {p r : QkPt D F k} {p' r' : QkPt D F' k} (hp : QkExt f p p') (hr : QkExt f r r')
    (h : QkAct oa a p r) : QkAct oa a p' r' := by
  rw [(qkExt_iff hB f hf _ _).1 hp, (qkExt_iff hB f hf _ _).1 hr, qkAct_iff hB hG, ← qkExt_qkSmul]
  exact qkExt_congr hB f hf ((qkAct_iff hB hG oa _ _ _).1 h)

end Extension

theorem relations_are_functions (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
    (hB : D.TauBimult) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    letI := gtGroup D F
    (∀ g g' : GtPtF D F, g.b = g'.b → (∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (g'.s χ)) → g = g') ∧
    ((∀ g g' g'' : GtPtF D F, g.IsAdd g' g'' ↔ g'' = g + g') ∧ (∀ g : GtPtF D F, g.IsZero ↔ g = 0) ∧
      ∀ (k : ℕ) (g h : GtPtF D F), GtPtF.IsNsmul k g h ↔ h = k • g) ∧
    ((∀ (y : D.X) (g : GtPtF D F), GtPtF.IsIota y g ↔ g = iota hB F y) ∧
      (∀ g : GtPtF D F, gtProj D F g = Additive.ofMul g.b) ∧
      (0 : GtPtF D F).b = 1 ∧ ∀ g g' : GtPtF D F, (g + g').b = g.b * g'.b) ∧
    (∀ k : ℕ, Equivalence (QkPt.Equiv D F (k := k)) ∧ (∀ p p' : QkPt D F k, ∃ r, QkAdd p p' r) ∧
      ∀ p p' q q' r r' : QkPt D F k, QkPt.Equiv D F p q → QkPt.Equiv D F p' q' → QkAdd p p' r →
        (QkAdd q q' r' ↔ QkPt.Equiv D F r r')) ∧
    (∀ (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O),
      letI := gtModule hG oa F
      (∀ (a : O) (g g' : GtPtF D F), GtAct oa a g g' ↔ g' = a • g) ∧
      (∀ (a : O) (y : D.X), iota hB F (a • y) = a • iota hB F y) ∧
      (∀ (a : O) (g : GtPtF D F), (a • g).b = g.b ≫ oa.onB.act a) ∧
      ∀ (k : ℕ) (a : O), (∀ p : QkPt D F k, ∃ r, QkAct oa a p r) ∧
        ∀ p q r r' : QkPt D F k, QkPt.Equiv D F p q → QkAct oa a p r → (QkAct oa a q r' ↔ QkPt.Equiv D F r r')) ∧
    ∀ (F' : Type) [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F'),
      f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ k : ℕ,
      (∀ p : QkPt D F k, ∃! p' : QkPt D F' k, QkExt f p p') ∧
      (∀ (p q : QkPt D F k) (p' q' : QkPt D F' k), QkExt f p p' → QkExt f q q' → QkPt.Equiv D F p q →
        QkPt.Equiv D F' p' q') ∧
      (∀ (p q r : QkPt D F k) (p' q' r' : QkPt D F' k), QkExt f p p' → QkExt f q q' → QkExt f r r' → QkAdd p q r →
        QkAdd p' q' r') ∧
      ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O) (p r : QkPt D F k)
        (p' r' : QkPt D F' k), QkExt f p p' → QkExt f r r' → QkAct oa a p r → QkAct oa a p' r' :=
  ⟨fun _ _ => gt_ext, ⟨isAdd_iff_eq, isZero_iff_eq, isNsmul_iff_eq⟩, ⟨isIota_iff_eq hB, gtProj_apply, zero_b, add_b⟩,
    fun _ => ⟨equiv_equivalence hB, fun p p' => ⟨_, qkAdd_qkAdd hB p p'⟩,
      fun _ _ _ _ _ _ h h' e => qkAdd_iff_of_equiv hB h h' e⟩,
    fun _ _ _ _ oa => ⟨gtAct_iff_eq_gtSmul hG oa, iota_smul hG oa hB, gtSmul_b hG oa,
      fun _ a => ⟨fun p => ⟨_, qkAct_qkSmul hB hG oa a p⟩, fun _ _ _ _ h e => qkAct_iff_of_equiv hB hG oa h e⟩⟩,
    fun _ _ _ f hf _ => ⟨existsUnique_qkExt hB f hf, fun _ _ _ _ => equiv_of_qkExt hB f hf,
      fun _ _ _ _ _ _ => qkAdd_of_qkExt hB f hf, fun _ _ _ _ oa _ _ _ _ _ => qkAct_of_qkExt hB f hf hG oa⟩⟩

end GlobalTheory.TorusExt
