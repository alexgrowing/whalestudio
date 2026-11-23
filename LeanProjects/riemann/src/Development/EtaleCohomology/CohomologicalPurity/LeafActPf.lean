import Development.EtaleCohomology.CohomologicalPurity.LeafThomCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom
namespace ActPf

variable {d : ℕ} {A : Type} [CommRing A]

def φ {U : Scheme.{0}} (s : U ⟶ Spec (CommRingCat.of A)) : A →+* Γ(U, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ s.appTop).hom

theorem φ_comp {V U : Scheme.{0}} (f : V ⟶ U) (s : U ⟶ Spec (CommRingCat.of A)) :
    φ (f ≫ s) = f.appTop.hom.comp (φ s) := rfl

def actV (M : Matrix (Fin d) (Fin d) A) {U : Scheme.{0}} (s : U ⟶ Spec (CommRingCat.of A))
    (v : Fin (d + 1) → Γ(U, ⊤)) : Fin (d + 1) → Γ(U, ⊤) :=
  Fin.cons (v 0) ((M.map (φ s)).mulVec (Fin.tail v))

theorem actV_mem (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {U : Scheme.{0}}
    (s : U ⟶ Spec (CommRingCat.of A)) (v : Fin (d + 1) → Γ(U, ⊤)) (p : U)
    (h : ∃ i : Fin (d + 1), k ≤ i.val ∧ p ∈ U.basicOpen (v i)) :
    ∃ i : Fin (d + 1), k ≤ i.val ∧ p ∈ U.basicOpen (actV M s v i) := by
  obtain ⟨i, hi, hp⟩ := h
  by_contra hc
  push Not at hc
  have hM' : IsUnit (M.map (φ s)).det := by
    have h := hM.map (φ s); rw [RingHom.map_det] at h; exact h
  have hz : ∀ j : Fin d, (U.Γevaluation p).hom ((M.map (φ s)).mulVec (Fin.tail v) j) = 0 := by
    intro j
    have := hc j.succ (by simp; omega)
    simp only [actV, Fin.cons_succ] at this
    exact (Scheme.evaluation_eq_zero_iff_notMem_basicOpen _ _ _ _).2 this
  have ht : ∀ j : Fin d, (U.Γevaluation p).hom (Fin.tail v j) = 0 := by
    intro j
    have hinv : (M.map (φ s))⁻¹.mulVec ((M.map (φ s)).mulVec (Fin.tail v)) = Fin.tail v := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM', Matrix.one_mulVec]
    rw [← hinv, RingHom.map_mulVec]
    have : ((U.Γevaluation p).hom ∘ (M.map (φ s)).mulVec (Fin.tail v)) = 0 := funext hz
    rw [this, Matrix.mulVec_zero]; rfl
  cases i using Fin.cases with
  | zero =>
    have := hc 0 (by simp at hi; omega)
    simp only [actV, Fin.cons_zero] at this
    exact this hp
  | succ j =>
    exact ((Scheme.evaluation_eq_zero_iff_notMem_basicOpen _ _ _ _).1 (ht j)) hp

def actF (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {U : Scheme.{0}}
    (s : U ⟶ Spec (CommRingCat.of A)) : Vec (d + 1) k U ⥤ Vec (d + 1) k U where
  obj v := ⟨actV M s v.1, fun p => actV_mem M hM hk s v.1 p (v.2 p)⟩
  map {v w} u := ⟨u.1, fun i => by
    cases i using Fin.cases with
    | zero => simp only [actV, Fin.cons_zero]; exact u.2 0
    | succ j =>
      simp only [actV, Fin.cons_succ]
      have : Fin.tail v.1 = (u.1 : Γ(U, ⊤)) • Fin.tail w.1 := funext fun l => by
        simp only [Fin.tail, Pi.smul_apply, smul_eq_mul]; exact u.2 l.succ
      rw [this, Matrix.mulVec_smul]; rfl⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem comp_val {N k : ℕ} {U : Scheme.{0}} {X Y Z : Vec N k U} (a : X ⟶ Y) (b : Y ⟶ Z) :
    (a ≫ b).1 = b.1 * a.1 := rfl

theorem eqToHom_val {N k : ℕ} {U : Scheme.{0}} {X Y : Vec N k U} (h : X = Y) : (eqToHom h).1 = 1 := by
  subst h; rfl

theorem actV_map (M : Matrix (Fin d) (Fin d) A) {V U : Scheme.{0}} (f : V ⟶ U) (s : U ⟶ Spec (CommRingCat.of A))
    (v : Fin (d + 1) → Γ(U, ⊤)) :
    (fun i => f.appTop.hom (actV M s v i)) = actV M (f ≫ s) (fun i => f.appTop.hom (v i)) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [actV]
  | succ j =>
    simp only [actV, Fin.cons_succ]
    rw [RingHom.map_mulVec, φ_comp, Matrix.map_map]
    rfl

theorem actF_map (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {V U : Scheme.{0}}
    (f : V ⟶ U) (s : U ⟶ Spec (CommRingCat.of A)) :
    actF M hM hk s ⋙ Vec.map (d + 1) k f = Vec.map (d + 1) k f ⋙ actF M hM hk (f ≫ s) := by
  refine CategoryTheory.Functor.ext (fun v => Subtype.ext (actV_map M f s v.1)) (fun v w u => ?_)
  apply Subtype.ext
  simp only [comp_val, eqToHom_val, one_mul]
  erw [eqToHom_val, mul_one]
  rfl

def actSp (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {E : Spc}
    (a : E ⟶ Pj (d + 1) k) (b : E ⟶ sp A) : E ⟶ Pj (d + 1) k where
  app n :=
    { app := fun U => TypeCat.ofHom fun x =>
        ((show Fin (n.unop.len + 1) ⥤ Vec (d + 1) k U.unop from (a.app n).app U x) ⋙
          actF M hM hk (show U.unop ⟶ Spec (CommRingCat.of A) from (b.app n).app U x) :
          Fin (n.unop.len + 1) ⥤ Vec (d + 1) k U.unop)
      naturality := fun U U' f => by
        ext x
        have h1 := ConcreteCategory.congr_hom ((a.app n).naturality f) x
        have h2 := ConcreteCategory.congr_hom ((b.app n).naturality f) x
        refine (congrArg₂ (fun (F : Fin (n.unop.len + 1) ⥤ Vec (d + 1) k U'.unop)
          (s : U'.unop ⟶ Spec (CommRingCat.of A)) => (F ⋙ actF M hM hk s : Fin (n.unop.len + 1) ⥤ _)) h1 h2).trans ?_
        exact congrArg (fun G => (show Fin (n.unop.len + 1) ⥤ Vec (d + 1) k U.unop from (a.app n).app U x) ⋙ G)
          (actF_map M hM hk f.unop (show U.unop ⟶ Spec (CommRingCat.of A) from (b.app n).app U x)).symm }
  naturality n m f := by
    ext U x
    have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (a.naturality f) U) x
    have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app (b.naturality f) U) x
    exact (congrArg₂ (fun (F : Fin (m.unop.len + 1) ⥤ Vec (d + 1) k U.unop)
          (s : U.unop ⟶ Spec (CommRingCat.of A)) => (F ⋙ actF M hM hk s : Fin (m.unop.len + 1) ⥤ _)) h1 h2).trans rfl

theorem actSp_comp (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {E' E : Spc}
    (g : E' ⟶ E) (a : E ⟶ Pj (d + 1) k) (b : E ⟶ sp A) :
    g ≫ actSp M hM hk a b = actSp M hM hk (g ≫ a) (g ≫ b) := by
  ext n U x; rfl

theorem actSp_incl (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {E : Spc}
    (a : E ⟶ Pj (d + 1) 1) (b : E ⟶ sp A) :
    actSp M hM le_rfl a b ≫ Pj.incl (d + 1) = actSp M hM (Nat.zero_le 1) (a ≫ Pj.incl (d + 1)) b := by
  ext n U x; rfl

theorem actSp_line (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {E : Spc}
    (a : E ⟶ Pj (d + 1) k) (b : E ⟶ sp A) :
    actSp M hM hk a b ≫ Pj.line (d + 1) k = a ≫ Pj.line (d + 1) k := by
  ext n U x; rfl

theorem actSp_pt (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) (x : Fin d → A) :
    actSp M hM (Nat.zero_le 1) (Pj.pt (vec1 x)) (𝟙 (sp A)) = Pj.pt (vec1 (M.mulVec x)) := by
  ext n U f
  refine CategoryTheory.Functor.ext (fun _ => Subtype.ext ?_) (fun _ _ _ => ?_)
  · funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j =>
      show ((M.map (φ _)).mulVec _) j = φ _ ((M.mulVec x) j)
      rw [RingHom.map_mulVec]
      rfl
  · apply Subtype.ext
    erw [comp_val, comp_val, eqToHom_val, eqToHom_val]
    simp only [one_mul, mul_one]
    erw [eqToHom_val]
    rfl

end ActPf

open ActPf in
theorem LeafAct_of : LeafAct := by
  intro d A _ M hM
  let gR : PR (d + 1) 0 A ⟶ PR (d + 1) 0 A :=
    prod.lift (actSp M hM (Nat.zero_le 1) prod.fst prod.snd) prod.snd
  let gL : PR (d + 1) 1 A ⟶ PR (d + 1) 1 A := prod.lift (actSp M hM le_rfl prod.fst prod.snd) prod.snd
  have hw : gL ≫ (pr d A).hom = (pr d A).hom ≫ gR := by
    apply prod.hom_ext
    · simp only [pr, Arrow.mk_hom, Category.assoc, prod.map_fst, prod.lift_fst, gL, gR]
      rw [prod.lift_fst_assoc, actSp_incl, actSp_comp, prod.map_fst, prod.map_snd, Category.comp_id]
    · simp only [pr, Arrow.mk_hom, Category.assoc, prod.map_snd, Category.comp_id, prod.lift_snd, gL, gR]
  refine ⟨Arrow.homMk gL gR hw, ?_, ?_, ?_⟩
  · change gR ≫ prod.fst ≫ Pj.line (d + 1) 0 = _
    rw [prod.lift_fst_assoc, actSp_line]
  · change gR ≫ prod.snd = _
    exact prod.lift_snd _ _
  · intro x
    change chart x ≫ gR = _
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, actSp_comp, chart, prod.lift_fst, prod.lift_snd, actSp_pt, chart, prod.lift_fst]
    · rw [Category.assoc, prod.lift_snd, chart, chart, prod.lift_snd, prod.lift_snd]

end LateralTheory.CohomologicalPurity.Thom
