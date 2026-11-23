import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.KProps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.ResMIncl
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.SplitField
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.gr_aff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

universe w v u

namespace CrystallineSemistableComparison.HT

open Pb CH CrystallineSemistableComparison.Auxff

section Gen
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem gen_assoc {F₁ F₂ F₃ F₁₂ F₂₃ F : C ⥤ ModuleCat.{w} R} (P₁ : Pairing F₁ F₂ F₁₂) (P₂ : Pairing F₁₂ F₃ F)
    (P₃ : Pairing F₂ F₃ F₂₃) (P₄ : Pairing F₁ F₂₃ F)
    (hμ : ∀ T x y z, P₂.μ T (P₁.μ T x y) z = P₄.μ T x (P₃.μ T y z)) {p q r a b n : ℕ} (h₁ : p + q = a) (h₂ : a + r = n)
    (h₃ : q + r = b) (h₄ : p + b = n) (x : H F₁ p) (y : H F₂ q) (z : H F₃ r) :
    P₂.cup h₂ (P₁.cup h₁ x y) z = P₄.cup h₄ x (P₃.cup h₃ y z) := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F₁) p).1 x
  obtain ⟨g, hg, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F₂) q).1 y
  obtain ⟨k, hk, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F₃) r).1 z
  obtain ⟨c1, e1⟩ := CrystallineSemistableComparison.P.cup_cls P₁ h₁ f g hf hg
  obtain ⟨c3, e3⟩ := CrystallineSemistableComparison.P.cup_cls P₃ h₃ g k hg hk
  rw [e1, e3]
  obtain ⟨c2, e2⟩ := CrystallineSemistableComparison.P.cup_cls P₂ h₂ _ k c1 hk
  obtain ⟨c4, e4⟩ := CrystallineSemistableComparison.P.cup_cls P₄ h₄ f _ hf c3
  rw [e2, e4]
  refine cls_congr _ (funext fun s => ?_) _ _
  rw [cupC_apply, cupC_apply, term_cupC, term_cupC, hμ]
  refine congrArg₂ (fun u v => P₄.μ _ u v) (term_congr _ _ _ _ _ ?_)
    (congrArg₂ (fun u v => P₃.μ _ u v) (term_congr _ _ _ _ _ ?_) (term_congr _ _ _ _ _ ?_)) <;>
  · funext t
    apply Fin.ext
    simp only [front, back, Function.comp]
    try omega

theorem gen_left {F₀ F : C ⥤ ModuleCat.{w} R} (P : Pairing F₀ F F) (o : ∀ T, F₀.obj T)
    (ho : ∀ {T T' : C} (φ : T ⟶ T'), (F₀.map φ).hom (o T) = o T') (hμ : ∀ T x, P.μ T (o T) x = x) (h0) (n : ℕ) (x : H F n) :
    P.cup (Nat.zero_add n) ((cx F₀).cls (n := 0) (fun s => o _) h0) x = x := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨hc, e⟩ := CrystallineSemistableComparison.P.cup_cls P (Nat.zero_add n) (fun s => o _) f h0 hf
  refine e.trans (cls_congr _ (funext fun s => ?_) _ _)
  rw [cupC_apply, term_id _ s f _ _ (fun t => by simp [back])]
  exact (congrArg (fun u => P.μ _ u (f s)) (ho _)).trans (hμ _ _)

theorem gen_right {F₀ F : C ⥤ ModuleCat.{w} R} (P : Pairing F F₀ F) (o : ∀ T, F₀.obj T)
    (ho : ∀ {T T' : C} (φ : T ⟶ T'), (F₀.map φ).hom (o T) = o T') (hμ : ∀ T x, P.μ T x (o T) = x) (h0) (n : ℕ) (x : H F n) :
    P.cup (Nat.add_zero n) x ((cx F₀).cls (n := 0) (fun s => o _) h0) = x := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨hc, e⟩ := CrystallineSemistableComparison.P.cup_cls P (Nat.add_zero n) f (fun s => o _) hf h0
  refine e.trans (cls_congr _ (funext fun s => ?_) _ _)
  rw [cupC_apply, term_id _ s f _ _ (fun t => by simp [front])]
  exact (congrArg (fun u => P.μ _ (f s) u) (ho _)).trans (hμ _ _)

variable {A : C ⥤ CommAlgCat.{0} R}

theorem pair_mk {a b a' b' a'' b'' : IdF A} (h : MulOk a b a' b' a'' b'') {T : C} (x y : A.obj T) (hx : x ∈ a.S T)
    (hy : y ∈ a'.S T) : h.pair.μ T (sqMk a b x hx) (sqMk a' b' y hy) = sqMk a'' b'' (x * y) (h.aa T hx hy) := h.mul_mk x y hx hy

theorem mk_congr (a b : IdF A) {T : C} {x y : A.obj T} (e : x = y) (hx : x ∈ a.S T) (hy : y ∈ a.S T) :
    sqMk a b x hx = sqMk a b y hy := by subst e; rfl

end Gen

theorem dividedPowerFiltration_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {r : ℕ} (hr : 1 ≤ r) : pdP δ r ≤ J := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, h, rfl⟩
  have key : ∀ l : List (ℕ × B), (∀ q ∈ l, q.2 ∈ J) → 1 ≤ (l.map Prod.fst).sum → (l.map fun q => δ.dpow q.1 q.2).prod ∈ J := by
    intro l
    induction l with
    | nil => intro _ h; simp at h
    | cons q l ih =>
      intro hl h
      simp only [List.map_cons, List.prod_cons, List.sum_cons] at h ⊢
      by_cases h0 : q.1 = 0
      · exact Ideal.mul_mem_left _ _ (ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (by omega))
      · exact Ideal.mul_mem_right _ _ (δ.dpow_mem h0 (hl q List.mem_cons_self))
  exact key l hl (hr.trans h)

theorem tfBase_field (K : Type) [Field K] [CharZero K] {s : ℕ} (hs : 1 ≤ s) : TFBase (dividedPowersBot K) 1 s where
  nil := le_bot_iff.1 (dividedPowerFiltration_le _ hs)
  tf r x hx := by simpa using hx
  dv n hn := ⟨0, (n : K)⁻¹, by rw [pow_zero, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn)]⟩

theorem kFin_of (hF : FinO) : KFin := by
  intro K _ _ X q _ _ a n
  obtain ⟨U⟩ := (cov_ex q).1 inferInstance
  have hU : sSup (Set.range U.U) = ⊤ := U.cover
  have hb := hdg_res q (a + 1) _ hU a (Nat.lt_succ_self a) n
  refine ⟨?_, fun hn => ?_⟩
  · have := hF 1 (a + 1) (tfBase_field K (by omega)) q U _ hU (a : ℤ) ((a : ℤ) + 1) (by omega) (by push_cast; omega) n
    exact Module.Finite.equiv (LinearEquiv.ofBijective _ hb).symm
  · have := (glob_van_st (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (grT (smFun X q) a) (TF 1 (a + 1))
      U.U a).1 (fun S hS j hj => gr_aff_pf q _ (U.inter S hS) (a + 1) a j (Nat.lt_succ_self a) hj.ne) n hn
    have h2 : Subsingleton (HQ (TO q 1 (a + 1) (Set.range U.U)) (a : ℤ) ((a : ℤ) + 1) n) := this
    exact hb.1.subsingleton

section Form
variable {K : Type} [CommRing K] {X Y Z : Scheme.{0}}

theorem pt_id' {q : X ⟶ Spec (CommRingCat.of K)} {B₀ : Type} [CommRing B₀] (J : Ideal B₀) (h)
    (y : (smFun X q).Pt.obj (CommRingCat.of (B₀ ⧸ J))) :
    (smFun X q).Pt.map (CommRingCat.ofHom (Ideal.quotientMap J (RingHom.id B₀) h)) y = y := by
  have e : Ideal.quotientMap J (RingHom.id B₀) h = RingHom.id _ := by ext; rfl
  rw [e, CommRingCat.ofHom_id, (smFun X q).Pt.map_id]; rfl

theorem gr_prism {q : X ⟶ Spec (CommRingCat.of K)} {C' : Type 1} [Category.{0} C'] {F' : C' ⥤ ModuleCat.{0} K} {a : ℕ}
    (m m' : CH.Mor (grT (smFun X q) a) F' (RingHom.id K)) (η : ∀ T, m.G.obj T ⟶ m'.G.obj T)
    (nat : ∀ {T T' : C'} (f : T ⟶ T') (x : (m.G.obj T).B), (η T').φ ((m.G.map f).φ x) = (m'.G.map f).φ ((η T).φ x))
    (hτ : ∀ (T : C') (x : (m.G.obj T).B) hx, m'.τ T (sqMk _ _ ((η T).φ x) (dividedPowerFiltration_map (η T).dp a hx)) = m.τ T (sqMk _ _ x hx))
    (n : ℕ) (x : CH.H (grT (smFun X q) a) n) : m.pull n x = m'.pull n x :=
  CrystallineSemistableComparison.P.prism m m' ⟨η, fun _ _ f => Thick.Hom.ext (RingHom.ext (nat f)) (funext fun j => j.elim)⟩ (fun T x => by
    obtain ⟨y, hy, rfl⟩ := sq_surj _ _ x
    exact hτ T y hy) n x

abbrev pM {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)} (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) :
    CH.Mor (grT (smFun Y p) a) (grT (smFun X q) a) (RingHom.id K) :=
  (smS u hu).sq (a := thFil _ (a : ℤ)) (b := thFil _ ((a : ℤ) + 1)) (a' := thFil _ (a : ℤ)) (b' := thFil _ ((a : ℤ) + 1))
    (fun _ _ hx => hx) fun _ _ hx => hx

theorem pull_id' (q : X ⟶ Spec (CommRingCat.of K)) (hu : 𝟙 X ≫ q = q) (a n : ℕ) (x : Hdg q a n) : pullH (𝟙 X) hu a n x = x :=
  (gr_prism (pM (𝟙 X) hu a) (CH.Mor.id _)
    (fun T => mkH (γ := dividedPowersBot K) (p := 0) (T := (smMor (𝟙 X) hu).obj T) (T' := T) (RingHom.id T.B) (fun _ => rfl)
      (DPMorphism.id T.δ).isDPMorphism le_rfl ((pt_id' _ _ _).trans (Subtype.ext (Prod.ext rfl (Category.comp_id _)))))
    (fun _ _ => rfl) (fun _ _ _ => rfl) n x).trans (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id K) (CH.Mor.id _) (CH.Mor.id _) n x).2

theorem pull_comp' {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)} {o : Z ⟶ Spec (CommRingCat.of K)}
    (u : X ⟶ Y) (hu : u ≫ p = q) (v : Y ⟶ Z) (hv : v ≫ o = p) (h : (u ≫ v) ≫ o = q) (a n : ℕ) (x : Hdg o a n) :
    pullH (u ≫ v) h a n x = pullH u hu a n (pullH v hv a n x) :=
  (gr_prism (pM (u ≫ v) h a) ((pM v hv a).comp (σ'' := RingHom.id K) (pM u hu a))
    (fun T => mkH (γ := dividedPowersBot K) (p := 0) (T := (smMor (u ≫ v) h).obj T) (T' := (smMor v hv).obj ((smMor u hu).obj T))
      (RingHom.id T.B) (fun _ => rfl) (DPMorphism.id T.δ).isDPMorphism le_rfl
      ((pt_id' _ _ _).trans (Subtype.ext (Prod.ext rfl (Category.assoc _ _ _).symm))))
    (fun _ _ => rfl) (fun _ _ _ => rfl) n x).trans (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id K) (pM v hv a) (pM u hu a) n x).1

theorem pull_cup' {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)} (u : X ⟶ Y) (hu : u ≫ p = q)
    {a a' c i j n : ℕ} (ha : a + a' = c) (h : i + j = n) (x : Hdg p a i) (y : Hdg p a' j) :
    pullH u hu c n (cupH p ha h x y) = cupH q ha h (pullH u hu a i x) (pullH u hu a' j y) :=
  CrystallineSemistableComparison.P.cup_pull (grOk (smFun Y p) ha).pair (grOk (smFun X q) ha).pair (smMor u hu).functor (pM u hu a).τ (pM u hu a').τ
    (pM u hu c).τ (pM u hu a).nat (pM u hu a').nat (pM u hu c).nat (fun T x y => by
      obtain ⟨x, hx, rfl⟩ := sq_surj _ _ x
      obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
      exact (congrArg ((pM u hu c).τ T) (pair_mk (grOk (smFun Y p) ha) x y hx hy)).trans
        (pair_mk (grOk (smFun X q) ha) (T := T) x y hx hy).symm) h x y

def oneSec (q : X ⟶ Spec (CommRingCat.of K)) (T : Thick (smFun X q)) : (grT (smFun X q) 0).obj T :=
  sqMk _ _ (1 : T.B) (show (1 : T.B) ∈ T.pdPow 0 from T.pdPow_zero ▸ trivial)

theorem oneSec_map (q : X ⟶ Spec (CommRingCat.of K)) {T T' : Thick (smFun X q)} (φ : T ⟶ T') :
    ((grT (smFun X q) 0).map φ).hom (oneSec q T) = oneSec q T' :=
  Subtype.ext (congrArg (Ideal.Quotient.mk _) (map_one φ.φ))

theorem oneH_eq (q : X ⟶ Spec (CommRingCat.of K)) :
    ∃ h0, oneH q = (cx (grT (smFun X q) 0)).cls (n := 0) (fun s => oneSec q _) h0 := ⟨_, rfl⟩

end Form

theorem kForm : KForm where
  bilin q _ _ _ _ _ _ ha h := CrystallineSemistableComparison.P.cup_bilin (grOk (smFun _ q) ha).pair h
  pull_id q u hu e a n x := by subst e; exact pull_id' q hu a n x
  pull_comp u hu v hv h a n x := pull_comp' u hu v hv h a n x
  pull_cup u hu _ _ _ _ _ _ ha h x y := pull_cup' u hu ha h x y
  pull_one u hu := rfl
  one_cup {K _ X} q a n x := by
    obtain ⟨h0, e⟩ := oneH_eq q
    rw [e]
    refine ⟨gen_left (grOk (smFun X q) (Nat.zero_add a)).pair (oneSec q) (oneSec_map q) (fun T x => ?_) h0 n x,
      gen_right (grOk (smFun X q) (Nat.add_zero a)).pair (oneSec q) (oneSec_map q) (fun T x => ?_) h0 n x⟩
    · obtain ⟨x, hx, rfl⟩ := sq_surj _ _ x
      exact (pair_mk _ _ _ _ _).trans (mk_congr _ _ (one_mul _) _ _)
    · obtain ⟨x, hx, rfl⟩ := sq_surj _ _ x
      exact (pair_mk _ _ _ _ _).trans (mk_congr _ _ (mul_one _) _ _)
  assoc {K _ X} q _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ e₁ e₂ e₃ e₄ x y z :=
    gen_assoc (grOk (smFun X q) h₁).pair (grOk (smFun X q) h₂).pair (grOk (smFun X q) h₃).pair (grOk (smFun X q) h₄).pair
      (fun T x y z => by
        obtain ⟨x, hx, rfl⟩ := sq_surj _ _ x
        obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
        obtain ⟨z, hz, rfl⟩ := sq_surj _ _ z
        rw [pair_mk, pair_mk, pair_mk, pair_mk]
        exact mk_congr _ _ (mul_assoc _ _ _) _ _) e₁ e₂ e₃ e₄ x y z

end CrystallineSemistableComparison.HT
