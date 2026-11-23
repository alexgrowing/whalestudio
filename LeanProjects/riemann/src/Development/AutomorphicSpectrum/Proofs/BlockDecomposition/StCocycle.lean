import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

def wz {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T) (I : Fin j → Fin d) (s : ComposableArrows C j) :
    Φ.A.obj (s.obj (Fin.last j)) :=
  ∏ k : Fin j, (Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom
    (u (I k) (s.obj k.succ) -
      (Φ.A.map (s.map (homOfLE (Fin.castSucc_lt_succ (i := k)).le))).hom (u (I k) (s.obj k.castSucc)))

theorem wz_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T)
    (hu : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T')
    (I : Fin j → Fin d) (s : ComposableArrows C j) : wz u I s ∈ (Fil j).S _ := by
  have key : ∀ (S : Finset (Fin j)) (f : Fin j → Φ.A.obj (s.obj (Fin.last j))),
      (∀ k, f k ∈ (Fil 1).S _) → ∏ k ∈ S, f k ∈ (Fil ((S.card : ℕ) : ℤ)).S _ := by
    classical
    intro S f hf
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.card_empty]
      rw [hF.top _ (by simp)]
      trivial
    | insert a S ha ih =>
      have e : (insert a S).card = 1 + S.card := by rw [Finset.card_insert_of_notMem ha, Nat.add_comm]
      rw [Finset.prod_insert ha, e]
      exact hF.mul 1 S.card _ (by simpa using hf a) ih
  have := key Finset.univ (fun k => (Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom
    (u (I k) (s.obj k.succ) -
      (Φ.A.map (s.map (homOfLE (Fin.castSucc_lt_succ (i := k)).le))).hom (u (I k) (s.obj k.castSucc))))
    (fun k => by
      rw [hF.one]
      exact Φ.J.map_mem _ (hu _ _))
  simpa [wz] using this

variable {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O))

abbrev LL : (nlBase O ⊥ (dividedPowersBot O) 0).Fun := nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)

abbrev GF (r : ℕ) : Thick (LL q) ⥤ ModuleCat.{0} O := sq (thFil (LL q) r) (thFil (LL q) ((r : ℤ) + 1))

abbrev SS (l s : ℕ) (W : X.Opens) : ObjectProperty (Thick (LL q)) :=
  St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {W}

variable {q}

theorem ev_nat {W : X.Opens} {T T' : Thick (LL q)} (φ : T ⟶ T') (h : InU W T) (h' : InU W T') (f : Γ(X, W)) :
    ev T' h' f = Ideal.quotientMap T'.J φ.φ φ.hle (ev T h f) := by
  have e : pt T' = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T := by
    have := φ.pt
    unfold pt
    rw [← this]
    rfl
  have key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ X) (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T)
      (hh : ⊤ ≤ y ⁻¹ᵁ W), GlobalTheory.Cris.evalAt y W hh f = Ideal.quotientMap T'.J φ.φ φ.hle (ev T h f) := by
    intro y hy hh
    subst hy
    exact evalAt_map (B := CommRingCat.of (T.B ⧸ T.J)) (B' := CommRingCat.of (T'.B ⧸ T'.J)) _ (pt T) h hh f
  exact key _ e h'

theorem ev_res {W W' : X.Opens} (hW : W' ≤ W) (T : Thick (LL q)) (h : InU W T) (h' : InU W' T) (f : Γ(X, W)) :
    ev T h' (rs hW f) = ev T h f := evalAt_res (pt T) hW h h' f

theorem ev_str {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (a : O) :
    ev T h (strV q W a) = Ideal.Quotient.mk T.J (T.i a) :=
  (evalAt_base q (Ideal.Quotient.mk ⊥) (show PtOver X q (Ideal.Quotient.mk (⊥ : Ideal O)) (T.B ⧸ T.J) from T.y).1.1 (pt T)
    (show PtOver X q (Ideal.Quotient.mk (⊥ : Ideal O)) (T.B ⧸ T.J) from T.y).2 h a).trans (T.w a)

open Classical in

def lft (W : X.Opens) (T : Thick (LL q)) (f : Γ(X, W)) : T.B :=
  if h : InU W T then Function.surjInv Ideal.Quotient.mk_surjective (ev T h f) else 0

theorem lft_spec {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f : Γ(X, W)) :
    Ideal.Quotient.mk T.J (lft W T f) = ev T h f := by
  rw [lft, dif_pos h]
  exact Function.surjInv_eq _ _

def IsLift (W : X.Opens) {d : ℕ} (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B) : Prop :=
  ∀ i (T : Thick (LL q)) (h : InU W T), Ideal.Quotient.mk T.J (u i T) = ev T h (t i)

def Rp {W : X.Opens} (P : ObjectProperty (Thick (LL q))) {d r : ℕ} (u : Fin d → ∀ T : Thick (LL q), T.B)
    (x : Idx r d → Γ(X, W)) (c : HU (GF q r) P r) : Prop :=
  CrystallineSemistableComparison.Pb.Rep (sFil P r) (sFil P ((r : ℤ) + 1)) (fun s => ∑ I : Idx r d,
    wz (Φ := sP P) (fun i T => u i T.obj) I.1 s *
      (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I))) c

end GlobalTheory.CompanionTheory.GrForm

noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

def StCocycle : Prop := ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T)
    (hu : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T')
    (y : ∀ T : C, Φ.A.obj T) (hy : ∀ {T T' : C} (φ : T ⟶ T'), y T' - (Φ.A.map φ).hom (y T) ∈ Φ.J.S T')
    (I : Fin j → Fin d),
    ∃ f : CH.Cn (sq (Fil j) (Fil ((j : ℤ) + 1))) j, CH.d _ j f = 0 ∧
      ∀ s, (show sqM (Fil j) (Fil ((j : ℤ) + 1)) _ from f s).1 = Ideal.Quotient.mk _ (wz u I s * y _)

def StExists : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W : X.Opens) {d : ℕ}
    (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W t u)
    (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (r : ℕ) (x : Idx r d → Γ(X, W)),
    ∃ c, Rp (W := W) P u x c

def StAdd : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W : X.Opens) {d : ℕ}
    (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W t u)
    (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (r : ℕ) (x x' : Idx r d → Γ(X, W))
    (c c' : HU (GF q r) P r), Rp (W := W) P u x c → Rp (W := W) P u x' c' →
      Rp (W := W) P u (x + x') (c + c') ∧ Rp (W := W) P u (-x) (-c)

def StSmul : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W : X.Opens) {d : ℕ}
    (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W t u)
    (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (r : ℕ) (x : Idx r d → Γ(X, W))
    (c : HU (GF q r) P r) (a : O), Rp (W := W) P u x c → Rp (W := W) P u (fun I => strV q W a * x I) (a • c)

def StRes : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W W' : X.Opens) (hW : W' ≤ W)
    {d : ℕ} (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W t u)
    (P P' : ObjectProperty (Thick (LL q))) (hPP : P' ≤ P) (hP : ∀ T, P T → InU W T) (hP' : ∀ T, P' T → InU W' T)
    (r : ℕ) (x : Idx r d → Γ(X, W)) (c : HU (GF q r) P r), Rp (W := W) P u x c →
      Rp (W := W') P' u (fun I => rs hW (x I)) ((resU (GF q r) hPP).pull r c)

def StAct : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W : X.Opens)
    (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (r : ℕ) (z : Γ(X, W)),
    ∃ m : HU (GF q r) P r →+ HU (GF q r) P r, ∀ {d : ℕ} (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B),
      IsLift W t u → ∀ (x : Idx r d → Γ(X, W)) (c : HU (GF q r) P r), Rp (W := W) P u x c →
        Rp (W := W) P u (fun I => z * x I) (m c)

def StFrame : Prop := ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {W : X.Opens} {d : ℕ} (c : Coord q W d)
    (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W c.t u),
    ∃ (E : Frame (sP (SS q l s W)) d) (σ : ∀ T, E.D ⟶ T) (θ : Γ(X, W) ≃+* (sP (SS q l s W)).A.obj E.D),
      E.GrConst (sFil (SS q l s W)) ∧ (∀ n : ℕ, n ≠ 0 → (sFil (SS q l s W) n).S E.D = ⊥) ∧
      E.Coords (fun i => θ (c.t i)) ∧
      (∀ i T, ((sP (SS q l s W)).A.map (σ T)).hom (θ (c.t i)) = u i T.obj) ∧
      ∀ (T : (SS q l s W).FullSubcategory) (h : InU W T.obj) (f : Γ(X, W)),
        Ideal.Quotient.mk T.obj.J (show T.obj.B from ((sP (SS q l s W)).A.map (σ T)).hom (θ f)) = ev T.obj h f

def StLoc : Prop := ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {W : X.Opens} {d : ℕ} (c : Coord q W d)
    (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W c.t u) (r : ℕ) (hr : r < s),
    (∀ cl : HU (GF q r) (SS q l s W) r, ∃ x, Rp (W := W) (SS q l s W) u x cl) ∧
      ∀ x : Idx r d → Γ(X, W), Rp (W := W) (SS q l s W) u x 0 → x = 0

def StVan : Prop := ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (r j : ℕ), r < s → j ≠ r →
    Subsingleton (HU (GF q r) (SS q l s W) j)

def StVB : Prop := ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {ι : Type} [Fintype ι] (U : ι → X.Opens) (d : ι → ℕ)
    (c : ∀ α, Coord q (U α) (d α)) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i)) (r : ℕ), r < s →
    Nonempty (VB (strV q) U (CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q l s (U α)) r))

def StCover : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [Smooth q]
    (V : X.Opens), IsAffineOpen V → ∃ (ι : Type) (_ : Fintype ι) (U : ι → X.Opens) (d : ι → ℕ)
      (_ : ∀ α, Coord q (U α) (d α)), (⨆ α, U α) = V ∧ ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i)

end GlobalTheory.CompanionTheory.GrForm
