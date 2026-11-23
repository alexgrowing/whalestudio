import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationCriticalComparisonMapStatement
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LocCmp

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R C'} {c : IdF Φ'.A}

def Gpt (m : QMor Φ Φ' c) {d : ℕ} (E : Frame Φ d) (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D) : Pt E' ⥤ Pt E where
  obj X := ⟨m.G.obj X.T, e ≫ m.G.map X.s⟩
  map {X Y} f := m.G.map (show X.T ⟶ Y.T from f)
  map_id X := m.G.map_id X.T
  map_comp f g := m.G.map_comp f g

section Cut

variable (m : QMor Φ Φ' c) {d : ℕ} {E : Frame Φ (d + 1)} {E' : Frame Φ' (d + 1)} {e : E.D ⟶ m.G.obj E'.D}

theorem τ_zero (he : m.Fr E E' e) {T : C'} (s s' : E'.D ⟶ T) (h : E'.τ 0 s s' = 0) :
    E.τ 0 (e ≫ m.G.map s) (e ≫ m.G.map s') = 0 := by
  apply m.inj T
  rw [he 0 s s', h, map_zero, map_zero]

def Gcut (he : m.Fr E E' e) : Cut E' ⥤ Cut E where
  obj Y := ⟨m.G.obj Y.T, e ≫ m.G.map Y.s⟩
  map {X Y} φ := ⟨m.G.map φ.1, by
    have := τ_zero m he (X.s ≫ φ.1) Y.s φ.2
    rwa [m.G.map_comp, ← Category.assoc] at this⟩
  map_id X := Cut.hom_ext (m.G.map_id X.T)
  map_comp f g := Cut.hom_ext (m.G.map_comp f.1 g.1)

def m1 (he : m.Fr E E' e) : QMor (Cut.Φ1 E) (Cut.Φ1 E') (c.res (Cut.U E')) where
  G := Gcut m he
  ρ Y := m.ρ Y.T
  inj Y := m.inj Y.T
  nat φ x y h := m.nat φ.1 x y h
  dp Y k x y hx hy h := m.dp Y.T k x y hx hy h

def e1 (he : m.Fr E E' e) : (Cut.E1 E).D ⟶ (m1 m he).G.obj (Cut.E1 E').D :=
  ⟨e, by
    change E.τ 0 (𝟙 E.D ≫ e) (e ≫ m.G.map (𝟙 E'.D)) = 0
    rw [m.G.map_id, Category.id_comp, Category.comp_id]
    exact E.τ_self 0 e⟩

theorem Fr1 (he : m.Fr E E' e) : (m1 m he).Fr (Cut.E1 E) (Cut.E1 E') (e1 m he) :=
  fun i {T} s s' => he i.succ s.1 s'.1

variable (Q : Poly Φ) (Q' : Poly Φ')

def etaAt (he : m.Fr E E' e) (X : Pt E') : (Cut.P0 Q).obj ((Gpt m E E' e).obj X) ⟶ (Gcut m he).obj ((Cut.P0 Q').obj X) :=
  Cut.adjInv Q ((Gpt m E E' e).obj X) ((Gcut m he).obj ((Cut.P0 Q').obj X)) (m.G.map (Q'.j X.T))

theorem etaAt_j (he : m.Fr E E' e) (X : Pt E') :
    Q.j (m.G.obj X.T) ≫ (etaAt m Q Q' he X).1 = m.G.map (Q'.j X.T) :=
  Cut.adjInv_j Q ((Gpt m E E' e).obj X) ((Gcut m he).obj ((Cut.P0 Q').obj X)) (m.G.map (Q'.j X.T))

theorem etaAt_nat (he : m.Fr E E' e) {X Y : Pt E'} (φ : X.T ⟶ Y.T) :
    Q.j (m.G.obj X.T) ≫ Cut.Pmap (X := (Gpt m E E' e).obj X) (Y := (Gpt m E E' e).obj Y) Q (m.G.map φ) ≫ (etaAt m Q Q' he Y).1 =
      Q.j (m.G.obj X.T) ≫ (etaAt m Q Q' he X).1 ≫ m.G.map (Cut.Pmap (X := X) (Y := Y) Q' φ) := by
  have hP : Q.j (m.G.obj X.T) ≫ Cut.Pmap (X := (Gpt m E E' e).obj X) (Y := (Gpt m E E' e).obj Y) Q (m.G.map φ) =
      m.G.map φ ≫ Q.j (m.G.obj Y.T) := Cut.Pmap_j (X := (Gpt m E E' e).obj X) (Y := (Gpt m E E' e).obj Y) Q (m.G.map φ)
  rw [← Category.assoc, hP, Category.assoc, etaAt_j, ← Category.assoc, etaAt_j, ← m.G.map_comp, ← m.G.map_comp,
    Cut.Pmap_j]

def eta (he : m.Fr E E' e) : Gpt m E E' e ⋙ Cut.P0 Q ⟶ Cut.P0 Q' ⋙ Gcut m he where
  app X := etaAt m Q Q' he X
  naturality {X Y} φ := Cut.truncation_hom_ext Q (etaAt_nat m Q Q' he (X := X) (Y := Y) φ)

theorem eta_j (he : m.Fr E E' e) (X : Pt E') :
    Q.j (m.G.obj X.T) ≫ ((eta m Q Q' he).app X).1 = m.G.map (Q'.j X.T) :=
  etaAt_j m Q Q' he X

theorem eta_X (he : m.Fr E E' e) (X : Pt E') :
    m.ρ (Q'.P X.T) ((Φ.A.map ((eta m Q Q' he).app X).1).hom (Q.X (m.G.obj X.T))) = Ideal.Quotient.mk _ (Q'.X X.T) := by
  have h1 : (Φ.A.map ((eta m Q Q' he).app X).1).hom (Q.X (m.G.obj X.T)) =
      E.τ 0 ((e ≫ m.G.map X.s) ≫ m.G.map (Q'.j X.T)) (e ≫ m.G.map (Cut.sec Q' X)) :=
    Q.lift_X _ _ (E.mem 0 ((e ≫ m.G.map X.s) ≫ m.G.map (Q'.j X.T)) (e ≫ m.G.map (Cut.sec Q' X)))
  have h2 := he 0 (X.s ≫ Q'.j X.T) (Cut.sec Q' X)
  rw [Cut.sec_spec, if_pos rfl, m.G.map_comp, ← Category.assoc] at h2
  rw [h1, h2]

def etaH (he : m.Fr E E' e) (X : Pt E') : Q.P (m.G.obj X.T) ⟶ m.G.obj (Q'.P X.T) := ((eta m Q Q' he).app X).1

theorem etaH_j (he : m.Fr E E' e) (X : Pt E') : Q.j (m.G.obj X.T) ≫ etaH m Q Q' he X = m.G.map (Q'.j X.T) :=
  eta_j m Q Q' he X

theorem etaH_X (he : m.Fr E E' e) (X : Pt E') :
    m.ρ (Q'.P X.T) ((Φ.A.map (etaH m Q Q' he X)).hom (Q.X (m.G.obj X.T))) = Ideal.Quotient.mk _ (Q'.X X.T) :=
  eta_X m Q Q' he X

end Cut

end GlobalTheory.CompanionTheory.LocCmp

namespace GlobalTheory.CompanionTheory.LocCmp

section Tr

variable {R : Type} [CommRing R] {D D' P P' : Type 1} [Category.{0} D] [Category.{0} D'] [Category.{0} P] [Category.{0} P']
  {F : D ⥤ ModuleCat.{0} R} {F' : D' ⥤ ModuleCat.{0} R}

def tr (m₀ : CH.Mor F F' (RingHom.id R)) (L : P ⥤ D) (L' : P' ⥤ D') (K : P' ⥤ P) (η : K ⋙ L ⟶ L' ⋙ m₀.G) :
    CH.Mor (L ⋙ F) (L' ⋙ F') (RingHom.id R) where
  G := K
  τ X := (m₀.τ (L'.obj X)).comp (F.map (η.app X)).hom
  nat {X Y} φ x := by
    change m₀.τ _ ((F.map (η.app Y)).hom ((F.map (L.map (K.map φ))).hom x)) =
      (F'.map (L'.map φ)).hom (m₀.τ _ ((F.map (η.app X)).hom x))
    rw [← m₀.nat]
    refine congrArg (m₀.τ _) ?_
    have h := congrArg (fun f => (F.map f).hom x) (η.naturality φ)
    simp only [Functor.map_comp] at h
    exact h

theorem tr_pull (m₀ : CH.Mor F F' (RingHom.id R)) (L : P ⥤ D) (L' : P' ⥤ D') (K : P' ⥤ P) (η : K ⋙ L ⟶ L' ⋙ m₀.G)
    (n : ℕ) (x : CH.H F n) :
    (tr m₀ L L' K η).pull n ((CH.Mor.restrict F L).pull n x) = (CH.Mor.restrict F' L').pull n (m₀.pull n x) := by
  rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) (CH.Mor.restrict F L) (tr m₀ L L' K η) n x).1,
    ← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) m₀ (CH.Mor.restrict F' L') n x).1]
  exact CrystallineSemistableComparison.P.prism _ _ η (fun _ _ => rfl) n x

theorem tr_bij (m₀ : CH.Mor F F' (RingHom.id R)) {L : P ⥤ D} {L' : P' ⥤ D'} (K : P' ⥤ P) (η : K ⋙ L ⟶ L' ⋙ m₀.G)
    {U : D ⥤ P} {U' : D' ⥤ P'} (a : L ⊣ U) (a' : L' ⊣ U') (n : ℕ) :
    Function.Bijective (m₀.pull n) ↔ Function.Bijective ((tr m₀ L L' K η).pull n) := by
  have h := CrystallineSemistableComparison.P.adj F L U a n
  have h' := CrystallineSemistableComparison.P.adj F' L' U' a' n
  have e : ((tr m₀ L L' K η).pull n : _ → _) ∘ (CH.Mor.restrict F L).pull n =
      (CH.Mor.restrict F' L').pull n ∘ m₀.pull n := funext fun x => tr_pull m₀ L L' K η n x
  rw [← Function.Bijective.of_comp_iff _ h, e, Function.Bijective.of_comp_iff' h']

end Tr

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R C'} {c : IdF Φ'.A}

def etaU (m : QMor Φ Φ' c) {d : ℕ} (E : Frame Φ d) (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D) :
    Gpt m E E' e ⋙ Pt.U E ⟶ Pt.U E' ⋙ m.G where
  app X := 𝟙 (m.G.obj X.T)
  naturality {X Y} φ := (Category.comp_id _).trans (Category.id_comp _).symm

def low (m : QMor Φ Φ' c) (B : IdF Φ'.A) (hB : ∀ T, c.S T ≤ B.S T) {d : ℕ} (E : Frame Φ d) (E' : Frame Φ' d)
    (e : E.D ⟶ m.G.obj E'.D) : CH.Mor (Pt.U E ⋙ CH.modF Φ.A) (Pt.U E' ⋙ sq (IdF.top Φ'.A) B) (RingHom.id R) :=
  tr (m.o B hB) (Pt.U E) (Pt.U E') (Gpt m E E' e) (etaU m E E' e)

section Cut

variable (m : QMor Φ Φ' c) (B : IdF Φ'.A) (hB : ∀ T, c.S T ≤ B.S T) {d : ℕ} {E : Frame Φ (d + 1)} {E' : Frame Φ' (d + 1)}
  {e : E.D ⟶ m.G.obj E'.D} (he : m.Fr E E' e) (Q : Poly Φ) (Q' : Poly Φ')

def cutO : CH.Mor (Cut.U E ⋙ CH.modF Φ.A) (Cut.U E' ⋙ sq (IdF.top Φ'.A) B) (RingHom.id R) where
  G := Gcut m he
  τ Y := (m.o B hB).τ Y.T
  nat φ x := (m.o B hB).nat φ.1 x

def mid : CH.Mor (Cut.P0 Q ⋙ Cut.U E ⋙ CH.modF Φ.A) (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (IdF.top Φ'.A) B) (RingHom.id R) :=
  tr (cutO m B hB he) (Cut.P0 Q) (Cut.P0 Q') (Gpt m E E' e) (eta m Q Q' he)

theorem mid_bij (n : ℕ) : Function.Bijective ((cutO m B hB he).pull n) ↔ Function.Bijective ((mid m B hB he Q Q').pull n) :=
  tr_bij _ _ _ (Cut.adj Q) (Cut.adj Q') n

end Cut

theorem low_bij (m : QMor Φ Φ' c) (B : IdF Φ'.A) (hB : ∀ T, c.S T ≤ B.S T) {d : ℕ} (E : Frame Φ d) (E' : Frame Φ' d)
    (e : E.D ⟶ m.G.obj E'.D) (n : ℕ) :
    Function.Bijective ((m.o B hB).pull n) ↔ Function.Bijective ((low m B hB E E' e).pull n) :=
  tr_bij _ _ _ (Pt.adj E) (Pt.adj E') n

end GlobalTheory.CompanionTheory.LocCmp

namespace GlobalTheory.CompanionTheory.LocCmp

section Base

variable {R : Type} [CommRing R]

theorem H_succ_zero {K : Cx.{1} R} {M : Type} [AddCommGroup M] [Module R M] {ε : M →ₗ[R] K.X 0} (h : K.ResUpTo 1 ε) (n : ℕ)
    (x : K.H (n + 1)) : x = 0 := by
  obtain ⟨u, hu, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K (n + 1)).1 x
  rw [(CrystallineSemistableComparison.P.cls_surj K (n + 1)).2.1]
  obtain ⟨y, hy⟩ := h.2.2.2 n u hu
  exact ⟨y, by simpa using hy⟩

theorem mapH_bij_of_res {K L : Cx.{1} R} (φ : Cx.Hom K L (RingHom.id R)) {M M' : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (ε : M →ₗ[R] K.X 0) (ε' : M' →ₗ[R] L.X 0) (a : M →ₗ[R] M')
    (ha : Function.Bijective a) (hc : ∀ x, φ.f 0 (ε x) = ε' (a x)) (hK : K.ResUpTo 1 ε) (hL : L.ResUpTo 1 ε') (n : ℕ) :
    Function.Bijective (φ.mapH n) := by
  cases n with
  | zero =>
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨u, hu, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K 0).1 x
      rw [CrystallineSemistableComparison.P.mapH_cls φ 0 u hu (by rw [φ.comm, hu, map_zero]), (CrystallineSemistableComparison.P.cls_surj L 0).2.1] at hx
      have h0 : φ.f 0 u = 0 := hx
      obtain ⟨y, hy⟩ := hK.2.2.1 u hu
      rw [one_smul] at hy
      subst hy
      rw [hc] at h0
      have h1 : a y = 0 := by simpa using hL.2.1 (a y) h0
      have h2 : y = 0 := ha.1 (h1.trans (map_zero a).symm)
      rw [(CrystallineSemistableComparison.P.cls_surj K 0).2.1]
      change ε y = 0
      rw [h2, map_zero]
    · intro z
      obtain ⟨v, hv, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L 0).1 z
      obtain ⟨t, ht⟩ := hL.2.2.1 v hv
      rw [one_smul] at ht
      obtain ⟨s, rfl⟩ := ha.2 t
      subst ht
      refine ⟨K.cls (ε s) (hK.1 s), ?_⟩
      rw [CrystallineSemistableComparison.P.mapH_cls φ 0 _ _ (by rw [hc]; exact hv)]
      exact (CrystallineSemistableComparison.P.cls_surj L 0).2.2.1 _ _ _ _ |>.2 (by rw [hc, sub_self]; exact Submodule.zero_mem _)
  | succ n =>
    constructor
    · intro x y _
      rw [H_succ_zero hK n x, H_succ_zero hK n y]
    · intro y
      exact ⟨0, by rw [H_succ_zero hL n y, map_zero]⟩

end Base

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R C'} {c : IdF Φ'.A}

theorem base (m : QMor Φ Φ' c) (E : Frame Φ 0) (E' : Frame Φ' 0) (e : E.D ⟶ m.G.obj E'.D) (B : IdF Φ'.A)
    (hB : ∀ T, c.S T ≤ B.S T)
    (hb : Function.Bijective fun x : Φ.A.obj E.D => (m.o B hB).τ E'.D ((Φ.A.map e).hom x)) (j : ℕ) :
    Function.Bijective ((m.o B hB).pull j) := by
  refine mapH_bij_of_res (m.o B hB).hom _ _ (((m.o B hB).τ E'.D).comp ((CH.modF Φ.A).map e).hom) hb ?_
    (CrystallineSemistableComparison.P.initial (CH.modF Φ.A) E.D E.initial) (CrystallineSemistableComparison.P.initial (sq (IdF.top Φ'.A) B) E'.D E'.initial) j
  intro x
  funext s
  have h1 : E.initial.to (m.G.obj (s.obj (Fin.last 0))) = e ≫ m.G.map (E'.initial.to (s.obj (Fin.last 0))) := E.initial.hom_ext _ _
  change (m.o B hB).τ _ (((CH.modF Φ.A).map (E.initial.to (m.G.obj (s.obj (Fin.last 0))))).hom x) =
    ((sq (IdF.top Φ'.A) B).map (E'.initial.to (s.obj (Fin.last 0)))).hom ((m.o B hB).τ _ (((CH.modF Φ.A).map e).hom x))
  rw [h1, ← (m.o B hB).nat, Functor.map_comp]
  rfl

end GlobalTheory.CompanionTheory.LocCmp

namespace GlobalTheory.CompanionTheory.LocCmp

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R C'} {c : IdF Φ'.A}

section Ses

def qE (A : C ⥤ CommAlgCat.{0} R) (T : C) : A.obj T ≃ₗ[R] sqM (IdF.top A) (IdF.bot A) T :=
  LinearEquiv.ofBijective ((toSq (IdF.top A) (IdF.bot A) (fun _ => rfl)).τ T)
    ⟨fun x y h => by
      have h1 : Ideal.Quotient.mk ((IdF.bot A).S T) (show A.obj T from x) = Ideal.Quotient.mk _ (show A.obj T from y) :=
        congrArg Subtype.val h
      have h2 := Ideal.Quotient.eq.1 h1
      exact sub_eq_zero.1 h2,
     fun z => by
      obtain ⟨z, hz⟩ := z
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨y, rfl⟩⟩

def jW {d : ℕ} {E : Frame Φ (d + 1)} (Q : Poly Φ) (F : C ⥤ ModuleCat.{0} R) : Pt.U E ⋙ F ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ F :=
  Functor.whiskerRight (Cut.jNat Q) F

theorem ses0 {d : ℕ} (Q : Poly Φ) (E : Frame Φ (d + 1)) (hQ : Q.Crit (fun _ => IdF.bot _) 0) :
    ∃ β : Cut.P0 Q ⋙ Cut.U E ⋙ CH.modF Φ.A ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ CH.modF Φ.A,
      (∀ X, Function.Injective ((jW (E := E) Q (CH.modF Φ.A)).app X).hom) ∧
      (∀ X, Function.Exact ((jW (E := E) Q (CH.modF Φ.A)).app X).hom (β.app X).hom) ∧
      (∀ X, Function.Surjective (β.app X).hom) ∧
      ∀ (X : Pt E) (c c' : ℕ →₀ Φ.A.obj X.T), (∀ k, c' k = c (k + 1)) →
        (β.app X).hom (c.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) =
          c'.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T) := by
  have hT : ∀ r, Q.Crit (fun _ => IdF.top Φ.A) r := fun r T b => ⟨fun _ _ => trivial, fun _ => trivial⟩
  obtain ⟨β, b1, b2, b3, b4⟩ := GlobalTheory.T.filtration_critical_comparison_map Q E (fun _ => IdF.top Φ.A) (fun _ => IdF.bot Φ.A) 0
    (fun _ T x _ => trivial) (hT _) (hT _) hQ hQ
  let q : ∀ T : C, Φ.A.obj T ≃ₗ[R] sqM (IdF.top Φ.A) (IdF.bot Φ.A) T := qE Φ.A
  let β₀ : Cut.P0 Q ⋙ Cut.U E ⋙ CH.modF Φ.A ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ CH.modF Φ.A :=
    { app := fun X => ModuleCat.ofHom ((q (Q.P X.T)).symm.toLinearMap ∘ₗ (β.app X).hom ∘ₗ (q (Q.P X.T)).toLinearMap)
      naturality := fun {X Y} φ => by
        ext x
        apply (q (Q.P Y.T)).injective
        have h := congrArg (fun f => f.hom (q (Q.P X.T) x)) (β.naturality φ)
        have e1 : ∀ w, q (Q.P Y.T) ((Φ.A.map (Cut.Pmap Q φ)).hom w) =
            ((sq (IdF.top Φ.A) (IdF.bot Φ.A)).map (Cut.Pmap Q φ)).hom (q _ w) := fun w => rfl
        change q (Q.P Y.T) ((q (Q.P Y.T)).symm ((β.app Y).hom (q (Q.P Y.T) ((Φ.A.map (Cut.Pmap Q φ)).hom x)))) =
          q (Q.P Y.T) ((Φ.A.map (Cut.Pmap Q φ)).hom ((q (Q.P X.T)).symm ((β.app X).hom (q (Q.P X.T) x))))
        rw [LinearEquiv.apply_symm_apply, e1, e1, LinearEquiv.apply_symm_apply]
        exact h }
  have hj : ∀ (X : Pt E) (u : Φ.A.obj X.T), ((Functor.whiskerRight (Cut.jNat (E := E) Q) (sq (IdF.top Φ.A) (IdF.bot Φ.A))).app X).hom (q X.T u) =
      q (Q.P X.T) ((Φ.A.map (Q.j X.T)).hom u) := fun X u => rfl
  have hβ : ∀ (X : Pt E) (y : Φ.A.obj (Q.P X.T)), (β₀.app X).hom y = (q (Q.P X.T)).symm ((β.app X).hom (q (Q.P X.T) y)) := fun X y => rfl
  refine ⟨β₀, fun X x y h => ?_, fun X y => ⟨fun hy => ?_, ?_⟩, fun X y => ?_, fun X c c' hc => ?_⟩
  · apply (q X.T).injective
    apply b1 X
    rw [hj, hj]
    exact congrArg (q (Q.P X.T)) h
  · have hy' : (β.app X).hom (q (Q.P X.T) y) = 0 := (LinearEquiv.map_eq_zero_iff (q (Q.P X.T)).symm).1 ((hβ X y).symm.trans hy)
    obtain ⟨u, hu⟩ := (b2 X (q (Q.P X.T) y)).1 hy'
    obtain ⟨w, rfl⟩ := (q X.T).surjective u
    rw [hj] at hu
    exact ⟨w, (q (Q.P X.T)).injective hu⟩
  · rintro ⟨u, rfl⟩
    change (β₀.app X).hom ((Φ.A.map (Q.j X.T)).hom u) = 0
    have h0 := (b2 X (q (Q.P X.T) ((Φ.A.map (Q.j X.T)).hom u))).2 ⟨q X.T u, hj X u⟩
    rw [hβ, h0, map_zero]
  · obtain ⟨z, hz⟩ := b3 X (q (Q.P X.T) y)
    obtain ⟨w, rfl⟩ := (q (Q.P X.T)).surjective z
    exact ⟨w, by rw [hβ, hz, LinearEquiv.symm_apply_apply]⟩
  · rw [hβ, b4 X c c' (q (Q.P X.T) _) (q (Q.P X.T) _) hc rfl rfl, LinearEquiv.symm_apply_apply]

end Ses

end GlobalTheory.CompanionTheory.LocCmp

namespace GlobalTheory.CompanionTheory.LocCmp

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R C'} {c : IdF Φ'.A}

theorem o_mk (m : QMor Φ Φ' c) (B : IdF Φ'.A) (hB : ∀ T, c.S T ≤ B.S T) (T : C') (x : Φ.A.obj (m.G.obj T)) (y : Φ'.A.obj T)
    (h : m.ρ T x = Ideal.Quotient.mk _ y) :
    ((m.o B hB).τ T x : sqM (IdF.top Φ'.A) B T).1 = Ideal.Quotient.mk _ y := by
  change Ideal.Quotient.factor (hB T) (m.ρ T x) = _
  rw [h]
  rfl

theorem low_τ (m : QMor Φ Φ' c) (B : IdF Φ'.A) (hB : ∀ T, c.S T ≤ B.S T) {d : ℕ} (E : Frame Φ d) (E' : Frame Φ' d)
    (e : E.D ⟶ m.G.obj E'.D) (X : Pt E') (x : Φ.A.obj (m.G.obj X.T)) :
    (low m B hB E E' e).τ X x = (m.o B hB).τ X.T x := by
  exact congrArg (fun f => (m.o B hB).τ X.T (f.hom x)) ((CH.modF Φ.A).map_id (m.G.obj X.T))

section Comm

variable (m : QMor Φ Φ' c) {d : ℕ} {E : Frame Φ (d + 1)} {E' : Frame Φ' (d + 1)}
  {e : E.D ⟶ m.G.obj E'.D} (he : m.Fr E E' e) (Q : Poly Φ) (Q' : Poly Φ')

theorem mid_τ (B : IdF Φ'.A) (hB : ∀ T, c.S T ≤ B.S T) (X : Pt E') (x : Φ.A.obj (Q.P (m.G.obj X.T))) :
    (mid m B hB he Q Q').τ X x = (m.o B hB).τ (Q'.P X.T) ((Φ.A.map (etaH m Q Q' he X)).hom x) := rfl

theorem comm_f (B : IdF Φ'.A) (hB : ∀ T, c.S T ≤ B.S T) (X : Pt E') (x : Φ.A.obj (m.G.obj X.T)) :
    (mid m B hB he Q Q').τ X (((jW (E := E) Q (CH.modF Φ.A)).app ((Gpt m E E' e).obj X)).hom x) =
      ((jW (E := E') Q' (sq (IdF.top Φ'.A) B)).app X).hom ((low m B hB E E' e).τ X x) := by
  rw [low_τ]
  change (m.o B hB).τ (Q'.P X.T) ((Φ.A.map (etaH m Q Q' he X)).hom ((Φ.A.map (Q.j (m.G.obj X.T))).hom x)) =
    ((sq (IdF.top Φ'.A) B).map (Q'.j X.T)).hom ((m.o B hB).τ X.T x)
  rw [← Cut.mapA_comp, etaH_j, ← (m.o B hB).nat]
  rfl

theorem rho_ev (X : Pt E') (cc : ℕ →₀ Φ.A.obj (m.G.obj X.T)) (y : ℕ →₀ Φ'.A.obj X.T)
    (h : ∀ k, m.ρ X.T (cc k) = Ideal.Quotient.mk _ (y k)) :
    m.ρ (Q'.P X.T) ((Φ.A.map (etaH m Q Q' he X)).hom
        (cc.sum fun k u => (Φ.A.map (Q.j (m.G.obj X.T))).hom u * Φ.dp k (Q.X (m.G.obj X.T)))) =
      Ideal.Quotient.mk _ (y.sum fun k u => (Φ'.A.map (Q'.j X.T)).hom u * Φ'.dp k (Q'.X X.T)) := by
  classical
  rw [Finsupp.sum_of_support_subset cc (Finset.subset_union_left (s₂ := y.support)) _ (by intros; simp),
    Finsupp.sum_of_support_subset y (Finset.subset_union_right (s₁ := cc.support)) _ (by intros; simp),
    map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, map_mul]
  congr 1
  · rw [← Cut.mapA_comp, etaH_j]
    exact m.nat (Q'.j X.T) (cc k) (y k) (h k)
  · rw [Φ.dp_map _ k (Q.X_mem _)]
    exact m.dp _ k _ _ (Φ.J.map_mem _ (Q.X_mem _)) (Q'.X_mem _) (etaH_X m Q Q' he X)

theorem comm_g (B B' : IdF Φ'.A) (hB : ∀ T, c.S T ≤ B.S T) (hB' : ∀ T, c.S T ≤ B'.S T)
    (β₀ : Cut.P0 Q ⋙ Cut.U E ⋙ CH.modF Φ.A ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ CH.modF Φ.A)
    (hβ₀ : ∀ (X : Pt E) (c c' : ℕ →₀ Φ.A.obj X.T), (∀ k, c' k = c (k + 1)) →
        (β₀.app X).hom (c.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) =
          c'.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T))
    (β' : Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (IdF.top Φ'.A) B ⟶ Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (IdF.top Φ'.A) B')
    (hβ' : ∀ (X : Pt E') (c c' : ℕ →₀ Φ'.A.obj X.T) (z : sqM (IdF.top Φ'.A) B (Q'.P X.T)) (z' : sqM (IdF.top Φ'.A) B' (Q'.P X.T)),
        (∀ k, c' k = c (k + 1)) →
        z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ'.A.map (Q'.j X.T)).hom y * Φ'.dp k (Q'.X X.T)) →
        z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ'.A.map (Q'.j X.T)).hom y * Φ'.dp k (Q'.X X.T)) →
        (β'.app X).hom z = z')
    (X : Pt E') (x : Φ.A.obj (Q.P (m.G.obj X.T))) :
    (mid m B' hB' he Q Q').τ X ((β₀.app ((Gpt m E E' e).obj X)).hom x) = (β'.app X).hom ((mid m B hB he Q Q').τ X x) := by
  classical
  obtain ⟨cc, rfl⟩ := Q.span (m.G.obj X.T) x
  let g : Φ.A.obj (m.G.obj X.T) → Φ'.A.obj X.T :=
    fun u => if u = 0 then 0 else Classical.choose (Ideal.Quotient.mk_surjective (m.ρ X.T u))
  have g0 : g 0 = 0 := if_pos rfl
  have hg : ∀ u, m.ρ X.T u = Ideal.Quotient.mk _ (g u) := by
    intro u
    by_cases hu : u = 0
    · subst hu
      rw [g0, map_zero, map_zero]
    · simp only [g, if_neg hu]
      exact (Classical.choose_spec (Ideal.Quotient.mk_surjective (m.ρ X.T u))).symm
  let sc : ℕ →₀ Φ.A.obj (m.G.obj X.T) := GlobalTheory.CompanionTheory.PolySes.sh cc
  have e1 := hβ₀ ((Gpt m E E' e).obj X) cc sc (fun k => rfl)
  refine Eq.symm (hβ' X (cc.mapRange g g0) (sc.mapRange g g0) _ _ (fun k => ?_) ?_ ?_)
  · simp only [Finsupp.mapRange_apply]
    rfl
  · rw [mid_τ]
    exact o_mk m B hB _ _ _ (rho_ev m he Q Q' X cc _ fun k => by rw [Finsupp.mapRange_apply]; exact hg _)
  · rw [mid_τ]
    refine o_mk m B' hB' _ _ _ ?_
    erw [e1]
    exact rho_ev m he Q Q' X sc _ fun k => by rw [Finsupp.mapRange_apply]; exact hg _

theorem upBij {M N : Type 1} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) :
    UpTo (1 : R) f ↔ Function.Bijective f :=
  (CrystallineSemistableComparison.P.upTo_alg f LinearMap.id 1 1).2.2.2.2

theorem step (b : ℤ → IdF Φ'.A) (h : ∀ r T, c.S T ≤ (b r).S T) (r : ℤ) (hQ : Q.Crit (fun _ => IdF.bot _) 0)
    (h1 : Q'.Crit b r) (h2 : Q'.Crit b (r - 1))
    (mb : ∀ j, Function.Bijective ((mid m (b r) (h r) he Q Q').pull j))
    (mc : ∀ j, Function.Bijective ((mid m (b (r - 1)) (h (r - 1)) he Q Q').pull j)) (j : ℕ) :
    Function.Bijective ((low m (b r) (h r) E E' e).pull j) := by
  obtain ⟨β₀, a1, a2, a3, a4⟩ := ses0 Q E hQ
  have hT : ∀ r, Q'.Crit (fun _ => IdF.top Φ'.A) r := fun r T b => ⟨fun _ _ => trivial, fun _ => trivial⟩
  obtain ⟨β', b1, b2, b3, b4⟩ := GlobalTheory.T.filtration_critical_comparison_map Q' E' (fun _ => IdF.top Φ'.A) b r (fun _ T x _ => trivial) (hT _) (hT _) h1 h2
  obtain ⟨i1, i2, i3⟩ := CrystallineSemistableComparison.P.ses_cochains (jW (E := E) Q (CH.modF Φ.A)) β₀ a1 a2 a3
  obtain ⟨k1, k2, k3⟩ := CrystallineSemistableComparison.P.ses_cochains (jW (E := E') Q' (sq (IdF.top Φ'.A) (b r))) β' b1 b2 b3
  have key := (CrystallineSemistableComparison.P.five _ _ i1 i2 i3 _ _ k1 k2 k3 (low m (b r) (h r) E E' e).hom (mid m (b r) (h r) he Q Q').hom
    (mid m (b (r - 1)) (h (r - 1)) he Q Q').hom
    (fun n x => funext fun s => comm_f m he Q Q' (b r) (h r) (s.obj (Fin.last n)) (x (s ⋙ Gpt m E E' e)))
    (fun n x => funext fun s => comm_g m he Q Q' (b r) (b (r - 1)) (h r) (h (r - 1)) β₀ a4 β' b4 (s.obj (Fin.last n)) (x (s ⋙ Gpt m E E' e)))
    (1 : R)).2.1 (fun n => (upBij _).2 (mb n)) (fun n => (upBij _).2 (mc n)) j
  rw [one_pow] at key
  exact (upBij _).1 key

end Comm

theorem main : ∀ (d : ℕ) {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C} {Φ' : PDF R C'}
    {c : IdF Φ'.A} (m : QMor Φ Φ' c) (Q : Poly Φ) (Q' : Poly Φ') (E : Frame Φ d) (E' : Frame Φ' d)
    (e : E.D ⟶ m.G.obj E'.D) (he : m.Fr E E' e) (b : ℤ → IdF Φ'.A) (h : ∀ r T, c.S T ≤ (b r).S T) (r : ℤ)
    (hQ : Q.Crit (fun _ => IdF.bot _) 0) (hQ' : ∀ r' ≤ r, Q'.Crit b r'),
    (∀ r', r - d ≤ r' → r' ≤ r → Function.Bijective fun x : Φ.A.obj E.D => (m.o (b r') (h r')).τ E'.D ((Φ.A.map e).hom x)) →
    ∀ j, Function.Bijective ((m.o (b r) (h r)).pull j) := by
  intro d
  induction d with
  | zero =>
    intro C C' _ _ Φ Φ' c m Q Q' E E' e he b h r hQ hQ' hyp j
    exact base m E E' e (b r) (h r) (hyp r (by simp) le_rfl) j
  | succ d ih =>
    intro C C' _ _ Φ Φ' c m Q Q' E E' e he b h r hQ hQ' hyp j
    have hcut : ∀ s, s ≤ r → r - (d + 1 : ℕ) ≤ s - d → ∀ j, Function.Bijective ((mid m (b s) (h s) he Q Q').pull j) := by
      intro s hs hs' j
      refine (mid_bij m (b s) (h s) he Q Q' j).1 ?_
      exact ih (m1 m he) (Cut.Q1 (E := E) Q) (Cut.Q1 (E := E') Q') (Cut.E1 E) (Cut.E1 E') (e1 m he) (Fr1 m he)
        (fun r => (b r).res (Cut.U E')) (fun r T => h r T.T) s (Cut.criterion_truncation Q hQ)
        (fun r' hr' => Cut.criterion_truncation Q' (hQ' r' (hr'.trans hs)))
        (fun r' lo hi => hyp r' (by omega) (by omega)) j
    refine (low_bij m (b r) (h r) E E' e j).2 ?_
    exact step m he Q Q' b h r hQ (hQ' r le_rfl) (hQ' _ (by omega))
      (hcut r le_rfl (by push_cast; omega)) (hcut (r - 1) (by omega) (by push_cast; omega)) j

end GlobalTheory.CompanionTheory.LocCmp

section Final

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem GlobalTheory.CompanionTheory.LocCmp.localComparison : ∀ {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C} {Φ' : PDF R C'}
    {c : IdF Φ'.A} (m : QMor Φ Φ' c) (Q : Poly Φ) (Q' : Poly Φ') {d : ℕ} (E : Frame Φ d) (E' : Frame Φ' d)
    (e : E.D ⟶ m.G.obj E'.D) (he : m.Fr E E' e) (b : ℤ → IdF Φ'.A) (h : ∀ r T, c.S T ≤ (b r).S T) (r : ℤ)
    (hQ : Q.Crit (fun _ => IdF.bot _) 0) (hQ' : ∀ r' ≤ r, Q'.Crit b r'),
    (∀ r', r - d ≤ r' → r' ≤ r → Function.Bijective fun x : Φ.A.obj E.D => (m.o (b r') (h r')).τ E'.D ((Φ.A.map e).hom x)) →
    ∀ j, Function.Bijective ((m.o (b r) (h r)).pull j) := by
  intro R _ C C' _ _ Φ Φ' c m Q Q' d E E' e he b h r hQ hQ' hyp j
  exact GlobalTheory.CompanionTheory.LocCmp.main d m Q Q' E E' e he b h r hQ hQ' hyp j

end Final
