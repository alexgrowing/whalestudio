import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulMPull
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLiftTensorCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Diso GlobalTheory.CompanionTheory.DisoHm

noncomputable section

namespace GlobalTheory.CompanionTheory.DisoHm

theorem dividedPowerFiltration_bot {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (hJ : J = ⊥) {r : ℕ} (hr : 1 ≤ r) :
    pdP δ r = ⊥ := by
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro _ ⟨L, hL, hr', rfl⟩
  have : ∃ q ∈ L, q.1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : (L.map Prod.fst).sum = 0 := List.sum_eq_zero (by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      exact hc q hq)
    omega
  obtain ⟨q, hq, hq0⟩ := this
  have hz : δ.dpow q.1 q.2 = 0 := by
    have h2 : q.2 = 0 := by
      have := hL q hq
      rw [hJ] at this
      exact this
    rw [h2]
    exact δ.dpow_eval_zero hq0
  have : (L.map fun q => δ.dpow q.1 q.2).prod = 0 := List.prod_eq_zero (List.mem_map.2 ⟨q, hq, hz⟩)
  rw [this]
  exact zero_mem _

section Loc
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem tfBase_ol (h : OL l O) {s : ℕ} (hs : 1 ≤ s) : TFBase (dividedPowersBot O) l s where
  nil := dividedPowerFiltration_bot _ rfl hs
  tf r x hx := by
    cases r with
    | zero =>
      have h1 : (1 : O) ∈ pdP (dividedPowersBot O) 0 := Ideal.subset_span ⟨[], by simp, by simp, by simp⟩
      simpa using Ideal.mul_mem_left _ x h1
    | succ r =>
      rw [dividedPowerFiltration_bot _ rfl (by omega)] at hx ⊢
      have hl : (l : O) ∈ nonZeroDivisors O := h.tf l (Fact.out : l.Prime).ne_zero
      exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hl).1 hx
  dv n hn := by
    obtain ⟨v, u, hlu, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l (Fact.out : l.Prime).ne_one
    obtain ⟨w, hw⟩ := (h.unit u hlu).exists_right_inv
    refine ⟨v, w, ?_⟩
    rw [e]
    push_cast
    rw [mul_assoc, hw, mul_one]

theorem o_bij (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) (b : IdF (sP Q).A)
    (hb : ∀ T, (IdF.span (sP Q).A ((l : O) ^ m)).S T ≤ b.S T) (T : Q.FullSubcategory)
    (hle : b.S T ≤ (IdF.span (sP Q).A ((l : O) ^ m)).S T) :
    Function.Bijective (((gQ h Q m hQ P hP).o b hb).τ T) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from x)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from y)
    have e : Ideal.Quotient.mk (b.S T) (show (sP Q).A.obj T from a) = Ideal.Quotient.mk (b.S T) (show (sP Q).A.obj T from c) :=
      congrArg Subtype.val hxy
    exact Ideal.Quotient.eq.2 ((lm_eq_span Q m T).ge (hle (Ideal.Quotient.eq.1 e)))
  · rintro ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk (lm (l := l) T.obj m) a, Subtype.ext rfl⟩

theorem local_bij (hLoc : DH.LocCmpq) (hPA : DH.PolyAll) (hPT : KH.PolyTf) (hCA : DH.ChartAlg) (hCP : DH.ChartP)
    (hCG : DH.ChartGood) (h : OL l O) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ) (hd : d < s) (m : ℕ)
    (hQ : ∀ T, TO q l s {W} T → Good (l := l) T m)
    (hP : ∀ T, St (⊤ : ObjectProperty (Thick (Lm h q m))) {W} ((GF h (TO q l s {W}) m hQ).obj T)) (j : ℕ) :
    Function.Bijective ((gP h (TO q l s {W}) m hQ (St ⊤ {W}) hP).pull j) := by
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hnil : IsNilpotent ((l : ℕ) : Om l O m) := ⟨m, by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : O) ^ m})), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _⟩
  obtain ⟨PL, hPL⟩ := hPA (pdm h m) l hl0 q (κm l O m) ⊤ (Or.inl rfl) {W}
  obtain ⟨PO, hPO⟩ := hPT (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {W}
  obtain ⟨cL, -, hcL⟩ := hCP (pdm h m) l hl0 hnil q (κm l O m) c
  obtain ⟨cO, e, hTF, hi, ht, hev⟩ := hCA (dividedPowersBot O) l s (tfBase_ol h (by omega)) q (Ideal.Quotient.mk ⊥)
    (fun _ => rfl) c
  have hgL := hCG cL
  have hgO := hCG cO
  have hDQ : TO q l s {W} cO.D := ⟨hTF, W, rfl, cO.inV⟩
  have hDP : St (⊤ : ObjectProperty (Thick (Lm h q m))) {W} cL.D := ⟨trivial, W, rfl, cL.inV⟩
  have hT : Good (l := l) cO.D m := hQ _ hDQ
  have hevt : ∀ i, ev cO.D cO.inV (c.t i) = Ideal.Quotient.mk _ (cO.t i) := fun i => by rw [hev, ht]
  obtain ⟨σ, hσ⟩ := exists_sig h c m cL hgL hcL cO hevt hT
  have hσb := GlobalTheory.T.chart_lift_tensor_compat h c m cL hcL cO e hi ht hev hT σ hσ
  let E := frameC (Ideal.Quotient.mk (Ideal.span {(l : O) ^ m}))
    (cL.frame hgL (St (⊤ : ObjectProperty (Thick (Lm h q m))) {W}) (fun T hT => by
      obtain ⟨-, V, rfl, hV⟩ := hT
      exact hV) hDP)
  let E' := cO.frame hgO (TO q l s {W}) (fun T hT => by
      obtain ⟨-, V, rfl, hV⟩ := hT
      exact hV) hDQ
  let M := gQ h (TO q l s {W}) m hQ (St ⊤ {W}) hP
  let e' : E.D ⟶ M.G.obj E'.D := ObjectProperty.homMk σ
  have he : M.Fr E E' e' := by
    intro i T s₁ s₂
    change gρ h (TO q l s {W}) m hQ (St ⊤ {W}) hP T (gφ s₂.hom m (σ.φ (cL.t i)) - gφ s₁.hom m (σ.φ (cL.t i))) =
      Ideal.Quotient.mk _ (s₂.hom.φ (cO.t i) - s₁.hom.φ (cO.t i))
    rw [hσ]
    rfl
  let b : ℤ → IdF (sP (TO q l s {W})).A := fun r => stdI (TO q l s {W}) (some r) ((l : O) ^ m)
  have hb : ∀ (r : ℤ) T, (IdF.span (sP (TO q l s {W})).A ((l : O) ^ m)).S T ≤ (b r).S T := fun r T => le_sup_right
  have key := hLoc M (polyC _ PL) PO E E' e' he b hb s (polyC_crit _ PL 0 (hPL 0).2.1)
    (fun r hr => (hPO r hr).2 _) (fun r' h1 h2 => by
      have hr1 : 1 ≤ r' := by omega
      have hle : (b r').S E'.D ≤ (IdF.span (sP (TO q l s {W})).A ((l : O) ^ m)).S E'.D := by
        refine sup_le ?_ le_rfl
        have : cO.D.pdPow r'.toNat = ⊥ := dividedPowerFiltration_bot _ (by rw [cO.J_eq]; exact Ideal.map_bot) (by omega)
        exact this.le.trans bot_le
      exact (o_bij h _ m hQ _ hP (b r') (hb r') E'.D hle).comp hσb) j
  have hb' : ∀ T, (stdI (TO q l s {W}) none ((l : O) ^ m)).S T = (b s).S T := by
    intro T
    have : T.obj.pdPow (s : ℤ).toNat = ⊥ := by
      have := T.property.1.1
      simpa using this
    change (⊥ : Ideal T.obj.B) ⊔ _ = T.obj.pdPow (s : ℤ).toNat ⊔ _
    rw [this]
  have hB := sqLe_bij (a := IdF.top (sP (TO q l s {W})).A) (a' := IdF.top (sP (TO q l s {W})).A) (fun _ => rfl) hb' j
  refine (Function.Bijective.of_comp_iff' hB _).1 ?_
  have e2 : ⇑((sqLe (a := IdF.top (sP (TO q l s {W})).A) (a' := IdF.top (sP (TO q l s {W})).A) (fun _ => le_rfl)
      (fun T => (hb' T).le)).pull j) ∘ ⇑((gP h (TO q l s {W}) m hQ (St ⊤ {W}) hP).pull j) =
      ⇑((M.o (b s) (hb s)).pull j) :=
    funext fun x => (gQ_o h _ m hQ _ hP (b s) (hb s) (fun T => (hb' T).le) j x).symm
  rw [e2]
  exact key
end Loc

section Nest
variable {D : Type 1} [Category.{0} D]

abbrev nestF {P P₂ : ObjectProperty D} {Pn : ObjectProperty P.FullSubcategory}
    (h₁ : ∀ T, P₂ T → ∃ hp : P T, Pn ⟨T, hp⟩) : P₂.FullSubcategory ⥤ Pn.FullSubcategory :=
  Pn.lift (P.lift P₂.ι fun T => (h₁ _ T.property).1) fun T => (h₁ _ T.property).2

def nestAdj {P P₂ : ObjectProperty D} {Pn : ObjectProperty P.FullSubcategory}
    (h₁ : ∀ T, P₂ T → ∃ hp : P T, Pn ⟨T, hp⟩) (h₂ : ∀ T : Pn.FullSubcategory, P₂ T.obj.obj) :
    nestF h₁ ⊣ (P₂.lift (Pn.ι ⋙ P.ι) h₂) :=
  (CategoryTheory.Equivalence.mk (nestF h₁)
    (P₂.lift (Pn.ι ⋙ P.ι) h₂) (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm))
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm))).toAdjunction

end Nest

theorem mem_biInf {X : Scheme.{0}} {ι : Type} (U : ι → X.Opens) (S : Finset ι) (x : X) :
    x ∈ (⨅ α ∈ S, U α) ↔ ∀ α ∈ S, x ∈ U α := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.iInf_insert]
    simp [ih]

section St
variable {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem inU_top (T : Thick (nlFun γ p X q κ)) : InU ⊤ T := fun _ _ => trivial

theorem st_inf (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (U : Cov q) (S : Finset U.ι) (hS : S.Nonempty)
    (T : Thick (nlFun γ p X q κ)) :
    St Q {⨅ α ∈ S, U.U α} T ↔ St Q (Set.range U.U) T ∧ ∀ α ∈ S, InU (U.U α) T := by
  constructor
  · rintro ⟨h1, V, rfl, hV⟩
    have h2 : ∀ α ∈ S, InU (U.U α) T := fun α hα x hx =>
      ((mem_biInf U.U S _).1 (hV hx)) α hα
    obtain ⟨α, hα⟩ := hS
    exact ⟨⟨h1, U.U α, ⟨α, rfl⟩, h2 α hα⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, _, rfl, fun x hx => (mem_biInf U.U S _).2 fun α hα => h2 α hα hx⟩

end St

section Top
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

def scM (h : OL l O) (q : X ⟶ Spec (CommRingCat.of O)) (m : ℕ) (Q : ObjectProperty (Thick (Lm h q m))) :
    CH.Mor (Q.ι ⋙ OMm h q m) (CH.modF (sP Q).A) (Ideal.Quotient.mk (Ideal.span {(l : O) ^ m})) where
  G := 𝟭 _
  τ T := { toFun := fun x => x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  nat _ _ := rfl

theorem scM_bij (h : OL l O) (q : X ⟶ Spec (CommRingCat.of O)) (m : ℕ) (Q : ObjectProperty (Thick (Lm h q m))) (j : ℕ) :
    Function.Bijective ((scM h q m Q).pull j) :=
  idM_bij (scM h q m Q).τ (scM h q m Q).nat (fun _ => Function.bijective_id) j

theorem top_L (hZ : DH.Zar2) (h : OL l O) (q : X ⟶ Spec (CommRingCat.of O)) (m : ℕ) (𝒱 : Set X.Opens) (hU : sSup 𝒱 = ⊤) (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict (OMm h q m) (St (⊤ : ObjectProperty (Thick (Lm h q m))) 𝒱).ι).pull j) := by
  have hle : St (⊤ : ObjectProperty (Thick (Lm h q m))) 𝒱 ≤ ⊤ := fun _ _ => trivial
  have z := (hZ (Q₀ := ⊤) (Or.inr ⟨(Fact.out : l.Prime).ne_zero, Or.inl rfl⟩) 𝒱 ⊤ hle
    (fun T _ => ⟨trivial, _, rfl, by rw [hU]; exact inU_top T⟩) (fun _ _ _ _ _ => trivial) j).2.2
  have r1 : Function.Bijective ((CH.Mor.restrict (OMm h q m) (⊤ : ObjectProperty (Thick (Lm h q m))).ι).pull j) :=
    CrystallineSemistableComparison.P.mapH_bij _ (GlobalTheory.CompanionTheory.CosieveBC.restrict_bij _ (fun _ => trivial)) j
  have c1 := scM_bij h q m ⊤ j
  have c2 := scM_bij h q m (St (⊤ : ObjectProperty (Thick (Lm h q m))) 𝒱) j
  refine (Function.Bijective.of_comp_iff' c2 _).1 ?_
  have e : ⇑((scM h q m (St (⊤ : ObjectProperty (Thick (Lm h q m))) 𝒱)).pull j) ∘
      ⇑((CH.Mor.restrict (OMm h q m) (St (⊤ : ObjectProperty (Thick (Lm h q m))) 𝒱).ι).pull j) =
      ⇑((incl hle).o.pull j) ∘ ⇑((scM h q m ⊤).pull j) ∘ ⇑((CH.Mor.restrict (OMm h q m) (⊤ : ObjectProperty (Thick (Lm h q m))).ι).pull j) := by
    funext x
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
    rfl
  rw [e]
  exact z.comp (c1.comp r1)

def resO {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (hle : Q' ≤ Q) (c : b.R) :
    CH.Mor (sq (IdF.top (sP Q).A) (stdI Q none c)) (sq (IdF.top (sP Q').A) (stdI Q' none c)) (RingHom.id _) :=
  (incl hle).sq (fun _ _ _ => trivial) (incl_std hle none c)

theorem std0 {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (T : Q.FullSubcategory) :
    (IdF.top (sP Q).A).S T = (stdI Q (some 0) 0).S T := by
  have : (sFil Q 0).S T = ⊤ := T.obj.pdPow_zero
  exact (top_le_iff.1 (this.ge.trans le_sup_left)).symm

theorem top_O (hZ : DH.Zar2) (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (hU : sSup 𝒱 = ⊤) (hle : TO q l s 𝒱 ≤ TO q l s {⊤})
    (c : O) (j : ℕ) : Function.Bijective ((resO hle c).pull j) := by
  have z := (hZ (Q₀ := TF l s) (Or.inl ⟨rfl, l, s, rfl⟩) 𝒱 (TO q l s {⊤}) hle
    (fun T hT => ⟨hT.1, _, rfl, by rw [hU]; exact inU_top T⟩)
    (fun _ T' _ _ hT' => ⟨hT', ⊤, rfl, inU_top T'⟩) j).2.1 (some 0) none 0 c
  have t0 := sqLe_bij (b := stdI (TO q l s {⊤}) none c) (b' := stdI (TO q l s {⊤}) none c) (std0 (TO q l s {⊤})) (fun _ => rfl) j
  have t1 := sqLe_bij (b := stdI (TO q l s 𝒱) none c) (b' := stdI (TO q l s 𝒱) none c) (std0 (TO q l s 𝒱)) (fun _ => rfl) j
  refine (Function.Bijective.of_comp_iff' t1 _).1 ?_
  have e : ⇑((sqLe (a := IdF.top (sP (TO q l s 𝒱)).A) (b := stdI (TO q l s 𝒱) none c) (a' := stdI (TO q l s 𝒱) (some 0) 0) (b' := stdI (TO q l s 𝒱) none c) (fun T => (std0 (TO q l s 𝒱) T).le) (fun _ => le_rfl)).pull j) ∘
      ⇑((resO hle c).pull j) = ⇑(((incl hle).sq (incl_std hle (some 0) 0) (incl_std hle none c)).pull j) ∘
      ⇑((sqLe (a := IdF.top (sP (TO q l s {⊤})).A) (b := stdI (TO q l s {⊤}) none c) (a' := stdI (TO q l s {⊤}) (some 0) 0) (b' := stdI (TO q l s {⊤}) none c) (fun T => (std0 (TO q l s {⊤}) T).le) (fun _ => le_rfl)).pull j) := by
    funext x
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id O) (resO hle c) (sqLe (a := IdF.top (sP (TO q l s 𝒱)).A) (b := stdI (TO q l s 𝒱) none c) (a' := stdI (TO q l s 𝒱) (some 0) 0) (b' := stdI (TO q l s 𝒱) none c) (fun T => (std0 (TO q l s 𝒱) T).le) (fun _ => le_rfl)) j x).1).symm.trans
      (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id O) (sqLe (a := IdF.top (sP (TO q l s {⊤})).A) (b := stdI (TO q l s {⊤}) none c) (a' := stdI (TO q l s {⊤}) (some 0) 0) (b' := stdI (TO q l s {⊤}) none c) (fun T => (std0 (TO q l s {⊤}) T).le) (fun _ => le_rfl)) ((incl hle).sq (incl_std hle (some 0) 0) (incl_std hle none c)) j x).1))
    refine CrystallineSemistableComparison.P.prism (σ := RingHom.id O) _ _ (𝟙 _) (fun T y => ?_) j x
    obtain ⟨y, hy⟩ := y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    first
      | rfl
      | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)
  rw [e]
  exact z.comp t0

end Top

section Glue
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

set_option maxHeartbeats 1000000 in
theorem glue (h : OL l O) (U : Cov q) (s m : ℕ) (hQ : ∀ (𝒱 : Set X.Opens) T, TO q l s 𝒱 T → Good (l := l) T m)
    (hP : ∀ (𝒱 : Set X.Opens) T, St (⊤ : ObjectProperty (Thick (Lm h q m))) 𝒱 ((GF h (TO q l s 𝒱) m (hQ 𝒱)).obj T))
    (hloc : ∀ S : Finset U.ι, S.Nonempty → ∀ j, Function.Bijective
      ((gP h (TO q l s {⨅ α ∈ S, U.U α}) m (hQ _) (St ⊤ {⨅ α ∈ S, U.U α}) (hP _)).pull j)) (j : ℕ) :
    Function.Bijective ((gP h (TO q l s (Set.range U.U)) m (hQ _) (St ⊤ (Set.range U.U)) (hP _)).pull j) := by
  refine cover_bij (gP h (TO q l s (Set.range U.U)) m (hQ _) (St ⊤ (Set.range U.U)) (hP _))
    (fun α T => InU (U.U α) T.obj) (fun α T => InU (U.U α) T.obj) (fun α T T' φ hT => Site.inU_hom φ.hom hT)
    (fun α T T' φ hT => Site.inU_hom φ.hom hT) (fun T => ?_) (fun T => ?_) (fun α T hT => inU_G h T.obj m _ hT)
    (fun S hS j => ?_) j
  · obtain ⟨-, V, ⟨α, rfl⟩, hV⟩ := T.property
    exact ⟨α, hV⟩
  · obtain ⟨-, V, ⟨α, rfl⟩, hV⟩ := T.property
    exact ⟨α, hV⟩
  have h₁L : ∀ T, St (⊤ : ObjectProperty (Thick (Lm h q m))) {⨅ α ∈ S, U.U α} T →
      ∃ hp : St (⊤ : ObjectProperty (Thick (Lm h q m))) (Set.range U.U) T,
        capS (fun α (T : (St (⊤ : ObjectProperty (Thick (Lm h q m))) (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S ⟨T, hp⟩ :=
    fun T hT => ⟨((st_inf _ U S hS T).1 hT).1, ((st_inf _ U S hS T).1 hT).2⟩
  have h₁O : ∀ T, TO q l s {⨅ α ∈ S, U.U α} T → ∃ hp : TO q l s (Set.range U.U) T,
        capS (fun α (T : (TO q l s (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S ⟨T, hp⟩ :=
    fun T hT => ⟨((st_inf _ U S hS T).1 hT).1, ((st_inf _ U S hS T).1 hT).2⟩
  have aL := nestAdj h₁L (fun T => (st_inf _ U S hS T.obj.obj).2 ⟨T.obj.property, T.property⟩)
  have aO := nestAdj h₁O (fun T => (st_inf _ U S hS T.obj.obj).2 ⟨T.obj.property, T.property⟩)
  let rL : CH.Mor ((capS (fun α (T : (St (⊤ : ObjectProperty (Thick (Lm h q m))) (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S).ι ⋙
      (St (⊤ : ObjectProperty (Thick (Lm h q m))) (Set.range U.U)).ι ⋙ OMm h q m)
      ((St (⊤ : ObjectProperty (Thick (Lm h q m))) {⨅ α ∈ S, U.U α}).ι ⋙ OMm h q m) (RingHom.id O) :=
    CH.Mor.restrict _ (nestF h₁L)
  let rO : CH.Mor ((capS (fun α (T : (TO q l s (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S).ι ⋙
      sq (IdF.top (sP (TO q l s (Set.range U.U))).A) (stdI (TO q l s (Set.range U.U)) none ((l : O) ^ m)))
      (sq (IdF.top (sP (TO q l s {⨅ α ∈ S, U.U α})).A) (stdI (TO q l s {⨅ α ∈ S, U.U α}) none ((l : O) ^ m))) (RingHom.id O) :=
    CH.Mor.restrict _ (nestF h₁O)
  have bL : Function.Bijective (rL.pull j) := CrystallineSemistableComparison.P.adj _ _ _ aL j
  have bO : Function.Bijective (rO.pull j) := CrystallineSemistableComparison.P.adj _ _ _ aO j
  refine (Function.Bijective.of_comp_iff' bO _).1 ?_
  have e : ∀ x, rO.pull j ((morU (gP h (TO q l s (Set.range U.U)) m (hQ _) (St ⊤ (Set.range U.U)) (hP _))
      (U := capS (fun α T => InU (U.U α) T.obj) S) (U' := capS (fun α T => InU (U.U α) T.obj) S)
      fun T hT α hα => inU_G h T.obj m _ (hT α hα)).pull j x) =
      (gP h (TO q l s {⨅ α ∈ S, U.U α}) m (hQ _) (St ⊤ {⨅ α ∈ S, U.U α}) (hP _)).pull j (rL.pull j x) := by
    intro x
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id O) _ rO j x).1).symm.trans
      (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id O) rL _ j x).1))
    refine CrystallineSemistableComparison.P.prism (σ := RingHom.id O) _ _ (𝟙 _) (fun T y => ?_) j x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from y)
    first
      | rfl
      | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)
  have e2 := funext e
  refine (show Function.Bijective (fun x => rO.pull j ((morU (gP h (TO q l s (Set.range U.U)) m (hQ _) (St ⊤ (Set.range U.U)) (hP _))
      (U := capS (fun α T => InU (U.U α) T.obj) S) (U' := capS (fun α T => InU (U.U α) T.obj) S)
      fun T hT α hα => inU_G h T.obj m _ (hT α hα)).pull j x)) from ?_)
  rw [e2]
  exact (hloc S hS j).comp bL

end Glue

theorem main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (h : OL l O) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (U : Cov q) (s : ℕ) (hs : ∀ α, U.d α < s) (m : ℕ) (hG : ∀ T, TO q l s {⊤} T → Good (l := l) T m) (j : ℕ), DH.LocCmpq → DH.Zar2 → DH.PolyAll → KH.PolyTf → DH.ChartAlg → DH.ChartP → DH.ChartGood → DH.ChartGrConst → DH.IsFilS → KH.GlobBcSt → Function.Bijective ((gMor h (TO q l s {⊤}) m hG).pull j) := by
  intro l _ O _ h X q U s hs m hG j hLoc hZ hPA hPT hCA hCP hCG _ _ _
  have hUs : sSup (Set.range U.U) = ⊤ := by
    rw [sSup_range]
    exact U.cover
  have htop : ∀ 𝒱 : Set X.Opens, TO q l s 𝒱 ≤ TO q l s {⊤} := fun 𝒱 T hT => ⟨hT.1, ⊤, rfl, inU_top T⟩
  have hQ : ∀ (𝒱 : Set X.Opens) T, TO q l s 𝒱 T → Good (l := l) T m := fun 𝒱 T hT => hG T (htop 𝒱 T hT)
  have hP : ∀ (𝒱 : Set X.Opens) T, St (⊤ : ObjectProperty (Thick (Lm h q m))) 𝒱 ((GF h (TO q l s 𝒱) m (hQ 𝒱)).obj T) := fun 𝒱 T => by
    obtain ⟨-, V, hV, hin⟩ := T.property
    exact ⟨trivial, V, hV, inU_G h T.obj m _ hin⟩
  have g := glue h U s m hQ hP (fun S hS j => by
    obtain ⟨α, hα⟩ := hS
    obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c α) (iInf₂_le α hα : (⨅ α ∈ S, U.U α) ≤ U.U α) (U.inter S ⟨α, hα⟩)
    exact local_bij hLoc hPA hPT hCA hCP hCG h c' s (hs α) m _ _ j) j
  have tL := top_L hZ h q m _ hUs j
  have tO := top_O hZ q l s _ hUs (htop _) ((l : O) ^ m) j
  refine (Function.Bijective.of_comp_iff' tO _).1 ?_
  have e : ⇑((resO (htop (Set.range U.U)) ((l : O) ^ m)).pull j) ∘ ⇑((gMor h (TO q l s {⊤}) m hG).pull j) =
      ⇑((gP h (TO q l s (Set.range U.U)) m (hQ _) (St ⊤ (Set.range U.U)) (hP _)).pull j) ∘
      ⇑((CH.Mor.restrict (OMm h q m) (St (⊤ : ObjectProperty (Thick (Lm h q m))) (Set.range U.U)).ι).pull j) := by
    funext x
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id O) (gMor h (TO q l s {⊤}) m hG) (resO (htop (Set.range U.U)) ((l : O) ^ m)) j x).1).symm.trans
      (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id O) (CH.Mor.restrict (OMm h q m) (St (⊤ : ObjectProperty (Thick (Lm h q m))) (Set.range U.U)).ι)
        (gP h (TO q l s (Set.range U.U)) m (hQ _) (St ⊤ (Set.range U.U)) (hP _)) j x).1))
    refine CrystallineSemistableComparison.P.prism (σ := RingHom.id O) (CH.Mor.comp (σ'' := RingHom.id O) (gMor h (TO q l s {⊤}) m hG) (resO (htop (Set.range U.U)) ((l : O) ^ m)))
      (CH.Mor.comp (σ'' := RingHom.id O) (CH.Mor.restrict (OMm h q m) (St (⊤ : ObjectProperty (Thick (Lm h q m))) (Set.range U.U)).ι)
        (gP h (TO q l s (Set.range U.U)) m (hQ _) (St ⊤ (Set.range U.U)) (hP _))) (𝟙 _) (fun T y => ?_) j x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from y)
    first
      | rfl
      | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)
  rw [e]
  exact g.comp tL

end GlobalTheory.CompanionTheory.DisoHm
