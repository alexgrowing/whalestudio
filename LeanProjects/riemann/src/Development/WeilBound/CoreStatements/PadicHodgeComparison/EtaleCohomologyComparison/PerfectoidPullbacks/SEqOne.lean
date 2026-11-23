import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

def pdP {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (r : ℕ) : Ideal B :=
  Ideal.span {z | ∃ l : List (ℕ × B), (∀ q ∈ l, q.2 ∈ J) ∧ r ≤ (l.map Prod.fst).sum ∧
    z = (l.map fun q => δ.dpow q.1 q.2).prod}

theorem dividedPowerFiltration_map {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'} {δ : DividedPowers J}
    {δ' : DividedPowers J'} {f : B →+* B'} (hf : IsDPMorphism δ δ' f) (r : ℕ) {x : B} (hx : x ∈ pdP δ r) :
    f x ∈ pdP δ' r := by
  have : pdP δ r ≤ (pdP δ' r).comap f := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨l, hl, hr, rfl⟩
    refine Ideal.subset_span ⟨l.map fun q => (q.1, f q.2), ?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
      exact hf.1 (Ideal.mem_map_of_mem f (hl q' hq'))
    · simpa [List.map_map, Function.comp_def] using hr
    · rw [map_list_prod, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left fun q hq => ?_
      exact (hf.2 q.2 (hl q hq)).symm
  exact this hx

section General

variable {b : Base} (L : b.Fun)

theorem pdPow_eq (T : Thick L) (r : ℕ) : T.pdPow r = pdP T.δ r := rfl

def thA : Thick L ⥤ CommAlgCat.{0} b.R where
  obj T := letI := T.i.toAlgebra; CommAlgCat.of b.R T.B
  map {T T'} f :=
    letI := T.i.toAlgebra; letI := T'.i.toAlgebra
    CommAlgCat.ofHom { f.φ with commutes' := f.comm }
  map_id _ := rfl
  map_comp _ _ := rfl

theorem modF_thA : CH.modF (thA L) = O L := rfl

def thP : PDF b.R (Thick L) where
  A := thA L
  J := ⟨fun T => T.J, fun φ _ hx => φ.hle hx⟩
  dp {T} k x := T.δ.dpow k x
  dp_zero {T} _ hx := T.δ.dpow_zero hx
  dp_one {T} _ hx := T.δ.dpow_one hx
  dp_zero_right {T} _ hk := T.δ.dpow_eval_zero hk
  dp_add {T} k _ _ hx hy := T.δ.dpow_add hx hy
  dp_map φ k x hx := (φ.dp.2 x hx).symm

def thFil (r : ℤ) : IdF (thA L) := ⟨fun T => T.pdPow r.toNat, fun φ _ hx => dividedPowerFiltration_map φ.dp _ hx⟩

variable {L}

abbrev sP (Q : ObjectProperty (Thick L)) : PDF b.R Q.FullSubcategory := (thP L).res Q.ι

abbrev sFil (Q : ObjectProperty (Thick L)) (r : ℤ) : IdF (sP Q).A := (thFil L r).res Q.ι

abbrev HQ (Q : ObjectProperty (Thick L)) (r r' : ℤ) (j : ℕ) : Type 1 := CH.H (sq (sFil Q r) (sFil Q r')) j

abbrev HO (Q : ObjectProperty (Thick L)) (j : ℕ) : Type 1 := CH.H (CH.modF (sP Q).A) j

def TF (l s : ℕ) : ObjectProperty (Thick L) :=
  fun T => T.pdPow s = ⊥ ∧ ∀ (r : ℕ) (x : T.B), (l : T.B) * x ∈ T.pdPow r → x ∈ T.pdPow r

end General

def toSq {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A)
    (ha : ∀ T, a.S T = ⊤) : CH.Mor (CH.modF A) (sq a b) (RingHom.id R) where
  G := 𝟭 C
  τ T :=
    { toFun := fun x => sqMk a b (show A.obj T from x) (by rw [ha]; trivial)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  nat _ _ := rfl

abbrev nlBase (R : Type) [CommRing R] (I : Ideal R) (γ : DividedPowers I) (p : ℕ) : Base where
  R := R
  I := I
  γ := γ
  t := 1
  p := p

variable {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R}

def nlFun (γ : DividedPowers I) (p : ℕ) (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) :
    (nlBase R I γ p).Fun where
  ι := Empty
  A := Unit
  Pt := ptFun X q κ
  str y := y.1.1
  str_map _ _ := rfl
  In _ _ _ := True
  in_map _ _ _ := trivial
  f _ i := i.elim
  f_map i := i.elim
  g _ _ i := i.elim
  g_map i := i.elim
  f_eq i := i.elim
  g_self i := i.elim
  g_comp i := i.elim
  prod_f {_ _ y} _ := by simp
  prod_g _ _ := by simp

theorem smFun_eq {K : Type} [CommRing K] (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) :
    smFun X q = nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥) := rfl

variable {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

instance : IsEmpty (nlFun γ p X q κ).ι := inferInstanceAs (IsEmpty Empty)

theorem prod_e {M : Type} [CommMonoid M] (f : (nlFun γ p X q κ).ι → M) : ∏ j, f j = 1 := Finset.prod_of_isEmpty _

def pt (T : Thick (nlFun γ p X q κ)) : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ X :=
  (show PtOver X q κ (T.B ⧸ T.J) from T.y).1.2

def InU (V : X.Opens) (T : Thick (nlFun γ p X q κ)) : Prop := ⊤ ≤ pt T ⁻¹ᵁ V

def ev {V : X.Opens} (T : Thick (nlFun γ p X q κ)) (h : InU V T) : Γ(X, V) →+* T.B ⧸ T.J := GlobalTheory.Cris.evalAt (pt T) V h

def St (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (𝒱 : Set X.Opens) : ObjectProperty (Thick (nlFun γ p X q κ)) :=
  fun T => Q T ∧ ∃ V ∈ 𝒱, InU V T

def mkT (B : Type) [CommRing B] (i : R →+* B) (J : Ideal B) (δ : DividedPowers J)
    (adm : (p ≠ 0 → IsNilpotent (p : B)) ∧ (p = 0 → IsNilpotent J)) (compat : IsDPMorphism γ δ i)
    (y : PtOver X q κ (B ⧸ J)) (w : ∀ r, y.1.1 (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk J (i r)) :
    Thick (nlFun γ p X q κ) where
  B := B
  i := i
  J := J
  δ := δ
  adm := adm
  compat := compat
  α := ()
  y := y
  inα := trivial
  w := w
  x j := j.elim
  v j := j.elim
  s := 1
  hx j := j.elim
  hs := (prod_e _).trans (by simp)
  hv := (map_one _).trans (prod_e _).symm

theorem s_eq_one (T : Thick (nlFun γ p X q κ)) : T.s = 1 := by
  have h := T.hs
  rw [prod_e] at h
  ext
  simpa using h.symm

def mkH {T T' : Thick (nlFun γ p X q κ)} (φ : T.B →+* T'.B) (comm : ∀ r, φ (T.i r) = T'.i r)
    (dp : IsDPMorphism T.δ T'.δ φ) (hle : T.J ≤ T'.J.comap φ)
    (hpt : (nlFun γ p X q κ).Pt.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ hle)) T.y = T'.y) : T ⟶ T' where
  φ := φ
  u j := j.elim
  comm := comm
  dp := dp
  hle := hle
  pt := hpt
  hx j := j.elim
  hs := by
    have h1 := s_eq_one T
    have h2 := s_eq_one T'
    rw [h1, h2]
    exact ((congrArg₂ (· * ·) (prod_e _) (map_one _)).trans (mul_one 1)).symm
  hv j := j.elim

theorem hom_ext {T T' : Thick (nlFun γ p X q κ)} {f g : T ⟶ T'} (h : f.φ = g.φ) : f = g :=
  Thick.Hom.ext h (funext fun j => j.elim)

structure Chart (γ : DividedPowers I) (p : ℕ) (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (V : X.Opens) (d : ℕ) where
  D : Thick (nlFun γ p X q κ)
  t : Fin d → D.B
  etale : (MvPolynomial.eval₂Hom D.i t : MvPolynomial (Fin d) R →+* D.B).Etale
  J_eq : D.J = I.map D.i
  inV : InU V D
  rep : ∀ (B : CommRingCat.{0}) (y : PtOver X q κ B), ⊤ ≤ y.1.2 ⁻¹ᵁ V →
    ∃! φ : D.B ⧸ D.J →+* B, (ptFun X q κ).map (CommRingCat.ofHom φ) D.y = y

namespace Chart

variable {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d)

def Good : Prop :=
  (∀ T : Thick (nlFun γ p X q κ), InU V T → Nonempty (c.D ⟶ T)) ∧
  ∀ (T : Thick (nlFun γ p X q κ)) (σ : c.D ⟶ T) (y : Fin d → T.B), (∀ i, y i ∈ T.J) →
    ∃! σ' : c.D ⟶ T, ∀ i, σ'.φ (c.t i) - σ.φ (c.t i) = y i

def frame (h : c.Good) (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : ∀ T, Q T → InU V T) (hD : Q c.D) :
    Frame (sP Q) d where
  D := ⟨c.D, hD⟩
  ne T := (h.1 T.obj (hQ _ T.property)).map fun σ => ObjectProperty.homMk σ
  τ i {T} σ σ' := (σ'.hom.φ (c.t i) - σ.hom.φ (c.t i) : T.obj.B)
  mem i {T} σ σ' := by
    obtain ⟨φ, -, hu⟩ := c.rep (CommRingCat.of (T.obj.B ⧸ T.obj.J)) T.obj.y (hQ _ T.property)
    have e := (hu _ σ'.hom.pt).trans (hu _ σ.hom.pt).symm
    exact Ideal.Quotient.eq.1 (RingHom.congr_fun e (Ideal.Quotient.mk _ (c.t i)))
  add i {T} σ σ' σ'' := by
    change (_ : T.obj.B) = (_ - _ : T.obj.B) + (_ - _ : T.obj.B)
    ring
  nat i {T T'} σ σ' φ := (map_sub φ.hom.φ _ _).symm
  bij {T} σ y hy := by
    obtain ⟨σ', h1, h2⟩ := h.2 T.obj σ.hom y hy
    exact ⟨ObjectProperty.homMk σ', h1, fun τ hτ => ObjectProperty.hom_ext _ (h2 τ.hom hτ)⟩

end Chart

def strV (q : X ⟶ Spec (CommRingCat.of O)) (V : X.Opens) : O →+* Γ(X, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ q.appLE ⊤ V le_top).hom

structure Coord (q : X ⟶ Spec (CommRingCat.of O)) (V : X.Opens) (d : ℕ) where
  affine : IsAffineOpen V
  t : Fin d → Γ(X, V)
  etale : (MvPolynomial.eval₂Hom (strV q V) t : MvPolynomial (Fin d) O →+* Γ(X, V)).Etale

structure Cov (q : X ⟶ Spec (CommRingCat.of O)) where
  ι : Type
  [fin : Fintype ι]
  U : ι → X.Opens
  d : ι → ℕ
  c : ∀ α, Coord q (U α) (d α)
  cover : (⨆ α, U α) = ⊤
  inter : ∀ S : Finset ι, S.Nonempty → IsAffineOpen (⨅ α ∈ S, U α)

attribute [instance] Cov.fin

section Change

variable {O' : Type} [CommRing O'] {R' : Type} [CommRing R'] {I' : Ideal R'} {γ' : DividedPowers I'} {p' : ℕ}
  {X' : Scheme.{0}} {q' : X' ⟶ Spec (CommRingCat.of O')} {κ' : O' →+* R' ⧸ I'}

structure NMor (γ : DividedPowers I) (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I)
    (γ' : DividedPowers I') (q' : X' ⟶ Spec (CommRingCat.of O')) (κ' : O' →+* R' ⧸ I') (σ : R →+* R') where
  hI : IsDPMorphism γ γ' σ
  u : X' ⟶ X
  g : O →+* O'
  hu : u ≫ q = q' ≫ Spec.map (CommRingCat.ofHom g)
  hκ : ∀ (a : O) (r : R), κ a = Ideal.Quotient.mk _ r → κ' (g a) = Ideal.Quotient.mk _ (σ r)

variable {σ : R →+* R'}

def NMor.bar (m : NMor γ q κ γ' q' κ' σ) : R ⧸ I →+* R' ⧸ I' :=
  Ideal.quotientMap I' σ fun _ hx => m.hI.1 (Ideal.mem_map_of_mem σ hx)

theorem NMor.bar_κ (m : NMor γ q κ γ' q' κ' σ) : m.bar.comp κ = κ'.comp m.g := by
  ext a
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (κ a)
  rw [RingHom.comp_apply, RingHom.comp_apply, m.hκ a r hr.symm, ← hr]
  rfl

def NMor.mor (m : NMor γ q κ γ' q' κ' σ) (p : ℕ) : Mor (nlFun γ p X q κ) (nlFun γ' p X' q' κ') σ where
  hp := rfl
  hI := m.hI
  a := 1
  ha := by simp
  m := 1
  ht := by simp
  e i := i.elim
  he j := j.elim
  c α := α
  pt := { app := fun B => TypeCat.ofHom fun z => ⟨(z.1.1.comp m.bar, z.1.2 ≫ m.u), by
            rw [Category.assoc, m.hu, ← Category.assoc, z.2, ← Spec.map_comp, RingHom.comp_assoc, m.bar_κ]; rfl⟩
          naturality := fun B B' φ => by
            ext z
            refine Subtype.ext (Prod.ext rfl ?_)
            exact Category.assoc _ _ _ }
  str _ _ := rfl
  inc _ := trivial
  w _ i := i.elim
  w_map i := i.elim
  hf i := i.elim
  hg i := i.elim
  hw _ := Finset.prod_of_isEmpty (ι := Empty) _

def NMor.smor (m : NMor γ q κ γ' q' κ' σ) {p : ℕ} (Q : ObjectProperty (Thick (nlFun γ p X q κ)))
    (Q' : ObjectProperty (Thick (nlFun γ' p X' q' κ'))) (h : ∀ T, Q' T → Q ((m.mor p).obj T)) :
    SMor (sP Q) (sP Q') σ where
  G := Q.lift (Q'.ι ⋙ (m.mor p).functor) fun T => h _ T.property
  ρ T := RingHom.id _
  comm _ _ := rfl
  nat _ _ := rfl
  mem _ _ hx := hx
  dp _ _ _ _ := rfl

end Change

def incl {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) : SMor (sP Q) (sP Q') (RingHom.id _) where
  G := ObjectProperty.ιOfLE h
  ρ T := RingHom.id _
  comm _ _ := rfl
  nat _ _ := rfl
  mem _ _ hx := hx
  dp _ _ _ _ := rfl

def SMor.o {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C}
    {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ) : CH.Mor (CH.modF Φ.A) (CH.modF Φ'.A) σ where
  G := m.G
  τ T :=
    { toFun := fun x => m.ρ T x
      map_add' := map_add _
      map_smul' := fun r (x : Φ.A.obj _) => by
        change m.ρ T (r • x) = σ r • m.ρ T x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, m.comm] }
  nat φ x := m.nat φ x

end CrystallineSemistableComparison.Pb
