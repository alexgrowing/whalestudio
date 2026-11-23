import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CxPairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Opposite

universe w w' t t' v u v' u'

namespace CrystallineSemistableComparison.CH

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

abbrev elF (E : C ⥤ Type t) (F : C ⥤ ModuleCat.{w} R) : E.Elements ⥤ ModuleCat.{w} R := CategoryOfElements.π E ⋙ F

def elMor {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R) : Mor (elF E F) (elF E' F) (RingHom.id R) where
  G := CategoryOfElements.map p
  τ _ := LinearMap.id
  nat _ _ := rfl

def elCoef (E : C ⥤ Type t) {F F' : C ⥤ ModuleCat.{w} R} (α : F ⟶ F') : Mor (elF E F) (elF E F') (RingHom.id R) :=
  Mor.ofNatTrans (Functor.whiskerLeft _ α)

def cech {E' E : C ⥤ Type t} (p : E' ⟶ E) (n : ℕ) : C ⥤ Type t where
  obj T := {y : Fin (n + 1) → E'.obj T // ∀ i j, p.app T (y i) = p.app T (y j)}
  map {T T'} φ := TypeCat.ofHom fun y => ⟨fun i => E'.map φ (y.1 i), fun i j => by
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, y.2 i j]⟩
  map_id T := by ext y i; simp
  map_comp φ ψ := by ext y i; simp

def cechMap {E' E : C ⥤ Type t} (p : E' ⟶ E) {m n : ℕ} (g : Fin (m + 1) → Fin (n + 1)) : cech p n ⟶ cech p m where
  app T := TypeCat.ofHom fun y => ⟨fun i => y.1 (g i), fun i j => y.2 _ _⟩

def cechAug {E' E : C ⥤ Type t} (p : E' ⟶ E) (n : ℕ) : cech p n ⟶ E where
  app T := TypeCat.ofHom fun y => p.app T (y.1 0)
  naturality T T' φ := by
    ext y
    exact NatTrans.naturality_apply p φ (y.1 0)

abbrev cechCos {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R) : CosCx.{max u v w t} R where
  K n := cx (elF (cech p n) F)
  δ n i := (elMor (cechMap p i.succAbove) F).hom
  rel n j i q x := by
    have e : (cechMap p (j.succAbove i).succAbove ≫ cechMap p (i.predAbove j).succAbove : cech p (n + 2) ⟶ cech p n) =
        cechMap p j.succAbove ≫ cechMap p i.succAbove := by
      ext T y
      exact Subtype.ext (funext fun k => congrArg y.1 (Fin.succAbove_succAbove_succAbove_predAbove j i k))
    exact congrArg (fun a => (elMor a F).pullC q x) e

def cechAugRow {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R) :
    DCx.AugRow (cx (elF E F)) (cechCos p F).dcx where
  ε q := (elMor (cechAug p 0) F).pullC q
  hε q x := by
    have e : (cechMap p (0 : Fin 2).succAbove ≫ cechAug p 0 : cech p 1 ⟶ E) = cechMap p (1 : Fin 2).succAbove ≫ cechAug p 0 := by
      ext T y
      exact y.2 _ _
    have e' : (elMor (cechMap p (0 : Fin 2).succAbove) F).pullC q ((elMor (cechAug p 0) F).pullC q x) =
        (elMor (cechMap p (1 : Fin 2).succAbove) F).pullC q ((elMor (cechAug p 0) F).pullC q x) :=
      congrArg (fun a => (elMor a F).pullC q x) e
    refine (Cos.d_apply ((cechCos p F).cos q) 0 _).trans ?_
    rw [Fin.sum_univ_two]
    change (-1 : ℤ) ^ 0 • (elMor (cechMap p (0 : Fin 2).succAbove) F).pullC q ((elMor (cechAug p 0) F).pullC q x) +
      (-1 : ℤ) ^ 1 • (elMor (cechMap p (1 : Fin 2).succAbove) F).pullC q ((elMor (cechAug p 0) F).pullC q x) = 0
    rw [e']; simp
  comm q x := (elMor (cechAug p 0) F).d_pullC q x

structure CxF (C : Type u) [Category.{v} C] (R : Type) [CommRing R] where
  F : ℕ → (C ⥤ ModuleCat.{w} R)
  δ : ∀ q, F q ⟶ F (q + 1)
  dd : ∀ q T x, ((δ (q + 1)).app T).hom (((δ q).app T).hom x) = 0

abbrev CxF.obj (K : CxF.{w} C R) (T : C) : Cx.{w} R where
  X q := (K.F q).obj T
  d q := ((K.δ q).app T).hom
  dd q := K.dd q T

abbrev CxF.dcx (K : CxF.{w} C R) : DCx.{max u v w} R where
  X p q := Cn (K.F q) p
  dh p q := d (K.F q) p
  dv p q := (Mor.ofNatTrans (K.δ q)).pullC p
  hh p q := d_d (K.F q) p
  vv p q x := funext fun s => K.dd q _ _
  hv p q x := (Mor.ofNatTrans (K.δ q)).d_pullC p x

def CxF.augCol (K : CxF.{w} C R) {F : C ⥤ ModuleCat.{w} R} (η : F ⟶ K.F 0)
    (h : ∀ T x, ((K.δ 0).app T).hom ((η.app T).hom x) = 0) : DCx.AugCol (cx F) K.dcx where
  η p := (Mor.ofNatTrans η).pullC p
  hη p x := funext fun s => h _ _
  comm p x := (Mor.ofNatTrans η).d_pullC p x

def piF {ι : Type w} (F : ι → (C ⥤ ModuleCat.{w} R)) : C ⥤ ModuleCat.{w} R where
  obj T := ModuleCat.of R (∀ i, (F i).obj T)
  map φ := ModuleCat.ofHom (LinearMap.pi fun i => ((F i).map φ).hom.comp (LinearMap.proj i))
  map_id T := by ext x i; simp
  map_comp φ ψ := by ext x i; simp

def piProj {ι : Type w} (F : ι → (C ⥤ ModuleCat.{w} R)) (i : ι) : Mor (piF F) (F i) (RingHom.id R) where
  G := 𝟭 C
  τ T := LinearMap.proj (R := R) (φ := fun i => (F i).obj T) i
  nat _ _ := rfl

section Rel

variable {I : Type t} [Category.{t'} I] (π : C ⥤ I)

abbrev relF (F : C ⥤ ModuleCat.{w} R) (i : I) : StructuredArrow i π ⥤ ModuleCat.{w} R := StructuredArrow.proj i π ⋙ F

def relRes (F : C ⥤ ModuleCat.{w} R) {i i' : I} (a : i ⟶ i') : Mor (relF π F i) (relF π F i') (RingHom.id R) where
  G := StructuredArrow.map a
  τ _ := LinearMap.id
  nat _ _ := rfl

def relAug (F : C ⥤ ModuleCat.{w} R) (i : I) : Mor F (relF π F i) (RingHom.id R) := Mor.restrict F _

def relMor {R' : Type} [CommRing R'] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'}
    {σ : R →+* R'} (m : Mor F F' σ) (i : I) : Mor (relF π F i) (relF (m.G ⋙ π) F' i) σ where
  G := StructuredArrow.pre i m.G π
  τ x := m.τ x.right
  nat φ x := m.nat φ.right x

end Rel

section Ind

variable {T : Type u'} [Category.{v'} T] (j : T ⥤ C)

abbrev pts (A : C) : T ⥤ Type v := j ⋙ coyoneda.obj (op A)

def ptsAug (F : C ⥤ ModuleCat.{w} R) (A : C) : F.obj A →ₗ[R] Cn (elF (pts j A) (j ⋙ F)) 0 :=
  aug (elF (pts j A) (j ⋙ F)) fun x => (F.map (show A ⟶ j.obj x.1 from x.2)).hom

structure Powers (A : C) where
  B : C
  f : A ⟶ B
  K : ℕ → C
  a : ∀ n, A ⟶ K n
  ι : ∀ n, Fin n → (B ⟶ K n)
  w : ∀ n i, f ≫ ι n i = a n
  δ : ∀ n, Fin (n + 1) → (K n ⟶ K (n + 1))
  aδ : ∀ n k, a n ≫ δ n k = a (n + 1)
  ιδ : ∀ n k i, ι n i ≫ δ n k = ι (n + 1) (k.succAbove i)
  rel : ∀ n (k : Fin (n + 2)) (i : Fin (n + 1)), δ n (i.predAbove k) ≫ δ (n + 1) (k.succAbove i) = δ n i ≫ δ (n + 1) k
  iso0 : IsIso (a 0)
  iso1 : IsIso (ι 1 0)
  univ : ∀ n (t : T) (x : A ⟶ j.obj t) (y : Fin n → (B ⟶ j.obj t)), (∀ i, f ≫ y i = x) →
    ∃! z : K n ⟶ j.obj t, a n ≫ z = x ∧ ∀ i, ι n i ≫ z = y i

def Powers.dK {A : C} (P : Powers j A) (F : C ⥤ ModuleCat.{w} R) (n : ℕ) : F.obj (P.K n) →ₗ[R] F.obj (P.K (n + 1)) :=
  ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • (F.map (P.δ n k)).hom

def Powers.Good {A : C} (P : Powers j A) (F : C ⥤ ModuleCat.{w} R) (I : Ideal R) : Prop :=
  (∀ (t : T) (x : A ⟶ j.obj t), ∃ y : P.B ⟶ j.obj t, P.f ≫ y = x) ∧
  (∀ s ∈ I, InjUpTo s (P.dK j F 0) ∧ ∀ n, ExactUpTo s (P.dK j F n) (P.dK j F (n + 1))) ∧
  ∃ (t₀ : T) (g : P.B ⟶ j.obj t₀), (∀ (t : T) (y : P.B ⟶ j.obj t), ∃! φ : t₀ ⟶ t, g ≫ j.map φ = y) ∧ Almost I (F.map g).hom

end Ind

end CrystallineSemistableComparison.CH

namespace CrystallineSemistableComparison

variable (R : Type) [CommRing R] (G : Type) [TopologicalSpace G] (M : Type w) [AddCommGroup M] [Module R M]

abbrev lcCos : Cos.{w} R where
  X n := LocallyConstant (Fin (n + 1) → G) M
  δ n i := LocallyConstant.comapₗ R ⟨fun x k => x (i.succAbove k), by fun_prop⟩
  rel n j i f := by
    ext x
    exact congrArg f (funext fun k => congrArg x (Fin.succAbove_succAbove_succAbove_predAbove j i k))

variable {R G M} [AddCommGroup G]

def eqv (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) (n : ℕ) : Submodule R ((lcCos R G M).cx.X n) where
  carrier := {f | ∀ g ∈ S, ∀ x : Fin (n + 1) → G, f (fun i => g + x i) = ρ (Multiplicative.ofAdd g) (f x)}
  add_mem' {a b} ha hb g hg x := by
    change a _ + b _ = ρ _ (a x + b x)
    rw [ha g hg, hb g hg, map_add]
  zero_mem' g hg x := (map_zero _).symm
  smul_mem' c a ha g hg x := by
    change c • a _ = ρ _ (c • a x)
    rw [ha g hg, map_smul]

theorem lc_d_apply (n : ℕ) (f : LocallyConstant (Fin (n + 1) → G) M) (x : Fin (n + 2) → G) :
    (lcCos R G M).d n f x = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • f fun k => x (i.succAbove k) := by
  rw [Cos.d_apply]
  exact (map_sum (LocallyConstant.evalₗ R x) _ _).trans (Finset.sum_congr rfl fun i _ => map_zsmul _ _ _)

abbrev grpCx (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) : Cx.{w} R :=
  (lcCos R G M).cx.sub (eqv ρ S) fun n f hf g hg x => by
    change (lcCos R G M).d n f _ = ρ _ ((lcCos R G M).d n f x)
    rw [lc_d_apply, lc_d_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul]; exact congrArg _ (hf g hg _)

def grpAug (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) (N : Submodule R M)
    (h : ∀ g ∈ S, ∀ x ∈ N, ρ (Multiplicative.ofAdd g) x = x) : N →ₗ[R] (grpCx ρ S).X 0 where
  toFun x := ⟨LocallyConstant.const _ x.1, fun g hg _ => (h g hg x.1 x.2).symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end CrystallineSemistableComparison
