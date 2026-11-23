import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

def pick {α : Type*} [Zero α] (P : α → Prop) : α := by
  classical
  exact if h : ∃ a, P a then h.choose else 0

theorem pick_spec {α : Type*} [Zero α] {P : α → Prop} (h : ∃ a, P a) : P (pick P) := by
  unfold pick
  rw [dif_pos h]
  exact h.choose_spec

abbrev Sec.res {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) : Sec F V := (F.obj.map g.op).hom x

abbrev Sec.map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) : Sec G U := (φ.hom.app (op U)).hom x

section Twist

def Prim (q : ℕ) (A : Type) [CommRing A] : Type := {ζ : A // IsUnit (q : A) ∧ Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0}

def Prim.map {q : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (ζ : Prim q A) : Prim q B :=
  ⟨f ζ.1, by simpa using ζ.2.1.map f, by
    have h := Polynomial.aeval_algHom_apply f.toIntAlgHom ζ.1 (Polynomial.cyclotomic q ℤ)
    rw [ζ.2.2, map_zero] at h
    exact h⟩

def twRel (q : ℕ) (i : ℤ) (A : Type) [CommRing A] : Submodule (ULift.{1} (ZMod q)) (Prim q A →₀ ULift.{1} (ZMod q)) :=
  Submodule.span _ {x | ∃ (ζ ξ : Prim q A) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val ∧
    x = Finsupp.single ξ 1 - Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q))}

theorem twRel_le (q : ℕ) (i : ℤ) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    twRel q i A ≤ (twRel q i B).comap (Finsupp.lmapDomain _ _ (Prim.map f)) := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨ζ, ξ, a, hξ, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  refine Submodule.subset_span ⟨Prim.map f ζ, Prim.map f ξ, a, ?_, rfl⟩
  show f ξ.1 = f ζ.1 ^ _
  rw [hξ, map_pow]

def twF (q : ℕ) (i : ℤ) : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) where
  obj A := ModuleCat.of _ ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A)
  map f := ModuleCat.ofHom (Submodule.mapQ _ _ (Finsupp.lmapDomain _ _ (Prim.map f.hom)) (twRel_le q i f.hom))
  map_id A := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
    change Submodule.Quotient.mk (Finsupp.mapDomain id x) = Submodule.Quotient.mk x
    rw [Finsupp.mapDomain_id]
  map_comp f g := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
    change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.hom ∘ Prim.map f.hom) x) =
      Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.hom) (Finsupp.mapDomain (Prim.map f.hom) x))
    rw [Finsupp.mapDomain_comp]

def tw (q : ℕ) (i : ℤ) : Shv (ZMod q) := ofRings (ZMod q) (twF q i)

def twGen {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) : Sec (tw q i) U :=
  ofRings.sec (twF q i) U (Submodule.Quotient.mk (Finsupp.single ζ 1))

def resGen {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) : Sec ((res _ (tw q i)).X 0) U :=
  Sec.map (resι _ (tw q i)) (twGen i ζ)

abbrev Ht (q : ℕ) (E : Spc) (n i : ℤ) : Type 1 := H (ZMod q) E (tw q i) n

def Ht.cast {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i) : Ht q E n' i' := hn ▸ hi ▸ x

def Acyc (q : ℕ) (E : Spc) : Prop := ∀ n i, 0 < n → Subsingleton (Ht q E n i)

end Twist

section Cup
variable {R : Type} [CommRing R]

structure Pair (I J K : Cx R) where
  mul : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w → Sec (I.X s) U →ₗ[ULift.{1} R] Sec (J.X t) U →ₗ[ULift.{1} R] Sec (K.X w) U
  nat : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.res g (mul U s t w h a b) = mul V s t w h (Sec.res g a) (Sec.res g b)
  leibniz : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map (K.d w (w + 1)) (mul U s t w h a b) = mul U (s + 1) t (w + 1) (by omega) (Sec.map (I.d s (s + 1)) a) b +
      s.negOnePow • mul U s (t + 1) (w + 1) (by omega) a (Sec.map (J.d t (t + 1)) b)

instance (I J K : Cx R) : Zero (Pair I J K) :=
  ⟨⟨fun _ _ _ _ _ => 0, fun _ _ _ _ _ _ _ => by simp, fun _ _ _ _ _ _ _ => by simp⟩⟩

def Sx.sub {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) : Sx E l U :=
  (E.map (SimplexCategory.subinterval j l h).op).app (op U) x

def Pair.IsAW {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n)
    (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) : Prop :=
  ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx E N U), ev γ N w h U x =
    ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow • μ.mul U (-((p : ℕ) : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev α p _ rfl U (x.sub 0 p (by omega))) (ev β (N - p) _ rfl U (x.sub p (N - p) (by omega)))

def Pair.cup {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k) :
    CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k :=
  pick fun c => ∀ (α : Cocycle _ I n) (β : Cocycle _ J m) (γ : Cocycle _ K k), μ.IsAW hk α.1 β.1 γ.1 →
    c (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def IsTwPair {q : ℕ} {i j k : ℤ} (μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k))) : Prop :=
  ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), μ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ) = resGen k ζ

def twPair (q : ℕ) (i j : ℤ) : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j))) := pick IsTwPair

def cup (q : ℕ) {E : Spc} {n m i j : ℤ} : Ht q E n i →+ Ht q E m j →+ Ht q E (n + m) (i + j) := (twPair q i j).cup E rfl

def one (q : ℕ) (E : Spc) : Ht q E 0 0 :=
  pick fun c => ∃ α : Cocycle _ _ 0, CohomologyClass.mk α = c ∧
    ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ

def rootClass {q : ℕ} (i : ℤ) {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) : Ht q (sch.obj X) 0 i :=
  pick fun c => ∃ α : Cocycle _ _ 0, CohomologyClass.mk α = c ∧
    ∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 0 (by simp) U x = Sec.res x (resGen i ζ)

def cpow (q : ℕ) {E : Spc} (x : Ht q E 2 1) (k : ℕ) : Ht q E (2 * k) k :=
  Nat.rec (motive := fun k : ℕ => Ht q E (2 * k) k) ((one q E).cast (by simp) (by simp))
    (fun _ y => (cup q y x).cast (by push_cast; ring) (by push_cast; ring)) k

theorem cpow_zero (q : ℕ) {E : Spc} (x : Ht q E 2 1) : cpow q x 0 = (one q E).cast (by simp) (by simp) := rfl

theorem cpow_succ (q : ℕ) {E : Spc} (x : Ht q E 2 1) (k : ℕ) :
    cpow q x (k + 1) = (cup q (cpow q x k) x).cast (by push_cast; ring) (by push_cast; ring) := rfl

end Cup

section Kummer

def IsKum (q : ℕ) (t : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec ((res _ (tw q 1)).X 0) U) : Prop :=
  (∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) →
    Sec.res g (t U v) = t V (Units.map g.appTop.hom.toMonoidHom v)) ∧
  ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (v w : (Γ(U, ⊤))ˣ), (w : Γ(U, ⊤)) = ζ.1 * v → t U w = t U v + resGen 1 ζ

def kumT (q : ℕ) : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec ((res _ (tw q 1)).X 0) U := pick (IsKum q)

def kum (q : ℕ) {X : Scheme.{0}} (u : (Γ(X, ⊤))ˣ) : Ht q (sch.obj X) 1 1 :=
  pick fun c => ∃ γ : Cocycle _ _ 1, CohomologyClass.mk γ = c ∧
    (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
    ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
      ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def lineUnit {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 1 U) : (Γ(U, ⊤))ˣ :=
  Matrix.GeneralLinearGroup.det (glMat ((L.app (op (SimplexCategory.mk 1))).app (op U) x))

def c1 (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) : Ht q E 2 1 :=
  pick fun c => ∃ γ : Cocycle _ _ 2, CohomologyClass.mk γ = c ∧
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)

end Kummer

section Change
variable {S R : Type} [CommRing S] [CommRing R]

structure SemiMap (I : Cx S) (J : Cx R) where
  app : ∀ (U : Scheme.{0}) (s : ℤ), Sec (I.X s) U →+ Sec (J.X s) U
  nat : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (s : ℤ) (a : Sec (I.X s) U), Sec.res g (app U s a) = app V s (Sec.res g a)
  comm : ∀ (U : Scheme.{0}) (s t : ℤ) (a : Sec (I.X s) U), Sec.map (J.d s t) (app U s a) = app U t (Sec.map (I.d s t) a)

instance (I : Cx S) (J : Cx R) : Zero (SemiMap I J) := ⟨⟨fun _ _ => 0, fun _ _ _ => by simp, fun _ _ _ _ => by simp⟩⟩

structure NatOp (I : Cx S) (J : Cx R) where
  app : ∀ (E : Spc) (n : ℤ), CohomologyClass ((chains S).obj E) I n →+ CohomologyClass ((chains R).obj E) J n
  nat : ∀ {E E' : Spc} (f : E ⟶ E') (n : ℤ) (x : CohomologyClass ((chains S).obj E') I n),
    cpre (Cocycle.ofHom ((chains R).map f)) J n n (zero_add n) (app E' n x) =
      app E n (cpre (Cocycle.ofHom ((chains S).map f)) I n n (zero_add n) x)

instance (I : Cx S) (J : Cx R) : Zero (NatOp I J) := ⟨⟨fun _ _ => 0, fun _ _ _ => by simp⟩⟩

def SemiMap.op {I : Cx S} {J : Cx R} (ρ : SemiMap I J) : NatOp I J :=
  pick fun c => ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
    (∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev β.1 p s h U x = ρ.app U s (ev α.1 p s h U x)) →
    c.app E n (CohomologyClass.mk α) = CohomologyClass.mk β

def restrMap (φ : R →+* S) (F : Shv S) : SemiMap (res S F) (res R ((restr φ).obj F)) :=
  pick fun ρ => ∀ (U : Scheme.{0}) (a : Sec F U),
    ρ.app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)

def restrH (φ : R →+* S) (E : Spc) (F : Shv S) (n : ℤ) : H S E F n →+ H R E ((restr φ).obj F) n := (restrMap φ F).op.app E n

def redMap (Q q : ℕ) (i : ℤ) : SemiMap (res _ (tw Q i)) (res _ (tw q i)) :=
  pick fun ρ => ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) →
    ρ.app U 0 (resGen i ζ) = resGen i ξ

def red (Q q : ℕ) (E : Spc) (n i : ℤ) : Ht Q E n i →+ Ht q E n i := (redMap Q q i).op.app E n

theorem pull_red (Q q : ℕ) {E E' : Spc} (f : E ⟶ E') (n i : ℤ) (x : Ht Q E' n i) :
    pull _ f _ n (red Q q E' n i x) = red Q q E n i (pull _ f _ n x) :=
  (redMap Q q i).op.nat f n x

end Change

section Adic
variable (l : ℕ) [Fact l.Prime]

def HtL (k : ℕ) (E : Spc) (n i : ℤ) : Type 1 := Ht (l ^ k) E n i

instance (k : ℕ) (E : Spc) (n i : ℤ) : AddCommGroup (HtL l k E n i) := inferInstanceAs (AddCommGroup (Ht (l ^ k) E n i))

instance (k : ℕ) (E : Spc) (n i : ℤ) : Module ℤ_[l] (HtL l k E n i) :=
  Module.compHom (Ht (l ^ k) E n i) (PadicInt.toZModPow k)

theorem HtL.smul_eq (k k' : ℕ) (hk : k ≤ k') (E : Spc) (n i : ℤ) (r : ℤ_[l]) (x : HtL l k E n i) :
    r • x = (PadicInt.toZModPow k' r).val • x := by
  have h1 : PadicInt.toZModPow k r = ((PadicInt.toZModPow k' r).val : ZMod (l ^ k)) := by
    rw [← PadicInt.zmod_cast_comp_toZModPow k k' hk, RingHom.comp_apply, ZMod.castHom_apply, ZMod.cast_eq_val]
  change PadicInt.toZModPow k r • (show Ht (l ^ k) E n i from x) = _
  rw [h1, Nat.cast_smul_eq_nsmul]
  rfl

def HlSub (E : Spc) (n i : ℤ) : Submodule ℤ_[l] (∀ k, HtL l k E n i) where
  carrier := {x | ∀ k, red (l ^ (k + 1)) (l ^ k) E n i (x (k + 1)) = x k}
  zero_mem' k := map_zero _
  add_mem' {a b} ha hb k := (map_add (red (l ^ (k + 1)) (l ^ k) E n i) (a (k + 1)) (b (k + 1))).trans (congrArg₂ (· + ·) (ha k) (hb k))
  smul_mem' r x hx k := by
    change red (l ^ (k + 1)) (l ^ k) E n i (r • x (k + 1)) = r • x k
    rw [HtL.smul_eq l (k + 1) (k + 1) le_rfl, HtL.smul_eq l k (k + 1) (Nat.le_succ k), ← hx k]
    exact map_nsmul (red (l ^ (k + 1)) (l ^ k) E n i) _ _

abbrev Hl (E : Spc) (n i : ℤ) : Type 1 := HlSub l E n i

def pullHl {E E' : Spc} (f : E ⟶ E') (n i : ℤ) : Hl l E' n i →ₗ[ℤ_[l]] Hl l E n i where
  toFun x := ⟨fun k => pull _ f _ n (x.1 k), fun k => (pull_red _ _ f n i _).symm.trans (congrArg _ (x.2 k))⟩
  map_add' x y := Subtype.ext (funext fun k => map_add (pull _ f _ n) (x.1 k) (y.1 k))
  map_smul' r x := Subtype.ext (funext fun k => (pullL (ZMod (l ^ k)) f (tw (l ^ k) i) n).map_smul (PadicInt.toZModPow k r) (x.1 k))

theorem pullHl_id (E : Spc) (n i : ℤ) : pullHl l (𝟙 E) n i = LinearMap.id :=
  LinearMap.ext fun x => Subtype.ext (funext fun k => pull_id _ E _ n (x.1 k))

theorem pullHl_comp {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHl l (f ≫ g) n i = (pullHl l f n i).comp (pullHl l g n i) :=
  LinearMap.ext fun x => Subtype.ext (funext fun k => pull_comp _ f g _ n (x.1 k))

abbrev HQ (E : Spc) (n i : ℤ) : Type 1 := TensorProduct ℤ_[l] ℚ_[l] (Hl l E n i)

def pullHQ {E E' : Spc} (f : E ⟶ E') (n i : ℤ) : HQ l E' n i →ₗ[ℚ_[l]] HQ l E n i := (pullHl l f n i).baseChange ℚ_[l]

open GlobalTheory.Et
variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))

def galHl (n i : ℤ) : Representation ℤ_[l] (Ω ≃ₐ[k] Ω) (Hl l (sch.obj (geom Ω p)) n i) where
  toFun σ := pullHl l (sch.map (galMap Ω p σ)) n i
  map_one' := by rw [galMap_one, CategoryTheory.Functor.map_id, pullHl_id]; rfl
  map_mul' σ τ := by rw [galMap_mul, Functor.map_comp, pullHl_comp]; rfl

def galHQ (n i : ℤ) : Representation ℚ_[l] (Ω ≃ₐ[k] Ω) (HQ l (sch.obj (geom Ω p)) n i) where
  toFun σ := (galHl l Ω p n i σ).baseChange ℚ_[l]
  map_one' := by rw [map_one]; exact LinearMap.baseChange_id
  map_mul' σ τ := by rw [map_mul]; exact LinearMap.baseChange_comp _ _

end Adic

end GlobalTheory.EtC

end
