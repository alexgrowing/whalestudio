import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

universe w w' w₁ w₁' u v u' v'

namespace CrystallineSemistableComparison.E

open CH

section Abstract

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

structure Res (F : C ⥤ ModuleCat.{w'} R) where
  K : ℕ → (C ⥤ ModuleCat.{w} R)
  ι : ∀ c : C, F.obj c →ₗ[R] (K 0).obj c
  dv : ∀ (s : ℕ) (c : C), (K s).obj c →ₗ[R] (K (s + 1)).obj c

namespace Res

variable {F : C ⥤ ModuleCat.{w'} R} (T : Res.{w} F)

structure Good : Prop where
  ι_nat : ∀ {c c' : C} (φ : c ⟶ c') (x : F.obj c), T.ι c' ((F.map φ).hom x) = ((T.K 0).map φ).hom (T.ι c x)
  dv_nat : ∀ (s : ℕ) {c c' : C} (φ : c ⟶ c') (x : (T.K s).obj c),
    T.dv s c' (((T.K s).map φ).hom x) = ((T.K (s + 1)).map φ).hom (T.dv s c x)
  inj : ∀ c, Function.Injective (T.ι c)
  ex0 : ∀ c, Function.Exact (T.ι c) (T.dv 0 c)
  ex : ∀ s c, Function.Exact (T.dv s c) (T.dv (s + 1) c)

def ιC (k : ℕ) : Cn F k →ₗ[R] Cn (T.K 0) k where
  toFun z s := T.ι _ (z s)
  map_add' _ _ := funext fun _ => map_add _ _ _
  map_smul' _ _ := funext fun _ => map_smul _ _ _

def dvC (s k : ℕ) : Cn (T.K s) k →ₗ[R] Cn (T.K (s + 1)) k where
  toFun x t := T.dv s _ (x t)
  map_add' _ _ := funext fun _ => map_add _ _ _
  map_smul' _ _ := funext fun _ => map_smul _ _ _

def St {j : ℕ} (z : Cn F j) : ∀ (s k : ℕ), Cn (T.K s) k → Prop
  | 0, k, x => ∃ h : j = k, T.ιC k (h ▸ z) = x
  | s + 1, k, x => ∃ a : Cn (T.K s) k, T.dvC s k a = x ∧ St z s (k + 1) ((-1 : ℤ) ^ k • d (T.K s) k a)

def BZ (s : ℕ) : ∀ k : ℕ, Cn (T.K s) k → Prop
  | 0, x => x = 0
  | k + 1, x => ∃ b : Cn (T.K s) k, T.dvC s k b = 0 ∧ d (T.K s) k b = x

def VB : ∀ s : ℕ, Cn (T.K s) 0 → Prop
  | 0, x => x = 0
  | s + 1, x => ∃ b : Cn (T.K s) 0, d (T.K s) 0 b = 0 ∧ T.dvC s 0 b = x

def Edge {j : ℕ} (x : Cn (T.K j) 0) (h : H F j) : Prop :=
  ∃ (z : Cn F j) (hz : d F j z = 0), T.St z j 0 x ∧ (cx F).cls z hz = h

end Res

variable {R' : Type} [CommRing R'] {C' : Type u'} [Category.{v'} C'] {σ : R →+* R'}

structure ResMor {F : C ⥤ ModuleCat.{w'} R} {F' : C' ⥤ ModuleCat.{w₁'} R'} (T : Res.{w} F) (T' : Res.{w₁} F') (m : Mor F F' σ) where
  τ : ∀ (s : ℕ) (c : C'), (T.K s).obj (m.G.obj c) →+ (T'.K s).obj c
  nat : ∀ (s : ℕ) {c c' : C'} (φ : c ⟶ c') (x : (T.K s).obj (m.G.obj c)),
    τ s c' (((T.K s).map (m.G.map φ)).hom x) = ((T'.K s).map φ).hom (τ s c x)
  ι : ∀ (c : C') (x : F.obj (m.G.obj c)), τ 0 c (T.ι _ x) = T'.ι c (m.τ c x)
  dv : ∀ (s : ℕ) (c : C') (x : (T.K s).obj (m.G.obj c)), τ (s + 1) c (T.dv s _ x) = T'.dv s c (τ s c x)

def ResMor.pullC {F : C ⥤ ModuleCat.{w'} R} {F' : C' ⥤ ModuleCat.{w₁'} R'} {T : Res.{w} F} {T' : Res.{w₁} F'} {m : Mor F F' σ}
    (n : ResMor T T' m) (s k : ℕ) (x : Cn (T.K s) k) : Cn (T'.K s) k := fun t => n.τ s _ (x (t ⋙ m.G))

structure ResPair {F₁ F₂ F₃ : C ⥤ ModuleCat.{w'} R} (T₁ : Res.{w} F₁) (T₂ : Res.{w} F₂) (T₃ : Res.{w} F₃) (P : Pairing F₁ F₂ F₃) where
  μ : ∀ s t r : ℕ, s + t = r → Pairing (T₁.K s) (T₂.K t) (T₃.K r)
  ι : ∀ (c : C) (x : F₁.obj c) (y : F₂.obj c), (μ 0 0 0 rfl).μ c (T₁.ι c x) (T₂.ι c y) = T₃.ι c (P.μ c x y)
  leib : ∀ (s t r : ℕ) (h : s + t = r) (c : C) (x : (T₁.K s).obj c) (y : (T₂.K t).obj c),
    T₃.dv r c ((μ s t r h).μ c x y) = (μ (s + 1) t (r + 1) (by omega)).μ c (T₁.dv s c x) y +
      (-1 : ℤ) ^ s • (μ s (t + 1) (r + 1) (by omega)).μ c x (T₂.dv t c y)

end Abstract

open GlobalTheory.EtC

def Splits (U : Scheme.{0}) : Prop := ∀ (Y : Scheme.{0}) (f : Y ⟶ U), Etale f → Surjective f → ∃ s : U ⟶ Y, s ≫ f = 𝟙 U

def Rep {R : Type} [CommRing R] {I : GlobalTheory.EtC.Cx R} {X : Scheme.{0}} {n : ℤ} (x : CohomologyClass ((chains R).obj (sch.obj X)) I n)
    (a : Sec (I.X n) X) : Prop :=
  ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n, CohomologyClass.mk α = x ∧ ev α.1 0 n (by simp) X (𝟙 X) = a

def primRes {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) : Prim q Γ(V, ⊤) := ζ.map g.appTop.hom

def IsLC {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (f : LocallyConstant U (ZMod q)) (x : Sec (tw q i) U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (a : ZMod q), (∀ v : V, f (g v) = a) →
    Sec.res g x = (ULift.up a : ULift.{1} (ZMod q)) • twGen i (primRes g ζ)

def IsPow {q : ℕ} {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (f : LocallyConstant U (ZMod q)) (r : Γ(U, ⊤)) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (a : ZMod q), (∀ v : V, f (g v) = a) → g.appTop.hom r = (primRes g ζ).1 ^ a.val

def kap {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) : LocallyConstant U (ZMod q) →+ Sec (tw q i) U :=
  pick fun κ => ∀ f, IsLC i ζ f (κ f)

def lcRes (q : ℕ) {V U : Scheme.{0}} (g : V ⟶ U) : LocallyConstant U (ZMod q) →+* LocallyConstant V (ZMod q) :=
  LocallyConstant.comapRingHom ⟨g, g.continuous⟩

variable {C : Type u} [Category.{v} C]

def secF {R : Type} [CommRing R] (S : C ⥤ Scheme.{0}ᵒᵖ) (G : Shv R) : C ⥤ ModuleCat.{1} ℤ where
  obj c := ModuleCat.of ℤ (Sec G (S.obj c).unop)
  map φ := ModuleCat.ofHom (G.obj.map (S.map φ)).hom.toAddMonoidHom.toIntLinearMap
  map_id c := by ext x; simp
  map_comp φ ψ := by ext x; simp

def lcF (S : C ⥤ Scheme.{0}ᵒᵖ) (q : ℕ) : C ⥤ CommAlgCat.{0} ℤ where
  obj c := CommAlgCat.of ℤ (LocallyConstant (S.obj c).unop (ZMod q))
  map φ := CommAlgCat.ofHom (lcRes q (S.map φ).unop).toIntAlgHom
  map_id c := by ext x y; simp [lcRes]
  map_comp φ ψ := by ext x y; simp [lcRes]

structure Probe (C : Type u) [Category.{v} C] (q : ℕ) where
  S : C ⥤ Scheme.{0}ᵒᵖ
  split : ∀ c, Splits (S.obj c).unop
  ζ : ∀ c, Prim q Γ((S.obj c).unop, ⊤)
  ζ_nat : ∀ {c c' : C} (φ : c ⟶ c'), primRes (S.map φ).unop (ζ c) = ζ c'

namespace Probe

variable {q : ℕ} (P : Probe C q)

abbrev U (c : C) : Scheme.{0} := (P.S.obj c).unop

abbrev L : C ⥤ ModuleCat.{0} ℤ := modF (lcF P.S q)

def res (i : ℤ) : Res.{1} P.L where
  K s := secF P.S ((GlobalTheory.EtC.res _ (tw q i)).X (s : ℤ))
  ι c := (((resι _ (tw q i)).hom.app (op (P.U c))).hom.toAddMonoidHom.comp (kap i (P.ζ c))).toIntLinearMap
  dv s c := (((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)).hom.app (op (P.U c))).hom.toAddMonoidHom.toIntLinearMap

structure Pts (X : Scheme.{0}) where
  y : ∀ c, P.U c ⟶ X
  nat : ∀ {c c' : C} (φ : c ⟶ c'), (P.S.map φ).unop ≫ y c = y c'

variable {P} {X : Scheme.{0}}

def Pts.glob (Y : P.Pts X) (i : ℤ) (j : ℕ) (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) : Cn ((P.res i).K j) 0 :=
  fun s => Sec.res (Y.y (s.obj (Fin.last 0))) a

def Pts.IsEt (Y : P.Pts X) (i : ℤ) (j : ℕ) (x : Ht q (sch.obj X) j i) (h : H P.L j) : Prop :=
  ∃ a, Rep x a ∧ (P.res i).Edge (Y.glob i j a) h

def Pts.et (Y : P.Pts X) (i : ℤ) (j : ℕ) : Ht q (sch.obj X) j i →+ H P.L j := pick fun e => ∀ x, Y.IsEt i j x (e x)

end Probe

structure LineData (X : Scheme.{0}) where
  Y : Scheme.{0}
  f : Y ⟶ X
  sm : Smooth f
  surj : Surjective f
  u : ∀ {V : Scheme.{0}} (a b : V ⟶ Y), a ≫ f = b ≫ f → (Γ(V, ⊤))ˣ
  nat : ∀ {V' V : Scheme.{0}} (g : V' ⟶ V) (a b : V ⟶ Y) (h : a ≫ f = b ≫ f),
    u (g ≫ a) (g ≫ b) (by rw [Category.assoc, h, Category.assoc]) = Units.map g.appTop.hom.toMonoidHom (u a b h)
  coc : ∀ {V : Scheme.{0}} (a b c : V ⟶ Y) (h : a ≫ f = b ≫ f) (h' : b ≫ f = c ≫ f), u a b h * u b c h' = u a c (h.trans h')

def LineData.IsMap {X : Scheme.{0}} (D : LineData X) (L : cech D.f ⟶ ofCat (glCat 1)) : Prop :=
  ∀ (V : Scheme.{0}) (x : V ⟶ X) (a : Fin 2 → (V ⟶ D.Y)) (h : ∀ i, a i ≫ D.f = x),
    lineUnit L (cechPt D.f 1 x a h) = D.u (a 0) (a 1) ((h 0).trans (h 1).symm)

structure IsKumCoc {q : ℕ} {P : Probe C q} {X : Scheme.{0}} (Y : P.Pts X) (D : LineData X) (z : Cn P.L 2) where
  p : ∀ c, P.U c ⟶ D.Y
  hp : ∀ c, p c ≫ D.f = Y.y c
  r : ∀ {c c' : C}, (c ⟶ c') → (Γ(P.U c', ⊤))ˣ
  hr : ∀ {c c' : C} (φ : c ⟶ c'), r φ ^ q = D.u ((P.S.map φ).unop ≫ p c) (p c') (by rw [Category.assoc, hp, hp, Y.nat])
  hz : ∀ s : ComposableArrows C 2, IsPow (P.ζ (s.obj (Fin.last 2))) (z s)
    (Units.val (Units.map (P.S.map (s.map' 1 2)).unop.appTop.hom.toMonoidHom (r (s.map' 0 1)) * r (s.map' 1 2) * (r (s.map' 0 2))⁻¹))

def InGen : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ),
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U),
    Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧
  (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧
  ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
    twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ

def InSch : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : GlobalTheory.EtC.Cx R) (m n k : ℤ), m + 1 = n → n + 1 = k →
  (∀ z : Sec (I.X n) X, Sec.map (I.d n k) z = 0 → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n,
    (∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 n (by simp) U x = Sec.res x z) ∧ ∀ (p : ℕ) s h U x, ev α.1 (p + 1) s h U x = 0) ∧
  ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n, Sec.map (I.d n k) (ev α.1 0 n (by simp) X (𝟙 X)) = 0 ∧
    (CohomologyClass.mk α = 0 ↔ ∃ y : Sec (I.X m) X, Sec.map (I.d m n) y = ev α.1 0 n (by simp) X (𝟙 X))

def InTw : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j)

def InRed : Prop := ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)),
  ξ.1 = ζ.1 ^ (Q / q) → (redMap Q q i).app U 0 (resGen i ζ) = resGen i ξ

def InOp : Prop := ∀ (S R : Type) [CommRing S] [CommRing R] (I : GlobalTheory.EtC.Cx S) (J : GlobalTheory.EtC.Cx R) (ρ : SemiMap I J) (E : Spc) (n : ℤ)
  (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n), ρ.IsImage α.1 β.1 →
    ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β

def InKum : Prop := ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)

def InC1 : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc) (L : E ⟶ ofCat (glCat 1)), GlobalTheory.EtC.Inv q E →
  ∃ γ : Cocycle _ _ 2, CohomologyClass.mk γ = c1 q L ∧
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ.1 1 1 (by simp) U x = Sec.map ((GlobalTheory.EtC.res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)

structure EtIn : Prop where
  a2 : A2
  a11 : A11
  gen : InGen
  sch : InSch
  tw : InTw
  red : InRed
  op : InOp
  kum : InKum
  c1 : InC1

end CrystallineSemistableComparison.E
