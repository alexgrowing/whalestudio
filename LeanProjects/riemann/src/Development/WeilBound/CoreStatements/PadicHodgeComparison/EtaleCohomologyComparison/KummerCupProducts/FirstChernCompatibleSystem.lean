import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsKumCoc

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

universe w w'

namespace CrystallineSemistableComparison.E

open CH

def CupLeib : Prop := ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C] (F₁ F₂ F₃ : C ⥤ ModuleCat.{w} R) (P : Pairing F₁ F₂ F₃)
  (p q n : ℕ) (h : p + q = n) (x : Cn F₁ p) (y : Cn F₂ q),
  d F₃ n (P.cupC h x y) = P.cupC (show (p + 1) + q = n + 1 by omega) (d F₁ p x) y +
    (-1 : ℤ) ^ p • P.cupC (show p + (q + 1) = n + 1 by omega) x (d F₂ q y)

def CupCls : Prop := ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C] (F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R) (P : Pairing F₁ F₂ F₃)
  (p q n : ℕ) (h : p + q = n) (x : Cn F₁ p) (y : Cn F₂ q) (hx : d F₁ p x = 0) (hy : d F₂ q y = 0),
  ∃ hz : d F₃ n (P.cupC h x y) = 0, P.cup h ((cx F₁).cls x hx) ((cx F₂).cls y hy) = (cx F₃).cls _ hz

def CupOne : Prop := ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) (p : ℕ) (x : H (modF A) p),
  (mulP A).cup (add_zero p) x (oneH A) = x

def MorCup : Prop := ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (C : Type 1) [Category.{0} C]
  (A : C ⥤ CommAlgCat.{0} R) (A' : C ⥤ CommAlgCat.{0} R') (m : Mor (modF A) (modF A') σ)
  (ρ : ∀ c, A.obj (m.G.obj c) →+* A'.obj c), (∀ c x, m.τ c x = ρ c x) →
  m.pull 0 (oneH A) = oneH A' ∧ ∀ (p q n : ℕ) (h : p + q = n) (x : H (modF A) p) (y : H (modF A) q),
    m.pull n ((mulP A).cup h x y) = (mulP A').cup h (m.pull p x) (m.pull q y)

def StAdd : Prop := ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (T : Res.{1} F)
  (j : ℕ) (z z' : Cn F j) (s k : ℕ) (x x' : Cn (T.K s) k), T.St z s k x → T.St z' s k x' →
  T.St (z + z') s k (x + x') ∧ T.St (z - z') s k (x - x')

def StCol : Prop := ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (T : Res.{1} F), T.Good →
  (∀ (k : ℕ) (z : Cn F k), d _ k (T.ιC k z) = T.ιC (k + 1) (d F k z)) ∧
  (∀ (s k : ℕ) (a : Cn (T.K s) k), d _ k (T.dvC s k a) = T.dvC s (k + 1) (d _ k a)) ∧
  (∀ k, Function.Injective (T.ιC k)) ∧ (∀ k, Function.Exact (T.ιC k) (T.dvC 0 k)) ∧
  ∀ s k, Function.Exact (T.dvC s k) (T.dvC (s + 1) k)

def StEx : Prop := ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (T : Res.{1} F), T.Good →
  ∀ (s k j : ℕ), s + k = j → ∀ x : Cn (T.K s) k, T.dvC s k x = 0 → d _ k x = 0 → ∃ z : Cn F j, d F j z = 0 ∧ T.St z s k x

def StUniq : Prop := ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (T : Res.{1} F), T.Good →
  ∀ (j : ℕ) (z : Cn F j) (s k : ℕ) (x : Cn (T.K s) k), T.St z s k x → T.BZ s k x → z ∈ (cx F).B j

def StTop : Prop := ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (T : Res.{1} F), T.Good →
  ∀ (j : ℕ) (z : Cn F j), d F j z = 0 → ∀ (s k : ℕ) (x : Cn (T.K s) k), T.St z s k x → T.dvC s k x = 0 ∧ d _ k x = 0

def EdgeUniq : Prop := ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (T : Res.{1} F), T.Good →
  ∀ (j : ℕ) (x x' : Cn (T.K j) 0) (h h' : H F j), T.Edge x h → T.Edge x' h' →
    T.Edge (x + x') (h + h') ∧ (T.VB j (x - x') → h = h')

def EdgeMap : Prop := ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (C C' : Type 1) [Category.{0} C] [Category.{0} C']
  (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R') (T : Res.{1} F) (T' : Res.{1} F') (m : Mor F F' σ) (n : ResMor T T' m)
  (j : ℕ) (x : Cn (T.K j) 0) (h : H F j), T.Edge x h → T'.Edge (n.pullC j 0 x) (m.pull j h)

def StCupA : Prop := ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C] (F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R)
  (T₁ : Res.{1} F₁) (T₂ : Res.{1} F₂) (T₃ : Res.{1} F₃) (P : Pairing F₁ F₂ F₃) (μ : ResPair T₁ T₂ T₃ P), T₁.Good → T₂.Good →
  ∀ (i t n : ℕ) (z : Cn F₁ i) (y : Cn (T₂.K t) 0) (u : Cn F₃ n), T₂.dvC t 0 y = 0 → d _ 0 y = 0 →
  T₃.St u t i ((μ.μ 0 t t (zero_add t)).cupC (add_zero i) (T₁.ιC i z) y) →
  ∀ (s k r : ℕ) (h : s + t = r) (x : Cn (T₁.K s) k), T₁.St z s k x → T₃.St u r k ((μ.μ s t r h).cupC (add_zero k) x y)

def StCupB : Prop := ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C] (F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R)
  (T₁ : Res.{1} F₁) (T₂ : Res.{1} F₂) (T₃ : Res.{1} F₃) (P : Pairing F₁ F₂ F₃) (μ : ResPair T₁ T₂ T₃ P), T₁.Good → T₂.Good →
  ∀ (i j n : ℕ) (hn : i + j = n) (z : Cn F₁ i) (z' : Cn F₂ j), d F₁ i z = 0 →
  ∀ (t k r : ℕ) (h : i + k = r) (y : Cn (T₂.K t) k), T₂.St z' t k y →
    T₃.St (P.cupC hn z z') t r ((μ.μ 0 t t (zero_add t)).cupC h (T₁.ιC i z) y)

def EdgeCup : Prop := ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C] (F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R)
  (T₁ : Res.{1} F₁) (T₂ : Res.{1} F₂) (T₃ : Res.{1} F₃) (P : Pairing F₁ F₂ F₃) (μ : ResPair T₁ T₂ T₃ P), T₁.Good → T₂.Good →
  ∀ (i j n : ℕ) (hn : i + j = n) (x : Cn (T₁.K i) 0) (y : Cn (T₂.K j) 0) (a : H F₁ i) (b : H F₂ j), T₁.Edge x a → T₂.Edge y b →
    T₃.Edge ((μ.μ i j n hn).cupC (add_zero 0) x y) (P.cup hn a b)

open GlobalTheory.EtC

def EvExt : Prop := ∀ (R : Type) [CommRing R] (E : Spc) (I : GlobalTheory.EtC.Cx R) (n : ℤ) (α β : Cochain ((chains R).obj E) I n),
  ((∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev α p s h U x = ev β p s h U x) → α = β) ∧
  ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U),
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0

def EvNat : Prop := ∀ (R : Type) [CommRing R] (E : Spc) (I : GlobalTheory.EtC.Cx R) (n : ℤ) (α : Cochain ((chains R).obj E) I n)
  (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}),
  (∀ (V : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), ev α p s h V (Sx.res g x) = Sec.res g (ev α p s h U x)) ∧
  ∀ (E' : Spc) (f : E' ⟶ E) (x : Sx E' p U),
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (Sx.map f x)

def EvMk : Prop := ∀ (R : Type) [CommRing R] (E : Spc) (I : GlobalTheory.EtC.Cx R) (n : ℤ)
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (U V : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), a p s h V (Sx.res g x) = Sec.res g (a p s h U x)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def EvDel : Prop := ∀ (R : Type) [CommRing R] (E : Spc) (I : GlobalTheory.EtC.Cx R) (n m : ℤ) (hm : n + 1 = m) (β : Cochain ((chains R).obj E) I n)
  (U : Scheme.{0}),
  (∀ x : Sx E 0 U, ev (δ n m β) 0 m (by simp) U x = Sec.map (I.d n m) (ev β 0 n (by simp) U x)) ∧
  ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -(p : ℤ) + n = t) (x : Sx E (p + 1) U),
    ev (δ n m β) (p + 1) t (by push_cast; omega) U x = Sec.map (I.d s t) (ev β (p + 1) s hs U x) +
      m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev β p t ht U (x.face i)

def IsConc {R : Type} [CommRing R] {I : GlobalTheory.EtC.Cx R} {X : Scheme.{0}} {n : ℤ} (α : Cochain ((chains R).obj (sch.obj X)) I n)
    (a : Sec (I.X n) X) : Prop :=
  (∀ (U : Scheme.{0}) (x : U ⟶ X), ev α 0 n (by simp) U x = Sec.res x a) ∧
  ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (x : U ⟶ X), ev α (p + 1) s h U x = 0

def RepBasic : Prop := ∀ (R : Type) [CommRing R] (I : GlobalTheory.EtC.Cx R) (X : Scheme.{0}) (n : ℤ),
  (∀ x : CohomologyClass ((chains R).obj (sch.obj X)) I n, ∃ a, Rep x a) ∧
  (∀ (x : CohomologyClass ((chains R).obj (sch.obj X)) I n) a, Rep x a → ∀ m, Sec.map (I.d n m) a = 0) ∧
  (∀ (x y : CohomologyClass ((chains R).obj (sch.obj X)) I n) a b, Rep x a → Rep y b → Rep (x + y) (a + b) ∧ Rep (x - y) (a - b)) ∧
  (∀ a, Rep (0 : CohomologyClass ((chains R).obj (sch.obj X)) I n) a → ∀ k, k + 1 = n → ∃ b, Sec.map (I.d k n) b = a) ∧
  ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (x : CohomologyClass ((chains R).obj (sch.obj X)) I n) a, Rep x a →
    Rep (cpull ((chains R).map (sch.map f)) I n x) (Sec.res f a)

def RepConc : Prop := ∀ (R : Type) [CommRing R] (I : GlobalTheory.EtC.Cx R) (X : Scheme.{0}) (n : ℤ) (a : Sec (I.X n) X),
  (Sec.map (I.d n (n + 1)) a = 0 → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n, IsConc α.1 a) ∧
  (∀ x, Rep x a → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n, IsConc α.1 a ∧ CohomologyClass.mk α = x) ∧
  ∀ x y : CohomologyClass ((chains R).obj (sch.obj X)) I n, Rep x a → Rep y a → x = y

def RepCup : Prop := ∀ (R : Type) [CommRing R] (I J K : GlobalTheory.EtC.Cx R) (μ : Pair I J K) (X : Scheme.{0}) (n m k : ℤ) (h : n + m = k)
  (x : CohomologyClass ((chains R).obj (sch.obj X)) I n) (y : CohomologyClass ((chains R).obj (sch.obj X)) J m) a b,
  Rep x a → Rep y b → Rep (μ.cup (sch.obj X) h x y) (μ.mul X n m k h a b)

def RepOp : Prop := InOp → ∀ (S R : Type) [CommRing S] [CommRing R] (I : GlobalTheory.EtC.Cx S) (J : GlobalTheory.EtC.Cx R) (ρ : SemiMap I J)
  (X : Scheme.{0}) (n : ℤ) (x : CohomologyClass ((chains S).obj (sch.obj X)) I n) a,
  Rep x a → Rep (ρ.op.app (sch.obj X) n x) (ρ.app X n a)

def RepRoot : Prop := ∀ (q : ℕ) (i : ℤ) (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)),
  (∀ (V : Scheme.{0}) (g : V ⟶ X), Sec.res g (twGen i ζ) = twGen i (primRes g ζ) ∧ Sec.res g (resGen i ζ) = resGen i (primRes g ζ)) ∧
  Rep (rootClass i ζ) (resGen i ζ)

def RedRoot : Prop := InOp → InRed → ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ) (X : Scheme.{0}) (ζ : Prim Q Γ(X, ⊤)) (ξ : Prim q Γ(X, ⊤)),
  ξ.1 = ζ.1 ^ (Q / q) → red Q q _ 0 i (rootClass i ζ) = rootClass i ξ

def LcCover : Prop := ∀ (U : Scheme.{0}) (ι : Type) (f : LocallyConstant U ι), ∃ (W : ι → Scheme.{0}) (j : ∀ a, W a ⟶ U),
  (∀ a (v : W a), f (j a v) = a) ∧
  (∀ (V : Scheme.{0}) (g : V ⟶ U) (a : ι), (∀ v : V, f (g v) = a) → ∃ k : V ⟶ W a, k ≫ j a = g) ∧
  (∀ x y : Γ(U, ⊤), (∀ a, (j a).appTop.hom x = (j a).appTop.hom y) → x = y) ∧
  ∀ (R : Type) [CommRing R] (G : Shv R) (x : ∀ a, Sec G (W a)), ∃! y : Sec G U, ∀ a, Sec.res (j a) y = x a

def LocSplit : Prop := ∀ (U : Scheme.{0}), Splits U → ∀ P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop, Loc U P →
  ∃ (ι : Type) (f : LocallyConstant U ι), ∀ (V : Scheme.{0}) (g : V ⟶ U) (a : ι), (∀ v : V, f (g v) = a) → P V g

def ResLoc : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (s : ℕ) (U : Scheme.{0}) (x : Sec ((res R F).X ((s + 1 : ℕ) : ℤ)) U),
  Sec.map ((res R F).d ((s + 1 : ℕ) : ℤ) ((s + 1 + 1 : ℕ) : ℤ)) x = 0 →
  Loc U fun V g => ∃ y : Sec ((res R F).X (s : ℤ)) V, Sec.map ((res R F).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) y = Sec.res g x

def ResZero : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}),
  Function.Injective (Sec.map (resι R F) (U := U)) ∧
  (∀ x : Sec ((res R F).X 0) U, Sec.map ((res R F).d 0 1) x = 0 ↔ ∃ y, Sec.map (resι R F) y = x) ∧
  ∀ s : ℤ, s < 0 → Subsingleton (Sec ((res R F).X s) U)

def ResSplit : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), Splits U → ∀ s : ℕ,
  Function.Exact (Sec.map ((res R F).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) (U := U))
    (Sec.map ((res R F).d ((s + 1 : ℕ) : ℤ) ((s + 1 + 1 : ℕ) : ℤ)) (U := U))

def PrimAlg : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ : Prim q A),
  ζ.1 ^ q = 1 ∧ (∀ a b : ZMod q, a ≠ b → IsUnit (ζ.1 ^ a.val - ζ.1 ^ b.val)) ∧
  (∀ r : A, r ^ q - 1 = ∏ a : ZMod q, (r - ζ.1 ^ a.val)) ∧
  ∀ r : A, Polynomial.aeval r (Polynomial.cyclotomic q ℤ) = ∏ a : (ZMod q)ˣ, (r - ζ.1 ^ (a : ZMod q).val)

def RootPow : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
  (∀ r : Γ(U, ⊤), r ^ q = 1 → ∃ f, IsPow ζ f r) ∧ ∀ ξ : Prim q Γ(U, ⊤), ∃ f, IsPow ζ f ξ.1 ∧ ∀ u, IsUnit (f u)

def TwZero : Prop := InGen → ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)), twGen 0 ζ = twGen 0 ξ

def KapSpec : Prop := ∀ (q : ℕ) (i : ℤ) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (f : LocallyConstant U (ZMod q)),
  IsLC i ζ f (kap i ζ f) ∧ (∀ x, IsLC i ζ f x → x = kap i ζ f) ∧
  ∀ (V : Scheme.{0}) (g : V ⟶ U), Sec.res g (kap i ζ f) = kap i (primRes g ζ) (lcRes q g f)

def KapBij : Prop := InGen → ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Function.Bijective (kap i ζ)

def KapMul : Prop := InTw → ∀ (q : ℕ) [NeZero q] (i j : ℤ) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (f g : LocallyConstant U (ZMod q)),
  (twPair q i j).mul U 0 0 0 (add_zero 0) (Sec.map (resι _ _) (kap i ζ f)) (Sec.map (resι _ _) (kap j ζ g)) =
    Sec.map (resι _ _) (kap (i + j) ζ (f * g))

def KapRed : Prop := InRed → ∀ (Q q : ℕ) [NeZero Q] [NeZero q] (h : q ∣ Q) (i : ℤ) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)),
  ξ.1 = ζ.1 ^ (Q / q) → ∀ f : LocallyConstant U (ZMod Q),
  (redMap Q q i).app U 0 (Sec.map (resι _ _) (kap i ζ f)) = Sec.map (resι _ _) (kap i ξ (f.map (ZMod.castHom h (ZMod q))))

def KumPow : Prop := InKum → ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (f : LocallyConstant U (ZMod q))
  (r v : (Γ(U, ⊤))ˣ), IsPow ζ f r.val → kumT q U (r * v) = kumT q U v + Sec.map (resι _ _) (kap 1 ζ f)

def ResGood : Prop := InGen → ∀ (q : ℕ) [NeZero q] (C : Type 1) [Category.{0} C] (P : Probe C q) (i : ℤ), (P.res i).Good

def EtSpec : Prop := InGen → ∀ (q : ℕ) [NeZero q] (C : Type 1) [Category.{0} C] (P : Probe C q) (X : Scheme.{0}) (Y : P.Pts X)
  (i : ℤ) (j : ℕ) (x : Ht q (sch.obj X) j i), (∀ a, Rep x a → (P.res i).Edge (Y.glob i j a) (Y.et i j x)) ∧
    ∀ h, Y.IsEt i j x h → h = Y.et i j x

def EtNat : Prop := InGen → ∀ (q : ℕ) [NeZero q] (C C' : Type 1) [Category.{0} C] [Category.{0} C'] (P : Probe C q) (P' : Probe C' q)
  (X X' : Scheme.{0}) (Y : P.Pts X) (Y' : P'.Pts X') (u : X' ⟶ X) (m : Mor P.L P'.L (RingHom.id ℤ))
  (g : ∀ c : C', P'.U c ⟶ P.U (m.G.obj c)),
  (∀ {c c' : C'} (φ : c ⟶ c'), g c' ≫ (P.S.map (m.G.map φ)).unop = (P'.S.map φ).unop ≫ g c) →
  (∀ c f, m.τ c f = lcRes q (g c) f) → (∀ c, Y'.y c ≫ u = g c ≫ Y.y (m.G.obj c)) →
  ∀ i : ℤ, (i = 0 ∨ ∀ c, primRes (g c) (P.ζ _) = P'.ζ c) → ∀ (j : ℕ) (x : Ht q (sch.obj X) j i),
    m.pull j (Y.et i j x) = Y'.et i j (pull _ (sch.map u) _ j x)

def EtRed : Prop := InGen → InRed → InOp → ∀ (Q q : ℕ) [NeZero Q] [NeZero q] (h : q ∣ Q) (C C' : Type 1) [Category.{0} C] [Category.{0} C']
  (P : Probe C Q) (P' : Probe C' q) (X : Scheme.{0}) (Y : P.Pts X) (Y' : P'.Pts X) (m : Mor P.L P'.L (RingHom.id ℤ))
  (g : ∀ c : C', P'.U c ⟶ P.U (m.G.obj c)),
  (∀ {c c' : C'} (φ : c ⟶ c'), g c' ≫ (P.S.map (m.G.map φ)).unop = (P'.S.map φ).unop ≫ g c) →
  (∀ c (f : LocallyConstant (P.U (m.G.obj c)) (ZMod Q)), m.τ c f = lcRes q (g c) (f.map (ZMod.castHom h (ZMod q)))) →
  (∀ c, Y'.y c = g c ≫ Y.y (m.G.obj c)) → (∀ c, (P'.ζ c).1 = (primRes (g c) (P.ζ _)).1 ^ (Q / q)) →
  ∀ (i : ℤ) (j : ℕ) (x : Ht Q (sch.obj X) j i), m.pull j (Y.et i j x) = Y'.et i j (red Q q _ j i x)

def EtCup : Prop := InGen → InTw → ∀ (q : ℕ) [NeZero q] (C : Type 1) [Category.{0} C] (P : Probe C q) (X : Scheme.{0}) (Y : P.Pts X)
  (i i' i'' : ℤ) (hi : i + i' = i'') (j j' j'' : ℕ) (hj : j + j' = j'') (x : Ht q (sch.obj X) j i) (y : Ht q (sch.obj X) j' i'),
  Y.et i'' j'' ((cup q x y).cast (by omega) hi) = (mulP (lcF P.S q)).cup hj (Y.et i j x) (Y.et i' j' y)

def EtRoot : Prop := InGen → ∀ (q : ℕ) [NeZero q] (C : Type 1) [Category.{0} C] (P : Probe C q) (X : Scheme.{0}) (Y : P.Pts X)
  (ζ : Prim q Γ(X, ⊤)), (∀ c, primRes (Y.y c) ζ = P.ζ c) → ∀ i : ℤ, Y.et i 0 (rootClass i ζ) = oneH (lcF P.S q)

def CechPt : Prop := ∀ (Y X : Scheme.{0}) (f : Y ⟶ X) (k : ℕ) (U : Scheme.{0}),
  (∀ z : Sx (cech f) k U, ∃ x y h, z = cechPt f k x y h) ∧
  (∀ x y h x' y' h', cechPt f k (U := U) x y h = cechPt f k x' y' h' → y = y') ∧
  ∀ (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ Y)) (h : ∀ i, y i ≫ f = x),
    Sx.map (cechAug f) (cechPt f k x y h) = x ∧
    (∀ (V : Scheme.{0}) (g : V ⟶ U), Sx.res g (cechPt f k x y h) =
      cechPt f k (g ≫ x) (fun i => g ≫ y i) (fun i => by rw [Category.assoc, h i])) ∧
    ∀ (p : ℕ) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk k),
      Sx.along (cechPt f k x y h) θ = cechPt f p x (fun i => y (θ.toOrderHom i)) (fun i => h _)

def LineMap : Prop := ∀ (X : Scheme.{0}) (D : LineData X), ∃ L, D.IsMap L

def FirstChernCompatibleSystem : Prop := A2 → A11 → ∀ (l : ℕ) [Fact l.Prime] (Y X : Scheme.{0}) (f : Y ⟶ X) [Smooth f] [Surjective f],
  IsUnit (l : Γ(X, ⊤)) → ∀ L : cech f ⟶ ofCat (glCat 1), (∀ n, GlobalTheory.EtC.Inv (l ^ n) (cech f)) ∧
    ∃ x : Hl l (sch.obj X) 2 1, ∀ n, pull _ (cechAug f) _ 2 (x.1 n) = c1 (l ^ n) L

def FirstChernCoboundary : Prop := InC1 → ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (D : LineData X) (L : cech D.f ⟶ ofCat (glCat 1)), D.IsMap L →
  GlobalTheory.EtC.Inv q (cech D.f) → ∀ x : Ht q (sch.obj X) 2 1, pull _ (cechAug D.f) _ 2 x = c1 q L →
  ∃ (a : Sec ((res _ (tw q 1)).X 2) X) (η : ∀ V : Scheme.{0}, (V ⟶ D.Y) → Sec ((res _ (tw q 1)).X 1) V)
    (θ : ∀ (V : Scheme.{0}) (b c : V ⟶ D.Y), b ≫ D.f = c ≫ D.f → Sec ((res _ (tw q 1)).X 0) V), Rep x a ∧
    (∀ (V V' : Scheme.{0}) (g : V' ⟶ V) (b : V ⟶ D.Y), Sec.res g (η V b) = η V' (g ≫ b)) ∧
    (∀ (V V' : Scheme.{0}) (g : V' ⟶ V) (b c : V ⟶ D.Y) h h', Sec.res g (θ V b c h) = θ V' (g ≫ b) (g ≫ c) h') ∧
    (∀ (V : Scheme.{0}) (b : V ⟶ D.Y), Sec.map ((res _ (tw q 1)).d 1 2) (η V b) = Sec.res (b ≫ D.f) a) ∧
    (∀ (V : Scheme.{0}) (b c : V ⟶ D.Y) h (v : (Γ(V, ⊤))ˣ), v ^ q = D.u b c h →
      η V c - η V b = Sec.map ((res _ (tw q 1)).d 0 1) (θ V b c h - kumT q V v)) ∧
    ∀ (V : Scheme.{0}) (b c e : V ⟶ D.Y) h h' (v w : (Γ(V, ⊤))ˣ), v ^ q = D.u b c h → w ^ q = D.u c e h' →
      θ V c e h' - θ V b e (h.trans h') + θ V b c h = kumT q V v + kumT q V w - kumT q V (v * w)

def EtaleFirstChernKummer : Prop := InGen → InKum → InC1 → ∀ (q : ℕ) [NeZero q] (C : Type 1) [Category.{0} C] (P : Probe C q) (X : Scheme.{0})
  (Y : P.Pts X) (D : LineData X) (L : cech D.f ⟶ ofCat (glCat 1)), D.IsMap L → GlobalTheory.EtC.Inv q (cech D.f) →
  ∀ x : Ht q (sch.obj X) 2 1, pull _ (cechAug D.f) _ 2 x = c1 q L → ∀ z : Cn P.L 2, IsKumCoc Y D z →
    ∃ hz : d P.L 2 z = 0, Y.et 1 2 x = (cx P.L).cls z hz

end CrystallineSemistableComparison.E
