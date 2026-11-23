import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex
open scoped DirectSum TensorProduct

namespace GlobalTheory.EtC

variable {R : Type} [CommRing R]

def Loc (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Prop :=
  ∃ S : Sieve U, S ∈ Scheme.etaleTopology U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → P V g

abbrev sgl (F : Shv R) : Cx R := (CochainComplex.singleFunctor (Shv R) 0).obj F

def sglι (F : Shv R) : F ⟶ (sgl F).X 0 := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv

def resAug (F : Shv R) : sgl F ⟶ res R F := (injectiveResolution F).ι'

abbrev cpull {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ) : CohomologyClass L I n →+ CohomologyClass K I n :=
  cpre (Cocycle.ofHom f) I n n (zero_add n)

abbrev cpush (K : Cx R) {I J : Cx R} (f : I ⟶ J) (n : ℤ) : CohomologyClass K I n →+ CohomologyClass K J n :=
  cpost K (Cocycle.ofHom f) n n (add_zero n)

def Sx.face {E : Spc} {p : ℕ} {U : Scheme.{0}} (x : Sx E (p + 1) U) (i : Fin (p + 2)) : Sx E p U := (E.δ i).app (op U) x

def Sx.along {E : Spc} {p N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk N) : Sx E p U :=
  (E.map θ.op).app (op U) x

def Sx.res {E : Spc} {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) : Sx E p V := (E.obj (op (SimplexCategory.mk p))).map g.op x

def Sx.map {E E' : Spc} (f : E ⟶ E') {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) : Sx E' p U :=
  (f.app (op (SimplexCategory.mk p))).app (op U) x

abbrev Tens (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Type 1 :=
  ⨁ p : {p : ℤ × ℤ // p.1 + p.2 = w}, (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)

def Tens.res {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J V w :=
  DirectSum.lmap fun p => TensorProduct.map ((I.X p.1.1).obj.map g.op).hom ((J.X p.1.2).obj.map g.op).hom

def Pair.lift {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Sec (K.X w) U := by
  classical
  exact DirectSum.toModule _ _ _ fun p => TensorProduct.lift (μ.mul U p.1.1 p.1.2 w p.2)

def Pair.IsTensor {I J K : Cx R} (μ : Pair I J K) : Prop :=
  (∀ (U : Scheme.{0}) (w : ℤ) (y : Sec (K.X w) U), Loc U fun V g => ∃ x, μ.lift V w x = Sec.res g y) ∧
  ∀ (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w), μ.lift U w x = 0 → Loc U fun _ g => Tens.res g w x = 0

def Pair.Compat {I J K I' J' K' : Cx R} (μ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (m : K ⟶ K') : Prop :=
  ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map (m.f w) (μ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b)

def Pair.IsFlip {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K) : Prop :=
  ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    ν.mul U t s w (by omega) b a = (s * t).negOnePow • μ.mul U s t w h a b

def FlatS (M : Shv R) : Prop :=
  ∃ (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ M.obj),
    (∀ (U : Scheme.{0}) (y : Sec M U), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = Sec.res g y) ∧
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) ∧
    ∀ U : Scheme.{0}, Nonempty U → Module.Flat (ULift.{1} R) (P.obj (op U))

def IsTwRes (q : ℕ) (i : ℤ) (T : Cx (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U) : Prop :=
  T.IsStrictlyGE 0 ∧ ∃ ε : sgl (tw q i) ⟶ T, QuasiIso ε ∧
    ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map (ε.f 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) = e U ζ

def unitSec {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) : Sec Gm U := ofRings.sec unitsF U (ULift.up (Additive.ofMul u))

def secClass (F : Shv R) {X : Scheme.{0}} (s : Sec F X) : H R (sch.obj X) F 0 :=
  pick fun c => ∃ α : Cocycle _ _ 0, CohomologyClass.mk α = c ∧ ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s

def picClass {E : Spc} (L : E ⟶ ofCat (glCat 1)) : H ℤ E Gm 1 :=
  pick fun c => ∃ γ : Cocycle _ _ 1, CohomologyClass.mk γ = c ∧
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x))

def SemiMap.IsImage {S : Type} [CommRing S] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) {E : Spc} {n : ℤ}
    (α : Cochain ((chains S).obj E) I n) (β : Cochain ((chains R).obj E) J n) : Prop :=
  ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev β p s h U x = ρ.app U s (ev α p s h U x)

abbrev Pr (N : ℕ) : Type := Σ p r : ℕ, (SimplexCategory.mk p ⟶ SimplexCategory.mk N) × (SimplexCategory.mk r ⟶ SimplexCategory.mk N)

def Pr.push {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr M →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ fun z => ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩

def Pr.d₁ {N : ℕ} (z : Pr N) : Pr N →₀ ℤ :=
  Nat.casesOn (motive := fun p => (SimplexCategory.mk p ⟶ SimplexCategory.mk N) → (Pr N →₀ ℤ)) z.1 (fun _ => 0)
    (fun p a => ∑ i : Fin (p + 2), Finsupp.single ⟨p, z.2.1, SimplexCategory.δ i ≫ a, z.2.2.2⟩ ((-1) ^ (i : ℕ))) z.2.2.1

def Pr.d₂ {N : ℕ} (z : Pr N) : Pr N →₀ ℤ :=
  Nat.casesOn (motive := fun r => (SimplexCategory.mk r ⟶ SimplexCategory.mk N) → (Pr N →₀ ℤ)) z.2.1 (fun _ => 0)
    (fun r b => ∑ j : Fin (r + 2), Finsupp.single ⟨z.1, r, z.2.2.1, SimplexCategory.δ j ≫ b⟩ ((-1) ^ (j : ℕ))) z.2.2.2

def Pr.d (N : ℕ) : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr N →₀ ℤ) := Finsupp.linearCombination ℤ fun z => z.d₁ + (-1 : ℤ) ^ z.1 • z.d₂

def Pr.aw (N : ℕ) : Pr N →₀ ℤ := ∑ p : Fin (N + 1), Finsupp.single
  ⟨p, N - p, SimplexCategory.subinterval 0 p (by omega), SimplexCategory.subinterval p (N - p) (by omega)⟩ 1

def Pr.wa (N : ℕ) : Pr N →₀ ℤ := ∑ p : Fin (N + 1), Finsupp.single
  ⟨N - p, p, SimplexCategory.subinterval p (N - p) (by omega), SimplexCategory.subinterval 0 p (by omega)⟩ ((-1) ^ ((p : ℕ) * (N - p)))

def Pr.Deg {N : ℕ} (k : ℕ) (c : Pr N →₀ ℤ) : Prop := ∀ z ∈ c.support, z.1 + z.2.1 = k

def Pr.bd {N : ℕ} (c : Pr N →₀ ℤ) : Pr (N + 1) →₀ ℤ := ∑ i : Fin (N + 2), (-1 : ℤ) ^ (i : ℕ) • Pr.push (SimplexCategory.δ i) c

end GlobalTheory.EtC

end
