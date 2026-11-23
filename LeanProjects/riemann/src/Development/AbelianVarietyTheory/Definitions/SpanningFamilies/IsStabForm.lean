import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Dict

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ}

section Classical

variable (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

def pv (x : Frame X.Ψ r) (v : Fin r → E) : Fin g → ℂ := per X x v ∘ idx

def hx (x : Frame X.Ψ r) (z w : Fin g → ℂ) : ℂ :=
  (hMat X bas idx x *ᵥ z) ⬝ᵥ imInv X bas idx x *ᵥ star (hMat X bas idx x *ᵥ w)

def eps1 (w : E) (v : Fin r → E) : ℂ := cexp (Real.pi * I * ((EF X v (w • v) : ℚ) : ℂ))

def fock (x : Frame X.Ψ r) (k : ℕ) (a : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ) : (Fin g → ℂ) → ℂ := fun z =>
  cexp (-((k : ℂ) * Real.pi * hx X bas idx x (z + (1 / 2 : ℂ) • a) a)) * θ (z + a)

def IsTheta1 (w : E) (x : Frame X.Ψ r) (L : Lt E r) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  Differentiable ℂ θ ∧ ∀ v ∈ L, eps1 X w v • fock X bas idx x 1 (pv X idx x v) θ = θ

def MeanOne (x : Frame X.Ψ r) (L : Lt E r) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∃ (A : AddSubgroup (Fin g → ℂ)) (Fd : Set (Fin g → ℂ)), (∀ z, z ∈ A ↔ ∃ v ∈ L, z = pv X idx x v) ∧
    MeasureTheory.IsAddFundamentalDomain A Fd MeasureTheory.volume ∧
    (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hx X bas idx x z z).re)) / (MeasureTheory.volume Fd).toReal = 1

def hAct (h : Matrix (Fin n) (Fin n) E) (z : Fin n → Fin g → ℂ) : Fin n → Fin g → ℂ :=
  fun k i => ∑ k', rowType X (idx i) (h k k') * z k' i

def gphi {Q : Type} (w : E) (Λ : Lt E n) (L : Lt E r) (v : TF n g) (W : Q → ℂ)
    (Y : Q → Matrix (Fin n) (Fin r) E) : TF n g :=
  ∑ᶠ q, W q • heisG X bas (Y q) (projA X bas w (tens Λ L) v)

variable {X}

def datF (D : SW.Level X) (𝔐 : Ideal (𝓞 E)) (hn : r ≤ n) (y : Matrix (Fin n) (Fin r) E) : ℂ :=
  if h : (∃ k : D.J, D.Red (fun i => y (Fin.castLE hn i)) k) ∧
      ∀ k : Fin n, r ≤ (k : ℕ) → Cong X 𝔐 (y k) 0 then (D.lam h.1.choose : ℂˣ) else 0

def phiF (D : SW.Level X) (𝔐 : Ideal (𝓞 E)) (hn : r ≤ n) (v₀ : Lt E r → TF n g) (L : Lt E r) (Λ : Lt E n) :
    TF n g :=
  ∑ᶠ c : tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) ⧸
      (tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)).addSubgroupOf _,
    datF D 𝔐 hn (c.out : Matrix (Fin n) (Fin r) E) • heisG X bas (c.out : Matrix (Fin n) (Fin r) E)
      (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)))

variable (X)

structure IsStabForm (Δ : Subgroup (GL (Fin r) E)) (L : Lt E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ) : Prop where
  hol : DifferentiableOn ℂ Q X.dom
  bor : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x
  inv : ∀ ga ∈ Δ, mapL ga L = L → ∀ x ∈ X.dom, Q (lact ga x) = Q x
  bdd : ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la Q x ≤ C

def IsUnitFr (x : Frame X.Ψ r) : Prop := ∀ τ i, ‖dmin X.Gm x τ i‖ = 1

def HasPrinc (M : ℕ) : Prop :=
  ∀ ga : GL (Fin r) E, IsUStab X.Gm X.Λ ga →
    (∀ v ∈ X.Λ, ∃ u ∈ X.Λ, (ga : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • u) → ga ∈ X.Γ

def ChiOne (la : Wt X.Ψ r) : Prop := ∀ ga ∈ X.Γ, X.χ la ga = 1

end Classical

def castFr {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (x : Frame Ψ r) : Frame Ψ' r := fun τ => x ⟨τ.1, h ▸ τ.2⟩

structure SameSp (X X' : Data E r) : Prop where
  psi : X.Ψ = X'.Ψ
  gm : X.Gm = X'.Gm
  p0 : X.p0 = X'.p0
  xi : X.ξ0 = X'.ξ0
  ka : X.κ0 = X'.κ0

def holSub0 {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) : Submodule ℂ (FDSec X) :=
  holSub X la ⊓
    { carrier := {P | ∀ k, ∀ x ∉ (X k).dom, P k x = 0}
      add_mem' := fun hP hQ k x hx => by simp [hP k x hx, hQ k x hx]
      zero_mem' := fun _ _ _ => rfl
      smul_mem' := fun a P hP k x hx => by simp [hP k x hx] }

section Geo

variable {H : Host E} {Dw : Datum H}

structure IsMark (l : Geo.Tor.Level H) (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Prop where
  mem : ∀ a, mk a ∈ L
  inj : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), (∃ u ∈ L, mk a = l.M • u) → ∃ b, a = l.M • b
  surj : ∀ v ∈ Mfr l • L, ∃ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, v = mk a + l.M • u

structure IsDual (X : Data E r) (l : Geo.Tor.Level H) (ζ : ℂ) (L : Lt E r)
    (mk δ : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Prop where
  mem : ∀ a, δ a ∈ L
  pair : ∀ x, ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ζ ^ Dw.EF x (cSep l • a) =
    cexp (-(2 * Real.pi * I * ((EF X (δ x) (((l.M : E)⁻¹) • mk a) : ℚ) : ℂ)))

def IsRoots (l : Geo.Tor.Level H) (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)) (N : ℕ)
    (Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E) : Prop :=
  ∀ q b, (∃ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), Submodule.Quotient.mk a = q b ∧
      Y q b - ((l.M : E)⁻¹) • mk a ∈ L) ∧
    ∃ j : ℕ, ∀ s ∈ l.Mb ^ j, ∃ u ∈ L, s • Y q b = (2 * N) • u

def MarkOver (l l₂ : Geo.Tor.Level H) (L : Lt E r) (mk mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  ∀ a ∈ Mfr l₂ • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk₂ a = mk a + l.M • u

variable {l : Geo.Tor.Level H}

def wtX (c : Coeff l) (σ : c.F →+* ℂ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Wt X.Ψ r :=
  fun τ j => if X.p0 ≤ (j : ℕ) then
      (a (Function.invFun (relab c σ) τ.1, (j : ℕ) - X.p0) : ℤ) + ((n / 2 : ℕ) : ℤ)
    else -(a (Function.invFun (relab c σ) (conjEmb τ.1), X.p0 - 1 - (j : ℕ)) : ℤ) - ((n / 2 : ℕ) : ℤ)

structure Dic (Dw : Datum H) (c : Coeff l) (σ : c.F →+* ℂ) (X : Data E r) (g q0 n : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) where
  hr : X.p0 + q0 = r
  bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ
  idx : Fin g ≃ X.Ψ × Fin r
  sympl : IsSympl X bas
  e : Fin g ≃ Lt1 Dw
  eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)
  k : X.Ψ → Fin q0 → ℕ
  k' : X.Ψ → Fin X.p0 → ℕ
  per_eq : ∀ x v j, pv X idx x v j = perFr X x v (relab c σ (e j).1) (e j).2
  ty_eq : ∀ j, rowType X (idx j) = relab c σ (e j).1
  dir_eq : ∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)
  wt_eq : wtOf X hr k k' n = wtX c σ X a n
  mem : ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)),
    MvPolynomial.rename eL (MvPolynomial.map σ P) ∈ Harm.rowHighest ℂ k k'
  span : (Harm.rowHighest ℂ k k' : Submodule ℂ (Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))) ≤ Submodule.span ℂ
    ((fun P => MvPolynomial.rename eL (MvPolynomial.map σ P)) ''
      HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))

variable {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ]

structure AnFib (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)
    (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) where
  ex : (Fin g → ℂ) → (ptO Xo y.x ⟶ Xo.univ.t.G)
  ex_add : ∀ z w, ex (z + w) = ex z * ex w
  ex_onto : Function.Surjective ex
  ex_ker : ∀ z, ex z = 1 ↔ ∃ v ∈ L, z = pv X idx x v
  ex_lin : ∀ (a : 𝓞 E) z, ex (fun j => rowType X (idx j) (a : E) * z j) = ex z ≫ Xo.univ.t.act.act a
  hol : IsHolTo Set.univ (fun z => (ex z).left)
  der : ∀ ℓ : Lt1 Dw, IsDerivAt0 (fun z => (ex z).left) (Pi.single (e.symm ℓ) 1) (y.u ℓ.1 ℓ.2)
  fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ
  fr_hol : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}
  fr_ne : ∀ j z, ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0
  fr_g : ∀ j j' z, ⊤ ≤ (ex z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
    fr j z = valAt' (ex z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' z
  fr_0 : ∀ j, ⊤ ≤ (ex 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    fr j 0 = valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
      (Xo.univ.t.PP.rig.s (fun _ => j)).val
  χ : (Fin r → E) → ℂ
  χ_norm : ∀ v ∈ L, ‖χ v‖ = 1
  fr_per : ∀ v ∈ L, ∀ j z, ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    fr j z = χ v * cexp (Real.pi * hx X bas idx x z (pv X idx x v) +
      Real.pi / 2 * hx X bas idx x (pv X idx x v) (pv X idx x v)) * fr j (z + pv X idx x v)

variable {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}
  {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r} {L : Lt E r} {y : FrPt Xo c ℂ}

def AnFib.Reads (A : AnFib X bas idx e x L y) (k : ℤ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ j z (pt : Sp ℂ ⟶ Gx y.x), pt ≫ gxFst y.x = (A.ex z).left → pt ≫ gxSnd y.x = 𝟙 (Sp ℂ) →
    ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' pt ((LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)).U (fun _ => j)) (F.f (fun _ => j)) =
      θ z * A.fr j z ^ k

def AnFib.Marked (A : AnFib X bas idx e x L y) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo y.x a = A.ex (pv X idx x (((l.M : E)⁻¹) • mk a))

end Geo

def UnitC {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (d : DeltaDat Xo c n) : Prop :=
  ∀ (A : Algebra d.c₂.F ℂ) (y : @FrPt E _ _ _ H Dw d.l₂ d.Xo₂ d.c₂ ℂ _ A),
    ‖@evR E _ _ _ H Dw d.l₂ d.Xo₂ d.c₂ d.cδ ℂ _ A y‖ = 1

end

end GlobalTheory.Dict
