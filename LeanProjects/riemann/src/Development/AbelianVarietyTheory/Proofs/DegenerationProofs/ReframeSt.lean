import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CoeffFSumDerivEqFderiv

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Ex.Arch

section Values
variable {O : Type} [CommRing O] [StarRing O]

def lin (B : AnArc O) (la : B.La) (v : B.V) : ℂ := -(2 * Real.pi * Complex.I) * v.1 la.y + Real.pi * B.H v.2 la.l

def IsPrim (B : AnArc O) (w₀ : O) : Prop :=
  w₀ + star w₀ = 1 ∧ (∀ l, B.chi l = (-1) ^ B.Ef l (B.FLam w₀ l)) ∧ ∀ y, (B.psi y : ℂ) = eTwoPi (B.T y (w₀ • y))

def IsAbFrame (M : NumB ℂ) (B : AnArc O) (ex : (Fin B.gB → ℂ) → M.A) (fr : (Fin B.gB → ℂ) → ℂˣ)
    (th : (Fin B.gB → ℂ) → ℂ) : Prop :=
  (∀ z w, ex (z + w) = ex z * ex w) ∧ Function.Surjective ex ∧ (∀ z, ex z = 1 ↔ z ∈ B.abelian₂) ∧ fr 0 = 1 ∧
    (∀ (l : B.abelian₂) z, (fr z : ℂ) = B.ah l z * fr (z + l)) ∧
    (∀ x y z, M.θ (ex x) (ex y) (ex z) * fr (x + y) * fr (x + z) * fr (y + z) = fr (x + y + z) * fr x * fr y * fr z) ∧
    (∀ x, M.σ (ex x) * fr x = fr (-x)) ∧ th ∈ B.Theta 1 0 ∧ ∀ z, M.th (ex z) = th z * fr z

structure Dict (N : NumD ℂ) (B : AnArc O) where

  eX : B.X ≃+ N.X

  ex : (Fin B.gB → ℂ) → N.A

  fr : (Fin B.gB → ℂ) → ℂˣ

  th : (Fin B.gB → ℂ) → ℂ

  ab : IsAbFrame N.toNumB B ex fr th

  c_eq : ∀ x, N.c (eX x) = ex (B.ct x)

  ψ_eq : ∀ x, N.ψ (eX x) * fr (B.ct x) = B.psi x

variable {N : NumD ℂ} {B : AnArc O}

def Dict.IsPt (d : Dict N B) (v : B.V) (g : N.Gt) : Prop :=
  g.b = d.ex v.2 ∧ ∀ x, (g.s (d.eX x) : ℂ) * d.fr (B.ct x + v.2) = eTwoPi (v.1 x) * d.fr (B.ct x) * d.fr v.2

def Dict.Rep (d : Dict N B) (k : ℕ) (la : B.La) (p : N.QT k) : Prop :=
  p.1.1.toAdd = d.eX la.y ∧ d.IsPt ((k : ℂ)⁻¹ • B.P0 la) p.1.2

def tateDict (τ₀ : ℂ) : Dict (tate (Units.mk0 (eTwoPi (τ₀ / 2)) (AnArc.e_ne_zero _))) (AnArc.tate τ₀) where
  eX := AddEquiv.refl ℤ
  ex _ := 1
  fr _ := 1
  th := 1
  ab := ⟨fun _ _ => rfl, fun _ => ⟨0, rfl⟩, fun z => ⟨fun _ => Subsingleton.elim (α := Fin 0 → ℂ) _ _, fun _ => rfl⟩, rfl,
    fun l z => by
      have hl : l = 0 := Subsingleton.elim (α := (⊥ : Submodule ℤ (Fin 0 → ℂ))) _ _
      simp [hl, AnArc.ah],
    fun _ _ _ => rfl, fun _ => _root_.mul_one (1 : ℂˣ), AnArc.tate_one_mem_Theta τ₀ 1 0, fun _ => (_root_.mul_one (1 : ℂ)).symm⟩
  c_eq _ := rfl
  ψ_eq (x : ℤ) := by
    refine (_root_.mul_one _).trans (Units.ext ?_)
    change ((Units.mk0 (eTwoPi (τ₀ / 2)) (AnArc.e_ne_zero _) ^ x ^ 2 : ℂˣ) : ℂ) = eTwoPi (τ₀ * x ^ 2 / 2)
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← AnArc.e_mul_intCast]
    congr 1
    push_cast
    ring

def AllDict (P : ∀ {O : Type} [CommRing O] [StarRing O] {N : NumD ℂ} {B : AnArc O}, Dict N B → Prop) : Prop :=
  ∀ (O : Type) [CommRing O] [StarRing O] (N : NumD ℂ) (B : AnArc O) (d : Dict N B), P d

def PtSt : Prop := AllDict fun {_} _ _ {N} {B} d => (∀ v, ∃! g, d.IsPt v g) ∧ (∀ g, ∃ v, d.IsPt v g) ∧
  (∀ v v' g g', d.IsPt v g → d.IsPt v' g' → d.IsPt (v + v') (g * g')) ∧
  (∀ v, d.IsPt v 1 ↔ ∃ la : B.La, la.y = 0 ∧ v = B.P0 la) ∧ ∀ la : B.La, d.IsPt (B.P0 la) (N.io (d.eX la.y))

def QkSt : Prop := AllDict fun {_} _ _ {N} {B} d => ∀ k : ℕ, 0 < k → (∀ p, ∃ la, d.Rep k la p) ∧ (∀ la, ∃! p, d.Rep k la p) ∧
  (∀ la la' p p', d.Rep k la p → d.Rep k la' p' → d.Rep k (la + la') (p * p')) ∧
  ∀ (la la' : B.La) p p', d.Rep k la p → d.Rep k la' p' → (N.QEq p p' ↔ ∃ e, la' = la + k • e)

def WpSt : Prop := AllDict fun {_} _ _ {N} {B} d => ∀ k : ℕ, 0 < k → ∀ la la' p p', d.Rep k la p → d.Rep k la' p' →
  (N.wp p p' : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (B.EF la la' : ℂ) / k)

def TxSt : Prop := AllDict fun {O} _ _ {N} {B} d => ∀ w₀ : O, IsPrim B w₀ → ∀ (k : ℕ) (β : N.Form k),
  (∀ x y, B.be x y = β.be (d.eX x) (d.eX y)) → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (w : ℂ) (u : ℂˣ), (u : ℂ) = eTwoPi w →
  ∀ la p, d.Rep (m ^ 2) la p → ∀ x : B.X, (N.twist β u).txT m (N.twQ β u hm p) (d.eX x) =
    (-1) ^ B.EF la (w₀ • la) * Complex.exp (-(lin B la (B.Pw w la) / (2 * (m : ℂ) ^ 2))) *
      (B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.Pw w la) * eTwoPi (w * B.exponent 1 0 x))

def ThetaSt : Prop := ∀ (O : Type) [CommRing O] [StarRing O] (B : AnArc O) (w₀ : O), IsPrim B w₀ →
  ∀ th ∈ B.Theta 1 0, ∀ w : ℂ, Differentiable ℂ (B.Sum 1 0 th w) →
  ∀ (g : ℕ) (h : B.V ≃ₗ[ℂ] (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian →
    Submodule.span ℝ (Set.range (B.Pw w)) = ⊤ →
    (∀ a b, (hermForm Hm (h (B.Pw w a)) (h (B.Pw w b))).im = B.EF a b) →
    ∃ Θ : (Fin g → ℂ) → ℂ, Differentiable ℂ Θ ∧ (∀ v, Θ (h v) = 0 ↔ B.Sum 1 0 th w v = 0) ∧
      (∀ a z, Θ (z + h (B.Pw w a)) = (-1) ^ B.EF a (w₀ • a) * Complex.exp (Real.pi * hermForm Hm z (h (B.Pw w a)) +
        Real.pi / 2 * hermForm Hm (h (B.Pw w a)) (h (B.Pw w a))) * Θ z) ∧
      ∀ a (m : ℕ), m ≠ 0 → Complex.exp (-(Real.pi / 2 / (m : ℂ) ^ 2) * hermForm Hm (h (B.Pw w a)) (h (B.Pw w a))) *
          Θ ((m : ℂ)⁻¹ • h (B.Pw w a)) =
        Complex.exp (-(lin B a (B.Pw w a) / (2 * (m : ℂ) ^ 2))) * B.Sum 1 0 th w ((m : ℂ)⁻¹ • B.Pw w a)
end Values

section Fibre
variable {R : Type} [CommRing R] [IsDomain R]

def IsFib [Algebra (FractionRing R) ℂ] (P : PolAV (Sp R)) (J : (Sp ℂ ⟶ P.A.left) → P.L.ι) {g : ℕ}
    (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ)
    (ex : (Fin g → ℂ) → (TF (R := R) ℂ ⟶ P.A)) (fr : (Fin g → ℂ) → ℂˣ) : Prop :=
  (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ P.L.U (J ψ)) ∧
  ∃ (P' : PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left) (w : LB.Iso P'.L (P.L.pull φ)) (u : HolUnif P'.A P'.L g) (hΛ : u.Λ = Λ),
    IsGrpPullback P'.A P.A (TF (R := R) ℂ).hom φ ∧ w.IsGen ∧ u.IsAH Hm (fun l => χ ⟨l.1, hΛ ▸ l.2⟩) ∧
    (∀ v, IsTangent v → ∃! z, u.IsDiff z v) ∧ (∀ z, ∃! v, IsTangent v ∧ u.IsDiff z v) ∧
    (∀ f : P'.A ⟶ P'.A, IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f) ∧
    (∀ z, (ex z).left = (u.ex z).left ≫ φ) ∧
    ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P'.L.U i →
      (fr z : ℂ) = valAt' (u.ex z).left _ (w.s (fun _ => J (ex z).left, i)).val * u.fr i z

def RosGen (P : PolAV (Sp R)) (f f' : P.A ⟶ P.A) (r : LB.Gen (LB.LinComb P.L (rosatiφ P.A f f') rosatiε)) : Prop :=
  r.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ r (zero2 P.A)) (LB.oneGen P.L)

abbrev PrimT (P : PolAV (Sp R)) (f : P.A ⟶ P.A) : Type := LB.Gen (LB.LinComb P.L (K := Fin 4)
  ![(padd P.A (𝟙 _) f).left, 𝟙 P.A.left, f.left, (toUnit P.A ≫ η[P.A]).left] ![1, -2, -1, 2])

def PrimGen (P : PolAV (Sp R)) (f : P.A ⟶ P.A) (t : PrimT P f) : Prop :=
  t.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ t (eSec P.A)) (LB.oneGen P.L)
end Fibre

def AllFib (P : ∀ {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R)
    (_ : (Sp ℂ ⟶ D.P.A.left) → D.P.L.ι) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (_ : Matrix (Fin g) (Fin g) ℂ) (_ : Λ → ℂ)
    (_ : (Fin g → ℂ) → (TF (R := R) ℂ ⟶ D.P.A)) (_ : (Fin g → ℂ) → ℂˣ), Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R)
    (J : (Sp ℂ ⟶ D.P.A.left) → D.P.L.ι) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ)
    (ex : (Fin g → ℂ) → (TF (R := R) ℂ ⟶ D.P.A)) (fr : (Fin g → ℂ) → ℂˣ), IsFib D.P J Λ Hm χ ex fr → P D J Λ Hm χ ex fr

def FibExSt : Prop := ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (P : PolAV (Sp R))
  (J : (Sp ℂ ⟶ P.A.left) → P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ P.L.U (J ψ)) →
  ∃ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ)
    (ex : (Fin g → ℂ) → (TF (R := R) ℂ ⟶ P.A)) (fr : (Fin g → ℂ) → ℂˣ), IsFib P J Λ Hm χ ex fr ∧
    (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef

def FibGrpSt : Prop := AllFib fun {_} _ _ _ D _ {g} Λ Hm χ ex fr =>
  DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧ Hm.IsHermitian ∧
  (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ (∀ l, ‖χ l‖ = 1) ∧
  (∀ l m : Λ, χ (l + m) = χ l * χ m * Complex.exp (Real.pi * Complex.I * ((hermForm Hm l m).im : ℂ))) ∧
  (∀ z w, ex (z + w) = ex z * ex w) ∧ Function.Surjective ex ∧ (∀ z, ex z = 1 ↔ z ∈ Λ) ∧
  (∀ (l : Λ) z, (fr z : ℂ) = χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * fr (z + l)) ∧
  ∀ f : D.P.A ⟶ D.P.A, IsMonHom f → ∃! F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, ex (F z) = ex z ≫ f

def FibCubeSt : Prop := AllFib fun {_} _ _ _ D J {_} _ _ _ ex fr => ∀ x y z,
  vF (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t (lift (ex x) (lift (ex y) (ex z))).left J *
    fr (x + y) * fr (x + z) * fr (y + z) * fr 0 = fr (x + y + z) * fr x * fr y * fr z

def FibSymSt : Prop := AllFib fun {_} _ _ _ D J {_} _ _ χ ex fr =>
  (∀ x, vF D.sym (ex x).left J * fr x = fr (-x)) ∧ ∀ l, χ (-l) = χ l

def FibRosSt : Prop := AllFib fun {_} _ _ _ D J {g} _ Hm _ ex fr => ∀ (f f' : D.P.A ⟶ D.P.A), IsMonHom f → IsMonHom f' →
  ∀ F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z, ex (F z) = ex z ≫ f) → (∀ z, ex (G z) = ex z ≫ f') →
  ∀ r, RosGen D.P f f' r → (∀ x z, hermForm Hm (F x) z = hermForm Hm x (G z)) ∧
    ∀ x z, vF r (lift (ex x) (ex z)).left J * fr (F x) * fr z * fr (x + G z) = fr (F x + z) * fr x * fr (G z)

def FibPrimSt : Prop := AllFib fun {_} _ _ _ D J {g} Λ Hm χ ex fr => ∀ (f : D.P.A ⟶ D.P.A), IsMonHom f →
  ∀ (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ l ∈ Λ, F l ∈ Λ), (∀ z, ex (F z) = ex z ≫ f) →
  (∀ z w, hermForm Hm z w = hermForm Hm z (F w) + hermForm Hm (F z) w) →
  ∀ Ef : LinearMap.BilinForm ℤ Λ, (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) →
  ∀ t, PrimGen D.P f t → (∀ l : Λ, χ l = (-1) ^ Ef l ⟨F l, hF l l.2⟩) ∧
    ∀ z, vF t (ex z).left J * fr z ^ 2 * fr (F z) = fr (z + F z) * fr 0 ^ 2

def FibSecSt : Prop := AllFib fun {_} _ _ _ D J {g} _ _ _ ex fr => ∀ s : H0 D.P.L 1, ∃ θ : (Fin g → ℂ) → ℂ,
  Differentiable ℂ θ ∧ ∀ z, sF s (ex z).left J = θ z * fr z

def FibLieSt : Prop := AllFib fun {R} _ _ _ D _ {g} _ _ _ ex _ => ∀ (O : Type) [CommRing O] (act : Geo.Tor.OAct O D.P.A)
  (F : O → Module.End ℂ (Fin g → ℂ)), (∀ a z, ex (F a z) = ex z ≫ act.act a) → ∀ (τ : O →+* ℂ) (n : ℕ),
  LieMult act (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R _))) τ n →
    Module.finrank ℂ (⨅ a, (F a).eigenspace (τ a) : Submodule ℂ (Fin g → ℂ)) = n

def BrActSt : Prop := AllN fun {_} _ _ {D} {F} _ _ {N} ν => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O),
  (∀ a, ∃ r, RosGen D.P (oa.onB.act a) (oa.onB.act (star a)) r ∧ ∀ y y' : N.X,
    (N.τ (ν.eX.symm (a • ν.eX y)) y' : F) * vF r (lift (ν.eA (N.c y)) (ν.eA (N.c y'))).left ν.J =
      N.τ y (ν.eX.symm (star a • ν.eX y'))) ∧
  (∀ a, ∃ r, RosGen D.P (oa.onB.act (star a)) (oa.onB.act a) r ∧ ∀ g g' c c', ν.Pt g c → ν.Pt g' c' → GtAct oa a g g' →
    ν.eA c'.b = ν.eA c.b ≫ oa.onB.act a ∧ ∀ χ : N.X,
      (c'.s χ : F) = c.s (ν.eX.symm (star a • ν.eX χ)) * vF r (lift (ν.eA (N.c χ)) (ν.eA c.b)).left ν.J) ∧
  ∀ w₀, TraceFormTwistIso D oa w₀ → ∃ t, PrimGen D.P (oa.onB.act w₀) t ∧ ∀ y : N.X,
    (N.τ y (ν.eX.symm (w₀ • ν.eX y)) : F) * vF t (ν.eA (N.c y)).left ν.J = N.ψ y

section ThetaShiftProofs
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev An (H : Host E) : Type 1 := @AnArc (𝓞 E) _ H.starRing

def SigOK (D : Datum H) (B : An H) (r : ℕ) (ρ : ℂ) : Prop := letI := H.starRing
  ∀ τ : 𝓞 E →+* ℂ, Module.finrank ℂ (⨅ a, (B.F a).eigenspace (τ a) : Submodule ℂ (Fin B.gB → ℂ)) + r =
    open Classical in if τ H.rt = ρ then D.p else D.q

variable {D : Datum H} {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ]

def AbLinked (A : ArcF D R ℂ) (B : An H) : letI := H.starRing
    ((Fin B.gB → ℂ) → A.N.A) → ((Fin B.gB → ℂ) → ℂˣ) → ((Fin B.gB → ℂ) → ℂ) → Prop := letI := H.starRing
  fun ex fr th => IsAbFrame A.N.toNumB B ex fr th ∧ th ≠ 0 ∧ (∀ l, B.chi l = (-1) ^ B.Ef l (B.FLam H.w0 l)) ∧
    SigOK D B (Module.finrank (𝓞 E) A.D₀.X) A.ρ ∧
    (∀ a z, A.ν.eA (ex (B.F a z)) = A.ν.eA (ex z) ≫ A.oa.onB.act a) ∧
    (∀ a b r, RosGen A.D₀.P (A.oa.onB.act a) (A.oa.onB.act b) r → ∀ x z,
      vF r (lift (A.ν.eA (ex x)) (A.ν.eA (ex z))).left A.ν.J * fr (B.F a x) * fr z * fr (x + B.F b z) =
        fr (B.F a x + z) * fr x * fr (B.F b z)) ∧
    ∀ t, PrimGen A.D₀.P (A.oa.onB.act H.w0) t → ∀ z,
      vF t (A.ν.eA (ex z)).left A.ν.J * fr z ^ 2 * fr (B.F H.w0 z) = fr (z + B.F H.w0 z)

def ActLinked (A : ArcF D R ℂ) (B : An H) : letI := H.starRing; Dict A.N B → Prop := letI := H.starRing
  fun d => (∀ (a : 𝓞 E) x, d.eX (a • x) = A.act a (d.eX x)) ∧
    ∀ (a : 𝓞 E) g g' c c' v, A.ν.Pt g c → A.ν.Pt g' c' → GtAct A.oa a g g' → d.IsPt v c → d.IsPt (B.actV a v) c'

def IsTower (D : Datum H) {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La) (ζ : ℕ → ℂˣ)
    (f : ℕ → D.La → La) : Prop := ∀ n : ℕ, 0 < n →
  (∀ a b, ∃ e, f n (a + b) = f n a + f n b + n • e) ∧ (∀ (c : 𝓞 E) a, ∃ e, f n (c • a) = c • f n a + n • e) ∧
  (∀ a, (∃ e, f n a = n • e) ↔ ∃ b, a = n • b) ∧ (∀ x, ∃ a e, x = f n a + n • e) ∧
  (∀ m : ℕ, 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
  ∀ a b, ((ζ n ^ D.EF a b : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF (f n a) (f n b) : ℂ) / n)
end ThetaShiftProofs

def ValSt : Prop := AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ]
  (A : ArcF D R ℂ), ∃ (B : An H) (ex : _) (fr : _) (th : _), AbLinked A B ex fr th

def DictSt : Prop := AllD fun {E} _ _ _ {H} D => letI := H.starRing
  ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (A : ArcF D R ℂ) (k : ℕ) (β : A.N.Form k), A.Bal β →
  ∃ (B : An H) (d : Dict A.N B), ActLinked A B d ∧ (∀ x y, B.be x y = β.be (d.eX x) (d.eX y)) ∧ IsPrim B H.w0 ∧ d.th ≠ 0 ∧
    SigOK D B (Module.finrank (𝓞 E) B.X) A.ρ

def TowerSt : Prop := AllD fun {_} _ _ _ {H} D => letI := H.starRing
  ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (A : ArcF D R ℂ) (B : An H) (d : Dict A.N B),
  ActLinked A B d → ∃ f : ℕ → D.La → B.La, IsTower D B.EF A.I.ζ f ∧ ∀ n, 0 < n → ∀ a, d.Rep n (f n a) (A.q n a)

def TypeSt : Prop := AllD fun {E} _ _ _ {H} D => letI := H.starRing
  ∀ B : An H, SigOK D B (Module.finrank (𝓞 E) B.X) H.rt0 →
  ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (h : B.V ≃ₗ[ℂ] (Fin g → ℂ)), IsTypeFn H D.p D.q ty ∧
    ∀ (a : 𝓞 E) v i, h (B.actV a v) i = ty i (a : E) * h v i

def AllPer (Q : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (_ : Datum H) {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (_ : LinearMap.BilinForm ℤ La) {g : ℕ} (_ : Fin g → (E →+* ℂ)) (_ : La →+ (Fin g → ℂ)), Prop) : Prop :=
  AllD fun {E} _ _ _ {H} D => ∀ (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (P : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsTypeFn H D.p D.q ty →
    Function.Bijective EF → (∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y)) →
    (∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i) → Function.Injective P → DiscreteTopology P.range →
    Submodule.span ℝ (Set.range P) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) → Q D EF ty P

def TripleSt : Prop := AllPer fun {E} _ _ _ {H} D {_} _ _ EF {g} ty P => letI := H.starRing
  ∃ (Q : PolAV (Sp ℂ)) (oa : Q.OAct (𝓞 E)) (L₀ : LB Q.A.left) (u : HolUnif Q.A L₀ g), Q.g = g ∧
    LBIso Q.L (cubeLB Q.A ![𝟙 Q.A, oa.act H.w0] Q.L) ∧ DetCond D (ofRingAct oa.toRingAct) (𝟙 (Sp ℂ)) H.rt0 ∧
    (∀ v, IsTangent v → ∃! z, u.IsDiff z v) ∧ (∀ z, ∃! v, IsTangent v ∧ u.IsDiff z v) ∧
    (∀ z, u.ex z = 1 ↔ z ∈ P.range) ∧ (∀ (a : 𝓞 E) z, u.ex (fun k => ty k (a : E) * z k) = u.ex z ≫ oa.act a) ∧
    ∀ (k : ℕ) a b (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • P a)) (u.ex ((k : ℂ)⁻¹ • P b)) (unitOn c)

def ReframeSt : Prop := ∀ (Q : PolAV (Sp ℂ)) (L₀ : LB Q.A.left) (g : ℕ) (u₀ : HolUnif Q.A L₀ g), Q.g = g →
  (∀ v, IsTangent v → ∃! z, u₀.IsDiff z v) → (∀ z, ∃! v, IsTangent v ∧ u₀.IsDiff z v) →
  ∃ (u : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ)
    (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin Q.g → ℂ)), u.IsAH Hm χ ∧ (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧
    ∀ z, u.ex (F z) = u₀.ex z

def ObjSt : Prop := AllPer fun {E} _ _ _ {H} D {_} _ _ EF {g} ty P => letI := H.starRing
  ∃ (Q : PolAV (Sp ℂ)) (oa : Q.OAct (𝓞 E)) (u : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ)
    (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin Q.g → ℂ)) (hΛ : ∀ a, F (P a) ∈ u.Λ),
    LBIso Q.L (cubeLB Q.A ![𝟙 Q.A, oa.act H.w0] Q.L) ∧ DetCond D (ofRingAct oa.toRingAct) (𝟙 (Sp ℂ)) H.rt0 ∧
    u.IsAH Hm χ ∧ (∀ z ∈ u.Λ, ∃ a, z = F (P a)) ∧ (∀ a b, (hermForm Hm (F (P a)) (F (P b))).im = EF a b) ∧
    (∀ a, χ ⟨F (P a), hΛ a⟩ = (-1) ^ EF a (H.w0 • a)) ∧
    (∀ (a : 𝓞 E) z, u.ex (F fun k => ty k (a : E) * z k) = u.ex (F z) ≫ oa.act a) ∧
    ∀ (k : ℕ) a b (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • F (P a))) (u.ex ((k : ℂ)⁻¹ • F (P b))) (unitOn c)

end GlobalTheory.Ex.Arch
end
