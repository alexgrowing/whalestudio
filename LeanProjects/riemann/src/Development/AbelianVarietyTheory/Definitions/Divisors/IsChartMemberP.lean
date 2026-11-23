import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

structure VPre {O : Type} [CommRing O] (bar : O → O) (q : ℕ) {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ)
    (A : Type) [CommRing A] [IsLocalRing A] : Type 2 where
  posW : PosW W

  Y : Type 1

  V : Y → Type
  [ring : ∀ y, CommRing (V y)]
  [dom : ∀ y, IsDomain (V y)]
  [loc : ∀ y, IsLocalRing (V y)]
  cn : ∀ y, IsCN (V y)

  ev : ∀ y, A →+* V y
  ev_loc : ∀ y, IsLocalHom (ev y)

  X : Y → Type
  [add : ∀ y, AddCommGroup (X y)]
  [mod : ∀ y, Module O (X y)]
  [fin : ∀ y, Module.Finite O (X y)]
  [proj : ∀ y, Module.Projective O (X y)]
  [freeZ : ∀ y, Module.Free ℤ (X y)]
  [finZ : ∀ y, Module.Finite ℤ (X y)]
  rank_le : ∀ y, Module.finrank O (X y) ≤ q

  m : Y → ℕ

  t : ∀ y, Fin (m y) → V y
  t_mem : ∀ y i, t y i ∈ maximalIdeal (V y) ∧ t y i ≠ 0

  δ : ∀ y, Fin (m y) → LinearMap.BilinForm ℤ (X y)
  bal : ∀ y i, δ y i ∈ balForms bar (X y)
  nonneg : ∀ y i x, 0 ≤ δ y i x x
  pos : ∀ y x, x ≠ 0 → ∃ i, 0 < δ y i x x

  Q : Type

  u : ∀ y, (Fin s → X y) → Q → V y
  u_unit : ∀ y mu, ∃ c, IsUnit (u y mu c)

attribute [instance] VPre.ring VPre.dom VPre.loc VPre.add VPre.mod VPre.fin VPre.proj VPre.freeZ VPre.finZ

section
variable {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {A : Type} [CommRing A] [IsLocalRing A]

def VSys.pre {N₁ : ℕ} (Φ : VSys bar q W N₁ A) : VPre bar q W A where
  posW := Φ.posW
  Y := Φ.Y
  V := Φ.V
  cn := Φ.cn
  ev := Φ.ev
  ev_loc := Φ.ev_loc
  X := Φ.X
  rank_le := Φ.rank_le
  m := Φ.m
  t := Φ.t
  t_mem := Φ.t_mem
  δ := Φ.δ
  bal := Φ.bal
  nonneg := Φ.nonneg
  pos := Φ.pos
  Q := Φ.Q
  u := Φ.u
  u_unit := Φ.u_unit

namespace VPre
variable (Φ : VPre bar q W A)

def term (y : Φ.Y) (mu : Fin s → Φ.X y) (c : Φ.Q) : Φ.V y := Φ.u y mu c * mono W (Φ.t y) (Φ.δ y) mu

def abelian₂ : Prop :=
  ∃ C : ℕ, ∀ y, Φ.m y = 1 → ∀ i x, x ≠ 0 → ∃ h ∈ maximalIdeal A, Φ.ev y h ∣ Φ.t y i ^ (C * (Φ.δ y i x x).toNat)

def Four (N₁ : ℕ) : Prop :=
  ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ N₁ ∣ N ∧ ∃ k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y, k y₀ = LinearMap.id ∧
    (∀ y, IsUnimodMod O N (k y)) ∧ ∀ (l : ℕ) (a : Fin l × Fin s → Φ.X y₀) (c : Fin l → Φ.Q) (e : ℕ), ∃ f : A,
      ∀ (y : Φ.Y) (j : ℕ), ∃ S : Finset (Fin l × Fin s → Φ.X y), (↑S : Set _) ⊆ orbit O N₁ N (k y) a ∧
        (∀ mu ∈ orbit O N₁ N (k y) a, mu ∉ S → (j : ℤ) ≤ ∑ i, lin W mu (Φ.δ y i)) ∧
        Φ.ev y f - ∑ mu ∈ S, ∏ i, Φ.u y (fun v => mu (i, v)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun v => mu (i, v)) ∈
          maximalIdeal (Φ.V y) ^ j ⊔ (maximalIdeal A ^ e).map (Φ.ev y)

def IsClassSum (y : Φ.Y) (N : ℕ) (κ : Fin s → Φ.X y) (c : Φ.Q) {V' : Type} [CommRing V'] [IsLocalRing V']
    (io : Φ.V y →+* V') (x : V') : Prop :=
  ∀ j : ℕ, ∃ S : Finset (Fin s → Φ.X y), (∀ mu ∈ S, ∀ v, CongMod N (mu v) (κ v)) ∧
    (∀ mu, (∀ v, CongMod N (mu v) (κ v)) → mu ∉ S → (j : ℤ) ≤ ∑ i, qW W (Φ.δ y i) mu) ∧
    x - io (∑ mu ∈ S, Φ.term y mu c) ∈ maximalIdeal V' ^ j

def Exact (N₁ : ℕ) : Prop :=
  ∀ (y : Φ.Y) (κ : Fin s → Φ.X y) (c : Φ.Q), ∃ h : A, Φ.IsClassSum y N₁ κ c (RingHom.id _) (Φ.ev y h)

def ClassSums [IsDomain A] (N₁ : ℕ) : Prop :=
  ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ 1 ≤ N ∧ N₁ ∣ N ∧ ∃ k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y, k y₀ = LinearMap.id ∧
    (∀ y, IsUnimodMod O N (k y)) ∧ ∃ (L : Type) (_ : Field L) (_ : Algebra (FractionRing A) L) (_ : Algebra A L)
      (_ : IsScalarTower A (FractionRing A) L) (_ : FiniteDimensional (FractionRing A) L) (_ : IsGalois (FractionRing A) L)
      (𝔷 : Ideal (integralClosure A L)) (f : (Fin s → Φ.X y₀) → Φ.Q → integralClosure A L), 𝔷.IsMaximal ∧
      (∀ κ κ' c, (∀ v, CongMod N (κ v) (κ' v)) → f κ c = f κ' c) ∧
      (∀ y, ∃ (V' : Type) (_ : CommRing V') (_ : IsLocalRing V') (io : Φ.V y →+* V') (ev' : integralClosure A L →+* V'),
        io.Finite ∧ IsLocalHom io ∧ (∀ I : Ideal (Φ.V y), (I.map io).comap io = I) ∧
        ev'.comp (algebraMap A _) = io.comp (Φ.ev y) ∧ (maximalIdeal V').comap ev' = 𝔷 ∧
        ∀ κ c, Φ.IsClassSum y N (fun v => k y (κ v)) c io (ev' (f κ c))) ∧
      ∀ σ : L ≃ₐ[FractionRing A] L, (∀ x x' : integralClosure A L, (x' : L) = σ x → (x ∈ 𝔷 ↔ x' ∈ 𝔷)) →
        ∃ ga : Φ.X y₀ →ₗ[ℤ] Φ.X y₀, (∀ (b : O) x, CongMod N (ga (b • x)) (b • ga x)) ∧ (N : ℤ) ∣ LinearMap.det ga - 1 ∧
          (∀ x, CongMod N₁ (ga x) x) ∧ ∀ κ c, σ (f κ c : L) = (f (fun v => ga (κ v)) c : L)

def rescale (v : ∀ y, (Φ.V y)ˣ) : VPre bar q W A :=
  { Φ with
    u := fun y mu c => Φ.u y mu c * v y
    u_unit := fun y mu => (Φ.u_unit y mu).imp fun _ h => h.mul (v y).isUnit }

def toVSys (N₁ : ℕ) (hl : Φ.abelian₂) (hf : Φ.Four N₁) : VSys bar q W N₁ A where
  posW := Φ.posW
  Y := Φ.Y
  V := Φ.V
  cn := Φ.cn
  ev := Φ.ev
  ev_loc := Φ.ev_loc
  X := Φ.X
  rank_le := Φ.rank_le
  m := Φ.m
  t := Φ.t
  t_mem := Φ.t_mem
  δ := Φ.δ
  bal := Φ.bal
  nonneg := Φ.nonneg
  pos := Φ.pos
  Q := Φ.Q
  u := Φ.u
  u_unit := Φ.u_unit
  lam := hl
  four := hf

theorem pre_toVSys (N₁ : ℕ) (hl : Φ.abelian₂) (hf : Φ.Four N₁) : (Φ.toVSys N₁ hl hf).pre = Φ := rfl

end VPre

theorem VSys.pre_lam {N₁ : ℕ} (Φ : VSys bar q W N₁ A) : Φ.pre.abelian₂ := Φ.lam

theorem VSys.pre_four {N₁ : ℕ} (Φ : VSys bar q W N₁ A) : Φ.pre.Four N₁ := Φ.four
end

namespace Sep

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

def IsThetaTerms₀ (D : DegPre V₁) (N₁ : ℕ) {X C : Type} [AddCommGroup X] (e : X ≃+ D.X) (T : X → C → V₁) : Prop :=
  ∃ (th : Fam D (FractionRing V₁) 1) (g : C → GtPtF D (FractionRing V₁)) (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A))
    (w : ∀ c, Frm D (FractionRing V₁) 1 (g c).b),
    (∀ c, (g c).b = toUnit _ ≫ b c) ∧ (∀ c, ∃ o, GtPtF.IsNsmul N₁ (g c) o ∧ o.IsZero) ∧
    (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ N₁ = 1 →
      ∃ c, p = toUnit _ ≫ b c) ∧
    (∀ c, (w c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
      val (w c) (𝟙 _) z J ^ (N₁ ^ 2) * val κ (g c).b.left z J = 1) ∧
    (∀ mu c, IsCoef 1 (g c) (w c) (e mu) (th.s (e mu)) (algebraMap V₁ (FractionRing V₁) (T mu c)))

theorem IsThetaTerms.zero {D : DegPre V₁} {N₁ : ℕ} {X C : Type} [AddCommGroup X] {e : X ≃+ D.X} {T : X → C → V₁}
    (h : IsThetaTerms D N₁ e T) : IsThetaTerms₀ D N₁ e T := by
  obtain ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅, -⟩ := h
  exact ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅⟩

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  (X₁ : Setup F W i) (z₁ : X₁.M.Z)

def RegAt (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) : Prop :=
  ∀ a ∈ X₁.S.R, a ∈ X₁.M.O ((jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V₁)))

variable (Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁))

def HasTraitsR : Prop :=
  ∀ (T : Trait F) (ev : X₁.M.Z.presheaf.stalk z₁ →+* T.V), IsLocalHom ev → RegAt X₁ z₁ ev →
    jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = T.y ≫ i →
    ∃ (y : Φ.Y) (f : T.V →+* Φ.V y) (e : Φ.X y ≃+ T.D.toPre.X), Φ.m y = 1 ∧ IsPrincipalIdealRing (Φ.V y) ∧
      Function.Injective f ∧ IsLocalHom f ∧ f.comp ev = Φ.ev y ∧
      ∀ k, Φ.t y k = f T.ϖ ∧ ∀ a b, Φ.δ y k a b = T.β (e a) (e b)

def IsChartMemberP [IsLocalRing V] (N₁ : ℕ) (Q : Data V) (ξ : Sp V ⟶ Z) {m : ℕ} (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ Q.X) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m) : Prop :=
  Function.Injective ρ ∧ ρ.Finite ∧ spMap (Φ.ev y) ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = spMap ρ ≫ ξ ∧
    (∀ k, Φ.t y k = ρ (t (h k)) ∧ ∀ a b, Φ.δ y k a b = δ (h k) (e a) (e b)) ∧
    ∃ (D : DegPre (Φ.V y)) (e₈ : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e₈ ∧
      IsThetaTerms₀ D N₁ e₈ fun mu c => Φ.term y (fun a => e.symm (mu a)) c

theorem HasTraits.reg {N₁ : ℕ} {Ψ : VSys (id : ℤ → ℤ) g W N₁ (X₁.M.Z.presheaf.stalk z₁)} (h : HasTraits X₁ z₁ Ψ) :
    HasTraitsR X₁ z₁ Ψ.pre := fun T ev h₁ _ h₂ => h T ev h₁ h₂

end Sep

end GlobalTheory.Poinc
