import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMapMemLocalSpan

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts

namespace GlobalTheory.ChainDesc

section Crd

variable {X : Scheme.{0}} {h : ℕ} {E : X.Modules} (ι : E ⟶ freeModule X (Fin h))

def crd (W : X.Opens) : Γ(E, W) →ₗ[Γ(X, W)] (Fin h → Γ(X, W)) :=
  (GlobalTheory.LatGlue.coords X h W).toLinearMap ∘ₗ appLinear ι W

theorem crd_apply (W : X.Opens) (s : Γ(E, W)) (i : Fin h) :
    crd ι W s i = ((GlobalTheory.VB.isFrame_freeFrame X (Fin h)).basis le_top).repr (ι.app W s) i := rfl

theorem crd_resM {W W' : X.Opens} (hle : W' ≤ W) (s : Γ(E, W)) :
    crd ι W' (resM E hle s) = piMap (resG X hle) (Fin h) (crd ι W s) := by
  change GlobalTheory.LatGlue.coords X h W' (ι.app W' (resM E hle s)) = _
  rw [GlobalTheory.Twist.app_resM, GlobalTheory.LatGlue.coords_resM]
  rfl

theorem crd_injective [Mono ι] (W : X.Opens) : Function.Injective (crd ι W) :=
  (GlobalTheory.LatGlue.coords X h W).injective.comp (injective_app_of_mono ι W)

abbrev latOf (W : X.Opens) : Submodule Γ(X, W) (Fin h → Γ(X, W)) := LinearMap.range (crd ι W)

end Crd

section Loc

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ]
  {h : ℕ}

def IsQuot (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) {E : B.X.Modules} (ι : E ⟶ freeModule B.X (Fin h))
    (N : ∀ W : B.X.Opens, Submodule Γ(B.X, W) (Fin h → Γ(B.X, W))) (Q : AM B Λ) (t : E ⟶ Q.V) : Prop :=
  Q.V.IsQuasicoherent ∧ ∀ W : B.X.Opens, IsAffineOpen W → Function.Surjective (t.app W) ∧
    (∀ s, t.app W s = 0 ↔ crd ι W s ∈ N W) ∧
    ∀ (a : Λ) (s s' : Γ(E, W)), crd ι W s' = mv (RingHom.id _) (M a) (crd ι W s) →
      (Q.ρ a : Q.V ⟶ Q.V).app W (t.app W s) = t.app W s'

theorem IsQuot.exists_equiv {M : Λ →+* Matrix (Fin h) (Fin h) ℤ} {E : B.X.Modules} {ι : E ⟶ freeModule B.X (Fin h)} [Mono ι]
    {N : ∀ W : B.X.Opens, Submodule Γ(B.X, W) (Fin h → Γ(B.X, W))} {Q : AM B Λ} {t : E ⟶ Q.V} (k : IsQuot M ι N Q t)
    {W : B.X.Opens} (hW : IsAffineOpen W) {L N' : Submodule Γ(B.X, W) (Fin h → Γ(B.X, W))} (hL : L = latOf ι W)
    (hN : N' = N W) : ∃ e : Qt L N' ≃ₗ[Γ(B.X, W)] Γ(Q.V, W),
      ∀ (s : Γ(E, W)) (x : L), x.1 = crd ι W s → e (Submodule.Quotient.mk x) = t.app W s := by
  subst hL hN
  obtain ⟨h1, h2, -⟩ := k.2 W hW
  let a := LinearEquiv.ofInjective _ (crd_injective ι W)
  let u : latOf ι W →ₗ[Γ(B.X, W)] Γ(Q.V, W) := appLinear t W ∘ₗ a.symm.toLinearMap
  have hu : ∀ s, u (a s) = t.app W s := fun s => congrArg (t.app W) (a.symm_apply_apply s)
  have hk : (N W).comap (latOf ι W).subtype = LinearMap.ker u := by
    ext x
    obtain ⟨s, rfl⟩ := a.surjective x
    rw [LinearMap.mem_ker, hu, h2]
    rfl
  refine ⟨(Submodule.quotEquivOfEq _ _ hk).trans (u.quotKerEquivOfSurjective fun y => ?_), fun s x hx => ?_⟩
  · obtain ⟨s, rfl⟩ := h1 y
    exact ⟨_, hu s⟩
  · obtain rfl : x = a s := Subtype.ext hx
    exact hu s

abbrev baseOn (h : ℕ) (π : Γ(B.X, ⊤)) (W : B.X.Opens) : Submodule Γ(B.X, W) (Fin h → Γ(B.X, W)) :=
  baseOf (resG B.X le_top π) h

abbrev ChainOn (p h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (W : B.X.Opens) : Type :=
  RChain p Γ(B.X, W) h o (resG B.X le_top π) (fun n => resG B.X le_top (γ n)) Γ(Lie.V, W) Γ(Om.V, W)

variable {p o : ℕ} {Lie Om : AM B Λ} {π : Γ(B.X, ⊤)} {γ : ℕ → Γ(B.X, ⊤)}

def Fits {E : ℕ → B.X.Modules} (ι : ∀ n, E n ⟶ freeModule B.X (Fin h)) {W : B.X.Opens}
    (D : ChainOn p h o Lie Om π γ W) : Prop := ∀ n ≤ o, D.L n = latOf (ι n) W

def ResMap {W W' : B.X.Opens} (hle : W' ≤ W) (D : ChainOn p h o Lie Om π γ W) (D' : ChainOn p h o Lie Om π γ W') : Prop :=
  D.Map D' (resG B.X hle) 1 (resM Lie.V hle) (resM Om.V hle)

def IsLoc (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) {E : ℕ → B.X.Modules} (ι : ∀ n, E n ⟶ freeModule B.X (Fin h)) {I : Type}
    (V : I → B.X.Opens) (D : ∀ i, ChainOn p h o Lie Om π γ (V i)) : Prop :=
  (∀ i, IsAffineOpen (V i)) ∧ (∀ x : B.X, ∃ i, x ∈ V i) ∧ (∀ i k, IsAffineOpen (V i ⊓ V k)) ∧
  (∀ n, GlobalTheory.VB.IsVB (E n) h ∧ Mono (ι n)) ∧ (∀ i, Fits ι (D i)) ∧
  (∀ i k, ∃ D' : ChainOn p h o Lie Om π γ (V i ⊓ V k), Fits ι D' ∧ ResMap inf_le_left (D i) D' ∧
    ResMap inf_le_right (D k) D') ∧
  ∀ (i : I) (a : Λ), (D i).Map (D i) (RingHom.id _) (M a) ((Lie.ρ a : Lie.V ⟶ Lie.V).app _) ((Om.ρ a : Om.V ⟶ Om.V).app _)

def JOn {E : B.X.Modules} (ι : E ⟶ freeModule B.X (Fin h)) {W : B.X.Opens} (D : ChainOn p h o Lie Om π γ W)
    {Q : B.X.Modules} (t : E ⟶ Q) (j : Lie.V ⟶ Q) : Prop :=
  ∀ (s : Γ(Lie.V, W)) (x : Γ(E, W)) (y : D.L 0), y.1 = crd ι W x → D.j s = Submodule.Quotient.mk y →
    j.app W s = t.app W x

def ROn {E : B.X.Modules} (ι : E ⟶ freeModule B.X (Fin h)) {W : B.X.Opens} (D : ChainOn p h o Lie Om π γ W)
    {Q : B.X.Modules} (t : E ⟶ Q) (ρ : Om.V ⟶ Q) : Prop :=
  ∀ (s : Γ(Om.V, W)) (x : Γ(E, W)) (y : D.L 0), y.1 = crd ι W x →
    D.ρ s = Submodule.Quotient.mk (Submodule.Quotient.mk y) → ρ.app W s = t.app W x

end Loc

section Cover

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B B' : Vert.Model O} {Λ : Type} [CommRing Λ]

def IsCov (f : Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp) : Prop :=
  GlobalTheory.IsNormalScheme B'.X ∧ IsFinite f.f ∧ (∀ U, Function.Injective (g U)) ∧
  (∀ (U : AffOp B.X) (a : Γ(B.X, U.1)), g U ((f.f.app U.1).hom a) = algebraMap Γ(B.X, U.1) U.Bp a) ∧
  ∀ (U U' : AffOp B.X) (hle : U'.1 ≤ U.1) (a : Γ(B'.X, f.f ⁻¹ᵁ U.1)),
    g U' ((B'.X.presheaf.map (homOfLE (f.f.preimage_mono hle)).op).hom a) = AffOp.res hle (g U a)

variable {p h o : ℕ} {Lie Om : AM B Λ} {π : Γ(B.X, ⊤)} {γ : ℕ → Γ(B.X, ⊤)} (C : ChainsBp p h o Lie Om π γ)
  (f : Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp)

abbrev ChainUp (p h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (f : Vert.Model.Hom B' B)
    (W : B'.X.Opens) : Type :=
  ChainOn p h o ((pullA f.f).obj Lie) ((pullA f.f).obj Om) (f.f.appTop π) (fun n => f.f.appTop (γ n)) W

def IsLatOf {E : ℕ → B'.X.Modules} (ι : ∀ n, E n ⟶ freeModule B'.X (Fin h)) : Prop :=
  ∀ n, GlobalTheory.VB.IsVB (E n) h ∧ Mono (ι n) ∧ ∀ U : AffOp B.X,
    latOf (ι n) (f.f ⁻¹ᵁ U.1) = ((C U).L (min n o)).comap (piMap (g U) (Fin h)) ∧
    (C U).L (min n o) = Submodule.span U.Bp (piMap (g U) (Fin h) '' (latOf (ι n) (f.f ⁻¹ᵁ U.1) : Set _))

def IsDown (U : AffOp B.X) (S : Set (Γ(Om.V, U.1) × (C U).L 0)) (D : ChainUp p h o Lie Om π γ f (f.f ⁻¹ᵁ U.1)) : Prop :=
  ∃ (l : Γ((Scheme.Modules.pullback f.f).obj Lie.V, f.f ⁻¹ᵁ U.1) →ₛₗ[g U] SecBp Lie.V U)
    (m : Γ((Scheme.Modules.pullback f.f).obj Om.V, f.f ⁻¹ᵁ U.1) →ₛₗ[g U] SecBp Om.V U),
    (∀ s, l (pullbackSections f.f Lie.V le_rfl s) = 1 ⊗ₜ s) ∧ (∀ s, m (pullbackSections f.f Om.V le_rfl s) = 1 ⊗ₜ s) ∧
    D.Map (C U) (g U) 1 l m ∧ (∀ n ≤ o, ∀ x, x ∈ D.L n ↔ piMap (g U) (Fin h) x ∈ (C U).L n) ∧
    (∀ n, o < n → D.L n = baseOn h (f.f.appTop π) (f.f ⁻¹ᵁ U.1)) ∧
    (∀ s ∈ S, ∃ x : D.L 0, piMap (g U) (Fin h) x.1 = s.2.1 ∧
      D.ρ (pullbackSections f.f Om.V le_rfl s.1) = Submodule.Quotient.mk (Submodule.Quotient.mk x)) ∧
    (∀ x, cstBp U π ∣ g U x → resG B'.X le_top (f.f.appTop π) ∣ x) ∧
    ∀ y, l y ∈ (p : U.Bp) • (⊤ : Submodule U.Bp (SecBp Lie.V U)) → y ∈ (p : Γ(B'.X, f.f ⁻¹ᵁ U.1)) •
      (⊤ : Submodule Γ(B'.X, f.f ⁻¹ᵁ U.1) Γ((Scheme.Modules.pullback f.f).obj Lie.V, f.f ⁻¹ᵁ U.1))

variable {C f g}

theorem IsCov.map_cst (k : IsCov f g) (U : AffOp B.X) (a : Γ(B.X, ⊤)) :
    g U (resG B'.X le_top (f.f.appTop a)) = cstBp U a := by
  rw [cstBp, ← k.2.2.2.1]
  congr 1
  exact (ConcreteCategory.congr_hom (f.f.naturality (homOfLE (le_top : U.1 ≤ ⊤)).op) a).symm

theorem IsCov.isAffineOpen (k : IsCov f g) (U : AffOp B.X) : IsAffineOpen (f.f ⁻¹ᵁ U.1) :=
  haveI := k.2.1
  U.2.1.preimage f.f

theorem IsDown.fits {U : AffOp B.X} {S : Set (Γ(Om.V, U.1) × (C U).L 0)} {D : ChainUp p h o Lie Om π γ f (f.f ⁻¹ᵁ U.1)}
    (k : IsDown C f g U S D) {E : ℕ → B'.X.Modules} {ι : ∀ n, E n ⟶ freeModule B'.X (Fin h)} (hι : IsLatOf C f g ι) :
    Fits ι D := fun n hn => by
  obtain ⟨l, m, -, -, -, h1, -⟩ := k
  ext x
  rw [h1 n hn, ((hι n).2.2 U).1, min_eq_left hn]
  rfl

variable (C f g)

def JUp (U : AffOp B.X) {E : B'.X.Modules} (ι : E ⟶ freeModule B'.X (Fin h)) {Q : B'.X.Modules} (t : E ⟶ Q)
    (j : (Scheme.Modules.pullback f.f).obj Lie.V ⟶ Q) : Prop :=
  ∀ s : Γ(Lie.V, U.1), ∃ (x : Γ(E, f.f ⁻¹ᵁ U.1)) (y : (C U).L 0), y.1 = piMap (g U) (Fin h) (crd ι _ x) ∧
    (C U).j (1 ⊗ₜ s) = Submodule.Quotient.mk y ∧ j.app _ (pullbackSections f.f Lie.V le_rfl s) = t.app _ x

def RUp (U : AffOp B.X) {E : B'.X.Modules} (ι : E ⟶ freeModule B'.X (Fin h)) {Q : B'.X.Modules} (t : E ⟶ Q)
    (ρ : (Scheme.Modules.pullback f.f).obj Om.V ⟶ Q) : Prop :=
  ∀ s : Γ(Om.V, U.1), ∃ (x : Γ(E, f.f ⁻¹ᵁ U.1)) (y : (C U).L 0), y.1 = piMap (g U) (Fin h) (crd ι _ x) ∧
    (C U).ρ (1 ⊗ₜ s) = Submodule.Quotient.mk (Submodule.Quotient.mk y) ∧
      ρ.app _ (pullbackSections f.f Om.V le_rfl s) = t.app _ x

end Cover

end GlobalTheory.ChainDesc

end
