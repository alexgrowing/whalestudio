import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutsSecOfIsLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalModelLettersPresentation

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
open GlobalTheory.GroupBplus (AffOp IsPropG TorsionMap Tors)
open GlobalTheory.RingChain (RChain IsOf)
open GlobalTheory.LineNorm (IsTanBasis)
open GlobalTheory.OmegaHT (crd ToOpen)
open GlobalTheory.PDivGroup (muRoot omegaMap tateMap dualHom dlog)
open GlobalTheory.PerfdLat (PrismData ConstTate eps dualBaseChange bcTate piMap)
open GlobalTheory.Published (CycPerfd)
open scoped TensorProduct Pointwise

namespace GlobalTheory.ChainPts.SysB

section Ring

variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] {GG : PDivGroup p A}

def polBC (pol : GG ≅ GG.dual) (R : Type) [CommRing R] [Algebra A R] : GG.baseChange R ⟶ (GG.baseChange R).dual :=
  PDivGroup.baseChangeMap R pol.hom ≫ (dualBaseChange R GG).inv

def IsLevels {M : Type} [AddCommGroup M] [Module A M] (c : M →ₗ[A] GG.omega) : Prop :=
  (∀ n, Function.Surjective fun w => (c w).1 n) ∧ ∀ n w, (c w).1 n = 0 ↔ ∃ w', w = (p : A) ^ n • w'

def IsChainOf (D : PrismData p) (pol : GG ≅ GG.dual) {ε : (PDivGroup.mu p A).Tate} (c : ConstTate ε GG) {h o : ℕ}
    (e : GG.height = h) {π : A} {γ : ℕ → A} {Lie Om : Type} [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om]
    (cω : Om →ₗ[A] GG.omega) (pr : Lie →ₗ[A] Module.Dual A Om) (C : RChain p A h o π γ Lie Om) : Prop :=
  ¬ IsUnit (p : A) → ∃ (S : CycPerfd p) (_ : Algebra A S.R) (ec : AdicCompletion (Ideal.span {(p : A)}) A ≃+* S.R)
    (_ : ∀ a, ec (algebraMap A _ a) = algebraMap A S.R a) (hε : ∀ n, muRoot (eps S) n = algebraMap A S.R (muRoot ε n))
    (eL : S.R ⊗[A] Lie ≃ₗ[S.R] (GG.baseChange S.R).Lie) (eO : S.R ⊗[A] Om ≃ₗ[S.R] (GG.baseChange S.R).dual.omega),
    (∀ y w, eL (1 ⊗ₜ y) ((GG.toBase S.R).omega (cω w)) = algebraMap A S.R (pr y w)) ∧
    (∀ w, omegaMap _ _ (polBC pol S.R) (eO (1 ⊗ₜ w)) = (GG.toBase S.R).omega (cω w)) ∧
    IsOf D (c.baseChange S.R hε) e (fun y => eL (1 ⊗ₜ y)) (fun w => eO (1 ⊗ₜ w)) C

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

def ct {t : SAB H (Sp A)} {act : PDivGroup.Action (𝓞 E) GG} {pol : GG ≅ GG.dual} {θ : TorsionMap t.G GG}
    {ε : (PDivGroup.mu p A).Tate} {τ : Dw.La →+ GG.Tate} (hP : IsPropG Dw t GG act pol θ ε τ) {n : ℕ} (e : GG.height = n)
    (b : Module.Basis (Fin n) ℤ Dw.La) : ConstTate ε GG :=
  hP.constTate (b.reindex (finCongr e.symm))

def actMat {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ :=
  (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom.comp (Module.toModuleEnd ℤ Dw.La)

theorem actMat_apply {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) (a : 𝓞 E) (k i : Fin n) :
    actMat b a k i = b.repr (a • b i) k := LinearMap.toMatrixAlgEquiv_apply b _ k i

def IsDlog {ε : (PDivGroup.mu p A).Tate} (c : ConstTate ε GG) {n : ℕ} (e : GG.height = n) {M : Type} [AddCommGroup M]
    [Module A M] (cω : M →ₗ[A] GG.omega) (η : Fin n → M) : Prop :=
  ∀ j, (cω (η j)).1 1 = (dlog GG (c.t' (Fin.cast e.symm j))).1 1

end Ring

section Form

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def FormLink (Z : LocM.Mdl Y i₀) {X : Scheme.{0}} [IsIntegral X] (h : X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw)
    {F : X.Modules} {s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)} (hs : ∀ a, GlobalTheory.VB.IsFrame (s a)) (U : AffOp X)
    {t : SAB H (Sp U.Bp)} (φt : t.G.left ⟶ (Y Z.i).t.G.left)
    (lam : U.Bp ⊗[Γ(X, U.1)] Γ(F, U.1) →ₗ[U.Bp] Pdiv.omega t.G) : Prop :=
  ∀ (σ : Γ(F, U.1)) (v : Pdiv.LieG t.G) (k : Type) [Field k] (κ : U.Bp →+* k) (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k),
    spMap φ ≫ Z.chart a = spMap κ ≫ U.toX ≫ h → ∀ cf : Fin r → k,
      IsCombAtG (Y Z.i).t (spMap κ ≫ U.toX ≫ h ≫ Z.π) (fun i => (Z.fr a).bc φ (x i).1 (x i).2) cf
        (spMap (dualMap κ) ≫ v.1.left ≫ φt) →
      κ ((lam (1 ⊗ₜ σ)).1 v) = ∑ i, cf i * valF (spMap κ ≫ U.toX) _ (crd (hs a) σ i)

end Form

def RingExSt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : PrismData p) (A K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K]
    [IsAlgClosed K] [CharZero K] [Algebra A K] [IsFractionRing A K] (GG : PDivGroup p A) (pol : GG ≅ GG.dual)
    (ε : (PDivGroup.mu p A).Tate) (c : ConstTate ε GG) (h o : ℕ) (e : GG.height = h) (π : A) (γ : ℕ → A) (Lie Om : Type)
    [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om] [Module.Finite A Lie] [Module.Projective A Lie]
    [Module.Finite A Om] [Module.Projective A Om] (cω : Om →ₗ[A] GG.omega) (pr : Lie →ₗ[A] Module.Dual A Om),
    (∀ n, IsPrimitiveRoot (muRoot ε n) (p ^ n)) → IsLevels cω → Function.Bijective pr → π = muRoot ε 1 - 1 →
    (∀ k ≤ o, γ k = ∑ i ∈ Finset.range p, muRoot ε (k + 2) ^ i) →
    ∃ C : RChain p A h o π γ Lie Om, IsChainOf D pol c e cω pr C

def RingResSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (D : PrismData p)
    (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (t : SAB H (Sp A)) (GG : PDivGroup p A)
    (act : PDivGroup.Action (𝓞 E) GG) (pol : GG ≅ GG.dual) (θ : TorsionMap t.G GG) (ε : (PDivGroup.mu p A).Tate)
    (τ : Dw.La →+ GG.Tate) (hP : IsPropG Dw t GG act pol θ ε τ) (t' : SAB H (Sp A')) (GG' : PDivGroup p A')
    (act' : PDivGroup.Action (𝓞 E) GG') (pol' : GG' ≅ GG'.dual) (θ' : TorsionMap t'.G GG') (ε' : (PDivGroup.mu p A').Tate)
    (τ' : Dw.La →+ GG'.Tate) (hP' : IsPropG Dw t' GG' act' pol' θ' ε' τ') (n o : ℕ) (e : GG.height = n) (e' : GG'.height = n)
    (b : Module.Basis (Fin n) ℤ Dw.La) (π : A) (γ : ℕ → A) (π' : A') (γ' : ℕ → A') (Lie Om Lie' Om' : Type)
    [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om] [AddCommGroup Lie'] [Module A' Lie'] [AddCommGroup Om']
    [Module A' Om'] (cω : Om →ₗ[A] GG.omega) (pr : Lie →ₗ[A] Module.Dual A Om) (cω' : Om' →ₗ[A'] GG'.omega)
    (pr' : Lie' →ₗ[A'] Module.Dual A' Om') (C : RChain p A n o π γ Lie Om) (C' : RChain p A' n o π' γ' Lie' Om')
    (f : GG' ≅ GG.baseChange A') (l : Lie → Lie') (m : Om → Om'),
    IsChainOf D pol (ct hP e b) e cω pr C → IsChainOf D pol' (ct hP' e' b) e' cω' pr' C' →
    (∀ k, muRoot ε' k = algebraMap A A' (muRoot ε k)) →
    pol'.hom ≫ dualHom _ _ f.inv ≫ (dualBaseChange A' GG).hom = f.hom ≫ PDivGroup.baseChangeMap A' pol.hom →
    (∀ x, tateMap _ _ A' f.hom (τ' x) = bcTate A' (τ x)) →
    (∀ w, cω' (m w) = omegaMap _ _ f.hom ((GG.toBase A').omega (cω w))) →
    (∀ y w, pr' (l y) (m w) = algebraMap A A' (pr y w)) → π ∣ (p : A) → π' = algebraMap A A' π →
    (∀ k, C'.L k = Submodule.span A' (piMap (algebraMap A A') (Fin n) '' (C.L k : Set (Fin n → A)))) ∧
      C.Map C' (algebraMap A A') 1 l m

def RingActSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (D : PrismData p)
    (A : Type) [CommRing A] (t : SAB H (Sp A)) (GG : PDivGroup p A)
    (act : PDivGroup.Action (𝓞 E) GG) (pol : GG ≅ GG.dual) (θ : TorsionMap t.G GG) (ε : (PDivGroup.mu p A).Tate)
    (τ : Dw.La →+ GG.Tate) (hP : IsPropG Dw t GG act pol θ ε τ) (n o : ℕ) (e : GG.height = n)
    (b : Module.Basis (Fin n) ℤ Dw.La) (π : A) (γ : ℕ → A) (Lie Om : Type)
    [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om] (cω : Om →ₗ[A] GG.omega)
    (pr : Lie →ₗ[A] Module.Dual A Om) (C : RChain p A n o π γ Lie Om) (a : 𝓞 E) (l : Lie → Lie) (m m' : Om → Om),
    IsChainOf D pol (ct hP e b) e cω pr C →
    (∀ w, cω (m w) = omegaMap GG GG (act (H.bar a)) (cω w)) → (∀ w, cω (m' w) = omegaMap GG GG (act a) (cω w)) →
    (∀ y w, pr (l y) w = pr y (m' w)) → π ∣ (p : A) → C.Map C (RingHom.id A) (actMat b a) l m

def RingJSt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : PrismData p) (A : Type) [CommRing A] (GG : PDivGroup p A) (pol : GG ≅ GG.dual)
    (ε : (PDivGroup.mu p A).Tate) (c : ConstTate ε GG) (n o : ℕ) (e : GG.height = n) (π : A) (γ : ℕ → A) (Lie Om : Type)
    [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om] (cω : Om →ₗ[A] GG.omega)
    (pr : Lie →ₗ[A] Module.Dual A Om) (C : RChain p A n o π γ Lie Om) (η : Fin n → Om),
    IsChainOf D pol c e cω pr C → IsLevels cω → IsDlog c e cω η → π ∣ (p : A) →
    ∀ (y : Lie) (x : C.L 0), C.j y = Submodule.Quotient.mk x ↔ ∀ j, π ∣ x.1 j - pr y (η j)

def RingRSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (D : PrismData p)
    (A : Type) [CommRing A] (t : SAB H (Sp A)) (GG : PDivGroup p A)
    (act : PDivGroup.Action (𝓞 E) GG) (pol : GG ≅ GG.dual) (θ : TorsionMap t.G GG) (ε : (PDivGroup.mu p A).Tate)
    (τ : Dw.La →+ GG.Tate) (hP : IsPropG Dw t GG act pol θ ε τ) (n o : ℕ) (e : GG.height = n)
    (b : Module.Basis (Fin n) ℤ Dw.La) (π : A) (γ : ℕ → A) (Lie Om : Type)
    [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om] [Module.Finite A Om] [Module.Projective A Om]
    (cω : Om →ₗ[A] GG.omega) (pr : Lie →ₗ[A] Module.Dual A Om) (C : RChain p A n o π γ Lie Om) (η : Fin n → Om),
    IsChainOf D pol (ct hP e b) e cω pr C → IsLevels cω → IsDlog (ct hP e b) e cω η → π ∣ (p : A) →
    ∀ w : Om, C.ρ w = 0 ↔ w ∈ Submodule.span A (Set.range η) ⊔ (p : A) • (⊤ : Submodule A Om)

def KerRSt : Prop :=
  ∀ (p : ℕ) (A : Type) [CommRing A] (n o : ℕ) (π : A) (γ : ℕ → A) (Lie Om : Type) [AddCommGroup Lie] [Module A Lie]
    [AddCommGroup Om] [Module A Om] (C : RChain p A n o π γ Lie Om) (R : Type) [CommRing R] [IsDomain R] (φ : A →+* R),
    φ π ≠ 0 → ∀ (r : ℕ) (f : Module.Basis (Fin r) A Om),
      C.kerR φ f = (Submodule.span R {v : Fin r → R | ∃ w, C.ρ w = 0 ∧ v = fun l => φ (f.repr w l)} : Set (Fin r → R))

def OmegaResSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (tX : SAB H X)
    (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (x : Sp A ⟶ X) (t : SAB H (Sp A)) (t' : SAB H (Sp A'))
    (φ : t.G.left ⟶ tX.G.left) (φ' : t'.G.left ⟶ tX.G.left), IsGrpPullback t.G tX.G x φ →
    IsGrpPullback t'.G tX.G (spMap (algebraMap A A') ≫ x) φ' →
    ∀ (GG : PDivGroup p A) (GG' : PDivGroup p A') (θ : TorsionMap t.G GG) (θ' : TorsionMap t'.G GG')
      (c : Pdiv.omega t.G →ₗ[A] GG.omega) (c' : Pdiv.omega t'.G →ₗ[A'] GG'.omega) (f : GG' ≅ GG.baseChange A'),
      θ.IsOmega c → θ'.IsOmega c' →
      (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra A B] [Algebra A' B] [IsScalarTower A A' B]
        (z : Tors t.G (p ^ n) B) (z' : Tors t'.G (p ^ n) B), z.1.left ≫ φ = z'.1.left ≫ φ' →
          ∀ a, θ.pt n B z a = θ'.pt n B z' (f.hom.app n (1 ⊗ₜ a))) →
      ∀ (w : Pdiv.omega t.G) (w' : Pdiv.omega t'.G),
        (∀ (v : Pdiv.LieG t.G) (v' : Pdiv.LieG t'.G), v'.1.left ≫ φ' = spMap (dualMap (algebraMap A A')) ≫ v.1.left ≫ φ →
          w'.1 v' = algebraMap A A' (w.1 v)) →
        c' w' = omegaMap _ _ f.hom ((GG.toBase A').omega (c w))

def HTSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (X : Scheme.{0})
    [IsLocallyNoetherian X] (tX : SAB H X), X.IsSeparated → ∀ (A : Type) [CommRing A] [IsDomain A] (x : Sp A ⟶ X) (t : SAB H (Sp A))
    (φ : t.G.left ⟶ tX.G.left), IsGrpPullback t.G tX.G x φ → ∀ (GG : PDivGroup p A)
    (act : PDivGroup.Action (𝓞 E) GG) (pol : GG ≅ GG.dual) (θ : TorsionMap t.G GG) (ε : (PDivGroup.mu p A).Tate)
    (τ : Dw.La →+ GG.Tate) (hP : IsPropG Dw t GG act pol θ ε τ) (n : ℕ) (e : GG.height = n)
    (b : Module.Basis (Fin n) ℤ Dw.La) (c : Pdiv.omega t.G →ₗ[A] GG.omega), θ.IsOmega c →
    ∀ (η : Fin n → Pdiv.omega t.G), IsDlog (ct hP e b) e c η → ∀ (g : ℕ) (u : Fin g → Pdiv.LieG t.G),
    IsTanBasis tX x (fun i => (u i).1.left ≫ φ) → ∀ (C : SCF p) (κ : A →+* ↥(intO ↥C.S)),
    Set.range (spMap ((intO ↥C.S).subtype.comp κ) ≫ x) ⊆ abLocus tX.G →
    ∀ (a : Fin g → ↥C.S) (v : Sp (DualNumber ↥C.S) ⟶ tX.G.left),
      IsCombAtG tX (spMap ((intO ↥C.S).subtype.comp κ) ≫ x)
        (fun i => spMap (dualMap ((intO ↥C.S).subtype.comp κ)) ≫ (u i).1.left ≫ φ) a v →
      (v ∈ latHT tX p (spMap ((intO ↥C.S).subtype.comp κ) ≫ x) ↔
        (∀ j, ‖∑ i, (κ ((η j).1 (u i)) : ↥C.S) * a i‖ ≤ 1) ∧ ∀ i, ‖(p : ↥C.S) * a i‖ ≤ 1)

def RootSt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : Vert.Model O) (p : ℕ) [Fact p.Prime] (o : ℕ)
    (ζ : Γ(B.X, ⊤)) (z : ∀ U : AffOp B.X, ℕ → U.Bp), IsPrimitiveRoot ζ (p ^ (o + 2)) →
    (∀ U n, IsPrimitiveRoot (z U n) (p ^ n)) →
    (∀ (U U' : AffOp B.X) (hle : U'.1 ≤ U.1) (n : ℕ), z U' n = AffOp.res hle (z U n)) →
    ∃ (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)), IsRootOfP p π (p - 1) ∧ (∀ k ≤ o, IsRootOfP p (γ k) (p ^ (k + 1))) ∧
      ∀ U, cstBp U π = z U 1 - 1 ∧ ∀ k ≤ o, cstBp U (γ k) = ∑ i ∈ Finset.range p, z U (k + 2) ^ i

def PairSt : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (F : X.Modules) (r : ℕ), GlobalTheory.VB.IsVB F r → ∀ U : AffOp X,
    Module.Finite U.Bp (U.Bp ⊗[Γ(X, U.1)] Γ(F, U.1)) ∧ Module.Projective U.Bp (U.Bp ⊗[Γ(X, U.1)] Γ(F, U.1)) ∧
    ∃ pr : U.Bp ⊗[Γ(X, U.1)] Γ(GlobalTheory.VB.dual F, U.1) →ₗ[U.Bp] Module.Dual U.Bp (U.Bp ⊗[Γ(X, U.1)] Γ(F, U.1)),
      Function.Bijective pr ∧ ∀ y w, pr (1 ⊗ₜ y) (1 ⊗ₜ w) = algebraMap Γ(X, U.1) U.Bp (GlobalTheory.VB.dualApp y le_rfl w)

def ActSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ)
    (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : LocM.Mdl Y i₀) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (B : Vert.Model O) (h : B.X ⟶ Z.X) (r : ℕ) (x : Fin r → Letter Dw), Function.Bijective x →
    ∀ hfr : ∀ a, GlobalTheory.VB.IsFrame (GlobalTheory.TanSec.secX Z h x a),
      ∃ ρ : 𝓞 E →* End (GlobalTheory.VB.dual (GlobalTheory.TanSec.lieX Z h)),
        IsEqLat Z h x true (⟨GlobalTheory.VB.dual (GlobalTheory.TanSec.lieX Z h), ρ⟩ : AM B (𝓞 E)) fun a => (hfr a).coord

def FormSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ)
    (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : LocM.Mdl Y i₀) (X : Scheme.{0}) [IsIntegral X]
    (h : X ⟶ Z.X) (r : ℕ) (x : Fin r → Letter Dw), Function.Bijective x →
    ∀ (hfr : ∀ a, GlobalTheory.VB.IsFrame (GlobalTheory.TanSec.secX Z h x a)) (U : AffOp X) (t : SAB H (Sp U.Bp))
      (φt : t.G.left ⟶ (Y Z.i).t.G.left), IsGrpPullback t.G (Y Z.i).t.G (U.toX ≫ h ≫ Z.π) φt →
      ∃ lam : U.Bp ⊗[Γ(X, U.1)] Γ(GlobalTheory.VB.dual (GlobalTheory.TanSec.lieX Z h), U.1) →ₗ[U.Bp] Pdiv.omega t.G,
        Function.Bijective lam ∧ FormLink Z h x (fun a => (hfr a).dual) U φt lam

def FormResSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ)
    (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : LocM.Mdl Y i₀) (X : Scheme.{0}) [IsIntegral X]
    (h : X ⟶ Z.X) (r : ℕ) (x : Fin r → Letter Dw), Function.Bijective x → ToOpen Z h →
    ∀ (F : X.Modules) (s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)) (hs : ∀ a, GlobalTheory.VB.IsFrame (s a))
      (U U' : AffOp X) (hle : U'.1 ≤ U.1) (t : SAB H (Sp U.Bp)) (t' : SAB H (Sp U'.Bp))
      (φt : t.G.left ⟶ (Y Z.i).t.G.left) (φt' : t'.G.left ⟶ (Y Z.i).t.G.left),
      IsGrpPullback t.G (Y Z.i).t.G (U.toX ≫ h ≫ Z.π) φt → ∀ lam lam', FormLink Z h x hs U φt lam →
      FormLink Z h x hs U' φt' lam' → ∀ (σ : Γ(F, U.1)) (v : Pdiv.LieG t.G) (v' : Pdiv.LieG t'.G),
        v'.1.left ≫ φt' = spMap (dualMap (AffOp.res hle)) ≫ v.1.left ≫ φt →
          (lam' (1 ⊗ₜ resM F hle σ)).1 v' = AffOp.res hle ((lam (1 ⊗ₜ σ)).1 v)

def FormActSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ)
    (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : LocM.Mdl Y i₀) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (B : Vert.Model O) (h : B.X ⟶ Z.X) (r : ℕ) (x : Fin r → Letter Dw), Function.Bijective x →
    ToOpen Z h → ∀ (F : AM B (𝓞 E)) (s : ∀ a : Fin Z.m, Fin r → Γ(F.V, h ⁻¹ᵁ (Z.U a).1)) (k : IsEqLat Z h x true F s)
      (U : AffOp B.X) (t : SAB H (Sp U.Bp)) (φt : t.G.left ⟶ (Y Z.i).t.G.left),
      IsGrpPullback t.G (Y Z.i).t.G (U.toX ≫ h ≫ Z.π) φt →
      (∀ a, (t.act.act a).left ≫ φt = φt ≫ ((Y Z.i).t.act.act a).left) → ∀ lam, FormLink Z h x k.2.2.1.frame U φt lam →
      ∀ (a : 𝓞 E) (σ : Γ(F.V, U.1)) (v v' : Pdiv.LieG t.G), v'.1 = v.1 ≫ t.act.act (H.bar a) →
        (lam (1 ⊗ₜ (F.ρ a : F.V ⟶ F.V).app _ σ)).1 v = (lam (1 ⊗ₜ σ)).1 v'

def TanSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ)
    (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : LocM.Mdl Y i₀) (X : Scheme.{0}) [IsIntegral X]
    (h : X ⟶ Z.X) (r : ℕ) (x : Fin r → Letter Dw), Function.Bijective x →
    ∀ (F : X.Modules) (s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)) (hs : ∀ a, GlobalTheory.VB.IsFrame (s a))
      (U : AffOp X) (t : SAB H (Sp U.Bp)) (φt : t.G.left ⟶ (Y Z.i).t.G.left),
      IsGrpPullback t.G (Y Z.i).t.G (U.toX ≫ h ≫ Z.π) φt →
      ∀ lam : U.Bp ⊗[Γ(X, U.1)] Γ(F, U.1) →ₗ[U.Bp] Pdiv.omega t.G, Function.Bijective lam → FormLink Z h x hs U φt lam →
      ∀ (f : Fin r → Γ(F, U.1)), GlobalTheory.VB.IsFrame f → ∃ u : Fin r → Pdiv.LieG t.G,
        IsTanBasis (Y Z.i).t (U.toX ≫ h ≫ Z.π) (fun l => (u l).1.left ≫ φt) ∧
        (∀ l m, (lam (1 ⊗ₜ f m)).1 (u l) = if l = m then 1 else 0) ∧
        ∀ (k : Type) [Field k] (κ : U.Bp →+* k) (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k),
          spMap φ ≫ Z.chart a = spMap κ ≫ U.toX ≫ h → ∀ (cf : Fin r → k) (v : Sp (DualNumber k) ⟶ (Y Z.i).t.G.left),
            IsCombAtG (Y Z.i).t (spMap κ ≫ U.toX ≫ h ≫ Z.π) (fun i => (Z.fr a).bc φ (x i).1 (x i).2) cf v →
            IsCombAtG (Y Z.i).t (spMap κ ≫ U.toX ≫ h ≫ Z.π) (fun l => spMap (dualMap κ) ≫ (u l).1.left ≫ φt)
              (fun l => ∑ i, cf i * valF (spMap κ ≫ U.toX) _ (crd (hs a) (f l) i)) v

end GlobalTheory.ChainPts.SysB

end
