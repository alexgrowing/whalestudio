import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PerCApply

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR

namespace UpperTheory.Gal.W2

def TanDeriv : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Y : Scheme.{0}) (s' : Y ⟶ Sp ℂ) (B : Set V) (s : V → (Sp ℂ ⟶ Y)) (v₀ : V), IsOpen B → v₀ ∈ B →
    IsHolTo B s → (∀ v ∈ B, s v ≫ s' = spMap (RingHom.id ℂ)) → ∀ y : CxPts s' (RingHom.id ℂ), y.1 = s v₀ →
    ∀ W : Y.Opens, y ∈ CxPts.ptsIn s' (RingHom.id ℂ) W → ∃ ψ : Ω[Sec s' W⁄ℂ] →ₗ[ℂ] (V →L[ℂ] ℂ),
      (∀ (b : Sec s' W) (ω : Ω[Sec s' W⁄ℂ]), ψ (b • ω) = CxPts.ev s' (RingHom.id ℂ) W b y • ψ ω) ∧
      ∀ b : Sec s' W, ψ (KaehlerDifferential.D ℂ (Sec s' W) b) = fderiv ℂ (fun v => valAt' (s v) W b) v₀

def FlatAffine : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Y : Scheme.{0}) (B : Set V) (s : V → (Sp ℂ ⟶ Y)) (v₀ w : V), IsOpen B → v₀ ∈ B → IsHolTo B s →
    ∀ W : Y.Opens, IsAffineOpen W → ⊤ ≤ s v₀ ⁻¹ᵁ W →
    (∀ f : Γ(Y, W), fderiv ℂ (fun v => valAt' (s v) W f) v₀ w = 0) → Flat s v₀ w

def ConjCharpoly : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (d : ℕ), Module.finrank ℂ V = d →
    ∀ (τ : V →ₗ[ℂ] (Fin d → ℂ)) (G : V →ₗ[ℂ] V) (A : Matrix (Fin d) (Fin d) ℂ), Function.Injective τ →
    (∀ w, τ (G w) = A *ᵥ τ w) → A.charpoly = G.charpoly

def TanChart : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (d : ℕ), Module.finrank ℂ V = d → ∀ (Z Y : Scheme.{0}) (sZ : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ)
    (c₁ c₂ : Y ⟶ Z) (h₁ : c₁ ≫ sZ = s') (h₂ : c₂ ≫ sZ = s') (B : Set V) (s : V → (Sp ℂ ⟶ Y)) (v₀ : V), IsOpen B → v₀ ∈ B →
    IsHolTo B s → (∀ v ∈ B, s v ≫ s' = spMap (RingHom.id ℂ)) → (∀ w, Flat s v₀ w → w = 0) →
    ∀ (G : V → V) (G' : V →L[ℂ] V), HasFDerivAt G G' v₀ → G v₀ = v₀ → (∀ᶠ v in 𝓝 v₀, s v ≫ c₂ = s (G v) ≫ c₁) →
    ∀ y : CxPts s' (RingHom.id ℂ), y.1 = s v₀ → ∀ A, GlobalTheory.W1.IsTan d c₁ c₂ h₁ h₂ y A → A.charpoly = (G' : V →ₗ[ℂ] V).charpoly

def TanExists : Prop :=
  ∀ (Z Y : Scheme.{0}) (sZ : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (d : ℕ), SmoothOfRelativeDimension d sZ →
    ∀ (c₁ c₂ : Y ⟶ Z) (h₁ : c₁ ≫ sZ = s') (h₂ : c₂ ≫ sZ = s'), Etale c₁ → ∀ y : CxPts s' (RingHom.id ℂ),
    y.1 ≫ c₁ = y.1 ≫ c₂ → ∃ A, GlobalTheory.W1.IsTan d c₁ c₂ h₁ h₂ y A

def FlatComp : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Y Y' : Scheme.{0}) (f : Y ⟶ Y') (s : V → (Sp ℂ ⟶ Y)) (v₀ w : V), Flat s v₀ w → Flat (fun v => s v ≫ f) v₀ w

def FlatPre : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (V' : Type) [NormedAddCommGroup V'] [NormedSpace ℂ V'] (Y : Scheme.{0}) (B : Set V) (s : V → (Sp ℂ ⟶ Y)),
    IsHolTo B s → ∀ (φ : V' → V) (φ' : V' →L[ℂ] V) (v₀ w : V'), HasFDerivAt φ φ' v₀ → φ v₀ ∈ B →
    (Flat (fun v => s (φ v)) v₀ w ↔ Flat s (φ v₀) (φ' w))

def PbFlat : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (P Y₁ Y₂ T : Scheme.{0}) (p₁ : P ⟶ Y₁) (p₂ : P ⟶ Y₂) (f₁ : Y₁ ⟶ T) (f₂ : Y₂ ⟶ T), IsPullback p₁ p₂ f₁ f₂ →
    ∀ (B : Set V) (s : V → (Sp ℂ ⟶ P)) (v₀ w : V), IsOpen B → v₀ ∈ B → IsHolTo B (fun v => s v ≫ p₁) →
    IsHolTo B (fun v => s v ≫ p₂) → Flat (fun v => s v ≫ p₁) v₀ w → Flat (fun v => s v ≫ p₂) v₀ w → Flat s v₀ w

def ExpImm0 : Prop :=
  ∀ (X : Scheme.{0}) (A : Over X) [GrpObj A] (g : ℕ) (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ A)), IsExp y e →
    ∀ w, Flat (fun z => (e z).left) 0 w → w = 0

def ExpImm : Prop :=
  ∀ (X : Scheme.{0}) (A : Over X) [GrpObj A] (g : ℕ) (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ A)), IsExp y e →
    ∀ z₀ w, Flat (fun z => (e z).left) z₀ w → w = 0

def HolPi : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (X : Scheme.{0}) (A : Over X) (k : ℕ) (B : Set V) (s : V → (Sp ℂ ⟶ (GlobalTheory.KS.pow A k).left)), IsOpen B →
    IsHolTo B (fun v => s v ≫ (GlobalTheory.KS.pow A k).hom) → (∀ j, IsHolTo B (fun v => s v ≫ (GlobalTheory.KS.pr A j).left)) → IsHolTo B s

def PerNear : Prop :=
  ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)) (M₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → IsHermOf D P₀ M₀ →
    ∀ (d : ℕ) (co : (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ), (∀ b, co b ∈ Csp bar ρ M₀) →
    ∃ B : Set (Fin d → ℂ), IsOpen B ∧ 0 ∈ B ∧ IsHolPeriods D ρ B (fun b => perC P₀ (co b))

def PerCoordLoc : Prop :=
  ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)) (M₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → IsHermOf D P₀ M₀ →
    ∀ (d : ℕ) (co : (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ), IsCoordC bar ρ M₀ co →
    ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))) (b₀ : Fin m → ℂ), IsOpen B → b₀ ∈ B →
    IsHolPeriods D ρ B P → P b₀ = P₀ → ∃ c : (Fin m → ℂ) → (Fin d → ℂ), DifferentiableAt ℂ c b₀ ∧ c b₀ = 0 ∧
      ∀ᶠ b in 𝓝 b₀, ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, P b x = h (perC P₀ (co (c b)) x)

def PerLin : Prop :=
  ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar) (P P' : D.La →+ (Fin g → ℂ)) (H : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P → H.det ≠ 0 →
    (∀ a, ρ a * H = H * ρ a) → (∀ x, P' x = H *ᵥ P x) → IsPeriod D ρ P'

def AdExists : Prop :=
  ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)) (M₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → IsHermOf D P₀ M₀ →
    ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), FixesPer D P₀ ga H →
    H.det ≠ 0 ∧ (∀ a, ρ a * H = H * ρ a) ∧ ∀ C ∈ Csp bar ρ M₀, H * C * (H.map star)⁻¹ ∈ Csp bar ρ M₀

def BaseImm : Prop :=
  ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar) (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (A : Over X) [GrpObj A] (S : Sheet s A D ρ) (d : ℕ), SmoothOfRelativeDimension d s →
    ∀ (P₀ : D.La →+ (Fin g → ℂ)) (M₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → IsHermOf D P₀ M₀ →
    ∀ co : (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ, IsCoordC bar ρ M₀ co →
    ∀ w, Flat (fun b => S.u (perC P₀ (co b))) 0 w → w = 0

def PtHol : Prop :=
  ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar) (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (A : Over X) [GrpObj A] (S : Sheet s A D ρ) (k m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))), IsOpen B → IsHolPeriods D ρ B P →
    IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) => S.pt k (P bz.1) bz.2)

def PtImm : Prop :=
  ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar) (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (A : Over X) [GrpObj A] (S : Sheet s A D ρ) (k m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))) (b₀ : Fin m → ℂ), IsOpen B → b₀ ∈ B →
    IsHolPeriods D ρ B P → (∀ w, Flat (fun b => S.u (P b)) b₀ w → w = 0) → ∀ (z₀ : Fin k → Fin g → ℂ) w,
    Flat (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) => S.pt k (P bz.1) bz.2) (b₀, z₀) w → w = 0

def PtFibre : Prop :=
  ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar) (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (A : Over X) [GrpObj A] (S : Sheet s A D ρ) (k : ℕ) (P : D.La →+ (Fin g → ℂ)), IsPeriod D ρ P →
    (∀ z, S.pt k P z ≫ (GlobalTheory.KS.pow A k).hom = S.u P) ∧ (∀ z j, S.pt k P z ≫ (GlobalTheory.KS.pr A j).left = (S.ex P (z j)).left) ∧
    (∀ y : Sp ℂ ⟶ (GlobalTheory.KS.pow A k).left, y ≫ (GlobalTheory.KS.pow A k).hom = S.u P → ∃ z, y = S.pt k P z) ∧
    (∀ z z', S.pt k P z = S.pt k P z' ↔ ∀ j, z j - z' j ∈ P.range) ∧
    ∀ P' (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), IsPeriod D ρ P' → (∀ x, P' x = h (P x)) →
      ∀ z, S.pt k P' (fun j => h (z j)) = S.pt k P z

def TriCharpoly : Prop :=
  ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (T : V →ₗ[ℂ] V) (Θ : W →ₗ[ℂ] W) (R : V →ₗ[ℂ] W) (G : V × W →ₗ[ℂ] V × W), (∀ v w, G (v, w) = (T v, Θ w + R v)) →
    G.charpoly = T.charpoly * Θ.charpoly

def DetOfCharpoly : Prop :=
  ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (T : V →ₗ[ℂ] V) (Θ : W →ₗ[ℂ] W) (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ), A.charpoly = T.charpoly * Θ.charpoly →
    ∀ y : ℂ, (1 - y • A).det = LinearMap.det (1 - y • T) * LinearMap.det (1 - y • Θ)

def CorrChart : Prop :=
  ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar) (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (A : Over X) [GrpObj A] (S : Sheet s A D ρ) (k : ℕ) (Z : Scheme.{0}) (c₁ c₂ : (GlobalTheory.KS.pow A k).left ⟶ Z)
    (P₀ : D.La →+ (Fin g → ℂ)) (M₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → IsHermOf D P₀ M₀ →
    ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), FixesPer D P₀ ga H →
    ∀ L : (Fin k → Fin g → ℂ) →ₗ[ℂ] (Fin k → Fin g → ℂ), CorrEq S c₁ c₂ ga L →
    ∀ C : Matrix (Fin g) (Fin g) ℂ, IsPeriod D ρ (perC P₀ C) → IsPeriod D ρ (perC P₀ (H * C * (H.map star)⁻¹)) →
    ∀ z, S.pt k (perC P₀ C) z ≫ c₂ = S.pt k (perC P₀ (H * C * (H.map star)⁻¹)) (fibMap H L z) ≫ c₁

def LocTan : Prop :=
  ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar) (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (A : Over X) [GrpObj A] (S : Sheet s A D ρ) (d : ℕ), SmoothOfRelativeDimension d s → ∀ (k : ℕ) (Z : Scheme.{0}) (sZ : Z ⟶ Sp ℂ)
    (c₁ c₂ : (GlobalTheory.KS.pow A k).left ⟶ Z) (h₁ : c₁ ≫ sZ = (GlobalTheory.KS.pow A k).hom ≫ s) (h₂ : c₂ ≫ sZ = (GlobalTheory.KS.pow A k).hom ≫ s)
    (P₀ : D.La →+ (Fin g → ℂ)) (M₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → IsHermOf D P₀ M₀ →
    ∀ co : (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ, IsCoordC bar ρ M₀ co →
    ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), FixesPer D P₀ ga H →
    ∀ T : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ), (∀ b, co (T b) = H * co b * (H.map star)⁻¹) →
    ∀ L : (Fin k → Fin g → ℂ) →ₗ[ℂ] (Fin k → Fin g → ℂ), CorrEq S c₁ c₂ ga L →
    ∀ z₀ : Fin k → Fin g → ℂ, (∀ j, fibMap H L z₀ j - z₀ j ∈ P₀.range) →
    ∀ y : CxPts ((GlobalTheory.KS.pow A k).hom ≫ s) (RingHom.id ℂ), y.1 = S.pt k P₀ z₀ →
    ∀ At, GlobalTheory.W1.IsTan (d + k * g) c₁ c₂ h₁ h₂ y At → At.charpoly = T.charpoly * (fibMap H L).charpoly

def TorusCount : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (Λ : AddSubgroup W),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set W) = ⊤ → ∀ Θ : W →ₗ[ℂ] W, (∀ z ∈ Λ, Θ z ∈ Λ) →
    LinearMap.det (1 - Θ) ≠ 0 → ∃ Fz : Finset W, (∀ z ∈ Fz, Θ z - z ∈ Λ) ∧
      (∀ z, Θ z - z ∈ Λ → ∃! z', z' ∈ Fz ∧ z - z' ∈ Λ) ∧
      (Fz.card : ℂ) = LinearMap.det (1 - Θ) * (starRingEnd ℂ) (LinearMap.det (1 - Θ))

def DetReal : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (f : W →ₗ[ℂ] W),
    ((LinearMap.det (f.restrictScalars ℝ) : ℝ) : ℂ) = LinearMap.det f * (starRingEnd ℂ) (LinearMap.det f)

def PiLattice : Prop :=
  ∀ (g k : ℕ) (Λ : AddSubgroup (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    DiscreteTopology (AddSubgroup.pi (Set.univ : Set (Fin k)) fun _ => Λ) ∧
    Submodule.span ℝ ((AddSubgroup.pi (Set.univ : Set (Fin k)) fun _ => Λ : AddSubgroup (Fin k → Fin g → ℂ)) : Set (Fin k → Fin g → ℂ)) = ⊤

def LocSum : Prop :=
  ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar) (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (A : Over X) [GrpObj A] (S : Sheet s A D ρ) (d : ℕ), SmoothOfRelativeDimension d s → ∀ (k : ℕ) (Z : Scheme.{0}) (sZ : Z ⟶ Sp ℂ)
    (c₁ c₂ : (GlobalTheory.KS.pow A k).left ⟶ Z) (h₁ : c₁ ≫ sZ = (GlobalTheory.KS.pow A k).hom ≫ s) (h₂ : c₂ ≫ sZ = (GlobalTheory.KS.pow A k).hom ≫ s)
    (P₀ : D.La →+ (Fin g → ℂ)) (M₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → IsHermOf D P₀ M₀ →
    ∀ co : (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ, IsCoordC bar ρ M₀ co →
    ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), FixesPer D P₀ ga H →
    ∀ T : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ), (∀ b, co (T b) = H * co b * (H.map star)⁻¹) →
    ∀ L : (Fin k → Fin g → ℂ) →ₗ[ℂ] (Fin k → Fin g → ℂ), CorrEq S c₁ c₂ ga L →
    (∀ z : Fin k → Fin g → ℂ, (∀ j, z j ∈ P₀.range) → ∀ j, fibMap H L z j ∈ P₀.range) →
    (∀ z z', S.pt k P₀ z ≫ c₁ = S.pt k P₀ z' ≫ c₁ → S.pt k P₀ z = S.pt k P₀ z') →
    LinearMap.det (1 - T) ≠ 0 → LinearMap.det (1 - fibMap H L) ≠ 0 →
    ∃ Fx : Finset (CxPts ((GlobalTheory.KS.pow A k).hom ≫ s) (RingHom.id ℂ)),
      (∀ y, y ∈ Fx ↔ y.1 ≫ (GlobalTheory.KS.pow A k).hom = S.u P₀ ∧ y.1 ≫ c₁ = y.1 ≫ c₂) ∧
      ∀ At : CxPts ((GlobalTheory.KS.pow A k).hom ≫ s) (RingHom.id ℂ) → Matrix (Fin (d + k * g)) (Fin (d + k * g)) ℂ,
        (∀ y ∈ Fx, GlobalTheory.W1.IsTan (d + k * g) c₁ c₂ h₁ h₂ y (At y)) → (∀ y ∈ Fx, (1 - At y).det ≠ 0) ∧
        ∀ t : ℂ, ∑ y ∈ Fx, lefTerm (At y) t = LinearMap.det (1 - t • T) / LinearMap.det (1 - T) *
          (LinearMap.det (1 - t • fibMap H L) * (starRingEnd ℂ) (LinearMap.det (1 - fibMap H L)))

end UpperTheory.Gal.W2
