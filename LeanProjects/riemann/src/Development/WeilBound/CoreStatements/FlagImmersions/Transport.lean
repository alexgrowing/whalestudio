import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifDefs
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX

noncomputable section

namespace RootFieldNumerics

open AlgebraicGeometry CategoryTheory NumberField Filter Topology Matrix
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

def Descend : Prop :=
  ∀ (e : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (h : Y → X) (S U : Set X) (f : Y → ℂ), HoloMap B A h → IsDegreeOff A B h 1 S →
    IsOpen U → B.HoloOn (h ⁻¹' U) f → ∃ F : X → ℂ, A.HoloOn U F ∧ ∀ y, h y ∈ U → F (h y) = f y

def Biholo : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (D.p + D.q))
    (Sys : AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx),
    Or.Re.J = ⊤ → Or.Fl.deg = 1 → Ht.AmpleQ RM.y RM.A.a →
    ∃ ψ : Sys.X → Or.Re.R.X, HoloMap Sys.A Or.Re.R.A ψ ∧ (∀ x, Or.Re.π (ψ x) = x) ∧ ∀ w, ψ (Or.Re.π w) = w

def LocPer : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (n : ℕ) (V : Set (Fin n → ℂ))
    (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)), 1 ≤ D.p + D.q → IsOpen V → IsHolTo V z → (∀ t ∈ V, 𝔐.Interior (z t)) → ∀ t₀ ∈ V,
    ∃ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (R : (Fin n → ℂ) → RiemLat E g Λ) (V' : Set (Fin n → ℂ))
      (σ : CMType H ⊕ CMType H → (𝓞 E →+* ℂ)), IsOpen V' ∧ t₀ ∈ V' ∧ V' ⊆ V ∧ IsHolFam V' R ∧
      (∀ t ∈ V', 𝔐.LabVal (z t) id σ) ∧ SheetDecomposition.VecAt 𝔐 R z t₀

def Transport : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Sp ℂ ⟶ X) (g : ℕ)
    (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (A₀ : Type)
    (x : A₀ → Fin g → ℂ) (v : A₀ → (epsAt z ⟶ t.G)), R.form = R'.form → (∀ a, R'.P a = h (R.P a)) →
    FibreLatVec t z R' x v → FibreLatVec t z R (fun a => h.symm (x a)) v

def FrameVals : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y ∅ y) (z : Sp ℂ ⟶ 𝔐.X)
    (s : CMType H ⊕ CMType H) (b : Fin (labelRk D s) → 𝔐.Li), 1 ≤ D.p + D.q → 𝔐.Interior z →
    (𝔐.V s).IsFrameAt b ⟨centre z, 𝔐.all _⟩ → (∀ i, ∃ v, 𝔐.M.ValAt z (b i) v) ∧
    ∀ (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (σ : CMType H ⊕ CMType H → (𝓞 E →+* ℂ))
      (x : Fin (labelRk D s) → Fin g → ℂ) (v : Fin (labelRk D s) → (epsAt z ⟶ 𝔐.t.G)), 𝔐.LabVal z id σ →
      (∀ i, 𝔐.M.ValAt z (b i) (v i)) → FibreLatVec 𝔐.t z R x v →
      LinearIndependent ℂ x ∧ Submodule.span ℂ (Set.range x) = eigSp R.B (σ s) ∧
        𝔐.M.GramAt 𝔐.t.PP.L z b ((Real.pi : ℂ) • R.gram x) ∧ (R.gram x).PosDef

def grLog {p q : ℕ} (Γ : Matrix (Fin p) (Fin p) ℂ) (Γ' : Matrix (Fin q) (Fin q) ℂ) (k : ℕ) : ℝ :=
  if k < p then Real.log (Real.sqrt (leadMinor Γ (k + 1) / leadMinor Γ k))
  else -Real.log (Real.sqrt (leadMinor Γ' (p + q - 1 - k + 1) / leadMinor Γ' (p + q - 1 - k)))

def perMat {p q : ℕ} (Q : Matrix (Fin q) (Fin (p + q)) ℂ) (L : Matrix (Fin (p + q)) (Fin p) ℂ) :
    Matrix (Fin (p + q)) (Fin (p + q)) ℂ :=
  Matrix.of fun a b => if h : (b : ℕ) < q then (sigForm (p + q) p a : ℂ) * Q ⟨q - 1 - b, by omega⟩ a
    else L a ⟨b - q, by have := b.2; omega⟩

def MatStep : Prop :=
  ∀ (p q : ℕ) (Γ : Matrix (Fin p) (Fin p) ℂ) (Γ' : Matrix (Fin q) (Fin q) ℂ) (M : Matrix (Fin p) (Fin (p + q)) ℂ)
    (Q : Matrix (Fin q) (Fin (p + q)) ℂ) (L : Matrix (Fin (p + q)) (Fin p) ℂ), Γ.PosDef → Γ'.PosDef →
    Mᴴ * Γ * M - Qᵀ * Γ'ᵀ * Q.map (starRingEnd ℂ) = diagonal (fun a => (sigForm (p + q) p a : ℂ)) → M * L = 1 →
    InFlagDomain (p + q) p (perMat Q L) ∧
      (∀ i : Fin (p + q), stepPot (p + q) p i (perMat Q L) = ∑ k ∈ Finset.Iic i, grLog Γ Γ' k) ∧
      ∀ a b, (M * perMat Q L) a b = if (b : ℕ) = q + a then 1 else 0

def IsFrames {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} {g n p q : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (V : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ))
    (x : Ψ → Fin p → (Fin n → ℂ) → Fin g → ℂ) (x' : Ψ → Fin q → (Fin n → ℂ) → Fin g → ℂ) : Prop :=
  (∀ τ i, AnalyticOnNhd ℂ (x τ i) V) ∧ (∀ τ i, AnalyticOnNhd ℂ (x' τ i) V) ∧ ∀ t ∈ V, ∀ τ,
    (LinearIndependent ℂ (fun i => x τ i t) ∧ Submodule.span ℂ (Set.range fun i => x τ i t) = eigSp (R t).B (σ τ)) ∧
    LinearIndependent ℂ (fun i => x' τ i t) ∧
      Submodule.span ℂ (Set.range fun i => x' τ i t) = eigSp (R t).B ((starRingEnd ℂ).comp (σ τ))

def PerCoord : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (g n p q : ℕ) (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (V : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ))
    (x : Ψ → Fin p → (Fin n → ℂ) → Fin g → ℂ) (x' : Ψ → Fin q → (Fin n → ℂ) → Fin g → ℂ), IsOpen V → IsHolFam V R →
    IsCMFam σ → IsFrames V R σ x x' →
    ∃ (M : Ψ → (Fin n → ℂ) → Matrix (Fin p) (Fin (p + q)) ℂ) (Q : Ψ → (Fin n → ℂ) → Matrix (Fin q) (Fin (p + q)) ℂ)
      (cc : Ψ → Λ → Fin (p + q) → ℂ), (∀ τ a b, AnalyticOnNhd ℂ (fun t => M τ t a b) V) ∧
      (∀ τ a b, AnalyticOnNhd ℂ (fun t => Q τ t a b) V) ∧ ∀ t ∈ V,
        (∀ τ, (M τ t)ᴴ * (R t).gram (fun i => x τ i t) * M τ t -
          (Q τ t)ᵀ * ((R t).gram fun i => x' τ i t)ᵀ * (Q τ t).map (starRingEnd ℂ) =
            diagonal fun a => (sigForm (p + q) p a : ℂ)) ∧
        (∀ a, (R t).P a = ∑ τ, (∑ i, (M τ t *ᵥ cc τ a) i • x τ i t + ∑ i, (Q τ t *ᵥ star (cc τ a)) i • x' τ i t)) ∧
        LinearIndependent ℂ (Sum.elim (fun a : Ψ × Fin p => x a.1 a.2 t) fun a : Ψ × Fin q => x' a.1 a.2 t) ∧
        Submodule.span ℂ (Set.range (Sum.elim (fun a : Ψ × Fin p => x a.1 a.2 t) fun a : Ψ × Fin q => x' a.1 a.2 t)) = ⊤

def SameFl {Ψ : Type} {N : ℕ} (g g' : Ψ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ τ, ∃ T : Matrix (Fin N) (Fin N) ℂ, T.BlockTriangular id ∧ g' τ = g τ * T

def PerMat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (g n p q : ℕ) (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (V : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ))
    (x : Ψ → Fin p → (Fin n → ℂ) → Fin g → ℂ) (x' : Ψ → Fin q → (Fin n → ℂ) → Fin g → ℂ), IsOpen V → IsHolFam V R →
    IsCMFam σ → IsFrames V R σ x x' → ∀ t₀ ∈ V,
    ∃ (V' : Set (Fin n → ℂ)) (gm : Ψ → (Fin n → ℂ) → Matrix (Fin (p + q)) (Fin (p + q)) ℂ), IsOpen V' ∧ t₀ ∈ V' ∧ V' ⊆ V ∧
      (∀ τ a b, AnalyticOnNhd ℂ (fun t => gm τ t a b) V') ∧
      (∀ t ∈ V', ∀ τ, InFlagDomain (p + q) p (gm τ t) ∧ ∀ i : Fin (p + q), stepPot (p + q) p i (gm τ t) =
        ∑ k ∈ Finset.Iic i, grLog ((R t).gram fun i => x τ i t) ((R t).gram fun i => x' τ i t) k) ∧
      ∀ t ∈ V', ∀ t' ∈ V', SameFl (fun τ => gm τ t) (fun τ => gm τ t') →
        ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ a, (R t').P a = h ((R t).P a)) ∧ ∀ τ k,
          flagStep ℂ (fun i => h.symm (x τ i t')) k = flagStep ℂ (fun i => x τ i t) k ∧
          flagStep ℂ (fun i => h.symm (x' τ i t')) k = flagStep ℂ (fun i => x' τ i t) k

def RankLem : Prop :=
  ∀ (e m : ℕ) (V : Set (Fin e → ℂ)) (Φ : (Fin e → ℂ) → Fin m → ℂ), IsOpen V → V.Nonempty → AnalyticOnNhd ℂ Φ V →
    (∀ t ∈ V, {t' ∈ V | Φ t' = Φ t}.Countable) → ∃ t ∈ V, Function.Injective (fderiv ℂ Φ t)

def FlagImm : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] (N e : ℕ) (V : Set (Fin e → ℂ)) (gm : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ), IsOpen V →
    V.Nonempty → (∀ τ a b, AnalyticOnNhd ℂ (fun t => gm τ t a b) V) → (∀ t ∈ V, ∀ τ, IsUnit (gm τ t).det) →
    (∀ t ∈ V, {t' ∈ V | SameFl (fun τ => gm τ t) fun τ => gm τ t'}.Countable) →
    ∃ t ∈ V, ∀ v : Fin e → ℂ,
      (∀ τ, ((gm τ t)⁻¹ * Matrix.of fun a b => fderiv ℂ (fun z => gm τ z a b) t v).BlockTriangular id) → v = 0

def GenRigid : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y ∅ y) (Fl : 𝔐.Flag), 1 ≤ D.p + D.q → Fl.deg = 1 →
    ∃ U : 𝔐.X.Opens, genPt 𝔐.ξ ∈ U ∧ ∀ (b : ∀ s, Fin (labelRk D s) → 𝔐.Li) (z z' : Sp ℂ ⟶ 𝔐.X) (p : Sp ℂ ⟶ Y.X)
      (v : (Σ s, Fin (labelRk D s)) → (epsAt z ⟶ 𝔐.t.G)) (v' : (Σ s, Fin (labelRk D s)) → (epsAt z' ⟶ 𝔐.t.G))
      (w w' : (Σ s, Fin (labelRk D s)) → (epsAt p ⟶ Y.t.G)) (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ]
      (R : RiemLat E g Λ) (x x' : (Σ s, Fin (labelRk D s)) → Fin g → ℂ),
      (∀ s i, flagStep Ω (b s) i = flagStep Ω (Fl.b s) i) → centre z ∈ U → centre z' ∈ U → 𝔐.Interior z → 𝔐.Interior z' →
      (∀ s, (𝔐.V s).IsFrameAt (b s) ⟨centre z, 𝔐.all _⟩) → (∀ s, (𝔐.V s).IsFrameAt (b s) ⟨centre z', 𝔐.all _⟩) →
      z ≫ 𝔐.f = p → z' ≫ 𝔐.f = p → (∀ a, 𝔐.M.ValAt z (b a.1 a.2) (v a)) → (∀ a, 𝔐.M.ValAt z' (b a.1 a.2) (v' a)) →
      (∀ a, (v a).left ≫ 𝔐.m.φ = (w a).left) → (∀ a, (v' a).left ≫ 𝔐.m.φ = (w' a).left) →
      FibreLatVec Y.t p R (Sum.elim x x') (Sum.elim w w') →
      (∀ s k, flagStep ℂ (fun i => x ⟨s, i⟩) k = flagStep ℂ (fun i => x' ⟨s, i⟩) k) → z = z'

def CountGen : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y ∅ y) (Fl : 𝔐.Flag), 1 ≤ D.p + D.q → Fl.deg = 1 →
    ∃ U : 𝔐.X.Opens, genPt 𝔐.ξ ∈ U ∧ ∀ (b : ∀ s, Fin (labelRk D s) → 𝔐.Li) (g : ℕ) (Λ : Type) [AddCommGroup Λ]
      [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (F : CMType H ⊕ CMType H → ℕ → Submodule ℂ (Fin g → ℂ)),
      (∀ s i, flagStep Ω (b s) i = flagStep Ω (Fl.b s) i) →
      {z : Sp ℂ ⟶ 𝔐.X | centre z ∈ U ∧ 𝔐.Interior z ∧ (∀ s, (𝔐.V s).IsFrameAt (b s) ⟨centre z, 𝔐.all _⟩) ∧
        ∃ (x : (Σ s, Fin (labelRk D s)) → Fin g → ℂ) (v : (Σ s, Fin (labelRk D s)) → (epsAt z ⟶ 𝔐.t.G)),
          (∀ a, 𝔐.M.ValAt z (b a.1 a.2) (v a)) ∧ FibreLatVec 𝔐.t z R x v ∧
          ∀ s k, flagStep ℂ (fun i => x ⟨s, i⟩) k = F s k}.Countable

def PotLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (D.p + D.q))
    (Sys : AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx)
    (ψ : Sys.X → Or.Re.R.X) (k : Fin Sys.A.n) (V : Set (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ))
    (z : (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ) → (Sp ℂ ⟶ Or.𝔐.X)) (tr : RootIx D → RM.Ω)
    (ν : RootIx D → (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ) → ℝ),
    HoloMap Sys.A Or.Re.R.A ψ → (∀ x, Or.Re.π (ψ x) = x) → IsOpen V → V ⊆ (Sys.A.chart k).target →
    (∀ t ∈ V, (Sys.A.chart k).symm t ∈ Sys.open' ∧
      CoordsAt Or.𝔐.ξ RM.y (z t) (Or.Re.R.lift (ψ ((Sys.A.chart k).symm t)) (ψ ((Sys.A.chart k).symm t))) ∧
      ∀ r, Or.𝔐.M.IsGrNorm Or.𝔐.t.PP.L (Or.𝔐.V (HodgeCpt.rootIdx D r).1) (Or.Fl.b (HodgeCpt.rootIdx D r).1)
        (HodgeCpt.rootIdx D r).2 (z t) (tr r) (ν r t)) →
    ∀ t₁ ∈ V, ∀ p : RootIx D, ∃ G : (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ) → ℂ, AnalyticAt ℂ G t₁ ∧ ∀ᶠ t in 𝓝 t₁,
      (Sys.potH (some p)).φ ((Sys.A.chart k).symm t₁) ((Sys.A.chart k).symm t) =
        ∑ i ∈ Finset.Iic p.2, (HodgeCpt.rootSgn D (p.1, i) : ℝ) * Real.log (ν (p.1, i) t) + (G t).re

def PtsFam : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (D.p + D.q))
    (Sys : AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx)
    (ψ : Sys.X → Or.Re.R.X), Or.Re.J = ⊤ → HoloMap Sys.A Or.Re.R.A ψ → (∀ x, Or.Re.π (ψ x) = x) → (∀ w, ψ (Or.Re.π w) = w) →
    ∃ z : Sys.X → (Sp ℂ ⟶ Or.𝔐.X), Function.Injective z ∧ (∀ x, CoordsAt Or.𝔐.ξ RM.y (z x) (Or.Re.R.lift (ψ x) (ψ x))) ∧
      (∀ k, IsHolTo (Sys.A.chart k).target fun t => z ((Sys.A.chart k).symm t)) ∧
      ∀ U : Or.𝔐.X.Opens, genPt Or.𝔐.ξ ∈ U → ∃ x ∈ Sys.open', centre (z x) ∈ U

end RootFieldNumerics
