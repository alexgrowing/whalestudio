import Mathlib
import Development.AutomorphicSpectrum.Definitions.TwistedFlags.DownChainSucc
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup GlobalTheory.CompanionTheory.Sep
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.UnitaryDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Place

variable {r n : ℕ}

def vnorm (y : Fin n → ℂ) : ℝ := Real.sqrt (∑ i, ‖y i‖ ^ 2)

def embM (ι : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ) (h : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ι * h * ιᴴ + vecMulVec z (star z)

structure IsAdapted (ε : Fin r → Bool) (ε' : Fin n → Bool) (ι : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ) : Prop where
  rank : r + 1 = n
  orth : ιᴴ * ι = 1
  perp : ιᴴ *ᵥ z = 0
  unit : star z ⬝ᵥ z = 1
  form : Formalism.REAL.Jm ε' * ι = ι * Formalism.REAL.Jm ε
  formz : Formalism.REAL.Jm ε' *ᵥ z = z

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

def coef (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ := ⟪v, π g v⟫_ℂ

structure PlaceOK (ε : Fin r → Bool) (ε' : Fin n → Bool) (ι : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ)
    (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ρ : Matrix (Fin r) (Fin r) ℂ → (H' →L[ℂ] H')) (v : H) (w : H')
    (c Λ : ℝ) : Prop where
  unit : ‖v‖ = 1
  ne : w ≠ 0
  pos : 0 < c
  decay : ∃ C : ℝ, ∀ g : Formalism.REAL.UJ ε',
    ‖coef π v (Formalism.MainNotions.S.uMat g)‖ ≤ C * Formalism.REAL.hs (Formalism.MainNotions.S.uMat g) ^ (-(3 * (n : ℝ) ^ 2))
  eigen : ∀ ξ : H', ∫ h : Formalism.REAL.UJ ε, coef π v (embM ι z (Formalism.MainNotions.S.uMat h)) * ⟪ξ, ρ (Formalism.MainNotions.S.uMat h) w⟫_ℂ
    ∂(Formalism.REAL.muG ε) = c * ⟪ξ, w⟫_ℂ
  coset : ∀ g : Formalism.REAL.UJ ε', ∫⁻ h : Formalism.REAL.UJ ε, ‖coef π v (Formalism.MainNotions.S.uMat g * embM ι z (Formalism.MainNotions.S.uMat h))‖ₑ
    ∂(Formalism.REAL.muG ε) ≤ ENNReal.ofReal (c * Λ * vnorm (Formalism.MainNotions.S.uMat g *ᵥ z) ^ (-(2 * (n : ℝ) + 5)))
  lip : ∀ X : Matrix (Fin r) (Fin r) ℂ, Formalism.REAL.inG ε X →
    ∫⁻ h : Formalism.REAL.UJ ε, ‖coef π v (embM ι z (NormedSpace.exp (-X) * Formalism.MainNotions.S.uMat h)) -
      coef π v (embM ι z (Formalism.MainNotions.S.uMat h))‖ₑ ∂(Formalism.REAL.muG ε) ≤ ENNReal.ofReal (c * Λ * Real.sqrt (Formalism.REAL.hs X))

end Place

section Adelic

variable {D : D7} (θ : InfFam D) {Y V : HSp D} {SY SV : D.what₂.Tau → SPar}

def nPl (D : D7) : ℕ := Fintype.card D.what₂.Tau

def upAt (M : DSModel V SV) (τ : D.what₂.Tau) (a : Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  atTau θ V τ ((M.fr τ)⁻¹ * a * M.fr τ)

def frMat (M : DSModel V SV) (τ : D.what₂.Tau) (g : GA D V) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  M.fr τ * infMat D.sp.cm.sig V.gram (θ τ) g * (M.fr τ)⁻¹

def nrmAt (M : DSModel V SV) (x : GA D V) (y : Fin V.rank → D.host.E) (τ : D.what₂.Tau) : ℝ :=
  vnorm (frMat θ M τ x⁻¹ *ᵥ (M.fr τ *ᵥ fun i => tauE D τ (y i)))

variable (V) in

def latAt (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (x : GA D V) : Set (Fin V.rank → D.host.E) :=
  {y | (Lev.finE V x⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (y i)) ∈
    Formalism.L2.Herm.hatL (F := D.host.F) Λ}

def LineLow (M : DSModel V SV) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (𝔞 : Ideal (𝓞 D.host.E))
    (x : GA D V) (t : ℝ) : Prop :=
  ∀ y ∈ latAt V (𝔞 • Λ) x, y ≠ 0 → Real.sqrt (Ideal.absNorm 𝔞) * t ^ nPl D ≤ ∏ τ, nrmAt θ M x y τ

def LipAt (M : DSModel V SV) (φ : GA D V → ℂ) (Γ : ℝ) : Prop :=
  ∀ τ X, Formalism.REAL.inG (M.ε τ) X → ∀ y, ‖φ (y * upAt θ M τ (NormedSpace.exp X)) - φ y‖ ≤ Γ * Real.sqrt (Formalism.REAL.hs X)

def IsSplit (M : DSModel V SV) (e : ((∀ τ, Formalism.REAL.UJ (M.ε τ)) × GfC V) ≃ₜ* GA D V) : Prop :=
  (∀ p τ, frMat θ M τ (e p) = Formalism.MainNotions.S.uMat (p.1 τ)) ∧ (∀ p, Lev.finE V (e p) = Lev.finE V p.2) ∧
    ∀ ν : Measure (GA D V), ν.IsHaarMeasure → ∃ νf : Measure (GfC V), νf.IsHaarMeasure ∧ νf.IsMulRightInvariant ∧
      ((Measure.pi fun τ => Formalism.REAL.muG (M.ε τ)).prod νf).map e = ν

def kInf (M : DSModel V SV) (v : M.Vec) (g : GA D V) : ℂ := ∏ τ, coef (M.σ τ) (v τ : M.H τ) (frMat θ M τ g)

def kAll (M : DSModel V SV) (v : M.Vec) (kf : GA D V → ℂ) (g : GA D V) : ℂ := kInf θ M v g * kf g

def poin (k : GA D V → ℂ) (y x : GA D V) : ℂ := ∑' γ : GQ V, k (y⁻¹ * γ * x)

variable (d : HermitianOrthogonalExtensionData Y V 1 1)

def zVec : Fin V.rank → D.host.E := fun i => d.a i 0

def latV (Λ : Submodule (𝓞 D.host.E) (Fin Y.rank → D.host.E)) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  d.lat Λ fun _ => 1

def MovesZ (γ : GA D V) (z : Fin V.rank → D.host.E) : Prop :=
  (matHom V γ).1 *ᵥ (fun i => incA D (zVec d i)) = fun i => incA D (z i)

def iotaAt (MY : DSModel Y SY) (MV : DSModel V SV) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin Y.rank) ℂ :=
  MV.fr τ * (frameMat V Y d.ι).map (tauE D τ) * (MY.fr τ)⁻¹

def zAt (MV : DSModel V SV) (τ : D.what₂.Tau) : Fin V.rank → ℂ := MV.fr τ *ᵥ fun i => tauE D τ (zVec d i)

structure Std (Λ : Submodule (𝓞 D.host.E) (Fin Y.rank → D.host.E)) (MY : DSModel Y SY) (MV : DSModel V SV) : Prop where
  fam : IsInfFam θ
  sigY : Y.SigOK
  sigV : V.SigOK
  sdY : IsSelfDualC Y Λ
  sdV : IsSelfDualC V (latV d Λ)
  adapted : ∀ τ, IsAdapted (MY.ε τ) (MV.ε τ) (iotaAt d MY MV τ) (zAt d MV τ)

def ArchOK (MY : DSModel Y SY) (MV : DSModel V SV) (v : MV.Vec) (w : MY.Vec) (c : D.what₂.Tau → ℝ) (Λ : ℝ) : Prop :=
  ∀ τ, PlaceOK (MY.ε τ) (MV.ε τ) (iotaAt d MY MV τ) (zAt d MV τ) (MV.σ τ) (MY.σ τ) (v τ : MV.H τ) (w τ : MY.H τ) (c τ) Λ

structure FinOK (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (𝔞 : Ideal (𝓞 D.host.E))
    (K₀ : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (J : Set (GA D Y)) (χ : GA D Y → ℂ) (A : ℕ) (kf : GA D V → ℂ) : Prop where
  ne : 𝔞 ≠ ⊥
  opn : IsOpen ((K₀.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))
  inf : ∀ g, ∀ a ∈ GinfC V, kf (g * a) = kf g ∧ kf (a * g) = kf g
  lev : ∀ g, ∀ k ∈ Lev.levA V K₀, kf (g * k) = kf g ∧ kf (k * g) = kf g
  bdd : ∀ g, ‖kf g‖ ≤ 1
  supp : ∀ g, kf g ≠ 0 → Lev.finE V g ∈ congLev D.sp.cm V.gram L 𝔞
  cusp : ∀ (j : ℕ) (C : Matrix (Fin V.rank) (Fin j) D.host.E), IsIsoFrame V C → ∀ x, ∃ s : Finset (GA D V), s.Nonempty ∧
    (∀ u ∈ s, u ∈ NI V C ∧ u ∈ GfC V) ∧ ∀ g, ∑ u ∈ s, kf (g * u * x) = 0
  ident : ∃ U KH : Subgroup (GA D Y),
    (∀ h, h ∈ KH ↔ h ∈ GfC Y ∧ Lev.finE V (stabilizerEmbedding d h) ∈ congLev D.sp.cm V.gram L 𝔞) ∧ U ≤ KH ∧
    U.relIndex KH ≠ 0 ∧ U.relIndex KH ≤ A ∧ (∀ h ∈ U, h ∈ J ∧ kf (stabilizerEmbedding d h) * χ h = 1) ∧
    ∀ h ∈ GfC Y, h ∉ U → kf (stabilizerEmbedding d h) = 0

structure RowOK (MY : DSModel Y SY) (Λ : Submodule (𝓞 D.host.E) (Fin Y.rank → D.host.E)) (g : ℕ) (J : Set (GA D Y))
    (χ : GA D Y → ℂ) (w : MY.Vec) (u : GA D Y → ℂ) : Prop where
  val : ∃ t : MMap MY, IsMultMap θ MY J χ t ∧ u = t w
  ne : u ≠ 0
  bdd : ∃ N : ℝ, ∀ x, ‖u x‖ ≤ N
  pos : 1 ≤ g
  lev : ∀ k ∈ Lev.levA Y (congLev D.sp.cm Y.gram Λ (Ideal.span {(g : 𝓞 D.host.E)})), ∀ x, u (x * k) = u x

def tLow (D : D7) (r g q : ℕ) (Λ : ℝ) : ℝ := 1 / 2 * ((4 * (r : ℝ) ^ 2 * nPl D * g * D.host.rdE * Λ) ^ q)⁻¹

def DeepEnough (D : D7) (r g q A : ℕ) (Λ : ℝ) (𝔞 : Ideal (𝓞 D.host.E)) : Prop :=
  2 * A * Λ ^ nPl D * Real.exp (10 * (r + 2) * nPl D) < Real.sqrt (Ideal.absNorm 𝔞) * tLow D r g q Λ ^ nPl D

def lamMax (D : D7) (b : ℝ) : ℝ := Real.exp (sizeP D 1000 b / (D.R.f : ℝ) ^ 2)

end Adelic

def IsGenLevel {D : D7} {Pg : Finset (Pl D.host.E)} (PP : Pg) (ψ₀ : AddChar (kP PP.1) ℂ) (P : LevelP Pg D.R.r ℂ) : Prop :=
  (∀ g : G0 Pg D.R.r, g ∈ P.H ↔ (∀ PP', PP' ≠ PP → g PP' = 1) ∧ (∀ a, (g PP).1 a a = 1) ∧
    ∀ a b, b < a → (g PP).1 a b = 0) ∧
  ∀ g : P.H, ((P.chi g : ℂˣ) : ℂ) = ψ₀ (∑ a : Fin D.R.r, ∑ b : Fin D.R.r,
    if (b : ℕ) = a + 1 then ((g : G0 Pg D.R.r) PP).1 a b else 0)

def ArchAll : Prop := Big fun {D} _ _ _ _ _ _ _ _ _ _ R sc G W _ =>
  ∃ (MV : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0))) (v : MV.Vec) (w : (R.MY 0).Vec) (c : D.what₂.Tau → ℝ),
    Std W.θ G.sp.dec0 (R.ΛY 0) (R.MY 0) MV ∧ ArchOK G.sp.dec0 (R.MY 0) MV v w c (lamMax D sc.b)

def FinAll : Prop := Big fun {D} _ _ _ _ _ _ _ _ _ _ R sc G _ _ =>
  ∀ (PP : R.Pg) (ψ₀ : AddChar (kP PP.1) ℂ), ψ₀ ≠ 1 → ∀ P : LevelP R.Pg D.R.r ℂ, IsGenLevel PP ψ₀ P →
    ∃ (𝔞 : Ideal (𝓞 D.host.E)) (kf : GA D (G.V (.core 0)) → ℂ), Real.exp (sizeP D sc.cDep sc.b) ≤ Ideal.absNorm 𝔞 ∧
      FinOK G.sp.dec0 (latV G.sp.dec0 (R.ΛY 0)) 𝔞 (G.levCong (.core 0)) (levS _ (R.βY 0) (R.dat0 P))
        (Lev.levChi _ (R.βY 0) (R.dat0 P)) ((D.host.g 0 * D.host.g 1) ^ D.R.r ^ 2) kf

def RowAll : Prop := Big fun {D} _ _ _ _ _ _ _ _ _ _ R _ _ W _ =>
  ∀ P : LevelP R.Pg D.R.r ℂ, ∀ t ∈ R.EEat P, t ≠ 0 → ∀ w : (R.MY 0).Vec, (∀ τ, w τ ≠ 0) →
    RowOK W.θ (R.MY 0) (R.ΛY 0) (D.host.g 0 * D.host.g 1) (levS _ (R.βY 0) (R.dat0 P))
      (Lev.levChi _ (R.βY 0) (R.dat0 P)) w (t w)

def NumAll : Prop := Big fun {D} _ _ _ _ _ _ _ _ _ _ R sc G _ M =>
  (∀ 𝔞 : Ideal (𝓞 D.host.E), Real.exp (sizeP D sc.cDep sc.b) ≤ Ideal.absNorm 𝔞 →
    DeepEnough D (Yc D 0).rank (D.host.g 0 * D.host.g 1) D.R.m ((D.host.g 0 * D.host.g 1) ^ D.R.r ^ 2) (lamMax D sc.b) 𝔞) ∧
  1 ≤ lamMax D sc.b ∧ 1 ≤ (Yc D 0).rank ∧ 1 ≤ D.R.m ∧
  (∀ τ, (Finset.univ.filter fun a => (R.MY 0).ε τ a = false).card ≤ D.R.m) ∧
  (show Measure (GA D (Yc D 0)) from M.ν (.grid 0 0)).IsHaarMeasure ∧
  IsFundamentalDomain (GQ (Yc D 0)) (show Set (GA D (Yc D 0)) from M.fd (.grid 0 0))
    (show Measure (GA D (Yc D 0)) from M.ν (.grid 0 0))

def GenPer : Prop := Big fun {D} _ _ _ _ _ _ _ _ _ _ R _ _ W M =>
  ∀ (PP : R.Pg) (ψ₀ : AddChar (kP PP.1) ℂ), ψ₀ ≠ 1 → ∀ P : LevelP R.Pg D.R.r ℂ, IsGenLevel PP ψ₀ P →
    ∀ t₁ ∈ R.EEat P, t₁ ≠ 0 → ∃ w : SmT (R.MY 0), HasPeriod W M (rowForm R w t₁)

end GlobalTheory.CompanionTheory.UnitaryDecomposition

end
