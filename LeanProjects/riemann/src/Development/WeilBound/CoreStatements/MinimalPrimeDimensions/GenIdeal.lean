import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open GroundTheory.Heights₂.Heights (IsProjPrime IsChowForm IsMultiHomog relComps localMult chowDegree reduceMod
  HermNorm ArchData fsLog cycleIntegral fundCycle chowHt)

namespace ChowFormHeightComparison₂.CF

section Defs

variable {R : Type} [CommRing R] {Z : Scheme.{0}} {B : LB Z} {m : ℕ}

structure Emb (p : Z ⟶ Sp R) (s : Fin m → B.Sec) : Prop where
  isLB : B.IsLB
  cover : ⨆ k, nonzeroLocus (s k) = ⊤
  chart : ∀ k, IsAffineOpen (nonzeroLocus (s k)) ∧ ∃ t : Fin m → Γ(Z, nonzeroLocus (s k)),
    Function.Surjective (eval₂Hom (algX p (nonzeroLocus (s k))) t) ∧
    ∀ j i, resG Z (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) ((s j).f i) =
      resG Z (inf_le_left : nonzeroLocus (s k) ⊓ B.U i ≤ nonzeroLocus (s k)) (t j) *
        resG Z (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) ((s k).f i)

def coneHom (p : Z ⟶ Sp R) (s : Fin m → B.Sec) (z : Z) (i : B.ι) (h : z ∈ B.U i) :
    MvPolynomial (Fin m) R →+* Polynomial (Z.residueField z) :=
  eval₂Hom (Polynomial.C.comp ((Z.evaluation (B.U i) z h).hom.comp (algX p (B.U i))))
    fun k => Polynomial.X * Polynomial.C (Z.evaluation (B.U i) z h ((s k).f i))

def ptIdeal (p : Z ⟶ Sp R) (s : Fin m → B.Sec) (z : Z) : Ideal (MvPolynomial (Fin m) R) :=
  ⨅ (i : B.ι) (h : z ∈ B.U i), RingHom.ker (coneHom p s z i h)

def IsComb (p : Z ⟶ Sp R) (s : Fin m → B.Sec) (u : Fin m → R) (su : B.Sec) : Prop :=
  ∀ i, su.f i = ∑ k, algX p (B.U i) (u k) * (s k).f i

def coords (p : Z ⟶ Sp R) (σ : R →+* ℂ) (hB : B.IsLB) (s : Fin m → B.Sec) (y : CxPts p σ) : Fin m → ℂ :=
  fun k => ev p σ (B.U (pick hB y)) ((s k).f (pick hB y)) y

def IsFS {p : Z ⟶ Sp R} {σ : R →+* ℂ} (φ : Weight p σ B) (s : Fin m → B.Sec) (h : HermNorm m) : Prop :=
  ∀ i, ∀ y ∈ ptsIn p σ (B.U i), φ.φ i y = Real.log (h.dualNorm (fun k => ev p σ (B.U i) ((s k).f i) y) ^ 2)

end Defs

abbrev genIdeal {K : Type} [Field K] [NumberField K] {Z : Scheme.{0}} [IsIntegral Z] {B : LB Z} {m : ℕ}
    (p : Z ⟶ Sp (𝓞 K)) (s : Fin m → B.Sec) : Ideal (MvPolynomial (Fin m) K) :=
  (ptIdeal p s (genericPoint Z)).map (MvPolynomial.map (algebraMap (𝓞 K) K))

def StPts : Prop :=
  ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp R) (B : LB Z) (m : ℕ) (s : Fin m → B.Sec),
    Emb p s → (∀ z, IsProjPrime (ptIdeal p s z)) ∧ (∀ z z', z ⤳ z' ↔ ptIdeal p s z ≤ ptIdeal p s z') ∧
      (∀ W, IsProjPrime W → ptIdeal p s (genericPoint Z) ≤ W → ∃ z, ptIdeal p s z = W) ∧
      (∀ (u : Fin m → R) (su : B.Sec), IsComb p s u su → ∀ z, z ∈ nonzeroLocus su ↔ GroundTheory.Heights₂.Heights.linForm u ∉ ptIdeal p s z)

def StPull : Prop :=
  ∀ (R : Type) [CommRing R] (Z Y : Scheme.{0}) (p : Z ⟶ Sp R) (B : LB Z) (m : ℕ) (s : Fin m → B.Sec) (i : Y ⟶ Z)
    [IsClosedImmersion i], Emb p s → Emb (i ≫ p) (fun k => GlobalTheory.secPull (s k) i) ∧
      (∀ y, ptIdeal (i ≫ p) (fun k => GlobalTheory.secPull (s k) i) y = ptIdeal p s (i y)) ∧
      ∀ (u : Fin m → R) (su : B.Sec), IsComb p s u su → IsComb (i ≫ p) (fun k => GlobalTheory.secPull (s k) i) u (GlobalTheory.secPull su i)

def StDiv : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (p : Z ⟶ Sp R)
    (B : LB Z) (m : ℕ) (s : Fin m → B.Sec) (hE : Emb p s) (u : Fin m → R) (su : B.Sec), IsComb p s u su →
    ∀ hu : genericPoint Z ∈ nonzeroLocus su,
      (∀ z, (divOfSec hE.isLB su hu).mult z ≠ 0 ↔
        ptIdeal p s z ∈ relComps (ptIdeal p s (genericPoint Z) ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm u})) ∧
      ∀ z, (divOfSec hE.isLB su hu).mult z ≠ 0 → (divOfSec hE.isLB su hu).mult z =
        localMult (ptIdeal p s (genericPoint Z) ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm u}) (ptIdeal p s z)

def StVert : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp (𝓞 K)) (B : LB Z) (m : ℕ)
    (s : Fin m → B.Sec) (v : HeightOneSpectrum (𝓞 K)) (d : ℕ), IsProjOver p → Emb p s →
    (ptIdeal p s (genericPoint Z)).comap (C : 𝓞 K →+* MvPolynomial (Fin m) (𝓞 K)) = v.asIdeal →
    topologicalKrullDim Z = d →
    ∃ _ : Algebra v.asIdeal.ResidueField Γ(Z, ⊤),
      topSelfIntersection v.asIdeal.ResidueField B d = chowDegree (reduceMod v (ptIdeal p s (genericPoint Z))) (d + 1)

def StCharts : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp (𝓞 K)) (B : LB Z) (m : ℕ)
    (s : Fin m → B.Sec) (e : ℕ) (hE : Emb p s), IsArithVar p e →
    ∃ (n : ℕ) (q : MvPolynomial (Fin m) (𝓞 K)), q.IsHomogeneous n ∧ q ∉ ptIdeal p s (genericPoint Z) ∧
      ∀ (σ : 𝓞 K →+* ℂ) (y : CxPts p σ), eval₂ σ (coords p σ hE.isLB s y) q ≠ 0 →
        ∃ c : AlgChart p σ e, y ∈ c.e.source

def StArch : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp (𝓞 K)) (B : LB Z) (m : ℕ)
    (s : Fin m → B.Sec) (e : ℕ) (hE : Emb p s), IsArithVar p e →
    (∃ f, IsChowForm (genIdeal p s) (e + 1) f) → IsProjPrime (genIdeal p s) →
    ∀ (σ : K →+* ℂ) (φ : Weight p (σ.comp (algebraMap (𝓞 K) K)) B) (h : HermNorm m), φ.IsCInf → IsFS φ s h →
    ∀ u : Fin m → K, GroundTheory.Heights₂.Heights.linForm u ∉ genIdeal p s →
      φ.chernInt e {y | ∑ k, σ (u k) * coords p _ hE.isLB s y k ≠ 0}
          (fun y => fsLog h (fun k => σ (u k)) (coords p _ hE.isLB s y)) =
        cycleIntegral h (fundCycle ((genIdeal p s).map (MvPolynomial.map σ))) e (fsLog h fun k => σ (u k)) ∧
      (e = 0 → ∑ᶠ y : CxPts p (σ.comp (algebraMap (𝓞 K) K)), fsLog h (fun k => σ (u k)) (coords p _ hE.isLB s y) =
        cycleIntegral h (fundCycle ((genIdeal p s).map (MvPolynomial.map σ))) e (fsLog h fun k => σ (u k)))

def StForm : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (d N m δ : ℕ) (g : Matrix (Fin N) (Fin m) K)
    (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span K (Set.range g.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) →
    ∀ (y : Fin N → Ω) (Φ : MvPolynomial (Fin (d + 1) × Fin N) K),
    GlobalTheory.ChowHt.IsChowFormInt (GlobalTheory.CompHt.coneIdeal K y) d δ Φ → ∀ H : ArchData K m,
    (∀ (σ : K →+* ℂ) (x : Fin N → ℂ), (H.normAt σ).dualNorm (fun k => ∑ j, σ (g j k) * x j) =
      GlobalTheory.Adelic.archSize (A σ) x) →
    IsChowForm (GlobalTheory.CompHt.coneIdeal K fun k => ∑ j, algebraMap K Ω (g j k) * y j) (d + 1) (GlobalTheory.ChowHt.linSubst g Φ) ∧
      IsMultiHomog δ (GlobalTheory.ChowHt.linSubst g Φ) ∧
      GlobalTheory.ChowHt.formHeight δ g A Φ = chowHt H (d + 1) δ (GlobalTheory.ChowHt.linSubst g Φ)

def StModel : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (m : ℕ) (t : Fin m → Ω)
    (Z : GlobalTheory.ZH.RatModel (𝓞 K) Ω), Z.IsCl t → ∀ (H : LB Z.Z), H.IsLB → ∀ (e : H.ι → Ω), Z.GenTriv H e →
    ∀ (s : Fin m → H.Sec), (∀ k, Z.HasVal e (s k) (t k)) → ⨆ k, nonzeroLocus (s k) = ⊤ → CharZero Γ(Z.Z, ⊤) →
    Emb Z.s s ∧ genIdeal Z.s s = GlobalTheory.CompHt.coneIdeal K t

def StDim : Prop :=
  ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z],
    Order.coheight (i (genericPoint Z)) = 1 → topologicalKrullDim Z = D

def StMain : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (H : ArchData K m) (e : ℕ) (Z : Scheme.{0}) [IsIntegral Z]
    (p : Z ⟶ Sp (𝓞 K)) (L : HermLB p) (s : Fin m → L.B.Sec), IsArithVar p e → Emb p s →
    (∀ σ : K →+* ℂ, IsFS (L.φ (σ.comp (algebraMap (𝓞 K) K))) s (H.normAt σ)) →
    ∀ (δ : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin m) K), IsChowForm (genIdeal p s) (e + 1) f → IsMultiHomog δ f →
    ∀ a, L.IsSelfInter a → a = (Module.finrank ℚ K : ℝ) * chowHt H (e + 1) δ f

end ChowFormHeightComparison₂.CF
