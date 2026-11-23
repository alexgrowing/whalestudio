import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

section Objects

variable {E : Type} [Field E] [NumberField E]

def UI (β : (A E)ˣ → ℂ) : ℂ := ∫ z in normOneFundamentalDomain E, β (z : IdeleGroup E) ∂normOneMeasure E

def sZ (D : Dat ℚ E) (z : (A E)ˣ) : GL (Fin 2) (A E) := aE z * dM (Units.map (D.bar : A E →* A E) z)⁻¹

def SLP (M : Meas ℚ) (φ : GL (Fin 2) (A E) → ℂ) : ℂ := ∫ g in M.D, φ (em E (gl g)) ∂M.μ

def UPer (D : Dat ℚ E) (M : Meas ℚ) (φ : GL (Fin 2) (A E) → ℂ) : ℂ := UI fun z => SLP M fun x => φ (x * sZ D z)
variable (E) in

structure MeasE where
  μ : Measure (G1 E)
  D : Set (G1 E)
  haar : μ.IsHaarMeasure
  right : μ.IsMulRightInvariant
  meas : MeasurableSet D
  fund : IsFundamentalDomain (Gam E) D μ

def mean (N : MeasE E) (Ψ : GL (Fin 2) (A E) → ℂ) : ℂ := ∫ h in N.D, Ψ (gl h) ∂N.μ

def J1 (D : Dat ℚ E) (N : MeasE E) (Ψ : GL (Fin 2) (A E) → ℂ) : ℂ := UI fun z => mean N fun x => Ψ (x * sZ D z)

def II (N : MeasE E) (Ψ : GL (Fin 2) (A E) → ℂ) : ℂ := UI fun t => mean N fun x => Ψ (x * aE t)

abbrev rp (ξ : Fin 4 → ℚ) : V4 ℚ := fun i => rt (ξ i)

def qr (δ : ℚ) (ξ : Fin 4 → ℚ) : ℚ := ξ 2 ^ 2 - δ * ξ 3 ^ 2 - ξ 1 * ξ 0

def ThOn (S : Set (Fin 4 → ℚ)) (φ : V4 ℚ → ℂ) : ℂ := ∑' ξ : S, φ (rp ξ.1)

def X0 : Fin 4 → ℚ := ![0, 0, 0, 1]

def PosInv (π : TR.CuspSub ℚ 2) : Prop :=
  ∀ f ∈ π.V, ∀ s g, f.1 (GroundTheory.Automorphic.Reduction.centralSection ℚ 2 s * g) = f.1 g

variable [IsTotallyComplex E] {D : Dat ℚ E} (W : Weil D) (N : MeasE E)

def fOn (S : Set (Fin 4 → ℚ)) (ph : S4 ℚ) (φ : GL (Fin 2) (A E) → ℂ) (g : G1 ℚ) : ℂ :=
  J1 D N fun x => ThOn S (W.Om g (W.L x ph)).1 * φ x

def f0 (ph : S4 ℚ) (φ : GL (Fin 2) (A E) → ℂ) (g : G1 ℚ) : ℂ := J1 D N fun x => Th (W.Om g (W.L x ph)).1 * φ x

end Objects

def All (Q : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E), Weil D → Meas ℚ → MeasE E → CuspSub E 2 → Prop) :
    Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (W : Weil D) (M : Meas ℚ) (N : MeasE E) (P : CuspSub E 2),
    Q E D W M N P

def MeasEEx : Prop := ∀ (E : Type) [Field E] [NumberField E], Nonempty (MeasE E)

def VolE : Prop := ∀ (E : Type) [Field E] [NumberField E] (N : MeasE E), N.μ N.D < ⊤

def RedE : Prop := ∀ (E : Type) [Field E] [NumberField E], ∃ (c : ℝ) (C : Set (G1 E)), 0 < c ∧ IsCompact C ∧
  ∀ h : G1 E, ∃ γ u b, ∃ k ∈ C, ratS E γ * h = nU u * mD b * k ∧ c ≤ ab b

def InvE : Prop := ∀ (E : Type) [Field E] [NumberField E] (N : MeasE E),
  (∀ t, MeasurePreserving (cD t) N.μ N.μ) ∧ ∀ Ψ : GL (Fin 2) (A E) → ℂ, LRat Ψ →
    (∀ h : G1 E, (mean N fun x => Ψ (x * gl h)) = mean N Ψ) ∧ ∀ γ, (mean N fun x => Ψ (x * ratGL E 2 γ)) = mean N Ψ

def TorCo : Prop := ∀ (E : Type) [Field E] [NumberField E], ∃ α : G1 E → IdeleGroup E, Measurable α ∧
  (∀ u h, α (nU u * h) = α h) ∧ ∀ t h, α (mD t * h) = t * α h

def SzLaws : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E),
  (∀ z z', sZ D (z * z') = sZ D z * sZ D z') ∧ Continuous (sZ D) ∧ (∀ z, nu ℚ (sZ D z) = 1) ∧ (∀ h : G1 E, nu ℚ (gl h) = 1) ∧
  (∀ z, D.act (sZ D z) (rp X0) = rp X0) ∧ (∀ g : G1 ℚ, D.act (em E (gl g)) (rp X0) = rp X0) ∧
  (∀ e : Eˣ, ∃ γ, sZ D (IdeleGroup.diagonal E e) = ratGL E 2 γ) ∧
  (∀ z g, sZ D z * em E (gl g) = em E (gl (cD (ideleNorm ℚ E z)⁻¹ g)) * sZ D z) ∧
  (∀ z, sZ D z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * em E (dM (ideleNorm ℚ E z)⁻¹)) ∧
  (∀ x, nu ℚ x = 1 → ∀ v, q4 D.δ (D.act x v) = q4 D.δ v) ∧ ∀ ξ, q4 D.δ (rp ξ) = rt (qr D.δ ξ)

def LatSum : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ))
  (C : Set (GL (Fin 2) (A E))) (c : ℝ) (s : ℕ), IsCompact K → IsCompact C → (∀ k ∈ C, nu ℚ k = 1) → 0 < c →
    ∃ (n r : ℕ) (B : ℝ), ∀ (a : (A ℚ)ˣ) u (b : (A E)ˣ), ∀ k ∈ C, c ≤ ab a → c ≤ ab b →
      (Summable fun ξ : Fin 4 → ℚ => wt K n fun i => (a : A ℚ) * D.act (gl (nU u * mD b) * k)⁻¹ (rp ξ) i) ∧
      ∑' ξ : Fin 4 → ℚ, (wt K n fun i => (a : A ℚ) * D.act (gl (nU u * mD b) * k)⁻¹ (rp ξ) i) ≤ B * ab b ^ r ∧
      ∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, (wt K n fun i => (a : A ℚ) * D.act (gl (nU u * mD b) * k)⁻¹ (rp ξ.1) i) ≤
        B * (ab a)⁻¹ ^ s * ab b ^ r

def DecE : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (P : CuspSub E 2), ∀ φ ∈ P.V,
  Pp.Lf φ.1 ∧ (∀ g, ∫ b in fundamentalSet E, φ.1 (gl (nU b) * g) ∂(adeleMeasure E) = 0) ∧
  ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∀ c : ℝ, 0 < c → ∀ r : ℕ,
    ∃ B : ℝ, ∀ b a, ∀ k ∈ C, c ≤ ab a → ‖φ.1 (gl (nU b * mD a) * k)‖ ≤ B * (ab a)⁻¹ ^ r

def Maj : Prop := All fun E _ _ _ D W _ _ P => ∀ ph ∈ Fock D.δ, ∀ φ ∈ P.V, ∀ C : Set (GL (Fin 2) (A E)), IsCompact C →
  (∀ k ∈ C, nu ℚ k = 1) → ∀ c : ℝ, 0 < c → ∀ s : ℕ, ∃ B : ℝ, ∀ b a, ∀ k' ∈ KK ℚ, c ≤ ab a → ∀ h : G1 E, ∀ k ∈ C,
    (Summable fun ξ : Fin 4 → ℚ => ‖(W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 (rp ξ)‖) ∧
    (∑' ξ : Fin 4 → ℚ, ‖(W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 (rp ξ)‖) * ‖φ.1 (gl h * k)‖ ≤ B * ab a ^ 2 ∧
    (∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, ‖(W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 (rp ξ.1)‖) * ‖φ.1 (gl h * k)‖ ≤
      B * (ab a)⁻¹ ^ s

def ThCont : Prop := All fun E _ _ _ D W _ _ _ => ∀ ph ∈ Fock D.δ, ∀ S : Set (Fin 4 → ℚ),
  ContinuousOn (fun p : G1 ℚ × GL (Fin 2) (A E) => ThOn S (W.Om p.1 (W.L p.2 ph)).1) {p | nu ℚ p.2 = 1}

def MeanZero : Prop := All fun _ _ _ _ _ _ _ N P => ∀ φ ∈ P.V, ∀ y, (mean N fun x => φ.1 (x * y)) = 0

def Orb1 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E),
  (∀ γ : SpecialLinearGroup (Fin 2) E, ∃ ρ : (Fin 4 → ℚ) ≃ₗ[ℚ] (Fin 4 → ℚ), ∀ ξ, D.act (gl (ratS E γ)) (rp ξ) = rp (ρ ξ)) ∧
  (∀ ξ, ξ ≠ 0 → qr D.δ ξ = 0 → ∃ (γ : SpecialLinearGroup (Fin 2) E) (r : ℚ), r ≠ 0 ∧ rp ξ = D.act (gl (ratS E γ)) (rp ![0, r, 0, 0])) ∧
  (∀ (γ : SpecialLinearGroup (Fin 2) E) (r r' : ℚ), r ≠ 0 → D.act (gl (ratS E γ)) (rp ![0, r, 0, 0]) = rp ![0, r', 0, 0] → γ 1 0 = 0) ∧
  (∀ γ : SpecialLinearGroup (Fin 2) E, γ 1 0 = 0 → ∃ c : ℚ, c ≠ 0 ∧ ∀ r, D.act (gl (ratS E γ)) (rp ![0, r, 0, 0]) = rp ![0, c * r, 0, 0]) ∧
  ∀ (u : A E) (r : ℚ), D.act (gl (nU u)) (rp ![0, r, 0, 0]) = rp ![0, r, 0, 0]

def OrbS : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E),
  (∀ ξ, qr D.δ ξ = qr D.δ X0 → ∃ γ : SpecialLinearGroup (Fin 2) E, rp ξ = D.act (gl (ratS E γ)) (rp X0)) ∧
  (∀ h : G1 E, D.act (gl h) (rp X0) = rp X0 ↔ ∃ g : G1 ℚ, gl h = em E (gl g)) ∧
  ∀ γ : SpecialLinearGroup (Fin 2) E, D.act (gl (ratS E γ)) (rp X0) = rp X0 ↔ ∃ g, gl (ratS E γ) = em E (gl (ratS ℚ g))

def Rank1 : Prop := All fun _ _ _ _ D W _ N P => ∀ ph ∈ Fock D.δ, ∀ φ ∈ P.V, ∀ g y, nu ℚ y = 1 →
  (mean N fun x => ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (x * y) ph)).1 * φ.1 (x * y)) = 0

def ThetaLiftEqAnisotropicPart : Prop := All fun _ _ _ _ D W _ N P => ∀ ph ∈ Fock D.δ, ∀ φ ∈ P.V, f0 W N ph φ.1 = fOn W N {ξ | qr D.δ ξ ≠ 0} ph φ.1

def Coef : Prop := All fun _ _ _ _ D W _ N P => ∀ ph ∈ Fock D.δ, ∀ φ ∈ P.V, ∀ (t : ℚ) g,
  ∫ b in fundamentalSet ℚ, fOn W N {ξ | qr D.δ ξ ≠ 0} ph φ.1 (nU b * g) * ψ (-(b * rt t)) ∂(adeleMeasure ℚ) =
    ((adeleMeasure ℚ).real (fundamentalSet ℚ) : ℝ) * fOn W N {ξ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = t} ph φ.1 g

structure CuspFn (u : G1 ℚ → ℂ) : Prop where
  cont : Continuous u
  left : LInv u
  bdd : ∃ B : ℝ, ∀ g, ‖u g‖ ≤ B
  cusp : ∀ g, ∫ b in fundamentalSet ℚ, u (nU b * g) ∂(adeleMeasure ℚ) = 0

def ThetaLiftIsBoundedCuspidal : Prop := All fun _ _ _ _ D W _ N P => ∀ ph ∈ Fock D.δ, ∀ φ ∈ P.V, CuspFn (f0 W N ph φ.1)

def Dens : Prop := ∀ (M : Meas ℚ) (u : G1 ℚ → ℂ), CuspFn u → u ≠ 0 →
  ∃ π : TR.CuspSub ℚ 2, PosInv π ∧ ∃ f ∈ π.V, ∫ g in M.D, f.1 (gl g) * u g ∂M.μ ≠ 0

def Fub : Prop := All fun _ _ _ _ D W M N P => ∀ ph ∈ Fock D.δ, ∀ φ ∈ P.V, ∀ π : TR.CuspSub ℚ 2, ∀ f ∈ π.V,
  ∫ g in M.D, f.1 (gl g) * f0 W N ph φ.1 g ∂M.μ = J1 D N fun x => lift W M f.1 ph x * φ.1 x

def MomKill : Prop := ∀ (δ : ℚ), δ < 0 → ∀ (Y : Type) [MeasurableSpace Y] (m : Measure Y) [SFinite m] (p : Y → V4 ℚ) (w : Y → ℂ),
  Measurable p → Measurable w → (∀ K, IsCompact K → ∃ n, Integrable (fun y => (wt K n (p y) : ℂ) * w y) m) →
  (∀ ph ∈ Fock δ, ∫ y, ph.1 (p y) * w y ∂m = 0) →
  ∀ Ψ : V4 ℚ → ℂ, Measurable Ψ → Integrable (fun y => Ψ (p y) * w y) m → ∫ y, Ψ (p y) * w y ∂m = 0

def OrbFn : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (M : Meas ℚ) (j : G1 ℚ →* G1 E),
  (∀ g, gl (j g) = em E (gl g)) → ∀ c : G1 E → ℂ, Continuous c → HasCompactSupport c →
    ∃ Ψ : V4 ℚ → ℂ, Measurable Ψ ∧ ∀ h : G1 E, Ψ (D.act (gl h)⁻¹ (rp X0)) = ∫ g, c (j g * h) ∂M.μ

def CoefPer : Prop := All fun E _ _ _ D W M N P => ∀ φ ∈ P.V,
  (∀ ph ∈ Fock D.δ, fOn W N {ξ | qr D.δ ξ = qr D.δ X0} ph φ.1 1 = 0) → ∀ h : G1 E, (UPer D M fun x => φ.1 (x * gl h)) = 0

def PerU : Prop := All fun E _ _ _ D W M _ P => ∀ (U : UMeas) (ω : HChar ℚ), GlobalTheory.DiscSpec.IsNormalised P → CenN P ω →
  (∀ φ ∈ P.V, ∀ h : G1 E, (UPer D M fun x => φ.1 (x * gl h)) = 0) → NoPer M U ω⁻¹ P ∧ NoPer M U (ω * W.η)⁻¹ P

def Rev : Prop := All fun E _ _ _ D W M N P => (∃ φ ∈ P.V, ∃ h : G1 E, (UPer D M fun x => φ.1 (x * gl h)) ≠ 0) →
  ∃ π : TR.CuspSub ℚ 2, PosInv π ∧ ∃ f ∈ π.V, ∃ ph ∈ Fock D.δ, ∃ φ ∈ P.V, (J1 D N fun x => lift W M f.1 ph x * φ.1 x) ≠ 0

def ToII : Prop := All fun _ _ _ _ D W M N P => GlobalTheory.DiscSpec.IsNormalised P → ∀ π : TR.CuspSub ℚ 2, PosInv π →
  (∃ f ∈ π.V, ∃ ph ∈ Fock D.δ, ∃ φ ∈ P.V, (J1 D N fun x => lift W M f.1 ph x * φ.1 x) ≠ 0) →
  ∃ π' : TR.CuspSub ℚ 2, PosInv π' ∧ ∃ f ∈ π'.V, ∃ ph ∈ Fock D.δ, ∃ φ ∈ P.V, (II N fun x => lift W M f.1 ph x * φ.1 x) ≠ 0

end UpperTheory.ConvolutionTheory.RankTwoDescent
