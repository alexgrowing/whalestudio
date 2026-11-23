import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.WhittakerModelGL2
import GroundTheory.AutomorphicForms.GL2Classical
import GroundTheory.AutomorphicForms.GL2.GodementSectionFactor
import GroundTheory.AutomorphicForms.ReductionMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace Ad3.R

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

abbrev SB (Φ : (Fin 2 → F) → ℂ) : Prop := Φ ∈ GodementSectionLocal.schwartzBruhat2 F

def chF (c : Fˣ →* ℂˣ) (s : ℂ) (t : F) : ℂ := if h : t = 0 then 0 else ((c (Units.mk0 t h) : ℂˣ) : ℂ) * mp (Units.mk0 t h) s

def dt (r r' : Fin 2 → F) : F := r 0 * r' 1 - r 1 * r' 0

def Kr (ν c : Fˣ →* ℂˣ) (s : ℂ) (r₁ r₂ r₃ : Fin 2 → F) : ℂ :=
  chF (ν * c) (s - 1) (dt r₁ r₂) * chF (ν⁻¹ * c) (s - 1) (dt r₃ r₂) * chF c⁻¹ (-s) (dt r₁ r₃)

def m2 (ψ : AddChar F Circle) : Measure (Fin 2 → F) := Measure.pi fun _ => selfDualMeasure ψ

def sF (ψ : AddChar F Circle) (Ψ : (Fin 2 → F) → ℂ) (r : Fin 2 → F) : ℂ := ∫ r', Ψ r' * (ψ (dt r' r) : ℂ) ∂m2 ψ

def triI (ν c : Fˣ →* ℂˣ) (s : ℂ) (φ₁ Ψ φ₃ : (Fin 2 → F) → ℂ) (p : (Fin 2 → F) × (Fin 2 → F) × (Fin 2 → F)) : ℂ :=
  Ψ p.1 * (φ₁ p.2.1 * conj (φ₃ p.2.2) * Kr ν c s p.2.1 p.1 p.2.2)

def Av (W W' : GL (Fin 2) F → ℂ) (c : Fˣ →* ℂˣ) (s : ℂ) (κ : GL (Fin 2) F) : ℂ :=
  ∫ a, W (dg2 a 1 * κ) * conj (W' (dg2 a 1 * κ)) * ((c a : ℂˣ) : ℂ) * mp a (s - 1) ∂multHaar F

def Zv [MeasurableSpace (GL (Fin 2) F)] (m : Measure (integralGL F 2)) (W W' : GL (Fin 2) F → ℂ) (Ψ : (Fin 2 → F) → ℂ)
    (c : Fˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ κ, GodementSectionLocal.localSection c c⁻¹ s Ψ κ.1 * Av W W' c s κ.1 ∂m

def upm (ϖ : Fˣ) (b : F) : GL (Fin 2) F := uni2 b * dg2 ϖ 1

def Reps (ϖ : Fˣ) (B : Finset F) : Prop :=
  ord (ϖ : F) = 1 ∧ (∀ b ∈ B, b ∈ 𝒪[F]) ∧ ∀ x ∈ 𝒪[F], ∃! b, b ∈ B ∧ ((ϖ⁻¹ : Fˣ) : F) * (x - b) ∈ 𝒪[F]

def GammaZeroLevelMembership (n : ℕ) (x : GL (Fin 2) F) (d : Fˣ) : Prop :=
  x ∈ integralGL F 2 ∧ (((unifUnit F)⁻¹ ^ n : Fˣ) : F) * x 1 0 ∈ 𝒪[F] ∧ (d : F) = x 1 1

def Law (ψ : AddChar F Circle) (ω : Fˣ →* ℂˣ) (W : GL (Fin 2) F → ℂ) : Prop :=
  (∀ x g, W (uni2 x * g) = (ψ x : ℂ) * W g) ∧ ∀ (z : Fˣ) g, W (dg2 z z * g) = ((ω z : ℂˣ) : ℂ) * W g

def TypeU (ω : Fˣ →* ℂˣ) (n : ℕ) (lam : ℂ) (W : GL (Fin 2) F → ℂ) : Prop :=
  (∀ x d, GammaZeroLevelMembership n x d → ∀ g, W (g * x) = ((ω d : ℂˣ) : ℂ) * W g) ∧
    ∀ ϖ B, Reps ϖ B → ∀ g, ∑ b ∈ B, W (g * upm ϖ b) = lam * W g

def TypeT (lam : ℂ) (W : GL (Fin 2) F → ℂ) : Prop :=
  (∀ x ∈ integralGL F 2, ∀ g, W (g * x) = W g) ∧
    ∀ ϖ B, Reps ϖ B → ∀ g, ∑ b ∈ B, W (g * upm ϖ b) + W (g * dg2 1 ϖ) = lam * W g

def ind0 : (Fin 2 → F) → ℂ := Set.indicator {x | ∀ i, x i ∈ 𝒪[F]} 1

end Loc

abbrev G2 : Type := AdelicGLn.AdelicGL ℚ 2
abbrev Jd : Type := IdeleGroup ℚ
abbrev Af : Type := FiniteAdeleRing (𝓞 ℚ) ℚ

instance (v : Pl) : MeasurableSpace (GL (Fin 2) (Qv v)) := borel _
instance (v : Pl) : BorelSpace (GL (Fin 2) (Qv v)) := ⟨rfl⟩

abbrev dia2 (γ : GL (Fin 2) ℚ) : G2 := AdelicGLn.diagonal ℚ 2 γ

def md (a : Jd) : ℝ := (IdeleGroup.ideleModule ℚ a : ℝ)
def Dt (g : G2) : ℝ := md (GeneralLinearGroup.det g)
def cdet (c : HeckeCharacter ℚ) (g : G2) : ℂ := (c.toIdele (GeneralLinearGroup.det g) : ℂ)
def pri (α : ℚˣ) : Jd := Units.map (algebraMap ℚ 𝔸[ℚ]).toMonoidHom α

def lf (v : Pl) (a : Afˣ) : (Qv v)ˣ := Units.map (adeleAt v).toMonoidHom a

def lc (v : Pl) (a : Jd) : (Qv v)ˣ := Units.map ((adeleAt v).comp Adele2.finRingHom).toMonoidHom a
def row (ξ : Fin 2 → ℚ) (g : G2) : Fin 2 → 𝔸[ℚ] := (fun i => algebraMap ℚ 𝔸[ℚ] (ξ i)) ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])
abbrev NZ : Type := {ξ : Fin 2 → ℚ // ξ ≠ 0}
def th (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ) (g : G2) : ℂ := ∑' ξ : NZ, Φ (row ξ.1 g)
def band : Set G2 := {g | 1 ≤ Dt g ∧ Dt g < 2}

def inv2 (g : G2) : G2 := dg2 (GeneralLinearGroup.det g)⁻¹ (GeneralLinearGroup.det g)⁻¹ * g
def sFA (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ) (r : Fin 2 → 𝔸[ℚ]) : ℂ := Adele2.adelicFourier2 ℚ Φ ![r 1, -r 0]
def lrow (z : Jd) (κ : G2) : Fin 2 → 𝔸[ℚ] := ![0, (z : 𝔸[ℚ])] ᵥ* (κ : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])
abbrev KA : Type := (maxCompact : Subgroup G2)
def pt (x : 𝔸[ℚ]) (a z : Jd) (κ : G2) : G2 := uni2 x * dg2 a 1 * dg2 z z * κ
def LInv {X : Type} (H : G2 → X) : Prop := ∀ γ g, H (dia2 γ * g) = H g
def CInv {X : Type} (H : G2 → X) : Prop := ∀ (z : Jd) g, H (dg2 z z * g) = H g

structure Set0 (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) : Prop where
  haar : μ.IsHaarMeasure
  right : μ.IsMulRightInvariant
  fd : IsFundamentalDomain (AdelicGLn.diagonal ℚ 2).range 𝓕 μ
  meas : MeasurableSet 𝓕
  vol : μ (𝓕 ∩ band) < ∞
  haarK : mK.IsHaarMeasure
  probK : IsProbabilityMeasure mK
  measD : MeasurableSet 𝓓
  uniqD : ∀ a : Jd, ∃! α : ℚˣ, pri α * a ∈ 𝓓
  finD : ∀ (τ : ℝ) (M : ℕ), 0 < τ → τ < M → ∫⁻ a in 𝓓, ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ τ) ∂ideleMeasure ℚ < ∞

def Coord (μ : Measure G2) (mK : Measure KA) (C : NNReal) : Prop := C ≠ 0 ∧ ∀ F : G2 → ℝ≥0∞, Measurable F →
  ∫⁻ g, F g ∂μ = C * ∫⁻ κ, ∫⁻ z, ∫⁻ a, ∫⁻ x, F (pt x a z κ.1) * ENNReal.ofReal (md a)⁻¹
    ∂adeleMeasure ℚ ∂ideleMeasure ℚ ∂ideleMeasure ℚ ∂mK

def Dec (H : G2 → ℂ) : Prop := ∀ M : ℕ, ∃ C : ℝ, ∀ x (a : Jd) (κ : KA), ‖H (uni2 x * dg2 a 1 * κ.1)‖ ≤ C * min 1 (md a)⁻¹ ^ M

structure Aut (H : G2 → ℂ) : Prop where
  cont : Continuous H
  left : LInv H
  cen : CInv H
  bdd : ∃ C : ℝ, ∀ g, ‖H g‖ ≤ C
  dec : Dec H

structure Par (H P : G2 → ℂ) : Prop where
  cont : Continuous P
  sum : ∀ (a : Jd) (κ : KA), HasSum (fun α : ℚˣ => P (dg2 (pri α * a) 1 * κ.1))
    (∫ x in fundamentalSet ℚ, H (uni2 x * dg2 a 1 * κ.1) ∂adeleMeasure ℚ)
  bd : ∀ M : ℕ, ∃ C : ℝ, ∀ (a : Jd) (κ : KA),
    ∑' α : ℚˣ, ‖P (dg2 (pri α * a) 1 * κ.1)‖ₑ ≤ ENNReal.ofReal (C * min 1 (md a)⁻¹ ^ M)

def Zg (μ : Measure G2) (𝓕 : Set G2) (H : G2 → ℂ) (c : HeckeCharacter ℚ) (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ) (s : ℂ) : ℂ :=
  ∫ g in 𝓕, H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g ∂μ

def Ag (P : G2 → ℂ) (c : HeckeCharacter ℚ) (s : ℂ) (κ : G2) : ℂ :=
  ∫ a, P (dg2 a 1 * κ) * (c.toIdele a : ℂ) * modPow a (s - 1) ∂ideleMeasure ℚ

def Jg (mK : Measure KA) (P : G2 → ℂ) (c : HeckeCharacter ℚ) (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ) (s : ℂ) : ℂ :=
  ∫ κ, godementSection c c⁻¹ s Φ κ.1 * Ag P c s κ.1 ∂mK

def Wh (φ : G2 → ℂ) (g : G2) : ℂ :=
  ∫ x in fundamentalSet ℚ, φ (uni2 x * g) * (adelicChar ℚ (-x) : ℂ) ∂adeleMeasure ℚ

def IsLoc2 (v : Pl) (x : GL (Fin 2) (Qv v)) (h : G2) : Prop := finAt v h = x ∧ (∀ v' ≠ v, finAt v' h = 1) ∧ ∀ w, infAt w h = 1

structure Om (N : ℕ) (χ : DirichletCharacter ℂ N) (ω : HeckeCharacter ℚ) : Prop where
  fin : IsOfFinOrder ω
  val : ∀ (d : Afˣ) (n : ℤ), (∀ v, ord (lf v d : Qv v) = 0) →
    (∀ v, pOf v ∣ N → ((N : Qv v))⁻¹ * ((lf v d : Qv v) - n) ∈ 𝒪[Qv v]) →
    (ω.toIdele (IdeleGroup.ofFinite d) : ℂ) * χ (n : ZMod N) = 1

open UpperHalfPlane in

structure Lift (k N : ℕ) [NeZero N] (f : ℍ → ℂ) (ω : HeckeCharacter ℚ) (φ : G2 → ℂ) : Prop where
  cont : Continuous φ
  left : LInv φ
  cen : ∀ (z : Jd) g, φ (dg2 z z * g) = (ω.toIdele z : ℂ) * φ g
  real : ∀ x : GL (Fin 2) ℝ, 0 < x.det.val → φ (realEmb x) = archLift (k : ℤ) f x
  rot : ∀ r : GL (Fin 2) ℝ, r.val * r.valᵀ = 1 → r.det.val = 1 → ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ g, φ (g * realEmb r) = u * φ g
  level : ∀ u ∈ Gamma0Level N, ∀ d : Afˣ, (∀ v, ord (lf v d : Qv v) = 0) →
    (∀ v, pOf v ∣ N → (lf v d : Qv v) = glAt v u 1 1) → ∀ g, φ (g * finEmb ℚ 2 u) = (ω.toIdele (IdeleGroup.ofFinite d) : ℂ) * φ g

def LocFn (v : Pl) (φ : G2 → ℂ) (g : G2) (W : GL (Fin 2) (Qv v) → ℂ) : Prop := ∀ x h, IsLoc2 v x h → W x = φ (g * h)

def lamOf (k : ℕ) (a : ℕ → ℂ) (v : Pl) : ℂ := a (pOf v) * ((pOf v : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ)

structure Hk (k N : ℕ) (a : ℕ → ℂ) (ω : HeckeCharacter ℚ) (φ : G2 → ℂ) : Prop where
  good : ∀ v, ¬ pOf v ∣ N → ∀ g W, LocFn v φ g W → TypeT (lamOf k a v) W
  bad : ∀ v, pOf v ∣ N → ∀ g W, LocFn v φ g W → TypeU (localChar ω v) (N.factorization (pOf v)) (lamOf k a v) W
  glob : ∀ κ : KA, (∀ w, infAt w κ.1 = 1) → (∀ v, pOf v ∣ N → finAt v κ.1 = 1) → ∀ g, φ (g * κ.1) = φ g

structure OmL (k N : ℕ) (χ : DirichletCharacter ℂ N) (ω : HeckeCharacter ℚ) : Prop where
  good : ∀ v, ¬ pOf v ∣ N → IsUnramifiedChar (localChar ω v) ∧ (localChar ω v (unifUnit (Qv v)) : ℂ) = χ (pOf v)
  bad : ∀ v, pOf v ∣ N → quasiCharConductor (localChar ω v) = N.factorization (pOf v)
  sign : ∀ S : Finset Pl, (∀ v, pOf v ∣ N → v ∈ S) → ∏ v ∈ S, ((localChar ω v (-1) : ℂˣ) : ℂ) = (-1) ^ k

structure Mod (N : ℕ) (ω : HeckeCharacter ℚ) (W : G2 → ℂ) (μ₁ μ₂ : ∀ v : Pl, (Qv v)ˣ →* ℂˣ)
    (φ₀ : ∀ v : Pl, (Fin 2 → Qv v) → ℂ) : Prop where
  u₁ : ∀ v, IsUnit1 (μ₁ v)
  u₂ : ∀ v, IsUnit1 (μ₂ v)
  mul : ∀ v, μ₁ v * μ₂ v = localChar ω v
  sb : ∀ v, SB (φ₀ v)
  one : ∀ v, W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) 1 = 1
  good : ∀ v, ¬ pOf v ∣ N → IsUnramifiedChar (μ₁ v) ∧ IsUnramifiedChar (μ₂ v) ∧ φ₀ v = ind0
  fac : ∀ v g, finAt v g = 1 → ∀ x h, IsLoc2 v x h → W (g * h) = W g * W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) x

def WR (k : ℕ) (t : ℝˣ) : ℂ := if (t : ℝ) < 0 then ((Real.sqrt |(t : ℝ)| ^ k * Real.exp (-2 * Real.pi * |(t : ℝ)|) : ℝ) : ℂ) else 0

def IsGauss (φ : 𝓢(Fin 2 → mixedEmbedding.mixedSpace ℚ, ℂ)) : Prop :=
  ∀ y, φ y = ((Real.exp (-Real.pi * ∑ i, ∑ w, (y i).1 w ^ 2) : ℝ) : ℂ)

def tst (γ : 𝓢(Fin 2 → mixedEmbedding.mixedSpace ℚ, ℂ)) (S : Finset Pl) (Ψ : ∀ v : S, (Fin 2 → Qv v.1) → ℂ) :
    (Fin 2 → 𝔸[ℚ]) → ℂ := Adele2.schwartzBruhatTensor2 γ (restrictedTensor2 S Ψ)

def IsUn (S : Finset Pl) (x : ∀ v : S, Qv v.1) (h : G2) : Prop :=
  (∀ v : S, finAt v.1 h = uni2 (x v)) ∧ (∀ v ∉ S, finAt v h = 1) ∧ ∀ w, infAt w h = 1

def Lp (c : HeckeCharacter ℚ) (S : Finset Pl) (s : ℂ) : ℂ := ∏' v : {v : Pl // v ∉ S}, localLFactor (localChar c v.1) s

def ZS (m : ∀ v : Pl, Measure (integralGL (Qv v) 2)) (μ₁ μ₂ : ∀ v : Pl, (Qv v)ˣ →* ℂˣ) (φ₀ : ∀ v : Pl, (Fin 2 → Qv v) → ℂ)
    (S : Finset Pl) (x : ∀ v : S, Qv v.1) (Ψ : ∀ v : S, (Fin 2 → Qv v.1) → ℂ) (c : HeckeCharacter ℚ) (s : ℂ) : ℂ :=
  ∏ v : S, Zv (m v.1) (W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1))
    (fun g => W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1) (g * uni2 (x v))) (Ψ v) (localChar c v.1) s

def GG (k : ℕ) (s : ℂ) : ℂ := Complex.Gammaℂ s * Complex.Gammaℂ (s + k - 1)

def IsK (m : ∀ v : Pl, Measure (integralGL (Qv v) 2)) : Prop := ∀ v, (m v).IsHaarMeasure ∧ IsProbabilityMeasure (m v)

end Ad3.R

end
