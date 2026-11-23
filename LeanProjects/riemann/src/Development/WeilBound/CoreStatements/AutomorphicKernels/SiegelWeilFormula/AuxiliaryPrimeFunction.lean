import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DefsPlus
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

structure Wk (B : Base F E) {m n : ℕ} (A : Spc F E m) (Y : Spc F E n) (r s : ℕ) (χ : Chr F E) (κ : Type) [Fintype κ]
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ))
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ)
    (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J)) : Prop where
  good : B.IsGood σ
  hm : 1 ≤ m
  hn : 1 ≤ n
  aniso : min r s = 0
  sign : A.IsHerm σ B r s ∧ (∀ i j, σ (Y.J j i) = -Y.J i j) ∨ A.IsSkew σ B r s ∧ ∀ i j, σ (Y.J j i) = Y.J i j
  hecke : IsHecke F E χ
  res : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m
  dbl : IsDbl (σ := σ) (A := A) (Y := Y) B.ψ dd χ om S l
  frame : IsFrame2 σ Y b
  stdK : IsStdK (σ := σ) (Y := Y) B b K
  hgt : IsHgt K a
  haar : μ.IsHaarMeasure
  dom : IsFundamentalDomain (ratU σ A.J) D μ

structure SD (σ : E →ₐ[F] E) : Type 1 where
  B : Base F E
  m : ℕ
  n : ℕ
  A : Spc F E m
  Y : Spc F E n
  r : ℕ
  s : ℕ
  χ : Chr F E
  κ : Type
  [fin : Fintype κ]
  dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ
  om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)
  S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ)
  l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ
  b : GL (Fin n ⊕ Fin n) E
  K : Subgroup (G2 σ Y)
  a : G2 σ Y → ℝ
  μ : Measure (UA σ A.J)
  D : Set (UA σ A.J)
  bs : Module.Basis (Fin 2) F E
  ok : Wk (σ := σ) B A Y r s χ κ dd om S l b K a μ D

attribute [instance] SD.fin

variable (F E) in

abbrev Mx (p q : ℕ) : Type := Matrix (Fin p) (Fin q) (AE F E)

def fP {m n : ℕ} (P : PX m n) (u : Fin m → Fin n → ℂ) : ℂ := evX P u * gs (2 * Real.pi) u

def IsSw {m n : ℕ} (f : (Fin m → Fin n → ℂ) → ℂ) : Prop := ∃ φ : 𝓢(Fin m → Fin n → ℂ, ℂ), ⇑φ = f

namespace SD

variable (d : SD σ)

abbrev G : Type := G2 σ d.Y

abbrev Fn : Type := (d.κ → AF F) → ℂ

abbrev sch : Submodule ℂ d.Fn := schA F d.κ

def KFin (Φ : d.Fn) : Prop :=
  Φ ∈ d.sch ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ))

def T (Φ : d.Fn) (X : Mx F E d.m d.n) : ℂ := d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ)

def gram (X Z : Mx F E d.m d.n) : Mx F E d.n d.n := Xᵀ * incM F d.A.J * Z.map (cA σ)

def tt (M : Mx F E d.n d.n) : AF F := Algebra.trace (AF F) (AE F E) M.trace

def cmb (c : Fin d.m × Fin d.n × Fin 2 → AF F) : Mx F E d.m d.n := fun i j => ∑ k, c (i, j, k) ⊗ₜ[F] d.bs k

def crd (X : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) : AF F :=
  (Algebra.TensorProduct.basis (AF F) d.bs).repr (X k.1 k.2.1) k.2.2

def schM : Submodule ℂ (Mx F E d.m d.n → ℂ) := (schA F (Fin d.m × Fin d.n × Fin 2)).comap (LinearMap.funLeft ℂ ℂ d.cmb)

def ratM : AddSubgroup (Mx F E d.m d.n) := AddSubgroup.closure (Set.range fun X : Matrix (Fin d.m) (Fin d.n) E => incM F X)

def IsCov (ν : Measure (Mx F E d.m d.n)) : Prop :=
  ν.IsAddHaarMeasure ∧ ∃ 𝓕, IsAddFundamentalDomain d.ratM 𝓕 ν ∧ ν 𝓕 = 1

def IsW (ε : ℤˣ) (w : d.G) : Prop := inFrame d.b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0

def Ht (x : d.G) : ℝ≥0 := (d.a x).toNNReal

def eis (f : d.G → ℂ) (s₁ z : ℂ) : d.G → ℂ :=
  GlobalTheory.Eis.cosetSum (par2 σ d.Y) (rat2 σ d.Y) fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x

def Eis (f : d.G → ℂ) (s₁ : ℂ) : Prop := ∀ s₀ : ℂ,
  ∃ (U : Set ℂ) (p : Polynomial ℂ) (Ê : ℂ → d.G → ℂ) (t : ℝ), IsOpen U ∧ IsRightDomain U ∧ s₀ ∈ U ∧ p ≠ 0 ∧
    (∀ g, DifferentiableOn ℂ (Ê · g) U) ∧ ContinuousOn (fun y : ℂ × d.G => Ê y.1 y.2) (U ×ˢ Set.univ) ∧
    (∀ z ∈ U, ∀ γ ∈ rat2 σ d.Y, ∀ g, Ê z (γ * g) = Ê z g) ∧
    ∀ z : ℂ, t < z.re → (∀ C : Set d.G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y) → ℝ, Summable u ∧
        ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term (par2 σ d.Y) (rat2 σ d.Y) (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) g q‖ ≤ u q) ∧
      ∀ g, Ê z g = p.eval z * d.eis f s₁ z g

def Strong : Prop := ∃ r' s', d.Y.IsHerm σ d.B r' s' ∨ d.Y.IsSkew σ d.B r' s'

def sec0 (Φ : d.Fn) (x : d.G) : ℂ := d.l (d.om x Φ)

def EisAll : Prop := ∀ Φ, d.KFin Φ → d.Eis (d.sec0 Φ) (s0 d.m d.n)

abbrev I (Φ : d.Fn) : d.G → ℂ := thetaMean d.om d.S d.μ d.D Φ

def orb (T : nF σ d.Y d.b) (Φ : d.Fn) : ℂ :=
  ⨍ g in d.D, ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1},
    d.T Φ (mat g⁻¹ * incM F X.1) ∂d.μ

def lamSet : Set ((d.G → ℂ) → ℂ) :=
  {L | ∃ nb lam 𝓖 T x, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 ∧ IsND T ∧ L = fun f => fc d.B.ψ d.b nb lam 𝓖 f T x}

def cw (w : InfinitePlace F) {α β : Type} (X : Matrix α β (AE F E)) : Matrix α β ℂ := X.map (piInf (d.B.emb w))

end SD

def dZ (n : ℕ) (ζ : ℂ) : M2 n := Matrix.fromBlocks 1 0 0 (ζ • 1)

structure RD (d : SD σ) where
  ε : ℤˣ
  ζ : ℂ
  fr : InfinitePlace F → GL (Fin d.m) ℂ
  sg : InfinitePlace F → ℤˣ
  ι : InfinitePlace F → (GR d.n →* d.G)
  hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0
  hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I
  hfr : ∀ w, ζ • ((fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (fr w).1.map star) = ((sg w : ℤ) : ℂ) • 1
  cont : ∀ w, Continuous (ι w)
  at_w : ∀ w y, dZ d.n ζ * d.cw w (inFrame d.b (ι w y)) = mR y * dZ d.n ζ
  off_w : ∀ w w' y, w' ≠ w → d.cw w' (inFrame d.b (ι w y)) = 1
  off_f : ∀ w y, finOne F • inFrame d.b (ι w y) = finOne F • (1 : Matrix _ _ (AE F E))

namespace RD

variable {d : SD σ} (R : RD d)

def loc (w : InfinitePlace F) (X : Mx F E d.m d.n) : Fin d.m → Fin d.n → ℂ := (((R.fr w)⁻¹).1 * d.cw w X).map star

def fockOn (s : Finset (InfinitePlace F)) : Submodule ℂ (Mx F E d.m d.n → ℂ) :=
  Submodule.span ℂ {f | ∃ (P : InfinitePlace F → PX d.m d.n) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ), g ∈ SB _ ∧
    f = fun X => (∏ w ∈ s, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2}

abbrev fock : Submodule ℂ (Mx F E d.m d.n → ℂ) := R.fockOn Finset.univ

abbrev away (w : InfinitePlace F) : Submodule ℂ (Mx F E d.m d.n → ℂ) := R.fockOn (Finset.univ.erase w)

def tens (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (Ψ : Mx F E d.m d.n → ℂ) (X : Mx F E d.m d.n) : ℂ :=
  f (R.loc w X) * Ψ X

def IsLocOp (w : InfinitePlace F) (L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ) : Prop :=
  ∀ y f, IsSw f → IsSw (L y f) ∧ ∀ Ψ : Mx F E d.m d.n → ℂ,
    (∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X) →
    ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om (R.ι w y) Φ) = R.tens w (L y f) Ψ

def IsLift (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) (φ : PX d.m d.n →ₗ[ℂ] d.Fn) : Prop :=
  ∀ P, φ P ∈ d.sch ∧ d.T (φ P) = R.tens w (fP P) Ψ

end RD

def TBij : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ),
  (∀ Φ ∈ d.sch, d.T Φ ∈ d.schM) ∧ (∀ f ∈ d.schM, ∃ Φ ∈ d.sch, d.T Φ = f) ∧ ∀ Φ ∈ d.sch, d.T Φ = 0 → Φ = 0

def TPar : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∀ Φ ∈ d.sch,
  (∀ (x : d.G) (β : Mx F E d.n d.n), inFrame d.b x = Matrix.fromBlocks 1 β 0 1 →
    ∀ X, d.T (d.om x Φ) X = d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * d.T Φ X) ∧
  (∀ (x : d.G) (t u : GL (Fin d.n) (AE F E)), inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1 →
    ∀ X, d.T (d.om x Φ) X = (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) * d.T Φ (X * (u⁻¹).1ᵀ)) ∧
  ∀ g X, d.T (d.S g Φ) X = d.T Φ (mat g⁻¹ * X)

def TWeyl : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∀ ν, d.IsCov ν → ∀ ε w, d.IsW ε w → ∀ Φ ∈ d.sch,
  ∀ X, d.T (d.om w Φ) X = ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.T Φ Z ∂ν

def TTheta : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∀ Φ ∈ d.sch,
  HasSum (fun X : Matrix (Fin d.m) (Fin d.n) E => d.T Φ (incM F X)) (thetaSum F Φ) ∧
  ∀ x g, d.om x (d.S g Φ) = d.S g (d.om x Φ)

def ThetaAuto : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), d.μ d.D ≠ 0 ∧ d.μ d.D ≠ ⊤ ∧ ∀ Φ ∈ d.sch,
  (∀ x, IntegrableOn (fun g => thetaSum F (d.om x (d.S g Φ))) d.D d.μ) ∧ Continuous (d.I Φ) ∧
  ∀ γ ∈ rat2 σ d.Y, ∀ x, d.I Φ (γ * x) = d.I Φ x

def ThetaCoef : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∀ Φ ∈ d.sch,
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ T x, fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = d.orb T (d.om x Φ)

def TAll : Prop := TBij ∧ TPar ∧ TWeyl ∧ TTheta ∧ ThetaAuto

def CoefEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∃ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖

def RDEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), Nonempty (RD d)

def AuxiliaryPrimeFunction : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), (∃ ν, d.IsCov ν) ∧ (∃ ε w, d.IsW ε w ∧ w ∈ rat2 σ d.Y) ∧
  IsTopologicalGroup d.G ∧ LocallyCompactSpace d.G ∧ T2Space d.G ∧ SecondCountableTopology d.G

def FockMem : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), R.fock ≤ d.schM ∧
  (∀ w, ∀ Ψ ∈ R.away w, (∀ P, R.tens w (fP P) Ψ ∈ R.fock) ∧
    ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X) ∧
  ∀ w, ∀ f ∈ R.fock, ∃ (k : ℕ) (P : Fin k → PX d.m d.n) (Ψ : Fin k → Mx F E d.m d.n → ℂ),
    (∀ i, Ψ i ∈ R.away w) ∧ f = ∑ i, R.tens w (fP (P i)) (Ψ i)

def LiftEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ w, ∀ Ψ ∈ R.away w, ∃ φ, R.IsLift w Ψ φ

def LocOpEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ w, ∃ L, R.IsLocOp w L

def LocInst : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ w L, R.IsLocOp w L →
  ∃ (sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)) (ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n) (p q : ℕ) (e : ℤ),
    (d.n ≤ d.m → GoodSig d.n p q) ∧ LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ ∧
    (∀ P y, sL P y = L y (fP P) 0) ∧ ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P)

def GSplit : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ w L, R.IsLocOp w L → ∀ Ψ ∈ R.away w, ∀ φ, R.IsLift w Ψ φ →
  ∀ g : d.G, ∃ (x : d.G) (y : GR d.n) (c : ℂ) (r : ℝ), 0 < r ∧ g = x * R.ι w y ∧
    ∀ y' : GR d.n, (d.Ht (x * R.ι w y') : ℝ) = r * hLoc y' ∧ ∀ P, d.sec0 (φ P) (x * R.ι w y') = c * L y' (fP P) 0

def GIinv : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ w, ∀ Ψ ∈ R.away w, ∀ φ, R.IsLift w Ψ φ →
  ∀ g a b P, d.I (φ (hOp (fun _ => true) (2 * Real.pi) a b P)) g = 0

def GIdil : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ w, ∀ Ψ ∈ R.away w, ∀ φ, R.IsLift w Ψ φ →
  ∀ (g : d.G) (X : Fin d.n → ℝ) (a : ℝ → GR d.n), (∀ t, IsDil X t (a t)) → ∃ (U : Set ℂ) (H : GR d.n → ℂ → ℂ), IsOpen U ∧
    (∀ t : ℝ, (t : ℂ) ∈ U) ∧ ContinuousOn (fun y : GR d.n × ℂ => H y.1 y.2) (Set.univ ×ˢ U) ∧ ∀ y, DifferentiableOn ℂ (H y) U ∧
      (∀ t : ℝ, H y t = d.I (φ 1) (g * R.ι w (y * a t))) ∧
      ∀ r : ℕ, iteratedDeriv r (H y) 0 = d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y)

def KFinPoly : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ Φ, d.KFin Φ → d.T Φ ∈ R.fock

def PolyKFin : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ Φ ∈ d.sch, d.T Φ ∈ R.fock → d.KFin Φ

def SecK : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∀ Φ, d.KFin Φ → IsSec d.K d.χ (s0 d.m d.n) (d.sec0 Φ)

def EisStrong : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), d.Strong → ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁

def LamBd : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∀ L ∈ d.lamSet,
  (∀ (a : ℂ) (f f' : d.G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
    (∀ γ ∈ rat2 σ d.Y, ∀ g, f' (γ * g) = f' g) → L (a • f + f') = a * L f + L f') ∧
  ∃ C : Set d.G, IsCompact C ∧ ∀ (f : d.G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
    (∀ x ∈ C, ‖f x‖ ≤ M) → ‖L f‖ ≤ M

def FourierZero : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ f : d.G → ℂ, Continuous f →
  (∀ β ∈ nF σ d.Y d.b, ∀ g, f (nb β * g) = f g) → (∀ T g, fc d.B.ψ d.b nb lam 𝓖 f T g = 0) → f = 0

def DenseW : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ w (y : GR d.n) (O : Set (GR d.n)), IsOpen O → y ∈ O →
  ∃ γ ∈ rat2 σ d.Y, ∃ y' ∈ O, ∃ x : d.G, γ = x * R.ι w y' ∧ ∀ y'' : GR d.n, x * R.ι w y'' = R.ι w y'' * x

def LamSing : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ w (f : d.G → ℂ), Continuous f → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
  (∀ L ∈ d.lamSet, L f = 0) → ∀ ψ₀, IsSingTest ψ₀ → ∀ nb : (Fin d.n → Fin d.n → ℝ) → GR d.n, (∀ x, mR (nb x) = nU (herm x)) →
    ∀ (g : d.G) (a b : GR d.n), ∫ x, f (g * R.ι w (a * nb x * b)) * ψ₀ x = 0

def Unfold : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ x,
    Integrable (fun β => flat d.a f s₁ z (w * nb β * x)) lam ∧ ∀ T, IsND T →
      fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T x = ∫ β, flat d.a f s₁ z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam

def WhitK : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), d.n < d.m → d.EisAll → ∀ Φ, d.KFin Φ →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ T, IsND T → ∀ x,
    HolValueAt (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
      (s0 d.m d.n) (d.orb T (d.om x Φ))

def Main : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), d.n < d.m → d.EisAll → ∀ Φ, d.KFin Φ → ∀ x,
  HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (d.I Φ x)

def MainOf : Prop :=
  AbsThm → TAll → ThetaCoef → RDEx → AuxiliaryPrimeFunction → FockMem → LiftEx → LocOpEx → LocInst → GSplit → GIinv → GIdil → KFinPoly →
    PolyKFin → SecK → LamBd → LamSing → Unfold → WhitK → Main

def HeadOf : Prop := EisBL → SecK → EisStrong → Main → SWStdLt

end PositivityTheory.SiegelWeilFormula

end
