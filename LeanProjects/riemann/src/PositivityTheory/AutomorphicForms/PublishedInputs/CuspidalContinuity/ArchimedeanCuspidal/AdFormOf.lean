import Mathlib
import GroundTheory.AutomorphicForms.FourierWhittaker
import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke
import GroundTheory.LocalFields.LocalZeta
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import Formalism.RealPlaceAnalysis.StatementE

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3

section Mat

variable {R : Type*} [CommRing R]

def uni (x y z : R) : GL (Fin 3) R :=
  ⟨!![1, x, y; 0, 1, z; 0, 0, 1], !![1, -x, x * z - y; 0, 1, -z; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring,
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring⟩

def dg (a b c : Rˣ) : GL (Fin 3) R :=
  ⟨!![(a : R), 0, 0; 0, b, 0; 0, 0, c], !![((a⁻¹ : Rˣ) : R), 0, 0; 0, (b⁻¹ : Rˣ), 0; 0, 0, (c⁻¹ : Rˣ)],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def cyc (u : R) : GL (Fin 3) R :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, u], !![0, -u, 1; 1, 0, 0; 0, 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def mm (t : Rˣ) (u : R) : GL (Fin 3) R := dg 1 1 t * cyc u

end Mat

section Fin

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def gam (ψ : AddChar F Circle) (μ : Fˣ →* ℂˣ) (s : ℂ) : ℂ :=
  localEpsilon μ ψ s * localLFactor μ⁻¹ (1 - s) / localLFactor μ s

def gam3 (ψ : AddChar F Circle) (ν c : Fˣ →* ℂˣ) (s : ℂ) : ℂ := gam ψ (ν * c) s * gam ψ c s * gam ψ (ν⁻¹ * c) s

def lf3 (ν c : Fˣ →* ℂˣ) (s : ℂ) : ℂ := localLFactor (ν * c) s * localLFactor c s * localLFactor (ν⁻¹ * c) s

def mp (x : Fˣ) (s : ℂ) : ℂ := ((modulus (x : F) : ℝ) : ℂ) ^ s

def IsUnit1 (μ : Fˣ →* ℂˣ) : Prop := Continuous μ ∧ ∀ x, ‖((μ x : ℂˣ) : ℂ)‖ = 1

def zF (W : GL (Fin 3) F → ℂ) (c : Fˣ →* ℂˣ) (s : ℂ) (a : Fˣ) : ℂ := W (dg a 1 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1)

def zF' (W : GL (Fin 3) F → ℂ) (c : Fˣ →* ℂˣ) (s : ℂ) (p : Fˣ × F) : ℂ := W (mm p.1 p.2) * ((c p.1 : ℂˣ) : ℂ) * mp p.1 s

structure WhF (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) (V : Submodule ℂ (GL (Fin 3) F → ℂ)) : Prop where
  ne : V ≠ ⊥
  stable : ∀ W ∈ V, ∀ h, (fun g => W (g * h)) ∈ V
  psi : ∀ W ∈ V, ∀ x y z g, W (uni x y z * g) = (ψ (x + z) : ℂ) * W g
  cen : ∀ W ∈ V, ∀ (a : Fˣ) g, W (dg a a a * g) = W g
  smooth : ∀ W ∈ V, ∃ U : OpenSubgroup (GL (Fin 3) F), ∀ g, ∀ u ∈ U, W (g * u) = W g
  gauge : ∀ W ∈ V, ∃ (C B : ℝ) (T : ℕ), ∀ (a b : Fˣ), ∀ k ∈ GLnLocal.integralGL F 3,
    ‖W (dg (a * b) b 1 * k)‖ ≤ C / ((modulus (a : F) : ℝ) * modulus (b : F)) ^ T ∧
      (W (dg (a * b) b 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B ∧ (modulus (b : F) : ℝ) ≤ B)
  int : ∀ W ∈ V, ∀ s : ℂ, 1 / 4 < s.re → Integrable (zF W 1 s) (multHaar F)
  int' : ∀ W ∈ V, ∀ s : ℂ, s.re < 3 / 4 → Integrable (zF' W 1 s) ((multHaar F).prod (selfDualMeasure ψ))
  fe : ∀ W ∈ V, ∀ c, IsUnit1 c → ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 →
    ∫ p, zF' W c s p ∂((multHaar F).prod (selfDualMeasure ψ)) =
      gam3 ψ ν c s * ∫ a, zF W c s a ∂multHaar F

def sphW (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) : GL (Fin 3) F → ℂ :=
  Spherical.sphericalWhittaker (Circle.coeHom.compAddChar ψ) ![ν (unifUnit F), 1, (ν (unifUnit F))⁻¹]

def IsStd (ψ : AddChar F Circle) : Prop := Continuous ψ ∧ ψ ≠ 1 ∧ addCharConductor ψ = 0

end Fin

def LocF : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (ψ : AddChar F Circle), IsStd ψ → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν →
    ∃ V, WhF ψ ν V ∧ (IsUnramifiedChar ν → sphW ψ ν ∈ V)

def LocU : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (ψ : AddChar F Circle), IsStd ψ → ∀ ν c : Fˣ →* ℂˣ, IsUnit1 ν → IsUnit1 c → IsUnramifiedChar ν → IsUnramifiedChar c →
    (∀ s : ℂ, 0 < s.re → ∫ a, zF (sphW ψ ν) c s a ∂multHaar F = lf3 ν c s) ∧
    (∀ s : ℂ, s.re < 1 → ∫ p, zF' (sphW ψ ν) c s p ∂((multHaar F).prod (selfDualMeasure ψ)) = lf3 ν c⁻¹ (1 - s)) ∧
    (∀ (t : Fˣ) (u : F), (u ∈ 𝒪[F] → sphW ψ ν (mm t u) = sphW ψ ν (dg 1 1 t)) ∧ (u ∉ 𝒪[F] → sphW ψ ν (mm t u) = 0)) ∧
    ∀ (a b : Fˣ), ∀ k ∈ GLnLocal.integralGL F 3, ‖sphW ψ ν (dg (a * b) b 1 * k)‖ ≤ ((modulus (a : F) : ℝ) * modulus (b : F))⁻¹ ∧
      (sphW ψ ν (dg (a * b) b 1 * k) ≠ 0 → (a : F) ∈ 𝒪[F] ∧ (b : F) ∈ 𝒪[F])

abbrev M3 : Type := Fin 3 → Fin 3 → ℝ

def ext (W : GL (Fin 3) ℝ → ℂ) (m : M3) : ℂ :=
  if h : (Matrix.of m).det ≠ 0 then W (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of m) h) else 0

def SmoothR (W : GL (Fin 3) ℝ → ℂ) : Prop := ContDiffOn ℝ (⊤ : ℕ∞) (ext W) {m | (Matrix.of m).det ≠ 0}

def der (i j : Fin 3) (W : GL (Fin 3) ℝ → ℂ) (g : GL (Fin 3) ℝ) : ℂ :=
  fderiv ℝ (ext W) (Matrix.of.symm g.val) (Matrix.of.symm (g.val * Matrix.single i j 1))

def psiR (x : ℝ) : ℂ := Complex.exp (-2 * Real.pi * Complex.I * x)

def chR (δ : Bool) (s : ℂ) (a : ℝˣ) : ℂ := (if δ ∧ (a : ℝ) < 0 then -1 else 1) * ((|(a : ℝ)| : ℝ) : ℂ) ^ s

def lR (k : ℕ) (δ : Bool) (s : ℂ) : ℂ := Complex.Gammaℂ (s + k - 1) * Complex.Gammaℝ (s + if δ then 0 else 1)

def gamR (k : ℕ) (δ : Bool) (s : ℂ) : ℂ := (-Complex.I) ^ (2 * k - if δ then 1 else 0) * lR k δ (1 - s) / lR k δ s

def mulR : Measure ℝˣ := Measure.comap Units.val (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹)

def O3 : Set (GL (Fin 3) ℝ) := {k | k.val * k.valᵀ = 1}

structure WhR (k : ℕ) (V : Submodule ℂ (GL (Fin 3) ℝ → ℂ)) (E : Fin 3 → Fin 3 → Module.End ℂ V) : Prop where
  stable : ∀ W ∈ V, ∀ h, (fun g => W (g * h)) ∈ V
  psi : ∀ W ∈ V, ∀ x y z g, W (uni x y z * g) = psiR (x + z) * W g
  cen : ∀ W ∈ V, ∀ (a : ℝˣ) g, W (dg a a a * g) = W g
  smooth : ∀ W ∈ V, SmoothR W
  lie : ∀ i j (W : V), (E i j W : GL (Fin 3) ℝ → ℂ) = der i j W
  gauge : ∀ W ∈ V, ∃ T : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ (a b : ℝˣ), ∀ o ∈ O3,
    ‖W (dg (a * b) b 1 * o)‖ ≤ C / (|(a : ℝ)| * |(b : ℝ)|) ^ T / ((1 + |(a : ℝ)|) * (1 + |(b : ℝ)|)) ^ N
  int : ∀ W ∈ V, ∀ s : ℂ, 1 / 4 < s.re → Integrable (fun a => W (dg a 1 1) * chR false (s - 1) a) mulR
  int' : ∀ W ∈ V, ∀ s : ℂ, s.re < 3 / 4 → Integrable (fun p : ℝˣ × ℝ => W (mm p.1 p.2) * chR false s p.1) (mulR.prod volume)
  fe : ∀ W ∈ V, ∀ (δ : Bool) (s : ℂ), 1 / 4 < s.re → s.re < 3 / 4 →
    ∫ p : ℝˣ × ℝ, W (mm p.1 p.2) * chR δ s p.1 ∂(mulR.prod volume) =
      gamR k δ s * ∫ a, W (dg a 1 1) * chR δ (s - 1) a ∂mulR
  cap : ∀ (u : ℂ) (W : V), Formalism.REAL.qdet E (u + 1) W = ((u + (k - 1)) * u * (u - (k - 1))) • W
  kfin : ∃ W ∈ V, W ≠ 0 ∧ FiniteDimensional ℂ (Submodule.span ℂ {W' | ∃ o ∈ O3, W' = fun g => W (g * o)})

def LocR : Prop := ∀ k : ℕ, 3 ≤ k → ∃ V E, WhR k V E

abbrev Pl : Type := HeightOneSpectrum (𝓞 ℚ)
abbrev Qv (v : Pl) : Type := v.adicCompletion ℚ
abbrev G3 : Type := AdelicGLn.AdelicGL ℚ 3

instance (v : Pl) : MeasurableSpace (Qv v) := borel _
instance (v : Pl) : BorelSpace (Qv v) := ⟨rfl⟩

structure Dat where
  k : ℕ
  three : 3 ≤ k
  ν : ∀ v : Pl, (Qv v)ˣ →* ℂˣ
  unit : ∀ v, IsUnit1 (ν v)
  bad : Finset Pl
  unr : ∀ v ∉ bad, IsUnramifiedChar (ν v)

structure admitted (D : Dat) (c : HeckeCharacter ℚ) (δ : Bool) (S : Finset Pl) : Prop where
  fin : IsOfFinOrder c
  sgn : ∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1
  bad : D.bad ⊆ S
  unr : ∀ v ∉ S, IsUnramifiedChar (localChar c v)

def eul (D : Dat) (c : HeckeCharacter ℚ) (S : Finset Pl) (s : ℂ) : ℂ :=
  ∏' v : {v : Pl // v ∉ S}, lf3 (D.ν v.1) (localChar c v.1) s

def gamS (D : Dat) (c : HeckeCharacter ℚ) (δ : Bool) (S : Finset Pl) (s : ℂ) : ℂ :=
  gamR D.k δ s * ∏ v ∈ S, gam3 (localAdelicChar ℚ v) (D.ν v) (localChar c v) s

def Ord (Λ : ℂ → ℂ) (a : ℝ) : Prop := ∀ b : ℝ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Λ s‖ ≤ C * Real.exp (C * s.im ^ 2)

def Cont (D : Dat) (c : HeckeCharacter ℚ) (S : Finset Pl) (e : ℕ) (Λ : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Λ {s | 1 / 4 < s.re} ∧ Ord Λ (1 / 3) ∧ ∀ s : ℂ, 1 < s.re → Λ s = (s - 1) ^ e * eul D c S s

def An (D : Dat) : Prop :=
  ∀ c δ S, admitted D c δ S → ∃ Λ Λ', Cont D c S 0 Λ ∧ Cont D c⁻¹ S 0 Λ' ∧
    ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 → Λ s = gamS D c δ S s * Λ' (1 - s)

def EA (i j : Fin 3) : Module.End ℂ (archSmooth ℚ 3) :=
  uAction (UniversalEnvelopingAlgebra.ι ℝ (⟨(Matrix.single i j 1 : Matrix (Fin 3) (Fin 3) (mixedEmbedding.mixedSpace ℚ)),
    Submodule.mem_top⟩ : (isExpLieAlgebra ℚ 3).lieSubalgebra))

abbrev dia (γ : GL (Fin 3) ℚ) : G3 := AdelicGLn.diagonal ℚ 3 γ

structure WhA (V : Submodule ℂ (G3 → ℂ)) : Prop where
  stable : ∀ W ∈ V, ∀ h, (fun g => W (g * h)) ∈ V
  psi : ∀ W ∈ V, ∀ x y z g, W (uni x y z * g) = (adelicChar ℚ (x + z) : ℂ) * W g
  cen : ∀ W ∈ V, ∀ (a : (𝔸[ℚ])ˣ) g, W (dg a a a * g) = W g
  arch : ∀ W ∈ V, IsArchSmooth W
  level : ∀ W ∈ V, ∃ U : OpenSubgroup (AdelicGLn.FiniteAdelicGL ℚ 3), ∀ g, ∀ u ∈ U, W (g * finEmb ℚ 3 u) = W g
  lie : ∀ W (hW : W ∈ V) i j, ((EA i j ⟨W, arch W hW⟩ : archSmooth ℚ 3) : G3 → ℂ) ∈ V
  gauge : ∀ W ∈ V, ∃ Ω : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact Ω ∧ ∃ T : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ a b : (𝔸[ℚ])ˣ,
    ∀ k ∈ (Reduction.maxCompact : Subgroup G3), ∀ w : InfinitePlace ℚ,
      ‖W (dg (a * b) b 1 * k)‖ ≤ C / ((IdeleGroup.ideleModule ℚ a : ℝ) * IdeleGroup.ideleModule ℚ b) ^ T /
        ((1 + ‖(a : 𝔸[ℚ]).1 w‖) * (1 + ‖(b : 𝔸[ℚ]).1 w‖)) ^ N ∧
      (W (dg (a * b) b 1 * k) ≠ 0 → (a : 𝔸[ℚ]).2 ∈ Ω ∧ (b : 𝔸[ℚ]).2 ∈ Ω)

def Vor (W : G3 → ℂ) : Prop :=
  ∑' a : ℚˣ, W (dia (dg a 1 1)) = ∑' b : ℚˣ, ∫ u, W (dia (dg 1 1 b) * cyc u) ∂adeleMeasure ℚ

def ConvA : Prop :=
  ∀ V, ∀ hV : WhA V, (∀ W ∈ V, Vor W) → ∃ U : V →ₗ[ℂ] archSmooth ℚ 3,
    (∀ W : V, IsLeftInvariant (U W : G3 → ℂ) ∧ HasModerateGrowth (U W : G3 → ℂ) ∧ IsCuspidal (U W : G3 → ℂ) ∧
      FourierWhittaker.whittaker (U W : G3 → ℂ) = W) ∧
    (∀ (W : V) h g, (U ⟨fun x => W.1 (x * h), hV.stable _ W.2 h⟩ : G3 → ℂ) g = (U W : G3 → ℂ) (g * h)) ∧
    ∀ (W : V) i j, U ⟨_, hV.lie _ W.2 i j⟩ = EA i j (U W)

def Mellin : Prop :=
  ∀ f₁ f₂ : IdeleGroup ℚ → ℂ, Continuous f₁ → Continuous f₂ →
    (∃ U : OpenSubgroup (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ u ∈ U, ∀ x, f₁ (x * IdeleGroup.ofFinite u) = f₁ x ∧ f₂ (x * IdeleGroup.ofFinite u) = f₂ x) →
    (∀ K : Set (IdeleGroup ℚ), IsCompact K → ∃ b : ℚˣ → ℝ, Summable b ∧ ∀ a : ℚˣ, ∀ x ∈ K,
      ‖f₁ (Units.map (algebraMap ℚ 𝔸[ℚ]).toMonoidHom a * x)‖ ≤ b a ∧ ‖f₂ (Units.map (algebraMap ℚ 𝔸[ℚ]).toMonoidHom a * x)‖ ≤ b a) →
    ∀ σ : ℝ, 0 < σ → Integrable (fun x => ‖f₁ x‖ * (IdeleGroup.ideleModule ℚ x : ℝ) ^ σ) (ideleMeasure ℚ) →
    Integrable (fun x => ‖f₂ x‖ * (IdeleGroup.ideleModule ℚ x : ℝ) ^ (-σ)) (ideleMeasure ℚ) →
    (∀ c : HeckeCharacter ℚ, IsOfFinOrder c → ∃ M : ℂ → ℂ, Differentiable ℂ M ∧ Ord M (-σ) ∧
      (∀ s : ℂ, s.re = σ → M s = ∫ x, f₁ x * (c.toIdele x : ℂ) * ((IdeleGroup.ideleModule ℚ x : ℝ) : ℂ) ^ s ∂ideleMeasure ℚ) ∧
      ∀ s : ℂ, s.re = -σ → M s = ∫ x, f₂ x * (c.toIdele x : ℂ) * ((IdeleGroup.ideleModule ℚ x : ℝ) : ℂ) ^ s ∂ideleMeasure ℚ) →
    ∑' a : ℚˣ, f₁ (Units.map (algebraMap ℚ 𝔸[ℚ]).toMonoidHom a) = ∑' a : ℚˣ, f₂ (Units.map (algebraMap ℚ 𝔸[ℚ]).toMonoidHom a)

def IsLoc (v : Pl) (x : GL (Fin 3) (Qv v)) (h : G3) : Prop :=
  Reduction.finAt v h = x ∧ (∀ v' ≠ v, Reduction.finAt v' h = 1) ∧ ∀ w, Reduction.infAt w h = 1

def SphAt (D : Dat) (v : Pl) (W : G3 → ℂ) : Prop :=
  ∀ g : G3, Reduction.finAt v g = 1 → ∀ x h, IsLoc v x h → W (g * h) = W g * sphW (localAdelicChar ℚ v) (D.ν v) x

def Good (D : Dat) (V : Submodule ℂ (G3 → ℂ)) (hV : WhA V) : Prop :=
  (∀ W ∈ V, Vor W) ∧
  (∀ W (hW : W ∈ V) (u : ℂ), Formalism.REAL.qdet EA (u + 1) ⟨W, hV.arch W hW⟩ =
    ((u + (D.k - 1)) * u * (u - (D.k - 1))) • (⟨W, hV.arch W hW⟩ : archSmooth ℚ 3)) ∧
  (∀ W (hW : W ∈ V), (∑ i, EA i i) ⟨W, hV.arch W hW⟩ = 0) ∧
  ∃ W ∈ V, W ≠ 0 ∧ IsKFinite W ∧ ∃ S : Finset Pl, ∀ v ∉ S, SphAt D v W

def Glob : Prop := LocF → LocU → LocR → Mellin → ∀ D, An D → ∃ V hV, Good D V hV

open UpperHalfPlane CongruenceSubgroup in
open scoped MatrixGroups ModularForm in

structure IsForm (k N : ℕ) (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) (k : ℤ)) (a : ℕ → ℂ) : Prop where
  char : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → (f : ℍ → ℂ) ∣[(k : ℤ)] γ = χ ((γ 1 1 : ℤ) : ZMod N) • (f : ℍ → ℂ)
  exp : ∀ τ : ℍ, HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * τ)) (f τ)

def IsEig (k N : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ) : Prop :=
  a 0 = 0 ∧ a 1 = 1 ∧ ∀ p n : ℕ, p.Prime → a p * a n = a (p * n) + if p ∣ n then χ p * (p : ℂ) ^ (k - 1) * a (n / p) else 0

def Shim : Prop :=
  ∀ (k N M : ℕ) [NeZero N] [NeZero M] (hM : N ∣ M), 4 ∣ M → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) f a, IsForm k N χ f a →
    ∀ c : DirichletCharacter ℂ M, ∃ Λ : ℂ → ℂ, DifferentiableOn ℂ Λ {s | 1 / 4 < s.re} ∧ Ord Λ (1 / 3) ∧
      ∀ s : ℂ, 2 < s.re → Λ s = (s - 1) * DirichletCharacter.LFunction (c ^ 2) (2 * s) *
        LSeries (fun n => (c * DirichletCharacter.changeLevel hM χ⁻¹) n * a (n ^ 2)) (s + k - 1)

def pOf (v : Pl) : ℕ := Ideal.absNorm v.asIdeal

def SatOf (N : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ) (D : Dat) : Prop :=
  (∀ v, v ∈ D.bad ↔ pOf v ∣ N) ∧ ∀ v ∉ D.bad, ∃ α β : ℂˣ, (α : ℂ) + β = a (pOf v) ∧
    (α : ℂ) * β = χ (pOf v) * (pOf v : ℂ) ^ (D.k - 1) ∧ D.ν v (unifUnit (Qv v)) = α / β

def Pure (k N : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ α β : ℂ, α + β = a p → α * β = χ p * (p : ℂ) ^ (k - 1) → ‖α‖ = ‖β‖

def Dih (a : ℕ → ℂ) : Prop :=
  ∃ η : HeckeCharacter ℚ, η ≠ 1 ∧ η ^ 2 = 1 ∧ ∀ᶠ v : Pl in cofinite, IsUnramifiedChar (localChar η v) ∧
    (localChar η v (unifUnit (Qv v)) = 1 ∨ a (pOf v) = 0)

def FE (a : ℕ → ℂ) (D : Dat) : Prop :=
  ∀ c δ S, admitted D c δ S → ∀ Λ Λ', Cont D c S 1 Λ → Cont D c⁻¹ S 1 Λ' →
    (∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 → -s * Λ s = (s - 1) * gamS D c δ S s * Λ' (1 - s)) ∧ (Dih a ∨ Λ 1 = 0)

def RS : Prop :=
  ∀ (k N : ℕ) [NeZero N], 3 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ f a, IsForm k N χ f a → IsEig k N χ a →
    Pure k N χ a → ∃ D : Dat, D.k = k ∧ SatOf N χ a D ∧ FE a D

def EulOf : Prop :=
  Shim → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (D : Dat) f a, IsForm D.k N χ f a → IsEig D.k N χ a → SatOf N χ a D →
    ∀ c δ S, admitted D c δ S → ∃ Λ, Cont D c S 1 Λ

def AnOf : Prop :=
  ∀ a D, FE a D → (∀ c δ S, admitted D c δ S → ∃ Λ, Cont D c S 1 Λ) → Dih a ∨ An D

def AdForm : Prop :=
  ∀ (k N : ℕ) [NeZero N], 3 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ f a, IsForm k N χ f a → IsEig k N χ a →
    Pure k N χ a → Dih a ∨ ∃ D : Dat, D.k = k ∧ SatOf N χ a D ∧ ∃ V hV, Good D V hV ∧ ∃ U : V →ₗ[ℂ] archSmooth ℚ 3,
    (∀ W : V, IsLeftInvariant (U W : G3 → ℂ) ∧ HasModerateGrowth (U W : G3 → ℂ) ∧ IsCuspidal (U W : G3 → ℂ) ∧
      FourierWhittaker.whittaker (U W : G3 → ℂ) = W) ∧
    (∀ (W : V) h g, (U ⟨fun x => W.1 (x * h), hV.stable _ W.2 h⟩ : G3 → ℂ) g = (U W : G3 → ℂ) (g * h)) ∧
    ∀ (W : V) i j, U ⟨_, hV.lie _ W.2 i j⟩ = EA i j (U W)

theorem adForm_of (h1 : LocF) (h2 : LocU) (h3 : LocR) (h4 : Mellin) (h5 : Glob) (h6 : ConvA) (h7 : Shim) (h8 : RS)
    (h9 : EulOf) (h10 : AnOf) : AdForm := by
  intro k N _ hk χ hχ f a hf ha hp
  obtain ⟨D, rfl, hs, hfe⟩ := h8 k N hk χ hχ f a hf ha hp
  rcases h10 a D hfe (h9 h7 N χ D f a hf ha hs) with h | h
  · exact Or.inl h
  obtain ⟨V, hV, hg⟩ := h5 h1 h2 h3 h4 D h
  exact Or.inr ⟨D, rfl, hs, V, hV, hg, h6 V hV hg.1⟩

end Ad3
