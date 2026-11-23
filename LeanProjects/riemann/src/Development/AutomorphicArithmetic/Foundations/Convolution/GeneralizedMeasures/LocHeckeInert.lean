import Development.AutomorphicArithmetic.Foundations.Convolution.ASmooth
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong
import GroundTheory.AutomorphicForms.SatakeNormalized

noncomputable section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical

namespace UpperTheory.ConvolutionTheory.GM

section One

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

open Classical in

def conv (ν : Measure (archGroup K n)) (β γ : TI K n) : TI K n :=
  if h : ∃ δ : TI K n, ∀ g, δ g = ∫ x, β x * γ (x⁻¹ * g) ∂ν then h.choose else 0

def letter (a₀ : TI K n) : Option (Ix K n) → TI K n
  | none => a₀
  | some x => lact (zc x.1 x.2) a₀

def word (ν : Measure (archGroup K n)) (a₀ : TI K n) : List (Option (Ix K n)) → TI K n
  | [] => a₀
  | x :: w => conv ν (letter a₀ x) (word ν a₀ w)

def onInf (β : TI K n) (g : GL (Fin n) (InfiniteAdeleRing K)) : ℂ := β (archEquiv K n g)

def IsSph (w : Pl K) (p : MvPolynomial (Fin n) ℂ) (h : GL (Fin n) (w.adicCompletion K) → ℂ) : Prop :=
  ∃ (_ : MeasurableSpace (GL (Fin n) (w.adicCompletion K))) (_ : BorelSpace (GL (Fin n) (w.adicCompletion K)))
    (m : Measure (GL (Fin n) (w.adicCompletion K))) (_ : m.IsHaarMeasure),
    m (GLnLocal.integralGL (w.adicCompletion K) n) = 1 ∧ ∃ H : SphericalHecke m (F := w.adicCompletion K) (n := n),
      (∀ x, (H : HeckeAlgebra m) x = h x) ∧
        satakeTransform m H = polyEmb n (aeval (fun i : Fin n => esymm (Fin n) ℂ (i + 1)) p)

def iwCoset (w : Pl K) (ν : Fin n → ℤ) : Set (GL (Fin n) (w.adicCompletion K)) :=
  {g | ∃ a ∈ GLnLocal.iwahori (w.adicCompletion K) n, ∃ b ∈ GLnLocal.iwahori (w.adicCompletion K) n,
    g = a * Cartan.diagPow (w.adicCompletion K) n ν * b}

def levF (lev : ∀ v : Pl K, Subgroup (GL (Fin n) (v.adicCompletion K))) : Subgroup (AdelicGLn.FiniteAdelicGL K n) where
  carrier := {h | ∀ v, finAt v (finEmb K n h) ∈ lev v}
  one_mem' v := by rw [map_one, finAt_one]; exact one_mem _
  mul_mem' {a b} ha hb v := by
    rw [map_mul, finAt_mul]; exact mul_mem (ha v) (hb v)
  inv_mem' {a} ha v := by
    rw [map_inv, finAt_inv]; exact inv_mem (ha v)

def sphOp (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K) (h : GL (Fin n) (w.adicCompletion K) → ℂ) : LL μ →L[ℂ] LL μ :=
  ∑ᶠ c : GL (Fin n) (w.adicCompletion K) ⧸ GLnLocal.integralGL (w.adicCompletion K) n, h c.out • rhoL μ w c.out

def Good (ν : Fin n → ℤ) : Prop :=
  StrictAnti ν ∧ ∑ i, ν i = 0 ∧ ∀ J : Finset (Fin n), J.Nonempty → J ≠ Finset.univ → ∑ i ∈ J, ν i ≠ 0

end One

section Two

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def cmp {v : Pl F} (w : PlacesOver E v) : GL (Fin n) (CompletionsOver E v) →* GL (Fin n) (w.1.adicCompletion E) :=
  mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)

def prodFn {v : Pl F} (h : ∀ w : PlacesOver E v, GL (Fin n) (w.1.adicCompletion E) → ℂ) (g : GL (Fin n) (CompletionsOver E v)) : ℂ :=
  ∏ᶠ w, h w (cmp w g)

open Classical in

def iwFn {q : Pl F} (w₀ : PlacesOver E q) (ν : Fin n → ℤ) : GL (Fin n) (CompletionsOver E q) → ℂ :=
  prodFn fun w => (iwCoset w.1 (if w = w₀ then ν else 0)).indicator 1

def levE (lev : ∀ v : Pl F, Subgroup (GL (Fin n) (CompletionsOver E v))) : Subgroup (AdelicGLn.FiniteAdelicGL E n) :=
  ⨅ v, (lev v).comap ((mapGL n (atFin v)).comp (finEmb E n))

def resIx (F : Type) [Field F] [NumberField F] [Algebra F E] : Option (Ix E n) → Option (Ix F n) :=
  Option.map fun x => (x.1.comp (algebraMap F E), x.2)

def ArchPair (σ : E ≃ₐ[F] E) (νE : Measure (archGroup E n)) (νF : Measure (archGroup F n)) (aE : TI E n) (aF : TI F n) (c : ℝ) : Prop :=
  ∀ [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing E))] [BorelSpace (GL (Fin n) (InfiniteAdeleRing E))]
    [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing F))] [BorelSpace (GL (Fin n) (InfiniteAdeleRing F))]
    (w : List (Option (Ix E n))),
    Match (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) (galInf σ) (Module.finrank F E)
      (νE.map (archEquiv E n).symm) (νF.map (archEquiv F n).symm) c (onInf (word νE aE w)) (onInf (word νF aF (w.map (resIx F))))

def MatchAt (σ : E ≃ₐ[F] E) (v : Pl F) (c : ℂ) (φ : GL (Fin n) (CompletionsOver E v) → ℂ) (f : GL (Fin n) (v.adicCompletion F) → ℂ) : Prop :=
  ∀ [MeasurableSpace (GL (Fin n) (CompletionsOver E v))] [BorelSpace (GL (Fin n) (CompletionsOver E v))]
    [MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [BorelSpace (GL (Fin n) (v.adicCompletion F))]
    (mE : Measure (GL (Fin n) (CompletionsOver E v))) (mF : Measure (GL (Fin n) (v.adicCompletion F))),
    mE.IsHaarMeasure → mF.IsHaarMeasure → mE (unitSet E n v) = 1 → mF (GLnLocal.integralGL (v.adicCompletion F) n) = 1 →
    Match (incFin E v) (galFin σ v) (Module.finrank F E) mE mF c φ f

variable (E) in

def Unr (v : Pl F) : Prop := ∀ w : PlacesOver E v, Algebra.IsUnramifiedAt (𝓞 F) w.1.asIdeal

variable (E) in

def Split (v : Pl F) : Prop := ∀ w : PlacesOver E v, Function.Surjective (completionMap v w.1)

structure Loc (σ : E ≃ₐ[F] E) (n : ℕ) (q : Pl F) (w₀ : PlacesOver E q) where
  S : Finset (Pl F)
  q_not : q ∉ S
  unr : ∀ v ∉ S, Unr E v
  φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ
  f : ∀ v : Pl F, GL (Fin n) (v.adicCompletion F) → ℂ
  c : Pl F → ℂ
  UE : ∀ v : Pl F, Subgroup (GL (Fin n) (CompletionsOver E v))
  UF : ∀ v : Pl F, Subgroup (GL (Fin n) (v.adicCompletion F))
  test : ∀ v ∈ S, IsLocallyConstant (φ v) ∧ HasCompactSupport (φ v) ∧ IsLocallyConstant (f v) ∧ HasCompactSupport (f v)
  lev : ∀ v ∈ S, IsOpen (UE v : Set (GL (Fin n) (CompletionsOver E v))) ∧ (UE v : Set _) ⊆ unitSet E n v ∧
    IsOpen (UF v : Set (GL (Fin n) (v.adicCompletion F))) ∧ UF v ≤ GLnLocal.integralGL (v.adicCompletion F) n
  inv : ∀ v ∈ S, (∀ u ∈ UE v, ∀ g, φ v (u * g) = φ v g) ∧ ∀ u ∈ UF v, ∀ g, f v (u * g) = f v g
  mat : ∀ v ∈ S, MatchAt σ v (c v) (φ v) (f v)
  at_q : φ q = iwFn w₀ 0 ∧ f q = (iwCoset q 0).indicator 1 ∧
    (∀ g, g ∈ UE q ↔ ∀ w, cmp w g ∈ GLnLocal.iwahori (w.1.adicCompletion E) n) ∧ UF q = GLnLocal.iwahori (q.adicCompletion F) n
  off : ∀ v ∉ S, v ≠ q → φ v = (unitSet E n v).indicator 1 ∧
    f v = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1 ∧ (UE v : Set _) = unitSet E n v ∧
    UF v = GLnLocal.integralGL (v.adicCompletion F) n

variable {μE : Measure (normOneGL E n)} [μE.IsHaarMeasure] {μF : Measure (normOneGL F n)} [μF.IsHaarMeasure] {θ : Twist μE} {l : ℕ}
  {σ : E ≃ₐ[F] E} {q : Pl F} {w₀ : PlacesOver E q}

def IsSideE (L : Loc σ n q w₀) (νE : Measure (archGroup E n)) (aE : TI E n) (ν : Fin n → ℤ) (𝔢 : Side θ l) : Prop :=
  𝔢.ν = νE ∧ 𝔢.a₀ = aE ∧ (∀ w, w ∈ 𝔢.S ↔ w.under (𝓞 F) ∈ L.S ∨ w.under (𝓞 F) = q) ∧ 𝔢.U = levE L.UE ∧
    (∀ x, 𝔢.g x = avg (tensE (onInf aE) L.φ) x) ∧ 𝔢.Uq 0 = Uiw μE w₀.1 ν

def IsSideF (L : Loc σ n q w₀) (νF : Measure (archGroup F n)) (aF : TI F n) (ν : Fin n → ℤ) (𝔣 : Side (Twist.id μF) l) : Prop :=
  𝔣.ν = νF ∧ 𝔣.a₀ = aF ∧ (∀ v, v ∈ 𝔣.S ↔ v ∈ L.S ∨ v = q) ∧ 𝔣.U = levF L.UF ∧
    (∀ x, 𝔣.g x = avg (tensF (onInf aF) L.f) x) ∧ 𝔣.Uq 0 = Uiw μF q ν

end Two

def AmpFn {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (a : TI K n) : Prop :=
  SmoothT a ∧ LeftFin a ∧ 0 ≤ Oinf μ ν a ∧ ‖Oinf μ ν a‖ ≤ 1

def LocUnit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n → ∀ v : Pl F, Unr E v →
    MatchAt σ v 1 ((unitSet E n v).indicator 1) ((GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1)

def LocHeckeSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n → ∀ v : Pl F, Split E v →
    ∀ (p : PlacesOver E v → MvPolynomial (Fin n) ℂ) (h : ∀ w : PlacesOver E v, GL (Fin n) (w.1.adicCompletion E) → ℂ)
      (f : GL (Fin n) (v.adicCompletion F) → ℂ), (∀ w, IsSph w.1 (p w) (h w)) → IsSph v (∏ᶠ w, p w) f → MatchAt σ v 1 (prodFn h) f

def LocHeckeInert : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n → ∀ v : Pl F, Unr E v → ¬ Split E v →
    ∀ (w : PlacesOver E v) (t : Multiset ℂ), t.card = n → 0 ∉ t → ∀ D : ℕ,
      ∃ γ : MvPolynomial (Fin n) ℂ, eval (fun i : Fin n => t.esymm (i + 1)) γ ≠ 0 ∧
        ∀ p : MvPolynomial (Fin n) ℂ, p.totalDegree ≤ D → ∀ h f, IsSph w.1 (γ * p) h →
          IsSph v (aeval (powE (Module.finrank F E)) (γ * p)) f → MatchAt σ v 1 (fun g => h (cmp w g)) f

def LocQ : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n → ∀ q : Pl F, Split E q →
    ∃ c : ℝ, 0 < c ∧ ∀ (w₀ : PlacesOver E q) (ν : Fin n → ℤ), MatchAt σ q c (iwFn w₀ ν) ((iwCoset q ν).indicator 1)

def GM : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μE : Measure (normOneGL E n)) [μE.IsHaarMeasure] (μF : Measure (normOneGL F n)) [μF.IsHaarMeasure] (θ : Twist μE),
      IsGalTwist σ θ → ∀ (q : Pl F) (w₀ : PlacesOver E q), Split E q →
    ∀ (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (aE : TI E n) (aF : TI F n)
      (ci : ℝ), 0 < ci → AmpFn μE νE aE → AmpFn μF νF aF → ArchPair σ νE νF aE aF ci →
    ∃ κ : ℝ, 0 < κ ∧ ∀ (L : Loc σ n q w₀) (ν : Fin n → ℤ), Good ν →
      ∃ (𝔢 : Side θ (Module.finrank F E)) (𝔣 : Side (Twist.id μF) (Module.finrank F E)),
        IsSideE L νE aE ν 𝔢 ∧ IsSideF L νF aF ν 𝔣 ∧ GeoPair 𝔢 𝔣 (κ * ∏ v ∈ L.S, L.c v)

end UpperTheory.ConvolutionTheory.GM
