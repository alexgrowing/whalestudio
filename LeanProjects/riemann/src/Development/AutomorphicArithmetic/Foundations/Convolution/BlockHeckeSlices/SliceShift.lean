import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Summand
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe

noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

structure AbsSys {τ κ A V : Type} [Fintype τ] {n r : ℕ} [CommRing A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V] [Module A V]
    (Z : τ × Fin n → A) (H : κ → A) (I : Fin r → A) (t : Multiplicative (Fin r → ℝ) →* A) (c : V →ₗ[ℂ] ((Fin r → ℝ) → ℂ))
    (idx : Fin n → Fin r) (Λ : τ × Fin n → ℂ) (h : κ → EP (Fin r)) (good : Set κ) (C : ℝ) : Prop where
  surj : Function.Surjective idx
  shift : ∀ v φ x, c (t (Multiplicative.ofAdd v) • φ) x = c φ (x + v)
  deriv : ∀ j φ x, HasDerivAt (fun s : ℝ => c φ (x + Pi.single j s)) (c (I j • φ) x) 0
  cen : ∀ p φ, c (Z p • φ) = c (MvPolynomial.aeval (fun q => algebraMap ℂ A (Λ q) + I (idx q.2)) (blockE p) • φ)
  hecke : ∀ k ∈ good, ∀ φ, c (H k • φ) = c (lift I t (h k) • φ)
  bound : ∀ (φ : V) (β : Fin r →₀ ℕ) (R : ℝ), ∃ B : ℝ, ∀ (α : (τ × Fin n) →₀ ℕ) (x : Fin r → ℝ), ‖x‖ ≤ R →
    ‖c ((α.prod (fun p e => Z p ^ e) * β.prod fun j e => I j ^ e) • φ) x‖ ≤ B * C ^ α.degree

def AbsFar : Prop :=
  ∀ (τ : Type) [Fintype τ] [Nonempty τ] (n : ℕ) (C S₀ : ℝ), ∃ B : ℝ,
    ∀ (κ A V : Type) (r : ℕ) [CommRing A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
      (Z : τ × Fin n → A) (H : κ → A) (I : Fin r → A) (t : Multiplicative (Fin r → ℝ) →* A) (c : V →ₗ[ℂ] ((Fin r → ℝ) → ℂ))
      (idx : Fin n → Fin r) (Λ : τ × Fin n → ℂ) (h : κ → EP (Fin r)) (good : Set κ), AbsSys Z H I t c idx Λ h good C →
      (∀ j, ‖∑ p ∈ Finset.univ.filter fun p : τ × Fin n => idx p.2 = j, Λ p‖ ≤ S₀) → (∃ p, B < ‖Λ p‖) → c = 0

def AbsKill : Prop :=
  ∀ (τ κ A V : Type) [Fintype τ] [Nonempty τ] (n r : ℕ) [CommRing A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V] [Module A V]
    [IsScalarTower ℂ A V] (Z : τ × Fin n → A) (H : κ → A) (I : Fin r → A) (t : Multiplicative (Fin r → ℝ) →* A)
    (c : V →ₗ[ℂ] ((Fin r → ℝ) → ℂ)) (idx : Fin n → Fin r) (Λ : τ × Fin n → ℂ) (h : κ → EP (Fin r)) (good : Set κ) (C : ℝ),
    AbsSys Z H I t c idx Λ h good C → ∀ (F : KF (τ × Fin n) κ) (G : ℕ → MvPolynomial κ (MvPolynomial (τ × Fin n) ℂ)),
    (∀ k ∈ F.vars, k ∈ good) → (∀ z : Fin r → ℂ, evK (fun p => Λ p + z (idx p.2)) (fun k => ev z (h k)) F = 0) →
    (∀ k, MvPolynomial.map (MvPolynomial.aeval blockE : MvPolynomial (τ × Fin n) ℂ →ₐ[ℂ] MvPolynomial (τ × Fin n) ℂ).toRingHom (G k) =
      pieceK k F) →
    ∀ φ x, HasSum (fun k => c (MvPolynomial.eval₂ (MvPolynomial.aeval Z).toRingHom H (G k) • φ) x) 0

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]

abbrev Pl : Type := HeightOneSpectrum (𝓞 E)

abbrev qc {E : Type} [Field E] [NumberField E] (w : Pl E) : ℂ := ((Formalism.UG.qV E w : ℕ) : ℂ)

def j1 (r s : ℕ) : Module.End ℂ (Sm E (r + s)) :=
  ((r * Module.finrank ℚ E : ℕ) : ℂ)⁻¹ • ∑ τ : E →+* ℂ, ∑ i : Fin r, Eop τ (Fin.castAdd s i) (Fin.castAdd s i)

def Cusp {E : Type} [Field E] [NumberField E] {n : ℕ} (φ : GA E n → ℂ) : Prop :=
  ∀ r, 0 < r → r < n → ∀ g, AutomorphicForm.constantTerm r φ g = 0

def ZSpec : Prop := ∀ (n : ℕ) (τ : E →+* ℂ), zC E n τ 0 = 1 ∧
  ∀ u : ℂ, capC (a := n) τ u = ∑ i ∈ Finset.range (n + 1), u ^ (n - i) • zC E n τ i

def UmgOps : Prop := ∀ n : ℕ, Umg (0 : Sm E n) ∧ ∀ φ : Sm E n, Umg φ → Continuous φ.1 ∧ (∀ ψ, Umg ψ → Umg (φ + ψ)) ∧
  (∀ c : ℂ, Umg (c • φ)) ∧ (∀ u, Umg (uC E n u φ)) ∧ (∀ g, Umg (rt E n g φ)) ∧ ∀ w j, Umg (hk n w j φ)

def BandOps : Prop := ∀ (n : ℕ) (C : ℝ), 0 ≤ C → Band C (0 : Sm E n) ∧ ∀ φ : Sm E n, Band C φ → (∀ ψ, Band C ψ → Band C (φ + ψ)) ∧
  (∀ c : ℂ, Band C (c • φ)) ∧ (∀ u, Band C (uC E n u φ)) ∧ (∀ g, Band C (rt E n g φ)) ∧ ∀ w j, Band C (hk n w j φ)

def HkOps : Prop := ∀ (n : ℕ) (w : Pl E) (j : ℕ),
  (∀ φ : Sm E n, hk n w j φ = (qc w ^ (((j : ℂ) * ((n : ℂ) - j)) / 2))⁻¹ • GlobalTheory.LFun.heckeVec (rw n w) (GlobalTheory.LFun.KGL w n)
    (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) (GlobalTheory.LFun.exists_isUnifV w).choose j) φ) ∧
  (∀ u, Commute (uC E n u) (hk n w j)) ∧ (∀ y, Commute (rt E n (infGL E n y)) (hk n w j)) ∧
  ∀ (S : Set (Pl E)) (φ : Sm E n), w ∉ S → Sph S φ → Sph S (hk n w j φ) ∧ hk n w 0 φ = φ ∧
    (∀ k : KA E n, Sph S (rt E n k φ) ∧ rt E n k (hk n w j φ) = hk n w j (rt E n k φ)) ∧
    ∀ w' ∉ S, ∀ j', hk n w j (hk n w' j' φ) = hk n w' j' (hk n w j φ)

def RapidDecay : Prop := ∀ (n : ℕ) (φ : Sm E n), Umg φ → Cusp φ.1 → ∀ N : ℕ, ∃ C : ℝ, ∀ x : normOneGL E n,
  ‖φ.1 (x : GA E n)‖ * PositivityTheory.Rg.Tf.Core.qht x ^ N ≤ C

def CuspUmg : Prop := ∀ (n : ℕ) (f : Sm E n), f.1 ∈ AutomorphicForm.cuspForms E n → Umg f ∧ Cusp f.1

def CtOps : Prop := ∀ (r s : ℕ) (φ : Sm E (r + s)), Umg φ → ∃ F : Sm E (r + s), F.1 = AutomorphicForm.constantTerm r φ.1 ∧
  (∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g) ∧
  (∀ (γ : GL (Fin r) E × GL (Fin s) E) g, F.1 (lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) * g) = F.1 g) ∧
  ∀ u, (uC E (r + s) u F).1 = AutomorphicForm.constantTerm r (uC E (r + s) u φ).1

def SliceBound : Prop := ∀ (S : Set (Pl E)) (r s : ℕ) (b : Blo S r),
  (∀ N : ℕ, ∃ C R : ℝ, ∀ (φ : Sm E (r + s)) (B : ℝ), Umg φ → (∀ g, ‖φ.1 g‖ ≤ B * AutomorphicForm.height g ^ N) →
    ∀ t m, ‖slice b.f.1 t φ.1 m‖ ≤ C * B * Real.exp (R * |t|) * AutomorphicForm.height m ^ N) ∧
  ∀ (φ ψ : Sm E (r + s)) (c : ℂ), Umg φ → Umg ψ → ∀ t m,
    slice b.f.1 t (c • φ + ψ).1 m = c * slice b.f.1 t φ.1 m + slice b.f.1 t ψ.1 m

def SliceUmg : Prop := ∀ (S : Set (Pl E)) (r s : ℕ) (b : Blo S r) (t : ℝ) (φ : Sm E (r + s)), Umg φ →
  ∃ ψ : Sm E s, ψ.1 = slice b.f.1 t φ.1 ∧ Umg ψ ∧
    (∀ τ i j, (Eop τ i j ψ).1 = slice b.f.1 t (Eop τ (Fin.natAdd r i) (Fin.natAdd r j) φ).1) ∧
    (∀ g, (rt E s g ψ).1 = slice b.f.1 t (rt E (r + s) (lev (Ad E) r s (1, g)) φ).1) ∧ (Sph S φ → Sph S ψ) ∧
    ∀ (e : ℕ) (ρ : KA E (r + s) → Matrix (Fin e) (Fin e) ℂ), Killed ρ φ.1 → Killed (resR ρ) ψ.1

def SliceShift : Prop := ∀ (S : Set (Pl E)) (r s : ℕ) (b : Blo S r) (t : ℝ) (φ : Sm E (r + s)) (m : GA E s), Umg φ →
  (∀ v, slice b.f.1 t (rt E (r + s) (lev (Ad E) r s (zt E r v, 1)) φ).1 m = slice b.f.1 (t + v) φ.1 m) ∧
  HasDerivAt (fun v => slice b.f.1 v φ.1 m) (slice b.f.1 t (j1 E r s φ).1 m) t

def SliceCapR : Prop := ∀ (S : Set (Pl E)) (r s : ℕ) (b : Blo S r) (t : ℝ) (φ : Sm E (r + s)) (τ : E →+* ℂ) (u : ℂ), Umg φ →
  slice b.f.1 t (capR r s τ u φ).1 =
    slice b.f.1 t (Polynomial.aeval (j1 E r s) (∏ i, (Polynomial.X + Polynomial.C (u + b.Λ τ i))) φ).1

def SliceCap : Prop := ∀ (S : Set (Pl E)) (r s : ℕ) (b : Blo S r) (t : ℝ) (φ : Sm E (r + s)) (τ : E →+* ℂ) (u : ℂ), Umg φ →
  slice b.f.1 t (cap τ u φ).1 = slice b.f.1 t (capS r s τ (u + (r : ℂ) / 2)
    (Polynomial.aeval (j1 E r s) (∏ i, (Polynomial.X + Polynomial.C (u - (s : ℂ) / 2 + b.Λ τ i))) φ)).1

def SliceHecke : Prop := ∀ (S : Set (Pl E)) (r s : ℕ) (b : Blo S r) (t : ℝ) (φ : Sm E (r + s)) (ψ : ℝ → Sm E s) (w : Pl E) (j : ℕ),
  Umg φ → Sph S φ → w ∉ S → j ≤ r + s → (∀ v, (ψ v).1 = slice b.f.1 v φ.1) →
  slice b.f.1 t (hk (r + s) w j φ).1 = (∑ a ∈ (Finset.range (j + 1)).filter fun a => j - a ≤ s,
    (((b.sat w).map fun x : ℂˣ => (x : ℂ)).esymm a * qc w ^ (((s : ℂ) * a - (r : ℂ) * ((j : ℂ) - a)) / 2)) •
      hk s w (j - a) (ψ (t - a * Real.log (Formalism.UG.qV E w)))).1

def CompBound : Prop := ∀ (S : Set (Pl E)) (n : ℕ) (d : Dat S n),
  (∀ N : ℕ, ∃ C R : ℝ, ∀ (φ : Sm E n) (B : ℝ), Umg φ → (∀ g, ‖φ.1 g‖ ≤ B * AutomorphicForm.height g ^ N) →
    ∀ t, ‖d.comp φ.1 t‖ ≤ C * B * Real.exp (R * ‖t‖)) ∧
  ∀ (φ ψ : Sm E n) (c : ℂ), Umg φ → Umg ψ → ∀ t, d.comp (c • φ + ψ).1 t = c * d.comp φ.1 t + d.comp ψ.1 t

def CompShift : Prop := ∀ (S : Set (Pl E)) (n : ℕ) (d : Dat S n) (φ : Sm E n) (t : Fin d.len → ℝ), Umg φ →
  (∀ v, d.comp (rt E n (d.tr v) φ).1 t = d.comp φ.1 (t + v)) ∧
  ∀ j, HasDerivAt (fun x : ℝ => d.comp φ.1 (t + Pi.single j x)) (d.comp (d.J j φ).1 t) 0

def CompCap : Prop := ∀ (S : Set (Pl E)) (n : ℕ) (d : Dat S n) (φ : Sm E n) (τ : E →+* ℂ) (u : ℂ), Umg φ →
  d.comp (cap τ u φ).1 = d.comp ((List.ofFn fun i : Fin n =>
    algebraMap ℂ (Module.End ℂ (Sm E n)) (u + d.lam τ i + (d.rho (d.idx i) : ℂ)) + d.J (d.idx i)).prod φ).1

def CompHecke : Prop := ∀ (S : Set (Pl E)) (n : ℕ) (d : Dat S n) (φ : Sm E n) (w : Pl E) (j : ℕ) (t : Fin d.len → ℝ),
  Umg φ → Sph S φ → w ∉ S → j ≤ n →
  d.comp (hk n w j φ).1 t = ∑ a ∈ Finset.piAntidiag Finset.univ j,
    (∏ l, ((d.sat l w).map fun x : ℂˣ => (x : ℂ)).esymm (a l) * qc w ^ (-(d.rho l : ℂ) * a l)) *
      d.comp φ.1 (t - fun l => a l * Real.log (Formalism.UG.qV E w))

def DatBasics : Prop := (∀ (S : Set (Pl E)) (r : ℕ) (b : Blo S r), ∑ τ, ∑ i, b.Λ τ i = 0) ∧
  ∀ (S : Set (Pl E)) (n : ℕ) (d : Dat S n), Function.Surjective d.idx ∧ d.len ≤ n ∧
    (∀ j, ∑ p ∈ Finset.univ.filter fun p : (E →+* ℂ) × Fin n => d.idx p.2 = j, d.lam p.1 p.2 = 0) ∧
    (∀ j w, w ∉ S → (d.sat j w).card = d.size j) ∧ d.tr 0 = 1 ∧ (∀ v v', d.tr (v + v') = d.tr v * d.tr v') ∧
    (∀ v, ∃ y, d.tr v = infGL E n y) ∧ (∀ j l, Commute (d.J j) (d.J l)) ∧ (∀ j v, Commute (d.J j) (rt E n (d.tr v))) ∧
    ∀ j, ∃ u, d.J j = uC E n u

def ResTyp : Prop := ∀ (r s : ℕ) (ρ : Typ E (r + s)), (∃ ρ' : KA E r →* Matrix (Fin ρ.d) (Fin ρ.d) ℂ, Continuous ρ' ∧ ⇑ρ' = resL ρ.ρ) ∧
  (∃ ρ' : KA E s →* Matrix (Fin ρ.d) (Fin ρ.d) ℂ, Continuous ρ' ∧ ⇑ρ' = resR ρ.ρ) ∧
  ∀ (k : KA E r) (k' : KA E s), lev (Ad E) r s ((k : GA E r), (k' : GA E s)) ∈ KA E (r + s)

def KilledOps : Prop := ∀ (n : ℕ) (ρ : Typ E n) (φ : Sm E n), Killed ρ.ρ φ.1 → (∀ k : KA E n, Killed ρ.ρ (rt E n k φ).1) ∧
  AutomorphicForm.IsKFinite φ.1

def EigComp : Prop := ∀ (S : Set (Pl E)) (r : ℕ) (ρ : Typ E r) (ψ : Sm E r), 0 < r → Umg ψ → Cusp ψ.1 → Killed ρ.ρ ψ.1 → Sph S ψ →
  (∃ x : normOneGL E r, ψ.1 (x : GA E r) ≠ 0) → ∃ b : Blo S r, Killed ρ.ρ b.f.1 ∧
    ∫ y, ψ.1 ((Quotient.out y : normOneGL E r) : GA E r) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r))
      ∂quotientMeasure (rationalGLOne E r) (mu1 E r) ≠ 0

def LangStep : Prop := ∀ (S : Set (Pl E)) (r s : ℕ) (ρ : Typ E (r + s)) (φ : Sm E (r + s)), 0 < r → Umg φ → Killed ρ.ρ φ.1 → Sph S φ →
  (∀ r', 0 < r' → r' < r → ∀ g, AutomorphicForm.constantTerm r' φ.1 g = 0) →
  (∀ (k : KA E (r + s)) (b : Blo S r), Killed (resL ρ.ρ) b.f.1 → ∀ t, slice b.f.1 t (rt E (r + s) k φ).1 = 0) →
  ∀ g, AutomorphicForm.constantTerm r φ.1 g = 0

def Langlands : Prop := ∀ (S : Set (Pl E)) (n : ℕ) (ρ : Typ E n) (φ : Sm E n), Umg φ → Killed ρ.ρ φ.1 → Sph S φ →
  ((∀ (k : KA E n) (d : Dat S n), d.HasTyp ρ.ρ → d.comp (rt E n k φ).1 = 0) → φ = 0) ∧
  ((∀ (k : KA E n) (d : Dat S n), d.HasTyp ρ.ρ → 2 ≤ d.len → d.comp (rt E n k φ).1 = 0) → Cusp φ.1)

open Classical in

def NearBlo : Prop := ∀ (S : Set (Pl E)) (r : ℕ) (ρ : Typ E r) (B : ℝ),
  {p : ((E →+* ℂ) → Fin r → ℂ) × (Pl E → Multiset ℂˣ) | ∃ b : Blo S r, Killed ρ.ρ b.f.1 ∧ (∀ τ i, ‖b.Λ τ i‖ ≤ B) ∧
    p.1 = b.Λ ∧ ∀ w, p.2 w = if w ∈ S then 0 else b.sat w}.Finite

def NearDat : Prop := ∀ (S : Set (Pl E)) (n : ℕ) (ρ : Typ E n) (B : ℝ), ∃ D : Set (Dat S n), D.Finite ∧
  ∀ d : Dat S n, d.HasTyp ρ.ρ → (∀ τ i, ‖d.lam τ i‖ ≤ B) → ∃ d' ∈ D, d'.len = d.len ∧
    ∀ F : KF ((E →+* ℂ) × Fin n) (Pl E × Fin n), (∀ x ∈ F.vars, x.1 ∉ S) → d'.Kills F → d.Kills F

def Far : Prop := ∀ (n : ℕ) (C : ℝ), 0 ≤ C → ∃ B : ℝ, ∀ (S : Set (Pl E)) (d : Dat S n) (φ : Sm E n), Band C φ → Sph S φ →
  (∃ τ i, B < ‖d.lam τ i‖) → d.comp φ.1 = 0

def Gen {E : Type} [Field E] [NumberField E] {n : ℕ} (F : KF ((E →+* ℂ) × Fin n) (Pl E × Fin n))
    (G : ℕ → MvPolynomial (Pl E × Fin n) (MvPolynomial ((E →+* ℂ) × Fin n) ℂ)) : Prop :=
  ∀ k, MvPolynomial.map (MvPolynomial.aeval blockE :
    MvPolynomial ((E →+* ℂ) × Fin n) ℂ →ₐ[ℂ] MvPolynomial ((E →+* ℂ) × Fin n) ℂ).toRingHom (G k) = pieceK k F

def KillOne : Prop := ∀ (S : Set (Pl E)) (n : ℕ) (C : ℝ) (d : Dat S n) (φ : Sm E n) (F : KF ((E →+* ℂ) × Fin n) (Pl E × Fin n)) G,
  0 ≤ C → Band C φ → Sph S φ → (∀ x ∈ F.vars, x.1 ∉ S) → d.Kills F → Gen F G →
  ∀ t, HasSum (fun k => d.comp (app (G k) φ).1 t) 0

def IsSum {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}
    (G : ℕ → MvPolynomial (Pl E × Fin n) (MvPolynomial ((E →+* ℂ) × Fin n) ℂ)) (φ w : Sm E n) : Prop :=
  ∃ N : ℕ, ∀ ε > (0 : ℝ), ∀ᶠ e : ℕ in Filter.atTop, ∀ g,
    ‖(w - ∑ k ∈ Finset.range e, app (G k) φ).1 g‖ ≤ ε * AutomorphicForm.height g ^ N

def KillComp : Prop := ∀ (S : Set (Pl E)) (n : ℕ) (C : ℝ) (φ w : Sm E n) (F : KF ((E →+* ℂ) × Fin n) (Pl E × Fin n)) G,
  0 ≤ C → Band C φ → Sph S φ → Umg w → (∀ x ∈ F.vars, x.1 ∉ S) → Gen F G → IsSum G φ w →
  ∀ (k : KA E n) (d : Dat S n), (d.Kills F ∨ ∀ ψ : Sm E n, Band C ψ → Sph S ψ → d.comp ψ.1 = 0) → d.comp (rt E n k w).1 = 0

def FunKill : Prop := ∀ (S : Set (Pl E)) (n : ℕ) (ρ : Typ E n) (C : ℝ), 0 ≤ C → ∃ D : Set (Dat S n), D.Finite ∧ (∀ d ∈ D, 2 ≤ d.len) ∧
  ∀ (φ w : Sm E n) (F : KF ((E →+* ℂ) × Fin n) (Pl E × Fin n)) G, Band C φ → Sph S φ → Umg w → Killed ρ.ρ w.1 → Sph S w →
    (∀ x ∈ F.vars, x.1 ∉ S) → (∀ d ∈ D, d.Kills F) → Gen F G → IsSum G φ w → Cusp w.1

end UpperTheory.ConvolutionTheory.BW
