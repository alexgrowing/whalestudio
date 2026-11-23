import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.AutomorphicFormsLeSm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.AffChar

noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n r s : ℕ}

def zC (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (τ : E →+* ℂ) (i : ℕ) : UpperTheory.V.Cm.UC E n :=
  ∑ j : Fin (n + 1), (Lagrange.basis Finset.univ (fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) j).coeff (n - i) •
    UpperTheory.V.Cm.capC τ ((j : ℕ) : ℂ)

theorem zC_mem (τ : E →+* ℂ) (i : ℕ) : zC E n τ i ∈ Subalgebra.center ℂ (UpperTheory.V.Cm.UC E n) :=
  Subalgebra.sum_mem _ fun _ _ => Subalgebra.smul_mem _ (UpperTheory.V.Cm.capC_mem_center _ _) _

def evZ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) :
    MvPolynomial ((E →+* ℂ) × Fin n) ℂ →ₐ[ℂ] Subalgebra.center ℂ (UpperTheory.V.Cm.UC E n) :=
  MvPolynomial.aeval fun p => ⟨zC E n p.1 (p.2 + 1), zC_mem _ _⟩

def zop (P : MvPolynomial ((E →+* ℂ) × Fin n) ℂ) : Module.End ℂ (Sm E n) := UpperTheory.V.Cm.uC E n (evZ E n P : UpperTheory.V.Cm.UC E n)

abbrev rw (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Representation ℂ (GL (Fin n) (w.adicCompletion E)) (Sm E n) :=
  (finRep E n).comp (locGL E n w)

def hk (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (j : ℕ) : Module.End ℂ (Sm E n) :=
  (((Formalism.UG.qV E w : ℕ) : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2))⁻¹ •
    ∑ᶠ c : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n,
      Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) (GlobalTheory.LFun.exists_isUnifV w).choose j c.out • rw n w c.out

variable {S : Set (HeightOneSpectrum (𝓞 E))}

def hmon (β : (HeightOneSpectrum (𝓞 E) × Fin n) →₀ ℕ) : Module.End ℂ (Sm E n) :=
  (β.support.toList.map fun p => hk n p.1 (p.2 + 1) ^ β p).prod

def app (G : MvPolynomial (HeightOneSpectrum (𝓞 E) × Fin n) (MvPolynomial ((E →+* ℂ) × Fin n) ℂ)) : Module.End ℂ (Sm E n) :=
  ∑ β ∈ G.support, zop (G.coeff β) * hmon β

def Sph (S : Set (HeightOneSpectrum (𝓞 E))) (φ : Sm E n) : Prop := ∀ w ∉ S, ∀ k ∈ GlobalTheory.LFun.KGL w n, rw n w k φ = φ

structure Umg (φ : Sm E n) : Prop where
  left : AutomorphicForm.IsLeftInvariant φ.1
  level : IsOpen {k | finRep E n k φ = φ}
  growth : ∃ N : ℕ, ∀ u : UpperTheory.V.Cm.UC E n, ∃ B : ℝ, ∀ g, ‖(UpperTheory.V.Cm.uC E n u φ).1 g‖ ≤ B * AutomorphicForm.height g ^ N

structure Band (C : ℝ) (φ : Sm E n) : Prop extends Umg φ where
  band : ∃ N : ℕ, ∀ u : UpperTheory.V.Cm.UC E n, ∃ B : ℝ, ∀ (α : ((E →+* ℂ) × Fin n) →₀ ℕ) (g : GA E n),
    ‖(UpperTheory.V.Cm.uC E n u (zop (MvPolynomial.monomial α 1) φ)).1 g‖ ≤ B * C ^ α.degree * AutomorphicForm.height g ^ N

abbrev KA (E : Type) [Field E] [NumberField E] (n : ℕ) : Subgroup (AdelicGLn.AdelicGL E n) := maxCompact

structure Typ (E : Type) [Field E] [NumberField E] (n : ℕ) where
  d : ℕ
  ρ : KA E n →* Matrix (Fin d) (Fin d) ℂ
  cont : Continuous ρ

def Killed {m d : ℕ} (ρ : KA E m → Matrix (Fin d) (Fin d) ℂ) (φ : GA E m → ℂ) : Prop :=
  ∀ x : KA E m →₀ ℂ, (x.sum fun k c => c • ρ k) = 0 → ∀ g : GA E m, (x.sum fun k c => c * φ (g * (k : GA E m))) = 0

open Classical in

def resL {d : ℕ} (ρ : KA E (r + s) → Matrix (Fin d) (Fin d) ℂ) (k : KA E r) : Matrix (Fin d) (Fin d) ℂ :=
  if h : lev (Ad E) r s ((k : GA E r), 1) ∈ KA E (r + s) then ρ ⟨_, h⟩ else 0

open Classical in

def resR {d : ℕ} (ρ : KA E (r + s) → Matrix (Fin d) (Fin d) ℂ) (k : KA E s) : Matrix (Fin d) (Fin d) ℂ :=
  if h : lev (Ad E) r s (1, (k : GA E s)) ∈ KA E (r + s) then ρ ⟨_, h⟩ else 0

def mu1 (E : Type) [Field E] [NumberField E] (n : ℕ) : Measure (normOneGL E n) := Measure.haar

instance (E : Type) [Field E] [NumberField E] (n : ℕ) : (mu1 E n).IsHaarMeasure := by unfold mu1; infer_instance

def zt (E : Type) [Field E] [NumberField E] (n : ℕ) (t : ℝ) : AdelicGLn.AdelicGL E n := centralSection E n ⟨Real.exp t, Real.exp_pos t⟩

def slice (f : GA E r → ℂ) (t : ℝ) (φ : GA E (r + s) → ℂ) (m : GA E s) : ℂ :=
  ∫ y, AutomorphicForm.constantTerm r φ (lev (Ad E) r s (zt E r t * ((Quotient.out y : normOneGL E r) : GA E r), m)) *
    starRingEnd ℂ (f ((Quotient.out y : normOneGL E r) : GA E r)) ∂quotientMeasure (rationalGLOne E r) (mu1 E r)

structure Blo (S : Set (HeightOneSpectrum (𝓞 E))) (r : ℕ) where
  pos : 0 < r
  f : Sm E r
  ne : f ≠ 0
  cusp : f.1 ∈ AutomorphicForm.cuspForms E r
  cen : ∀ t g, f.1 (zt E r t * g) = f.1 g
  summand : ∃ V, C.IsSummand (mu1 E r) V ∧ ((cuspToL2 (mu1 E r) ⟨f.1, cusp⟩ : cuspidalL2 (mu1 E r)) : C.LL (mu1 E r)) ∈ V
  Λ : (E →+* ℂ) → Fin r → ℂ
  inf : ∀ τ u, cap τ u f = (∏ i, (u + Λ τ i)) • f
  sat : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ
  isSat : ∀ w ∉ S, GlobalTheory.LFun.IsSatVecGL w (rw r w) f (sat w)

inductive Dat (S : Set (HeightOneSpectrum (𝓞 E))) : ℕ → Type
  | nil : Dat S 0
  | cons {r s : ℕ} (b : Blo S r) (d : Dat S s) : Dat S (r + s)

namespace Dat

def len : {n : ℕ} → Dat S n → ℕ
  | _, nil => 0
  | _, cons _ d => d.len + 1

def comp : {n : ℕ} → (d : Dat S n) → (GA E n → ℂ) → (Fin d.len → ℝ) → ℂ
  | _, nil, φ, _ => φ 1
  | _, cons b d, φ, t => d.comp (slice b.f.1 (t (0 : Fin (d.len + 1))) φ) fun j => t (j.succ : Fin (d.len + 1))

def idx : {n : ℕ} → (d : Dat S n) → Fin n → Fin d.len
  | _, nil => fun i => i.elim0
  | _, cons _ d => Fin.addCases (fun _ => (0 : Fin (d.len + 1))) fun i => ((d.idx i).succ : Fin (d.len + 1))

def lam : {n : ℕ} → Dat S n → (E →+* ℂ) → Fin n → ℂ
  | _, nil => fun _ i => i.elim0
  | _, cons b d => fun τ => Fin.addCases (b.Λ τ) (d.lam τ)

def sat : {n : ℕ} → (d : Dat S n) → Fin d.len → HeightOneSpectrum (𝓞 E) → Multiset ℂˣ
  | _, nil => fun j => j.elim0
  | _, cons b d => fun j => Fin.cases (motive := fun _ => HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) b.sat d.sat (j : Fin (d.len + 1))

def HasTyp : {n : ℕ} → Dat S n → {e : ℕ} → (KA E n → Matrix (Fin e) (Fin e) ℂ) → Prop
  | _, nil, _, _ => True
  | _, cons b d, _, ρ => Killed (resL ρ) b.f.1 ∧ d.HasTyp (resR ρ)

variable (d : Dat S n)

def size (j : Fin d.len) : ℕ := (Finset.univ.filter fun i => d.idx i = j).card

def rho (j : Fin d.len) : ℝ := ((∑ l ∈ Finset.Iio j, (d.size l : ℝ)) - ∑ l ∈ Finset.Ioi j, (d.size l : ℝ)) / 2

def J (j : Fin d.len) : Module.End ℂ (Sm E n) :=
  ((d.size j * Module.finrank ℚ E : ℕ) : ℂ)⁻¹ • ∑ τ : E →+* ℂ, ∑ i ∈ Finset.univ.filter fun i => d.idx i = j, Eop τ i i

def tr (v : Fin d.len → ℝ) : GA E n :=
  diagUnits n fun i => posIdele (K := E) (Real.exp (v (d.idx i) / (d.size (d.idx i) * Module.finrank ℚ E : ℕ))) (Real.exp_pos _)

def ptL (z : Fin d.len → ℂ) (p : (E →+* ℂ) × Fin n) : ℂ := d.lam p.1 p.2 + z (d.idx p.2)

def ptS (z : Fin d.len → ℂ) (w : HeightOneSpectrum (𝓞 E)) : Multiset ℂ :=
  ∑ j, (d.sat j w).map fun b : ℂˣ => (b : ℂ) * ((Formalism.UG.qV E w : ℕ) : ℂ) ^ (-z j)

def ptH (z : Fin d.len → ℂ) (p : HeightOneSpectrum (𝓞 E) × Fin n) : ℂ := (d.ptS z p.1).esymm (p.2 + 1)

def Kills (F : PositivityTheory.Rg.Fx.KF ((E →+* ℂ) × Fin n) (HeightOneSpectrum (𝓞 E) × Fin n)) : Prop := ∀ z, PositivityTheory.Rg.Fx.evK (d.ptL z) (d.ptH z) F = 0

end Dat

end UpperTheory.ConvolutionTheory.BW
