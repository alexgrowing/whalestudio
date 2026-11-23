import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch

variable {D : D7}

structure Lvl (V : HSp D) where

  L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

  c : GL (Fin V.rank) (AE D)

def Lvl.K {V : HSp D} (l : Lvl V) : Subgroup (GA D V) := levelAll D.sp.cm.sig V.gram l.L l.c

def Lvl.Good {V : HSp D} (l : Lvl V) : Prop :=
  Submodule.IsLattice D.host.E l.L ∧ (∀ v, IsSelfDualAt D.sp.cm.sig V.gram l.L v) ∧ IsMaj V l.c

def Lvl.form {V : HSp D} (l : Lvl V) : Mx D V.rank V.rank := adj (l.c⁻¹).1 ⬝ (l.c⁻¹).1

def Compat {T T' : HSp D} {t : ℕ} (d : HypDec T T' t) (l : Lvl T) (l' : Lvl T') : Prop :=
  (∀ z, z ∈ l.L ↔ (d.qX *ᵥ z ∈ stdLattice D.host.E t ∧ d.q0 *ᵥ z ∈ l'.L ∧ d.qY *ᵥ z ∈ stdLattice D.host.E t)) ∧
  ∀ w, l.form.map (compInf D.host.F D.host.E w) =
    (adj d.pX ⬝ d.pX + adj d.p0 ⬝ (l'.form ⬝ d.p0) + adj d.pY ⬝ d.pY : Mx D T.rank T.rank).map (compInf D.host.F D.host.E w)

theorem Lvl.K_frameLat (V : HSp D) (a : GL (Fin V.rank) (AE D)) : Lvl.K (⟨frameLat V, a⟩ : Lvl V) = Kmax V a := rfl

theorem Lvl.good_frameLat (V : HSp D) {a : GL (Fin V.rank) (AE D)} (ha : IsMaj V a) :
    Lvl.Good (⟨frameLat V, a⟩ : Lvl V) :=
  ⟨SelfDual.isLattice_frameLat V, SelfDual.isSelfDualAt_frameLat D V, ha⟩

theorem Lvl.exists_good (V : HSp D) : ∃ l : Lvl V, l.Good ∧ l.K = Kmax V l.c :=
  let ⟨a, ha⟩ := exists_isMaj V
  ⟨⟨frameLat V, a⟩, Lvl.good_frameLat V ha, rfl⟩

theorem Lvl.Good.isCompact_K {V : HSp D} {l : Lvl V} (h : l.Good) : IsCompact (l.K : Set (GA D V)) :=
  haveI := h.1
  isCompact_levelAll (isCMExt_host D) _ _ _

theorem Lvl.form_frame {V : HSp D} (l : Lvl V) : (adj l.c.1 ⬝ (l.form ⬝ l.c.1) : Mx D V.rank V.rank) = 1 := by
  have h : ((l.c⁻¹).1 * l.c.1 : Matrix _ _ (AE D)) = 1 := l.c.inv_mul
  change Formalism.UG.cT _ l.c.1 * (Formalism.UG.cT _ (l.c⁻¹).1 * (l.c⁻¹).1 * l.c.1) = (1 : Matrix _ _ (AE D))
  rw [Matrix.mul_assoc, h, Matrix.mul_one, ← Formalism.UG.cT_mul, h, Formalism.UG.cT_one]

section SlopeTestRemainingChoices

variable {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (K : Subgroup (GA D T))

def sphericalSectionIwasawa (s : ℂ) : GA D T → ℂ := fun h => npow (iwAbs (absDet d) K h) (s + rhoH T r)

def sphericalEisensteinSeriesOnGroup (h : GA D T) : ℂ → ℂ := fun s => cosetSum (stab d) (GQ T) (sphericalSectionIwasawa d K s) h

def residueFieldAlt : ℂ := laurent (sphericalEisensteinSeriesOnGroup d K 1) (rhoH T r) (-1)

theorem sphericalSection_maximalCompact (b : GL (Fin T.rank) (AE D)) : sphericalSectionIwasawa d (Kmax T b) = sphericalSection d b := rfl

end SlopeTestRemainingChoices

section Centre

variable (θ : InfFam D) (n : ℕ) (τ : D.what₂.Tau)

def atG (x : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) : StdUnn.G D n :=
  if h : ∃ g : StdUnn.G D n, compAt θ τ (StdUnn.mat g) = x ∧ (∀ τ', τ' ≠ τ → compAt θ τ' (StdUnn.mat g) = 1) ∧
    (StdUnn.mat g).map (finPart D) = 1 then h.choose else 1

def rderG (X : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) (f : StdUnn.G D n → ℂ) : StdUnn.G D n → ℂ :=
  fun g => deriv (fun t : ℝ => f (g * atG θ n τ (NormedSpace.exp (t • X)))) 0

def conjG (Z : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) : Matrix (Fin (n + n)) (Fin (n + n)) ℂ :=
  -((StdUnn.blk4 (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0)⁻¹ * Zᴴ * StdUnn.blk4 (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0)

theorem conjG_I_smul_one : conjG n (Complex.I • 1) = Complex.I • 1 := by
  have h : StdUnn.blk4 (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0 * StdUnn.blk4 (0 : Matrix (Fin n) (Fin n) ℂ) (-1) 1 0 = 1 := by
    simp [StdUnn.blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  have hu := Matrix.isUnit_det_of_right_inverse h
  unfold conjG
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.nonsing_inv_mul _ hu]
  simp

def rderCG (Z : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) (f : StdUnn.G D n → ℂ) : StdUnn.G D n → ℂ :=
  rderG θ n τ ((1 / 2 : ℂ) • (Z + conjG n Z)) f + Complex.I • rderG θ n τ ((1 / (2 * Complex.I) : ℂ) • (Z - conjG n Z)) f

def gelfG (k : ℕ) (f : StdUnn.G D n → ℂ) : StdUnn.G D n → ℂ :=
  ∑ idx : Fin (k + 1) → Fin (n + n),
    (List.ofFn fun a : Fin (k + 1) => rderCG θ n τ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr (fun A acc => A acc) f

def centreG (p : MvPolynomial ℕ ℂ) (f : StdUnn.G D n → ℂ) : StdUnn.G D n → ℂ := polyAct (gelfG θ n τ) p f

end Centre

section Ops

variable {n : ℕ}

def projS {T : HSp D} {K : Subgroup (GA D T)} (ν : Measure K) (Φ : Mx D T.rank n → ℂ) : Mx D T.rank n → ℂ :=
  fun x => ∫ k, Φ (mt T (k : GA D T)⁻¹ ⬝ x) ∂ν

def ikS {T T' : HSp D} {t : ℕ} (d : HypDec T T' t) (μ : Measure (Mx D t n)) (Φ : Mx D T.rank n → ℂ) : Mx D T'.rank n → ℂ :=
  fun a => ∫ x, Φ (d.jX ⬝ x + d.j0 ⬝ a) ∂μ

theorem projS_of_invariant {T : HSp D} {K : Subgroup (GA D T)} (ν : Measure K) [IsProbabilityMeasure ν]
    {Φ : Mx D T.rank n → ℂ} (h : ∀ k ∈ K, ∀ x : Mx D T.rank n, Φ (mt T k ⬝ x) = Φ x) : projS ν Φ = Φ := by
  funext x
  have : ∀ k : K, Φ (mt T (k : GA D T)⁻¹ ⬝ x) = Φ x := fun k => h _ (K.inv_mem k.2) x
  simp [projS, this]

variable (θ : InfFam D) (τ : D.what₂.Tau)

def cenH (V : HSp D) (p : MvPolynomial ℕ ℂ) (Φ : Mx D V.rank n → ℂ) : Mx D V.rank n → ℂ :=
  fun x => centreAct θ τ V p (fun h => Φ (mt V h⁻¹ ⬝ x)) 1

variable {θ} {V V₀ : HSp D} {r : ℕ} (ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n))

def cenG (p : MvPolynomial ℕ ℂ) (Φ : schwartzA θ V.rank n) : Mx D V.rank n → ℂ :=
  fun x => centreG θ n τ p (fun g => (ω g Φ).1 x) 1

def KFin (Φ : schwartzA θ V.rank n) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ StdUnn.K D n, Ψ = ω k Φ})

variable (d : HypDec V V₀ r) (K : Subgroup (GA D V))

def IsRegS (zG zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ) : Prop :=
  (∀ Φ, cenG τ ω zG Φ = cenH θ τ V zH Φ.1) ∧
  (∀ Φ Ψ : schwartzA θ V.rank n, Ψ.1 = cenH θ τ V zH Φ.1 → ∀ g, Grow.RapidDec V (StdUnn.theta ω Ψ g)) ∧
  (∀ s, centreAct θ τ V zH (sphericalSectionIwasawa d K s) = P.eval s • sphericalSectionIwasawa d K s) ∧ P ≠ 0

def regIntS (m : Measure (GA D V)) (P : Polynomial ℂ) (Ψ : schwartzA θ V.rank n) (g : StdUnn.G D n) : ℂ → ℂ :=
  fun s => (residueFieldAlt d K * P.eval s)⁻¹ *
    ⨍ q, descend (GQ V) (fun h => StdUnn.theta ω Ψ g h * sphericalEisensteinSeriesOnGroup d K h s) q ∂autMeasure V m

def eisS (H : StdUnn.G D n → ℝ≥0) (Φ : schwartzA θ V.rank n) (g : StdUnn.G D n) : ℂ → ℂ :=
  fun s => cosetSum (StdUnn.P D n) (StdUnn.GF D n) (StdUnn.sect ω H Φ s) g

end Ops

end GlobalTheory.RegSch

end
