import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LinDefs

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

abbrev KV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : Type := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v

abbrev RV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : Type :=
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E

abbrev OV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : ValuationSubring (KV I v) :=
  v.adicCompletionIntegers I.F

def IsAdaptedFirstProjection (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) (p1 : RV I v →+* KV I v) : Prop :=
  (∀ c : KV I v, p1 (algebraMap (KV I v) (RV I v) c) = c) ∧ p1 ε = 1 ∧
    p1 (PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v ε) = 0 ∧
    ∀ x ∈ Formalism.UG.intOE I.E, p1 (PI.UnitaryGroupMassFormula.AdIndexEq.inclV I v x) ∈ OV I v

def vec1 {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v) (x : Fin I.n → RV I v) :
    Fin I.n → KV I v := fun i => p1 (x i)

def vec2 {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v) (x : Fin I.n → RV I v) :
    Fin I.n → KV I v := fun i => p1 (PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (x i))

def Lam1 (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v) :
    Submodule (OV I v) (Fin I.n → KV I v) :=
  Submodule.span (OV I v) (vec1 p1 '' (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) : Set _))

def Lam2 (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v) :
    Submodule (OV I v) (Fin I.n → KV I v) :=
  Submodule.span (OV I v) (vec2 p1 '' (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) : Set _))

def Pm (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v) : Matrix (Fin I.n) (Fin I.n) (KV I v) :=
  I.J.map (p1.comp (PI.UnitaryGroupMassFormula.AdIndexEq.inclV I v))

def LinHyp (K : Type) [Field K] (O : ValuationSubring K) (n r : ℕ) (P : Matrix (Fin n) (Fin n) K) (g : K)
    (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K) (u φ u0 φ0 : Fin n → K) (t : K) : Prop :=
  g ∈ O ∧ g⁻¹ ∉ O ∧
    (∀ β ∈ Λ2, ∀ x ∈ Λ1, pr P β x ∈ O) ∧
    (∀ i, a i ∈ Λ1 ∧ a' i ∈ Λ1 ∧ α i ∈ Λ2 ∧ α' i ∈ Λ2) ∧
    (∀ i j, pr P (α i) (a j) = 0 ∧ pr P (α' i) (a' j) = 0 ∧
      pr P (α i) (a' j) = (if i = j then 1 else 0) ∧ pr P (α' i) (a j) = (if i = j then 1 else 0)) ∧
    u ∈ Λ1 ∧ φ ∈ Λ2 ∧ u0 ∈ Λ1 ∧ φ0 ∈ Λ2 ∧
    (∀ i, pr P (α i) u = 0 ∧ pr P (α' i) u = 0 ∧ pr P φ (a i) = 0 ∧ pr P φ (a' i) = 0) ∧
    t ∈ O ∧ (∃ s ∈ O, t - 1 = g * s) ∧ pr P φ u = -t ∧
    (∀ i, (∃ s ∈ O, pr P (α i) u0 = g * s) ∧ (∃ s ∈ O, pr P (α' i) u0 = g * s) ∧
      (∃ s ∈ O, pr P φ0 (a i) = g * s) ∧ (∃ s ∈ O, pr P φ0 (a' i) = g * s)) ∧
    (∃ s ∈ O, pr P φ0 u0 + 1 = g * s)

def LinConcl (K : Type) [Field K] (O : ValuationSubring K) (n r : ℕ) (P : Matrix (Fin n) (Fin n) K) (g : K)
    (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K) (u φ u0 φ0 : Fin n → K)
    (T : GL (Fin n) K) : Prop :=
  (∀ x ∈ Λ1, (T : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ Λ1 ∧
    ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ Λ1) ∧
  (∀ β ∈ Λ2, (∃ β' ∈ Λ2, β' ᵥ* P = (β ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K)) ∧
    (∃ β' ∈ Λ2, β' ᵥ* P = (β ᵥ* P) ᵥ* ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∧
  (∀ i, (T : Matrix (Fin n) (Fin n) K) *ᵥ a i = a i ∧ (T : Matrix (Fin n) (Fin n) K) *ᵥ a' i = a' i ∧
    (α i ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) = α i ᵥ* P ∧
    (α' i ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) = α' i ᵥ* P) ∧
  (∃ w ∈ Λ1, ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u - u0 = g • w) ∧
  (∃ β ∈ Λ2, (φ ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) - φ0 ᵥ* P = g • (β ᵥ* P))

theorem linConcl_of (hL : LocLin) (K : Type) [Field K] (O : ValuationSubring K) (n r : ℕ)
    (P : Matrix (Fin n) (Fin n) K) (g : K) (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)
    (u φ u0 φ0 : Fin n → K) (t : K) (h : LinHyp K O n r P g Λ1 Λ2 a a' α α' u φ u0 φ0 t) :
    ∃ T : GL (Fin n) K, LinConcl K O n r P g Λ1 Λ2 a a' α α' u φ u0 φ0 T := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact hL K O n r P g Λ1 Λ2 a a' α α' u φ u0 φ0 t h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15

def LinData (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (Rf : RefData I g r k e f) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v) (t : ℕ) : Prop :=
  LinHyp (KV I v) (OV I v) I.n r (Pm I v p1) (g : KV I v) (Lam1 I v p1) (Lam2 I v p1)
    (fun i => vec1 p1 (PI.FinKW.vecV I v (incl I (e i)))) (fun i => vec1 p1 (PI.FinKW.vecV I v (incl I (f i))))
    (fun i => vec2 p1 (PI.FinKW.vecV I v (incl I (e i)))) (fun i => vec2 p1 (PI.FinKW.vecV I v (incl I (f i))))
    (vec1 p1 (PI.FinKW.vecV I v (incl I z))) (vec2 p1 (PI.FinKW.vecV I v (incl I z)))
    (vec1 p1 (PI.FinKW.vecV I v Rf.z0)) (vec2 p1 (PI.FinKW.vecV I v Rf.z0)) (t : KV I v)

def LinOut (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (Rf : RefData I g r k e f) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v)
    (T : GL (Fin I.n) (KV I v)) : Prop :=
  LinConcl (KV I v) (OV I v) I.n r (Pm I v p1) (g : KV I v) (Lam1 I v p1) (Lam2 I v p1)
    (fun i => vec1 p1 (PI.FinKW.vecV I v (incl I (e i)))) (fun i => vec1 p1 (PI.FinKW.vecV I v (incl I (f i))))
    (fun i => vec2 p1 (PI.FinKW.vecV I v (incl I (e i)))) (fun i => vec2 p1 (PI.FinKW.vecV I v (incl I (f i))))
    (vec1 p1 (PI.FinKW.vecV I v (incl I z))) (vec2 p1 (PI.FinKW.vecV I v (incl I z)))
    (vec1 p1 (PI.FinKW.vecV I v Rf.z0)) (vec2 p1 (PI.FinKW.vecV I v Rf.z0)) T

def SumOne (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) : Prop :=
  ε + PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v ε = 1

def LocSplitP : Prop :=
  ∀ (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)), SumOne I v (PI.FinKW.psiV I v Rf.ew) →
    ∃ p1 : RV I v →+* KV I v, IsAdaptedFirstProjection I v (PI.FinKW.psiV I v Rf.ew) p1

def BridgeA : Prop :=
  ∀ (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (Rf : RefData I g r k e f), Hyps I g r k e f z →
    ∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal → SumOne I v (PI.FinKW.psiV I v Rf.ew) →
    ∀ p1 : RV I v →+* KV I v, IsAdaptedFirstProjection I v (PI.FinKW.psiV I v Rf.ew) p1 →
    ∀ t : ℕ, t ≡ 1 [MOD g] → Formalism.UG.hform (starRingEnd I.E) I.J z z = -(t : I.E) →
      LinData I g r k e f z Rf v p1 t

def BridgeB : Prop :=
  ∀ (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (Rf : RefData I g r k e f), Hyps I g r k e f z →
    ∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal → SumOne I v (PI.FinKW.psiV I v Rf.ew) →
    ∀ p1 : RV I v →+* KV I v, IsAdaptedFirstProjection I v (PI.FinKW.psiV I v Rf.ew) p1 →
    ∀ T : GL (Fin I.n) (KV I v), LinOut I g r k e f z Rf v p1 T → LocConcl I g r e f z Rf.z0 v

theorem locCore_of (hS : LocSplitP) (hA : BridgeA) (hB : BridgeB) (hL : LocLin) : LocCore := by
  intro I g r k e f z Rf hH v hv hsum
  obtain ⟨p1, hp1⟩ := hS I g r k e f Rf v hsum
  obtain ⟨t, ht1, ht2⟩ := hH.2.2.2.2.2.2.2.1
  obtain ⟨T, hT⟩ := linConcl_of hL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hA I g r k e f z Rf hH v hv hsum p1 hp1 t ht1 ht2)
  exact hB I g r k e f z Rf hH v hv hsum p1 hp1 T hT

theorem target_of' (hI : LocIdem) (hS : LocSplitP) (hA : BridgeA) (hB : BridgeB) (hL : LocLin) (hG : Glue) :
    _root_.PI.ScXuExists.Target := by
  first
  | exact target_of hI (locCore_of hS hA hB hL) hG
  | exact target_of hI hG (locCore_of hS hA hB hL)
  | (unfold PI.ScXuExists.Target LocIdem Glue LocCore at *; done)

end PI.UnitaryGroupMassFormula.ScXuExists
