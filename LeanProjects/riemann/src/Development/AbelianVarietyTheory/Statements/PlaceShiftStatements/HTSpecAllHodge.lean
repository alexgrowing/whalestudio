import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
import Formalism.LocalToGlobal.CyclotomicLocalNorms.NormSubToZModPowVal
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions.Loc

namespace GlobalTheory.HTLink

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

abbrev EtV {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) : Type 1 :=
  GlobalTheory.EtC.HQ l (GlobalTheory.EtC.sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) q)) n 0

def etAct {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) (σ : ↥(GK K)) : EtV q n →ₗ[ℚ_[l]] EtV q n :=
  GlobalTheory.EtC.galHQ l (PadicAlgCl l) q n 0 (IntermediateField.fixingSubgroupEquiv K.1 σ)

def etPull {X X' : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : X' ⟶ Sp ↥K.1} {f : X' ⟶ X} (hf : f ≫ q = q') (n : ℕ) :
    EtV q n →ₗ[ℚ_[l]] EtV q' n :=
  GlobalTheory.EtC.pullHQ l (GlobalTheory.EtC.sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) q' f hf)) n 0

abbrev HodgeV {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) (a : Fin (n + 1)) : Type :=
  GlobalTheory.HodgeCoh.hodgeH q a (n - a)

def toC (K : FinExt l) : ↥K.1 →+* ℂ_[l] := (algebraMap (PadicAlgCl l) ℂ_[l]).comp (algebraMap ↥K.1 (PadicAlgCl l))

def chiPow (σ : GQ l) (i : ℤ) : ℂ_[l] := (algebraMap ℚ_[l] ℂ_[l] (Formalism.L2.LocGap.Gal.χQ l σ : ℚ_[l])) ^ i

structure Frame {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) : Type 1 where

  d : ℕ

  b : Module.Basis (Fin d) ℚ_[l] (EtV q n)

  e : Fin (n + 1) → ℕ

  c : ∀ a, Module.Basis (Fin (e a)) ↥K.1 (HodgeV q n a)

namespace Frame

variable {X X' : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : X' ⟶ Sp ↥K.1} {n : ℕ}

abbrev Col (F : Frame q n) : Type := Σ a : Fin (n + 1), Fin (F.e a)

def rho (F : Frame q n) (σ : ↥(GK K)) : Matrix (Fin F.d) (Fin F.d) ℂ_[l] :=
  (LinearMap.toMatrix F.b F.b (etAct q n σ)).map (algebraMap ℚ_[l] ℂ_[l])

def etMat (F : Frame q n) (F' : Frame q' n) {f : X' ⟶ X} (hf : f ≫ q = q') : Matrix (Fin F'.d) (Fin F.d) ℂ_[l] :=
  (LinearMap.toMatrix F.b F'.b (etPull hf n)).map (algebraMap ℚ_[l] ℂ_[l])

def hodgeMat (F : Frame q n) (F' : Frame q' n) {f : X' ⟶ X} (hf : f ≫ q = q') : Matrix F'.Col F.Col ℂ_[l] :=
  (Matrix.blockDiagonal' fun a : Fin (n + 1) =>
    LinearMap.toMatrix (F.c a) (F'.c a) (GlobalTheory.HodgeCoh.hodgePull hf a (n - a))).map (toC K)

def IsHT (F : Frame q n) (Φ : Matrix (Fin F.d) F.Col ℂ_[l]) : Prop :=
  (∃ Ψ : Matrix F.Col (Fin F.d) ℂ_[l], Φ * Ψ = 1 ∧ Ψ * Φ = 1) ∧
    ∀ σ : ↥(GK K), F.rho σ * Φ.map (Formalism.Per.σC (σ : GQ l)) =
      Φ * Matrix.diagonal fun j : F.Col => chiPow (σ : GQ l) (-((j.1 : ℕ) : ℤ))

end Frame

def SmProj {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) : Prop := Smooth q ∧ IsProjOver q

universe u

structure HodgeFam (K : FinExt l) : Type (max 1 (u + 1)) where

  H : ∀ {X : Scheme.{0}}, (X ⟶ Sp ↥K.1) → ∀ n : ℕ, Fin (n + 1) → Type u

  [add : ∀ {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) (a : Fin (n + 1)), AddCommGroup (H q n a)]

  [mod : ∀ {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) (a : Fin (n + 1)), Module ↥K.1 (H q n a)]

  pull : ∀ {X X' : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : X' ⟶ Sp ↥K.1} {f : X' ⟶ X}, f ≫ q = q' →
    ∀ (n : ℕ) (a : Fin (n + 1)), H q n a →ₗ[↥K.1] H q' n a

attribute [instance] HodgeFam.add HodgeFam.mod

def hodgeFam (K : FinExt l) : HodgeFam.{0} K where
  H q n a := HodgeV q n a
  pull hf n a := GlobalTheory.HodgeCoh.hodgePull hf a (n - a)

abbrev Pairing (D : HodgeFam.{u} K) {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) : Type (max 1 u) :=
  ∀ a : Fin (n + 1), EtV q n →ₗ[ℚ_[l]] Module.Dual ↥K.1 (D.H q n a) →ₗ[↥K.1] ℂ_[l]

structure IsHTPair {D : HodgeFam.{u} K} {X : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {n : ℕ} (h : Pairing D q n) : Prop where

  finEt : FiniteDimensional ℚ_[l] (EtV q n)

  finH : ∀ a, FiniteDimensional ↥K.1 (D.H q n a)

  equi : ∀ (σ : ↥(GK K)) (a : Fin (n + 1)) (v : EtV q n) (φ : Module.Dual ↥K.1 (D.H q n a)),
    chiPow (σ : GQ l) ((a : ℕ) : ℤ) * h a (etAct q n σ v) φ = Formalism.Per.σC (σ : GQ l) (h a v φ)

  inj : ∀ (m : ℕ) (v : Fin m → EtV q n) (c : Fin m → ℂ_[l]), LinearIndependent ℚ_[l] v →
    (∀ (a : Fin (n + 1)) (φ : Module.Dual ↥K.1 (D.H q n a)), ∑ i, c i * h a (v i) φ = 0) → c = 0

  onto : ∑ a, Module.finrank ↥K.1 (D.H q n a) = Module.finrank ℚ_[l] (EtV q n)

def IsNat {D : HodgeFam.{u} K} {X X' : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : X' ⟶ Sp ↥K.1} {f : X' ⟶ X} (hf : f ≫ q = q')
    {n : ℕ} (h : Pairing D q n) (h' : Pairing D q' n) : Prop :=
  ∀ (a : Fin (n + 1)) (v : EtV q n) (φ' : Module.Dual ↥K.1 (D.H q' n a)),
    h' a (etPull hf n v) φ' = h a v (φ' ∘ₗ D.pull hf n a)

def HTOn (K : FinExt l) (P : CrystallineSemistableComparison.Model l K.1 → Prop) (D : HodgeFam.{u} K) (n : ℕ) : Prop :=
  ∃ h : ∀ M : CrystallineSemistableComparison.Model l K.1, P M → Pairing D M.q n,
    (∀ (M : CrystallineSemistableComparison.Model l K.1) (hM : P M), IsHTPair (h M hM)) ∧
    ∀ (M N : CrystallineSemistableComparison.Model l K.1) (hM : P M) (hN : P N) (g : M.X ⟶ N.X) (hg : g ≫ N.p = M.p),
      IsNat (CrystallineSemistableComparison.Model.genMap_q g hg) (h N hN) (h M hM)

def SmProjModel (M : CrystallineSemistableComparison.Model l K.1) : Prop := Smooth M.p ∧ IsProjOver M.p

def HTSpec (D : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), HodgeFam.{u} K) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (n : ℕ), HTOn K SmProjModel (D l K) n

def HTSpecHodge : Prop := HTSpec fun _ _ K => hodgeFam K

def HTSpecAll (D : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), HodgeFam.{u} K) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (n : ℕ),
    ∃ h : ∀ (X : Scheme.{0}) (q : X ⟶ Sp ↥K.1), SmProj q → Pairing (D l K) q n,
      (∀ (X : Scheme.{0}) (q : X ⟶ Sp ↥K.1) (hq : SmProj q), IsHTPair (h X q hq)) ∧
      ∀ (X X' : Scheme.{0}) (q : X ⟶ Sp ↥K.1) (q' : X' ⟶ Sp ↥K.1) (hq : SmProj q) (hq' : SmProj q')
        (f : X' ⟶ X) (hf : f ≫ q = q'), IsNat hf (h X q hq) (h X' q' hq')

def HTSpecAllHodge : Prop := HTSpecAll fun _ _ K => hodgeFam K

end GlobalTheory.HTLink

end
