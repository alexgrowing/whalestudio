import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeOfExplicitAndCompact
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset Formalism.MainNotions.S
open scoped TensorProduct

def eqvFn {G : Type} [Group G] (Γ K : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V]
    (a : Γ →* Module.End ℂ V) (ψ : K →* ℂˣ) : Submodule ℂ (G → V) where
  carrier := {φ | ∀ (γ : Γ) (x : G) (κ : K), φ (γ * x * κ) = ((ψ κ)⁻¹ : ℂˣ) • a γ (φ x)}
  add_mem' := by
    intro φ φ' h h' γ x κ
    simp only [Pi.add_apply, map_add, smul_add, h γ x κ, h' γ x κ]
  zero_mem' := by
    intro γ x κ
    simp
  smul_mem' := by
    intro c φ h γ x κ
    simp only [Pi.smul_apply, map_smul, h γ x κ]
    rw [smul_comm]

abbrev GAf (D : D7) : Type :=
  letI := D.host.cmStar
  ↥(Formalism.UG.UPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F))

def GF (D : D7) : Subgroup (GAf D) :=
  letI := D.host.cmStar
  (Formalism.UG.ratPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F)).subgroupOf
    (Formalism.UG.UPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F))

def KPi (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Subgroup (GAf D) :=
  letI := D.host.cmStar
  (Lv u).U.subgroupOf
    (Formalism.UG.UPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F))

def colFn (D : D7) (Lv : LevelData D) (u : D.what₂.Word) (V : Type) [AddCommGroup V] [Module ℂ V]
    (a : GF D →* Module.End ℂ V) (ψ : KPi D Lv u →* ℂˣ) : Submodule ℂ (GAf D → V) :=
  eqvFn (GF D) (KPi D Lv u) V a ψ

def TrivStab (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  ∀ c : (D.mem u).C.cls 0,
    Formalism.UG.ratPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊓
      (Lv u).U.map (MulAut.conj ((Lv u).y c : GL (Fin D.R.k) _)).toMonoidHom = ⊥

def LevelDataRankBound (D : D7) (Lv : LevelData D) : Prop :=
  ∀ u : D.what₂.Word, TrivStab D Lv u →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (a : GF D →* Module.End ℂ V) (ψ : KPi D Lv u →* ℂˣ),
      Module.finrank ℂ (colFn D Lv u V a ψ) = Nat.card ((D.mem u).C.cls 0) * Module.finrank ℂ V

def AdmittedWeylDimension (_D : D7) : Prop :=
  ∀ (k : ℕ) (u : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsHCTypeU k u π → ((Module.finrank ℂ H : ℕ) : ℝ) = dimV u

structure ColRep (D : D7) (Lv : LevelData D) (u : D.what₂.Word) where
  H : D.what₂.Tau → Type
  [nacg : ∀ ρ, NormedAddCommGroup (H ρ)]
  [ips : ∀ ρ, InnerProductSpace ℂ (H ρ)]
  π : ∀ ρ, Matrix (Fin D.R.k) (Fin D.R.k) ℂ → (H ρ →L[ℂ] H ρ)
  π_type : ∀ ρ, IsHCTypeU D.R.k (uColR D u ρ) (π ρ)
  B : D.what₂.Tau → Matrix (Fin D.R.k) (Fin D.R.k) ℂ
  B_spec : letI := D.host.cmStar; ∀ ρ, (B ρ).conjTranspose * B ρ = D.sp.gram0.map (embOf D ρ)
  a : GF D →* Module.End ℂ (⨂[ℂ] ρ, H ρ)
  a_spec : ∀ (γ : GF D) (γ0 : GL (Fin D.R.k) D.host.E),
    (γ : GAf D).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F)
      (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0 →
    ∀ v : ∀ ρ, H ρ, a γ (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ
      (fun ρ => π ρ (B ρ * (γ0 : Matrix (Fin D.R.k) (Fin D.R.k) D.host.E).map (embOf D ρ) * (B ρ)⁻¹) (v ρ))
  ψ : KPi D Lv u →* ℂˣ

attribute [instance] ColRep.nacg ColRep.ips

abbrev ColRep.V {D : D7} {Lv : LevelData D} {u : D.what₂.Word} (X : ColRep D Lv u) : Type := ⨂[ℂ] ρ, X.H ρ

def BaseWeightColumnCondition (D : D7) (Lv : LevelData D) (u : D.what₂.Word) (X : ColRep D Lv u) : Prop :=
  Nonempty ((D.mem u).A.Mu0 ≃ₗ[ℂ] colFn D Lv u X.V X.a X.ψ)

theorem ColRep.dim_eq {D : D7} {Lv : LevelData D} {u : D.what₂.Word} (X : ColRep D Lv u) (hW : AdmittedWeylDimension D) :
    ((Module.finrank ℂ X.V : ℕ) : ℝ) = ∏ ρ, dimV (uColR D u ρ) := by
  classical
  have hfd : ∀ ρ, FiniteDimensional ℂ (X.H ρ) := fun ρ => (X.π_type ρ).2.1
  have h1 : Module.finrank ℂ X.V = ∏ ρ, Module.finrank ℂ (X.H ρ) := by
    rw [Module.finrank_eq_card_basis (Basis.piTensorProduct (fun ρ => Module.finBasis ℂ (X.H ρ)))]
    simp
  rw [h1]
  push_cast
  exact Finset.prod_congr rfl fun ρ _ => hW D.R.k (uColR D u ρ) (X.H ρ) (X.π ρ) (X.π_type ρ)

theorem rankMu0_of_CL (D : D7) (Lv : LevelData D) (h : LevelDataRankBound D Lv) (hW : AdmittedWeylDimension D) (u : D.what₂.Word)
    (hs : TrivStab D Lv u) (X : ColRep D Lv u) (hX : BaseWeightColumnCondition D Lv u X) :
    ((haveI := (D.mem u).A.Mu0_fd; Module.finrank ℂ (D.mem u).A.Mu0 : ℕ) : ℝ) =
      (Nat.card ((D.mem u).C.cls 0) : ℝ) * ∏ ρ, dimV (uColR D u ρ) := by
  obtain ⟨e⟩ := hX
  have hfd : ∀ ρ, FiniteDimensional ℂ (X.H ρ) := fun ρ => (X.π_type ρ).2.1
  rw [e.finrank_eq, h u hs X.V X.a X.ψ, ← X.dim_eq hW]
  push_cast
  ring

theorem mu0Tie_of_CL (D : D7) (Lv : LevelData D) (h : LevelDataRankBound D Lv) (hW : AdmittedWeylDimension D) (u : D.what₂.Word)
    (hs : TrivStab D Lv u) (X : ColRep D Lv u) (hX : BaseWeightColumnCondition D Lv u X) : Mu0Tie D u :=
  fun _ => rankMu0_of_CL D Lv h hW u hs X hX

theorem trivStab_of (D : D7) (Lv : LevelData D) (h17 : adm17 D Lv) (hp : Conclusion4p D Lv) (hg : GBig D)
    (u : D.what₂.Word) : TrivStab D Lv u := h17 hg u (hp u)

def CTHyp (D : D7) (sc : Scale) (n₀ : ℕ) (A C cb : ℝ) : Prop :=
  NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 ∧
  n₀ ≤ D.R.r ∧ (D.R.rS + 1) ^ 2 ≤ D.R.r ∧
  Real.log (Real.log D.host.rdE) ≤ (D.R.r : ℝ) ∧
  (∀ (τ : D.what₂.Tau) (i : Fin D.R.r), |lamS D.R (D.hc τ) i| ≤ sc.b ^ 2) ∧
  (D.host.g 0 : ℝ) * D.host.g 1 ≤ sc.b ^ A ∧ 4 * D.R.r < D.host.g 0 ∧ SplitsCompl D.host.E (D.host.g 0) ∧
  (∀ τ : D.what₂.Tau, Formalism.QuantumDeterminants.GapAtLeast (epsS D.R) (lamS D.R (D.hc τ))
    (C * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * Real.log (sc.b * D.host.rdE))) ∧
  Real.log (D.R.f : ℝ) ≤ Real.sqrt (D.R.r : ℝ) ∧ 2 ≤ sc.b ∧
  Real.log (Real.log sc.b) ≤ cb * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ)

def RowsEx (D : D7) : Prop := ∃ X : RowsAut, Formalism.MainNotions.PlaceDegreeData.RowsTie D X

def LemmaCTBound (D : D7) (sc : Scale) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  CTHyp D sc n₀ A C cb ∧ sc.x ^ (sc.eps / 8) ≤ c * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ)

def CTBound (D : D7) (sc : Scale) (c : ℝ) : Prop :=
  |(D.what₂.Dall : ℝ) - D.what₂.Dstar| ≤
    Real.exp (-(c * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ))) * D.what₂.Dstar ∧
  Real.exp (-(c * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ))) * D.what₂.Dstar ≤
    Real.exp (-(sc.x ^ (sc.eps / 8))) * D.what₂.Dstar

def CTBoundOfCountBoundAndExistence (D : D7) (sc : Scale) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  Formalism.MainNotions.PlaceDegreeData.WordCountBound D n₀ A C c cb → RowsEx D → LemmaCTBound D sc n₀ A C c cb → CTBound D sc c

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def CTBoundAlongFamily : Prop :=
  ∀ (n₀ : ℕ) (A C c cb : ℝ), 0 < c → 0 < cb → 2 * (Fm.CYL + 1) ≤ A → 2 * C ≤ Fm.Ch0r →
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, LemmaCTBound (Fm.D x i) (Fm.L x i).sc n₀ A C c cb

def RowsExF : Prop := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, RowsEx (Fm.D x i)

def CTBoundF (c : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, CTBound (Fm.D x i) (Fm.L x i).sc c

end Fam

end Formalism.MainNotions.StandardLattice
