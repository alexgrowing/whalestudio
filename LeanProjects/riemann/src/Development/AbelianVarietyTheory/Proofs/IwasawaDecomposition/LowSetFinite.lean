import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitComponentsDeterminedByPointOfBaseChange

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
  GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.RatSide

section Clauses

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def HeckeRd (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Sb : Finset (PlE D.host))
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j)) : Prop :=
  ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat R Sb (idxOf D j) k P α Rr → ∀ x : Fin (R.nW (idxOf D j)) → D.what₂.LL,
    (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) (hL j k P x)) =
      hkNorm R (idxOf D j) k P • heckeOn (R.MW (idxOf D j) (sg0 D A3.A)) Rr
        ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x))

def LvlPsi (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) : Prop :=
  (∀ g : G, g ∈ F.P0 ↔ (R.eG.trans cG) g ∈ Formalism.IndefR.NX.U D.nd) ∧
    ∀ (u : F.P0) (hu : (R.eG.trans cG) u ∈ Formalism.IndefR.NX.U D.nd),
      (((psiUOf D.nd (NX.xiRed D) θ ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) = (((F.ψ0 u)⁻¹ : D.what₂.LLˣ) : D.what₂.LL)

end Clauses

section Rat

variable {D : D7}

def FormsC (S : RatDat D.ntw) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm ∧ FiniteDimensional S.Ks (FmK S j) ∧
    ∃ T : Finset (S.WL j), (∀ x ∈ T, x ∈ (S.A j).MK) ∧
      (∀ x ∈ (S.A j).MK, x ∈ (S.A j).WK ∧ x ∈ Submodule.span (𝓞 S.Ks) (T : Set (S.WL j))) ∧
      ∀ x ∈ (S.A j).WK, x ∈ Submodule.span S.Ks (T : Set (S.WL j))

def StabC (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ k P (x : S.WL j), x ∈ (S.A j).WK → hL j k P x ∈ (S.A j).WK

def IntC (S : RatDat D.ntw) (Sb : Finset (PlE D.host)) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) : Prop :=
  ∀ j k P, 1 ≤ j → j ≤ D.R.m → IsSplitPl D.host P → P ∉ Sb → k ≤ D.R.r → ∃ n : ℕ,
    ∀ x ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), x ∈ goodL D S θ j →
      (normV P) ^ n • hL j k P x ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j))

def SpanC (S : RatDat D.ntw) (Sb : Finset (PlE D.host)) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → goodL D S θ j ≤
    ⨆ σ ∈ {σ | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}, goodL D S θ j ⊓ ⨅ (k : ℕ) (P : PlE D.host)
      (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ Sb), Module.End.eigenspace (hL j k P) ((eig j σ k P : ↥D.LL0) : D.what₂.LL)

def lowSet (D : D7) : Set (PlE D.host) := {v | ∃ p ∈ lowAll D, p ≠ 0 ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal}

theorem lowSet_finite (D : D7) : (lowSet D).Finite := by
  refine Set.Finite.subset (Set.Finite.biUnion (s := (((lowAll D).filter (· ≠ 0) : Finset ℕ) : Set ℕ)) (Finset.finite_toSet _)
    fun p hp => GlobalTheory.RowTie.placesOver_finite_of_ne_zero D.host.E p (Finset.mem_filter.1 hp).2) ?_
  rintro v ⟨p, hp, hp0, hv⟩
  exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hp, hp0⟩)) hv

def SbD (D : D7) : Finset (PlE D.host) := (lowSet_finite D).toFinset

theorem overSet_SbD (D : D7) : OverSet D (SbD D) (lowAll D) := by
  intro v hv
  obtain ⟨p, hp, -, hv⟩ := (lowSet_finite D).mem_toFinset.1 hv
  exact ⟨p, hp, hv⟩

end Rat

section State

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def kKsOf (x : St P) : x.m.z.core.Q.c.F →+* ↥(Dof x).LL0 :=
  (algebraMap x.m.z.core.Q.c.F (Dof x).what₂.LL).codRestrict (Dof x).LL0 x.m.z.fieldValues_mem_fixedField

theorem hkOf (x : St P) (y : x.m.z.core.Q.c.F) :
    ((kKsOf x y : ↥(Dof x).LL0) : (Dof x).what₂.LL) = algebraMap x.m.z.core.Q.c.F (Dof x).what₂.LL y := rfl

abbrev SOf (x : St P) : RatDat (Dof x).ntw := ratDatR x.m.z.R x.m.z.cG (kKsOf x) (hkOf x)

end State

end GlobalTheory.HeightCounting.RatSide
