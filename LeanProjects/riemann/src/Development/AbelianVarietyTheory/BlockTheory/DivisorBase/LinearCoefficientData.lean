import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.L2.DIV
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.LinearCoefficientData

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsRecPlaces (D : D7) (Pg : Finset (Pl D.host.E)) : Prop :=
  ∀ PP, PP ∈ Pg ↔ ∃ kv : (Σ k : Fin 2, D.nd.PlG k), D.naut.plGw kv.1 kv.2 = PP

def resMap {E : Type} [Field E] [NumberField E] (p : ℕ) (PP : Pl E) (h : (p : 𝓞 E) ∈ PP.asIdeal) :
    ZMod p →+* kP PP :=
  ZMod.castHom (m := ringChar (kP PP))
    ((ringChar.spec (kP PP) p).1 (by
      rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 h)) (kP PP)

def idx {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (PP : ↥Pg) : (Σ k : Fin 2, D.nd.PlG k) :=
  ((h PP.1).1 PP.2).choose

theorem idx_spec {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (PP : ↥Pg) :
    D.naut.plGw (idx h PP).1 (idx h PP).2 = PP.1 :=
  ((h PP.1).1 PP.2).choose_spec

theorem idx_mem {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (PP : ↥Pg) :
    ((D.host.g (idx h PP).1 : ℕ) : 𝓞 D.host.E) ∈ PP.1.asIdeal := by
  have h1 := D.naut.plGw_over (idx h PP).1 (idx h PP).2
  rw [idx_spec h PP] at h1
  exact h1

theorem idx_eq {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (PP : ↥Pg) (kv : Σ k : Fin 2, D.nd.PlG k)
    (e : D.naut.plGw kv.1 kv.2 = PP.1) : idx h PP = kv := by
  have h1 := idx_mem h PP
  have h2 : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ PP.1.asIdeal := by
    have := D.naut.plGw_over kv.1 kv.2
    rw [e] at this
    exact this
  have h3 := idx_spec h PP
  generalize idx h PP = a at h1 h3
  obtain ⟨k, v⟩ := a
  obtain ⟨k', v'⟩ := kv
  have hk : k = k' := by
    by_contra hne
    have hg : D.host.g k ≠ D.host.g k' := by
      have := D.host.g_ne
      fin_cases k <;> fin_cases k' <;> first | exact absurd rfl hne | exact this | exact this.symm
    have hc : IsCoprime ((D.host.g k : ℕ) : 𝓞 D.host.E) ((D.host.g k' : ℕ) : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime k) (D.host.g_prime k')).2 hg)
    obtain ⟨a, b, hab⟩ := hc
    refine PP.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
  subst hk
  have hv : v = v' := D.naut.plGw_inj k (h3.trans e.symm)
  rw [hv]

def toG0 {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (γ : G0g D.nd) : G0 Pg D.R.r := fun PP =>
  Matrix.GeneralLinearGroup.map (resMap (D.host.g (idx h PP).1) PP.1 (idx_mem h PP)) (γ (idx h PP))

def eCoef {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) : G0 Pg D.R.r →₀ ℂ :=
  Finsupp.mapDomain (toG0 h) D.ntypes.e0.coeff

def datR (V : HSp D) (hr : V.rank = D.R.r) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ) (fr : Lev.Frm) :
    LevDat D.host.E ℂ V.rank :=
  Lev.datY V.rank D.R.r D.R.t 0 hr.ge Pg ∅ P (fun _ _ => 1) (fun _ => 1) fr

def eLin (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (e : G0 L.Pg L.r →₀ ℂ) :
    (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun F := Lev.eAct V β L e F
  map_add' F G := by
    funext x
    simp only [Lev.eAct, Finsupp.sum, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold Lev.actG0
    split_ifs
    · simp only [Pi.add_apply]; ring
    · simp
  map_smul' c F := by
    funext x
    simp only [Lev.eAct, Finsupp.sum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold Lev.actG0
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul]; ring
    · simp

theorem rank_zeroth_component_eq (D : D7) : (D.sp.Y 0).rank = D.R.r := by
  rw [D.sp.Y_rank 0 (Nat.zero_le _)]; simp [Ranks.rankY]

abbrev InfFam (D : D7) : Type := D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)

abbrev Eig (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

abbrev datE (D : D7) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ) : LevDat D.host.E ℂ (D.sp.Y 0).rank :=
  datR (D.sp.Y 0) (rank_zeroth_component_eq D) Pg P Lev.Frm.B

abbrev datWj (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ) :
    LevDat D.host.E ℂ (D.sp.W j).rank :=
  datR (D.sp.W j) (D.sp.W_rank j h1 h2) Pg P Lev.Frm.A

def EEc (θ : InfFam D) (M : Mult.DSModel (D.sp.Y 0) (Mult.parB (Mult.tparRec D) 0)) {Pg : Finset (Pl D.host.E)}
    (h : IsRecPlaces D Pg) (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (P : LevelP Pg D.R.r ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : Eig D) : Submodule ℂ (Mult.MMap M) :=
  Mult.EEpart θ M (Lev.levG (D.sp.Y 0) β (datE D Pg P)) (Lev.levChi (D.sp.Y 0) β (datE D Pg P))
    (eLin (D.sp.Y 0) β (datE D Pg P) (eCoef h)) S c

def Wc (θ : InfFam D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (M : Mult.DSModel (D.sp.W j) (Mult.parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)))) {Pg : Finset (Pl D.host.E)}
    (h : IsRecPlaces D Pg) (β : GL (Fin (D.sp.W j).rank) (Lev.EAf D)) (P : LevelP Pg D.R.r ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : Eig D) : Submodule ℂ (Mult.MMap M) :=
  Mult.Wpart θ j M (Lev.levG (D.sp.W j) β (datWj D j h1 h2 Pg P)) (Lev.levChi (D.sp.W j) β (datWj D j h1 h2 Pg P))
    (eLin (D.sp.W j) β (datWj D j h1 h2 Pg P) (eCoef h)) S c

def ParamGap (D : D7) : Prop :=
  ∀ τ (n : ℕ), n + 1 < D.R.r → Formalism.L2.NTheta.lamAt (D.hc τ) (n + 1) + (D.R.r : ℚ) ≤ Formalism.L2.NTheta.lamAt (D.hc τ) n

def IsFrameOf (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) : Prop :=
  ∃ (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), Lev.IsBaseFrame V β Λ N

def DimPartsAt {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (P : LevelP Pg D.R.r ℂ) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ →
  ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (M₀ : Mult.DSModel (D.sp.Y 0) (Mult.parB (Mult.tparRec D) 0))
    (M₁ : Mult.DSModel (D.sp.W j) (Mult.parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j))))
    (β₀ : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (β₁ : GL (Fin (D.sp.W j).rank) (Lev.EAf D)),
    IsFrameOf (D.sp.Y 0) β₀ → IsFrameOf (D.sp.W j) β₁ →
  ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)),
    Mult.SphOff (Lev.levG (D.sp.Y 0) β₀ (datE D Pg P) : Set (GA D (D.sp.Y 0)))
      (Lev.levChi (D.sp.Y 0) β₀ (datE D Pg P)) S →
    Mult.SphOff (Lev.levG (D.sp.W j) β₁ (datWj D j h1 h2 Pg P) : Set (GA D (D.sp.W j)))
      (Lev.levChi (D.sp.W j) β₁ (datWj D j h1 h2 Pg P)) S →
  ∀ c : Eig D,
    FiniteDimensional ℂ (EEc θ M₀ h β₀ P S c) ∧ FiniteDimensional ℂ (Wc θ j h1 h2 M₁ h β₁ P S c) ∧
      Module.finrank ℂ (Wc θ j h1 h2 M₁ h β₁ P S c) = Module.finrank ℂ (EEc θ M₀ h β₀ P S c)

def DimensionDecompositionAtBasePrime (D : D7) : Prop :=
  ∀ (Pg : Finset (Pl D.host.E)) (h : IsRecPlaces D Pg) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ),
    IsGenericPsi Pg ψ → DimPartsAt h (P0 Pg D.R.r ψ)

def DimParts : Prop :=
  ∀ D : D7, ParamGap D → GlobalTheory.GLq.ESerTie D → DimensionDecompositionAtBasePrime D

def DimPartsThree : Prop :=
  ∀ D : D7, ParamGap D → GlobalTheory.GLq.ESerTie D →
    ∀ (Pg : Finset (Pl D.host.E)) (h : IsRecPlaces D Pg) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ),
      IsGenericPsi Pg ψ → DimPartsAt h (LevelP.triv Pg D.R.r ℂ) ∧ DimPartsAt h (P0 Pg D.R.r ψ) ∧
        DimPartsAt h (PsharpSym Pg D.R.r D.R.rS D.R.k ψ)

theorem DimPartsThree.dimParts (h : DimPartsThree) : DimParts :=
  fun D h1 h2 Pg hP ψ hψ => (h D h1 h2 Pg hP ψ hψ).2.1

theorem exists_isRecPlaces (D : D7) : ∃ Pg, IsRecPlaces D Pg := by
  classical
  letI := D.nd.finPlG
  exact ⟨Finset.univ.image fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.naut.plGw kv.1 kv.2, fun PP => by simp⟩

example (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ) :
    (datE D Pg P).P = P ∧ (datWj D j h1 h2 Pg P).P = P.conj := ⟨rfl, rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.LinearCoefficientData

end
