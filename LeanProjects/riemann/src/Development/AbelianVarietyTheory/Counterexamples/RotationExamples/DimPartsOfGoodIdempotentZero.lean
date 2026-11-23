import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LinearCoefficientData

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke.LinearCoefficientData
open scoped TensorProduct

namespace GlobalTheory.DimPartsTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure Matching (D : D7) (Pg : Finset (Pl D.host.E)) where
  plg : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg
  mem : ∀ PP : ↥Pg, ((D.host.g (plg.symm PP).1 : ℕ) : 𝓞 D.host.E) ∈ PP.1.asIdeal
  nconj : ∀ PP PP' : ↥Pg, ¬ IsConjPl D.host PP.1 PP'.1

def Matching.toG0 {Pg : Finset (Pl D.host.E)} (μ : Matching D Pg) (γ : G0g D.nd) : G0 Pg D.R.r := fun PP =>
  Matrix.GeneralLinearGroup.map (resMap (D.host.g (μ.plg.symm PP).1) PP.1 (μ.mem PP)) (γ (μ.plg.symm PP))

def Matching.eCoef {Pg : Finset (Pl D.host.E)} (μ : Matching D Pg) : G0 Pg D.R.r →₀ ℂ :=
  Finsupp.mapDomain μ.toG0 D.ntypes.e0.coeff

def DimAtWith {Pg : Finset (Pl D.host.E)} (e : G0 Pg D.R.r →₀ ℂ) (P : LevelP Pg D.R.r ℂ) : Prop :=
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
    let A := Mult.EEpart θ M₀ (Lev.levG (D.sp.Y 0) β₀ (datE D Pg P)) (Lev.levChi (D.sp.Y 0) β₀ (datE D Pg P))
      (eLin (D.sp.Y 0) β₀ (datE D Pg P) e) S c
    let B := Mult.Wpart θ j M₁ (Lev.levG (D.sp.W j) β₁ (datWj D j h1 h2 Pg P))
      (Lev.levChi (D.sp.W j) β₁ (datWj D j h1 h2 Pg P)) (eLin (D.sp.W j) β₁ (datWj D j h1 h2 Pg P) e) S c
    FiniteDimensional ℂ A ∧ FiniteDimensional ℂ B ∧ Module.finrank ℂ B = Module.finrank ℂ A

theorem dimPartsAt_iff {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (P : LevelP Pg D.R.r ℂ) :
    DimPartsAt h P ↔ DimAtWith (eCoef h) P := Iff.rfl

def DimPartsAnyMatching : Prop :=
  ∀ D : D7, ParamGap D → GlobalTheory.GLq.ESerTie D →
    ∀ (Pg : Finset (Pl D.host.E)) (μ : Matching D Pg) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ),
      IsGenericPsi Pg ψ → DimAtWith μ.eCoef (P0 Pg D.R.r ψ)

def recMatching {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) : Matching D Pg where
  plg :=
    { toFun := fun kv => ⟨D.naut.plGw kv.1 kv.2, (h _).2 ⟨kv, rfl⟩⟩
      invFun := idx h
      left_inv := fun kv => idx_eq h _ kv rfl
      right_inv := fun PP => Subtype.ext (idx_spec h PP) }
  mem := idx_mem h
  nconj := by
    intro PP PP' hc
    have h1 := idx_mem h PP
    have h2 := idx_mem h PP'
    have e1 := idx_spec h PP
    have e2 := idx_spec h PP'
    generalize idx h PP = a at h1 e1
    generalize idx h PP' = b at h2 e2
    obtain ⟨k, v⟩ := a
    obtain ⟨k', v'⟩ := b
    by_cases hk : k = k'
    · subst hk
      rw [← e1, ← e2] at hc
      exact D.naut.plGw_nconj k v v' hc
    · have h3 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP'.1.asIdeal :=
        (hc _ _ (by simp)).1 h1
      have hg : D.host.g k ≠ D.host.g k' := by
        have := D.host.g_ne
        fin_cases k <;> fin_cases k' <;> first | exact absurd rfl hk | exact this | exact this.symm
      have hcp : IsCoprime ((D.host.g k : ℕ) : 𝓞 D.host.E) ((D.host.g k' : ℕ) : 𝓞 D.host.E) :=
        Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime k) (D.host.g_prime k')).2 hg)
      obtain ⟨a, b, hab⟩ := hcp
      refine PP'.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
      rw [← hab]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h3) (Ideal.mul_mem_left _ _ h2)

theorem recMatching_eCoef {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) : (recMatching h).eCoef = eCoef h := rfl

theorem dimParts_of_anyMatching (H : DimPartsAnyMatching) : DimParts := fun D h1 h2 Pg h ψ hψ =>
  (dimPartsAt_iff h _).2 (recMatching_eCoef h ▸ H D h1 h2 Pg (recMatching h) ψ hψ)

theorem eLin_zero (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) : eLin V β L 0 = 0 := by
  ext F x
  simp [eLin, Lev.eAct]

theorem goodPart_zero {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : Mult.DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) : Mult.goodPart θ M J χ 0 = ⊥ := by
  rw [eq_bot_iff]
  intro T hT
  have h := hT.2
  have h0 : Mult.postOn M (0 : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) T = 0 := by
    ext v; simp [Mult.postOn]
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, h0, LinearMap.id_apply, zero_sub, neg_eq_zero] at h
  simpa using h

theorem dimAtWith_zero {Pg : Finset (Pl D.host.E)} (P : LevelP Pg D.R.r ℂ) : DimAtWith 0 P := by
  intro θ _ j h1 h2 M₀ M₁ β₀ β₁ _ _ S _ _ c A B
  have hA : A = ⊥ := by
    simp only [A, Mult.EEpart, Mult.EErec, Mult.EE]
    erw [eLin_zero, goodPart_zero]; simp
  have hB : B = ⊥ := by
    simp only [B, Mult.Wpart, Mult.WgoodRec, Mult.Wgood]
    erw [eLin_zero, goodPart_zero]; simp
  rw [hA, hB]
  exact ⟨inferInstance, inferInstance, by simp⟩

theorem dimParts_of_good_idempotent_zero (h0 : D.ntypes.e0 = 0) : DimensionDecompositionAtBasePrime D := by
  intro Pg h ψ _
  have : eCoef h = 0 := by simp [eCoef, h0]
  rw [dimPartsAt_iff, this]
  exact dimAtWith_zero _

theorem paramGap_of_params (L : SizeData₂ D) (Pm : ParameterChoice' D L) : ParamGap D := by
  intro τ n hn
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hg : (D.R.r : ℝ) ≤ Formalism.BasicNotions.LevelStarExponents.gapS D Pm.Cgap := by
    unfold Formalism.BasicNotions.LevelStarExponents.gapS
    have h1 : D.R.r ≤ D.R.N D.R.m * D.R.m ^ 10 := by
      have a : D.R.r ≤ D.R.N D.R.m := by
        unfold Ranks.r Ranks.N
        have : D.R.m ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      exact a.trans (Nat.le_mul_of_pos_right _ (by positivity))
    have h2 : (D.R.r : ℝ) ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 := by exact_mod_cast h1
    have h3 : 0 ≤ Pm.Cgap * D.R.k * (D.R.m : ℝ) ^ 4 := by have := Pm.Cgap_pos; positivity
    linarith
  obtain ⟨s1, s2, s3⟩ := Pm.sig_gaps τ
  have cast : ∀ x : ℚ, Formalism.BasicNotions.LevelStarExponents.gapS D Pm.Cgap < (x : ℝ) → (D.R.r : ℚ) ≤ x := fun x hx => by
    have : ((D.R.r : ℚ) : ℝ) ≤ (x : ℝ) := by push_cast; linarith
    exact_mod_cast this
  unfold Ranks.r at hn
  unfold Formalism.L2.NTheta.lamAt
  by_cases h1 : n + 1 < D.R.k - 1
  · rw [dif_pos h1, dif_pos (by omega : n < D.R.k - 1)]
    have := cast _ (s1 n h1)
    linarith
  · by_cases h2 : n + 1 = D.R.k - 1
    · rw [dif_neg h1, dif_pos (by omega : n < D.R.k - 1), dif_pos (by omega : n + 1 - (D.R.k - 1) < D.R.m)]
      have := cast _ (s2 (by omega) (by omega))
      have e1 : (⟨n, by omega⟩ : Fin (D.R.k - 1)) = ⟨D.R.k - 2, by omega⟩ := Fin.ext (by simp only; omega)
      have e2 : (⟨n + 1 - (D.R.k - 1), by omega⟩ : Fin D.R.m) = ⟨0, by omega⟩ := Fin.ext (by simp only; omega)
      rw [e1, e2]
      linarith
    · rw [dif_neg h1, dif_neg (by omega : ¬ n < D.R.k - 1), dif_pos (by omega : n + 1 - (D.R.k - 1) < D.R.m),
        dif_pos (by omega : n - (D.R.k - 1) < D.R.m)]
      have := cast _ (s3 (n - (D.R.k - 1)) (by omega))
      have e2 : (⟨n + 1 - (D.R.k - 1), by omega⟩ : Fin D.R.m) = ⟨n - (D.R.k - 1) + 1, by omega⟩ :=
        Fin.ext (by simp only; omega)
      rw [e2]
      linarith

end GlobalTheory.DimPartsTest

end
