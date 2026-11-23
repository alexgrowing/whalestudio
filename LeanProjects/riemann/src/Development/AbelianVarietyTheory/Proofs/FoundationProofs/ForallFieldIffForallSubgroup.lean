import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.ReductionClauses

noncomputable section

namespace GlobalTheory.PointIrredCompare

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ReductionClauses
open scoped Pointwise

section Galois

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem mem_smul_iff (A : ValuationSubring Ω) (g : G F Ω) (y : Ω) :
    y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]

theorem valuation_smul_lt_one_iff (A : ValuationSubring Ω) (g : G F Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', mem_smul_iff, mem_smul_iff, map_inv₀,
    map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]

theorem conj_mem_Ine_of_smul {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, mem_smul_iff]
      have : (g⁻¹ : G F Ω) (g x) = x := by
        show (g⁻¹ * g) x = x
        simp
      rw [this]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (valuation_smul_lt_one_iff A g _).1 (hσ.2 _ hx')
    have e : (g⁻¹ : G F Ω) (σ (g x) - g x) = (g⁻¹ * σ * g) x - x := by
      rw [map_sub]
      congr 1
      show (g⁻¹ * g) x = x
      simp
    rwa [e] at h

theorem Ine_le_of_normal [IsAlgClosure F Ω] {A B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A w) (hB : IsPlaceOver B w) (Hs : Subgroup (G F Ω)) [hn : Hs.Normal]
    (h : Ine (F := F) A ≤ Hs) : Ine (F := F) B ≤ Hs := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver hA hB
  intro σ hσ
  have := hn.conj_mem _ (h (conj_mem_Ine_of_smul hσ)) g
  simpa [mul_assoc] using this

end Galois

section Hyps

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem lpDim_spehLoc (p : Part A.CG) (w : PlE H) : A.lpDim (spehLoc N A p w) = p.a * p.d := by
  have h : ∀ l : List ℝ, A.lpDim (l.foldr
      (fun k acc => A.lpSum (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) acc) (A.lpZero w)) =
      p.a * l.length := by
    intro l
    induction l with
    | nil => simp [A.lpDim_zero]
    | cons a l ih => simp only [List.foldr_cons, A.lpDim_sum, A.lpDim_tw, A.locG_dim, ih, List.length_cons]; ring
  unfold spehLoc
  rw [h]
  simp

theorem lpDim_isoLoc (P : List (Part A.CG)) (w : PlE H) : A.lpDim (isoLoc N A P w) = rankIso N A P := by
  induction P with
  | nil => simp [isoLoc, rankIso, A.lpDim_zero]
  | cons p P ih =>
    have : isoLoc N A (p :: P) w = A.lpSum (spehLoc N A p w) (isoLoc N A P w) := rfl
    rw [this, A.lpDim_sum, ih, lpDim_spehLoc]
    simp [rankIso]

theorem rank_of_hasParamX {i : N.Loc} {x : N.X i} {Sig : List (Part A.CG)} (h : HasParamX N A i x Sig) :
    (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) ∧ rankIso N A Sig = R.r := by
  obtain ⟨P, -, h1, -, h3, -⟩ := h
  refine ⟨fun p hp => ?_, ?_⟩
  · have := h1 ⟨p.a, A.tw p.π A.etaTinv, p.d⟩
      (List.mem_map.2 ⟨p, List.mem_append_left _ hp, rfl⟩)
    exact ⟨this.1, this.2.1⟩
  · simp only [rankIso, twistIso, muPart, List.map_map, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Ranks.nV] at h3 ⊢
    have e : List.map ((fun p : Part A.CG => p.a * p.d) ∘
        fun p : Part A.CG => (⟨p.a, A.tw p.π A.etaTinv, p.d⟩ : Part A.CG)) Sig =
        List.map (fun p : Part A.CG => p.a * p.d) Sig := rfl
    rw [e] at h3
    omega

def FullLabels (Sig : List (Part A.CG)) : Prop :=
  ∀ (k : Fin 2) (v : N.PlG k),
    (A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v))).natDegree = A.lpDim (isoLoc N A Sig (A.plGw k v))

theorem fullLabels_of_good {i : N.Loc} {x : N.X i} {Sig : List (Part A.CG)} (h : HasParamX N A i x Sig)
    (hg : goodSig N A Sig) : FullLabels N A Sig := fun k v => by
  rw [lpDim_isoLoc, (rank_of_hasParamX N A h).2]
  exact ((hg k).1.1 v).2.1

def WildTrivial (Sig : List (Part A.CG)) : Prop :=
  ∀ k, ∀ w ∈ placesOver H.E (H.g k), DepthZero N A (isoLoc N A Sig w)

def TameChosen (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  ∀ k : Fin 2, N.l i ≠ H.g k → ∀ w ∈ placesOver H.E (H.g k),
    ¬ ((redRep N i ρ (N.gam0 i w) : GL (Fin R.r) (IsLocalRing.ResidueField (N.O i))) :
        Matrix (Fin R.r) (Fin R.r) (IsLocalRing.ResidueField (N.O i))).charpoly.IsRoot
      (IsLocalRing.residue (N.O i) ((N.chi i 1 (N.gam0 i w) : (N.O i)ˣ) : N.O i))

def CoreConcl (i : N.Loc) (Sig : List (Part A.CG)) : Prop :=
  IsCuspIso N A Sig ∧ ∀ ρ, IsRepOfSig N A i Sig ρ → ClauseB N A i ρ ∧ ClauseC N A i ρ ∧ TameChosen N i ρ

variable {A} in

def SurplusConcl (T : NTypes A) (i : N.Loc) (Sig : List (Part A.CG)) : Prop :=
  (∀ π : A.CG R.r, Sig = [⟨R.r, π, 1⟩] → A.csd π ∧ A.ralg π) ∧
  (∀ i', i' ≠ i → ∀ ρ, IsRepOfSig N A i' Sig ρ → ClauseB N A i' ρ ∧ ClauseC N A i' ρ) ∧
  ∀ i' ρ, IsRepOfSig N A i' Sig ρ → ClauseD N T i' ρ ∧ ClauseTame N i' ρ

end Hyps

def Core (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (Sig : List (Part D.naut.CG)), HasParamX D.nd D.naut i x Sig →
    goodSig D.nd D.naut Sig → CoreConcl D.nd D.naut i Sig

def CoreTame (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (Sig : List (Part D.naut.CG)), HasParamX D.nd D.naut i x Sig →
    WildTrivial D.nd D.naut Sig → goodSig D.nd D.naut Sig → CoreConcl D.nd D.naut i Sig

def Surplus (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (Sig : List (Part D.naut.CG)), HasParamX D.nd D.naut i x Sig →
    WildTrivial D.nd D.naut Sig → goodSig D.nd D.naut Sig → SurplusConcl D.nd D.ntypes i Sig

def DepthLink (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (Sig : List (Part D.naut.CG)), HasParamX D.nd D.naut i x Sig →
    FullLabels D.nd D.naut Sig → WildTrivial D.nd D.naut Sig

end GlobalTheory.PointIrredCompare

end
