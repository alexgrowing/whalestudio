import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SenWeights
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DiagonalQuotientEigen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries

noncomputable section

namespace GlobalTheory.SenCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

section Operators

variable {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D] [Module A D] [Module O D]
  [IsScalarTower O A D]

def NabOn (π : A) (g : D →ₗ[O] D) (P : Submodule O D) (nb : ↥P →ₗ[O] ↥P) : Prop :=
  ∀ x : ↥P, π • ((nb x : ↥P) : D) = g x - x

variable {π : A} {g : D →ₗ[O] D} {P Q : Submodule O D}

end Operators

section Residue

variable {O : Type} [CommRing O]

end Residue

section Sen

variable {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D] [Module A D] [Module O D]
  [IsScalarTower O A D] [IsDomain O] [IsDiscreteValuationRing O]

end Sen

section Wach

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem NΔl_eq (i : ZMod n) : DiagonalQuotientEigen.NΔl W T i = SenWeightsAlt.Ni W T i := rfl

theorem γD_smulA (g : W.Gam) (a : LetA O n) (x : W.DD T) : W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rwa [algebraMap_smul, W.γE_ext, algebraMap_smul] at this

theorem γA_letE (g : W.Gam) (i : ZMod n) : W.γA g (letE i) = letE i := by
  funext j
  change W.γ₀ g (Pi.single (M := fun _ => PowerSeries O) i 1 j) = Pi.single (M := fun _ => PowerSeries O) i 1 j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem mul_letE {a b : LetA O n} {i : ZMod n} (h : a i = b i) : a * letE i = b * letE i := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [h]
  · simp [letE, hj]

theorem letE_mul (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  rw [mul_letE (b := 1) (by simp [letE]), one_mul]

theorem mem_Ni {i : ZMod n} {x : W.DD T} :
    x ∈ SenWeightsAlt.Ni W T i ↔ x ∈ W.NΔ T ∧ (letE i : LetA O n) • x = x := by
  refine and_congr_right fun hx => ⟨?_, fun h => ⟨x, hx.1, h⟩⟩
  rintro ⟨y, -, rfl⟩
  change (letE i : LetA O n) • (letE i : LetA O n) • y = (letE i : LetA O n) • y
  rw [smul_smul, letE_mul]

theorem γD_mem_Ni {i : ZMod n} (g : W.Gam) {x : W.DD T} (hx : x ∈ SenWeightsAlt.Ni W T i) :
    W.γD T g x ∈ SenWeightsAlt.Ni W T i := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := (mem_Ni W T).1 hx
  refine (mem_Ni W T).2 ⟨⟨W.N_Γ T g x h1, fun δ hδ => ?_⟩, ?_⟩
  · rw [← W.γD_mul, mul_comm, W.γD_mul, h2 δ hδ]
  · rw [← γA_letE W g i, ← γD_smulA, h3]

theorem γA_mem_AΔ (g : W.Gam) {c : LetA O n} (hc : c ∈ W.AΔ) : W.γA g c ∈ W.AΔ := fun δ hδ => by
  funext j
  have h : W.γ₀ δ (c j) = c j := congrFun (hc δ hδ) j
  change (W.γ₀ δ * W.γ₀ g) (c j) = W.γ₀ g (c j)
  rw [← map_mul, mul_comm, map_mul, AlgHom.mul_apply, h]

theorem twγ_one (g : W.Gam) : SenWeightsAlt.twγ W g T 1 = W.γD T g :=
  LinearMap.ext fun x => one_smul (LetA O n) (W.γD T g x)

section RankOne

variable {r : ℕ} (hr : r = 1) (β : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (hβ : ∀ k, (β k : W.DD T) ∈ W.NΔ T)
include hr hβ

end RankOne

end Wach

section Prime

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P)

def OpFrom (m : ℤ) : Prop :=
  5 ≤ l → ∀ (K LL : FinExt l) (hA : CaseA K LL) (g : (H.W K 1 LL hA.2.2).Gam),
    (((H.W K 1 LL hA.2.2).χΓ g : (↥(OL LL))ˣ) : ↥(OL LL)) = 1 + (l : ↥(OL LL)) →
    ∀ (h : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ)
      (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
      CrysWith (P.PD K) (H.W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u ∧ u ≤ h i) →
      (∀ i, DiagonalQuotientEigen.SenPair (H.W K 1 LL hA.2.2) T g 1 i (U i) 0) ∧
        ∀ (χ₁ : ↥(GK K) →* (↥(OL LL))ˣ) (w : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℤ)
          (hχ : IsCrysChar (LL := ↥LL.1) (P.PD K) (H.W K 1 LL hA.2.2).emb χ₁ w),
          (∀ i, m ≤ w i ∧ w i ≤ h i) →
          ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
            (b : (H.W K 1 LL hA.2.2).DD (charLat ℚ_[l] Subtype.val_injective χ₁ hχ.1))
            (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))),
            DiagonalQuotientEigen.IsGenWith (H.W K 1 LL hA.2.2) (charLat ℚ_[l] Subtype.val_injective χ₁ hχ.1) g i b a →
              DiagonalQuotientEigen.SenPair (H.W K 1 LL hA.2.2) T g a i (U i) (w i)

def QuoFrom (m : ℤ) : Prop :=
  ∀ (K LL : FinExt l) (hg : Good K 1 LL) (lam : ↥(OL LL)),
    Standing P K LL (H.W K 1 LL hg).emb lam →
    ∀ g : (H.W K 1 LL hg).Gam, (((H.W K 1 LL hg).χΓ g : (↥(OL LL))ˣ) : ↥(OL LL)) = 1 + (l : ↥(OL LL)) →
    ∀ (h : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ), (∀ i, 2 ≤ h i) →
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ),
      CrysWith (P.PD K) (H.W K 1 LL hg).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u ∧ u ≤ (h i : ℤ)) →
      (∀ i, SenWeightsAlt.Concl (H.W K 1 LL hg) l lam T i ((H.W K 1 LL hg).γD T g) (U i)) ∧
      ∀ (χ₁ : ↥(GK K) →* (↥(OL LL))ˣ) (w : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℤ)
        (hχ : IsCrysChar (P.PD K) (H.W K 1 LL hg).emb χ₁ w), (∀ i, m ≤ w i ∧ w i ≤ (h i : ℤ) - 1) →
        ∀ i, (∃ e b, SenWeightsAlt.IsInvMult (H.W K 1 LL hg) g (charLat ℚ_[l] Subtype.val_injective χ₁ hχ.1) i e b) ∧
          ∀ e b, SenWeightsAlt.IsInvMult (H.W K 1 LL hg) g (charLat ℚ_[l] Subtype.val_injective χ₁ hχ.1) i e b →
            SenWeightsAlt.Concl (H.W K 1 LL hg) l lam T i (SenWeightsAlt.twγ (H.W K 1 LL hg) g T b)
              ((U i).map fun u => u - w i)

theorem OpFrom.mono {m m' : ℤ} (hm : m ≤ m') (h : OpFrom P H m) : OpFrom P H m' :=
  fun h5 K LL hA g hg hh U T hT hU => ⟨(h h5 K LL hA g hg hh U T hT hU).1, fun χ₁ w hχ hw =>
    (h h5 K LL hA g hg hh U T hT hU).2 χ₁ w hχ fun i => ⟨hm.trans (hw i).1, (hw i).2⟩⟩

variable {K LL : FinExt l} (hA : CaseA K LL)

theorem standing_iff {hg : Good K 1 LL} (lam : ↥(OL LL)) :
    Standing P K LL (H.W K 1 LL hg).emb lam ↔ 5 ≤ l ∧ CaseA K LL ∧ Irreducible lam :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2.2.2.2⟩, fun h => ⟨h.1, h.2.1, by rw [show K0 K = K.1 from inf_eq_left.2 h.2.1.1],
    (H.W K 1 LL hg).emb_bij, (H.W K 1 LL hg).emb_σ, h.2.2⟩⟩

end Prime

end GlobalTheory.SenCompare
