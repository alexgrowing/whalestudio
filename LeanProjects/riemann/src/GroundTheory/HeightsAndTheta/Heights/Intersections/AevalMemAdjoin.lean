import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsEvalKerKrullDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace FibreTranscendence

theorem aeval_red {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L] {J : Type} (y : J → L)
    (g : MvPolynomial J ℤ) :
    aeval y (MvPolynomial.map (Int.castRingHom (ZMod p)) g) = aeval y g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf => simp only [map_mul, hf, map_X, aeval_X]

theorem aeval_mem_adjoin {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L] {J : Type} (y : J → L)
    (g : MvPolynomial J ℤ) : aeval y g ∈ IntermediateField.adjoin (ZMod p) (Set.range y) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [intCast_mem]
  | add f g hf hg => simpa using add_mem hf hg
  | mul_X f i hf =>
    simpa using mul_mem hf (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

variable {K : Type} {ι : K → Type}

theorem ker_aeval_F {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L] (y : (Σ k, ι k) → L)
    {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) (hJ : RingHom.ker (aeval y : MRing ι →ₐ[ℤ] L) = J) :
    RingHom.ker (aeval y : MRingOver (ZMod p) ι →ₐ[ZMod p] L) = J.map (PointVertical.red (ι := ι) p) := by
  ext f
  obtain ⟨g, rfl⟩ := PointVertical.red_surjective (ι := ι) p f
  rw [PointVertical.mem_map_red_iff p hp, RingHom.mem_ker, ← hJ, RingHom.mem_ker]
  exact iff_of_eq (congrArg (· = 0) (aeval_red p y g))

theorem trdeg_adjoin [Fintype K] [∀ k, Fintype (ι k)] (hE : EvalKerKrullDim.Statement) {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L]
    (y : (Σ k, ι k) → L) {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J)
    (hJ : RingHom.ker (aeval y : MRing ι →ₐ[ℤ] L) = J) {n : ℕ} (hV : IsProjVarF (J.map (PointVertical.red (ι := ι) p)) n) :
    Algebra.trdeg (ZMod p) (IntermediateField.adjoin (ZMod p) (Set.range y)) = ((n + Fintype.card K : ℕ) : Cardinal) := by
  have h := hE K ι (ZMod p) L y
  rw [ker_aeval_F p y hp hJ, hV.2] at h
  have h' : (Algebra.trdeg (ZMod p) (IntermediateField.adjoin (ZMod p) (Set.range y))).toENat =
      ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h.symm
  exact Cardinal.toENat_eq_natCast.mp h'

end FibreTranscendence

open FibreTranscendence in

theorem FibreTranscendenceDegreeAlt.proof (hE : EvalKerKrullDim.Statement) : FibreTranscendenceDegreeAlt.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' n hv hp hW hV G'
  classical
  have hpI : ((p : ℕ) : MRing ι) ∈ imageZ v W' := by
    show rename v ((p : ℕ) : MRing ι) ∈ W'
    simpa using hp
  have hΦp : ((p : ℕ) : G'.Φ) = 0 := by
    have h := hpI
    rw [← G'.ker_x, RingHom.mem_ker] at h
    simpa using h
  have hΦ'p : ((p : ℕ) : G'.Φ') = 0 := by
    have h := hp
    rw [← G'.genericFibre_ker_target, RingHom.mem_ker] at h
    simpa using h
  have : CharP G'.Φ p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hΦp
  have : CharP G'.Φ' p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hΦ'p
  let _ : Algebra (ZMod p) G'.Φ := ZMod.algebra _ p
  let _ : Algebra (ZMod p) G'.Φ' := ZMod.algebra _ p
  have : IsScalarTower (ZMod p) G'.Φ G'.Φ' := IsScalarTower.of_algebraMap_eq fun a =>
    DFunLike.congr_fun (Subsingleton.elim (algebraMap (ZMod p) G'.Φ')
      ((algebraMap G'.Φ G'.Φ').comp (algebraMap (ZMod p) G'.Φ))) a

  have hx := trdeg_adjoin hE p G'.x hpI G'.ker_x
    (by rw [← PointVertical.imageVar_red p v hp]; exact hV)
  have htop : IntermediateField.adjoin (ZMod p) (Set.range G'.x) = ⊤ := by
    refine eq_top_iff.2 fun c _ => ?_
    obtain ⟨f, g, -, rfl⟩ := G'.gen c
    exact div_mem (aeval_mem_adjoin p _ f) (aeval_mem_adjoin p _ g)
  have hΦ : Algebra.trdeg (ZMod p) G'.Φ = ((n + Fintype.card K : ℕ) : Cardinal) := by
    rw [← hx, htop, IntermediateField.topEquiv.trdeg_eq]

  set E := IntermediateField.adjoin G'.Φ
    (Set.range fun q : (Σ k : FibreBlock κ, ι' k.1) => G'.x' ⟨q.1.1, q.2⟩) with hEdef
  have hEeq : E.restrictScalars (ZMod p) = IntermediateField.adjoin (ZMod p) (Set.range G'.x') := by
    refine le_antisymm (fun c hc => ?_) (IntermediateField.adjoin_le_iff.2 ?_)
    · have hle : E.toSubfield ≤ (IntermediateField.adjoin (ZMod p) (Set.range G'.x')).toSubfield := by
        rw [hEdef, IntermediateField.adjoin_toSubfield]
        refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
        · rintro _ ⟨c, rfl⟩
          obtain ⟨f, g, -, rfl⟩ := G'.gen c
          have key : ∀ f : MRing ι, algebraMap G'.Φ G'.Φ' (aeval G'.x f) = aeval G'.x' (rename v f) := by
            intro f
            induction f using MvPolynomial.induction_on with
            | C a => simp
            | add f g hf hg => simp only [map_add, hf, hg]
            | mul_X f i hf => simp only [map_mul, hf, aeval_X, rename_X, G'.compat]
          rw [map_div₀, key, key]
          exact div_mem (aeval_mem_adjoin p _ _) (aeval_mem_adjoin p _ _)
        · rintro _ ⟨q, rfl⟩
          exact IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩
      exact hle hc
    · rintro _ ⟨q, rfl⟩
      show G'.x' q ∈ E
      by_cases hq : q.1 ∈ Set.range κ
      · obtain ⟨q0, rfl⟩ := hv.2.2.2 q hq
        rw [G'.compat]
        exact E.algebraMap_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨q.1, hq⟩, q.2⟩, rfl⟩
  have hEt : Algebra.trdeg (ZMod p) E = ((n + Fintype.card K' : ℕ) : Cardinal) := by
    rw [← trdeg_adjoin hE p G'.x' hp G'.genericFibre_ker_target hW, ← hEeq]
    rfl

  have hadd := trdeg_add_eq (ZMod p) G'.Φ (A := E)
  rw [hΦ, hEt] at hadd
  have hc : Fintype.card (FibreBlock κ) + Fintype.card K = Fintype.card K' := by
    simp only [← Nat.card_eq_fintype_card]
    have h1 := Set.ncard_add_ncard_compl (Set.range κ)
    rw [Set.ncard_range_of_injective hv.1, add_comm] at h1
    exact h1
  have hlt : Algebra.trdeg G'.Φ E < Cardinal.aleph0 := by
    refine lt_of_le_of_lt (le_add_self.trans_eq hadd) Cardinal.natCast_lt_aleph0
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 hlt
  rw [hm] at hadd ⊢
  have : n + Fintype.card K + m = n + Fintype.card K' := by exact_mod_cast hadd
  exact_mod_cast (by omega : m = Fintype.card (FibreBlock κ))

end GroundTheory.Heights₂.Heights.Inter
