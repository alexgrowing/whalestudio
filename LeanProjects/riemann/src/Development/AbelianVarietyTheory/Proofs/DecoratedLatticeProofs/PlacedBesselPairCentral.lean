import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFrameHermitianIdeal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselTranslateVector
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalTraceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstIsotropicVectorCoordinatesNeZeroStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponen
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReductionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesMemCompletedHermitianLaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLattiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdemAtUniqueOrth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramEqOfInst

noncomputable section

set_option maxHeartbeats 1600000

namespace GlobalTheory.LevelLine

section Gen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat ValuativeRel
open GlobalTheory.LocMod (ofSplit MovedTo)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Small (e x : AE D) : Prop :=
  finPart D (e * x) ∈ intAE D ∧ ¬ ∃ y, finPart D (e * y) ∈ intAE D ∧ e * (x * y) = e

def Cond (e : AE D) (n : ℕ) (a : AE D) : Prop :=
  Small e a ∧ ∀ x, Small e x → finPart D (e * (cA D a * x ^ n)) ∈ intAE D

theorem int_pr (q : SplitPt D k) (a : AE D) : finPart D (q.e * a) ∈ intAE D ↔ valuation k (q.pr a) ≤ 1 := by
  rw [← q.sec_pr, ← q.int_iff, Valuation.mem_integer_iff]

theorem small_iff (q : SplitPt D k) (x : AE D) : Small q.e x ↔ valuation k (q.pr x) < 1 := by
  have he : ∀ z : AE D, q.e * z = q.e ↔ q.pr z = 1 := fun z => by
    rw [← q.sec_pr, ← sec_one]
    exact ⟨fun h => by simpa only [q.pr_sec] using congrArg q.pr h, fun h => by rw [h]⟩
  simp only [Small, int_pr, he]
  simp only [RingHom.map_mul]
  constructor
  · rintro ⟨h1, h2⟩
    refine lt_of_le_of_ne h1 fun h => h2 ⟨q.sec (q.pr x)⁻¹, ?_, ?_⟩
    · rw [q.pr_sec, map_inv₀, h, inv_one]
    · rw [q.pr_sec]
      refine mul_inv_cancel₀ fun h0 => ?_
      rw [h0, map_zero] at h
      exact zero_ne_one h
  · refine fun h => ⟨h.le, ?_⟩
    rintro ⟨y, h1, h2⟩
    have h3 := congrArg (valuation k) h2
    rw [map_mul, map_one] at h3
    exact (mul_lt_one_of_lt_of_le h h1).ne h3

theorem cond_iff (q : SplitPt D k) {ϖ : k} (hϖ : ∀ x : k, valuation k x < 1 ↔ valuation k x ≤ valuation k ϖ) (n : ℕ) (a : AE D) :
    Cond q.e n a ↔ valuation k (q.pr a) ≤ valuation k ϖ ∧ valuation k (q.pr (cA D a)) * valuation k ϖ ^ n ≤ 1 := by
  simp only [Cond, small_iff, int_pr, hϖ]
  simp only [RingHom.map_mul, RingHom.map_pow, Valuation.map_mul, Valuation.map_pow]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h x hx => le_trans ?_ h⟩
  · simpa only [q.pr_sec] using h (q.sec ϖ) (by rw [q.pr_sec])
  · gcongr

theorem mulVec_sec (q : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → k) :
    M *ᵥ (fun i => q.sec (y i)) = fun i => q.sec ((M.map q.pr *ᵥ y) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, sec_mul_right, mul_comm]

variable {Y : Type} [Fintype Y] [DecidableEq Y]

theorem int_moved (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D) (Λ : Lat V)
    (β : GL (Fin V.rank) (Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β Λ) (t : GA D V) (G : GlobalTheory.LocMod.Frame k V.rank Y)
    (σ : Fin V.rank ≃ Y) (hM : MovedTo (ofSplit q) V t β (G.β.submatrix id σ)) (y : Y → k) :
    (fun i => q.sec (((mt V t⁻¹).map q.pr *ᵥ (G.β *ᵥ y)) i)) ∈ latV V Λ (· = q.v) ↔ ∀ i, y i ∈ 𝒪[k] := by
  obtain ⟨π, h1, -, h2, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D k q PP hq
  have hl : ∀ y : Fin V.rank → k, (fun i => q.sec (y i)) ∈ latV V Λ (· = q.v) ↔
      ∀ i, (((Matrix.GeneralLinearGroup.map π β)⁻¹).val *ᵥ y) i ∈ 𝒪[k] := fun y => by
    have h3 : (fun i => q.sec (y i)) ∈ latV V Λ (· = q.v) ↔
        (fun i => toEAf D (q.sec (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
      ⟨GlobalTheory.T.latticeCompletionAtPlaces_mem_completedHermitianLattice D V Λ _ _, GlobalTheory.T.mem_latticeCompletionAtPlaces_of_finPart_mem_hatLattice D V Λ _ _ fun i => sec_mem_idAt q _⟩
    rw [h3, hβ]
    refine forall_congr' fun i => ?_
    have h4 : ∀ j, (1 - toEAf D q.e) * toEAf D (q.sec (y j)) = 0 := fun j => by
      rw [sub_mul, one_mul, ← map_mul, e_mul_sec, sub_self]
    rw [h2, ← map_inv]
    simp only [mulVec, dotProduct, Finset.mul_sum, mul_left_comm (1 - toEAf D q.e), h4, mul_zero, Finset.sum_const_zero, zero_mem,
      true_and, map_sum, map_mul, h1, q.pr_sec]
    rfl
  have hs : Function.Surjective (toEAf D) := by
    refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
    exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id
  choose f hf using hs
  have e : (β.val.map f).map (toEAf D) = β.val := by ext i j; exact hf _
  have hB : (β.val.map f).map q.pr = (Matrix.GeneralLinearGroup.map π β).val := by
    ext i j
    change q.pr (f (β.val i j)) = π (β.val i j)
    rw [← h1, hf]
  have h5 : (mt V t).map q.pr * (β.val.map f).map q.pr = G.β.submatrix id σ := by
    rw [← Matrix.map_mul]; exact hM _ e
  have h6 : (mt V t⁻¹).map q.pr * (mt V t).map q.pr = 1 := by
    rw [← Matrix.map_mul, ← GlobalTheory.MixModel.mt_mul, inv_mul_cancel, GlobalTheory.MixModel.mt_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have h7 : G.β *ᵥ y = G.β.submatrix id σ *ᵥ (y ∘ σ) := by
    rw [Matrix.submatrix_mulVec_equiv, Function.comp_id, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  rw [hl, h7, ← h5, hB, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mul_assoc ((mt V t⁻¹).map q.pr), h6,
    Matrix.one_mul, Units.inv_mul, Matrix.one_mulVec]
  exact ⟨fun h i => by simpa using h (σ.symm i), fun h i => h _⟩

theorem single_int (m₁ : Y) (x : k) : (∀ i, (Pi.single m₁ x : Y → k) i ∈ 𝒪[k]) ↔ x ∈ 𝒪[k] := by
  refine ⟨fun h => by simpa using h m₁, fun h i => ?_⟩
  by_cases hi : i = m₁
  · subst hi; rwa [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hi]; exact zero_mem _

theorem line_moved (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D) (Λ : Lat V)
    (β : GL (Fin V.rank) (Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β Λ) (hΛ : IsSelfDualC V Λ) (t : GA D V)
    (G : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (hM : MovedTo (ofSplit q) V t β (G.β.submatrix id σ))
    (u : Fin V.rank → D.host.E) (m₀ m₁ : Y) (κ κ' : k) (hκ : κ ≠ 0) (hu : ∀ r, G.β r m₀ = κ * q.pr (incA D (u r)))
    (hp : ∀ m, ∑ r, G.β r m * q.pr (incA D (star ((V.gram *ᵥ u) r))) = if m = m₁ then κ' else 0)
    (a : AE D) (ha : a ∈ idAt D (· = q.v)) :
    mt V t⁻¹ *ᵥ (fun r => a * incA D (u r)) ∈ latV V Λ (· = q.v) ↔ q.pr a / κ ∈ 𝒪[k] ∧ q.pr (cA D a) * κ' ∈ 𝒪[k] := by
  have hI := int_moved q hq V Λ β hβ t G σ hM
  have hae : a = q.sec (q.pr a) + cA D (q.sec (q.pr (cA D a))) := by
    rw [q.sec_pr, q.sec_pr, RingHom.map_mul, cA_cA, ← add_mul, (idem_iff q a).1 ha]
  have hy : (fun r => a * incA D (u r)) = (fun r => q.sec (q.pr a * q.pr (incA D (u r)))) +
      (fun r => cA D (q.sec (q.pr (cA D a) * q.pr (incA D (star (u r)))))) := by
    funext r
    rw [Pi.add_apply]
    conv_lhs => rw [hae]
    rw [add_mul, sec_mul_right]
    congr 1
    have e : incA D (u r) = cA D (incA D (star (u r))) := by rw [cA_incA, star_star]
    rw [e, ← RingHom.map_mul, sec_mul_right]
  rw [hy, Matrix.mulVec_add, mulVec_sec, mt_csec]
  refine (decomp hΛ _ _).trans (and_congr ?_ ?_)
  · have e : (fun r => q.pr a * q.pr (incA D (u r))) = G.β *ᵥ Pi.single m₀ (q.pr a / κ) := by
      funext r
      rw [Matrix.mulVec_single]
      change _ = G.β r m₀ * (q.pr a / κ)
      rw [hu]
      field_simp
    rw [e, hI, single_int]
  generalize q.pr (cA D a) = A
  have h6 : (mt V t⁻¹).map q.pr * (mt V t).map q.pr = 1 := by
    rw [← Matrix.map_mul, ← GlobalTheory.MixModel.mt_mul, inv_mul_cancel, GlobalTheory.MixModel.mt_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have ht : ∀ i, q.pr (incA D (star ((V.gram *ᵥ u) i))) =
      ∑ j, q.pr (cA D (incA D (V.gram i j))) * q.pr (incA D (star (u j))) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', map_sum, map_mul, cA_incA]
  have hsum : ∀ y : Y → k, ∑ i, ∑ j, ((mt V t⁻¹).map q.pr *ᵥ (G.β *ᵥ y)) i * q.pr (cA D (incA D (V.gram i j))) *
      (((mt V t⁻¹).map fun a => q.pr (cA D a)) *ᵥ fun r => A * q.pr (incA D (star (u r)))) j = y m₁ * (A * κ') := by
    intro y
    rw [pairing_inv]
    have h1 : ∑ i, ∑ j, (G.β *ᵥ y) i * q.pr (cA D (incA D (V.gram i j))) * (A * q.pr (incA D (star (u j)))) =
        A * ∑ m, y m * ∑ r, G.β r m * q.pr (incA D (star ((V.gram *ᵥ u) r))) := by
      have h2 : ∀ i, ∑ j, (G.β *ᵥ y) i * q.pr (cA D (incA D (V.gram i j))) * (A * q.pr (incA D (star (u j)))) =
          A * ((G.β *ᵥ y) i * q.pr (incA D (star ((V.gram *ᵥ u) i)))) := fun i => by
        rw [ht i, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      simp only [h2]
      generalize (fun r => q.pr (incA D (star ((V.gram *ᵥ u) r)))) = P at *
      simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_comm.trans (Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun r _ => ?_)
      ring
    rw [h1]
    simp only [hp, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [csec_mem_iff hΛ]
  constructor
  · intro h
    have h2 := h _ ((hI (Pi.single m₁ 1)).2 ((single_int m₁ 1).2 (one_mem _)))
    rwa [hsum, Pi.single_eq_same, one_mul] at h2
  · intro hA x hx
    have e : x = (mt V t⁻¹).map q.pr *ᵥ (G.β *ᵥ (G.γ *ᵥ ((mt V t).map q.pr *ᵥ x))) := by
      rw [Matrix.mulVec_mulVec _ G.β, G.βγ, Matrix.one_mulVec, Matrix.mulVec_mulVec, h6, Matrix.one_mulVec]
    rw [e] at hx ⊢
    rw [hsum]
    exact mul_mem ((hI _).1 hx m₁) hA

theorem line_bes (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP) {ρ : ℕ} (B : BesLev D ρ)
    (Λ : Lat B.V) (β : GL (Fin B.V.rank) (Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β Λ) (hΛ : IsSelfDualC B.V Λ) (t : GA D B.V)
    {c : ℕ} (FA : GlobalTheory.LocMod.Frame k B.A.rank Y) (F : GlobalTheory.LocMod.Frame k B.V.rank (Y ⊕ Fin c)) (s : k) (hs : s ≠ 0)
    (hF : (ofSplit q).IsBesFrame B s FA F) (bas : GL (Y ⊕ Fin c) k) (ϖ : kˣ)
    (hb : bas.val = diagonal (Sum.elim (fun _ => 1) fun j => (ϖ : k) ^ (j.val + 1))) (σ : Fin B.V.rank ≃ Y ⊕ Fin c)
    (hM : MovedTo (ofSplit q) B.V t β ((F.β * bas.val).submatrix id σ)) (i : Fin ρ) (hi : i.val = 0)
    (a : AE D) (ha : a ∈ idAt D (· = q.v)) :
    mt B.V t⁻¹ *ᵥ (fun r => a * incA D (B.d.e r i)) ∈ latV B.V Λ (· = q.v) ↔
      q.pr a / (s * (ofSplit q).xi ^ ρ * ϖ) ∈ 𝒪[k] ∧
      q.pr (cA D a) * (s * (-(ofSplit q).hz B / (ofSplit q).xi) * (-1 / (ofSplit q).xi) ^ (ρ - 1) * (ϖ : k) ^ (2 * ρ + 1)) ∈ 𝒪[k] := by
  obtain ⟨hc, h1, h2, h3, h4⟩ := hF
  subst hc
  have hρ := i.2
  let G : GlobalTheory.LocMod.Frame k B.V.rank (Y ⊕ Fin (2 * ρ + 1)) := ⟨F.β * bas.val, (bas⁻¹).val * F.γ,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc bas.val, Units.mul_inv, Matrix.one_mul, F.βγ],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, Units.inv_mul]⟩
  have hG : ∀ r m, G.β r m = F.β r m * (Sum.elim (fun _ => 1) fun j : Fin (2 * ρ + 1) => (ϖ : k) ^ (j.val + 1)) m := fun r m => by
    change (F.β * bas.val) r m = _
    rw [hb, Matrix.mul_diagonal]
  let π : D.host.E →+* k := q.pr.comp (incA D)
  have hπ : ∀ x, (ofSplit q).pr x = π x := fun _ => rfl
  have hπ' : ∀ x, q.pr (incA D x) = π x := fun _ => rfl
  have key : ∀ {m : Type} (M : Matrix (Fin B.V.rank) m D.host.E) (j : m),
      ∑ r, π (M r j) * π (star ((B.V.gram *ᵥ fun r => B.d.e r i) r)) = π (star ((Mᴴ * B.V.gram * B.d.e) j i)) := by
    intro m M j
    rw [Matrix.mul_assoc, Matrix.mul_apply, star_sum, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [star_mul', Matrix.conjTranspose_apply, star_star, map_mul]
    rfl
  refine line_moved q hq B.V Λ β hβ hΛ t G σ hM (fun r => B.d.e r i) (Sum.inr ⟨0, by omega⟩) (Sum.inr ⟨2 * ρ, by omega⟩) _ _
    (mul_ne_zero (mul_ne_zero hs (pow_ne_zero _ (GlobalTheory.LocMod.Witness.xi_ne _))) ϖ.ne_zero) (fun r => ?_) (fun m => ?_) a ha
  · rw [hG, h2 i _ hi.symm, hi]
    simp only [Sum.elim_inr, hπ, hπ', Nat.sub_zero, zero_add, pow_one]
    ring
  simp only [hG, hπ', mul_right_comm _ (Sum.elim _ _ m), ← Finset.sum_mul]
  generalize hP : (fun r => π (star ((B.V.gram *ᵥ fun r => B.d.e r i) r))) = P
  simp only [congrFun hP] at key ⊢
  rcases m with m | j
  · have h5 : ∀ l, ∑ r, π ((B.d.i₀ * B.o.iA) r l) * P r = 0 := fun l => by
      rw [key, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc B.d.i₀ᴴ, B.d.i₀e, Matrix.mul_zero,
        Matrix.zero_apply, star_zero, map_zero]
    have h6 : ∑ r, F.β r (Sum.inl m) * P r = ∑ l, FA.β l m * ∑ r, π ((B.d.i₀ * B.o.iA) r l) * P r := by
      generalize B.d.i₀ * B.o.iA = M at h1
      simp only [h1, Matrix.mul_apply, Matrix.map_apply, hπ, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun r _ => ?_)
      ring
    rw [h6, if_neg (by simp)]
    simp only [h5, mul_zero, Finset.sum_const_zero, zero_mul]
  have hj := j.2
  rcases lt_trichotomy j.val ρ with h | h | h
  · rw [if_neg (by simp only [Sum.inr.injEq, Fin.ext_iff]; omega)]
    simp only [h2 ⟨j.val, h⟩ j rfl, hπ, mul_assoc, ← Finset.mul_sum, key]
    rw [B.d.ee, Matrix.zero_apply, star_zero, map_zero]
    simp
  · rw [if_neg (by simp only [Sum.inr.injEq, Fin.ext_iff]; omega)]
    have h5 := key (B.d.i₀ * replicateCol Unit (vecB B.o B.ζ)) ()
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc B.d.i₀ᴴ, B.d.i₀e, Matrix.mul_zero,
        Matrix.zero_apply, star_zero, map_zero] at h5
    have h6 : ∑ r, F.β r (Sum.inr j) * P r = s * ∑ r, π ((B.d.i₀ * replicateCol Unit (vecB B.o B.ζ)) r ()) * P r := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [h3 j h, mul_assoc]
      rfl
    rw [h6, h5, mul_zero, zero_mul]
  · have h6 : ∑ r, F.β r (Sum.inr j) * P r = s * (-(ofSplit q).hz B / (ofSplit q).xi) * (-1 / (ofSplit q).xi) ^ (ρ - 1 - (2 * ρ - j.val)) *
        ∑ r, π (B.d.e' r ⟨2 * ρ - j.val, by omega⟩) * P r := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [h4 ⟨2 * ρ - j.val, by omega⟩ j (by simp only; omega), mul_assoc]
      rfl
    rw [h6, key, B.d.e'e]
    by_cases e : j.val = 2 * ρ
    · rw [if_pos (by simp only [Sum.inr.injEq, Fin.ext_iff]; omega), Matrix.one_apply, if_pos (by simp only [Fin.ext_iff]; omega)]
      simp [e]
    · rw [if_neg (by simp only [Sum.inr.injEq, Fin.ext_iff]; omega), Matrix.one_apply, if_neg (by simp only [Fin.ext_iff]; omega)]
      simp

theorem val_nat (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP) (T : ℕ)
    (hT : (T : 𝓞 D.host.E) ∉ PP.asIdeal) : valuation k (T : k) = 1 := by
  obtain ⟨π, -, h, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D k q PP hq
  have h1 := h.int T
  have h2 := h.ker T
  rw [map_natCast] at h1
  rw [map_natCast, map_natCast] at h2
  refine le_antisymm h1 (not_lt.1 fun h3 => hT ?_)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h2.2 h3

end Gen

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Matrix
open GlobalTheory.LocMod (ofSplit)

theorem norm_vec {D : D7} {ρ : ℕ} (B : BesLev D ρ) :
    star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = star (B.d.i₀ *ᵥ vecB B.o B.ζ) ⬝ᵥ B.V.gram *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) := by
  rw [← B.o.isoB, ← B.d.iso, vecB]
  simp only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

theorem sc_even {k : Type} [Field k] (sc : ℕ → k) (x : k) (h : ∀ j, sc (j + 1 + 1) = sc j * x) (n : ℕ) :
    sc (2 * n) = sc 0 * x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, h, ih]; ring

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem sc_mul {c : Comm D} {v : VCom c} (G : GLoc v) {μ lam : D.host.E} {ζ₀ : Fin c.Lz.rank → D.host.E}
    (h1 : μ * lam = -D.host.xi0 ^ (D.R.m / 2)) (h3 : ∀ j h, v.τ j h *ᵥ ζ₀ = lam • (c.bes j 0 h).ζ)
    (hl : G.z₀ = fun r => (ofSplit G.q).pr (ζ₀ r)) (h₀ : 0 + 2 * D.R.rS + 2 = D.R.m) : G.sc 0 * G.q.pr (incA D μ) = 1 := by
  have hs := G.hs
  have hh : G.s + 2 * 0 + 2 = D.R.m := by omega
  have h4 := G.tau hh
  rw [hl] at h4
  let π : D.host.E →+* G.k := (ofSplit G.q).π.comp (incA D)
  have hπ : ∀ a, (ofSplit G.q).pr a = π a := fun _ => rfl
  have hζ : ∃ a, (c.bes G.s 0 hh).ζ a ≠ 0 := by
    by_contra hc
    push Not at hc
    apply (c.bes G.s 0 hh).line.2
    rw [show (c.bes G.s 0 hh).ζ = 0 from funext hc]; simp
  obtain ⟨a, ha⟩ := hζ
  have h5 := congrFun h4 a
  have h6 : (((v.τ G.s hh).map (ofSplit G.q).pr) *ᵥ fun r => (ofSplit G.q).pr (ζ₀ r)) a =
      π ((v.τ G.s hh *ᵥ ζ₀) a) := (RingHom.map_mulVec π _ _ a).symm
  rw [h6, h3] at h5
  have h7 : π lam = -((ofSplit G.q).xi * G.sc G.s) := by
    have hz : π ((c.bes G.s 0 hh).ζ a) ≠ 0 := by simpa using ha
    apply mul_right_cancel₀ hz
    simpa [hπ] using h5
  have hx : (ofSplit G.q).xi = π D.host.xi0 := rfl
  have hm : G.s = 2 * D.R.rS := by omega
  have hm2 : D.R.m / 2 = D.R.rS + 1 := by omega
  have h8 := congrArg π h1
  rw [map_mul, h7, hm, sc_even _ _ G.sc_step, map_neg, map_pow, hm2, hx] at h8
  have hx0 : π D.host.xi0 ≠ 0 := hx ▸ GlobalTheory.LocMod.Witness.xi_ne _
  change G.sc 0 * π μ = 1
  apply mul_right_cancel₀ (pow_ne_zero (D.R.rS + 1) hx0)
  linear_combination -h8

theorem single (W : RealPack ex) (hW : PkHyp W) (r : Fin D.R.rS) (hr : r.1 = 0) {u : D.what₂.Word} (f : FamCh W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (hP : Placed f B) (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : PP ∈ (pk W).Pg) :
    ∃ e, Formalism.L2.NTheta.IsIdemAt e PP ∧ ∀ c ∈ idAt D (· = PP.under (𝓞 D.host.F)),
      (mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ *ᵥ
        (fun i => c * incA D (W.S.X.ιE (W.S.X.eR r (Fin.cast (rank_eq W.S.X W.Q.instEq) i)))) ∈
          latV (D.sp.Y 0) ((pk W).ΛY 0) (· = PP.under (𝓞 D.host.F)) ↔
        Cond e (2 * D.R.rS + 1) (c * incA D ((W.S.X.B.g : D.host.E) ^ D.R.rS)⁻¹)) := by
  obtain ⟨k, i1, i2, i3, i4, ι, v, o, n, G, pl, hc, hv, ht, -, -, hR, hb⟩ := hP
  obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
  obtain ⟨hq, hqv⟩ := hR.idem i
  rw [hi] at hq hqv
  change (G i).q.v = PP.under _ at hqv
  change Formalism.L2.NTheta.IsIdemAt _ PP at hq
  refine ⟨_, hq, fun c hcv => ?_⟩
  rw [← hqv] at hcv ⊢
  obtain ⟨μ, lam, n1, n2, n3⟩ := hb.norm
  have hξ : -D.host.xi0 ^ (D.R.m / 2) ≠ 0 := neg_ne_zero.2 (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hμ : μ ≠ 0 := left_ne_zero_of_mul (n1 ▸ hξ)
  have h₀ : 0 + 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.rS
    omega
  have hg : ((W.S.X.B.g : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.L2.SG.Pf.modulus_g_ne_zero W.S.X)
  obtain ⟨s, hs, he⟩ := GlobalTheory.LineIdeal.first_vec (F0 W u) (W.S.tr u) hW.bot.idE hc.std B hμ n2 r hr
  have hd : B.d.e = (f.c.bes 0 D.R.rS h₀).d.e := eq_of_heq (Sigma.mk.inj (congrArg
    (fun Z : BesLev D D.R.rS => (⟨Z.V.rank, Z.d.e⟩ : Σ n, Matrix (Fin n) (Fin D.R.rS) D.host.E)) (hb.lev h₀))).2
  have hsc := sc_mul (G i) n1 n3 (hb.last i) h₀
  have hT : ((D.mem u).A.T : 𝓞 D.host.E) ∉ PP.asIdeal := fun hT => by
    refine Finset.disjoint_left.1 hv.disj ((ht.gP _).2 ⟨PP, hPP, rfl⟩) ((ht.tP _).2 ?_)
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
    rwa [map_natCast]
  have hTv := val_nat (G i).q hq _ hT
  have hz : star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = star μ * (μ * -((D.mem u).A.T : D.host.E)) := by
    have e : B.d.i₀ *ᵥ vecB B.o B.ζ = μ • GlobalTheory.Core.SBesEx.cY W.S.X W.Q.instEq (W.S.X.zu u) := funext n2
    refine (norm_vec B.lev).trans ?_
    change star (B.d.i₀ *ᵥ vecB B.o B.ζ) ⬝ᵥ (D.sp.Y 0).gram *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = _
    rw [e, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, GlobalTheory.Core.SBesEx.cY_isom D _ _ hW.bot.idE, W.S.X.zu_norm]
    rfl
  have hzu := (G i).hz_unit 0 _ h₀
  have hzu' := hzu
  rw [← hb.lev h₀] at hzu'
  change valuation _ ((G i).q.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ))) = 1 at hzu'
  have hμ1 : valuation _ ((G i).q.pr (incA D μ)) = 1 := by
    have := congrArg (valuation _) hsc
    rwa [map_mul, (G i).sc_unit, one_mul, map_one] at this
  have hμ2 : valuation _ ((G i).q.pr (incA D (star μ))) = 1 := by
    simp only [hz, RingHom.map_mul, RingHom.map_neg, map_natCast, Valuation.map_mul, Valuation.map_neg, hμ1, hTv, mul_one] at hzu'
    exact hzu'
  have hxi : valuation _ (ofSplit (G i).q).xi = 1 := by
    have := congrArg (valuation _) ((G i).sc_step 0)
    rw [map_mul, (G i).sc_unit, (G i).sc_unit, one_mul] at this
    exact this.symm
  obtain ⟨σ, -, hM⟩ := hR.frame i 0 ((G i).s + 1) (Nat.zero_add _)
  obtain ⟨hsd, hfr⟩ := GlobalTheory.T.self_dual_lattice_frame_chain W hW 0 (by omega)
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> simp
  have H := line_bes (G i).q hq (f.c.B 0 _ h₀) ((pk W).ΛY 0) ((pk W).βY 0) hfr hsd (f.g.b 0) _ _ _
    (fun h0 => by simpa [h0] using (G i).sc_unit 0) ((G i).bes 0 _ h₀ _ (Nat.zero_add _)) _ (G i).S.ϖ
    (Matrix.fromBlocks_diagonal _ _) (σ.symm.trans (GlobalTheory.StepData.stdOrd _ _ 0 _ (Nat.zero_add _))) hM r hr
    (incA D (s * μ)⁻¹ * (c * incA D ((W.S.X.B.g : D.host.E) ^ D.R.rS)⁻¹))
    (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hcv))
  have e : (fun i => c * incA D (W.S.X.ιE (W.S.X.eR r (Fin.cast (rank_eq W.S.X W.Q.instEq) i)))) =
      fun l => incA D (s * μ)⁻¹ * (c * incA D ((W.S.X.B.g : D.host.E) ^ D.R.rS)⁻¹) * incA D (B.d.e l r) := by
    funext l
    rw [he, mul_comm (incA D _), mul_assoc, mul_assoc, ← RingHom.map_mul, ← RingHom.map_mul]
    congr 2
    field_simp
  rw [e, hd]
  refine H.trans ?_
  rw [cond_iff (G i).q (G i).S.unif]
  generalize c * incA D ((W.S.X.B.g : D.host.E) ^ D.R.rS)⁻¹ = a
  have hs1 : valuation _ ((G i).q.pr (incA D (s * μ)⁻¹)) = 1 := by
    rw [← RingHom.comp_apply, map_inv₀, map_inv₀, RingHom.comp_apply]
    rcases hs with rfl | rfl <;> simp [hμ1]
  have hs2 : valuation _ ((G i).q.pr (incA D (star (s * μ)⁻¹))) = 1 := by
    rw [star_inv₀, ← RingHom.comp_apply, map_inv₀, map_inv₀, RingHom.comp_apply]
    rcases hs with rfl | rfl <;> simp [hμ2]
  have hϖ : 0 < valuation _ ((G i).S.ϖ : (G i).k) := by simp [zero_lt_iff]
  simp only [Valuation.mem_integer_iff, RingHom.map_mul, GlobalTheory.FinPl.FrameLat.cA_incA, Valuation.map_mul, map_div₀, Valuation.map_neg,
    Valuation.map_pow, Valuation.map_one, hs1, hs2, hxi, hzu, (G i).sc_unit, one_mul, one_pow, div_one, div_le_one₀ hϖ]

theorem line_indep : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ (hr : 1 ≤ D.R.rS) u u' (f : FamCh W u) (f' : FamCh W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), Placed f B → Placed f' B' → ∀ a₀ a a₀' a', IsAt f B a₀ a → IsAt f' B' a₀' a' → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∃ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) = v) → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((pk W).ΛY 0) (· = v) ↔ Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f'.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((pk W).ΛY 0) (· = v)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' _ _ v ⟨PP, hPP, hv⟩ c hc
  subst hv
  obtain ⟨e, he, h⟩ := single W hW ⟨0, hr⟩ rfl f B hP PP hPP
  obtain ⟨e', he', h'⟩ := single W hW ⟨0, hr⟩ rfl f' B' hP' PP hPP
  obtain rfl := (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D e e' PP PP he he').1 rfl
  exact (h c hc).trans (h' c hc).symm

end GlobalTheory.LevelLine

end
