import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitQuotientTopology.IsClosedRStab
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueLayeredStrictFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalDomainMeasureEqStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentBlockUpperUnitriangularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFlagDepthAtLeastOfFreeEntriesVanishStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentBlockEntriesMulOfHasFlagDepthAtLeastStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReAntidiagonalEntryEqZeroOfFlagDepthStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentModelProductActionMeasurePreservingStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureUnipotentTuplesFreeEntryBlocksStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentRadicalFormsUnitSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentMemModelUnipotentAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentModelActionIsActionAndFaithfulStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentEntryMemInverseDifferentLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCornerEntryMemIdealLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentMiddleRowMemHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentAntidiagonalMemSkewLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowEmbeddingMemIntegralOrthogonalGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowIsometryEntriesInModelCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PiUnipotentModelMeasurableFullMeasureStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftEntryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LiftRowMiddleSpaceIntegralPointStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftCornerStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftAntidiagonalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeInverseDifferentPowDivLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeInverseDifferentPowMulLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SkewLatticeInverseDifferentPowCovolumeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeMiddleLatticeHomLatticeIdealStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalBlockCovolumesProdStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem cM_one (k r : ℕ) (β : Bk r) : cM k r β (Matrix.of.symm 1) = 0 := by
  rcases β with p | a | p | a
  · show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r p.1.1) (eI k r p.1.2) = 0
    exact Matrix.one_apply_ne (fun h => p.2.ne (by simpa [eI, Fin.ext_iff] using h))
  · funext j
    show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r a) (wI k r j) = 0
    refine Matrix.one_apply_ne (fun h => ?_)
    have h' := congrArg Fin.val h
    simp only [eI, wI] at h'
    have := a.isLt
    omega
  · show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r p.1.1) (esI k r p.1.2) = 0
    refine Matrix.one_apply_ne (fun h => ?_)
    have h' := congrArg Fin.val h
    simp only [eI, esI] at h'
    have := p.1.1.isLt
    have := p.1.2.isLt
    omega
  · show ((1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r a) (esI k r a)).im = 0
    rw [Matrix.one_apply]
    split_ifs <;> simp

theorem pos_le (k r : ℕ) (i : Fin (2 * r + k + 1)) : pos k r i ≤ 2 * r := by
  have := i.isLt
  unfold pos
  split_ifs <;> omega

theorem eq_one_of_dep {k r : ℕ} {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (h : Dep k r (2 * r + 1) (x - 1)) : x = 1 := by
  refine sub_eq_zero.1 (Matrix.ext fun i j => ?_)
  exact h i j (by have := pos_le k r j; omega)

theorem countable_units (E : Type) [Field E] [NumberField E] (n : ℕ) :
    Countable (Matrix (Fin n) (Fin n) E)ˣ := by
  haveI : Countable E :=
    Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Function.Injective.countable (f := fun u : (Matrix (Fin n) (Fin n) E)ˣ => (u : Matrix (Fin n) (Fin n) E))
    Units.val_injective

theorem ofReal_five (t u h c g : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hh : 0 ≤ h) (hc : 0 ≤ c) (hg : 0 ≤ g) :
    ENNReal.ofReal (t * (u * h * c * g)) =
      ENNReal.ofReal t * (ENNReal.ofReal u * ENNReal.ofReal h * ENNReal.ofReal c * ENNReal.ofReal g) := by
  rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul hu]

abbrev MM (k r : ℕ) (E : Type) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E

theorem covolume_N : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → IsHermND σ J → GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ → IsFrame (σ : E →+* E) J (algebraMap F E T) P → IsDual (σ : E →+* E) J P f → tupLat (id1 E r) (sideM P f) ≤ Λ → IsModelAt J A → (∀ a, 0 < s a) → Adapted A P f s → AllSome (IsDomN (σ : E →+* E) J Λ P A) fun 𝓓 => Measure.pi (fun _ : InfinitePlace E => haarLie (Nset k r) 1) 𝓓 = ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (-(((k : ℝ) + 1) * (r : ℝ) ^ 2) - 4 * ((r : ℝ) ^ 3 - r) / 3 - 3 * (r : ℝ) / 2) * (∏ a : Fin r, s a ^ (4 * (r - (a : ℕ)) + 2 * k)) ^ Fintype.card (InfinitePlace E)) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hV : IsVolData σ J Λ P f T A s := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  obtain ⟨⟨G, hG⟩, hGu⟩ := GlobalTheory.T.integralUnipotentRadical_forms_unit_subgroup F E σ k r J Λ P f T A s hV
  obtain ⟨ha1, ha2, ha3⟩ := GlobalTheory.T.unipotentModelAction_isAction_and_faithful F E σ k r J Λ P f T A s hV
  have hmem := GlobalTheory.T.integralUnipotent_mem_modelUnipotentAtPlace F E σ k r J Λ P f T A s hV
  choose DU hDUm hDUf hDUv using fun p : UTr r =>
    GlobalTheory.T.covolume_inverseDifferentPow_div_lattice F E σ h1 h2 (r - p.1.1.val) (r - p.1.2.val) (s p.1.1 / s p.1.2) (div_pos (h9 _) (h9 _))
  choose DC hDCm hDCf hDCv using fun p : UTr r =>
    GlobalTheory.T.covolume_inverseDifferentPow_mul_lattice F E σ h1 h2 (r - p.1.1.val) (r - p.1.2.val) (s p.1.1 * s p.1.2) (mul_pos (h9 _) (h9 _))
  choose DH hDHm hDHf hDHv using GlobalTheory.T.covolume_middleLattice_homLattice_ideal F E σ k r J Λ P f T A s hV
  choose DG hDGm hDGf hDGv using fun a : Fin r =>
    GlobalTheory.T.skewLattice_inverseDifferentPow_covolume F E σ h1 h2 (r - a.val) (s a ^ 2) (pow_pos (h9 _) 2)
  let LB := blkSet (InfinitePlace E) k r
    (fun p => (ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) : Set _))
    (fun a => homLat (σ : E →+* E) J Λ P f A (dInv E (r - a.val)) (s a))
    (fun p => (ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) : Set _))
    (fun a => (skewLat (σ : E →+* E) (dInv E (2 * (r - a.val))) (s a ^ 2) : Set _))
  let DB := blkSet (InfinitePlace E) k r DU DH DC DG
  let NN : Set (InfinitePlace E → Mt k r) := {x | ∀ w, Matrix.of (x w) ∈ Nset k r}
  let ρ : G → (InfinitePlace E → Mt k r) → (InfinitePlace E → Mt k r) :=
    fun g => actM A ((g : (MM k r E)ˣ) : MM k r E)
  let o : InfinitePlace E → Mt k r := fun _ => Matrix.of.symm 1
  let gm : G → InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    fun g => gM A ((g : (MM k r E)ˣ) : MM k r E)
  have hρo : ∀ g w, ρ g o w = Matrix.of.symm (gm g w) := fun g w => by
    show Matrix.of.symm (gm g w * 1) = Matrix.of.symm (gm g w)
    rw [mul_one]
  have hgm : ∀ g w, gm g w ∈ Nset k r := fun g => hmem _ ((hG _).1 g.2)
  have hρ1 : ∀ x, ρ 1 x = x := fun x => by
    have e : (((1 : G) : (MM k r E)ˣ) : MM k r E) = 1 := rfl
    show actM A (((1 : G) : (MM k r E)ˣ) : MM k r E) x = x
    rw [e]; exact ha1 x
  have hρm : ∀ g h x, ρ (g * h) x = ρ g (ρ h x) := fun g h x => by
    have e : (((g * h : G) : (MM k r E)ˣ) : MM k r E) = ((g : (MM k r E)ˣ) : MM k r E) * ((h : (MM k r E)ˣ) : MM k r E) := rfl
    show actM A (((g * h : G) : (MM k r E)ˣ) : MM k r E) x = _
    rw [e]; exact ha2 _ _ x
  have hρN : ∀ g, ∀ x ∈ NN, ρ g x ∈ NN := fun g x hx w =>
    PI.AmpOrbQuot.nset_mul (hgm g w) (hx w)
  have hdep : ∀ (g : G) (d : ℕ), (∀ β : Bk r, degB r β < d →
      (fun w => cM k r β (ρ g o w)) = 0) → ∀ w, Dep k r d (gm g w - 1) := fun g d hg w =>
    GlobalTheory.T.hasFlagDepthAtLeast_of_free_entries_vanish k r _ d (hgm g w) fun β hβ => by
      have := congrFun (hg β hβ) w
      rwa [hρo] at this
  have tw := GlobalTheory.T.existsUnique_layered_strictFundamentalDomain (V := fun β : Bk r => InfinitePlace E → VM k r β) ρ NN o (degB r)
    (fun β x w => cM k r β (x w)) LB DB (fun w => by simpa [o] using PI.AmpOrbQuot.nset_one) hρ1 hρm hρN
    (by
      rintro (p | a | p | a)
      · exact (ideLat _ _).zero_mem
      · exact ⟨0, ⟨fun a => by simp [form], fun c _ => by simp⟩, fun w l => by
          have e : (fun i => w.embedding ((0 : Fin (2 * r + k + 1) → E) i)) = 0 := by ext; simp
          rw [e, Matrix.mulVec_zero]
          simp [herm]
          rfl⟩
      · exact (ideLat _ _).zero_mem
      · exact (skewLat _ _ _).zero_mem)
    (by
      rintro (p | a | p | a) v
      · exact hDUf p v
      · exact hDHf a v
      · exact hDCf p v
      · exact hDGf a v)
    (fun β => funext fun w => cM_one k r β)
    (fun d g hg x hx β hβ => funext fun w => by
      have := GlobalTheory.T.unipotentBlockEntries_mul_of_hasFlagDepthAtLeast k r (gm g w) (Matrix.of (x w)) d (hdep g d hg w) (GlobalTheory.T.flagUnipotent_block_upper_unitriangular k r _ (hx w)) β hβ
      show cM k r β (ρ g x w) = cM k r β (x w) + cM k r β (ρ g o w)
      rw [hρo]
      exact this)
    (by
      intro g β hβ
      have hgN := (hG _).1 g.2
      have e : (fun w => cM k r β (ρ g o w)) = fun w => cM k r β (Matrix.of.symm (gm g w)) :=
        funext fun w => by rw [hρo]
      show (fun w => cM k r β (ρ g o w)) ∈ LB β
      rw [e]
      rcases β with p | a | p | a
      · exact GlobalTheory.T.integralUnipotent_entry_mem_inverseDifferentLattice F E σ k r J Λ P f T A s hV _ hgN p
      · exact GlobalTheory.T.integralUnipotent_middleRow_mem_homLattice F E σ k r J Λ P f T A s hV _ hgN a
      · exact GlobalTheory.T.integralUnipotent_corner_entry_mem_idealLattice F E σ k r J Λ P f T A s hV _ hgN p
      · exact GlobalTheory.T.integralUnipotent_antidiagonal_mem_skewLattice F E σ k r J Λ P f T A s hV _ hgN a fun w =>
          GlobalTheory.T.re_antidiagonal_entry_eq_zero_of_flagDepth k r _ a (hgm g w) (hdep g _ hβ w))
    (by
      have lift : ∀ (β : Bk r) (l : InfinitePlace E → VM k r β),
          (∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = l w) ∧
            ∀ β' : Bk r, β' ≠ β → degB r β' ≤ degB r β → ∀ w, cM k r β' (Matrix.of.symm (gM A γ w)) = 0) →
          ∃ g : G, (fun w => cM k r β (ρ g o w)) = l ∧ ∀ β', β' ≠ β → degB r β' ≤ degB r β →
            (fun w => cM k r β' (ρ g o w)) = 0 := by
        rintro β l ⟨γ, hγ, hl, h0⟩
        obtain ⟨u, rfl⟩ := hGu γ hγ
        refine ⟨⟨u, (hG u).2 hγ⟩, funext fun w => ?_, fun β' h h' => funext fun w => ?_⟩
        · rw [hρo]; exact hl w
        · rw [hρo]; exact h0 β' h h' w
      rintro (p | a | p | a) l hl
      · exact lift _ _ (GlobalTheory.T.exists_integral_unipotent_lift_entry F E σ k r J Λ P f T A s hV p l hl)
      · exact lift _ _ (GlobalTheory.T.lift_row_middleSpace_integralPoint F E σ k r J Λ P f T A s hV a l hl)
      · exact lift _ _ (GlobalTheory.T.exists_integral_unipotent_lift_corner F E σ k r J Λ P f T A s hV p l hl)
      · exact lift _ _ (GlobalTheory.T.exists_integral_unipotent_lift_antidiagonal F E σ k r J Λ P f T A s hV a l hl))
    (fun g hg => by
      have h1' : ∀ w, gm g w = 1 := fun w => eq_one_of_dep (hdep g _ (fun β _ => hg β) w)
      exact Subtype.ext (Units.ext (ha3 _ h1')))
  obtain ⟨hNm, hN0⟩ := GlobalTheory.T.pi_unipotentModel_measurable_full_measure (InfinitePlace E) k r
  obtain ⟨hDm, hDv⟩ := GlobalTheory.T.measure_unipotent_tuples_free_entry_blocks (InfinitePlace E) k r DU DH DC DG hDUm hDHm hDCm hDGm
  set Dset : Set (InfinitePlace E → Mt k r) := {x | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧
    ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet (InfinitePlace E) k r DU DH DC DG β} with hDset
  have hstrict : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ Dset := fun x hx => by
    obtain ⟨g, hg, hu⟩ := tw x hx
    exact ⟨g, ⟨hρN g x hx, hg⟩, fun g' hg' => hu g' hg'.2⟩
  have conv : ∀ S : Set (InfinitePlace E → Mt k r), (∀ x ∈ NN, ∃! g : G, ρ g x ∈ S) ↔
      ∀ x ∈ NN, ∃! γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E,
        (InN (σ : E →+* E) J P γ ∧ latMap γ Λ = Λ) ∧ actM A γ x ∈ S := fun S => by
    refine forall₂_congr fun x hx => ?_
    constructor
    · rintro ⟨g, hg, hu⟩
      refine ⟨_, ⟨(hG _).1 g.2, hg⟩, fun γ hγ => ?_⟩
      obtain ⟨u, rfl⟩ := hGu γ hγ.1
      exact congrArg (fun g : G => ((g : (MM k r E)ˣ) : MM k r E)) (hu ⟨u, (hG u).2 hγ.1⟩ hγ.2)
    · rintro ⟨γ, hγ, hu⟩
      obtain ⟨u, rfl⟩ := hGu γ hγ.1
      refine ⟨⟨u, (hG u).2 hγ.1⟩, hγ.2, fun g hg => ?_⟩
      exact Subtype.ext (Units.ext (hu _ ⟨(hG _).1 g.2, hg⟩))
  haveI : Countable G := by
    haveI := countable_units E (2 * r + k + 1)
    infer_instance
  refine ⟨⟨Dset, hDm, (conv Dset).1 hstrict⟩, fun 𝓓 h𝓓 => ?_⟩
  have hEq := GlobalTheory.T.strictFundamentalDomain_measure_eq (G := G) _ ρ NN 𝓓 Dset hNm hN0 h𝓓.1 hDm hρ1 hρm hρN
    (fun g => GlobalTheory.T.unipotentModelProductAction_measurePreserving E k r A _ (hgm g)) ((conv 𝓓).2 h𝓓.2) hstrict
  beta_reduce
  rw [hEq, hDv]
  simp only [hDUv, hDHv, hDCv, hDGv]
  have hd : 0 < |(NumberField.discr F : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)
  rw [← GlobalTheory.T.unipotentRadical_blockCovolumes_prod _ (Fintype.card (InfinitePlace E)) k r s hd h9]
  have nnU : ∀ p : UTr r, 0 ≤ (2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) + 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 / s p.1.2) ^ (2 * Fintype.card (InfinitePlace E)) := fun p => by
    have := h9 p.1.1; have := h9 p.1.2; positivity
  have nnC : ∀ p : UTr r, 0 ≤ (2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) - 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 * s p.1.2) ^ (2 * Fintype.card (InfinitePlace E)) := fun p => by
    have := h9 p.1.1; have := h9 p.1.2; positivity
  have nnH : ∀ a : Fin r, 0 ≤ ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) * s a ^ (2 * Fintype.card (InfinitePlace E))) ^ (k + 1) := fun a => by
    have := h9 a; positivity
  have nnG : ∀ a : Fin r, 0 ≤ |(NumberField.discr F : ℝ)| ^ (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) * (s a ^ 2) ^ Fintype.card (InfinitePlace E) := fun a => by
    have := h9 a; positivity
  rw [← ENNReal.ofReal_prod_of_nonneg fun p _ => nnU p, ← ENNReal.ofReal_prod_of_nonneg fun a _ => nnH a,
    ← ENNReal.ofReal_prod_of_nonneg fun p _ => nnC p, ← ENNReal.ofReal_prod_of_nonneg fun a _ => nnG a,
    ofReal_five _ _ _ _ _ (by positivity) (Finset.prod_nonneg fun p _ => nnU p) (Finset.prod_nonneg fun a _ => nnH a)
      (Finset.prod_nonneg fun p _ => nnC p) (Finset.prod_nonneg fun a _ => nnG a),
    ENNReal.ofReal_pow (by norm_num)]
  simp

end GlobalTheory.SnMass.VolN
