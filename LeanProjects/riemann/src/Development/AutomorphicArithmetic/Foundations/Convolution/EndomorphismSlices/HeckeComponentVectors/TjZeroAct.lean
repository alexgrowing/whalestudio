import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PPairSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SatOfEig

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.F.RS

attribute [local instance] borelG borelF borelA borelH

section SlopeTestRemainingChoices

open GlobalTheory.LGrp GlobalTheory.LFun.SatCompare GlobalTheory.LocGL GlobalTheory.WeylGL

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem unifIs (w : Pl E) : IsUnifV E w (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) :=
  Classical.epsilon_spec (exists_isUnifV w)

private theorem tj_indep (w : Pl E) (n j : ℕ) {ϖ ϖ' : w.adicCompletion E} (hu : IsUnifV E w ϖ)
    (hu' : IsUnifV E w ϖ') : Tj ℂ n (Ov E w) ϖ' j = Tj ℂ n (Ov E w) ϖ j := by
  have h0 := ne_zero_of_isUnifV hu
  have hv : Valued.v (ϖ' / ϖ) = 1 := by
    rw [map_div₀, hu, hu', div_self WithZero.coe_ne_zero]
  have e := Final.TjIndep _ (Ov E w) ϖ (ϖ' / ϖ) ℂ n j hv.le
    (show Valued.v (ϖ' / ϖ)⁻¹ ≤ 1 by rw [map_inv₀, hv, inv_one]) (div_ne_zero (ne_zero_of_isUnifV hu') h0)
  rwa [div_mul_cancel₀ _ h0] at e

private theorem tj_zero_act (w : Pl E) (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GLw n w) V) {ϖ : w.adicCompletion E} (hu : IsUnifV E w ϖ) {x : V}
    (hx : x ∈ fixed π (KGL w n)) : heckeVec π (KGL w n) (Tj ℂ n (Ov E w) ϖ 0) x = x := by
  have h0 := ne_zero_of_isUnifV hu
  have e : Tj ℂ n (Ov E w) ϖ 0 = dosetInd ℂ (KGL w n) 1 := by
    rw [Tj_eq h0]
    congr 1
  rw [e, heckeVec_one (Final.GLintComm E w n) hx]

private theorem tj_top_ne (w : Pl E) (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GLw n w) V) {ϖ : w.adicCompletion E} (hu : IsUnifV E w ϖ) {x : V} (hx0 : x ≠ 0)
    (hx : x ∈ fixed π (KGL w n)) {c : ℂ} (h1 : heckeVec π (KGL w n) (Tj ℂ n (Ov E w) ϖ n) x = c • x) : c ≠ 0 := by
  intro e
  have h0 := ne_zero_of_isUnifV hu
  have hTn : Tj ℂ n (Ov E w) ϖ n = dosetInd ℂ (KGL w n) (tor h0 fun _ => 1) := by
    rw [Tj_eq h0]; simp
  rw [e, zero_smul, hTn, heckeVec_dosetInd (R := {tor h0 fun _ => 1}) hx, Finset.sum_singleton] at h1
  · exact hx0 (by simpa [← Module.End.mul_apply, ← map_mul] using congrArg (π (tor h0 fun _ => 1)⁻¹) h1)
  · intro γ hγ
    exact mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simpa using hγ⟩
  · intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doset.1 hg
    refine ⟨_, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    rw [← tor_const_comm, mul_assoc, inv_mul_cancel_left]
    exact mul_mem ha hb

end SlopeTestRemainingChoices

theorem UpperTheory.Zero.ConvolutionTheory.EB.sat2Ex :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (V ι : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLw a w × GLw b w) V) (x : ι → V)
    (t : Fin (a + 1) × Fin (b + 1) → ℂ), x ≠ 0 → (∀ i, x i ∈ fixed ρ (K2 a b w)) →
    (∀ (p : Fin (a + 1) × Fin (b + 1)) i, heckeVec ρ (K2 a b w) (fun y : GLw a w × GLw b w => Tj ℂ a (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) p.1 y.1 * Tj ℂ b (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) p.2 y.2) (x i) = t p • x i) →
    ∃ B₁ B₂ : Multiset ℂˣ, B₁.card = a ∧ B₂.card = b ∧ (∀ p, t p = satEig (qV E w) a B₁ p.1 * satEig (qV E w) b B₂ p.2) ∧ ∀ i, IsSat2 w ρ (x i) B₁ B₂ := by
  intro E _ _ _ a b w V ι _ _ ρ x t hx0 hfix ht
  have hu := unifIs w
  have hKa := Final.GLintComm E w a
  have hKb := Final.GLintComm E w b
  have hTa := fun i : ℕ => Tj_mem_hecke (n := a) hu i
  have hTb := fun j : ℕ => Tj_mem_hecke (n := b) hu j
  obtain ⟨k₀, hk₀⟩ : ∃ k, x k ≠ 0 := Function.ne_iff.1 hx0
  have fA : ∀ k, x k ∈ fixed (ρ.comp (MonoidHom.inl _ _)) (KGL w a) := fun k =>
    GlobalTheory.LGrp.mem_fixed.2 fun g hg =>
      GlobalTheory.LGrp.mem_fixed.1 (hfix k) (g, 1) (Subgroup.mem_prod.2 ⟨hg, one_mem _⟩)
  have fB : ∀ k, x k ∈ fixed (ρ.comp (MonoidHom.inr _ _)) (KGL w b) := fun k =>
    GlobalTheory.LGrp.mem_fixed.2 fun g hg =>
      GlobalTheory.LGrp.mem_fixed.1 (hfix k) (1, g) (Subgroup.mem_prod.2 ⟨one_mem _, hg⟩)
  have fAB : ∀ k (j : ℕ), heckeVec (ρ.comp (MonoidHom.inr _ _)) (KGL w b)
      (Tj ℂ b (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) j) (x k) ∈ fixed (ρ.comp (MonoidHom.inl _ _)) (KGL w a) := by
    intro k j
    refine GlobalTheory.LGrp.mem_fixed.2 fun g hg => ?_
    have key := map_heckeVec hKb (hTb j) (ρ := ρ.comp (MonoidHom.inr _ _)) (ρ' := ρ.comp (MonoidHom.inr _ _))
      ((ρ.comp (MonoidHom.inl _ _)) g) (fun g' y => by
        simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        simp) (x k)
    rw [key, GlobalTheory.LGrp.mem_fixed.1 (fA k) g hg]
  have pp : ∀ (p : Fin (a + 1) × Fin (b + 1)) k, heckeVec (ρ.comp (MonoidHom.inl _ _)) (KGL w a)
      (Tj ℂ a (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) p.1) (heckeVec (ρ.comp (MonoidHom.inr _ _)) (KGL w b)
        (Tj ℂ b (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) p.2) (x k)) = t p • x k := fun p k => by
    rw [← heckeVec_pairProd ρ hKa hKb (hTa _) (hTb _) (hfix k)]
    exact ht p k
  have eA : ∀ (i : Fin (a + 1)) k, heckeVec (ρ.comp (MonoidHom.inl _ _)) (KGL w a)
      (Tj ℂ a (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) i) (x k) = t (i, 0) • x k := fun i k => by
    have := pp (i, 0) k
    simp only [Fin.val_zero] at this
    rwa [tj_zero_act w b _ hu (fB k)] at this
  have eB : ∀ (j : Fin (b + 1)) k, heckeVec (ρ.comp (MonoidHom.inr _ _)) (KGL w b)
      (Tj ℂ b (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) j) (x k) = t (0, j) • x k := fun j k => by
    have := pp (0, j) k
    simp only [Fin.val_zero] at this
    rwa [tj_zero_act w a _ hu (fAB k j)] at this
  have t00 : t (0, 0) = 1 := by
    have h1 := eA 0 k₀
    simp only [Fin.val_zero] at h1
    rw [tj_zero_act w a _ hu (fA k₀)] at h1
    exact smul_left_injective ℂ hk₀ (by simpa using h1.symm)
  have mul : ∀ p : Fin (a + 1) × Fin (b + 1), t p = t (p.1, 0) * t (0, p.2) := fun p => by
    have h1 := pp p k₀
    rw [eB p.2 k₀, heckeVec_smul_pair _ hKa (hTa _), eA p.1 k₀, smul_smul, mul_comm] at h1
    exact smul_left_injective ℂ hk₀ h1.symm
  have hta : t (Fin.last a, 0) ≠ 0 :=
    tj_top_ne w a _ hu hk₀ (fA k₀) (by simpa using eA (Fin.last a) k₀)
  have htb : t (0, Fin.last b) ≠ 0 :=
    tj_top_ne w b _ hu hk₀ (fB k₀) (by simpa using eB (Fin.last b) k₀)
  obtain ⟨B₁, c₁, h₁⟩ := GlobalTheory.T.exists_multiset_satakeEigenvalue_eq (qV E w) a (qV_ne_zero w)
    (fun i => if h : i < a + 1 then t (⟨i, h⟩, 0) else 0) (by simpa using t00)
    (by simpa [Fin.last] using hta)
  obtain ⟨B₂, c₂, h₂⟩ := GlobalTheory.T.exists_multiset_satakeEigenvalue_eq (qV E w) b (qV_ne_zero w)
    (fun j => if h : j < b + 1 then t (0, ⟨j, h⟩) else 0) (by simpa using t00)
    (by simpa [Fin.last] using htb)
  have s₁ : ∀ i : Fin (a + 1), satEig (qV E w) a B₁ i = t (i, 0) := fun i => by
    rw [h₁ i (Nat.lt_succ_iff.1 i.2), dif_pos i.2]
  have s₂ : ∀ j : Fin (b + 1), satEig (qV E w) b B₂ j = t (0, j) := fun j => by
    rw [h₂ j (Nat.lt_succ_iff.1 j.2), dif_pos j.2]
  have tp : ∀ p : Fin (a + 1) × Fin (b + 1), t p = satEig (qV E w) a B₁ p.1 * satEig (qV E w) b B₂ p.2 := fun p => by
    rw [s₁, s₂]
    exact mul p
  refine ⟨B₁, B₂, c₁, c₂, tp, fun k => ⟨hfix k, c₁, c₂, fun ϖ hϖ i hi j hj => ?_⟩⟩
  have h := ht (⟨i, Nat.lt_succ_iff.2 hi⟩, ⟨j, Nat.lt_succ_iff.2 hj⟩) k
  rw [tp] at h
  rw [tj_indep w a i hu hϖ, tj_indep w b j hu hϖ]
  exact h
