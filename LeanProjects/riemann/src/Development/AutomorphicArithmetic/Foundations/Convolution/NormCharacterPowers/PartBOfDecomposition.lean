import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.BcSumD
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.GaloisGenerators.LocRoots
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep PositivityTheory.RgJS PositivityTheory.Rg.Tf.ChR

namespace UpperTheory.ConvolutionTheory.R

namespace Pb2

theorem val_pow {E : Type} [Field E] [NumberField E] (η : HChar E) (j : ℕ) (v : HeightOneSpectrum (𝓞 E)) :
    (η ^ j).val v = η.val v ^ j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, pow_succ, ← ih]; rfl

theorem bd {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} {π : CG E n} (hπ : π.IsUnitary)
    {S : Finset (HeightOneSpectrum (𝓞 E))} {α : Off E S → Fin n → ℂˣ} (hα : SatOff π S α) (v : Off E S) (a : Fin n) :
    ‖(α v a : ℂ)‖ ≤ Real.sqrt (nq v) := by
  rw [Real.sqrt_eq_rpow]
  exact (PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound E n π hπ v.1 _ (hα v) (α v a) (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))).2.le

theorem fam {n f q q' : ℕ} {A α : Fin n → ℂˣ} (h : Finset.univ.val.map A = Finset.univ.val.map fun a => α a ^ f)
    (hq : q' = q ^ f) (hα : ∀ a, ‖(α a : ℂ)‖ ≤ Real.sqrt q) :
    (∀ k : ℕ, ∑ a, (A a : ℂ) ^ k = ∑ a, (α a : ℂ) ^ (f * k)) ∧ ∀ a, ‖(A a : ℂ)‖ ≤ Real.sqrt q' := by
  refine ⟨fun k => ?_, fun a => ?_⟩
  · have := congrArg (fun m : Multiset ℂˣ => (m.map fun z : ℂˣ => (z : ℂ) ^ k).sum) h
    simp only [Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum, Units.val_pow_eq_pow_val, ← pow_mul] at this
    exact this
  · have hm : A a ∈ Finset.univ.val.map fun a => α a ^ f := h ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val a)
    obtain ⟨b, -, e⟩ := Multiset.mem_map.1 hm
    rw [← e, hq, Units.val_pow_eq_pow_val, norm_pow, Nat.cast_pow]
    refine (pow_le_pow_left₀ (norm_nonneg _) (hα b) f).trans (Real.le_sqrt_of_sq_le (le_of_eq ?_))
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]

end Pb2

open Pb2

theorem partB_of_decomposition : Decomp → PartB := by
  intro hD F E _ _ _ _ _ _ _ _ l hl hFE η hη n n' π π' _ _ hπ hπ'
  classical
  subst hFE
  have hη1 : η ^ Module.finrank F E = 1 := hη.2.1
  have hb := Filter.eventually_cofinite.1 ((hD F E hl).and hη.2.2)
  refine ⟨hb.toFinset, fun S hS T hT α β A B hα hβ hA hB s hs => ?_⟩
  have ho : ∀ w : HeightOneSpectrum (𝓞 E), Over w (w.under (𝓞 F)) := fun w => rfl
  have hg := fun v : Off F S => not_not.1 fun h => v.2 (hS (hb.mem_toFinset.2 h))
  let u : Off E T → Off F S := fun w => ⟨w.1.under (𝓞 F), fun h => w.2 ((hT _ _ (ho _)).2 h)⟩
  let f : Off E T → ℕ := fun w => if normV w.1 = normV (u w).1 then 1 else Module.finrank F E
  have hc1 : ∀ v, η.val v ^ Module.finrank F E = 1 := fun v => by rw [← val_pow, hη1]; rfl
  have hnorm : ∀ w, nq w = nq (u w) ^ f w := fun w => by
    show normV w.1 = normV (u w).1 ^ f w
    by_cases h : normV w.1 = normV (u w).1
    · simp only [f, if_pos h, pow_one, h]
    · simp only [f, if_neg h]
      exact ((hg (u w)).1.resolve_left fun h' => h (h'.2 _ rfl)).2 _ rfl
  have hC : Cover (Module.finrank F E) nq nq u f fun v => (η.val v.1 : ℂ) := by
    refine ⟨hnorm, fun v => ?_⟩
    have hcard : Nat.card {w // u w = v} = Nat.card {w : HeightOneSpectrum (𝓞 E) // w.under (𝓞 F) = v.1} :=
      Nat.card_congr ⟨fun w => ⟨w.1.1, congrArg Subtype.val w.2⟩,
        fun w => ⟨⟨w.1, fun h => v.2 (w.2 ▸ (hT _ _ (ho w.1)).1 h)⟩, Subtype.ext w.2⟩, fun _ => rfl, fun _ => rfl⟩
    obtain ⟨h | h, -, he⟩ := hg v
    · obtain ⟨w, hw⟩ := (Nat.card_ne_zero.1 (h.1.trans_ne hl.ne_zero)).1
      refine Or.inl ⟨hcard.trans h.1, ?_, ?_⟩
      · rintro w rfl
        exact if_pos (h.2 _ rfl)
      · have := (he w (hw ▸ ho w)).1 ⟨hw ▸ ho w, (h.2 w hw).trans (pow_one _).symm⟩
        simp only [this, Units.val_one]
    · have hne : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v.1 → normV w ≠ normV v.1 := fun w hw e =>
        hl.ne_one (Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm v.1)
          (((h.2 w hw).symm.trans e).trans (pow_one _).symm))
      obtain ⟨w, hw⟩ := (Nat.card_ne_zero.1 (h.1.trans_ne one_ne_zero)).1
      refine Or.inr ⟨hcard.trans h.1, ?_, ?_⟩
      · rintro w rfl
        exact if_neg (hne _ rfl)
      · have h1 : η.val v.1 ≠ 1 := fun e => hne w hw (((he w (hw ▸ ho w)).2 e).2.trans (pow_one _))
        haveI := Fact.mk hl
        rw [IsPrimitiveRoot.coe_units_iff, ← orderOf_eq_prime (hc1 _) h1]
        exact IsPrimitiveRoot.orderOf _
  have fA := fun w => fam (hA w (u w) (f w) ⟨ho _, hnorm w⟩) (hnorm w) (bd hπ hα (u w))
  have fB := fun w => fam (hB w (u w) (f w) ⟨ho _, hnorm w⟩) (hnorm w) (bd hπ' hβ (u w))
  have pF := prime_sum_converges_and_diverges F S
  have e := (bcSumD _ _ _ nq nq u f _ hl.pos (fun v => le_trans one_le_two (pF.two v)) hC _ _ _ _
    (fun v a => (α v a : ℂ)) (fun v b => (β v b : ℂ)) (fun w a => (A w a : ℂ)) (fun w b => (B w b : ℂ)) s
    (fun w => (fA w).1) (fun w => (fB w).1) (euler_product_log_bound _ nq _ _ _ _ s pF (bd hπ hα) (bd hπ' hβ) hs).1).2
  have hn : ∀ v, ‖((η.val v : ℂˣ) : ℂ)‖ = 1 := fun v =>
    Complex.norm_eq_one_of_pow_eq_one (by rw [← Units.val_pow_eq_pow_val, hc1, Units.val_one]) hl.ne_zero
  unfold LS
  rw [(euler_product_log_bound _ nq _ _ _ _ s (prime_sum_converges_and_diverges E T) (fun w => (fA w).2) (fun w => (fB w).2) hs).2.1, e,
    Complex.exp_sum, Finset.prod_range]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  exact (euler_product_log_bound _ nq _ _ _ _ s pF (bd hπ hα) (fun v b => by
    rw [norm_mul, norm_pow, hn, one_pow, mul_one]
    exact bd hπ' hβ v b) hs).2.1.symm

end UpperTheory.ConvolutionTheory.R
