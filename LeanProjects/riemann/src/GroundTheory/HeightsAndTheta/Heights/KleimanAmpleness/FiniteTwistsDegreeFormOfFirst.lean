import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreJoin
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver GeneratesOver)

noncomputable section

section Graded

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem aeval_CX_of_isHomogeneous {r : ℕ} (η : Fin r → Ω) {f : MvPolynomial (Fin r) S} {e : ℕ}
    (hf : f.IsHomogeneous e) :
    aeval (fun j => Polynomial.C (η j) * Polynomial.X) f = Polynomial.C (aeval η f) * Polynomial.X ^ e := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have he : ∑ i ∈ d.support, d i = e := by
    rw [← hf (mem_support_iff.mp hd), Finsupp.weight_apply]
    simp_rw [smul_eq_mul, Finsupp.sum, Pi.one_apply, mul_one]
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, he,
    Polynomial.algebraMap_apply, map_prod, map_pow, Polynomial.C_mul]
  ring

theorem powerSum_finite {K : Type} [Fintype K] {ι : K → Type} (y : (Σ k, ι k) → Ω) (γ β : K → ℤ) {r : ℕ}
    (η : Fin (r + 1) → Ω) (H : ℕ → Submodule S Ω) (hH : ∀ b : ℕ, H b = secOver S y (γ + b • β))
    {n : ℕ} (deg : Fin n → ℕ) (gen : Fin n → Ω) (hgen : ∀ k, gen k ∈ H (deg k))
    (hle : ∀ b : ℕ, H b ≤ Submodule.span S {z | ∃ (k : Fin n) (f : MvPolynomial (Fin (r + 1)) S) (e : ℕ),
        f.IsHomogeneous e ∧ e + deg k = b ∧ z = aeval η f * gen k}) :
    Module.Finite (IndefiniteRowSideFullHecke.Kleiman2.genRing S η) (IndefiniteRowSideFullHecke.Kleiman2.powerSum S y γ β η) := by
  set Q := Submodule.span (IndefiniteRowSideFullHecke.Kleiman2.genRing S η)
    (Set.range fun k => Polynomial.C (gen k) * Polynomial.X ^ deg k) with hQ
  have hmem : ∀ (b : ℕ) (s : Ω), s ∈ H b → Polynomial.C s * Polynomial.X ^ b ∈ Q := by
    intro b s hs
    have key : ∀ t ∈ Submodule.span S {z | ∃ (k : Fin n) (f : MvPolynomial (Fin (r + 1)) S) (e : ℕ),
        f.IsHomogeneous e ∧ e + deg k = b ∧ z = aeval η f * gen k}, Polynomial.C t * Polynomial.X ^ b ∈ Q := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨k, f, e, hf, he, rfl⟩ := hz
        have hg : aeval (fun j => Polynomial.C (η j) * Polynomial.X) f ∈ IndefiniteRowSideFullHecke.Kleiman2.genRing S η := by
          rw [IndefiniteRowSideFullHecke.Kleiman2.genRing, Algebra.adjoin_range_eq_range_aeval]
          exact ⟨f, rfl⟩
        have h1 : Polynomial.C (aeval η f * gen k) * Polynomial.X ^ b =
            (⟨_, hg⟩ : IndefiniteRowSideFullHecke.Kleiman2.genRing S η) • (Polynomial.C (gen k) * Polynomial.X ^ deg k) := by
          rw [Subalgebra.smul_def, smul_eq_mul]
          change _ = aeval (fun j => Polynomial.C (η j) * Polynomial.X) f * _
          rw [aeval_CX_of_isHomogeneous η hf, ← he, pow_add, map_mul]
          ring
        rw [h1]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
      | zero => simp
      | add a c _ _ ha hc =>
        rw [map_add, add_mul]
        exact add_mem ha hc
      | smul a z _ hz =>
        have h1 : Polynomial.C (a • z) * Polynomial.X ^ b =
            (⟨algebraMap S (Polynomial Ω) a, Subalgebra.algebraMap_mem _ a⟩ : IndefiniteRowSideFullHecke.Kleiman2.genRing S η) •
              (Polynomial.C z * Polynomial.X ^ b) := by
          rw [Subalgebra.smul_def, smul_eq_mul]
          change _ = algebraMap S (Polynomial Ω) a * _
          rw [Polynomial.algebraMap_apply, Algebra.smul_def, map_mul]
          ring
        rw [h1]
        exact Submodule.smul_mem _ _ hz
    exact key s (hle b hs)
  have heq : IndefiniteRowSideFullHecke.Kleiman2.powerSum S y γ β η = Q := by
    apply le_antisymm
    · rw [IndefiniteRowSideFullHecke.Kleiman2.powerSum, Submodule.span_le]
      rintro _ ⟨b, s, hs, rfl⟩
      exact hmem b s (by rw [hH b]; exact hs)
    · rw [hQ, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨deg k, gen k, by rw [← hH (deg k)]; exact hgen k, rfl⟩
  rw [Module.Finite.iff_fg, heq]
  exact Submodule.fg_span (Set.finite_range _)

end Graded

theorem FiniteTwists.finiteTwists_degree_form_of_first (hSeg : SegreBase.Statement) (hP : BundlePair.Statement)
    (hA : Kleiman.FiniteTwists.Statement.{0, 0}) : IndefiniteRowSideFullHecke.Kleiman2.FiniteTwists.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y γ β n η hS hy hη hgen
  obtain ⟨hbase, hsec, hgenIff⟩ := hSeg S K ι Ω y hy
  obtain ⟨N, ⟨e⟩⟩ : ∃ N : ℕ, Nonempty ((∀ k, ι k) ≃ Fin (N + 1)) := by
    have : Nonempty (∀ k, ι k) := ⟨fun k => (hy k).choose⟩
    exact ⟨Fintype.card (∀ k, ι k) - 1, ⟨(Fintype.equivFin _).trans
      (finCongr (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm)⟩⟩
  obtain ⟨G, B, hGB, hgenB⟩ := hP S (Unit ⊕ K) (Sum.elim (fun _ : Unit => ∀ k, ι k) ι) Ω (segreJoin y)
    (Sum.inl ()) N e hbase (IndefiniteRowSideFullHecke.Kleiman2.pullDeg γ) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β)
  have hpd : ∀ b : ℕ, (IndefiniteRowSideFullHecke.Kleiman2.pullDeg γ + b • IndefiniteRowSideFullHecke.Kleiman2.pullDeg β : Unit ⊕ K → ℤ) =
      IndefiniteRowSideFullHecke.Kleiman2.pullDeg (γ + b • β) := by
    intro b
    funext o
    cases o <;> simp [IndefiniteRowSideFullHecke.Kleiman2.pullDeg]
  have hsecs : ∀ b : ℕ, (G.twist (B.pow b)).secs = secOver S y (γ + b • β) := by
    intro b
    rw [hGB b, hpd b, hsec]
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun hn => ?_
    subst hn
    obtain ⟨u, -, hu⟩ := hgen (fun k => (hy k).choose) (fun k => (hy k).choose_spec)
    simp at hu
  have hβ : ∀ j, η j ∈ secOver S (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) := fun j => by
    rw [hsec]
    exact hη j
  obtain ⟨hηB, hspan⟩ := (hgenB (r + 1) η).mp ⟨hβ, (hgenIff β (r + 1) η).mpr hgen⟩
  have hx : IndefiniteRowSideFullHecke.Kleiman2.blockVec (segreJoin y) (Sum.inl ()) ∘ e.symm ≠ 0 := by
    obtain ⟨i, hi⟩ := hbase.1 (Sum.inl ())
    intro h0
    apply hi
    have h1 := congrFun h0 (e i)
    change segreJoin y ⟨Sum.inl (), e.symm (e i)⟩ = 0 at h1
    have h2 : e.symm (e i) = i := e.symm_apply_apply i
    rw [h2] at h1
    exact h1
  obtain ⟨m, deg, gen, hgen1, hle⟩ := hA S Ω N _ G B r η hx hηB hspan
  exact powerSum_finite y γ β η _ hsecs deg gen hgen1 hle

theorem FiniteTwists.equiv (hSeg : SegreBase.Statement) (hP : BundlePair.Statement) :
    Kleiman.FiniteTwists.Statement.{0, 0} ↔ IndefiniteRowSideFullHecke.Kleiman2.FiniteTwists.Statement :=
  ⟨FiniteTwists.finiteTwists_degree_form_of_first hSeg hP, fun _ => Kleiman.FiniteTwists.full⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
