import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleChartSmoothAlgebraLocalPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftingResidueValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyVanishingOfFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseSectionsOfAlgebraicAffineNbhdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.DenseSec
theorem chart : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R), ∃ (g : ℕ) (t : Fin g → A) (h : A), (∀ i, ε (t i) = 0) ∧ IsUnit (ε h) ∧ GlobalTheory.DenseSec.EtChart R A t h := GlobalTheory.T.exists_etale_chart_smooth_algebra_local_point
theorem hensel : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (ε : A →ₐ[R] R), IsUnit (ε h) → ∀ c : Fin g → R, (∀ i, c i - ε (t i) ∈ maximalIdeal R) → ∃ a : A →ₐ[R] R, IsUnit (a h) ∧ ∀ i, a (t i) = c i := GlobalTheory.T.exists_section_lifting_residue_values
theorem fibre : ∀ (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (Ω : Type) [Field Ω] [Algebra R Ω], IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ Q : MvPolynomial (Fin g) Ω, Q ≠ 0 ∧ ∀ a : A →ₐ[R] Ω, a h ≠ 0 → GlobalTheory.DenseSec.pt a f = 0 → MvPolynomial.eval (fun i => a (t i)) Q = 0 := GlobalTheory.T.exists_poly_vanishing_of_fiber
theorem reduce : (∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R) (Ω : Type) [Field Ω] [Algebra R Ω], RingHom.ker (algebraMap R Ω) ≠ maximalIdeal R → IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ a : A →ₐ[R] R, GlobalTheory.DenseSec.pt ((Algebra.ofId R Ω).comp a) f ≠ 0) → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (U : Over (Sp R)), Smooth U.hom → ∀ (e : Sp R ⟶ U.left), e ≫ U.hom = 𝟙 _ → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Sp R), closedPoint R ∉ Set.range x → IrreducibleSpace (pullback U.hom x : Scheme.{0}) → ∀ O : (pullback U.hom x).Opens, (O : Set (pullback U.hom x : Scheme.{0})).Nonempty → ∃ (a : Sp R ⟶ U.left) (aΩ : Sp Ω ⟶ pullback U.hom x), a ≫ U.hom = 𝟙 _ ∧ aΩ ≫ pullback.fst _ _ = x ≫ a ∧ aΩ ≫ pullback.snd _ _ = 𝟙 _ ∧ Set.range aΩ ⊆ O := GlobalTheory.T.denseSections_of_algebraic_affineNbhd

theorem image_maximalIdeal_infinite {R Ω : Type} [CommRing R] [IsLocalRing R] [Field Ω] [Algebra R Ω]
    (hker : RingHom.ker (algebraMap R Ω) ≠ maximalIdeal R) :
    (algebraMap R Ω '' (maximalIdeal R : Set R)).Infinite := by
  have hle : RingHom.ker (algebraMap R Ω) ≤ maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  obtain ⟨m0, hm0, hm0k⟩ : ∃ m0 ∈ maximalIdeal R, m0 ∉ RingHom.ker (algebraMap R Ω) := by
    by_contra hcon
    push_neg at hcon
    exact hker (le_antisymm hle hcon)
  rw [RingHom.mem_ker] at hm0k
  have hne : ∀ n k : ℕ, n < k → algebraMap R Ω (m0 ^ (n + 1)) ≠ algebraMap R Ω (m0 ^ (k + 1)) := by
    intro n k hnk heq
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hnk
    have h1 : algebraMap R Ω (m0 ^ (d + 1)) = 1 := by
      have hpow : algebraMap R Ω (m0 ^ (n + 1)) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hm0k
      have : algebraMap R Ω (m0 ^ (n + 1)) * algebraMap R Ω (m0 ^ (d + 1)) = algebraMap R Ω (m0 ^ (n + 1)) * 1 := by
        rw [_root_.mul_one, ← map_mul, ← _root_.pow_add, heq]
        congr 2
        omega
      exact mul_left_cancel₀ hpow this
    have h2 : 1 - m0 ^ (d + 1) ∈ maximalIdeal R :=
      hle (by rw [RingHom.mem_ker, map_sub, map_one, h1, sub_self])
    have h3 : m0 ^ (d + 1) ∈ maximalIdeal R := Ideal.pow_mem_of_mem _ hm0 _ d.succ_pos
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Ideal.add_mem _ h2 h3))
  have hinj : Function.Injective (fun n : ℕ => algebraMap R Ω (m0 ^ (n + 1))) := by
    intro n k h
    by_contra hnk
    rcases lt_or_gt_of_ne hnk with hlt | hlt
    · exact hne n k hlt h
    · exact hne k n hlt h.symm
  exact Set.infinite_of_injective_forall_mem hinj (fun n => ⟨m0 ^ (n + 1), Ideal.pow_mem_of_mem _ hm0 _ n.succ_pos, rfl⟩)

theorem exists_eval_ne_zero_of_infinite {Ω : Type} [Field Ω] (S : Set Ω) (hS : S.Infinite) (g : ℕ)
    (Q : MvPolynomial (Fin g) Ω) (hQ : Q ≠ 0) : ∃ c : Fin g → Ω, (∀ i, c i ∈ S) ∧ MvPolynomial.eval c Q ≠ 0 := by
  obtain ⟨T, hTS, hT⟩ := hS.exists_subset_card_eq (Q.totalDegree + 1)
  by_contra hcon
  push_neg at hcon
  apply hQ
  refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset Q (fun _ => T) (fun i => ?_) (fun x hx => hcon x (fun i => hTS (hx i)))
  rw [hT]
  exact Nat.lt_succ_of_le (MvPolynomial.degreeOf_le_totalDegree Q i)

theorem key : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R) (Ω : Type) [Field Ω] [Algebra R Ω], RingHom.ker (algebraMap R Ω) ≠ maximalIdeal R → IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ a : A →ₐ[R] R, GlobalTheory.DenseSec.pt ((Algebra.ofId R Ω).comp a) f ≠ 0 := by
  intro R _ _ hc A _ _ _ ε Ω _ _ hker hirr f hf
  obtain ⟨g, t, h, ht0, hεh, hch⟩ := chart R A ε
  obtain ⟨Q, hQ, hQv⟩ := fibre R A g t h hch Ω hirr f hf
  obtain ⟨c', hc'S, hc'Q⟩ := exists_eval_ne_zero_of_infinite _ (image_maximalIdeal_infinite hker) g Q hQ
  choose c hcm hcc using hc'S
  obtain ⟨a, hah, hat⟩ := hensel R hc A g t h hch ε hεh c (fun i => by simpa [ht0] using hcm i)
  refine ⟨a, fun h0 => hc'Q ?_⟩
  have hv := hQv ((Algebra.ofId R Ω).comp a) (by simpa using (hah.map (algebraMap R Ω)).ne_zero) h0
  have hc' : c' = fun i => ((Algebra.ofId R Ω).comp a) (t i) := by
    funext i
    simp [hat, hcc]
  rw [hc']
  exact hv

theorem dense_sections : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (U : Over (Sp R)), Smooth U.hom → ∀ (e : Sp R ⟶ U.left), e ≫ U.hom = 𝟙 _ → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Sp R), closedPoint R ∉ Set.range x → IrreducibleSpace (pullback U.hom x : Scheme.{0}) → ∀ O : (pullback U.hom x).Opens, (O : Set (pullback U.hom x : Scheme.{0})).Nonempty → ∃ (a : Sp R ⟶ U.left) (aΩ : Sp Ω ⟶ pullback U.hom x), a ≫ U.hom = 𝟙 _ ∧ aΩ ≫ pullback.fst _ _ = x ≫ a ∧ aΩ ≫ pullback.snd _ _ = 𝟙 _ ∧ Set.range aΩ ⊆ O := reduce key
end GlobalTheory.DenseSec
