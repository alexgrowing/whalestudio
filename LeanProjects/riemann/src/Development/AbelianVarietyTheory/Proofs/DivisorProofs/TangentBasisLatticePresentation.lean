import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

theorem sp_epsMul_mul {S : Type} [CommRing S] (a b : S) :
    spMap (epsMul a) ≫ spMap (epsMul b) = spMap (epsMul (a * b)) := by
  rw [GlobalTheory.ShFam.Pad.Guard.sp_comp]
  congr 1
  ext r <;> simp [epsMul, mul_assoc]

theorem exists_norm_eq_pi {m : ℕ} {C : Type} [NormedAddCommGroup C] (f : Fin m → C) (hf : 0 < ‖f‖) :
    ∃ k₀, ‖f k₀‖ = ‖f‖ ∧ ∀ k, ‖f k‖ ≤ ‖f k₀‖ := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact absurd hf (by simp [Subsingleton.elim f 0])
  obtain ⟨k₀, -, hk⟩ := Finset.exists_max_image Finset.univ (fun k => ‖f k‖) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  refine ⟨k₀, le_antisymm (norm_le_pi_norm f k₀) ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    fun k => hk k (Finset.mem_univ _)), fun k => hk k (Finset.mem_univ _)⟩

theorem latPres_scale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T : Scheme.{0}) (t : SAB H T) (R : Type) [CommRing R] (x : Sp R ⟶ T) (kind : ℕ → Bool) (sc : ℕ → ℝ) (g M : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (h : Fin M → Fin g → R), GlobalTheory.LineNorm.IsTanBasis t x e → LatPres t x kind (fun _ => 0) e h → ∀ (m : ℕ) (d : Fin m → R), (∃ n : ℕ, n ≠ 0 ∧ (n : R) ∈ Ideal.span (Set.range d)) → (∀ (p : ℕ) [Fact p.Prime] (φ : R →+* ↥(intO ℂ_[p])), ‖fun k => ((φ (d k) : ↥(intO ℂ_[p])) : ℂ_[p])‖ = (p : ℝ) ^ (-sc p)) → ∃ (M' : ℕ) (h' : Fin M' → Fin g → R), LatPres t x kind sc e h' := by
  intro E _ _ _ H T t R _ x kind sc g M e h hT hP m d hd hn
  classical
  obtain ⟨⟨n₀, hn₀, hsp⟩, hP2⟩ := hP
  obtain ⟨n, hn0, hnd⟩ := hd
  let h' : Fin (m * M) → Fin g → R := fun l => d (finProdFinEquiv.symm l).1 • h (finProdFinEquiv.symm l).2
  refine ⟨m * M, h', ⟨n * n₀, Nat.mul_ne_zero hn0 hn₀, fun i => ?_⟩, ?_⟩
  · have key : ∀ r ∈ Ideal.span (Set.range d), ∀ v ∈ Submodule.span R (Set.range h),
        r • v ∈ Submodule.span R (Set.range h') := by
      intro r hr v hv
      induction hr using Submodule.span_induction with
      | mem r hr =>
        obtain ⟨k, rfl⟩ := hr
        induction hv using Submodule.span_induction with
        | mem v hv =>
          obtain ⟨j, rfl⟩ := hv
          exact Submodule.subset_span ⟨finProdFinEquiv (k, j), by simp only [h', Equiv.symm_apply_apply]⟩
        | zero => simp
        | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
        | smul c v _ hv => rw [smul_comm]; exact Submodule.smul_mem _ _ hv
      | zero => simp
      | add r s _ _ hr hs => rw [add_smul]; exact add_mem hr hs
      | smul c r _ hr => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ _ hr
    have h1 := key _ hnd _ (hsp i)
    convert h1 using 1
    ext j
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp [Nat.cast_mul]
  · intro p _ φ
    obtain ⟨δ₀, hδ₀, hL⟩ := hP2 p φ
    have hpos : 0 < (p : ℝ) ^ (-sc p) :=
      Real.rpow_pos_of_pos (Nat.cast_pos.2 (Fact.out : p.Prime).pos) _
    obtain ⟨k₀, hk₀, hmax⟩ := exists_norm_eq_pi (fun k => ((φ (d k) : ↥(intO ℂ_[p])) : ℂ_[p]))
      ((hn p φ).symm ▸ hpos)
    refine ⟨δ₀ * ((φ (d k₀) : ↥(intO ℂ_[p])) : ℂ_[p]), ?_, fun cf w hw => ?_⟩
    · rw [norm_mul, hδ₀, neg_zero, Real.rpow_zero, one_mul]
      exact hk₀.trans (hn p φ)
    · have htan : ∀ i, IsTanAtG t (spMap ((intO ℂ_[p]).subtype.comp φ) ≫ x)
          (spMap (dualMap ((intO ℂ_[p]).subtype.comp φ)) ≫ e i) := fun i =>
        GlobalTheory.FactorDepth.isTanAtG_map t _ (hT.1 i)
      have hw' := GlobalTheory.ShFam.Pad.Guard.comb_smul htan hw ((φ (d k₀) : ↥(intO ℂ_[p])) : ℂ_[p])
      rw [← sp_epsMul_mul, Category.assoc, hL _ _ hw']
      have e1 : ∀ j, ‖∑ i, ((φ (h j i) : ↥(intO ℂ_[p])) : ℂ_[p]) * (((φ (d k₀) : ↥(intO ℂ_[p])) : ℂ_[p]) * cf i)‖ =
          ‖((φ (d k₀) : ↥(intO ℂ_[p])) : ℂ_[p])‖ * ‖∑ i, ((φ (h j i) : ↥(intO ℂ_[p])) : ℂ_[p]) * cf i‖ := by
        intro j
        rw [← norm_mul, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∀ l, ‖∑ i, ((φ (h' l i) : ↥(intO ℂ_[p])) : ℂ_[p]) * cf i‖ =
          ‖((φ (d (finProdFinEquiv.symm l).1) : ↥(intO ℂ_[p])) : ℂ_[p])‖ *
            ‖∑ i, ((φ (h (finProdFinEquiv.symm l).2 i) : ↥(intO ℂ_[p])) : ℂ_[p]) * cf i‖ := by
        intro l
        rw [← norm_mul, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [h', Pi.smul_apply, smul_eq_mul, map_mul]
        push_cast
        ring
      simp only [e1, e2]
      constructor
      · intro H l
        exact (mul_le_mul_of_nonneg_right (hmax _) (norm_nonneg _)).trans (H _)
      · intro H j
        simpa using H (finProdFinEquiv (k₀, j))

end GlobalTheory.ArLieBase
