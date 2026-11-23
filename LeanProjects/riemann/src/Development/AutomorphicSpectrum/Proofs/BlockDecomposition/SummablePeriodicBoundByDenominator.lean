import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Compare

theorem summable_comp_of_injective_prod {X Y Q : Type*} [Finite Q] {d : Y → ℝ}
    (hd : ∀ y, 0 ≤ d y) (hs : Summable d) (y : X → Y) (q : X → Q)
    (hinj : Function.Injective fun x => (y x, q x)) : Summable fun x => d (y x) := by
  have h1 : Summable (fun p : Y × Q => d p.1 * (fun _ : Q => (1 : ℝ)) p.2) :=
    Summable.mul_of_nonneg hs (Summable.of_finite) hd (fun _ => zero_le_one)
  have h2 := h1.comp_injective hinj
  simpa [Function.comp_def] using h2

theorem finite_quot_nsmul {M : Type*} [AddCommGroup M] [Module.Finite ℤ M] {τ : ℕ} (hτ : 0 < τ) :
    Finite (M ⧸ (nsmulAddMonoidHom τ : M →+ M).range) := by
  haveI : Module.Finite ℤ (M ⧸ (nsmulAddMonoidHom τ : M →+ M).range) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' _).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  apply Module.finite_of_fg_torsion
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H m =>
    refine ⟨⟨(τ : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hτ.ne')⟩, ?_⟩
    have : ((τ : ℤ) • (m : M ⧸ (nsmulAddMonoidHom τ : M →+ M).range))
        = ((τ • m : M) : M ⧸ (nsmulAddMonoidHom τ : M →+ M).range) := by
      rw [natCast_zsmul]; rfl
    show ((τ : ℤ) • (m : M ⧸ (nsmulAddMonoidHom τ : M →+ M).range)) = 0
    rw [this, QuotientAddGroup.eq_zero_iff]
    exact ⟨m, rfl⟩

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]

theorem mem_hermO_iff (σ : E →ₐ[F] E) (n : ℕ) (c : hermE σ n) :
    c ∈ hermO σ n ↔ ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = c.1 a b := Iff.rfl

def toInt (σ : E →ₐ[F] E) (n : ℕ) : hermO σ n →+ Matrix (Fin n) (Fin n) (𝓞 E) where
  toFun c := Matrix.of fun a b => Classical.choose ((mem_hermO_iff σ n c.1).1 c.2 a b)
  map_zero' := by
    ext a b
    have h := Classical.choose_spec ((mem_hermO_iff σ n (0 : hermO σ n).1).1 (0 : hermO σ n).2 a b)
    refine Eq.trans h ?_
    change _ = algebraMap (𝓞 E) E 0
    rw [map_zero]
    rfl
  map_add' := by
    intro c d
    ext a b
    have h1 := Classical.choose_spec ((mem_hermO_iff σ n (c + d).1).1 (c + d).2 a b)
    have h2 := Classical.choose_spec ((mem_hermO_iff σ n c.1).1 c.2 a b)
    have h3 := Classical.choose_spec ((mem_hermO_iff σ n d.1).1 d.2 a b)
    refine Eq.trans h1 ?_
    change _ = algebraMap (𝓞 E) E (_ + _)
    rw [map_add]
    exact Eq.trans rfl (Eq.symm (Eq.trans (congrArg₂ (· + ·) h2 h3) rfl))

theorem algebraMap_toInt (σ : E →ₐ[F] E) (n : ℕ) (c : hermO σ n) (a b : Fin n) :
    algebraMap (𝓞 E) E (toInt σ n c a b) = c.1.1 a b :=
  Classical.choose_spec ((mem_hermO_iff σ n c.1).1 c.2 a b)

theorem toInt_injective (σ : E →ₐ[F] E) (n : ℕ) : Function.Injective (toInt σ n) := by
  intro c d h
  apply Subtype.ext
  apply Subtype.ext
  ext a b
  rw [← algebraMap_toInt σ n c a b, ← algebraMap_toInt σ n d a b, h]

theorem finite_hermO (σ : E →ₐ[F] E) (n : ℕ) : Module.Finite ℤ (hermO σ n) :=
  Module.Finite.of_injective (toInt σ n).toIntLinearMap (toInt_injective σ n)

theorem Kc_le_add {n : ℕ} (c l : Matrix (Fin n) (Fin n) E)
    (hl : ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = l a b) : Kc c ≤ Kc (c + l) := by
  intro y hy i
  obtain ⟨o, ho⟩ := hy i
  choose m hm using hl
  refine ⟨o + ∑ j, m i j * y j, ?_⟩
  rw [Matrix.add_mulVec, Pi.add_apply, map_add, ho]
  congr 1
  simp [Matrix.mulVec, dotProduct, hm]

theorem delta_add {n : ℕ} (c l : Matrix (Fin n) (Fin n) E)
    (hl : ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = l a b) : delta (c + l) = delta c := by
  have h1 := Kc_le_add c l hl
  have h2 := Kc_le_add (c + l) (-l) (fun a b => by
    obtain ⟨o, ho⟩ := hl a b
    exact ⟨-o, by simp [ho]⟩)
  rw [add_neg_cancel_right] at h2
  unfold delta
  rw [le_antisymm h2 h1]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Compare

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Compare in

theorem summable_quot_of_le_delta_rpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (Λ : AddSubgroup (hermE σ n)) (t : F), t ≠ 0 → ∀ τ : ℕ, 0 < τ →
    (∀ c ∈ hermO σ n, ((τ : F) / t) • c ∈ Λ) →
    ∀ g : hermE σ n → ℝ, (∀ c, 0 ≤ g c) → (∀ c, ∀ l ∈ Λ, g (c + l) = g c) →
    ∀ C s : ℝ, (∀ c, g c ≤ C * (delta (t • c).1 : ℝ) ^ (-s)) →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) →
    Summable (fun x : hermE σ n ⧸ Λ => g (Quotient.out x)) := by
  intro F E _ _ _ _ _ σ n Λ t ht τ hτ hΛ g hg hper C s hb hsum
  haveI : Module.Finite ℤ (hermO σ n) := finite_hermO σ n
  haveI := finite_quot_nsmul (M := hermO σ n) hτ
  let y : hermE σ n ⧸ Λ → hermE σ n ⧸ hermO σ n :=
    fun x => QuotientAddGroup.mk (t • Quotient.out x)
  have hmem : ∀ x, t • Quotient.out x - Quotient.out (y x) ∈ hermO σ n := by
    intro x
    have h : (QuotientAddGroup.mk (Quotient.out (y x)) : hermE σ n ⧸ hermO σ n)
        = QuotientAddGroup.mk (t • Quotient.out x) := QuotientAddGroup.out_eq' (y x)
    have := QuotientAddGroup.eq.1 h
    rwa [neg_add_eq_sub] at this
  let w : hermE σ n ⧸ Λ → hermO σ n := fun x => ⟨_, hmem x⟩
  let q : hermE σ n ⧸ Λ → hermO σ n ⧸ (nsmulAddMonoidHom τ : hermO σ n →+ hermO σ n).range :=
    fun x => QuotientAddGroup.mk (w x)
  have hinj : Function.Injective fun x => (y x, q x) := by
    intro x x' h
    have hy : y x = y x' := congrArg Prod.fst h
    have hq : q x = q x' := congrArg Prod.snd h
    obtain ⟨c, hc⟩ := QuotientAddGroup.eq.1 hq
    have hc' : τ • (c.1 : hermE σ n) = t • (Quotient.out x' - Quotient.out x) := by
      have := congrArg Subtype.val hc
      simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg,
        AddSubgroup.coe_nsmul] at this
      rw [this]
      simp only [w, hy, smul_sub]
      abel
    have hd : Quotient.out x' - Quotient.out x = ((τ : F) / t) • (c.1 : hermE σ n) := by
      rw [div_eq_inv_mul, mul_smul, Nat.cast_smul_eq_nsmul F τ, hc', smul_smul,
        inv_mul_cancel₀ ht, one_smul]
    have hmemΛ : Quotient.out x' - Quotient.out x ∈ Λ := hd ▸ hΛ _ c.2
    rw [← QuotientAddGroup.out_eq' x, ← QuotientAddGroup.out_eq' x']
    apply QuotientAddGroup.eq.2
    rwa [neg_add_eq_sub]
  have hdnn : ∀ z : hermE σ n ⧸ hermO σ n,
      0 ≤ (delta (Quotient.out z).1 : ℝ) ^ (-s) := fun z => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hs := summable_comp_of_injective_prod hdnn hsum y q hinj
  refine Summable.of_nonneg_of_le (fun x => hg _) (fun x => ?_) (hs.mul_left |C|)
  have hdelta : delta (t • Quotient.out x).1 = delta (Quotient.out (y x)).1 := by
    have hl : ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (w x).1.1 a b := (w x).2
    rw [← delta_add (Quotient.out (y x)).1 (w x).1.1 hl]
    congr 1
    simp [w]
  refine (hb _).trans ?_
  rw [hdelta]
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (hdnn _)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
