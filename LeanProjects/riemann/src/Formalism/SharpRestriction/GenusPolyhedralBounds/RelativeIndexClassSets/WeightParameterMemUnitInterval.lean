import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndexDeterminant.NegLogValuation
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.ThreeForms
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsBasisOfPid

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.MainNotions.Gaps.LocalGlobalPassage

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.DivisionValues (vw conjPl)
open Formalism.EigenvalueLevelCeiling (lix cut sc IsLatIn plc)

structure Run (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) where

  jn : ℕ

  X : WeightAlgebra.PJ D B P jn

  S : WeightAlgebra.Scal B

  ka : WeightFamilies.Wt D jn

  wL : WeightFamilies.Wt D jn

  wF : WeightFamilies.Wt D jn

  T : ℕ

  nus : HeightOneSpectrum (𝓞 B.KO) → ℝ

  β : ℝ

namespace Run

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} (Q : Run D B P)

def Concl : Prop := WeightAlgebra.Concl Q.X Q.S Q.ka Q.wL Q.wF Q.T Q.nus Q.β

def M0 : Submodule (𝓞 B.KO) (B.Cusp Q.jn Q.ka) := B.Mlat Q.jn Q.ka

def Th0 : Submodule (𝓞 B.KO) (B.Cusp Q.jn Q.ka) :=
  (Q.X.Theta Q.S Q.ka Q.wL Q.wF Q.T).comap ((Q.X.inc Q.ka).restrictScalars (𝓞 B.KO))

def eLa (la : HeightOneSpectrum (𝓞 B.KO)) : ℤ := Q.X.eLa Q.T Q.nus la

theorem eLa_ge (la : HeightOneSpectrum (𝓞 B.KO)) : (Q.T : ℝ) * Q.nus la ≤ (Q.eLa la : ℝ) := by
  refine le_trans ?_ (Int.le_ceil _)
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  split_ifs <;> linarith

end Run

section Comparison₂

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def RemOK {n : ℕ} (v : HeightOneSpectrum (𝓞 K)) (M Th : Submodule (𝓞 K) (Fin n → K)) (E : ℕ) (ρ : ℝ) : Prop :=
  ∀ W : Submodule K (Fin n → K), (lix v (cut W M) (cut W Th) : ℝ) ≤ (E : ℝ) * (finrank K W : ℝ) + ρ

variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P' : Type} [Group P'] [Finite P'] {c : OnConst}

def rOf (O : OnObj S P' c) (k : Bool) (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : ℝ :=
  if k then O.r2 v j else O.r1 v j

def used (O : OnObj S P' c) (v : HeightOneSpectrum (𝓞 K)) : Bool := decide (plc v = O.pde)

structure TheoremZeroData (O : OnObj S P' c) {D : D7} (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) [Algebra B.KO K] where

  run : Bool → Bs.J → Run D B P

  ι : ∀ k j, B.Cusp (run k j).jn (run k j).ka →ₗ[B.KO] (Fin (O.nZ j) → K)

  ThR : Bool → HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (O.nZ j) → K)

  e0 : Bool → HeightOneSpectrum (𝓞 B.KO) → Bs.J → ℤ

  ER : Bool → HeightOneSpectrum (𝓞 K) → Bs.J → ℕ

  indep : ∀ k j (m : ℕ) (b : Fin m → B.Cusp (run k j).jn (run k j).ka),
    LinearIndependent B.KO b → LinearIndependent K fun a => ι k j (b a)

  isLattice_lattice : ∀ k j, Submodule.IsLattice B.KO (run k j).M0

  Ms_eq : ∀ k j, O.Ms j = Submodule.span (𝓞 K) (ι k j '' ((run k j).M0 : Set _))

  Ms_top : ∀ j, Submodule.span K (O.Ms j : Set (Fin (O.nZ j) → K)) = ⊤

  Th_le : ∀ k v j, Submodule.span (𝓞 K) (ι k j '' ((run k j).Th0 : Set _)) ≤ ThR k v j

  exponent_bound_ter : ∀ k la j, ((run k j).T : ℝ) * (run k j).nus la ≤ (e0 k la j : ℝ)

  E_le : ∀ k v j, (v.asIdeal.ramificationIdx (𝓞 B.KO) : ℤ) * e0 k (v.under (𝓞 B.KO)) j ≤ (ER k v j : ℤ)

  Th1_eq : ∀ v j, O.Th1 v j = ThR (used O v) v j

  E_used : ∀ v j, O.E v j = ER (used O v) v j

  Th1_ok : AtPair S fun v => ∀ j, (O.Th1 v j).FG ∧ O.Th1 v j ≤ O.Th v j

  a_ok : ∀ v j, O.a v j ≠ 0 ∧ vw v (O.a v j) = (O.E v j : ℤ)

  r_nonneg : ∀ k v j, 0 ≤ rOf O k v j

  r_le : ∀ k v j (ρ : ℝ), 0 ≤ ρ → RemOK v (O.Ms j) (ThR k v j) (ER k v j) ρ → rOf O k v j ≤ ρ

  r_ok : ∀ v j (ρ : ℝ), 0 ≤ ρ → RemOK v (O.Ms j) (O.Th1 v j) (O.E v j) ρ →
    RemOK v (O.Ms j) (O.Th1 v j) (O.E v j) (O.r v j)

  weight_parameter_mem_unit_interval : 0 ≤ O.de2 ∧ O.de2 ≤ 1

  budget : ∀ k j, (run k j).β ≤ (O.nZ j : ℝ) * (O.f * O.m * O.b * O.de2)

end Comparison₂

end Formalism.MainNotions.Gaps.LocalGlobalPassage

end

section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.MainNotions.Gaps.LocalGlobalPassage

open Formalism.HermitianLatticesTheory (lidx localization₂ locLen)

section Comp

variable {R K F : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup F] [Module K F] [Module R F] [IsScalarTower R K F] (v : HeightOneSpectrum R)

def bcC : F →ₗ[K] TensorProduct K (v.adicCompletion K) F := TensorProduct.mk K (v.adicCompletion K) F 1

def locC (N : Submodule R F) : Submodule (v.adicCompletionIntegers K) (TensorProduct K (v.adicCompletion K) F) :=
  Submodule.span (v.adicCompletionIntegers K) (bcC v '' (N : Set F))

def locKC (W : Submodule K F) : Submodule (v.adicCompletion K) (TensorProduct K (v.adicCompletion K) F) :=
  Submodule.span (v.adicCompletion K) (bcC v '' (W : Set F))

def LengthLocalizationLeCompletion : Prop :=
  ∀ (A T : Submodule R F) (W : Submodule K F),
    Module.length (v.adicCompletionIntegers K)
      (↥(locC v A ⊓ (locKC v W).restrictScalars (v.adicCompletionIntegers K)) ⧸
        (locC v T ⊓ (locKC v W).restrictScalars (v.adicCompletionIntegers K)).comap
          (locC v A ⊓ (locKC v W).restrictScalars (v.adicCompletionIntegers K)).subtype) ≠ ⊤ →
    Module.length R (↥(localization₂ v.asIdeal (A ⊓ W.restrictScalars R)) ⧸
        (localization₂ v.asIdeal (A ⊓ W.restrictScalars R ⊓ T)).comap (localization₂ v.asIdeal (A ⊓ W.restrictScalars R)).subtype) ≤
    Module.length (v.adicCompletionIntegers K)
      (↥(locC v A ⊓ (locKC v W).restrictScalars (v.adicCompletionIntegers K)) ⧸
        (locC v T ⊓ (locKC v W).restrictScalars (v.adicCompletionIntegers K)).comap
          (locC v A ⊓ (locKC v W).restrictScalars (v.adicCompletionIntegers K)).subtype)

def CompletionPreservesFinrank : Prop :=
  ∀ W : Submodule K F, FiniteDimensional K W → finrank (v.adicCompletion K) (locKC v W) = finrank K W

def CompletionSpanContainment : Prop :=
  ∀ (A : Submodule R F) (W : Submodule K F), W ≤ Submodule.span K (A : Set F) →
    locKC v W ≤ Submodule.span (v.adicCompletion K) (bcC v '' (A : Set F))

end Comp

section BC

variable {K0 K : Type} [Field K0] [NumberField K0] [Field K] [NumberField K] [Algebra K0 K]
  {Z0 : Type} [AddCommGroup Z0] [Module K0 Z0] [FiniteDimensional K0 Z0] [Module (𝓞 K0) Z0] [IsScalarTower (𝓞 K0) K0 Z0]
  {n : ℕ}

def up (ι : Z0 →ₗ[K0] (Fin n → K)) (A0 : Submodule (𝓞 K0) Z0) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.span (𝓞 K) (ι '' (A0 : Set Z0))

def IndexMulRamificationIndex (ι : Z0 →ₗ[K0] (Fin n → K)) : Prop :=
  (∀ (m : ℕ) (b : Fin m → Z0), LinearIndependent K0 b → LinearIndependent K fun a => ι (b a)) →
  Submodule.span K (Set.range ι) = ⊤ →
  ∀ A0 C0 : Submodule (𝓞 K0) Z0, A0.FG → Submodule.span K0 (A0 : Set Z0) = ⊤ → C0.FG →
    Submodule.span K0 (C0 : Set Z0) = ⊤ → ∀ v : HeightOneSpectrum (𝓞 K),
    lidx v.asIdeal (up ι A0) (up ι C0) =
      (v.asIdeal.ramificationIdx (𝓞 K0) : ℤ) * lidx (v.under (𝓞 K0)).asIdeal A0 C0

def ValuationMulRamificationIndex (K0 K : Type) [Field K0] [NumberField K0] [Field K] [NumberField K] [Algebra K0 K] : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 K)) (a : K0), a ≠ 0 →
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap K0 K a)) =
      (v.asIdeal.ramificationIdx (𝓞 K0) : ℤ) *
        FractionalIdeal.count K0 (v.under (𝓞 K0)) (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K0)) a)

def RamificationIndexNeZero (K0 K : Type) [Field K0] [NumberField K0] [Field K] [NumberField K] [Algebra K0 K] : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal.ramificationIdx (𝓞 K0) ≠ 0

def SumOverPlacesLeBaseSum (K0 K : Type) [Field K0] [NumberField K0] [Field K] [NumberField K] [Algebra K0 K] : Prop :=
  ∀ r : HeightOneSpectrum (𝓞 K0) → ℝ, (∀ la, 0 ≤ r la) → Summable (fun la => r la * Formalism.BasicNotions.lw K0 la) →
    ∀ S' : Finset (HeightOneSpectrum (𝓞 K)),
      ∑ v ∈ S', Formalism.BasicNotions.lw K v * ((v.asIdeal.ramificationIdx (𝓞 K0) : ℝ) * r (v.under (𝓞 K0))) ≤
        ∑' la, r la * Formalism.BasicNotions.lw K0 la

end BC

end Formalism.MainNotions.Gaps.LocalGlobalPassage

end

end

section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.MainNotions.Gaps.LocalGlobalPassage

open Formalism.HermitianLatticesTheory (lidx localization₂ locLen locS)

section CompP

variable {R K F : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup F] [Module K F] [Module R F] [IsScalarTower R K F] (v : HeightOneSpectrum R)

abbrev OOv : Subalgebra R K :=
  Localization.subalgebra.ofField K v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors

theorem mem_OOv (x : K) :
    x ∈ OOv (K := K) v ↔ ∃ (a s : R) (_ : s ∈ v.asIdeal.primeCompl),
      x = algebraMap R K a * (algebraMap R K s)⁻¹ :=
  Iff.rfl

theorem isDVR_OOv : IsDiscreteValuationRing (OOv (K := K) v) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot (OOv (K := K) v)

theorem alg_ne_zero {s : R} (hs : s ∉ v.asIdeal) : algebraMap R K s ≠ 0 := by
  intro h
  have : s = 0 := (IsFractionRing.injective R K) (by rw [h, map_zero])
  exact hs (this ▸ v.asIdeal.zero_mem)

theorem mem_localization_iff_mem_span' (M : Submodule R F) (x : F) :
    x ∈ localization₂ v.asIdeal M ↔ x ∈ Submodule.span (OOv (K := K) v) (M : Set F) := by
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hs0 := alg_ne_zero (K := K) v hs
    have hu : (algebraMap R K s)⁻¹ ∈ OOv (K := K) v := (mem_OOv v _).mpr ⟨1, s, hs, by simp⟩
    have hx : x = (⟨_, hu⟩ : OOv (K := K) v) • (s • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K s x, smul_smul]
      simp [hs0]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, Submonoid.one_mem _, by simpa using hy⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := hy
      obtain ⟨r, t, ht, hat⟩ := (mem_OOv v (a : K)).mp a.2
      refine ⟨t * s, mul_mem ht hs, ?_⟩
      have ht0 := alg_ne_zero (K := K) v ht
      have he : (t * s) • (a • y) = r • (s • y) := by
        rw [Subalgebra.smul_def, hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
          ← algebraMap_smul K s, smul_smul, smul_smul]
        congr 1
        rw [map_mul]
        field_simp
      rw [he]
      exact M.smul_mem r hsy

theorem val_alg (k : K) : Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  v.valuedAdicCompletion_eq_valuation' k

theorem mem_OOv_of_val {a : K} (h : v.valuation K a ≤ 1) : a ∈ OOv (K := K) v := by
  have := isDVR_OOv (K := K) v
  rcases ValuationRing.isInteger_or_isInteger (OOv (K := K) v) a with ⟨c, hc⟩ | ⟨c, hc⟩
  · rw [← hc]
    exact c.2
  · by_cases ha : a = 0
    · rw [ha]; exact Subalgebra.zero_mem _
    obtain ⟨r, s, hs, hrs⟩ := (mem_OOv v _).mp c.2
    have hc' : a⁻¹ = algebraMap R K r * (algebraMap R K s)⁻¹ := by
      rw [← hrs, ← hc]
      rfl
    have hs0 := alg_ne_zero (K := K) v hs
    by_cases hr : r ∈ v.asIdeal
    · exfalso
      have h1 : v.valuation K (algebraMap R K r) < 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap]; exact (v.intValuation_lt_one_iff_mem r).2 hr
      have h2 : v.valuation K (algebraMap R K s) = 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap]; exact (v.intValuation_eq_one_iff_mem_primeCompl s).2 hs
      have h3 : v.valuation K a⁻¹ < 1 := by
        rw [hc', map_mul, map_inv₀, h2, inv_one, mul_one]; exact h1
      have h4 : v.valuation K (a * a⁻¹) < 1 := by
        rw [map_mul]
        calc v.valuation K a * v.valuation K a⁻¹ ≤ 1 * v.valuation K a⁻¹ := mul_le_mul' h le_rfl
          _ = v.valuation K a⁻¹ := one_mul _
          _ < 1 := h3
      rw [mul_inv_cancel₀ ha, map_one] at h4
      exact lt_irrefl _ h4
    · have hr0 := alg_ne_zero (K := K) v hr
      refine (mem_OOv v _).mpr ⟨s, r, hr, ?_⟩
      rw [← inv_inv a, hc']
      field_simp

end CompP

section CompD

variable {R K F : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup F] [Module K F] [Module R F] [IsScalarTower R K F] (v : HeightOneSpectrum R)

theorem val_of_mem_OOv {a : K} (h : a ∈ OOv (K := K) v) : v.valuation K a ≤ 1 := by
  obtain ⟨r, s, hs, rfl⟩ := (mem_OOv v a).mp h
  have h2 : v.valuation K (algebraMap R K s) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]; exact (v.intValuation_eq_one_iff_mem_primeCompl s).2 hs
  rw [map_mul, map_inv₀, h2, inv_one, mul_one]
  exact v.valuation_le_one r

theorem bc_smul (k : K) (x : F) : bcC (K := K) v (k • x) = algebraMap K (v.adicCompletion K) k • bcC (K := K) v x := by
  rw [map_smul, algebraMap_smul]

theorem descent (T : Submodule R F) (y : F) (h : bcC (K := K) v y ∈ locC (K := K) v T) : y ∈ localization₂ v.asIdeal T := by
  classical
  have hdvr := isDVR_OOv (K := K) v
  obtain ⟨t', ht', hy'⟩ := Submodule.mem_span_finite_of_mem_span h
  obtain ⟨t, htT, rfl⟩ := Finset.subset_set_image_iff.1 ht'
  set L : Submodule (OOv (K := K) v) F := Submodule.span (OOv (K := K) v) (t : Set F) with hL
  have hfin : Module.Finite (OOv (K := K) v) L := Module.Finite.of_fg (Submodule.fg_span t.finite_toSet)
  have htf : Module.IsTorsionFree (OOv (K := K) v) L := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
    have h1 : ((r : K)) • (m : F) = 0 := congrArg Subtype.val h
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl (Subtype.ext h2)
    · exact Or.inr (Subtype.ext h2)
  have hfree : Module.Free (OOv (K := K) v) L := Module.free_of_finite_type_torsion_free'
  let u := Module.Free.chooseBasis (OOv (K := K) v) L
  let u' : Module.Free.ChooseBasisIndex (OOv (K := K) v) L → F := fun i => (u i : F)
  have hli0 : LinearIndependent (OOv (K := K) v) u' :=
    u.linearIndependent.map' L.subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent K u' := (LinearIndependent.iff_fractionRing (OOv (K := K) v) K).1 hli0
  have hspan : Submodule.span (OOv (K := K) v) (Set.range u') = L := by
    have e : Set.range u' = L.subtype '' Set.range u := by
      rw [← Set.range_comp]; rfl
    rw [e, Submodule.span_image, u.span_eq, Submodule.map_top, Submodule.range_subtype]
  let b := Module.Basis.extend hli.linearIndepOn_id
  let bh := b.baseChange (v.adicCompletion K)

  have hPF : ∀ x ∈ L, ∀ i, b.repr x i ∈ OOv (K := K) v ∧ ((i : F) ∉ Set.range u' → b.repr x i = 0) := by
    intro x hx
    rw [← hspan] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro i
      have hx' := Module.Basis.subset_extend hli.linearIndepOn_id hx
      have e : x = b ⟨x, hx'⟩ := (Module.Basis.extend_apply_self hli.linearIndepOn_id ⟨x, hx'⟩).symm
      rw [e, b.repr_self, Finsupp.single_apply]
      split_ifs with hi
      · exact ⟨Subalgebra.one_mem _, fun h => absurd (hi ▸ hx) h⟩
      · exact ⟨Subalgebra.zero_mem _, fun _ => rfl⟩
    | zero => intro i; simp
    | add x z _ _ hx hz =>
      intro i
      rw [map_add, Finsupp.add_apply]
      exact ⟨Subalgebra.add_mem _ (hx i).1 (hz i).1, fun h => by rw [(hx i).2 h, (hz i).2 h, add_zero]⟩
    | smul a x _ hx =>
      intro i
      rw [Subalgebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact ⟨Subalgebra.mul_mem _ a.2 (hx i).1, fun h => by rw [(hx i).2 h, mul_zero]⟩

  have hPH : ∀ z ∈ Submodule.span (v.adicCompletionIntegers K) ((t.image (bcC (K := K) v) : Finset _) : Set _),
      ∀ i, Valued.v (bh.repr z i) ≤ 1 ∧ ((i : F) ∉ Set.range u' → bh.repr z i = 0) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      intro i
      rw [Finset.coe_image] at hz
      obtain ⟨τ, hτ, rfl⟩ := hz
      have h1 := hPF τ (Submodule.subset_span hτ) i
      have e : bh.repr (bcC (K := K) v τ) i = algebraMap K (v.adicCompletion K) (b.repr τ i) := by
        show bh.repr ((1 : v.adicCompletion K) ⊗ₜ[K] τ) i = _
        rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
      rw [e, val_alg]
      exact ⟨val_of_mem_OOv v h1.1, fun h => by rw [h1.2 h, map_zero]⟩
    | zero => intro i; simp
    | add x z _ _ hx hz =>
      intro i
      rw [map_add, Finsupp.add_apply]
      exact ⟨Valuation.map_add_le _ (hx i).1 (hz i).1, fun h => by rw [(hx i).2 h, (hz i).2 h, add_zero]⟩
    | smul a x _ hx =>
      intro i
      have e : a • x = (a : v.adicCompletion K) • x := rfl
      rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
      exact ⟨mul_le_one' ((HeightOneSpectrum.mem_adicCompletionIntegers R K v).1 a.2) (hx i).1,
        fun h => by rw [(hx i).2 h, mul_zero]⟩
  have hy := hPH _ hy'
  have e : ∀ i, bh.repr (bcC (K := K) v y) i = algebraMap K (v.adicCompletion K) (b.repr y i) := by
    intro i
    show bh.repr ((1 : v.adicCompletion K) ⊗ₜ[K] y) i = _
    rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  have hyL : y ∈ L := by
    rw [← b.linearCombination_repr y, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 := hy i
    rw [e i, val_alg] at h1
    by_cases hi : (i : F) ∈ Set.range u'
    · have h2 := mem_OOv_of_val v h1.1
      have e2 : b.repr y i • b i = (⟨_, h2⟩ : OOv (K := K) v) • (i : F) := by
        rw [Subalgebra.smul_def, Module.Basis.extend_apply_self]
      rw [e2]
      exact hspan.le (Submodule.smul_mem _ _ (Submodule.subset_span hi))
    · have h3 := h1.2 hi
      have h4 : b.repr y i = 0 := (algebraMap K (v.adicCompletion K)).injective (by rw [h3, map_zero])
      rw [h4, zero_smul]
      exact Submodule.zero_mem _
  have h5 : y ∈ Submodule.span (OOv (K := K) v) ((Submodule.span R (t : Set F) : Submodule R F) : Set F) :=
    Submodule.span_mono Submodule.subset_span hyL
  have h6 := (mem_localization_iff_mem_span' (K := K) v _ y).2 h5
  obtain ⟨s, hs, hsy⟩ := h6
  exact ⟨s, hs, (Submodule.span_le.2 htT) hsy⟩

end CompD

section CompA

variable {R K F : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup F] [Module K F] [Module R F] [IsScalarTower R K F] (v : HeightOneSpectrum R)

theorem coe_algO (r : R) : ((algebraMap R (v.adicCompletionIntegers K) r : v.adicCompletionIntegers K) : v.adicCompletion K) =
    algebraMap K (v.adicCompletion K) (algebraMap R K r) := rfl

theorem exists_inv_mod (n : ℕ) {s : R} (hs : s ∉ v.asIdeal) : ∃ t : R, 1 - s * t ∈ v.asIdeal ^ n := by
  obtain ⟨y, i, hi, hyi⟩ := v.isMaximal.exists_inv hs
  obtain ⟨w, hw⟩ := sub_dvd_pow_sub_pow (1 : R) i n
  refine ⟨y * w, ?_⟩
  have e : 1 - s * (y * w) = i ^ n := by
    have h1 : (1 : R) - i = y * s := by rw [← hyi]; ring
    rw [h1, one_pow] at hw
    linear_combination hw
  rw [e]
  exact Ideal.pow_mem_pow hi n

theorem approx (c : v.adicCompletionIntegers K) (n : ℕ) :
    ∃ r : R, Valued.v ((c : v.adicCompletion K) - algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤
      WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  set p : v.adicCompletion K := algebraMap K (v.adicCompletion K) (algebraMap R K π) with hp
  have hpv : Valued.v p = WithZero.exp (-1 : ℤ) := by
    rw [hp, val_alg, HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hpn : Valued.v (p ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hpv, ← WithZero.exp_nsmul]; congr 1; simp
  have hopen : IsOpen {x : v.adicCompletion K |
      (x - (c : v.adicCompletion K)) * (p ^ n)⁻¹ ∈ (Valued.v.valuationSubring : ValuationSubring (v.adicCompletion K))} :=
    (Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage
      ((continuous_sub_right _).mul continuous_const)
  obtain ⟨k, hk⟩ := (v.denseRange_algebraMap K).exists_mem_open hopen ⟨c, by simp⟩
  have hk' : Valued.v (algebraMap K (v.adicCompletion K) k - (c : v.adicCompletion K)) ≤ WithZero.exp (-(n : ℤ)) := by
    have h1 : Valued.v ((algebraMap K (v.adicCompletion K) k - (c : v.adicCompletion K)) * (p ^ n)⁻¹) ≤ 1 :=
      (Valuation.mem_valuationSubring_iff _ _).1 hk
    rw [map_mul, map_inv₀, hpn] at h1
    have h2 := mul_le_mul' h1 (le_refl (WithZero.exp (-(n : ℤ))))
    rwa [mul_assoc, inv_mul_cancel₀ WithZero.exp_ne_zero, mul_one, one_mul] at h2
  have hle1 : WithZero.exp (-(n : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have hk1 : v.valuation K k ≤ 1 := by
    rw [← val_alg]
    have e : algebraMap K (v.adicCompletion K) k = (algebraMap K (v.adicCompletion K) k - c) + c := by ring
    rw [e]
    exact Valuation.map_add_le _ (hk'.trans hle1) ((HeightOneSpectrum.mem_adicCompletionIntegers R K v).1 c.2)
  obtain ⟨a, s, hs, rfl⟩ := (mem_OOv v k).mp (mem_OOv_of_val v hk1)
  obtain ⟨t, ht⟩ := exists_inv_mod v n hs
  refine ⟨a * t, ?_⟩
  have hs0 := alg_ne_zero (K := K) v hs
  have e1 : algebraMap R K a * (algebraMap R K s)⁻¹ - algebraMap R K (a * t) =
      algebraMap R K a * algebraMap R K (1 - s * t) * (algebraMap R K s)⁻¹ := by
    simp only [map_mul, map_sub, map_one]
    field_simp
  have h2 : v.valuation K (algebraMap R K s) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]; exact (v.intValuation_eq_one_iff_mem_primeCompl s).2 hs
  have h3 : v.valuation K (algebraMap R K a * (algebraMap R K s)⁻¹ - algebraMap R K (a * t)) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [e1, map_mul, map_mul, map_inv₀, h2, inv_one, mul_one]
    calc v.valuation K (algebraMap R K a) * v.valuation K (algebraMap R K (1 - s * t))
        ≤ 1 * WithZero.exp (-(n : ℤ)) := by
          refine mul_le_mul' (v.valuation_le_one a) ?_
          rw [HeightOneSpectrum.valuation_of_algebraMap]
          exact (v.intValuation_le_pow_iff_mem _ n).2 ht
      _ = _ := one_mul _
  have e2 : (c : v.adicCompletion K) - algebraMap K (v.adicCompletion K) (algebraMap R K (a * t)) =
      -(algebraMap K (v.adicCompletion K) (algebraMap R K a * (algebraMap R K s)⁻¹) - c) +
        algebraMap K (v.adicCompletion K) (algebraMap R K a * (algebraMap R K s)⁻¹ - algebraMap R K (a * t)) := by
    rw [map_sub]; ring
  rw [e2]
  refine Valuation.map_add_le _ ?_ ?_
  · rw [Valuation.map_neg]; exact hk'
  · rw [val_alg]; exact h3

theorem bc_smulR (r : R) (x : F) :
    bcC (K := K) v (r • x) = algebraMap R (v.adicCompletionIntegers K) r • bcC (K := K) v x := by
  have e : algebraMap R (v.adicCompletionIntegers K) r • bcC (K := K) v x =
      ((algebraMap R (v.adicCompletionIntegers K) r : v.adicCompletionIntegers K) : v.adicCompletion K) •
        bcC (K := K) v x := rfl
  rw [e, coe_algO, ← bc_smul, algebraMap_smul]

theorem isUnit_algO {s : R} (hs : s ∉ v.asIdeal) : IsUnit (algebraMap R (v.adicCompletionIntegers K) s) := by
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one, coe_algO, val_alg,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_eq_one_iff_mem_primeCompl s).2 hs

theorem bc_mem_locC (N : Submodule R F) {x : F} (hx : x ∈ localization₂ v.asIdeal N) : bcC (K := K) v x ∈ locC (K := K) v N := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨u, hu⟩ := isUnit_algO (K := K) v hs
  have h1 : bcC (K := K) v (s • x) ∈ locC (K := K) v N := Submodule.subset_span ⟨_, hsx, rfl⟩
  rw [bc_smulR, ← hu] at h1
  have h2 := (locC (K := K) v N).smul_mem (↑u⁻¹ : v.adicCompletionIntegers K) h1
  rwa [smul_smul, Units.inv_mul, one_smul] at h2

theorem exists_factor {π : R} (hπ : v.intValuation π = WithZero.exp (-1 : ℤ)) (n : ℕ) (d : v.adicCompletionIntegers K)
    (hd : Valued.v (d : v.adicCompletion K) ≤ WithZero.exp (-(n : ℤ))) :
    ∃ d' : v.adicCompletionIntegers K, d = algebraMap R (v.adicCompletionIntegers K) π ^ n * d' := by
  set p : v.adicCompletion K := algebraMap K (v.adicCompletion K) (algebraMap R K π) with hp
  have hpv : Valued.v p = WithZero.exp (-1 : ℤ) := by
    rw [hp, val_alg, HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, map_zero] at hpv
    exact WithZero.exp_ne_zero hpv.symm
  have hpn : Valued.v (p ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hpv, ← WithZero.exp_nsmul]; congr 1; simp
  have hmem : (d : v.adicCompletion K) * (p ^ n)⁻¹ ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hpn]
    calc Valued.v (d : v.adicCompletion K) * (WithZero.exp (-(n : ℤ)))⁻¹
        ≤ WithZero.exp (-(n : ℤ)) * (WithZero.exp (-(n : ℤ)))⁻¹ := mul_le_mul' hd le_rfl
      _ = 1 := mul_inv_cancel₀ WithZero.exp_ne_zero
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  show (d : v.adicCompletion K) = p ^ n * ((d : v.adicCompletion K) * (p ^ n)⁻¹)
  field_simp

end CompA

section CompM

variable {R K F : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup F] [Module K F] [Module R F] [IsScalarTower R K F] (v : HeightOneSpectrum R)

theorem mem_of_mem_localization_restrictScalars (W : Submodule K F) {x : F} (hx : x ∈ localization₂ v.asIdeal (W.restrictScalars R)) : x ∈ W := by
  obtain ⟨s, hs, hsx⟩ := hx
  have hs0 := alg_ne_zero (K := K) v hs
  have h1 : algebraMap R K s • x ∈ W := by rw [algebraMap_smul]; exact hsx
  have h2 := W.smul_mem (algebraMap R K s)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hs0, one_smul] at h2

theorem l1 : LengthLocalizationLeCompletion (K := K) (F := F) v := by
  intro A T W hfin
  set Ah := locC (K := K) v A ⊓ (locKC v W).restrictScalars (v.adicCompletionIntegers K) with hAh
  set Th := locC (K := K) v T ⊓ (locKC v W).restrictScalars (v.adicCompletionIntegers K) with hTh
  set A' := localization₂ v.asIdeal (A ⊓ W.restrictScalars R) with hA'
  set B' := localization₂ v.asIdeal (A ⊓ W.restrictScalars R ⊓ T) with hB'
  have hW : ∀ x ∈ A', x ∈ W := fun x hx =>
    mem_of_mem_localization_restrictScalars v W (Formalism.HermitianLatticesTheory.locBasic_locS_mono _ inf_le_right hx)
  have hmem : ∀ x ∈ A', bcC (K := K) v x ∈ Ah := fun x hx =>
    ⟨bc_mem_locC v A (Formalism.HermitianLatticesTheory.locBasic_locS_mono _ inf_le_left hx), Submodule.subset_span ⟨x, hW x hx, rfl⟩⟩
  let g : A' → (Ah ⧸ Th.comap Ah.subtype) := fun x => Submodule.Quotient.mk ⟨bcC (K := K) v x, hmem x x.2⟩
  have g_add : ∀ x y, g (x + y) = g x + g y := by
    intro x y
    have e : (⟨bcC (K := K) v ((x + y : A') : F), hmem _ (x + y).2⟩ : Ah) =
        ⟨bcC (K := K) v (x : F), hmem x x.2⟩ + ⟨bcC (K := K) v (y : F), hmem y y.2⟩ :=
      Subtype.ext (map_add (bcC (K := K) v) (x : F) (y : F))
    show Submodule.Quotient.mk _ = _
    rw [e]
    rfl
  have g_zero : g 0 = 0 := by
    have e : (⟨bcC (K := K) v ((0 : A') : F), hmem _ (0 : A').2⟩ : Ah) = 0 :=
      Subtype.ext (map_zero (bcC (K := K) v))
    show Submodule.Quotient.mk _ = _
    rw [e]
    rfl
  have g_smul : ∀ (r : R) x, g (r • x) = algebraMap R (v.adicCompletionIntegers K) r • g x := by
    intro r x
    have e : (⟨bcC (K := K) v ((r • x : A') : F), hmem _ (r • x).2⟩ : Ah) =
        algebraMap R (v.adicCompletionIntegers K) r • ⟨bcC (K := K) v (x : F), hmem x x.2⟩ :=
      Subtype.ext (bc_smulR (K := K) v r (x : F))
    show Submodule.Quotient.mk _ = _
    rw [e]
    rfl
  have g_ker : ∀ x y, g x = g y → ((x : F) - (y : F)) ∈ B' := by
    intro x y h
    have h1 := (Submodule.Quotient.eq _).1 h
    have h2 : bcC (K := K) v (x : F) - bcC (K := K) v (y : F) ∈ Th := h1
    rw [← map_sub] at h2
    have h3 := descent v T _ h2.1
    have h4 : ((x : F) - (y : F)) ∈ A' := A'.sub_mem x.2 y.2
    have h5 : ((x : F) - (y : F)) ∈ locS v.asIdeal.primeCompl (A ⊓ W.restrictScalars R) ⊓
        locS v.asIdeal.primeCompl T := ⟨h4, h3⟩
    rw [← Formalism.HermitianLatticesTheory.locBasic_locS_inf] at h5
    exact h5

  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  have hπm : algebraMap R (v.adicCompletionIntegers K) π ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one, coe_algO, val_alg,
      HeightOneSpectrum.valuation_of_algebraMap, hπ, ← WithZero.exp_zero]
    intro h
    have := WithZero.exp_injective h
    omega
  obtain ⟨n, hn⟩ := Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.exists_pow_smul_eq_zero (v.adicCompletionIntegers K) _ hπm
    (Ah ⧸ Th.comap Ah.subtype) (Module.length_ne_top_iff.1 hfin)
  have hact : ∀ (c : v.adicCompletionIntegers K), ∃ r : R, ∀ q : (Ah ⧸ Th.comap Ah.subtype),
      c • q = algebraMap R (v.adicCompletionIntegers K) r • q := by
    intro c
    obtain ⟨r, hr⟩ := approx v c n
    obtain ⟨d', hd'⟩ := exists_factor v hπ n (c - algebraMap R (v.adicCompletionIntegers K) r) hr
    refine ⟨r, fun q => ?_⟩
    have e : c = algebraMap R (v.adicCompletionIntegers K) r +
        d' * algebraMap R (v.adicCompletionIntegers K) π ^ n := by
      rw [mul_comm, ← hd']; ring
    conv_lhs => rw [e]
    rw [add_smul, mul_smul, hn, smul_zero, add_zero]
  let Φ : Submodule R (A' ⧸ B'.comap A'.subtype) → Submodule (v.adicCompletionIntegers K) (Ah ⧸ Th.comap Ah.subtype) :=
    fun N =>
    { carrier := g '' (N.comap (B'.comap A'.subtype).mkQ : Set A')
      zero_mem' := ⟨0, Submodule.zero_mem _, g_zero⟩
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, Submodule.add_mem _ hx hy, g_add x y⟩
      smul_mem' := by
        rintro c _ ⟨x, hx, rfl⟩
        obtain ⟨r, hr⟩ := hact c
        exact ⟨r • x, Submodule.smul_mem _ r hx, by rw [g_smul, hr]⟩ }
  have hΦ : StrictMono Φ := by
    refine strictMono_of_le_iff_le fun N N' => ⟨fun h => ?_, fun h => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, Submodule.comap_mono h hx, rfl⟩
    · intro q hq
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have h1 : g x ∈ Φ N := ⟨x, hq, rfl⟩
      obtain ⟨y, hy, hxy⟩ := h h1
      have h2 := g_ker y x hxy
      have h3 : (Submodule.Quotient.mk y : A' ⧸ B'.comap A'.subtype) = Submodule.Quotient.mk x :=
        (Submodule.Quotient.eq _).2 h2
      rw [← h3]
      exact hy
  rw [Module.length_eq_height, Module.length_eq_height]
  exact (Order.height_le_height_apply_of_strictMono Φ hΦ ⊤).trans (Order.height_mono le_top)

end CompM

end Formalism.MainNotions.Gaps.LocalGlobalPassage

end

end

section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.MainNotions.Gaps.LocalGlobalPassage

theorem exists_vw_eq {K : Type} [Field K] [NumberField K] [StarRing K] (v : HeightOneSpectrum (𝓞 K)) (E : ℕ) :
    ∃ a : K, a ≠ 0 ∧ Formalism.DivisionValues.vw v a = (E : ℤ) := by
  obtain ⟨ϖ, -, hϖ0, hϖ1, -⟩ := Formalism.DivisionValues.idxChange_unif (K := K) v
  have h0 : algebraMap (𝓞 K) K ϖ ≠ 0 := by
    simpa using hϖ0
  have h1 : Formalism.DivisionValues.vw v (algebraMap (𝓞 K) K ϖ) = 1 := hϖ1
  refine ⟨algebraMap (𝓞 K) K ϖ ^ E, pow_ne_zero _ h0, ?_⟩
  induction E with
  | zero =>
    rw [pow_zero]
    exact Formalism.DivisionValues.idxChange_cnt_one v
  | succ n ih =>
    have h2 : Formalism.DivisionValues.vw v (algebraMap (𝓞 K) K ϖ ^ n * algebraMap (𝓞 K) K ϖ) =
        Formalism.DivisionValues.vw v (algebraMap (𝓞 K) K ϖ ^ n) + Formalism.DivisionValues.vw v (algebraMap (𝓞 K) K ϖ) :=
      Formalism.DivisionValues.idxChange_cnt_mul v (pow_ne_zero _ h0) h0
    rw [pow_succ, h2, ih, h1]
    push_cast
    ring

section Comp

variable {R K F : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup F] [Module K F] [Module R F] [IsScalarTower R K F] (v : HeightOneSpectrum R)

theorem l1c : CompletionSpanContainment (K := K) (F := F) v := by
  intro A W hW
  unfold locKC
  rw [Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  have h : Submodule.span K (A : Set F) ≤
      ((Submodule.span (v.adicCompletion K) (bcC v '' (A : Set F))).restrictScalars K).comap (bcC v) := by
    rw [Submodule.span_le]
    intro x hx
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  exact h (hW hw)

theorem l1b : CompletionPreservesFinrank (K := K) (F := F) v := by
  intro W hWf
  have hinj : Function.Injective (LinearMap.baseChange (v.adicCompletion K) W.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap W.subtype W.injective_subtype
  have hr : LinearMap.range (LinearMap.baseChange (v.adicCompletion K) W.subtype) = locKC v W := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a w =>
        have e : LinearMap.baseChange (v.adicCompletion K) W.subtype (a ⊗ₜ[K] w) = a • bcC v (w : F) := by
          simp [bcC, TensorProduct.smul_tmul']
        rw [e]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, w.2, rfl⟩)
      | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy
    · unfold locKC
      rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨(1 : v.adicCompletion K) ⊗ₜ[K] (⟨w, hw⟩ : W), by simp [bcC]⟩
  rw [← hr, LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]

end Comp

end Formalism.MainNotions.Gaps.LocalGlobalPassage

end

end

section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.MainNotions.Gaps.LocalGlobalPassage

open Formalism.HermitianLatticesTheory (lidx localization₂ locLen locS)
open Formalism.EigenvalueLevelCeiling.ThreeFormsAlt (OO isDVR_OO mem_localization_iff_mem_span)

section LocBasis

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]

theorem exists_loc_basis (w : HeightOneSpectrum (𝓞 K)) (A : Submodule (𝓞 K) Z) (hfg : A.FG)
    (hA : Submodule.span K (A : Set Z) = ⊤) :
    ∃ b : Basis (Fin (finrank K Z)) K Z,
      localization₂ w.asIdeal A = localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range b)) :=
  _root_.UpperTheory.Reformulated.B.Qi33.exists_loc_basis w A hfg hA

end LocBasis

section StructureSheafH2BaseChange

open Formalism.HermitianLatticesTheory

variable {K0 K : Type} [Field K0] [NumberField K0] [Field K] [NumberField K] [Algebra K0 K]
  {Z0 : Type} [AddCommGroup Z0] [Module K0 Z0] [FiniteDimensional K0 Z0] [Module (𝓞 K0) Z0] [IsScalarTower (𝓞 K0) K0 Z0]
  {n : ℕ}

theorem iota_smul (ι : Z0 →ₗ[K0] (Fin n → K)) (s : 𝓞 K0) (x : Z0) :
    ι (s • x) = (algebraMap (𝓞 K0) (𝓞 K) s) • ι x := by
  rw [← algebraMap_smul K0 s x, map_smul, ← algebraMap_smul K (algebraMap (𝓞 K0) (𝓞 K) s) (ι x),
    ← algebraMap_smul K (algebraMap (𝓞 K0) K0 s) (ι x)]
  congr 1

theorem up_le_locP (ι : Z0 →ₗ[K0] (Fin n → K)) (v : HeightOneSpectrum (𝓞 K)) {A0 B0 : Submodule (𝓞 K0) Z0}
    (h : A0 ≤ localization₂ (v.under (𝓞 K0)).asIdeal B0) : up ι A0 ≤ localization₂ v.asIdeal (up ι B0) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨s, hs, hsx⟩ := h hx
  refine ⟨algebraMap (𝓞 K0) (𝓞 K) s, ?_, ?_⟩
  · intro hmem
    exact hs hmem
  · rw [← iota_smul]
    exact Submodule.subset_span ⟨_, hsx, rfl⟩

theorem localization_up_congr (ι : Z0 →ₗ[K0] (Fin n → K)) (v : HeightOneSpectrum (𝓞 K)) {A0 B0 : Submodule (𝓞 K0) Z0}
    (h : localization₂ (v.under (𝓞 K0)).asIdeal A0 = localization₂ (v.under (𝓞 K0)).asIdeal B0) :
    localization₂ v.asIdeal (up ι A0) = localization₂ v.asIdeal (up ι B0) := by
  have key : ∀ {X Y : Submodule (𝓞 K0) Z0},
      localization₂ (v.under (𝓞 K0)).asIdeal X = localization₂ (v.under (𝓞 K0)).asIdeal Y →
      localization₂ v.asIdeal (up ι X) ≤ localization₂ v.asIdeal (up ι Y) := by
    intro X Y hXY
    have h1 : X ≤ localization₂ (v.under (𝓞 K0)).asIdeal Y := by
      rw [← hXY]; exact locBasic_le_locS _ X
    have h2 := locBasic_locS_mono v.asIdeal.primeCompl (up_le_locP ι v h1)
    rwa [show locS v.asIdeal.primeCompl (localization₂ v.asIdeal (up ι Y)) = localization₂ v.asIdeal (up ι Y) from
      locBasic_locS_idem _ _] at h2
  exact le_antisymm (key h) (key h.symm)

theorem up_span_range (ι : Z0 →ₗ[K0] (Fin n → K)) {I : Type} (a : I → Z0) :
    up ι (Submodule.span (𝓞 K0) (Set.range a)) = Submodule.span (𝓞 K) (Set.range fun i => ι (a i)) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul s y _ hy => rw [iota_smul]; exact Submodule.smul_mem _ _ hy
  · refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨a i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩

end StructureSheafH2BaseChange

section Main

open Formalism.HermitianLatticesTheory

variable {K0 K : Type} [Field K0] [NumberField K0] [Field K] [NumberField K] [Algebra K0 K]
  {Z0 : Type} [AddCommGroup Z0] [Module K0 Z0] [FiniteDimensional K0 Z0] [Module (𝓞 K0) Z0] [IsScalarTower (𝓞 K0) K0 Z0]
  {n : ℕ}

theorem iota_eq_sum (ι : Z0 →ₗ[K0] (Fin n → K)) {d : ℕ} (b : Basis (Fin d) K0 Z0) (z : Z0) :
    ι z = ∑ i, algebraMap K0 K (b.repr z i) • ι (b i) := by
  conv_lhs => rw [← b.sum_repr z, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, algebraMap_smul]

theorem span_iota_basis (ι : Z0 →ₗ[K0] (Fin n → K)) (htop : Submodule.span K (Set.range ι) = ⊤) {d : ℕ}
    (b : Basis (Fin d) K0 Z0) : ⊤ ≤ Submodule.span K (Set.range fun i => ι (b i)) := by
  rw [← htop]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨z, rfl⟩
  rw [iota_eq_sum ι b z]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem l3 (h3a : ValuationMulRamificationIndex K0 K) (ι : Z0 →ₗ[K0] (Fin n → K)) : IndexMulRamificationIndex ι := by
  intro hind htop A0 C0 hAfg hA hCfg hC v
  let _ : StarRing K0 := starRingOfComm
  obtain ⟨a, ha⟩ := exists_loc_basis (v.under (𝓞 K0)) A0 hAfg hA
  obtain ⟨c, hc⟩ := exists_loc_basis (v.under (𝓞 K0)) C0 hCfg hC
  let aK : Basis (Fin (finrank K0 Z0)) K (Fin n → K) :=
    Basis.mk (hind _ a a.linearIndependent) (span_iota_basis ι htop a)
  let cK : Basis (Fin (finrank K0 Z0)) K (Fin n → K) :=
    Basis.mk (hind _ c c.linearIndependent) (span_iota_basis ι htop c)
  have haK : ∀ i, aK i = ι (a i) := fun i => Basis.mk_apply _ _ i
  have hcK : ∀ i, cK i = ι (c i) := fun i => Basis.mk_apply _ _ i
  let γ0 : Z0 ≃ₗ[K0] Z0 := a.equiv c (Equiv.refl _)
  let γ : (Fin n → K) ≃ₗ[K] (Fin n → K) := aK.equiv cK (Equiv.refl _)
  have hγ0 : ∀ i, γ0 (a i) = c i := fun i => by simp [γ0]
  have hγ : ∀ i, γ (aK i) = cK i := fun i => by simp [γ]
  have hL : lidx (v.under (𝓞 K0)).asIdeal A0 C0 =
      FractionalIdeal.count K0 (v.under (𝓞 K0))
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K0)) (LinearMap.det (γ0 : Z0 →ₗ[K0] Z0))) := by
    rw [PI.LatIdxDetW.lidx_congr _ ha hc, ← PI.LatIdxDetW.lidx_free (v.under (𝓞 K0)) a γ0]
    congr 1
    rw [Submodule.map_span, ← Set.range_comp]
    refine congrArg (Submodule.span (𝓞 K0)) (congrArg Set.range ?_)
    funext i
    exact (hγ0 i).symm
  have hR : lidx v.asIdeal (up ι A0) (up ι C0) =
      FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (LinearMap.det (γ : (Fin n → K) →ₗ[K] (Fin n → K)))) := by
    have h1 := localization_up_congr ι v ha
    have h2 := localization_up_congr ι v hc
    rw [up_span_range] at h1 h2
    have e1 : (Set.range fun i => ι (a i)) = Set.range aK := by
      congr 1; funext i; exact (haK i).symm
    have e2 : (Set.range fun i => ι (c i)) = Set.range cK := by
      congr 1; funext i; exact (hcK i).symm
    rw [e1] at h1
    rw [e2] at h2
    rw [PI.LatIdxDetW.lidx_congr _ h1 h2, ← PI.LatIdxDetW.lidx_free v aK γ]
    congr 1
    rw [Submodule.map_span, ← Set.range_comp]
    refine congrArg (Submodule.span (𝓞 K)) (congrArg Set.range ?_)
    funext i
    exact (hγ i).symm
  have hrepr : ∀ (z : Z0) (i : Fin (finrank K0 Z0)), aK.repr (ι z) i = algebraMap K0 K (a.repr z i) := by
    intro z i
    have h1 : ι z = ∑ i, algebraMap K0 K (a.repr z i) • aK i := by
      rw [iota_eq_sum ι a z]
      exact Finset.sum_congr rfl fun i _ => by rw [haK]
    rw [h1, Basis.repr_sum_self]
  have hdet : LinearMap.det (γ : (Fin n → K) →ₗ[K] (Fin n → K)) =
      algebraMap K0 K (LinearMap.det (γ0 : Z0 →ₗ[K0] Z0)) := by
    rw [← LinearMap.det_toMatrix aK, ← LinearMap.det_toMatrix a, RingHom.map_det]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    show aK.repr (γ (aK j)) i = algebraMap K0 K (a.repr (γ0 (a j)) i)
    rw [hγ, hγ0, hcK, hrepr]
  rw [hL, hR, hdet]
  exact h3a v _ (LinearEquiv.isUnit_det' γ0).ne_zero

end Main

end Formalism.MainNotions.Gaps.LocalGlobalPassage

end

end

section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.MainNotions.Gaps.LocalGlobalPassage

section BC4

variable {K0 K : Type} [Field K0] [NumberField K0] [Field K] [NumberField K] [Algebra K0 K]

theorem liesOver_under (v : HeightOneSpectrum (𝓞 K)) : v.asIdeal.LiesOver (v.under (𝓞 K0)).asIdeal :=
  ⟨by rw [HeightOneSpectrum.under_asIdeal]⟩

theorem ram_eq (v : HeightOneSpectrum (𝓞 K)) :
    (v.under (𝓞 K0)).asIdeal.ramificationIdx' v.asIdeal = v.asIdeal.ramificationIdx (𝓞 K0) := by
  have := liesOver_under (K0 := K0) v
  exact Ideal.ramificationIdx'_eq_ramificationIdx _ _ (v.under (𝓞 K0)).ne_bot

theorem l3e : RamificationIndexNeZero K0 K := fun v => by
  have := liesOver_under (K0 := K0) v
  rw [← ram_eq]
  exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v.asIdeal (v.under (𝓞 K0)).ne_bot

theorem l3a : ValuationMulRamificationIndex K0 K := fun v a ha => by
  have := liesOver_under (K0 := K0) v
  have ha' : algebraMap K0 K a ≠ 0 := by simpa using ha
  rw [← PI.LatIdxDetW.neg_log_valuation v ha', ← PI.LatIdxDetW.neg_log_valuation (v.under (𝓞 K0)) ha,
    ← HeightOneSpectrum.valuation_liesOver K (v.under (𝓞 K0)) v a, WithZero.log_pow, ram_eq]
  simp

theorem lw_eq (v : HeightOneSpectrum (𝓞 K)) :
    Formalism.BasicNotions.lw K v = (v.asIdeal.inertiaDeg (𝓞 K0) : ℝ) *
      Real.log (Ideal.absNorm (v.under (𝓞 K0)).asIdeal : ℝ) / (finrank ℚ K : ℝ) := by
  have := liesOver_under (K0 := K0) v
  unfold Formalism.BasicNotions.lw
  rw [← Ideal.absNorm_pow_inertiaDeg (v.under (𝓞 K0)).asIdeal v.asIdeal, Nat.cast_pow, Real.log_pow]

theorem sum_ef_le (la : HeightOneSpectrum (𝓞 K0)) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∈ T, v.under (𝓞 K0) = la) :
    ∑ v ∈ T, v.asIdeal.ramificationIdx (𝓞 K0) * v.asIdeal.inertiaDeg (𝓞 K0) ≤ finrank K0 K := by
  classical
  let _ : Fintype (la.asIdeal.primesOver (𝓞 K)) := Fintype.ofFinite _
  have h := Ideal.sum_ramification_inertia_eq_finrank la.asIdeal (𝓞 K)
  rw [← IsFractionRing.finrank_eq (𝓞 K0) K0 (𝓞 K) K,
    Finset.sum_set_coe (la.asIdeal.primesOver (𝓞 K))
      (f := fun q : Ideal (𝓞 K) => q.ramificationIdx (𝓞 K0) * q.inertiaDeg (𝓞 K0))] at h
  rw [← h]
  have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) (T : Set (HeightOneSpectrum (𝓞 K))) :=
    fun a _ b _ hab => HeightOneSpectrum.ext hab
  calc ∑ v ∈ T, v.asIdeal.ramificationIdx (𝓞 K0) * v.asIdeal.inertiaDeg (𝓞 K0)
      = ∑ q ∈ T.image (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal),
          q.ramificationIdx (𝓞 K0) * q.inertiaDeg (𝓞 K0) :=
        (Finset.sum_image (f := fun q : Ideal (𝓞 K) => q.ramificationIdx (𝓞 K0) * q.inertiaDeg (𝓞 K0)) hinj).symm
    _ ≤ _ := by
      refine Finset.sum_le_sum_of_subset ?_
      intro q hq
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hq
      rw [Set.mem_toFinset]
      refine ⟨v.isPrime, ?_⟩
      rw [← hT v hv]
      exact liesOver_under v

theorem lw_nonneg' (la : HeightOneSpectrum (𝓞 K0)) : 0 ≤ Formalism.BasicNotions.lw K0 la := by
  unfold Formalism.BasicNotions.lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

theorem l4 : SumOverPlacesLeBaseSum K0 K := by
  classical
  intro r hr hs S'
  set u : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K0) := fun v => v.under (𝓞 K0) with hu
  have h1 : ∑ v ∈ S', Formalism.BasicNotions.lw K v * ((v.asIdeal.ramificationIdx (𝓞 K0) : ℝ) * r (u v)) =
      ∑ la ∈ S'.image u, ∑ v ∈ S' with u v = la,
        Formalism.BasicNotions.lw K v * ((v.asIdeal.ramificationIdx (𝓞 K0) : ℝ) * r (u v)) :=
    (Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image_of_mem u hv) _).symm
  rw [h1]
  refine le_trans (Finset.sum_le_sum fun la _ => ?_)
    (hs.sum_le_tsum (S'.image u) fun la _ => mul_nonneg (hr la) (lw_nonneg' la))
  have h2 : ∀ v ∈ S'.filter (fun v => u v = la),
      Formalism.BasicNotions.lw K v * ((v.asIdeal.ramificationIdx (𝓞 K0) : ℝ) * r (u v)) =
        (r la * Real.log (Ideal.absNorm la.asIdeal : ℝ) / (finrank ℚ K : ℝ)) *
          ((v.asIdeal.ramificationIdx (𝓞 K0) * v.asIdeal.inertiaDeg (𝓞 K0) : ℕ) : ℝ) := by
    intro v hv
    have hv' : u v = la := (Finset.mem_filter.1 hv).2
    rw [lw_eq (K0 := K0) v, hv']
    have hv'' : v.under (𝓞 K0) = la := hv'
    rw [hv'']
    push_cast
    ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, ← Nat.cast_sum]
  have h3 := sum_ef_le la (S'.filter (fun v => u v = la)) (fun v hv => (Finset.mem_filter.1 hv).2)
  have h4 : (0 : ℝ) ≤ r la * Real.log (Ideal.absNorm la.asIdeal : ℝ) / (finrank ℚ K : ℝ) :=
    div_nonneg (mul_nonneg (hr la) (Real.log_natCast_nonneg _)) (Nat.cast_nonneg _)
  refine le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.2 h3) h4) (le_of_eq ?_)
  unfold Formalism.BasicNotions.lw
  rw [← Module.finrank_mul_finrank ℚ K0 K]
  have h5 : (finrank ℚ K0 : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Module.finrank_pos).ne'
  have h6 : (finrank K0 K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Module.finrank_pos).ne'
  push_cast
  field_simp

end BC4

end Formalism.MainNotions.Gaps.LocalGlobalPassage

end

end

section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.MainNotions.Gaps.LocalGlobalPassage

open Formalism.BasicNotions Formalism.MainNotions
open Formalism.HermitianLatticesTheory (lidx localization₂ locLen locS)
open Formalism.EigenvalueLevelCeiling

theorem span_of_fin {R K V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (v : HeightOneSpectrum R) (A N : Submodule R V)
    (h : Module.length R (↥(localization₂ v.asIdeal A) ⧸ (localization₂ v.asIdeal N).comap (localization₂ v.asIdeal A).subtype) ≠ ⊤) :
    (A : Set V) ⊆ Submodule.span K (N : Set V) := by
  intro x hx
  have hxA : x ∈ localization₂ v.asIdeal A := ⟨1, v.asIdeal.primeCompl.one_mem, by simpa using hx⟩
  set q := (localization₂ v.asIdeal N).comap (localization₂ v.asIdeal A).subtype with hq
  set f : R →ₗ[R] (↥(localization₂ v.asIdeal A) ⧸ q) := LinearMap.toSpanSingleton R _ (q.mkQ ⟨x, hxA⟩) with hf
  have hni : ¬ Function.Injective f := by
    intro hi
    have h1 : Module.length R R ≠ ⊤ := ne_top_of_le_ne_top h (Module.length_le_of_injective f hi)
    have h2 : IsFiniteLength R R := Module.length_ne_top_iff.mp h1
    have h3 : IsArtinian R R := (isFiniteLength_iff_isNoetherian_isArtinian.mp h2).2
    have h4 : IsArtinianRing R := h3
    have h5 : IsField R := IsArtinianRing.isField_of_isDomain R
    exact Ring.not_isField_iff_exists_prime.mpr ⟨v.asIdeal, v.ne_bot, v.isPrime⟩ h5
  have : ∃ d : R, d ≠ 0 ∧ f d = 0 := by
    by_contra hc
    push Not at hc
    apply hni
    rw [injective_iff_map_eq_zero]
    intro d hd
    by_contra h0
    exact hc d h0 hd
  obtain ⟨d, hd0, hd⟩ := this
  have hd' : d • (⟨x, hxA⟩ : ↥(localization₂ v.asIdeal A)) ∈ q := by
    have : q.mkQ (d • (⟨x, hxA⟩ : ↥(localization₂ v.asIdeal A))) = 0 := by
      rw [map_smul]; simpa [hf, LinearMap.toSpanSingleton_apply] using hd
    simpa using this
  obtain ⟨s, hs, hsx⟩ : d • x ∈ localization₂ v.asIdeal N := hd'
  have hs0 : s ≠ 0 := fun e => hs (e ▸ v.asIdeal.zero_mem)
  have hK : algebraMap R K (s * d) ≠ 0 := by
    simpa using (mul_ne_zero hs0 hd0)
  have e : x = (algebraMap R K (s * d))⁻¹ • (s • d • x) := by
    rw [smul_smul, ← algebraMap_smul K (s * d) x, smul_smul, inv_mul_cancel₀ hK, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)

def lenC {R K F : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup F] [Module K F] [Module R F] [IsScalarTower R K F] (v : HeightOneSpectrum R) (A T : Submodule R F)
    (V : Submodule (v.adicCompletion K) (TensorProduct K (v.adicCompletion K) F)) : ℕ∞ :=
  Module.length (v.adicCompletionIntegers K)
      (↥(locC v A ⊓ V.restrictScalars (v.adicCompletionIntegers K)) ⧸
        (locC v T ⊓ V.restrictScalars (v.adicCompletionIntegers K)).comap
          (locC v A ⊓ V.restrictScalars (v.adicCompletionIntegers K)).subtype)

theorem l1' {R K F : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup F] [Module K F] [Module R F] [IsScalarTower R K F] (v : HeightOneSpectrum R)
    (H1 : LengthLocalizationLeCompletion (K := K) (F := F) v) (A T : Submodule R F) (W : Submodule K F) (h : lenC v A T (locKC v W) ≠ ⊤) :
    Module.length R (↥(localization₂ v.asIdeal (A ⊓ W.restrictScalars R)) ⧸
        (localization₂ v.asIdeal (A ⊓ W.restrictScalars R ⊓ T)).comap (localization₂ v.asIdeal (A ⊓ W.restrictScalars R)).subtype) ≤
      lenC v A T (locKC v W) := H1 A T W h

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

theorem qlen_gen {j : ℕ} (X : WeightAlgebra.PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (A T : Submodule (𝓞 B.KO) X.Forms)
    (V : Submodule (X.Kl la) (X.Vl la)) :
    X.qlen la (X.loc la A ⊓ X.ofK la V) (X.loc la T ⊓ X.ofK la V) = lenC la A T V := rfl

theorem l2 (Q : Run D B P) (H1 : ∀ la : HeightOneSpectrum (𝓞 B.KO), LengthLocalizationLeCompletion (K := B.KO) (F := Q.X.Forms) la)
    (H1b : ∀ la : HeightOneSpectrum (𝓞 B.KO), CompletionPreservesFinrank (K := B.KO) (F := Q.X.Forms) la)
    (H1c : ∀ la : HeightOneSpectrum (𝓞 B.KO), CompletionSpanContainment (K := B.KO) (F := Q.X.Forms) la)
    (hM : Submodule.IsLattice B.KO Q.M0) (h : Q.Concl) :
    ∃ r : HeightOneSpectrum (𝓞 B.KO) → ℝ, (∀ la, 0 ≤ r la) ∧ Summable (fun la => r la * Formalism.BasicNotions.lw B.KO la) ∧
      (∑' la, r la * Formalism.BasicNotions.lw B.KO la) ≤ Q.β ∧ ∀ la,
        Submodule.span B.KO ((Q.M0 ⊓ Q.Th0 : Submodule (𝓞 B.KO) _) : Set (B.Cusp Q.jn Q.ka)) = ⊤ ∧
        ∀ e0 : ℤ, (Q.T : ℝ) * Q.nus la ≤ (e0 : ℝ) → ∀ W0 : Submodule B.KO (B.Cusp Q.jn Q.ka),
          (lidx la.asIdeal (Q.M0 ⊓ W0.restrictScalars (𝓞 B.KO)) (Q.M0 ⊓ Q.Th0 ⊓ W0.restrictScalars (𝓞 B.KO)) : ℝ) ≤
            (e0 : ℝ) * (finrank B.KO W0 : ℝ) + r la := by
  obtain ⟨r, h0, h1, h2, h3⟩ := h
  refine ⟨r, h0, h1, h2, fun la => ?_⟩
  set φ : B.Cusp Q.jn Q.ka →ₗ[B.KO] Q.X.Forms := Q.X.inc Q.ka with hφ
  have hinj : Function.Injective φ := Q.X.inc_inj Q.ka
  have hinj' : Function.Injective (φ.restrictScalars (𝓞 B.KO)) := hinj

  have key : ∀ e0 : ℤ, (Q.T : ℝ) * Q.nus la ≤ (e0 : ℝ) → ∀ W0 : Submodule B.KO (B.Cusp Q.jn Q.ka),
      Module.length (𝓞 B.KO) (↥(localization₂ la.asIdeal (Q.M0 ⊓ W0.restrictScalars (𝓞 B.KO))) ⧸
        (localization₂ la.asIdeal (Q.M0 ⊓ W0.restrictScalars (𝓞 B.KO) ⊓ Q.Th0)).comap
          (localization₂ la.asIdeal (Q.M0 ⊓ W0.restrictScalars (𝓞 B.KO))).subtype) ≠ ⊤ ∧
      ((locLen la.asIdeal (Q.M0 ⊓ W0.restrictScalars (𝓞 B.KO)) (Q.M0 ⊓ W0.restrictScalars (𝓞 B.KO) ⊓ Q.Th0) : ℕ) : ℝ) ≤
        (e0 : ℝ) * (finrank B.KO W0 : ℝ) + r la := by
    intro e0 he0 W0
    have hW : W0.map φ ≤ Submodule.span B.KO ((Q.X.Msup Q.ka : Submodule (𝓞 B.KO) Q.X.Forms) : Set Q.X.Forms) := by
      have e1 : Submodule.span B.KO ((Q.X.Msup Q.ka : Submodule (𝓞 B.KO) Q.X.Forms) : Set Q.X.Forms) =
          (Submodule.span B.KO (Q.M0 : Set _)).map φ := idxRules_span_map φ Q.M0
      rw [e1, hM.span_eq_top]
      exact Submodule.map_mono le_top
    have hV : locKC la (W0.map φ) ≤ Q.X.locK la (Q.X.Msup Q.ka) := H1c la (Q.X.Msup Q.ka) (W0.map φ) hW
    obtain ⟨hfin, hle⟩ := h3 la e0 he0 (locKC la (W0.map φ)) hV
    rw [qlen_gen] at hfin hle
    have hl1 := l1' la (H1 la) (Q.X.Msup Q.ka) (Q.X.Theta Q.S Q.ka Q.wL Q.wF Q.T) (W0.map φ) hfin
    have eA : Q.X.Msup Q.ka ⊓ (W0.map φ).restrictScalars (𝓞 B.KO) =
        (Q.M0 ⊓ W0.restrictScalars (𝓞 B.KO)).map (φ.restrictScalars (𝓞 B.KO)) := by
      rw [Submodule.map_inf _ hinj']
      rfl
    have eT : Q.X.Msup Q.ka ⊓ (W0.map φ).restrictScalars (𝓞 B.KO) ⊓ Q.X.Theta Q.S Q.ka Q.wL Q.wF Q.T =
        (Q.M0 ⊓ W0.restrictScalars (𝓞 B.KO) ⊓ Q.Th0).map (φ.restrictScalars (𝓞 B.KO)) := by
      rw [eA]
      ext y
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, hy⟩
        exact ⟨x, ⟨hx, hy⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hx'⟩, rfl⟩
        exact ⟨⟨x, hx, rfl⟩, hx'⟩
    rw [eT, eA, localization_map₄, localization_map₄, idxRules_len_map _ hinj'] at hl1
    have hdim : finrank (la.adicCompletion B.KO) (locKC la (W0.map φ)) = finrank B.KO W0 := by
      rw [H1b la _ inferInstance]
      exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective φ hinj W0)).symm
    rw [hdim] at hle
    unfold locLen
    exact ⟨ne_top_of_le_ne_top hfin hl1, le_trans (by exact_mod_cast ENat.toNat_le_toNat hl1 hfin) hle⟩
  constructor
  · have h4 := span_of_fin (K := B.KO) la _ _ (key _ (Q.eLa_ge la) ⊤).1
    rw [Submodule.restrictScalars_top, inf_top_eq] at h4
    rw [eq_top_iff, ← hM.span_eq_top]
    exact Submodule.span_le.mpr h4
  · intro e0 he0 W0
    rw [inf_right_comm, idxRules_lidx_of_le la.asIdeal inf_le_left]
    exact (key e0 he0 W0).2

end Formalism.MainNotions.Gaps.LocalGlobalPassage

end

end

section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.MainNotions.Gaps.LocalGlobalPassage

open Formalism.HermitianLatticesTheory (lidx localization₂ locLen locS)
open Formalism.EigenvalueLevelCeiling Formalism.DivisionValues
open Formalism.EigenvalueLevelCeiling.ThreeFormsAlt (mem_sc_inv isLatIn_cut qlen_anti_right)

section Mono

variable {R K V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem lidx_anti (p : Ideal R) [p.IsPrime] (W : Submodule K V) {A B' B : Submodule R V} (hA : A.FG)
    (hAW : Submodule.span K (A : Set V) = W) (hB'W : Submodule.span K (B' : Set V) = W) (hB'A : B' ≤ A) (hB : B' ≤ B) :
    lidx p A B ≤ lidx p A B' := by
  rw [idxRules_lidx_of_le p hB'A]
  have h1 : lidx p A B ≤ (locLen p A (A ⊓ B) : ℤ) := by
    unfold lidx
    have : (0 : ℤ) ≤ (locLen p B (A ⊓ B) : ℤ) := Int.natCast_nonneg _
    linarith
  refine h1.trans ?_
  have hfin := idxRules_fin p A B' hA (idxRules_le_locS hAW hB'W)
  have hle : localization₂ p B' ≤ localization₂ p (A ⊓ B) := Formalism.HermitianLatticesTheory.locBasic_locS_mono _ (le_inf hB'A hB)
  have := qlen_anti_right (localization₂ p A) hle
  unfold locLen
  exact_mod_cast ENat.toNat_le_toNat this hfin

end Mono

section BC5

variable {K0 K : Type} [Field K0] [NumberField K0] [Field K] [NumberField K] [StarRing K] [Algebra K0 K]
  {Z0 : Type} [AddCommGroup Z0] [Module K0 Z0] [FiniteDimensional K0 Z0] [Module (𝓞 K0) Z0] [IsScalarTower (𝓞 K0) K0 Z0]
  {n : ℕ}

theorem up_mono (ι : Z0 →ₗ[K0] (Fin n → K)) {A0 B0 : Submodule (𝓞 K0) Z0} (h : A0 ≤ B0) : up ι A0 ≤ up ι B0 :=
  Submodule.span_mono (Set.image_mono h)

theorem up_fg (ι : Z0 →ₗ[K0] (Fin n → K)) {A0 : Submodule (𝓞 K0) Z0} (h : A0.FG) : (up ι A0).FG := by
  obtain ⟨s, rfl⟩ := h
  have e : (s : Set Z0) = Set.range (fun x : s => (x : Z0)) := by simp
  rw [e, up_span_range]
  exact Submodule.fg_span (Set.finite_range _)

theorem up_top (ι : Z0 →ₗ[K0] (Fin n → K)) (htop : Submodule.span K (Set.range ι) = ⊤) {A0 : Submodule (𝓞 K0) Z0}
    (h : Submodule.span K0 (A0 : Set Z0) = ⊤) : Submodule.span K (up ι A0 : Set (Fin n → K)) = ⊤ := by
  rw [eq_top_iff, ← htop]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ Submodule.span K0 (A0 : Set Z0) := by rw [h]; exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [map_smul, ← algebraMap_smul K a (ι x)]
    exact Submodule.smul_mem _ _ hx

theorem l5 (ι : Z0 →ₗ[K0] (Fin n → K))
    (hind : ∀ (m : ℕ) (b : Fin m → Z0), LinearIndependent K0 b → LinearIndependent K fun a => ι (b a))
    (htop : Submodule.span K (Set.range ι) = ⊤) (M0 N0 : Submodule (𝓞 K0) Z0) (hMfg : M0.FG)
    (hM : Submodule.span K0 (M0 : Set Z0) = ⊤) (hN : Submodule.span K0 (N0 : Set Z0) = ⊤) (hNM : N0 ≤ M0)
    (v : HeightOneSpectrum (𝓞 K)) (e0 : ℤ) (ρ : ℝ) (E : ℕ)
    (hE : (E : ℤ) = (v.asIdeal.ramificationIdx (𝓞 K0) : ℤ) * e0)
    (h : ∀ W0 : Submodule K0 Z0,
      (lidx (v.under (𝓞 K0)).asIdeal (M0 ⊓ W0.restrictScalars (𝓞 K0)) (N0 ⊓ W0.restrictScalars (𝓞 K0)) : ℝ) ≤
        (e0 : ℝ) * (finrank K0 W0 : ℝ) + ρ)
    (Th : Submodule (𝓞 K) (Fin n → K)) (hTh : up ι N0 ≤ Th) :
    RemOK v (up ι M0) Th E ((v.asIdeal.ramificationIdx (𝓞 K0) : ℝ) * ρ) := by
  let _ : StarRing K0 := starRingOfComm
  set la := v.under (𝓞 K0) with hla
  set e := v.asIdeal.ramificationIdx (𝓞 K0) with he
  have he0 : e ≠ 0 := l3e v
  have hepos : (0 : ℤ) < (e : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero he0
  have he0nn : 0 ≤ e0 := by
    by_contra hc
    have : (e : ℤ) * e0 < 0 := mul_neg_of_pos_of_neg hepos (not_le.mp hc)
    have h2 : (0 : ℤ) ≤ (E : ℤ) := Int.natCast_nonneg _
    omega
  obtain ⟨E0, rfl⟩ := Int.eq_ofNat_of_zero_le he0nn
  obtain ⟨a0, ha0, hva0⟩ := exists_vw_eq la E0
  have hNfg : N0.FG := by
    have : IsNoetherian (𝓞 K0) M0 := isNoetherian_of_fg_of_noetherian M0 hMfg
    exact isNoetherian_submodule.mp this _ hNM
  have hML : IsLatIn ⊤ M0 := ⟨hMfg, hM⟩
  have hNL : IsLatIn ⊤ N0 := ⟨hNfg, hN⟩
  have h3f := (three_forms K0 Z0 la M0 N0 hML hNL hNM a0 E0 ρ ha0 hva0).mp (fun W0 => by
    have := h W0
    simp only [Int.cast_natCast] at this
    exact this)
  set C0 := M0 ⊓ sc a0⁻¹ N0 with hC0
  have hCL : IsLatIn ⊤ C0 := lattice_intersection K0 Z0 M0 N0 hML hNL a0⁻¹ (inv_ne_zero ha0)
  have hl3 := l3 l3a ι hind htop M0 C0 hMfg hM hCL.1 hCL.2 v
  set a : K := algebraMap K0 K a0 with ha
  have hane : a ≠ 0 := by
    rw [ha]; simpa using ha0
  have hva : vw v a = (E : ℤ) := by
    rw [hE]
    have := l3a v a0 ha0
    unfold vw at hva0 ⊢
    rw [this, hva0]
  have hMsL : IsLatIn ⊤ (up ι M0) := ⟨up_fg ι hMfg, up_top ι htop hM⟩
  have hNsL : IsLatIn ⊤ (up ι N0) := ⟨up_fg ι hNfg, up_top ι htop hN⟩
  have hCsL : IsLatIn ⊤ (up ι C0) := ⟨up_fg ι hCL.1, up_top ι htop hCL.2⟩
  have hIL : IsLatIn ⊤ (up ι M0 ⊓ sc a⁻¹ (up ι N0)) :=
    lattice_intersection K _ _ _ hMsL hNsL a⁻¹ (inv_ne_zero hane)
  have hCle : up ι C0 ≤ up ι M0 ⊓ sc a⁻¹ (up ι N0) := by
    refine le_inf (up_mono ι inf_le_left) (Submodule.span_le.mpr ?_)
    rintro _ ⟨x, hx, rfl⟩
    have hx2 : a0 • x ∈ N0 := (mem_sc_inv ha0 N0 x).mp hx.2
    refine (mem_sc_inv hane _ _).mpr ?_
    rw [ha, algebraMap_smul, ← map_smul]
    exact Submodule.subset_span ⟨_, hx2, rfl⟩
  have hmono := index_monotone K _ v ⊤ (up ι M0) (up ι C0) (up ι M0 ⊓ sc a⁻¹ (up ι N0)) hMsL hCsL hIL hCle
  have hd : (lix v (up ι M0) (up ι M0 ⊓ sc a⁻¹ (up ι N0)) : ℝ) ≤ (e : ℝ) * ρ := by
    have h1 : (lix v (up ι M0) (up ι M0 ⊓ sc a⁻¹ (up ι N0)) : ℝ) ≤ (lix v (up ι M0) (up ι C0) : ℝ) := by
      exact_mod_cast hmono
    have h2 : (lix v (up ι M0) (up ι C0) : ℝ) = (e : ℝ) * (lix la M0 C0 : ℝ) := by
      unfold lix
      rw [hl3]
      push_cast
      rfl
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h3f (Nat.cast_nonneg _))
  have hall := (three_forms K _ v (up ι M0) (up ι N0) hMsL hNsL (up_mono ι hNM) a E _ hane hva).mpr hd
  intro W
  refine le_trans ?_ (hall W)
  have hcA := isLatIn_cut W (up ι M0) hMsL
  have hcN := isLatIn_cut W (up ι N0) hNsL
  have := lidx_anti (K := K) v.asIdeal W (A := cut W (up ι M0)) (B' := cut W (up ι N0)) (B := cut W Th) hcA.1 hcA.2 hcN.2
    (inf_le_inf_right _ (up_mono ι hNM)) (inf_le_inf_right _ hTh)
  exact_mod_cast this

end BC5

end Formalism.MainNotions.Gaps.LocalGlobalPassage

end

end

section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.MainNotions.Gaps.LocalGlobalPassage

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.DivisionValues (vw conjPl)
open Formalism.EigenvalueLevelCeiling (lix cut sc IsLatIn plc)

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P' : Type} [Group P'] [Finite P'] {c : OnConst}

theorem r_eq_rOf (O : OnObj S P' c) (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : O.r v j = rOf O (used O v) v j := by
  unfold OnObj.r rOf used
  by_cases h : plc v = O.pde <;> simp [h]

theorem RemOK.mono {n : ℕ} {v : HeightOneSpectrum (𝓞 K)} {M Th : Submodule (𝓞 K) (Fin n → K)} {E' E : ℕ} {ρ : ℝ}
    (hE : E' ≤ E) (h : RemOK v M Th E' ρ) : RemOK v M Th E ρ := by
  intro W
  refine (h W).trans ?_
  have h1 : (E' : ℝ) ≤ (E : ℝ) := by exact_mod_cast hE
  have h2 : (0 : ℝ) ≤ (finrank K W : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right h1 h2]

theorem run_ok (O : OnObj S P' c) {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} [Algebra B.KO K]
    (t : TheoremZeroData O B P) (k : Bool) (j : Bs.J) (h : (t.run k j).Concl) :
    ∃ r : HeightOneSpectrum (𝓞 B.KO) → ℝ, (∀ la, 0 ≤ r la) ∧ Summable (fun la => r la * Formalism.BasicNotions.lw B.KO la) ∧
      (∑' la, r la * Formalism.BasicNotions.lw B.KO la) ≤ (t.run k j).β ∧
      (∀ v, Submodule.span K (t.ThR k v j : Set (Fin (O.nZ j) → K)) = ⊤) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), RemOK v (O.Ms j) (t.ThR k v j) (t.ER k v j)
        ((v.asIdeal.ramificationIdx (𝓞 B.KO) : ℝ) * r (v.under (𝓞 B.KO))) := by
  obtain ⟨r, h0, h1, h2, h3⟩ := l2 (t.run k j) (fun la => l1 la) (fun la => l1b la) (fun la => l1c la) (t.isLattice_lattice k j) h
  have hMs : O.Ms j = up (t.ι k j) (t.run k j).M0 := t.Ms_eq k j
  have htop : Submodule.span K (Set.range (t.ι k j)) = ⊤ := by
    rw [eq_top_iff, ← t.Ms_top j, hMs]
    have hsub : up (t.ι k j) (t.run k j).M0 ≤ (Submodule.span K (Set.range (t.ι k j))).restrictScalars (𝓞 K) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨z, _, rfl⟩
      exact Submodule.subset_span ⟨z, rfl⟩
    exact Submodule.span_le.mpr hsub
  have hle : ∀ v, up (t.ι k j) ((t.run k j).M0 ⊓ (t.run k j).Th0) ≤ t.ThR k v j := fun v =>
    (up_mono _ inf_le_right).trans (t.Th_le k v j)
  refine ⟨r, h0, h1, h2, fun v => ?_, fun v => ?_⟩
  · rw [eq_top_iff, ← up_top (t.ι k j) htop (h3 (v.under (𝓞 B.KO))).1]
    exact Submodule.span_mono (hle v)
  · rw [hMs]
    have hge : ((t.run k j).T : ℝ) * (t.run k j).nus (v.under (𝓞 B.KO)) ≤
        ((max (t.e0 k (v.under (𝓞 B.KO)) j) 0 : ℤ) : ℝ) :=
      (t.exponent_bound_ter k _ j).trans (by exact_mod_cast le_max_left _ _)
    have hE' : ((((v.asIdeal.ramificationIdx (𝓞 B.KO) : ℤ) * max (t.e0 k (v.under (𝓞 B.KO)) j) 0).toNat : ℕ) : ℤ) =
        (v.asIdeal.ramificationIdx (𝓞 B.KO) : ℤ) * max (t.e0 k (v.under (𝓞 B.KO)) j) 0 :=
      Int.toNat_of_nonneg (mul_nonneg (Int.natCast_nonneg _) (le_max_right _ _))
    have hle' : ((v.asIdeal.ramificationIdx (𝓞 B.KO) : ℤ) * max (t.e0 k (v.under (𝓞 B.KO)) j) 0).toNat ≤ t.ER k v j := by
      have h5 : (v.asIdeal.ramificationIdx (𝓞 B.KO) : ℤ) * max (t.e0 k (v.under (𝓞 B.KO)) j) 0 ≤ (t.ER k v j : ℤ) := by
        rcases max_choice (t.e0 k (v.under (𝓞 B.KO)) j) 0 with hm | hm
        · rw [hm]; exact t.E_le k v j
        · rw [hm, mul_zero]; exact Int.natCast_nonneg _
      omega
    exact RemOK.mono hle' (l5 (t.ι k j) (t.indep k j) htop _ _ (t.isLattice_lattice k j).fg (t.isLattice_lattice k j).span_eq_top
      (h3 (v.under (𝓞 B.KO))).1 inf_le_left v _ _ _ hE'
      ((h3 (v.under (𝓞 B.KO))).2 _ hge) _ (hle v))

theorem leafStatement_of_conclusions (O : OnObj S P' c) {D : D7} (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) [Algebra B.KO K]
    (t : TheoremZeroData O B P) (h : ∀ k j, (t.run k j).Concl) : LatticeIndexBoundAtPairs O := by
  have hbud : ∀ k j, ∀ S' : Finset (HeightOneSpectrum (𝓞 K)),
      ∑ v ∈ S', Formalism.DivisionValues.lw v * rOf O k v j ≤ (O.nZ j : ℝ) * (O.f * O.m * O.b * O.de2) := by
    intro k j S'
    obtain ⟨r, h0, h1, h2, -, h4⟩ := run_ok O t k j (h k j)
    refine le_trans ?_ ((l4 r h0 h1 S').trans (h2.trans (t.budget k j)))
    refine Finset.sum_le_sum fun v _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (lw_nonneg' v)
    exact t.r_le k v j _ (mul_nonneg (Nat.cast_nonneg _) (h0 _)) (h4 v)
  have hloc : ∀ v, (∀ j, (O.Th1 v j).FG ∧ O.Th1 v j ≤ O.Th v j) → ∀ j, IsLatIn ⊤ (O.Th1 v j) ∧ O.Th1 v j ≤ O.Th v j ∧
      O.a v j ≠ 0 ∧ vw v (O.a v j) = (O.E v j : ℤ) ∧ ∀ W : Submodule K (Fin (O.nZ j) → K),
      (lix v (cut W (O.Ms j)) (cut W (O.Th1 v j)) : ℝ) ≤ (O.E v j : ℝ) * (finrank K W : ℝ) + O.r v j := by
    intro v hv j
    obtain ⟨r, h0, -, -, h3, h4⟩ := run_ok O t (used O v) j (h _ j)
    refine ⟨⟨(hv j).1, ?_⟩, (hv j).2, (t.a_ok v j).1, (t.a_ok v j).2, ?_⟩
    · rw [t.Th1_eq v j]; exact h3 v
    · refine t.r_ok v j ((v.asIdeal.ramificationIdx (𝓞 B.KO) : ℝ) * r (v.under (𝓞 B.KO)))
        (mul_nonneg (Nat.cast_nonneg _) (h0 _)) ?_
      rw [t.Th1_eq v j, t.E_used v j]
      exact h4 v
  refine ⟨fun w hw => ⟨hloc w (t.Th1_ok w hw).1, hloc _ (t.Th1_ok w hw).2⟩, t.weight_parameter_mem_unit_interval.1, t.weight_parameter_mem_unit_interval.2,
    fun v j => ⟨t.r_nonneg false v j, t.r_nonneg true v j⟩, fun j S' => ⟨hbud false j S', hbud true j S'⟩⟩

end Formalism.MainNotions.Gaps.LocalGlobalPassage

end

end

section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.MainNotions.Gaps.LocalGlobalPassage

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.DivisionValues (vw conjPl)
open Formalism.EigenvalueLevelCeiling (lix cut sc IsLatIn plc)

section Rem

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}

def rem (v : HeightOneSpectrum (𝓞 K)) (M Th : Submodule (𝓞 K) (Fin n → K)) (E : ℕ) : ℝ :=
  max 0 (sSup (Set.range fun W : Submodule K (Fin n → K) =>
    (lix v (cut W M) (cut W Th) : ℝ) - (E : ℝ) * (finrank K W : ℝ)))

theorem rem_nonneg (v : HeightOneSpectrum (𝓞 K)) (M Th : Submodule (𝓞 K) (Fin n → K)) (E : ℕ) : 0 ≤ rem v M Th E :=
  le_max_left _ _

theorem rem_le {v : HeightOneSpectrum (𝓞 K)} {M Th : Submodule (𝓞 K) (Fin n → K)} {E : ℕ} {ρ : ℝ} (h0 : 0 ≤ ρ)
    (h : RemOK v M Th E ρ) : rem v M Th E ≤ ρ := by
  refine max_le h0 (csSup_le (Set.range_nonempty _) ?_)
  rintro _ ⟨W, rfl⟩
  have := h W
  simp only
  linarith

theorem rem_ok {v : HeightOneSpectrum (𝓞 K)} {M Th : Submodule (𝓞 K) (Fin n → K)} {E : ℕ} {ρ : ℝ}
    (h : RemOK v M Th E ρ) : RemOK v M Th E (rem v M Th E) := by
  intro W
  have hb : BddAbove (Set.range fun W : Submodule K (Fin n → K) =>
      (lix v (cut W M) (cut W Th) : ℝ) - (E : ℝ) * (finrank K W : ℝ)) := by
    refine ⟨ρ, ?_⟩
    rintro _ ⟨W, rfl⟩
    have := h W
    simp only
    linarith
  have h1 := le_csSup hb ⟨W, rfl⟩
  have h2 : sSup (Set.range fun W : Submodule K (Fin n → K) =>
      (lix v (cut W M) (cut W Th) : ℝ) - (E : ℝ) * (finrank K W : ℝ)) ≤ rem v M Th E := le_max_right _ _
  simp only at h1
  linarith

end Rem

section Exp

variable {K0 K : Type} [Field K0] [NumberField K0] [Field K] [NumberField K] [Algebra K0 K]

def EOf (e0 : HeightOneSpectrum (𝓞 K0) → ℤ) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  ((v.asIdeal.ramificationIdx (𝓞 K0) : ℤ) * e0 (v.under (𝓞 K0))).toNat

theorem EOf_eq {e0 : HeightOneSpectrum (𝓞 K0) → ℤ} (h : ∀ la, 0 ≤ e0 la) (v : HeightOneSpectrum (𝓞 K)) :
    (EOf e0 v : ℤ) = (v.asIdeal.ramificationIdx (𝓞 K0) : ℤ) * e0 (v.under (𝓞 K0)) :=
  Int.toNat_of_nonneg (mul_nonneg (Int.natCast_nonneg _) (h _))

end Exp

end Formalism.MainNotions.Gaps.LocalGlobalPassage

end

end

section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.MainNotions.Gaps.LocalGlobalPassage

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Indef Formalism.L2.Indef.Tree

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P' : Type} [Group P'] [Finite P'] {c : OnConst}
  {O : OnObj S P' c} {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} [Algebra B.KO K]

theorem TheoremZeroData.range_top (t : TheoremZeroData O B P) (k : Bool) (j : Bs.J) : Submodule.span K (Set.range (t.ι k j)) = ⊤ := by
  rw [eq_top_iff, ← t.Ms_top j, t.Ms_eq k j]
  have hsub : Submodule.span (𝓞 K) (t.ι k j '' ((t.run k j).M0 : Set _)) ≤
      (Submodule.span K (Set.range (t.ι k j))).restrictScalars (𝓞 K) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, _, rfl⟩
    exact Submodule.subset_span ⟨z, rfl⟩
  exact Submodule.span_le.mpr hsub

theorem TheoremZeroData.rk_eq (t : TheoremZeroData O B P) (k : Bool) (j : Bs.J) :
    (t.run k j).X.rk (t.run k j).ka (B.Mlat (t.run k j).jn (t.run k j).ka) = O.nZ j := by
  have h1 : (t.run k j).X.rk (t.run k j).ka (B.Mlat (t.run k j).jn (t.run k j).ka) =
      finrank B.KO (B.Cusp (t.run k j).jn (t.run k j).ka) := by
    unfold WeightAlgebra.PJ.rk
    have := (t.isLattice_lattice k j).span_eq_top
    unfold Run.M0 at this
    rw [this, finrank_top]
  rw [h1]
  set b := Module.finBasis B.KO (B.Cusp (t.run k j).jn (t.run k j).ka)
  have hli := t.indep k j _ b b.linearIndependent
  have hsp := span_iota_basis (t.ι k j) (t.range_top k j) b
  have := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
  rw [Module.finrank_fin_fun, Fintype.card_fin] at this
  exact this.symm

end Formalism.MainNotions.Gaps.LocalGlobalPassage

end

end
