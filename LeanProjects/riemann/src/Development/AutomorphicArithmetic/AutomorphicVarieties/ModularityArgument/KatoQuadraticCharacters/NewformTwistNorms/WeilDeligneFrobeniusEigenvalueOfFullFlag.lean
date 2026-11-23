import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CompatAtLQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Module UpperTheory.V.Af.Wd

namespace GlobalTheory.FlagFrob

private theorem cont_diag {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r : Γ →* GL (Fin n) (Qbar l)} (hr : Continuous r) {H : Subgroup Γ} {κ : Fin n → ↥H →* (Qbar l)ˣ}
    (hf : IsFlagOn r H κ) (i : Fin n) : Continuous fun s => (κ i s : Qbar l) := by
  obtain ⟨g, hg⟩ := hf
  have h1 : Continuous fun s : ↥H => (g * r s * g⁻¹ : GL (Fin n) (Qbar l)) :=
    (continuous_const.mul (hr.comp continuous_subtype_val)).mul continuous_const
  exact ((Units.continuous_val.comp h1).matrix_elem i i).congr fun s => (hg s).2 i

private theorem isRoot_of_tri {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ}
    (b : Basis (Fin n) ℂ W) (f : End ℂ W) (d : Fin n → ℂ)
    (h0 : ∀ i j, j < i → LinearMap.toMatrix b b f i j = 0) (h1 : ∀ i, LinearMap.toMatrix b b f i i = d i)
    (i : Fin n) : f.charpoly.IsRoot (d i) := by
  rw [← LinearMap.charpoly_toMatrix f b, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => h0 i j hij),
    Polynomial.IsRoot, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h1])

set_option maxHeartbeats 800000 in

theorem isRoot_charPol_wdAt :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw) (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      FlagAt M m r A κ → IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
      ∀ (i : Fin n) (φ : ↥(Weil h)), deg φ = 1 →
        (WD.charPol (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)) φ).IsRoot
          (((normV w : ℕ) : ℂ) ^ m i * ι ((κ i (Subgroup.inclusion (Weil_le_Dec h) φ) *
            cycBar F Ω l (φ : G F Ω) ^ (-m i) : (Qbar l)ˣ) : Qbar l)) := by
  rintro F Ω _ _ _ _ _ l _ ι n M hM m r hr w A h O _ _ _ Bw hj κ ⟨χ, hχ, hfl, hI⟩ hp i φ hφ
  have hκc := cont_diag hr hfl
  obtain ⟨L, ρ, κL, χL, hV, e, htri, hκ, hχL⟩ := UpperTheory.galois_representation_model_over_finite_extension F Ω l ι n r w A h O Bw hj κ χ
    (fun i => UpperTheory.galois_rep_values_in_finite_extension F Ω _ M hM _ (hχ i)) hfl hp
  obtain ⟨-, hcyc, hK⟩ := UpperTheory.crystalline_period_ring_properties F Ω l w A h O Bw hj
  obtain ⟨K', hK'⟩ := hK M hM
  let inc := Subgroup.inclusion (Weil_le_Dec h)
  let ε : ↥(Dec (F := F) A) →* (Qbar l)ˣ := (cycBar F Ω l).comp (Dec (F := F) A).subtype
  let ψ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ := fun i => κ i * ε ^ (-m i)
  let μ : ↥(Weil h) → Fin n → ℂ := fun σ i => ((normV w : ℕ) : ℂ) ^ (m i * deg σ) * ι (ψ i (inc σ) : Qbar l)
  have hεc : Continuous fun s => (ε s : Qbar l) := by
    have h0 : Continuous fun g : GQ l => (((Loc.PP l).χQ g : ℚ_[l]ˣ) : ℚ_[l]) := by
      obtain ⟨hc, -, hq⟩ := Loc.cycFacts l l
      simp only [hq]
      have h0 : Continuous fun g : GQ l => ((Loc.cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) := Units.continuous_val.comp hc
      exact continuous_subtype_val.comp h0
    exact ((continuous_algebraMap ℚ_[l] (Om l)).comp (h0.comp (continuous_subtype_val.comp Bw.e_cont))).congr
      fun s => hcyc L s
  have hψc : ∀ i, Continuous fun s => (ψ i s : Qbar l) := fun i => by
    refine ((hκc i).mul (hεc.zpow₀ (-m i) fun s => Or.inl (Units.ne_zero _))).congr fun s => ?_
    simp [ψ]
  haveI := hV.finite
  have T := UpperTheory.weilDeligne_triangularizable F Ω l ι w A h O Bw hj L n _ ρ κL μ htri (fun i hi σ y => by
    refine (UpperTheory.cyclotomicWeilChar_properties F Ω l ι w A h O Bw hj L (κL i) (χL i) (m i) ?_ ⟨K', fun g hg => ?_⟩ (fun g hg => ?_) hi σ y).trans ?_
    · refine ((hκc i).comp Bw.e_symm_cont).congr fun g => ?_
      rw [Function.comp_apply, ← hκ, MulEquiv.apply_symm_apply]
    · obtain ⟨s, rfl⟩ := Bw.e.surjective g
      refine Units.ext (Subtype.ext ?_)
      rw [hχL, hχ i s (hK' s hg)]
      rfl
    · obtain ⟨s, rfl⟩ := GlobalTheory.PstLaws.exists_ine_of_fix Bw h hj g hg
      refine Units.ext (Subtype.ext ?_)
      have h1 := congrArg Units.val (hI i (inc (ineIncl h s)) s.2)
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, ← hκ, ← hχL, ← hcyc L] at h1
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, MulMemClass.coe_mul]
      exact h1.trans (by congr 1)
    · congr 3
      have h1 : (ψ i (inc σ) : Qbar l) = (κ i (inc σ) : Qbar l) * (cycBar F Ω l (inc σ) : Qbar l) ^ (-m i) := by
        simp [ψ, ε]
      rw [h1, ← hκ, ← hcyc L, Units.val_mul, Units.val_zpow_eq_zpow_val, MulMemClass.coe_mul]
      congr 1) hV
  obtain ⟨b₀, hb₀⟩ := T
  have h2 := isRoot_of_tri b₀ _ _ (hb₀ (some φ)).1 (hb₀ (some φ)).2 i
  rw [e, wdPst_of_isPst ι Bw h hj hV, WD.charPol_mk]
  have h3 : μ φ i = ((normV w : ℕ) : ℂ) ^ m i * ι ((κ i (Subgroup.inclusion (Weil_le_Dec h) φ) *
      cycBar F Ω l (φ : G F Ω) ^ (-m i) : (Qbar l)ˣ) : Qbar l) := by
    simp only [μ, hφ, mul_one]
    rfl
  obtain ⟨u, -, hu, -, hc, hρ⟩ := wdRep_spec (Loc.PP l) ι Bw h hj ρ
  rw [← h3, (GlobalTheory.WeilDeligne.isFrobSS_of_unipotent u hu hc hρ).charpoly_eq φ]
  exact h2

end GlobalTheory.FlagFrob

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligne_frobenius_eigenvalue_of_full_flag : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw) (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      FlagAt M m r A κ → IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
      ∀ (i : Fin n) (φ : ↥(Weil h)), deg φ = 1 →
        (WD.charPol (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)) φ).IsRoot
          (((normV w : ℕ) : ℂ) ^ m i * ι ((κ i (Subgroup.inclusion (Weil_le_Dec h) φ) *
            cycBar F Ω l (φ : G F Ω) ^ (-m i) : (Qbar l)ˣ) : Qbar l)) := by
  first | exact @GlobalTheory.FlagFrob.isRoot_charPol_wdAt | exact GlobalTheory.FlagFrob.isRoot_charPol_wdAt | (intros; apply GlobalTheory.FlagFrob.isRoot_charPol_wdAt <;> assumption)

end
