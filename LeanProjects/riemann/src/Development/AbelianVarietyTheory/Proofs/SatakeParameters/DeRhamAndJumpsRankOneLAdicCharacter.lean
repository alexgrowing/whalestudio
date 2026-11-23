import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.TripleGal GlobalTheory.Pst
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CharAboveRead

open scoped TensorProduct

theorem exists_isInduced_of {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (τ : E →+* Om l) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ placesOver E l)
    (hτ : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) (A : ValuationSubring Ω) (hA : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
    (hj : Induces Bw) : ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1, IsInduced Bw τ τ' := by
  let jE : E →+* Om l := Bw.j.comp (algebraMap E Ω)
  have hjE : ∀ x : 𝓞 E, ‖jE (x : E)‖ < 1 ↔ x ∈ w.asIdeal := fun x =>
    (hj.valuation_lt_one_iff _).symm.trans (hA x)
  have iso := GlobalTheory.GalFirstClause.Emb.norm_eq_of_samePlace τ jE w hw hτ hjE
  have hker : ∀ t ∈ RingHom.ker (GlobalTheory.GalFirstClause.Emb.tensLift jE), GlobalTheory.GalFirstClause.Emb.tensLift τ t = 0 := fun t ht =>
    norm_eq_zero.1 (le_antisymm ((GlobalTheory.GalFirstClause.Emb.norm_tensLift_le jE τ (fun x => (iso x).symm) t).trans
      (by rw [RingHom.mem_ker.1 ht, norm_zero])) (norm_nonneg _))
  have hrange : (GlobalTheory.GalFirstClause.Emb.tensLift jE).range ≤ Bw.Kw.1.toSubalgebra := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      change GlobalTheory.GalFirstClause.Emb.tensLift jE (a ⊗ₜ y) ∈ _
      rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul]
      exact mul_mem (Bw.Kw.1.algebraMap_mem a) (Bw.j_E y)
    | add t₁ t₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  have hfin : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule (GlobalTheory.GalFirstClause.Emb.tensLift jE).range) := by
    haveI : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra) := Bw.Kw.2
    exact Submodule.finiteDimensional_of_le (Subalgebra.toSubmodule.monotone hrange)
  have hclosed : IsClosed ((GlobalTheory.GalFirstClause.Emb.tensLift jE).range : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule (GlobalTheory.GalFirstClause.Emb.tensLift jE).range)
  have hle : Bw.Kw.1.toSubalgebra ≤ (GlobalTheory.GalFirstClause.Emb.tensLift jE).range := by
    intro y hy
    refine closure_minimal ?_ hclosed (Bw.j_dense hy)
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by
      change GlobalTheory.GalFirstClause.Emb.tensLift jE (1 ⊗ₜ x) = jE x; rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul, map_one, one_mul]⟩
  let σ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l :=
    ((Ideal.Quotient.liftₐ (RingHom.ker (GlobalTheory.GalFirstClause.Emb.tensLift jE)) (GlobalTheory.GalFirstClause.Emb.tensLift τ) hker).comp
      (Ideal.quotientKerEquivRange (GlobalTheory.GalFirstClause.Emb.tensLift jE)).symm.toAlgHom).comp (Subalgebra.inclusion hle)
  refine ⟨σ.codRestrict Bw.LL.1.toSubalgebra (fun y => Bw.LL_split σ y), fun x => ?_⟩
  have key : (Ideal.quotientKerEquivRange (GlobalTheory.GalFirstClause.Emb.tensLift jE)).symm
      (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩) = Ideal.Quotient.mk _ (1 ⊗ₜ x) := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    change jE x = GlobalTheory.GalFirstClause.Emb.tensLift jE (1 ⊗ₜ x)
    rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul, map_one, one_mul]
  change τ x = σ ⟨jE x, Bw.j_E x⟩
  change τ x = Ideal.Quotient.liftₐ _ (GlobalTheory.GalFirstClause.Emb.tensLift τ) hker
    ((Ideal.quotientKerEquivRange (GlobalTheory.GalFirstClause.Emb.tensLift jE)).symm (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩))
  rw [key, Ideal.Quotient.liftₐ_apply]
  change τ x = GlobalTheory.GalFirstClause.Emb.tensLift τ (1 ⊗ₜ x)
  rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul, map_one, one_mul]

theorem continuous_rankOneOperator {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (μ : Γ →* Kˣ) (hμ : Continuous μ) : Continuous fun g => ((rk1 μ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) := by
  have hv : Continuous fun g => ((μ g : Kˣ) : K) := Units.continuous_val.comp hμ
  refine continuous_pi fun i => continuous_pi fun k => ?_
  have e : ∀ g, ((rk1 μ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) i k = ((μ g : Kˣ) : K) := fun g => by
    fin_cases i; fin_cases k; simp [rk1]
  simp only [e]
  exact hv

end GlobalTheory.CharAboveRead

namespace GlobalTheory.CharAboveRead

set_option maxHeartbeats 1000000 in

theorem deRham_and_jumps_rankOne_lAdic_character : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (μ : G D.host.E D.nd.Om →* (Qbar l)ˣ), Continuous μ → ∀ (J : (D.host.E →+* Qbar l) → Multiset ℤ)
    (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E l →
    (∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), Induces Bw →
      IsdRAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) ∧
      ∀ (τ : D.host.E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ (J τ)) →
    W.IsdRW l ι (rk1 μ) w ∧ ∀ τ : D.host.E →+* Qbar l, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) →
      W.jumpsW l ι (rk1 μ) τ = J τ := by
  intro D T W l _ ι μ hμ J w hw H
  have hcont : Continuous fun g => (rk1 μ g : Matrix (Fin 1) (Fin 1) (Qbar l)) := continuous_rankOneOperator μ hμ
  obtain ⟨K, ρ, hρc, hρ⟩ := GlobalTheory.GalFirstClause.finextRep l D.host.E D.nd.Om 1 (rk1 μ) hcont
  obtain ⟨j, L0, hj, hLL⟩ := GlobalTheory.PlaceBridge.exists_locBridge l D.host.E D.nd.Om w (D.nd.plOm.1 w) hw (D.nd.plOm.2 w)
  obtain ⟨Bw, hBj, hBLL, -, hBto⟩ := hLL L0 le_rfl
  have hind : Induces Bw := fun x => by rw [hBj]; exact hj x
  let LL' : FinExt l := supExt K Bw.LL
  have hK : K.1 ≤ LL'.1 := le_sup_left
  have hB : Bw.LL.1 ≤ LL'.1 := le_sup_right
  let ρ' : G D.host.E D.nd.Om →* GL (Fin 1) ↥LL'.1 := mapRep (IntermediateField.inclusion hK).toRingHom ρ
  have hρ' : mapRep (algebraMap ↥LL'.1 (Om l)) ρ' = rk1 μ := by
    rw [← hρ]
    ext g i k
    rfl
  have hρ'c : Continuous fun g => (ρ' g : Matrix (Fin 1) (Fin 1) ↥LL'.1) := by
    have hi : Continuous (IntermediateField.inclusion hK) :=
      continuous_induced_rng.2 continuous_subtype_val
    exact hρc.matrix_map hi
  have hmodel : IsModel Bw (resDec D.nd.plOm.1 (rk1 μ) w) LL'
      (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
    ⟨hB, by rw [← hρ']; rfl⟩
  let φ : ↥(OL L0) →+* Qbar l := L0.1.val.toRingHom.comp (OL L0).val.toRingHom
  have hφ : ∀ x, φ x = ((Bw.toLL x : ↥Bw.LL.1) : Om l) := fun x => (hBto x).symm
  have hcl := (W.loc l ι w hw _ Bw hind φ hφ).2 LL' hB 1 ρ' hρ'c
  rw [hρ'] at hcl
  have hab := H _ Bw hind
  have hdR : Bw.IsdRE (D.loc l) LL' (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
    (hmodel.isdRAt_iff (D.loc l)).1 hab.1
  refine ⟨hcl.2.1.2 hdR, fun τ hτ => ?_⟩
  obtain ⟨τ₀, hτ₀⟩ := exists_isInduced_of τ w hw hτ _ (D.nd.plOm.2 w) _ Bw hind
  let τ'' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1 := (IntermediateField.inclusion hB).comp τ₀
  have hτ'' : IsInduced Bw τ τ'' := fun x => hτ₀ x
  have hJ := hab.2 τ LL' τ'' hτ''
  ext n
  apply Nat.cast_injective (R := ℤ)
  rw [(hcl.2.2.2 τ τ'' hτ'').2 hdR n, IsJumpsAt.count_eq (D.loc l) hmodel hτ'' hJ n]

end GlobalTheory.CharAboveRead
