import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SatOfFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.CoeffExt TensorProduct Module

namespace UpperTheory.V.Af

theorem isSst_of_coord {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra ℚ_[l] LL] [Algebra ℚ_[l] LL'] [Algebra LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [Module LL' V'] [IsScalarTower ℚ_[l] LL' V'] [IsScalarTower LL LL' V']
    {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL' ↥(GK K) V'}
    {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[LL] (ι → V)} (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i))
    (hι : finrank LL LL' = Fintype.card ι) [Nonempty ι] (h : IsSst P ρ) : IsSst P ρ' := by
  unfold IsSst at h ⊢
  have e : ↥(Dst P ρ') ≃ₗ[LL] (ι → ↥(Dst P ρ)) :=
    subEquiv (tensCoord E (Bst P)) ((Dst P ρ').restrictScalars LL) _ fun x => by
      simp only [Submodule.restrictScalars_mem, mem_Dst]
      rw [forall_comm]
      refine forall_congr' fun g => ?_
      rw [← (tensCoord E (Bst P)).injective.eq_iff, funext_iff]
      simp only [GlobalTheory.PstExt.tensCoord_stRep P hE]
  have h1 := e.finrank_eq
  have h2 := E.finrank_eq
  rw [finrank_fun', ← Module.finrank_mul_finrank LL LL', hι] at h1 h2
  have hp : 0 < Fintype.card ι := Fintype.card_pos
  rw [Nat.eq_of_mul_eq_mul_left hp h1, Nat.eq_of_mul_eq_mul_left hp h2, h]

theorem isSstAt_conj {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O)
    {a : ℕ} {r r' : ↥Gw →* GL (Fin a) (Om l)} (A : GL (Fin a) (Om l)) (hc : ∀ g, r' g = A * r g * A⁻¹)
    (h : IsSstAt P Bw r) : IsSstAt P Bw r' := by
  obtain ⟨L₁, r₁, h₁, hs⟩ := h
  obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model A hc h₁
  refine ⟨L₂, r₂, hm, ?_⟩
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  have hρ : ∀ g, ∃ M : Matrix (Fin a) (Fin a) ↥L₁.1, (∀ x, Bw.repE L₁ r₁ g x = M.mulVec x) ∧
      ∀ x, Bw.repE L₂ (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x =
        (M.map (algebraMap ↥L₁.1 ↥L₂.1)).mulVec x :=
    fun g => ⟨r₁ (Bw.e.symm g), fun _ => rfl, fun _ => rfl⟩
  have : Nonempty (Fin (finrank ↥L₁.1 ↥L₂.1)) := ⟨⟨0, finrank_pos⟩⟩
  refine isSst_of_coord P (E := (e.symm.restrictScalars ↥L₁.1).trans (vecCoord ↥L₁.1 ↥L₂.1 a)) (fun g x i => ?_)
    (Fintype.card_fin _).symm hs
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [← he]
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, LinearEquiv.symm_apply_apply]
  exact vecCoord_rep hρ g y i

theorem sat_ae_of_smooth (hS : SatLoc) {F : Type} [Field F] [NumberField F] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    [Nontrivial V] (ρ : Representation ℂ (GL (Fin n) (Af F)) V) (hρ : GlobalTheory.PRep.IsSmooth ρ)
    (hi : ∀ w, ∃ σ, LocIsotypic ρ w σ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, GlobalTheory.LFun.HasSatGL w (ρ.comp (locGL F n w)) B := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨S, hS'⟩ := GlobalFixedVectors.exists_KAway_subset (M := 1) ((hρ v).mem_nhds (by simp))
  filter_upwards [S.finite_toSet.eventually_cofinite_notMem] with w hw
  obtain ⟨σ, hσ⟩ := hi w
  obtain ⟨h1, h2⟩ := hS F n w σ
  have hK : IsCompact (GlobalTheory.LFun.KGL w n : Set (GL (Fin n) (w.adicCompletion F))) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F w)
  obtain ⟨B, hB⟩ := h1 (hasFixed_of_sum σ.ρ σ.smooth (ρ.comp (locGL F n w)) _ hK hσ.2
    ⟨v, hv, fun u hu => hS' (GlobalFixedVectors.mem_KAway.2 ⟨locGL_mem_KLev n w
      (by rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top) hu,
      fun x hx => pLoc_locGL_of_ne (fun e : x = w => hw (e ▸ hx)) u⟩)⟩)
  exact ⟨B, (h2 _ _ hσ B).2 hB⟩

end UpperTheory.V.Af

end
