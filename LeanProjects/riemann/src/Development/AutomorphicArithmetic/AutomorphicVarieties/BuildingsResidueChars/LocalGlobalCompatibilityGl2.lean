import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CompatReal
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem norm_hom {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]
  rfl

private theorem embAt_of_induced {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : GlobalTheory.Pst.Induces Bw) (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1)
    (hτ : GlobalTheory.Pst.IsInduced Bw τ τ') : EmbAt w τ := by
  intro x
  rw [hτ]
  have h1 := norm_hom (LL'.1.val.comp τ') ⟨Bw.j (algebraMap F Ω x), Bw.j_E x⟩
  refine ((hj.valuation_lt_one_iff _).symm.trans (h x)).symm.trans ?_
  exact iff_of_eq (congrArg (· < 1) h1.symm)

theorem UpperTheory.local_global_compatibility_gl2 :
    Af.HypothesesH → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ) [Fact (n = 2)], 1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n) (χ : HChar F), Continuous r → π.IsRegAlg → π.Polarized χ → AttR ι r π → ∀ (w : HeightOneSpectrum (𝓞 F)) (m : Fin n → ℤ), (∀ τ : F →+* Qbar l, EmbAt w τ → π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) (infOf m)) → ∀ σ, π.IsLocComp w σ → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) rc, IsRec h rc → UpperTheory.V.Lev.AbW (rc (algNorm σ)) → Hi.DRat ι h (r.comp (Dec (F := F) A).subtype) (fun _ => Finset.univ.val.map fun j => -m j) fun s => (rc (algNorm σ)).charPol s := by
  intro PH F Ω _ _ _ _ _ _ l _ hl ι n _ hn r π χ hr hreg hpol hatt w m hm σ hσ A h rc hrc hab O _ _ _ Bw hj
  obtain ⟨-, wt, HT, -, -, hG⟩ := Af.exR PH F Ω l ι n hn π χ hreg hpol
  replace hG := hG r hr hatt
  obtain ⟨h1, h2, -, -⟩ := hG.above _ _ (Loc.tiedP l) w A h O Bw hj
  refine ⟨h1, fun τ LL' τ' hτ => ?_, fun s => ?_⟩
  · have e : HT τ = Finset.univ.val.map fun j => -m j := by
      refine Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective ?_
      have := hG.weights τ _ (hm τ (embAt_of_induced h Bw hj τ LL' τ' hτ))
      simp only [this, infOf, Multiset.map_map]
      exact Multiset.map_congr rfl fun i _ => by simp
    exact e ▸ h2 τ LL' τ' hτ
  · exact ((Af.compatReal PH F Ω l hl ι n hn r π χ hr hreg hpol hatt w σ hσ A h rc hrc).2 O Bw hj).2 (Or.inr hab) s
