import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

noncomputable section

open Pointwise

namespace GlobalTheory.SelInf

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem conj_Ine {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  have m : ∀ y : Ω, y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A := fun y => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  have m' : ∀ y : Ω, (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', m, m, map_inv₀,
      map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]
  have c : ∀ x : Ω, (g⁻¹ : G F Ω) (g x) = x := fun x => by
    show (g⁻¹ * g) x = x
    simp
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, m, c]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (m' _).1 (hσ.2 _ hx')
    rw [map_sub, c] at h
    exact h

variable {R R' : Type} [CommRing R] [CommRing R'] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [DiscreteTopology M] {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [DiscreteTopology M']
  {S : Set (HeightOneSpectrum (𝓞 F))} {ρ : Representation R (G F Ω) M} {ρS : Representation R' (GS Ω S) M'}
  (e : M ≃+ M') (he : ∀ g m, e (ρ g m) = ρS (toGS Ω S g) (e m))

include he in

theorem triv_of_mem {σ : G F Ω} (hσ : σ ∈ NS Ω S) (m : M) : ρ σ m = m := by
  apply e.injective
  have : toGS Ω S σ = 1 := (QuotientGroup.eq_one_iff σ).2 hσ
  rw [he, this, map_one]
  rfl

def infZ (z : Z1 ρS) : Z1 ρ :=
  ⟨fun g => e.symm (z.1 (toGS Ω S g)),
    (continuous_of_discreteTopology (f := e.symm)).comp (z.2.1.comp (continuous_toGS Ω S)), fun g h => by
      apply e.injective
      beta_reduce
      rw [map_add, he, map_mul, z.2.2]
      simp⟩

theorem infZ_apply (z : Z1 ρS) (g : G F Ω) : (infZ e he z).1 g = e.symm (z.1 (toGS Ω S g)) := rfl

theorem mk_infZ_eq_iff (z z' : Z1 ρS) :
    (Submodule.Quotient.mk (infZ e he z) : H1 ρ) = Submodule.Quotient.mk (infZ e he z') ↔
      (Submodule.Quotient.mk z : H1 ρS) = Submodule.Quotient.mk z' := by
  rw [Submodule.Quotient.eq, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.mem_comap, mem_coboundaries1, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨e m, fun g => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g', toGS Ω S g' = g := QuotientGroup.mk'_surjective _ g
    have h1 : e.symm (z.1 (toGS Ω S g)) - e.symm (z'.1 (toGS Ω S g)) = ρ g m - m := hm g
    have h2 := congrArg e h1
    rw [map_sub, map_sub, he, e.apply_symm_apply, e.apply_symm_apply] at h2
    exact h2
  · rintro ⟨m, hm⟩
    refine ⟨e.symm m, fun g => ?_⟩
    have h1 : z.1 (toGS Ω S g) - z'.1 (toGS Ω S g) = ρS (toGS Ω S g) m - m := hm (toGS Ω S g)
    change e.symm (z.1 (toGS Ω S g)) - e.symm (z'.1 (toGS Ω S g)) = _
    apply e.injective
    rw [map_sub, map_sub, he, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]
    exact h1

def infH : H1 ρS → H1 ρ := fun x => Submodule.Quotient.mk (infZ e he x.out)

theorem infH_mk (z : Z1 ρS) : infH e he (Submodule.Quotient.mk z) = Submodule.Quotient.mk (infZ e he z) :=
  (mk_infZ_eq_iff e he _ _).2 (Quotient.out_eq' _)

theorem infH_injective : Function.Injective (infH e he) := by
  intro x y h
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [infH_mk, infH_mk] at h
  exact (mk_infZ_eq_iff e he _ _).1 h

theorem Ine_le_NS {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    {σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) : σ ∈ NS Ω S := by
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, hσ⟩

theorem z_one {Γ : Type} [Group Γ] [TopologicalSpace Γ] {π : Representation R Γ M} (z : Z1 π) : z.1 1 = 0 := by
  have := z.2.2 1 1
  simpa using this

include he in

theorem mem_unrAt_iff {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    (z : Z1 ρ) :
    resH1 ρ (Dec (F := F) A).subtype continuous_subtype_val (Submodule.Quotient.mk z) ∈ Formalism.GaloisCohomology.unrAt ρ A ↔
      ∀ σ ∈ Ine (F := F) A, z.1 σ = 0 := by
  have h0 : resH1 ρ (Dec (F := F) A).subtype continuous_subtype_val (Submodule.Quotient.mk z) ∈ Formalism.GaloisCohomology.unrAt ρ A ↔
      (Submodule.Quotient.mk (restrictCocycles1 _ ((Ine (F := F) A).subgroupOf (Dec (F := F) A)).subtype continuous_subtype_val
        (restrictCocycles1 ρ (Dec (F := F) A).subtype continuous_subtype_val z)) : H1 _) = 0 := Iff.rfl
  rw [h0, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩ σ hσ
    have h1 : z.1 σ = ρ σ m - m := hm ⟨⟨σ, Ine_le_Dec A hσ⟩, hσ⟩
    rw [h1, triv_of_mem e he (Ine_le_NS hv hA hσ), sub_self]
  · intro h
    refine ⟨0, fun g => ?_⟩
    rw [map_zero, sub_zero]
    exact h g.1.1 g.2

include he in

theorem vanish_NS [IsAlgClosure F Ω] (A : Formalism.GaloisCohomology.Places F Ω) (z : Z1 ρ)
    (h : ∀ v ∉ S, ∀ σ ∈ Ine (F := F) (A.1 v), z.1 σ = 0) : ∀ σ ∈ NS Ω S, z.1 σ = 0 := by
  have hz := z.2.2
  have hinv : ∀ g, z.1 g + ρ g (z.1 g⁻¹) = 0 := fun g => by
    rw [← hz, mul_inv_cancel, z_one]
  let K : Subgroup (G F Ω) :=
    { carrier := {g | g ∈ NS Ω S ∧ z.1 g = 0}
      one_mem' := ⟨one_mem _, z_one z⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨mul_mem ha hb, by rw [hz, ha', hb', map_zero, add_zero]⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        have := hinv a
        rwa [ha', zero_add, triv_of_mem e he ha] at this }
  have hK : K.Normal := ⟨by
    rintro a ⟨ha, ha'⟩ g
    refine ⟨(normal_NS S).conj_mem a ha g, ?_⟩
    rw [mul_assoc, hz, hz, ha', zero_add, triv_of_mem e he ha, hinv]⟩
  have hc : IsClosed (K : Set (G F Ω)) :=
    (isClosed_NS Ω S).inter ((isClosed_discrete {(0 : M)}).preimage z.2.1)
  have hle : Subgroup.normalClosure
      (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring (Ω) | IsPlaceOver A v}, Inertia (F := F) A) ≤ K := by
    apply Subgroup.normalClosure_le_normal
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, B, hB, hτ⟩ := hτ
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (A.2 v) hB
    have h1 := conj_Ine (F := F) hτ
    have h2 : g⁻¹ * τ * g ∈ K := ⟨Ine_le_NS hv (A.2 v) h1, h v hv _ h1⟩
    have h3 := hK.conj_mem _ h2 g
    have h4 : g * (g⁻¹ * τ * g) * g⁻¹ = τ := by group
    rwa [h4] at h3
  intro σ hσ
  exact (Subgroup.topologicalClosure_minimal _ hle hc hσ).2

theorem exists_infZ (z : Z1 ρ) (h : ∀ σ ∈ NS Ω S, z.1 σ = 0) : ∃ z', infZ e he z' = z := by
  have hz := z.2.2
  have hw : ∀ a b : G F Ω, (QuotientGroup.leftRel (NS Ω S)) a b → e (z.1 a) = e (z.1 b) := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have : z.1 (a * (a⁻¹ * b)) = z.1 a := by rw [hz, h _ hab, map_zero, add_zero]
    rw [← this, mul_inv_cancel_left]
  refine ⟨⟨Quotient.lift (fun g => e (z.1 g)) hw,
    Continuous.quotient_lift ((continuous_of_discreteTopology (f := e)).comp z.2.1) hw, fun g g' => ?_⟩, ?_⟩
  · obtain ⟨g, rfl⟩ : ∃ g', toGS Ω S g' = g := QuotientGroup.mk'_surjective _ g
    obtain ⟨g', rfl⟩ : ∃ g'', toGS Ω S g'' = g' := QuotientGroup.mk'_surjective _ g'
    rw [← map_mul]
    change e (z.1 (g * g')) = e (z.1 g) + ρS (toGS Ω S g) (e (z.1 g'))
    rw [hz, map_add, he]
  · exact Subtype.ext (funext fun g => e.symm_apply_apply (z.1 g))

end

theorem selAll_equiv_sel : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R R' : Type) [CommRing R] [CommRing R'] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (M' : Type) [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [DiscreteTopology M'] (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω) (ρ : Representation R (G F Ω) M) (ρS : Representation R' (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M') (e : M ≃+ M'), ContAction ρ → (∀ g m, e (ρ g m) = ρS (toGS Ω _ g) (e m)) → ∀ (L : ∀ v, Submodule R (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) (LS : LocCond ρS (locFam S (fun v => A.1 v.1))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → (∀ (v : S) (z : Z1 (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)) (z' : Z1 (ρS.comp (locFam S (fun v => A.1 v.1) v))), (∀ g, z'.1 g = e (z.1 g)) → (Submodule.Quotient.mk z ∈ L v.1 ↔ Submodule.Quotient.mk z' ∈ LS v)) → Nonempty (Formalism.GaloisCohomology.SelAll ρ A L ≃ Sel ρS (locFam S (fun v => A.1 v.1)) (continuous_locFam S _) LS) := by
  intro F Ω _ _ _ _ _ R R' _ _ M _ _ _ _ M' _ _ _ _ S A ρ ρS e _ he L LS hL hLS
  have key : ∀ (z : Z1 ρS) (v : S),
      resH1 ρ (Dec (F := F) (A.1 v.1)).subtype continuous_subtype_val (Submodule.Quotient.mk (infZ e he z)) ∈ L v.1 ↔
      resH1 ρS (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v) (Submodule.Quotient.mk z) ∈ LS v :=
    fun z v => hLS v (restrictCocycles1 ρ (Dec (F := F) (A.1 v.1)).subtype continuous_subtype_val (infZ e he z))
      (restrictCocycles1 ρS (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v) z)
      (fun g => (e.apply_symm_apply _).symm)
  have hall : ∀ y : H1 ρ, y ∈ Formalism.GaloisCohomology.SelAll ρ A L ↔
      ∀ v, resH1 ρ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val y ∈ L v :=
    fun y => mem_Sel ρ (fun v => (Dec (F := F) (A.1 v)).subtype) (fun _ => continuous_subtype_val) L y
  have hmem : ∀ x : H1 ρS, x ∈ Sel ρS (locFam S (fun v => A.1 v.1)) (continuous_locFam S _) LS ↔
      infH e he x ∈ Formalism.GaloisCohomology.SelAll ρ A L := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [infH_mk, hall, mem_Sel]
    constructor
    · intro h v
      by_cases hv : v ∈ S
      · exact (key z ⟨v, hv⟩).2 (h ⟨v, hv⟩)
      · rw [hL v hv, mem_unrAt_iff e he (by simpa using hv) (A.2 v)]
        intro σ hσ
        have : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) σ = 1 :=
          (QuotientGroup.eq_one_iff σ).2 (Ine_le_NS (by simpa using hv) (A.2 v) hσ)
        rw [infZ_apply, this, z_one, map_zero]
    · intro h v
      exact (key z v).1 (h v.1)
  refine ⟨(Equiv.ofBijective (fun x : Sel ρS (locFam S (fun v => A.1 v.1)) (continuous_locFam S _) LS =>
    (⟨infH e he x.1, (hmem _).1 x.2⟩ : Formalism.GaloisCohomology.SelAll ρ A L)) ⟨?_, ?_⟩).symm⟩
  · intro x y h
    exact Subtype.ext (infH_injective e he (congrArg Subtype.val h))
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hy' := (hall _).1 hy
    obtain ⟨z', rfl⟩ := exists_infZ e he z (vanish_NS e he A z fun v hv => by
      have hv' : v ∉ S := by simpa using hv
      have := hy' v
      rwa [hL v hv', mem_unrAt_iff e he hv (A.2 v)] at this)
    exact ⟨⟨Submodule.Quotient.mk z', (hmem _).2 (by rw [infH_mk]; exact hy)⟩, Subtype.ext (infH_mk e he z')⟩

end GlobalTheory.SelInf
