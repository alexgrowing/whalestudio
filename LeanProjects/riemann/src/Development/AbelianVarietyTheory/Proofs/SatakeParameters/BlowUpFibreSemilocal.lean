import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ApartAllEmpty
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.CongL.LimAtLU

variable {a : ℕ}

theorem int_of_mem_inf {lam : DomWeight a} {x : ℂ} (hx : x ∈ infOfWeight lam) :
    ∃ j : ℤ, ((a : ℂ) - 1) / 2 - x = j := by
  obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
  exact ⟨(k : ℤ) - lam.w k, by push_cast; ring⟩

open Classical in

noncomputable def jumpsOf (lam : DomWeight a) : Multiset ℤ :=
  (infOfWeight lam).map fun z => if h : ∃ n : ℤ, ((a : ℂ) - 1) / 2 - z = n then h.choose else 0

theorem jumpsOf_map (lam : DomWeight a) :
    (jumpsOf lam).map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) := by
  rw [jumpsOf, Multiset.map_map]
  refine Multiset.map_congr rfl fun z hz => ?_
  have h := int_of_mem_inf hz
  simp only [Function.comp_apply, dif_pos h]
  exact h.choose_spec.symm

theorem eq_jumpsOf {lam : DomWeight a} {J : Multiset ℤ}
    (hJ : J.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z)) : J = jumpsOf lam :=
  Multiset.map_injective Int.cast_injective (hJ.trans (jumpsOf_map lam).symm)

theorem norm_algHom {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]
  rfl

theorem overPl_of_induced {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ}
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Bw : LocBridge l E Ω (Dec (F := E) A) O}
    (hj : GlobalTheory.Pst.Induces Bw) {τ : E →+* Qbar l} {LL' : FinExt l} {τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1}
    (hτ : GlobalTheory.Pst.IsInduced Bw τ τ') : OverPl ι (ι.toRingHom.comp τ) w := by
  intro x hx
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    RingEquiv.symm_apply_apply]
  rw [hτ]
  have h1 := norm_algHom (LL'.1.val.comp τ') ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩
  have h2 : ‖Bw.j (algebraMap E Ω x)‖ < 1 := (hj.valuation_lt_one_iff _).1 ((h x).2 hx)
  exact h1 ▸ h2

end GlobalTheory.CongL.LimAtLU

open Classical GlobalTheory.CongL.LimAtLU in

theorem GlobalTheory.CongL.crysDRU_of_linApprox : ClosedAtL → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → (∀ τ : E →+* ℂ, ∃ lam, HasWeightAt U τ lam) → ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Continuous r → IsSSRep r → ∀ C : Set (G E Ω →* GL (Fin a) (Qbar l)), LinApprox r C → (∀ ρ ∈ C, Continuous ρ ∧ ∃ U' : Submodule ℂ (UA E a → ℂ), SameWtAt ι w U U' ∧ CrysDRU U' ι ρ w) → CrysDRU U ι r w := by
  intro hC E Ω _ _ _ _ _ _ l _ ι a ha U _ hW r w hwl hr hss C hlin hCC
  intro P AI hT A hA O _ _ _ Bw hBw
  choose lamF hlamF using hW
  have key : ∀ lamG : (E →+* ℂ) → DomWeight a, (∀ σ, HasWeightAt U σ (lamG σ)) →
      (IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (jumpsOf (lamG (ι.toRingHom.comp τ)))) ∧
      ((∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype)) → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)) := by
    intro lamG hG
    refine hC E Ω l a ha P AI hT w A hA O Bw hBw (fun τ => jumpsOf (lamG (ι.toRingHom.comp τ))) r hr hss C hlin
      (fun ρ hρ => ?_)
    obtain ⟨hcont, U', hWW, hcd⟩ := hCC ρ hρ
    have h := hcd P AI hT A hA O Bw hBw
    exact ⟨hcont, GlobalTheory.CrysSst.isSstAt_of_isCrysAt l P AI hT E Ω _ O Bw a _ h.1,
      fun τ LL' τ' hi => h.2.2 τ LL' τ' hi _ _ ((hWW _ (overPl_of_induced ι hA hBw hi) _).1 (hG _)) (jumpsOf_map _)⟩
  refine ⟨(key lamF hlamF).2 fun ρ hρ => ?_, (key lamF hlamF).1.1, fun τ LL' τ' hi lam J hl hJ => ?_⟩
  · obtain ⟨-, U', -, hcd⟩ := hCC ρ hρ
    exact (hcd P AI hT A hA O Bw hBw).1
  · let lamG := Function.update lamF (ι.toRingHom.comp τ) lam
    have hG : ∀ σ, HasWeightAt U σ (lamG σ) := by
      intro σ
      rcases eq_or_ne σ (ι.toRingHom.comp τ) with h | h
      · rw [h]
        simpa [lamG] using hl
      · show HasWeightAt U σ (Function.update lamF (ι.toRingHom.comp τ) lam σ)
        rw [Function.update_of_ne h]
        exact hlamF σ
    have e := (key lamG hG).1.2 τ LL' τ' hi
    rw [eq_jumpsOf hJ]
    simpa [lamG] using e
