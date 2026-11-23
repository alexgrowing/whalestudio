import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedOfPowFixed

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.TameCycChoice

theorem zpow_iff {Γ L A F : Type} [Group Γ] [Field L] [CommRing A] [Field F] (e : L →+* F) (j : A →+* F)
    (hj : Function.Injective j) (ψ₀ : Γ →* Lˣ) (ψ : Γ →* Aˣ)
    (h : ∀ g, e ((ψ₀ g : Lˣ) : L) = j ((ψ g : Aˣ) : A)) (σ γ : Γ) (m : ℤ) :
    ψ σ = ψ γ ^ m ↔ ψ₀ σ = ψ₀ γ ^ m := by
  rw [← map_zpow, ← map_zpow, ← Units.val_inj, ← Units.val_inj, ← hj.eq_iff, ← e.injective.eq_iff, h, h]

theorem mem_zpowers_of_tameGen {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (B : ValuationSubring Ω) {Γ : Type} [Group Γ] (ψ : G E Ω →* Γ) (ho : IsOpen (ψ.ker : Set (G E Ω)))
    (hw : ∀ σ : G E Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → ψ σ = 1)
    {γ : G E Ω} (hγ : TameGenAt B γ) (σ : G E Ω) (hσ : σ ∈ Ine (F := E) B) :
    ψ σ ∈ Subgroup.zpowers (ψ γ) := by
  let K : Subgroup (G E Ω) := (Subgroup.zpowers (ψ γ)).comap ψ
  have hK : IsOpen (K : Set (G E Ω)) := Subgroup.isOpen_mono (H₁ := ψ.ker)
    (fun g hg => by rw [Subgroup.mem_comap, (MonoidHom.mem_ker).1 hg]; exact one_mem _) ho
  refine closure_minimal (t := (K : Set (G E Ω))) ?_ (K.isClosed_of_isOpen hK) (hγ.2 hσ)
  refine (Subgroup.closure_le K).2 ?_
  rintro g (rfl | hg)
  · exact Subgroup.mem_zpowers _
  · change ψ g ∈ Subgroup.zpowers _
    rw [hw g hg]; exact one_mem _

theorem tameCyc : ∀ (D : D7) (C : NChoice D), NChTie D C → TameCyc D C := by
  intro D C hT i v hv σ hσ
  obtain ⟨ψ₀, -, hW, hK⟩ := hT.psi_eq
  have hl : v ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i v (Or.inr hv)
  have hmem := mem_zpowers_of_tameGen (D.nd.plOm.1 v) (D.ntw.psiL i) (D.ntw.psiL_open i)
    (fun g hg => GlobalTheory.WildInertiaChar.trivial_on_wild D.host.E D.nd.Om v (D.nd.plOm.1 v) (D.nd.l i)
      (D.nd.lPrime i).out hl (D.nd.plOm.2 v) _ (D.ntw.psiL i) (D.ntw.psiL_open i) (D.ntw.psiL_ord i) g hg)
    (D.nd.restN_tameGenerator_generates i v (Or.inr hv)) σ hσ
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
  refine ⟨m, ?_⟩
  have h0 := (zpow_iff (D.nd.embK i) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))
    (IsFractionRing.injective _ _) (ψ₀ (D.nd.w i)) (D.ntw.psiL i) (hK i) σ (D.nd.gam0 i v) m).1 hm.symm
  exact (zpow_iff (C.embW (D.nd.w i))
    ((algebraMap (C.Oe (D.nd.w i)) (FractionRing (C.Oe (D.nd.w i)))).comp
      (algebraMap (D.ntw.Ok (C.twI (D.nd.w i)) (C.k' (D.nd.w i))) (C.Oe (D.nd.w i))))
    ((IsFractionRing.injective (C.Oe (D.nd.w i)) (FractionRing (C.Oe (D.nd.w i)))).comp (C.Oe_inj (D.nd.w i)))
    (ψ₀ (D.nd.w i)) (psiG D C (D.nd.w i)) (hW (D.nd.w i)) σ (D.nd.gam0 i v) m).2 h0

end GlobalTheory.TameCycChoice
