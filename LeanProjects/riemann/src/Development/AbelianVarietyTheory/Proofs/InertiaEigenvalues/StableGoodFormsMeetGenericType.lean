import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UupEqOneOfLeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableSubmoduleMeetsCharacterTypeVectorsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonoidAlgebraExistsRightInvOfMapFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubfieldAdjoinRootsOfUnityEmbeddingComplexStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRightInverseCentralProjectorUnitElementStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodIdempotentIrreducibleCharacterGenericSumNeZeStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.MeetsGen.exists_right_inv_generic_central_projector : ∀ (D : D7), GrpSide D → ∀ [Fintype (G0g D.nd)]
    (U : Subgroup (G0g D.nd)) [Fintype U],
    U = Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r →
    ∀ ψ : U →* ℂˣ, Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ →
    2 ≤ D.R.r → ∃ v : MonoidAlgebra ℂ (G0g D.nd),
      GlobalTheory.MeetsGen.uElt U (fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ)) D.ntypes.e0 * v = 1 := by
  intro D S _ U _ hU ψ hψ hr
  obtain ⟨hc, hi⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D
  exact GlobalTheory.T.exists_right_inverse_centralProjectorUnitElement U ψ D.ntypes.e0 hi (fun a => ((Subalgebra.mem_center_iff.mp hc) a).symm)
    (GlobalTheory.T.good_idempotent_irreducible_character_generic_sum_ne_zero D S U hU ψ hψ hr)

open GlobalTheory.MeetsGen in

theorem GlobalTheory.TwInputs.meetsAll_of_ties : GlobalTheory.Published.GreenCuspidal → ∀ (D : D7), NExpTied D → GrpSide D → MeetsAll D := by
  intro hG D T S i j b W hW hst hfix
  classical
  by_cases hr : D.R.r ≤ 1
  · have hFm0 : Fm0 D.nexp i j b = ⊤ := by
      rw [eq_top_iff]
      intro x _
      simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker]
      intro u
      have hu1 : u = 1 := Subtype.ext (GlobalTheory.MeetsGen.uup_eq_one_of_le_one _ _ hr _ (T.U_eq ▸ u.2))
      subst hu1
      simp
    rw [hFm0, inf_top_eq]
    exact hW
  have hr : 2 ≤ D.R.r := by omega
  haveI : ∀ k : Fin 2, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Fintype (G0g D.nd) := Fintype.ofFinite _
  haveI : Fintype D.nexp.U := Fintype.ofFinite _
  obtain ⟨θ, hθ, hψ⟩ := T.psiU_gen i b
  let s : ↥D.LL0 →+* FractionRing (D.ntw.O i) :=
    (IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
      (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)).comp (if b then D.ntw.emb0 i else D.ntw.emb0b i)
  let t : ↥D.LL0 →+* ℂ := D.what₂.embLL.comp D.LL0.val.toRingHom
  let Z : Set (FractionRing (D.ntw.O i)) :=
    {z | ∃ (x : Σ k : Fin 2, D.nd.PlG k) (a : Multiplicative (ZMod (D.host.g x.1))), z = ((θ x a : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i))}
  have hZ : ∀ z ∈ Z, ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
    rintro z ⟨x, a, rfl⟩
    haveI : NeZero (D.host.g x.1) := ⟨(D.host.g_prime x.1).ne_zero⟩
    refine ⟨Fintype.card (Multiplicative (ZMod (D.host.g x.1))), Fintype.card_pos, ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  obtain ⟨E, jE, hsE, hZE, hj⟩ := GlobalTheory.T.exists_subfield_adjoin_rootsOfUnity_embedding_complex s t Z hZ

  let θE : ∀ x : (Σ k : Fin 2, D.nd.PlG k), Multiplicative (ZMod (D.host.g x.1)) →* Eˣ := fun x =>
    { toFun := fun a => ⟨⟨((θ x a : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hZE ⟨x, a, rfl⟩⟩,
        ⟨(((θ x a)⁻¹ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hZE ⟨x, a⁻¹, by simp⟩⟩,
        Subtype.ext (by simp), Subtype.ext (by simp)⟩
      map_one' := by ext; simp
      map_mul' := fun a a' => by ext; simp }
  have hθE : ∀ x a, (((θE x a : Eˣ) : E) : FractionRing (D.ntw.O i)) = ((θ x a : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) :=
    fun _ _ => rfl
  let θ' : ∀ x : (Σ k : Fin 2, D.nd.PlG k), Multiplicative (ZMod (D.host.g x.1)) →* ℂˣ :=
    fun x => (Units.map jE.toMonoidHom).comp (θE x)
  have hθ' : 2 ≤ D.R.r → ∀ x, θ' x ≠ 1 := by
    intro h x h1
    apply hθ h x
    refine MonoidHom.ext fun a => Units.ext ?_
    have h2 := congrArg (fun φ : Multiplicative (ZMod (D.host.g x.1)) →* ℂˣ => ((φ a : ℂˣ) : ℂ)) h1
    simp only [θ', MonoidHom.comp_apply, Units.coe_map, MonoidHom.one_apply, Units.val_one] at h2
    have h3 : ((θE x a : Eˣ) : E) = 1 := jE.injective (by rw [map_one]; exact h2)
    have h4 : (((θE x a : Eˣ) : E) : FractionRing (D.ntw.O i)) = 1 := by rw [h3]; rfl
    rw [MonoidHom.one_apply, Units.val_one]
    exact (hθE x a).symm.trans h4
  let ψ' : D.nexp.U →* ℂˣ := (Formalism.L2.NX.psiStd _ _ θ').comp (Subgroup.inclusion T.U_eq.le)
  have hψ' : Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ' :=
    ⟨θ', hθ', fun u => rfl⟩
  obtain ⟨vC, hvC⟩ := GlobalTheory.MeetsGen.exists_right_inv_generic_central_projector D S D.nexp.U T.U_eq ψ' hψ' hr

  have hψE : ∀ u : D.nexp.U, ((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) ∈ E := by
    intro u
    rw [hψ u]
    simp only [Formalism.L2.NX.stdVal, Units.coe_prod]
    exact E.prod_mem fun x _ => hZE ⟨x, _, rfl⟩
  let fE : D.nexp.U → E := fun u => ⟨(((D.nexp.psiU i b u)⁻¹ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)),
    by rw [Units.val_inv_eq_inv_val]; exact E.inv_mem (hψE u)⟩
  let eE : MonoidAlgebra E (G0g D.nd) :=
    MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => (⟨s (D.nexp.eLL0 g), hsE _⟩ : E))
  have hψval : ∀ u : D.nexp.U, jE ⟨((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hψE u⟩ =
      ((ψ' u : ℂˣ) : ℂ) := by
    intro u
    have e1 : (⟨((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hψE u⟩ : E) =
        ∏ x, ((θE x (Multiplicative.ofAdd (Formalism.L2.NX.supSum D.R.r
          (((u : G0g D.nd) x : GL (Fin D.R.r) (ZMod (D.host.g x.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g x.1))))) : Eˣ) : E) := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_finsetProd, hθE]
      rw [hψ u]
      simp [Formalism.L2.NX.stdVal, Units.coe_prod]
    rw [e1, map_prod]
    simp [ψ', Formalism.L2.NX.psiStd, Formalism.L2.NX.stdVal, θ', Units.coe_prod]
  have hC1 : MonoidAlgebra.mapRingHom (G0g D.nd) jE (uElt D.nexp.U fE eE) =
      uElt D.nexp.U (fun u => (((ψ' u)⁻¹ : ℂˣ) : ℂ)) D.ntypes.e0 := by
    rw [GlobalTheory.MeetsGen.map_uElt]
    congr 1
    · funext u
      have e2 : fE u = (⟨((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hψE u⟩ : E)⁻¹ :=
        Subtype.ext (by simp [fE])
      rw [e2, map_inv₀, hψval, Units.val_inv_eq_inv_val]
    · refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
      rw [MonoidAlgebra.coeff_mapRingHom]
      simp only [eE, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
      rw [hj, ← D.nStage_trivialCharacter_coeff_eq]
      rfl
  have hK1 : MonoidAlgebra.mapRingHom (G0g D.nd) E.subtype eE = D.nexp.eAlg i b := by
    refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
    rw [MonoidAlgebra.coeff_mapRingHom, D.nexp.eAlg_def]
    simp only [eE, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
    rfl
  obtain ⟨vE, hvE⟩ := GlobalTheory.T.monoidAlgebra_exists_right_inv_of_map_field jE (uElt D.nexp.U fE eE) ⟨vC, by rw [hC1]; exact hvC⟩
  have hvK := congrArg (MonoidAlgebra.mapRingHom (G0g D.nd) E.subtype) hvE
  rw [map_mul, map_one, GlobalTheory.MeetsGen.map_uElt, hK1] at hvK
  have heq := GlobalTheory.MeetsGen.eq_sum_of_uElt_mul D.nexp.U _ (D.nexp.eAlg i b) _ (D.nexp.eAlg_idem i b) (D.nexp.eAlg_central i b) hvK
  exact GlobalTheory.T.stable_submodule_meets_character_type_vectors (D.nexp.actG i j b) D.nexp.U (D.nexp.psiU i b) (D.nexp.eAlg i b) _ heq W hW
    (fun g x hx => hst g x hx) (fun x hx => hfix x hx)

end
