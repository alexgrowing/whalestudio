import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqMulProdOfPartial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHoldsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoUnitaryPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesPureInnerProductsTensorProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerContractionOnePlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerContractionValuesKFiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCoverKFinitePairingOfRealIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CovariantPairingUniqueUpToScalarStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealLine

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

open Classical in

theorem exists_ins {a b : ℕ} (P : D.what₂.Tau → LPol b a) (τ : D.what₂.Tau) :
    ∃ j : LPol b a →ₗ[ℂ] PolF D b a, ∀ Q, j Q = glue (Function.update P τ Q) := by
  refine ⟨LinearMap.mulLeft ℂ
      (∏ σ ∈ Finset.univ.erase τ, (MvPolynomial.rename (fun s => (σ, s)) (P σ) : PolF D b a)) ∘ₗ
      (MvPolynomial.rename (fun s : Fin b × Fin a => (τ, s)) : LPol b a →ₐ[ℂ] PolF D b a).toLinearMap,
    fun Q => ?_⟩
  unfold glue
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ)]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
    Function.update_apply]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun σ hσ => ?_
  rw [if_neg (Finset.ne_of_mem_erase hσ)]

open Classical in

theorem locW_of_semiW {M : DSModel V S} {M' : DSModel W S'} {τ : D.what₂.Tau} {aS aT : ℚ}
    {A : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ} (h : SemiW M M' τ aS aT A)
    {P : D.what₂.Tau → LPol W.rank V.rank} {j : LPol W.rank V.rank →ₗ[ℂ] PolF D W.rank V.rank}
    (hj : ∀ Q, j Q = glue (Function.update P τ Q)) : LocW M M' τ aS aT (A ∘ₗ j) := by
  obtain ⟨hKs, hKt⟩ := GlobalTheory.T.realIntertwinerContraction_values_kFinite D V W S S' M M' τ aS aT A h
  have hG := (GlobalTheory.T.gluing_law_holds D V.rank W.rank).2
  have upd : ∀ Q Q' : LPol W.rank V.rank,
      Function.update (Function.update P τ Q) τ Q' = Function.update P τ Q' := fun Q Q' =>
    Function.update_idem _ _ _
  have hS : ∀ Z Q, fockS τ (M.ε τ) (M'.ε τ) Z (j Q) = j (locS (M.ε τ) (M'.ε τ) Z Q) := by
    intro Z Q
    rw [hj, hj, (hG τ (M.ε τ) (M'.ε τ) (Function.update P τ Q)).1 Z, upd]
    simp
  have hT : ∀ Z Q, fockT τ (M.ε τ) (M'.ε τ) Z (j Q) = j (locT (M.ε τ) (M'.ε τ) Z Q) := by
    intro Z Q
    rw [hj, hj, (hG τ (M.ε τ) (M'.ε τ) (Function.update P τ Q)).2 Z, upd]
    simp
  refine ⟨fun Q y => hKs (j Q) y, fun Q u => hKt (j Q) u, ?_, ?_⟩
  · intro X hX Q y u
    have e : srcOp M M' τ aT X (j Q) =
        j (locS (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) Q - ((aT : ℂ) * X.trace) • Q) := by
      rw [map_sub, map_smul, ← hS]
      simp [srcOp, sub_eq_add_neg]
    simp only [LinearMap.comp_apply]
    rw [← e]
    exact h.src X hX (j Q) y u
  · intro Y hY Q y y' hy
    have e : tgtOp M M' τ aS Y (j Q) =
        j (locT (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) Q + ((aS : ℂ) * Y.trace) • Q) := by
      rw [map_add, map_smul, ← hT]
      simp [tgtOp]
    simp only [LinearMap.comp_apply]
    rw [← e]
    exact h.tgt Y hY (j Q) y y' hy

theorem loc_line_of_matches {M : DSModel V S} {M' : DSModel W S'} {τ : D.what₂.Tau} {p q r s : ℕ} {T₁ : GrpData p q}
    {T₂ : GrpData r s} {R₁ : DSRep T₁} {R₂ : DSRep T₂} {e : Ix p q ≃ Fin V.rank} {e' : Ix r s ≃ Fin W.rank}
    {m m' : ℤ} {aS aT : ℚ} {U : M.H τ ≃ₗᵢ[ℂ] R₁.U.H} {U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H}
    {κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s} (hm : (m : ℚ) = 2 * aT) (hm' : (m' : ℚ) = 2 * aS)
    (hU : Matches R₁ M τ (barMat e) m U) (hU' : Matches R₂ M' τ (plainMat e') m' U')
    (hκ : IsPolyIso (M.ε τ) (M'.ε τ) e e' κ) {B₀ : Pol p q r s → R₂.HK.V → R₁.HK.V}
    (hB₀ : ∀ B, CoverW R₁ R₂ B → ∃ c : ℂ, ∀ P y, B P y = c • B₀ P y) :
    ∃ A₀ : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ, ∀ A, LocW M M' τ aS aT A → ∃ c : ℂ, A = c • A₀ := by

  have key : ∀ A, LocW M M' τ aS aT A → ∃ c : ℂ, ∀ P (x : R₂.HK.V) (y : M'.sm τ),
      U' (y : M'.H τ) = R₂.ι x → U (A P y) = c • R₁.ι (B₀ (κ P) x) := by
    intro A hA
    obtain ⟨B, hB, hBA⟩ := GlobalTheory.T.exists_cover_kFinite_pairing_of_realIntertwiner D V W S S' M M' τ p q r s T₁ T₂ R₁ R₂ e e' m m' aS aT U U' κ A
      hm hm' hU hU' hκ hA
    obtain ⟨c, hc⟩ := hB₀ B hB
    refine ⟨c, fun P x y hy => ?_⟩
    rw [← hBA P x y hy, hc, map_smul]

  have uniq : ∀ (A A' : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ) (c : ℂ),
      LocW M M' τ aS aT A → LocW M M' τ aS aT A' →
      (∀ P (y : M'.sm τ), U' (y : M'.H τ) ∈ Set.range R₂.ι → A P y = c • A' P y) → A = c • A' := by
    intro A A' c hA hA' hK
    refine LinearMap.ext fun P => LinearMap.ext fun y => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply]
    refine ext_inner_left ℂ fun u => ?_
    obtain ⟨b, hb, hbA⟩ := hA.kT P u
    obtain ⟨b', hb', hbA'⟩ := hA'.kT P u
    obtain ⟨x₁, hx₁⟩ := (hU'.kfin b).1 hb
    obtain ⟨x₂, hx₂⟩ := (hU'.kfin b').1 hb'
    have hdK : U' (b - (starRingEnd ℂ c) • b') ∈ Set.range R₂.ι :=
      ⟨x₁ - c • x₂, by rw [map_sub, map_smul, hx₁, hx₂, map_sub, map_smulₛₗ]; simp⟩
    have hsm : b - (starRingEnd ℂ c) • b' ∈ M'.sm τ := Submodule.subset_span (hU'.smooth _ hdK)
    have h0 : b - (starRingEnd ℂ c) • b' = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℂ)]
      have e₁ := hbA ⟨_, hsm⟩
      have e₂ := hbA' ⟨_, hsm⟩
      have e₃ := hK P ⟨_, hsm⟩ hdK
      rw [e₃, inner_smul_right] at e₁
      rw [inner_sub_left, inner_smul_left, ← e₁, ← e₂]
      simp
    rw [sub_eq_zero] at h0
    rw [inner_smul_right, hbA, hbA', h0, inner_smul_left]
    simp
  by_cases h0 : ∃ A₁, LocW M M' τ aS aT A₁ ∧ A₁ ≠ 0
  · obtain ⟨A₁, hA₁, hne⟩ := h0
    obtain ⟨c₁, hc₁⟩ := key A₁ hA₁
    have hc₁0 : c₁ ≠ 0 := by
      rintro rfl
      refine hne ?_
      have h := uniq A₁ A₁ 0 hA₁ hA₁ fun P y hy => by
        obtain ⟨x, hx⟩ := hy
        have h := hc₁ P x y hx.symm
        rw [zero_smul] at h
        rw [zero_smul]
        exact U.map_eq_zero_iff.mp h
      rwa [zero_smul] at h
    refine ⟨A₁, fun A hA => ?_⟩
    obtain ⟨c, hc⟩ := key A hA
    refine ⟨c / c₁, uniq A A₁ (c / c₁) hA hA₁ fun P y hy => ?_⟩
    obtain ⟨x, hx⟩ := hy
    apply U.injective
    rw [hc P x y hx.symm, map_smul, hc₁ P x y hx.symm, smul_smul, div_mul_cancel₀ _ hc₁0]
  · push_neg at h0
    exact ⟨0, fun A hA => ⟨0, by rw [smul_zero]; exact h0 A hA⟩⟩

theorem loc_line {X : ProvA} (hX : ChosenSeries X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X)
    (hH : GlobalTheory.Published.HarishChandraModules) (hB : ModelsAreCoverSeries D) (M : DSModel V S) (M' : DSModel W S')
    (τ : D.what₂.Tau) {t : ℕ} {al be ga de : List ℚ} (hd : Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de) {aS aT : ℚ}
    (hS : S τ = dualPar (signed (al ++ be) (ga ++ de) aT))
    (hS' : S' τ = dualPar (signed (al ++ block t ++ de) (ga ++ be) aS)) :
    ∃ A₀ : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ, ∀ A, LocW M M' τ aS aT A → ∃ c : ℂ, A = c • A₀ := by
  obtain ⟨hSB, hTB⟩ := hB
  have hA := hd.1
  have hI := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
  have hlen : (block t).length = t := by simp [block]

  have hsetS : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.HidaSetting X (al.length + be.length) (ga.length + de.length) (al ++ be) (ga ++ de)
      aT S τ := by
    refine ⟨?_, List.length_append, List.length_append, hI.2.1, hX _ _ _ hI.2.1, hS⟩
    have := hA.2.1
    omega
  obtain ⟨⟨e, he⟩, m, hm, hU⟩ := hSB X V S M τ _ _ (al ++ be) (ga ++ de) aT hsetS
  obtain ⟨U, hUm⟩ := hU e he

  have hsetT : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.HidaSetting X (al.length + de.length + t) (ga.length + be.length)
      (al ++ block t ++ de) (ga ++ be) aS S' τ := by
    refine ⟨?_, ?_, List.length_append, hI.2.2.1, hX _ _ _ hI.2.2.1, hS'⟩
    · have := hA.1
      omega
    · simp only [List.length_append, hlen]
      omega
  obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hTB X W S' M' τ _ _ (al ++ block t ++ de) (ga ++ be) aS hsetT
  obtain ⟨U', hUm'⟩ := hU' e' he'
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_fockPolynomialIso_unitaryPair _ _ _ _ V.rank W.rank (M.ε τ) (M'.ε τ) e e' he he'

  have hpq : 1 ≤ al.length + be.length + (ga.length + de.length) := by
    have := hA.2.1
    omega
  set R₁ := X.ds (al.length + be.length) (ga.length + de.length) (ofBlocks (al ++ be) (ga ++ de)) with hR₁
  have hadm : Formalism.MainNotions.SchurIrreducible.AdmGK R₁.HK :=
    (((GlobalTheory.Published.HarishChandraModules.admQ5_of_harishChandraModules hH X) _ _ hpq).1 R₁.U ⟨R₁.nontriv, R₁.irred⟩).2.2 R₁.HK R₁.ι
      ⟨R₁.ι_inj, R₁.ι_range, R₁.der⟩ |>.1
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.T.covariant_pairing_unique_up_to_scalar X _ _ _ _ _ _ hadm (h3.1 t al be ga de hd).2.2
  exact loc_line_of_matches hm hm' hUm hUm' hκ hB₀

theorem itLine (D : D7) (X : ProvA) (hX : ChosenSeries X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (hV : VacChar D)
    (hB : ModelsAreCoverSeries D) (hH : GlobalTheory.Published.HarishChandraModules) : ItLine D := by
  classical
  intro k V W M M' θ ψ hθ hk ω f hω hf It It' hIt hIt'
  obtain ⟨χS, χT, hW, hexp⟩ := hω

  have loc : ∀ τ, ∃ A₀ : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ,
      ∀ A, LocW M M' τ (expS D k τ) (expT D k τ) A → ∃ c : ℂ, A = c • A₀ := by
    intro τ
    obtain ⟨al, be, ga, de, hd, -, h1, h2⟩ := hk τ
    refine loc_line hX h3 hH hB M M' τ hd ?_ ?_
    · unfold parB
      unfold parA at h1
      rw [h1]
    · unfold parB
      unfold parA at h2
      rw [h2]
  choose A₀ hA₀ using loc

  have E : ∀ I₁ I₂ : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M,
      (∀ (P : D.what₂.Tau → LPol W.rank V.rank) (v : M'.Vec) (w : ∀ ρ, M.H ρ),
        ellT M w (inclT M (I₁ (glue P) (PiTensorProduct.tprod ℂ v))) =
          ellT M w (inclT M (I₂ (glue P) (PiTensorProduct.tprod ℂ v)))) → I₁ = I₂ := by
    intro I₁ I₂ h
    have hTL := tensorLaw D V _ M
    refine LinearMap.ext_on_range (GlobalTheory.T.gluing_law_holds D V.rank W.rank).1 fun P => ?_
    refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
    simp only [LinearMap.compMultilinearMap_apply]
    refine hTL.inj (sub_eq_zero.mp (hTL.sep _ fun w => ?_))
    rw [map_sub, h P v w, sub_self]

  have prod : ∀ I : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω (ptOf ψ θ M M' f) I →
      ∃ c : ℂ, ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (v : M'.Vec) (w : ∀ ρ, M.H ρ),
        ellT M w (inclT M (I (glue P) (PiTensorProduct.tprod ℂ v))) =
          c * ∏ ρ, ⟪w ρ, A₀ ρ (P ρ) (v ρ)⟫_ℂ := by
    intro I hI
    have hloc : ∀ (τ : D.what₂.Tau) (a : ∀ ρ, LPol W.rank V.rank × M'.sm ρ × M.H ρ), ∃ c : ℂ, ∀ z,
        ellT M (fun ρ => (Function.update a τ z ρ).2.2) (inclT M (I (glue fun ρ => (Function.update a τ z ρ).1)
          (PiTensorProduct.tprod ℂ fun ρ => (Function.update a τ z ρ).2.1))) = c * ⟪z.2.2, A₀ τ z.1 z.2.1⟫_ℂ := by
      intro τ a
      have hVτ := hV V W _ _ M M' θ ψ χS χT ω f τ (expS D k τ) (expT D k τ) hθ hW (hexp τ).1 (hexp τ).2 hf
      obtain ⟨A, hSemi, hA⟩ := GlobalTheory.T.exists_realIntertwiner_contraction_one_place D V W _ _ M M' θ ψ ω f τ (expS D k τ) (expT D k τ) I hθ hVτ.2.1
        hVτ.2.2 hI (fun ρ => (a ρ).2.1) (fun ρ => (a ρ).2.2)
      obtain ⟨j, hj⟩ := exists_ins (fun ρ => (a ρ).1) τ
      obtain ⟨c, hc⟩ := hA₀ τ (A ∘ₗ j) (locW_of_semiW hSemi hj)
      refine ⟨c, fun z => ?_⟩
      have e₁ : (fun ρ => (Function.update a τ z ρ).1) = Function.update (fun ρ => (a ρ).1) τ z.1 :=
        funext fun ρ => Function.apply_update (fun ρ (x : LPol W.rank V.rank × M'.sm ρ × M.H ρ) => x.1) a τ z ρ
      have e₂ : (fun ρ => (Function.update a τ z ρ).2.1) = Function.update (fun ρ => (a ρ).2.1) τ z.2.1 :=
        funext fun ρ => Function.apply_update (fun ρ (x : LPol W.rank V.rank × M'.sm ρ × M.H ρ) => x.2.1) a τ z ρ
      have e₃ : (fun ρ => (Function.update a τ z ρ).2.2) = Function.update (fun ρ => (a ρ).2.2) τ z.2.2 :=
        funext fun ρ => Function.apply_update (fun ρ (x : LPol W.rank V.rank × M'.sm ρ × M.H ρ) => x.2.2) a τ z ρ
      rw [e₁, e₂, e₃, ← hj, ← hA]
      change ⟪z.2.2, (A ∘ₗ j) z.1 z.2.1⟫_ℂ = _
      rw [hc, LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_right]
    obtain ⟨c, hc⟩ := eq_mul_prod_of_partial (A := fun ρ => LPol W.rank V.rank × M'.sm ρ × M.H ρ)
      (fun ρ z => ⟪z.2.2, A₀ ρ z.1 z.2.1⟫_ℂ)
      (fun a => ellT M (fun ρ => (a ρ).2.2)
        (inclT M (I (glue fun ρ => (a ρ).1) (PiTensorProduct.tprod ℂ fun ρ => (a ρ).2.1)))) hloc
    exact ⟨c, fun P v w => hc fun ρ => (P ρ, v ρ, w ρ)⟩
  obtain ⟨c, hc⟩ := prod It hIt
  obtain ⟨c', hc'⟩ := prod It' hIt'
  have hc0 : c ≠ 0 := by
    rintro rfl
    refine hIt.ne (E _ _ fun P v w => ?_)
    rw [hc, zero_mul]
    simp
  refine ⟨c' / c, E _ _ fun P v w => ?_⟩
  rw [hc', LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul, hc, smul_eq_mul, ← mul_assoc,
    div_mul_cancel₀ _ hc0]

end GlobalTheory.Chain.RealLine

end
