import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNonsplitSignTotallyPositiveEqOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.FiniteRefSign
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

noncomputable section

namespace PositivityTheory.BCUSide.HermitianLocalForms

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sgnOn_mul_self {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (Q : K[X]) (A : Matrix (Fin n) (Fin n) K) :
    sgnOn σ H Q A * sgnOn σ H Q A = 1 := by
  unfold sgnOn
  rw [← mul_zpow]
  norm_num

omit [IsCMField E] in

theorem sec_eq {S : Set (Pl E)} (hS : IsSection S) {w u : Pl E} (hw : w ∈ S) (hu : u ∈ S)
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : u = w := by
  obtain ⟨a, -, ha⟩ := hS w
  exact (ha u ⟨hu, h⟩).trans (ha w ⟨hw, rfl⟩).symm

theorem conv_norm {r : ℕ} (Q : SelfRecip E r) {θ : E} (hθ0 : θ ≠ 0) (hθ : IsCMField.complexConj E θ = -θ)
    {d : plus Q} (hd : (d : Fld Q) = algebraMap E _ θ * algebraMap E _ θ)
    (k : Type) [Field k] [Algebra (maximalRealSubfield E) k] (a : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ) (t : (plus Q)ˣ)
    (h : GlobalTheory.TraceClasses.IsValue (1 ⊗ₜ d) ((a : k ⊗[(maximalRealSubfield E)] plus Q) * (1 ⊗ₜ ((t : plus Q))⁻¹))) :
    ∃ z : (k ⊗[(maximalRealSubfield E)] Fld Q)ˣ, inclPlus Q k (a : k ⊗[(maximalRealSubfield E)] plus Q) *
      ((z : k ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q k (z : k ⊗[(maximalRealSubfield E)] Fld Q)) = (1 : k) ⊗ₜ (((t : plus Q) : Fld Q)) := by
  let T : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ :=
    Units.map (Algebra.TensorProduct.includeRight : plus Q →ₐ[(maximalRealSubfield E)] k ⊗[(maximalRealSubfield E)] plus Q).toMonoidHom t
  have hT : ((T⁻¹ : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ) : k ⊗[(maximalRealSubfield E)] plus Q) = 1 ⊗ₜ ((t : plus Q))⁻¹ := by
    rw [← Units.val_inv_eq_inv_val]; rfl
  have hmem : a * T⁻¹ ∈ norms Q k := by
    rw [GlobalTheory.TraceClasses.mem_norms_iff Q hθ0 hθ k hd, Units.val_mul, hT]
    exact h
  obtain ⟨c, hc⟩ := hmem
  have hc' : normHom Q k c = Units.map (inclPlus Q k).toMonoidHom (a * T⁻¹) := hc
  refine ⟨c⁻¹, ?_⟩
  have h4 : (c⁻¹ : (k ⊗[(maximalRealSubfield E)] Fld Q)ˣ).val * involBase Q k (c⁻¹ : (k ⊗[(maximalRealSubfield E)] Fld Q)ˣ).val =
      (normHom Q k c⁻¹ : k ⊗[(maximalRealSubfield E)] Fld Q) := rfl
  have h5 : normHom Q k c⁻¹ = (Units.map (inclPlus Q k).toMonoidHom a)⁻¹ *
      Units.map (inclPlus Q k).toMonoidHom T := by
    rw [map_inv, hc', map_mul, map_inv, mul_inv, inv_inv]
  rw [h4, h5]
  have h6 : inclPlus Q k (a : k ⊗[(maximalRealSubfield E)] plus Q) = (Units.map (inclPlus Q k).toMonoidHom a : k ⊗[(maximalRealSubfield E)] Fld Q) := rfl
  rw [h6, ← Units.val_mul, mul_inv_cancel_left]
  simp [T, inclPlus]

theorem factor_alt (hU : Unr E) {S : Set (Pl E)} (hS : IsSection S) {n : ℕ} {γ₀ : GL (Fin n) E}
    (hP : γ₀.val.charpoly ∈ Ell E n) {H₀ : Matrix (Fin n) (Fin n) E} (h1 : IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀) (h2 : H₀.det ≠ 0)
    (h3 : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀)
    (hpos : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q)
    (hsg0 : ∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1)
    {H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    (hH : ∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = H w)
    (hae : ∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val ∧ H w = cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val)
    (hsg : ∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H w) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1)
    (mw : ∀ w : Pl E, (w.adicCompletion E)[X]) (hmw : ∀ w, ¬ IsSplitAt w → H w = (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) (mw w))
    (wv : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → Pl E) (hwvS : ∀ v, wv v ∈ S) (hwv : ∀ v, (wv v).under (𝓞 (maximalRealSubfield E)) = v)
    {r : ℕ} (Q : SelfRecip E r) (hQ : Q.1 ∣ γ₀.val.charpoly) :
    ∃ t : (plus Q)ˣ,
      (∀ v (hw : ¬ IsSplitAt (wv v)), ∃ z : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] Fld Q)ˣ,
        locPhi hU (wv v) hw v (hwv v) Q (mw (wv v)) * ((z : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q _ (z : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] Fld Q)) =
          (1 : (v.adicCompletion (maximalRealSubfield E))) ⊗ₜ (((t : plus Q) : Fld Q))) ∧
      ∀ u : InfinitePlace (maximalRealSubfield E), ∃ z : (u.Completion ⊗[(maximalRealSubfield E)] Fld Q)ˣ,
        (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q _ (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) = 1 ⊗ₜ (((t : plus Q) : Fld Q)) := by
  classical

  have hx : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ,
      (∀ hw : ¬ IsSplitAt (wv v), inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) =
        locPhi hU (wv v) hw v (hwv v) Q (mw (wv v))) ∧ (IsSplitAt (wv v) → x = 1) := by
    intro v
    by_cases hs : IsSplitAt (wv v)
    · exact ⟨1, fun h => absurd hs h, fun _ => rfl⟩
    · have hHw := hH (wv v) hs
      rw [hmw _ hs] at hHw
      obtain ⟨x, hx⟩ := Lem.exists_plus E hU (wv v) hs v (hwv v) n γ₀ hP H₀ h1 h2 h3 (mw (wv v)) hHw.1 hHw.2.1 r Q hQ
      exact ⟨x, fun _ => hx, fun h => absurd h hs⟩
  choose x hx1 hx2 using hx

  have hB := Filter.eventually_cofinite.1 hae
  set B := {w : Pl E | ¬ (¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val ∧
    H w = cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val)} with hBdef
  set BV := (fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))) '' B with hBV
  have hBVf : BV.Finite := hB.image _
  have hgood : ∀ v, v ∉ BV → x v ∈ norms Q (v.adicCompletion (maximalRealSubfield E)) := by
    intro v hv
    by_cases hs : IsSplitAt (wv v)
    · rw [hx2 v hs]; exact one_mem _
    · have hnB : wv v ∉ B := fun h => hv ⟨wv v, h, hwv v⟩
      simp only [hBdef, Set.mem_ofPred_eq, not_not] at hnB
      obtain ⟨c, hc1, hc2⟩ := hnB hs
      rw [hmw _ hs] at hc2
      exact Lem.norms_of_conj E hU (wv v) hs v (hwv v) n γ₀ hP H₀ h1 h2 h3 (mw (wv v)) c hc1 hc2 r Q hQ (x v) (hx1 v hs)
  set X : GlobalTheory.QuadSymbol.FinFam (maximalRealSubfield E) := fun v => Units.map (Algebra.norm (v.adicCompletion (maximalRealSubfield E)) : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q →* (v.adicCompletion (maximalRealSubfield E))) (x v)
    with hXdef
  have hXn : ∀ v, v ∉ BV → X v ∈ GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E (v.adicCompletion (maximalRealSubfield E)) := fun v hv =>
    Lem.norm_mem E (v.adicCompletion (maximalRealSubfield E)) r Q (x v) (hgood v hv)
  have hA : GlobalTheory.QuadSymbol.AlmostNorm (maximalRealSubfield E) E X := hBVf.subset fun v hv => by
    by_contra h
    exact hv (hXn v h)

  set R : Pl E → ℂ := fun w => if IsSplitAt w then 1 else
    sgnOn (cj w) (H w) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) with hRdef
  have hXR : ∀ v, ((GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E (v.adicCompletion (maximalRealSubfield E)) (X v) : ℤ) : ℂ) = R (wv v) := by
    intro v
    by_cases hs : IsSplitAt (wv v)
    · have h1' : X v = 1 := by simp [hXdef, hx2 v hs]
      rw [h1', (GlobalTheory.QuadSymbol.eta_eq_one_iff).2 (one_mem _)]
      simp [hRdef, if_pos hs]
    · have key := Lem.sign_rel E hU (wv v) hs v (hwv v) n γ₀ hP H₀ h1 h2 h3 hpos (mw (wv v)) r Q hQ (x v) (hx1 v hs)
      rw [← hmw _ hs] at key
      simp only [hRdef, if_neg hs]
      rw [key, mul_assoc, sgnOn_mul_self, mul_one]

  have hwvw : ∀ w ∈ S, wv (w.under (𝓞 (maximalRealSubfield E))) = w := fun w hw => sec_eq hS hw (hwvS _) (hwv _)
  let cz : ℤˣ →* ℂ := (Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)
  have hcz : ∀ a : ℤˣ, cz a = ((a : ℤ) : ℂ) := fun a => rfl
  have hRS : ∀ w ∈ S, R w ≠ 1 → w.under (𝓞 (maximalRealSubfield E)) ∈ BV := by
    intro w hw hR
    by_contra hv
    apply hR
    rw [← hwvw w hw, ← hXR, (GlobalTheory.QuadSymbol.eta_eq_one_iff).2 (hXn _ hv)]
    simp
  set Af : Pl E → ℂ := fun w => if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H w) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) with hAf
  set Bf : Pl E → ℂ := fun w => if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) with hBf
  have hRAB : ∀ w, R w = Af w * Bf w := fun w => by
    simp only [hRdef, hAf, hBf]
    split_ifs <;> simp
  have hBB : ∀ w, Bf w * Bf w = 1 := fun w => by
    simp only [hBf]
    split_ifs
    · simp
    · exact sgnOn_mul_self _ _ _ _
  have hBfin : (S ∩ Function.mulSupport Bf).Finite :=
    (Lem.finite_ref_sign E hU n γ₀ H₀ h1 h2 hpos Q.1).subset fun w hw => by
      obtain ⟨-, hw⟩ := hw
      simp only [Function.mem_mulSupport, hBf] at hw
      split_ifs at hw with hs
      · exact absurd rfl hw
      · exact ⟨hs, hw⟩
  have hRfin : (S ∩ Function.mulSupport R).Finite := by
    refine Set.Finite.of_finite_image (f := fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))) (hBVf.subset ?_)
      ((GlobalTheory.TotPosSign.bijOn_under hS).injOn.mono Set.inter_subset_left)
    rintro _ ⟨w, ⟨hw, hR⟩, rfl⟩
    exact hRS w hw hR
  have hAfin : (S ∩ Function.mulSupport Af).Finite := by
    refine (hRfin.union hBfin).subset fun w ⟨hw, hA⟩ => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_inter_iff, Function.mem_mulSupport, not_or, not_and, not_not] at h
    apply hA
    have e1 := hRAB w
    rw [h.1 hw, h.2 hw, mul_one] at e1
    exact e1.symm
  have hprodS : ∏ᶠ w ∈ S, R w = 1 := by
    rw [finprod_mem_congr rfl fun w _ => hRAB w, finprod_mem_mul_distrib' hAfin hBfin,
      hsg Q.1 Q.2.1 hQ, hsg0 Q.1 Q.2.1 hQ, one_mul]
  have hprod : GlobalTheory.QuadSymbol.etaProd (maximalRealSubfield E) E X 1 = 1 := by
    unfold GlobalTheory.QuadSymbol.etaProd
    have hinf : ∏ u : InfinitePlace (maximalRealSubfield E), GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E u.Completion
        ((1 : GlobalTheory.QuadSymbol.InfFam (maximalRealSubfield E)) u) = 1 :=
      Finset.prod_eq_one fun u _ => (GlobalTheory.QuadSymbol.eta_eq_one_iff).2 (one_mem _)
    rw [hinf, mul_one]
    have hinj : Function.Injective cz := fun a b h => by
      rw [hcz, hcz] at h
      exact Units.ext (by exact_mod_cast h)
    apply hinj
    rw [MonoidHom.map_finprod _ (GlobalTheory.QuadSymbol.AlmostNorm.finite_mulSupport hA), map_one, ← hprodS,
      finprod_mem_eq_of_bijOn _ (GlobalTheory.TotPosSign.bijOn_under hS)
        (g := fun v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) => R (wv v)) (fun w hw => by rw [hwvw w hw]),
      finprod_mem_univ]
    exact finprod_congr fun v => hXR v

  obtain ⟨δ, hδ⟩ := GlobalTheory.QuadSymbol.exists_everywhereNorm_div_of_etaProd_eq_one (maximalRealSubfield E) E X 1 hA hprod
  obtain ⟨θ, hθ0, hθ⟩ : ∃ θ : E, θ ≠ 0 ∧ IsCMField.complexConj E θ = -θ := by
    obtain ⟨a, ha⟩ : ∃ a : E, IsCMField.complexConj E a ≠ a := by
      by_contra h
      push Not at h
      exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
    exact ⟨a - IsCMField.complexConj E a, sub_ne_zero.mpr ha.symm, by simp⟩
  obtain ⟨e, e0, e1⟩ := GlobalTheory.TraceClasses.exists_basis_theta Q hθ0 hθ
  let d : plus Q := ⟨algebraMap E _ θ * algebraMap E _ θ, by
    show invol Q _ = (AlgHom.id _ _) _
    rw [map_mul, GlobalTheory.TraceClasses.invol_theta Q hθ]
    simp⟩
  have hd : (d : Fld Q) = algebraMap E _ θ * algebraMap E _ θ := rfl
  have := GlobalTheory.TraceClasses.isQuadraticExtension Q hθ0 hθ
  have e2 : e 1 * e 1 = algebraMap _ _ d := by rw [e1]; exact hd.symm
  have hadj := GlobalTheory.TraceClasses.adjoin_eq_top Q hθ0 hθ
  have hxfin : {v | ¬ GlobalTheory.TraceClasses.IsValue (1 ⊗ₜ d) (x v : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)}.Finite :=
    hBVf.subset fun v hv => by
      by_contra h
      exact hv ((GlobalTheory.TraceClasses.mem_norms_iff Q hθ0 hθ _ hd (x v)).1 (hgood v h))
  obtain ⟨t, htf, hti⟩ := GlobalTheory.TraceClasses.exists_global e e0 e2 hadj x 1 hxfin δ
    (fun v => hδ.1 v) (fun u => by simpa [GlobalTheory.QuadSymbol.infDiag] using hδ.2 u)
  refine ⟨t, fun v hw => ?_, fun u => ?_⟩
  · obtain ⟨z, hz⟩ := conv_norm Q hθ0 hθ hd _ (x v) t (htf v)
    exact ⟨z, by rw [← hx1 v hw]; exact hz⟩
  · obtain ⟨z, hz⟩ := conv_norm Q hθ0 hθ hd u.Completion 1 t (by simpa using hti u)
    refine ⟨z, ?_⟩
    simpa using hz

theorem transport (hU : Unr E) {w w' : Pl E} (e : w' = w) (hw : ¬ IsSplitAt w) (hw' : ¬ IsSplitAt w')
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))} (hv : w.under (𝓞 (maximalRealSubfield E)) = v) (hv' : w'.under (𝓞 (maximalRealSubfield E)) = v)
    (mw : ∀ w : Pl E, (w.adicCompletion E)[X]) {r : ℕ} (Q : SelfRecip E r) (y : v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] Fld Q)
    (h : ∃ z : (v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] Fld Q)ˣ, locPhi hU w' hw' v hv' Q (mw w') *
      ((z : v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q _ (z : v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] Fld Q)) = y) :
    ∃ z : (v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] Fld Q)ˣ, locPhi hU w hw v hv Q (mw w) *
      ((z : v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q _ (z : v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] Fld Q)) = y := by
  subst e
  exact h

end PositivityTheory.BCUSide.HermitianLocalForms

open PositivityTheory.BCUSide.HermitianLocalForms in

theorem PositivityTheory.BCUSide.L.hermitian_form_local_global : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) → ∀ H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * γ₀.val.map (algebraMap E (w.adicCompletion E)) = H w) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H w = cT (cj w) c.val * H₀.map (algebraMap E (w.adicCompletion E)) * c.val) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H w) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) → ∃ H' : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H' ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H' * γ₀.val = H' ∧ (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H'.map τ = cT (starRingEnd ℂ) Q * Q) ∧ ∀ w, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H'.map (algebraMap E (w.adicCompletion E)) = cT (cj w) c.val * H w * c.val := by
  intro E _ _ _ hU S hS n γ₀ hP H₀ h1 h2 h3 hpos hsg0 H hH hae hsg
  classical

  have hm : ∀ w : Pl E, ∃ m : (w.adicCompletion E)[X], ¬ IsSplitAt w → H w = (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m := by
    intro w
    by_cases hs : IsSplitAt w
    · exact ⟨0, fun h => absurd hs h⟩
    · have hAdet : IsUnit (γ₀.val.map (algebraMap E (w.adicCompletion E))).det := by
        have e : (γ₀.val.map (algebraMap E (w.adicCompletion E))).det = algebraMap E _ γ₀.val.det :=
          (RingHom.map_det _ _).symm
        rw [e]
        exact (γ₀.isUnit.map Matrix.detMonoidHom).map _
      have hAsep : (γ₀.val.map (algebraMap E (w.adicCompletion E))).charpoly.Separable := by
        rw [Matrix.charpoly_map]; exact hP.2.2.1.map
      have hH0 : (H₀.map (algebraMap E (w.adicCompletion E))).det ≠ 0 := by
        have e : (H₀.map (algebraMap E (w.adicCompletion E))).det = algebraMap E _ H₀.det :=
          (RingHom.map_det _ _).symm
        rw [e]; exact (_root_.map_ne_zero _).2 h2
      have hinv0 : cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * (H₀.map (algebraMap E (w.adicCompletion E))) * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (H₀.map (algebraMap E (w.adicCompletion E))) := by
        have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) h3
        simp only [Matrix.map_mul, cT_map hU w hs] at this
        exact this
      obtain ⟨m, hm⟩ := Lem.ratio_poly _ (cj w) n _ _ (H w) hAdet hAsep hH0 hinv0 (hH w hs).2.2
      exact ⟨m, fun _ => hm⟩
  choose mw hmw using hm

  have hsurj : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ w, w ∈ S ∧ w.under (𝓞 (maximalRealSubfield E)) = v := fun v =>
    (GlobalTheory.TotPosSign.bijOn_under hS).surjOn (Set.mem_univ v)
  choose wv hwvS hwv using hsurj

  have ht := fun (r : ℕ) (Q : SelfRecip E r) (hQ : Q.1 ∣ γ₀.val.charpoly) =>
    factor_alt hU hS hP h1 h2 h3 hpos hsg0 hH hae hsg mw hmw wv hwvS hwv Q hQ
  choose! tt htt1 htt2 using ht
  obtain ⟨m, hmQ⟩ := Lem.exists_crt E n γ₀ hP (fun r Q => (((tt r Q : (plus Q)ˣ) : plus Q) : Fld Q))
  have hplus : ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly →
      invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q) := fun r Q hQ => by
    rw [hmQ r Q hQ]
    exact GlobalTheory.TraceClasses.invol_coe Q _
  refine ⟨H₀ * aeval γ₀.val m, Lem.herm_of_plus E n γ₀ hP H₀ h1 h2 h3 m hplus, ?_, ?_, ?_⟩
  ·
    have hc : aeval γ₀.val m * γ₀.val = γ₀.val * aeval γ₀.val m := by
      have := congrArg (aeval γ₀.val) (mul_comm m X)
      simpa only [map_mul, aeval_X] using this
    calc cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * (H₀ * aeval γ₀.val m) * γ₀.val
        = cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * (aeval γ₀.val m * γ₀.val) := by simp only [Matrix.mul_assoc]
      _ = cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val * aeval γ₀.val m := by rw [hc]; simp only [Matrix.mul_assoc]
      _ = H₀ * aeval γ₀.val m := by rw [h3]
  ·
    refine Lem.posDef_of_inf E n γ₀ hP H₀ h1 h2 h3 hpos m hplus fun r Q hQ u => ?_
    obtain ⟨z, hz⟩ := htt2 r Q hQ u
    exact ⟨z, by rw [hmQ r Q hQ]; exact hz⟩
  ·
    intro w hw
    have hwS := mem_S hS hw
    have e : wv (w.under (𝓞 (maximalRealSubfield E))) = w := sec_eq hS hwS (hwvS _) (hwv _)
    obtain ⟨c, hc1, hc2⟩ := Lem.local_assembly E hU w hw (w.under (𝓞 (maximalRealSubfield E))) rfl n γ₀ hP H₀ h1 h2 h3 (mw w) m
      fun r Q hQ => by
        rw [locPhi_atPl, hmQ r Q hQ]
        have hw' : ¬ IsSplitAt (wv (w.under (𝓞 (maximalRealSubfield E)))) := by rw [e]; exact hw
        exact transport hU e hw hw' rfl (hwv _) mw Q _ (htt1 r Q hQ (w.under (𝓞 (maximalRealSubfield E))) hw')
    exact ⟨c, hc1, by rw [hc2, ← hmw w hw]⟩
