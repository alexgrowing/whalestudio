import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsChartIncOrd
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsDehomogOrd
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsLocalMultOrd
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ord_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (x : R) :
    Ring.ord S (e x) = Ring.ord R x := by
  have : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  let g := Ideal.quotientEquiv (Ideal.span {x}) (Ideal.span {e x}) e
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  let f : (R ⧸ Ideal.span {x}) →ₛₗ[(e : R →+* S)] (S ⧸ Ideal.span {e x}) :=
    { toFun := g
      map_add' := map_add g
      map_smul' := fun r a => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, g,
          Ideal.quotientEquiv_mk, RingHom.coe_coe] }
  unfold Ring.ord
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact (Order.krullDim_eq_of_orderIso
    (Submodule.orderIsoMapComapOfBijective f (by exact g.bijective))).symm

theorem ord_atPrime_congr {R : Type*} [CommRing R] {P₁ P₂ : Ideal R} [P₁.IsPrime] [P₂.IsPrime]
    (h : P₁ = P₂) (x : R) :
    Ring.ord (Localization.AtPrime P₁) (algebraMap R _ x) =
      Ring.ord (Localization.AtPrime P₂) (algebraMap R _ x) := by
  subst h; rfl

theorem ord_atPrime_map_localization {R : Type*} [CommRing R] (M : Submonoid R) (P : Ideal R)
    [hP : P.IsPrime] (hd : Disjoint (M : Set R) P) [hP' : (P.map (algebraMap R (Localization M))).IsPrime]
    (x : R) :
    Ring.ord (Localization.AtPrime (P.map (algebraMap R (Localization M))))
        (algebraMap (Localization M) _ (algebraMap R _ x)) =
      Ring.ord (Localization.AtPrime P) (algebraMap R _ x) := by
  have hc : (P.map (algebraMap R (Localization M))).comap (algebraMap R (Localization M)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (Localization M) hP hd
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization M
    (P.map (algebraMap R (Localization M)))
  rw [← IsScalarTower.algebraMap_apply, ← e.commutes x]
  exact (ord_ringEquiv e.toRingEquiv _).trans (ord_atPrime_congr hc x)

theorem chartIncIdeal_eq_sup {F : Type} [Field F] {n : ℕ} {I W : Ideal (MvPolynomial (Fin n) F)}
    (t : Fin n → F) (e : ℕ) (h : I ≤ W) :
    chartIncIdeal W t e = W.map (rename Sum.inl) ⊔ chartIncIdeal I t e := by
  unfold chartIncIdeal
  rw [Ideal.map_sup, Ideal.map_sup]
  have hba : I.map (rename (Sum.inl : Fin n → Fin n ⊕ Fin e × Fin n)) ≤
      W.map (rename (Sum.inl : Fin n → Fin n ⊕ Fin e × Fin n)) := Ideal.map_mono h
  apply le_antisymm
  · exact sup_le (sup_le le_sup_left (le_sup_of_le_right (le_sup_of_le_left le_sup_right)))
      (le_sup_of_le_right le_sup_right)
  · exact sup_le (le_sup_of_le_left le_sup_left)
      (sup_le (sup_le (le_sup_of_le_left (le_sup_of_le_left hba)) (le_sup_of_le_left le_sup_right))
        le_sup_right)

private theorem linForm_isHomogeneous_one {F : Type} [Field F] {n : ℕ} (u : Fin n → F) :
    (linForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (u j) j

theorem ChartLocalOrder.proof (h₂ : ChartIncDomain.Statement) (h₃ : ChartKernel.Statement)
    (h₄ : ConeDimOfChowForm.Statement) (h₅ : ConeDimComponent.Statement)
    (h₆ : ChowFormExists.Statement) (h₇ : IncIdealPrime.Statement) (h₈ : ChartIncOrd.Statement)
    (h₉ : DehomogOrd.Statement) (h₁₀ : LocalMultOrd.Statement) : ChartLocalOrder.Statement := by
  intro F _ n e I W f t u q p _ hI hf hu hq hp _ hW hqW htW

  obtain ⟨hWp, hWd⟩ := h₅ F n e I W u hI (h₄ F n (e + 1) I f hI hf) hu hW
  have := hWp.isPrime
  have hIW : I ≤ W := le_sup_left.trans hW.1.1.2
  obtain ⟨g, hg⟩ := h₆ F n e W hWp hWd
  rw [isChowForm_iff] at hg
  have hinc : incIdeal W e = p := by
    have hpr := h₇ F n e W hWp.isPrime hWp.isRelevant
    have hqg : q ∈ Ideal.span {g} := hg.2 ▸ hqW
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hqg
    have hgu : ¬ IsUnit g := fun h => hpr.ne_top (by rw [hg.2, Ideal.span_singleton_eq_top.mpr h])
    have hcu : IsUnit c := (hq.irreducible.isUnit_or_isUnit (by rw [← hc, mul_comm])).resolve_left hgu
    rw [hp, hg.2, Ideal.span_singleton_eq_span_singleton]
    exact ⟨hcu.unit, by rw [IsUnit.unit_spec, mul_comm, hc]⟩

  obtain ⟨hdomW, hkerXW⟩ := h₂ F n e W t hWp htW
  have hkerW := h₃ F n e W t hWp htW
  have hcW := chartIncIdeal_eq_sup t e hIW
  have hcWp : (chartIncIdeal W t e).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdomW
  let π : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* ChartInc I t e := Ideal.Quotient.mk _
  have hkπ : RingHom.ker π = chartIncIdeal I t e := Ideal.mk_ker
  have hQ : W.map (chartX I t e) = (W.map (rename Sum.inl)).map π := by
    change _ = Ideal.map π (Ideal.map (rename Sum.inl).toRingHom _)
    rw [Ideal.map_map]; rfl
  have hmem : ∀ a, π a ∈ W.map (chartX I t e) ↔ a ∈ chartIncIdeal W t e := fun a => by
    have hkb : Ideal.comap π (⊥ : Ideal (ChartInc I t e)) = chartIncIdeal I t e := hkπ
    have hcm : Ideal.comap π ((W.map (rename Sum.inl)).map π) =
        W.map (rename Sum.inl) ⊔ chartIncIdeal I t e := by
      rw [← hkb]; exact Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective _
    rw [← hcW, ← hQ] at hcm
    exact SetLike.ext_iff.mp hcm a
  have h𝔔 : (W.map (chartX I t e)).IsPrime := by
    rw [hQ]
    exact isPrime_map_of_sup_ker π Ideal.Quotient.mk_surjective _ (by rw [hkπ, ← hcW]; exact hcWp)
  have hdisj : Disjoint ((Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl : Submonoid _) :
      Set (ChartInc I t e)) (W.map (chartX I t e)) := by
    rw [Set.disjoint_left]
    intro y hy hyQ
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hy
    have h1 : π (rename Sum.inr s) ∈ W.map (chartX I t e) := hyQ
    have h0 : algebraMap _ (ChartInc W t e) s = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ((hmem _).mp h1)
    have : s ∈ p := by rw [← hinc, ← hkerW]; exact h0
    exact hs this

  have hP : (chartIdeal I t e p W).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ (ChartLoc I t e p) _ h𝔔 hdisj
  refine ⟨hP, ?_⟩
  have hWI : (W.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIW)
  have hWQ : (W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))).IsPrime := by
    have := hdomW
    have hpr : (W ⊔ Ideal.span {linForm t - 1}).IsPrime := hkerXW ▸ RingHom.ker_isPrime _
    exact isPrime_map_of_sup_ker _ Ideal.Quotient.mk_surjective _
      (by rw [Ideal.mk_ker, ← sup_assoc, sup_eq_left.mpr hIW]; exact hpr)
  calc _ = Ring.ord (Localization.AtPrime (W.map (chartX I t e)))
          (algebraMap (ChartInc I t e) _ (chartX I t e (linForm u))) :=
        ord_atPrime_map_localization (hP' := hP) _ _ hdisj _
    _ = Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))))
          (algebraMap _ _ (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}) (linForm u))) :=
        h₈ F n e I W t (linForm u)
    _ = Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk I)))
          (algebraMap _ _ (Ideal.Quotient.mk I (linForm u))) :=
        (h₉ F n I W t hI.isHomog hWp.isHomog hIW htW (linForm u) 1 (linForm_isHomogeneous_one u)).symm
    _ = _ := (h₁₀ (MvPolynomial (Fin n) F) I W (linForm u) hW.1).symm

end GroundTheory.Heights₂.Heights
