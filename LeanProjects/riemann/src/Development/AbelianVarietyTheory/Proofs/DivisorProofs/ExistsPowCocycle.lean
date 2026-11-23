import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayMapEqOfRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartSpecMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationIndependentOfChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCombinationSquareZeroLiftsChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartSpecMapCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfSquareZeroThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomEqMulPowOfEqLocalizationAwayStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue.Red

theorem chartHom_pow_mul_eq {R : Type} [CommRing R] (X : Over (Sp R)) (hsm : Smooth X.hom)
    (W : X.left.Opens) (hW : IsAffineOpen W) {S : Type} [CommRing S] (u₁ u₂ : Sp S ⟶ X.left)
    (hu : u₁ ≫ X.hom = u₂ ≫ X.hom) (h₁ : u₁ ⁻¹ᵁ W = ⊤) (h₂ : u₂ ⁻¹ᵁ W = ⊤) (g : S)
    (hg : ∀ x, algebraMap S (Localization.Away g) (chartHom W u₁ h₁ x) =
      algebraMap S (Localization.Away g) (chartHom W u₂ h₂ x)) :
    ∃ M : ℕ, ∀ x, g ^ M * chartHom W u₁ h₁ x = g ^ M * chartHom W u₂ h₂ x := by
  have hle : W ≤ X.hom ⁻¹ᵁ ⊤ := by simp
  let b := (X.hom.appLE ⊤ W hle).hom
  have hft : b.FiniteType := by
    haveI := hsm
    exact HasRingHomProperty.appLE @LocallyOfFiniteType X.hom inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ hle
  have hcomp : ∀ (u : Sp S ⟶ X.left) (h : u ⁻¹ᵁ W = ⊤),
      (chartHom W u h).comp b = (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp
        (u ≫ X.hom).appTop.hom := by
    intro u h
    have e : (u ≫ X.hom).appTop = (u ≫ X.hom).appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    rw [e, ← Scheme.Hom.appLE_comp_appLE u X.hom ⊤ W ⊤ hle h.ge]
    rfl
  letI : Algebra Γ(Sp R, ⊤) Γ(X.left, W) := b.toAlgebra
  letI : Algebra Γ(Sp R, ⊤) S := ((chartHom W u₁ h₁).comp b).toAlgebra
  haveI : Algebra.FiniteType Γ(Sp R, ⊤) Γ(X.left, W) := hft
  let χ₁ : Γ(X.left, W) →ₐ[Γ(Sp R, ⊤)] S := { chartHom W u₁ h₁ with commutes' := fun r => rfl }
  let χ₂ : Γ(X.left, W) →ₐ[Γ(Sp R, ⊤)] S :=
    { chartHom W u₂ h₂ with
      commutes' := fun r => by
        have := congrArg (fun φ : Γ(Sp R, ⊤) →+* S => φ r) ((hcomp u₂ h₂).trans (hu ▸ (hcomp u₁ h₁).symm))
        exact this }
  exact GlobalTheory.T.exists_pow_mul_eq_of_algebraMap_localizationAway_eq _ _ _ χ₁ χ₂ g hg

end GlobalTheory.SecGlue.Red

namespace GlobalTheory.SecGlue.Red

theorem isCombIn_congr {Y : Scheme.{0}} {V : Y.Opens} {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    {u u' c c' : Sp S ⟶ Y} {w w' : ι → (Sp S ⟶ Y)} {a a' : ι → S} (hu : u = u') (hc : c = c')
    (hw : w = w') (ha : a = a') (h : IsCombIn V u c w a) : IsCombIn V u' c' w' a' := by
  subst hu hc hw ha; exact h

theorem isCombIn_one {Y : Scheme.{0}} {V : Y.Opens} {S : Type} [CommRing S] {u c w : Sp S ⟶ Y} {a : S}
    (h : IsCombIn V u c ![w] ![a]) : ∃ (hu : u ⁻¹ᵁ V = ⊤) (hc : c ⁻¹ᵁ V = ⊤) (hw : w ⁻¹ᵁ V = ⊤),
      ∀ x, chartHom V c hc x = chartHom V u hu x + a * (chartHom V w hw x - chartHom V u hu x) := by
  obtain ⟨hu, hc, hw, hx⟩ := h
  exact ⟨hu, hc, hw 0, fun x => by simpa using hx x⟩

theorem isCombIn_two {Y : Scheme.{0}} {V : Y.Opens} {S : Type} [CommRing S] {u c w₀ w₁ : Sp S ⟶ Y}
    {a₀ a₁ : S} (h : IsCombIn V u c ![w₀, w₁] ![a₀, a₁]) :
    ∃ (hu : u ⁻¹ᵁ V = ⊤) (hc : c ⁻¹ᵁ V = ⊤) (hw₀ : w₀ ⁻¹ᵁ V = ⊤) (hw₁ : w₁ ⁻¹ᵁ V = ⊤),
      ∀ x, chartHom V c hc x = chartHom V u hu x + a₀ * (chartHom V w₀ hw₀ x - chartHom V u hu x)
        + a₁ * (chartHom V w₁ hw₁ x - chartHom V u hu x) := by
  obtain ⟨hu, hc, hw, hx⟩ := h
  exact ⟨hu, hc, hw 0, hw 1, fun x => by simpa [Fin.sum_univ_two, add_assoc] using hx x⟩

theorem comp_overR {R : Type} [CommRing R] (X : Over (Sp R)) (a : R) {S : Type} [CommRing S] [Algebra R S]
    (ρ : Localization.Away a →+* S) (hρ : ρ.comp (algebraMap R _) = algebraMap R S)
    (u : Sp (Localization.Away a) ⟶ X.left) (hu : u ≫ X.hom = spMap (algebraMap R _)) :
    (spMap ρ ≫ u) ≫ X.hom = spMap (algebraMap R S) := by
  rw [Category.assoc, hu, ← spMap_comp, hρ]

theorem awR_comp {R : Type} [CommRing R] (x y : R) :
    (IsLocalization.Away.awayToAwayRight (P := Localization.Away (x * y)) x y).comp
      (algebraMap R (Localization.Away x)) = algebraMap R _ :=
  RingHom.ext (IsLocalization.Away.awayToAwayRight_eq x y)

theorem awL_comp {R : Type} [CommRing R] (x y : R) :
    (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (y * x)) x y).comp
      (algebraMap R (Localization.Away x)) = algebraMap R _ :=
  RingHom.ext (IsLocalization.Away.awayToAwayLeft_eq x y)

end GlobalTheory.SecGlue.Red

namespace GlobalTheory.SecGlue.Red

open IsLocalization.Away in
theorem exists_comb_pow {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = ⊥) (X : Over (Sp R)) (hsm : Smooth X.hom)
    (g₀ : Sp R₀ ⟶ X.left) (fj fl fk : R) (Vj Vl W : X.left.Opens) (hVj : IsAffineOpen Vj)
    (hVl : IsAffineOpen Vl) (hW : IsAffineOpen W)
    (ej tj : Sp (Localization.Away fj) ⟶ X.left) (el tl : Sp (Localization.Away fl) ⟶ X.left)
    (ek : Sp (Localization.Away fk) ⟶ X.left)
    (hej : ej ≫ X.hom = spMap (algebraMap R _)) (htj : tj ≫ X.hom = spMap (algebraMap R _))
    (hel : el ≫ X.hom = spMap (algebraMap R _)) (htl : tl ≫ X.hom = spMap (algebraMap R _))
    (rej : spMap (Localization.awayMap π fj) ≫ ej = spMap (algebraMap R₀ (Localization.Away (π fj))) ≫ g₀)
    (rtj : spMap (Localization.awayMap π fj) ≫ tj = spMap (algebraMap R₀ (Localization.Away (π fj))) ≫ g₀)
    (rel : spMap (Localization.awayMap π fl) ≫ el = spMap (algebraMap R₀ (Localization.Away (π fl))) ≫ g₀)
    (rtl : spMap (Localization.awayMap π fl) ≫ tl = spMap (algebraMap R₀ (Localization.Away (π fl))) ≫ g₀)
    (rek : spMap (Localization.awayMap π fk) ≫ ek = spMap (algebraMap R₀ (Localization.Away (π fk))) ≫ g₀)
    (N : ℕ)
    (hcj : IsCombIn Vj (spMap (awayToAwayRight (P := Localization.Away (fj * fk)) fj fk) ≫ ej)
      (spMap (awayToAwayRight (P := Localization.Away (fj * fk)) fj fk) ≫ tj)
      ![spMap (awayToAwayLeft (P := Localization.Away (fj * fk)) fk fj) ≫ ek]
      ![algebraMap R (Localization.Away (fj * fk)) fk ^ N])
    (hcl : IsCombIn Vl (spMap (awayToAwayRight (P := Localization.Away (fl * fk)) fl fk) ≫ el)
      (spMap (awayToAwayRight (P := Localization.Away (fl * fk)) fl fk) ≫ tl)
      ![spMap (awayToAwayLeft (P := Localization.Away (fl * fk)) fk fl) ≫ ek]
      ![algebraMap R (Localization.Away (fl * fk)) fk ^ N])
    (S : Type) [CommRing S] [Algebra R S] (ρj : Localization.Away fj →+* S)
    (ρl : Localization.Away fl →+* S) (hρj : ρj.comp (algebraMap R _) = algebraMap R S)
    (hρl : ρl.comp (algebraMap R _) = algebraMap R S) (hA : (spMap ρj ≫ ej) ⁻¹ᵁ W = ⊤) :
    ∃ c : Sp S ⟶ X.left, IsCombIn W (spMap ρl ≫ el) c ![spMap ρl ≫ tl, spMap ρj ≫ ej]
        ![1, 1 - algebraMap R S fk ^ N] ∧
      ∃ M₀ : ℕ, ∀ (h₁ : (spMap ρj ≫ tj) ⁻¹ᵁ W = ⊤) (h₂ : c ⁻¹ᵁ W = ⊤) x,
        algebraMap R S fk ^ M₀ * chartHom W (spMap ρj ≫ tj) h₁ x =
          algebraMap R S fk ^ M₀ * chartHom W c h₂ x := by
  set fS := algebraMap R S fk with hfS
  let ι : S →+* Localization.Away fS := algebraMap S (Localization.Away fS)
  have hι : ι.comp (algebraMap R S) = algebraMap R (Localization.Away fS) :=
    (IsScalarTower.algebraMap_eq R S _).symm

  have rA := isRed_of_away π hπ g₀ fj ej rej S ρj hρj
  have rTJ := isRed_of_away π hπ g₀ fj tj rtj S ρj hρj
  have rEL := isRed_of_away π hπ g₀ fl el rel S ρl hρl
  have rTL := isRed_of_away π hπ g₀ fl tl rtl S ρl hρl
  have hq := Ideal.Quotient.mk_surjective (I := redI π S)
  have hq2 := ker_mk_sq π hsq S
  have land : ∀ u, IsRed π hπ g₀ S u → u ⁻¹ᵁ W = ⊤ := fun u hu =>
    (GlobalTheory.T.preimage_eq_of_square_zero_thickening S _ _ hq hq2 X.left u _ (hu.eq rA) W).trans hA

  obtain ⟨c, hc, -, hcR⟩ := GlobalTheory.T.exists_affineCombination_squareZero_lifts_chart X.left W hW S _ _ hq hq2 (Fin 2) (spMap ρl ≫ el)
    ![spMap ρl ≫ tl, spMap ρj ≫ ej] ![1, 1 - fS ^ N] (land _ rEL)
    (Fin.forall_fin_two.2 ⟨rTL.eq rEL, rA.eq rEL⟩)
  have oEL := comp_overR X fl ρl hρl el hel
  have hcX : c ≫ X.hom = spMap (algebraMap R S) := by
    rw [hcR R X.hom (Fin.forall_fin_two.2 ⟨(comp_overR X fl ρl hρl tl htl).trans oEL.symm,
      (comp_overR X fj ρj hρj ej hej).trans oEL.symm⟩), oEL]
  refine ⟨c, hc, ?_⟩

  have uk : IsUnit (algebraMap R (Localization.Away fS) fk) := by
    rw [← hι, RingHom.comp_apply]; exact IsLocalization.Away.algebraMap_isUnit fS
  have hιρ : ∀ (a : R) (ρ : Localization.Away a →+* S), ρ.comp (algebraMap R _) = algebraMap R S →
      (ι.comp ρ).comp (algebraMap R _) = algebraMap R (Localization.Away fS) := by
    intro a ρ h; rw [RingHom.comp_assoc, h, hι]
  let εk := IsLocalization.Away.lift (S := Localization.Away fk) fk uk
  have hεk : εk.comp (algebraMap R _) = algebraMap R (Localization.Away fS) :=
    IsLocalization.Away.lift_comp _ _
  have hq' := Ideal.Quotient.mk_surjective (I := redI π (Localization.Away fS))
  have hq2' := ker_mk_sq π hsq (Localization.Away fS)
  have rEK := isRed_of_away π hπ g₀ fk ek rek _ εk hεk

  have side : ∀ (fa : R) (Va : X.left.Opens), IsAffineOpen Va → ∀ (ea ta : Sp (Localization.Away fa) ⟶ X.left)
      (ρa : Localization.Away fa →+* S), ρa.comp (algebraMap R _) = algebraMap R S →
      spMap (Localization.awayMap π fa) ≫ ea =
        spMap (algebraMap R₀ (Localization.Away (π fa))) ≫ g₀ →
      (spMap ρa ≫ ea) ⁻¹ᵁ W = ⊤ →
      IsCombIn Va (spMap (awayToAwayRight (P := Localization.Away (fa * fk)) fa fk) ≫ ea)
        (spMap (awayToAwayRight (P := Localization.Away (fa * fk)) fa fk) ≫ ta)
        ![spMap (awayToAwayLeft (P := Localization.Away (fa * fk)) fk fa) ≫ ek]
        ![algebraMap R (Localization.Away (fa * fk)) fk ^ N] →
      IsCombIn W (spMap ι ≫ spMap ρa ≫ ea) (spMap ι ≫ spMap ρa ≫ ta) ![spMap εk ≫ ek] ![ι fS ^ N] := by
    intro fa Va hVa ea ta ρa hρa rea hEa hca
    have ua : IsUnit (algebraMap R (Localization.Away fS) (fa * fk)) := by
      rw [map_mul]; exact (isUnit_of_away fa _ (hιρ fa ρa hρa)).mul uk
    let β := IsLocalization.Away.lift (S := Localization.Away (fa * fk)) (fa * fk) ua
    have hβ : β.comp (algebraMap R _) = algebraMap R (Localization.Away fS) :=
      IsLocalization.Away.lift_comp _ _
    have e1 : β.comp (awayToAwayRight (P := Localization.Away (fa * fk)) fa fk) = ι.comp ρa :=
      away_ext fa _ _ (by rw [RingHom.comp_assoc, awR_comp, hβ, hιρ fa ρa hρa])
    have e2 : β.comp (awayToAwayLeft (P := Localization.Away (fa * fk)) fk fa) = εk :=
      away_ext fk _ _ (by rw [RingHom.comp_assoc, awL_comp, hβ, hεk])
    have h1 := GlobalTheory.T.isAffineCombinationInChart_specMap_comp X.left Va _ _ β (Fin 1) _ _ _ _ hca
    have h1' : IsCombIn Va (spMap ι ≫ spMap ρa ≫ ea) (spMap ι ≫ spMap ρa ≫ ta)
        ![spMap εk ≫ ek] ![ι fS ^ N] := by
      refine isCombIn_congr ?_ ?_ ?_ ?_ h1
      · rw [← Category.assoc, ← spMap_comp, e1, spMap_comp, Category.assoc]
      · rw [← Category.assoc, ← spMap_comp, e1, spMap_comp, Category.assoc]
      · funext i; fin_cases i
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one]
        rw [← Category.assoc, ← spMap_comp, e2]
      · funext i; fin_cases i
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one, map_pow]
        rw [← RingHom.comp_apply, hβ, ← hι, RingHom.comp_apply]
    exact GlobalTheory.T.isAffineCombination_independent_of_chart X.left Va W hVa hW _ _ _ hq' hq2' (Fin 1) _ _ _ _
      (Fin.forall_fin_one.2 (rEK.eq (isRed_comp π hπ g₀ ι hι (isRed_of_away π hπ g₀ fa ea rea S ρa hρa))))
      h1' (GlobalTheory.SecGlue.preimage_spMap_comp_eq_top ι hEa)
  have sj := side fj Vj hVj ej tj ρj hρj rej hA hcj
  have sl := side fl Vl hVl el tl ρl hρl rel (land _ rEL) hcl
  have sc := GlobalTheory.T.isAffineCombinationInChart_specMap_comp X.left W S _ ι (Fin 2) _ _ _ _ hc
  have sc' : IsCombIn W (spMap ι ≫ spMap ρl ≫ el) (spMap ι ≫ c)
      ![spMap ι ≫ spMap ρl ≫ tl, spMap ι ≫ spMap ρj ≫ ej] ![1, 1 - ι fS ^ N] := by
    refine isCombIn_congr rfl rfl ?_ ?_ sc
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp
  obtain ⟨_, _, _, kj⟩ := isCombIn_one sj
  obtain ⟨_, _, _, kl⟩ := isCombIn_one sl
  obtain ⟨_, _, _, _, kc⟩ := isCombIn_two sc'
  have hTJ := land _ rTJ
  have hTL := land _ rTL
  have hEL := land _ rEL
  have hcW : c ⁻¹ᵁ W = ⊤ := hc.2.1
  obtain ⟨M₀, hM⟩ := chartHom_pow_mul_eq X hsm W hW (spMap ρj ≫ tj) c
    ((comp_overR X fj ρj hρj tj htj).trans hcX.symm) hTJ hcW fS (fun x => by
      have k1 := kj x
      have k2 := kl x
      have k3 := kc x
      simp only [GlobalTheory.SecGlue.chartHom_spMap_comp W ι _ hA, GlobalTheory.SecGlue.chartHom_spMap_comp W ι _ hTJ,
        GlobalTheory.SecGlue.chartHom_spMap_comp W ι _ hEL, GlobalTheory.SecGlue.chartHom_spMap_comp W ι _ hTL,
        GlobalTheory.SecGlue.chartHom_spMap_comp W ι _ hcW] at k1 k2 k3
      linear_combination k1 - k3 - k2)
  exact ⟨M₀, fun h₁ h₂ x => hM x⟩

end GlobalTheory.SecGlue.Red

namespace GlobalTheory.SecGlue.Red

theorem affineCombination_squareZero_lifts_cocycle {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = ⊥) (X : Over (Sp R))
    (g₀ : Sp R₀ ⟶ X.left) (fj fl fk : R) (Vj Vl W : X.left.Opens) (hVj : IsAffineOpen Vj)
    (hVl : IsAffineOpen Vl) (hW : IsAffineOpen W)
    (ej tj t'j : Sp (Localization.Away fj) ⟶ X.left) (el tl t'l : Sp (Localization.Away fl) ⟶ X.left)
    (rej : spMap (Localization.awayMap π fj) ≫ ej = spMap (algebraMap R₀ (Localization.Away (π fj))) ≫ g₀)
    (rtj : spMap (Localization.awayMap π fj) ≫ tj = spMap (algebraMap R₀ (Localization.Away (π fj))) ≫ g₀)
    (rel : spMap (Localization.awayMap π fl) ≫ el = spMap (algebraMap R₀ (Localization.Away (π fl))) ≫ g₀)
    (rtl : spMap (Localization.awayMap π fl) ≫ tl = spMap (algebraMap R₀ (Localization.Away (π fl))) ≫ g₀)
    (N M M₀ : ℕ) (hM : M₀ ≤ M)
    (h'j : IsCombIn Vj ej t'j ![tj] ![algebraMap R (Localization.Away fj) fk ^ M])
    (h'l : IsCombIn Vl el t'l ![tl] ![algebraMap R (Localization.Away fl) fk ^ M])
    (S : Type) [CommRing S] [Algebra R S] (ρj : Localization.Away fj →+* S)
    (ρl : Localization.Away fl →+* S) (hρj : ρj.comp (algebraMap R _) = algebraMap R S)
    (hρl : ρl.comp (algebraMap R _) = algebraMap R S) (hA : (spMap ρj ≫ ej) ⁻¹ᵁ W = ⊤)
    (c : Sp S ⟶ X.left)
    (hc : IsCombIn W (spMap ρl ≫ el) c ![spMap ρl ≫ tl, spMap ρj ≫ ej] ![1, 1 - algebraMap R S fk ^ N])
    (hM₀ : ∀ (h₁ : (spMap ρj ≫ tj) ⁻¹ᵁ W = ⊤) (h₂ : c ⁻¹ᵁ W = ⊤) x,
      algebraMap R S fk ^ M₀ * chartHom W (spMap ρj ≫ tj) h₁ x =
        algebraMap R S fk ^ M₀ * chartHom W c h₂ x) :
    IsCombIn W (spMap ρl ≫ el) (spMap ρj ≫ t'j) ![spMap ρl ≫ t'l, spMap ρj ≫ ej]
      ![1, 1 - algebraMap R S fk ^ (N + M)] := by
  set fS := algebraMap R S fk with hfS
  have rA := isRed_of_away π hπ g₀ fj ej rej S ρj hρj
  have rTJ := isRed_of_away π hπ g₀ fj tj rtj S ρj hρj
  have rEL := isRed_of_away π hπ g₀ fl el rel S ρl hρl
  have rTL := isRed_of_away π hπ g₀ fl tl rtl S ρl hρl
  have hq := Ideal.Quotient.mk_surjective (I := redI π S)
  have hq2 := ker_mk_sq π hsq S
  have land : ∀ u, IsRed π hπ g₀ S u → u ⁻¹ᵁ W = ⊤ := fun u hu =>
    (GlobalTheory.T.preimage_eq_of_square_zero_thickening S _ _ hq hq2 X.left u _ (hu.eq rA) W).trans hA
  have move : ∀ (fa : R) (Va : X.left.Opens), IsAffineOpen Va →
      ∀ (ea ta t'a : Sp (Localization.Away fa) ⟶ X.left) (ρa : Localization.Away fa →+* S),
      ρa.comp (algebraMap R _) = algebraMap R S →
      IsRed π hπ g₀ S (spMap ρa ≫ ea) → IsRed π hπ g₀ S (spMap ρa ≫ ta) →
      IsCombIn Va ea t'a ![ta] ![algebraMap R (Localization.Away fa) fk ^ M] →
      IsCombIn W (spMap ρa ≫ ea) (spMap ρa ≫ t'a) ![spMap ρa ≫ ta] ![fS ^ M] := by
    intro fa Va hVa ea ta t'a ρa hρa rE rT h
    have a1 := GlobalTheory.T.isAffineCombinationInChart_specMap_comp X.left Va _ S ρa (Fin 1) _ _ _ _ h
    have a1' : IsCombIn Va (spMap ρa ≫ ea) (spMap ρa ≫ t'a) ![spMap ρa ≫ ta] ![fS ^ M] := by
      refine isCombIn_congr rfl rfl ?_ ?_ a1
      · funext i; fin_cases i; rfl
      · funext i; fin_cases i
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one, map_pow]
        rw [← RingHom.comp_apply, hρa]
    exact GlobalTheory.T.isAffineCombination_independent_of_chart X.left Va W hVa hW S _ _ hq hq2 (Fin 1) _ _ _ _
      (Fin.forall_fin_one.2 (rT.eq rE)) a1' (land _ rE)
  obtain ⟨hA', hT'J, hTJ, k1⟩ := isCombIn_one (move fj Vj hVj ej tj t'j ρj hρj rA rTJ h'j)
  obtain ⟨hEL, hT'L, hTL, k2⟩ := isCombIn_one (move fl Vl hVl el tl t'l ρl hρl rEL rTL h'l)
  obtain ⟨_, hcW, _, _, k3⟩ := isCombIn_two hc
  refine ⟨hEL, hT'J, Fin.forall_fin_two.2 ⟨hT'L, hA⟩, fun x => ?_⟩
  have k4 := hM₀ hTJ hcW x
  have k1 := k1 x
  have k2 := k2 x
  have k3 := k3 x
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
  rw [Fin.sum_univ_two]
  show chartHom W _ hT'J x = chartHom W _ hEL x +
    ((1 : S) * (chartHom W (spMap ρl ≫ t'l) hT'L x - chartHom W _ hEL x) +
      (1 - fS ^ (N + (M₀ + d))) * (chartHom W (spMap ρj ≫ ej) hA x - chartHom W _ hEL x))
  linear_combination k1 - k2 + fS ^ (M₀ + d) * k3 + fS ^ d * k4

end GlobalTheory.SecGlue.Red

open GlobalTheory.SecGlue GlobalTheory.SecGlue.Red IsLocalization.Away in

theorem GlobalTheory.SecGlue.exists_pow_cocycle : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Fintype κ] (f : κ → R), ∀ (V : κ → X.left.Opens), (∀ k, IsAffineOpen (V k)) →
    ∀ (e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left),
    (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) →
    (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) →
    (∀ k, e k ⁻¹ᵁ V k = ⊤) →
    ∀ (N : ℕ) (t : κ → ∀ j, Sp (Localization.Away (f j)) ⟶ X.left),
    (∀ k j, t k j ≫ X.hom = spMap (algebraMap R (Localization.Away (f j)))) →
    (∀ k j, spMap (Localization.awayMap π (f j)) ≫ t k j = spMap (algebraMap R₀ (Localization.Away (π (f j)))) ≫ g₀) →
    (∀ k j, t k j ⁻¹ᵁ V j = ⊤) →
    (∀ k j, GlobalTheory.SecGlue.IsCombIn (V j) (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j) (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ t k j)
        ![spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k] ![algebraMap R (Localization.Away (f j * f k)) (f k) ^ N]) →
    ∀ (n : κ → κ → ℕ) (s : ∀ j l, Fin (n j l) → Localization.Away (f j * f l)) (W : ∀ j l, Fin (n j l) → X.left.Opens),
    (∀ j l, Ideal.span (Set.range (s j l)) = ⊤) → (∀ j l i, IsAffineOpen (W j l i)) →
    (∀ j l i, (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j) ⁻¹ᵁ W j l i = ⊤) →
    ∃ (M : ℕ) (t' : κ → ∀ j, Sp (Localization.Away (f j)) ⟶ X.left),
      (∀ k j, t' k j ≫ X.hom = spMap (algebraMap R (Localization.Away (f j)))) ∧
      (∀ k j, spMap (Localization.awayMap π (f j)) ≫ t' k j = spMap (algebraMap R₀ (Localization.Away (π (f j)))) ≫ g₀) ∧
      (∀ k j, t' k j ⁻¹ᵁ V j = ⊤) ∧
      ∀ j l k i, GlobalTheory.SecGlue.IsCombIn (W j l i) (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ e l)
        (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ t' k j)
        ![spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ t' k l, spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j]
        ![1, 1 - algebraMap R (Localization.Away (s j l i)) (f k) ^ (N + M)] := by
  intro R R₀ _ _ π hπ hsq X hsm g₀ _hg₀ κ _ f V hV e he hered hev N t ht htred htv hcomb n s W hs hW hej
  let ρR : ∀ j l (i : Fin (n j l)), Localization.Away (f j) →+* Localization.Away (s j l i) :=
    fun j l i => (algebraMap (Localization.Away (f j * f l)) _).comp
      (awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l))
  let ρL : ∀ j l (i : Fin (n j l)), Localization.Away (f l) →+* Localization.Away (s j l i) :=
    fun j l i => (algebraMap (Localization.Away (f j * f l)) _).comp
      (awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j))
  have hρR : ∀ j l i, (ρR j l i).comp (algebraMap R _) = algebraMap R _ := fun j l i => by
    simp only [ρR]; rw [RingHom.comp_assoc, awR_comp, ← IsScalarTower.algebraMap_eq]
  have hρL : ∀ j l i, (ρL j l i).comp (algebraMap R _) = algebraMap R _ := fun j l i => by
    simp only [ρL]; rw [RingHom.comp_assoc, awL_comp, ← IsScalarTower.algebraMap_eq]
  have hA : ∀ j l i, (spMap (ρR j l i) ≫ e j) ⁻¹ᵁ W j l i = ⊤ := fun j l i => by
    have := hej j l i
    rwa [← Category.assoc, ← spMap_comp] at this
  have hQ := fun j l k (i : Fin (n j l)) => exists_comb_pow π hπ hsq X hsm g₀ (f j) (f l) (f k)
    (V j) (V l) (W j l i) (hV j) (hV l) (hW j l i) (e j) (t k j) (e l) (t k l) (e k) (he j) (ht k j)
    (he l) (ht k l) (hered j) (htred k j) (hered l) (htred k l) (hered k) N (hcomb k j) (hcomb k l)
    _ (ρR j l i) (ρL j l i) (hρR j l i) (hρL j l i) (hA j l i)
  choose c hc M₀ hM₀ using hQ
  let M := Finset.univ.sup (fun p : (j : κ) × (l : κ) × κ × Fin (n j l) =>
    M₀ p.1 p.2.1 p.2.2.1 p.2.2.2)
  have hMle : ∀ j l k i, M₀ j l k i ≤ M := fun j l k i =>
    Finset.le_sup (f := fun p : (j : κ) × (l : κ) × κ × Fin (n j l) =>
      M₀ p.1 p.2.1 p.2.2.1 p.2.2.2) (Finset.mem_univ ⟨j, l, k, i⟩)
  have hT := fun k j => GlobalTheory.T.exists_affineCombination_squareZero_lifts_chart X.left (V j) (hV j) (Localization.Away (f j)) _
    (Ideal.Quotient.mk (redI π (Localization.Away (f j)))) Ideal.Quotient.mk_surjective
    (ker_mk_sq π hsq _) (Fin 1) (e j) ![t k j] ![algebraMap R (Localization.Away (f j)) (f k) ^ M]
    (hev j) (Fin.forall_fin_one.2 ((isRed_self π hπ g₀ (f j) (t k j) (htred k j)).eq
      (isRed_self π hπ g₀ (f j) (e j) (hered j))))
  choose t' ht'c ht'q ht'R using hT
  refine ⟨M, t', fun k j => ?_, fun k j => ?_, fun k j => (ht'c k j).2.1, fun j l k i => ?_⟩
  · exact (ht'R k j R X.hom (Fin.forall_fin_one.2 ((ht k j).trans (he j).symm))).trans (he j)
  · exact (awayMap_eq_of_red π (f j) _ _ (ht'q k j)).trans (hered j)
  · have h := affineCombination_squareZero_lifts_cocycle π hπ hsq X g₀ (f j) (f l) (f k) (V j) (V l) (W j l i) (hV j) (hV l) (hW j l i)
      (e j) (t k j) (t' k j) (e l) (t k l) (t' k l) (hered j) (htred k j) (hered l) (htred k l)
      N M (M₀ j l k i) (hMle j l k i) (ht'c k j) (ht'c k l) _ (ρR j l i) (ρL j l i) (hρR j l i)
      (hρL j l i) (hA j l i) (c j l k i) (hc j l k i) (hM₀ j l k i)
    simpa only [ρR, ρL, spMap_comp, Category.assoc] using h
