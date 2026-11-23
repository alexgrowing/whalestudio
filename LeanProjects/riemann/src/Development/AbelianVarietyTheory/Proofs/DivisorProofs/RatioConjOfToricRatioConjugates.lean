import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsValueTiedOfIsToricElt
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassTermBoundBetaOfToricDenominator
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.HeckeGal GlobalTheory.ToricDenom
open Cardinal

namespace GlobalTheory.ToricRatioBridge

abbrev algC : Subfield ℂ := (algebraicClosure ℚ ℂ).toSubfield

theorem mem_algC {z : ℂ} : z ∈ algC ↔ IsAlgebraic ℚ z := mem_algebraicClosure_iff

theorem isAlgebraic_finPart {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {m : I → ℤ}
    {χ : HChar E} (hm : HasInf χ φ m) {c : Ideal (OF E)} [Finite (PicO c)] (hu : ∀ y ∈ hatOUnits c, finPart χ y = 1)
    (y : (Af E)ˣ) : IsAlgebraic ℚ (finPart χ y : ℂ) := by
  let M : Subfield ℂ := algC
  let H : Subgroup (Af E)ˣ := M.toSubmonoid.units.comap (finPart χ)
  have hH : ∀ y, y ∈ H ↔ (finPart χ y : ℂ) ∈ M := fun y =>
    ⟨fun h => h.1, fun h => (Submonoid.mem_units_iff _ _).2 ⟨h, by rw [Units.val_inv_eq_inv_val]; exact M.inv_mem h⟩⟩
  have hE : ∀ (σ : E →+* ℂ) (x : E), σ x ∈ M := fun σ x =>
    mem_algC.2 ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom).isAlgebraic
  have hle : princ ⊔ hatOUnits c ≤ H := by
    refine sup_le ?_ fun u h => (hH u).2 (by rw [hu u h]; exact one_mem M)
    rintro _ ⟨k, rfl⟩
    rw [hH, eq_inv_of_mul_eq_one_left (finPart_mul_inf χ k), Units.val_inv_eq_inv_val, (hasInfRatio_iff χ φ m).1 hm k]
    exact inv_mem (prod_mem fun i _ => zpow_mem (div_mem (hE _ _) (hE ((starRingEnd ℂ).comp (φ i)) _)) _)
  let p : PicO c →* (Af E)ˣ ⧸ H := QuotientGroup.map _ _ (MonoidHom.id _) hle
  have : Finite ((Af E)ˣ ⧸ H) := Finite.of_surjective p fun q => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨QuotientGroup.mk y, rfl⟩
  have hn := pow_card_eq_one' (G := (Af E)ˣ ⧸ H) (x := (QuotientGroup.mk y))
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hH, map_pow, Units.val_pow_eq_pow_val] at hn
  exact IsAlgebraic.of_pow Nat.card_pos (mem_algC.1 hn)

theorem exists_eq_of_isAlgebraic {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* ℂ) {z : ℂ} (hz : IsAlgebraic ℚ z) :
    ∃ x : Ω, j x = z := by
  let _ : Algebra Ω ℂ := j.toAlgebra
  have : CharZero Ω := RingHom.charZero j
  have : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun q => (map_ratCast j q).symm
  have hi : IsIntegral Ω z := (hz.isIntegral).tower_top
  obtain ⟨x, hx⟩ := minpoly.mem_range_of_degree_eq_one Ω z
    (IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hi))
  exact ⟨x, hx⟩

theorem comp_eq_of_sqrt {R : Ranks} (H : Host R) (f g : H.E →+* ℂ) (h : f H.sqrtMinusD = g H.sqrtMinusD) :
    f.comp (algebraMap H.K H.E) = g.comp (algebraMap H.K H.E) := by
  refine RingHom.ext fun x => ?_
  have hx : (x : H.E) ∈ Algebra.adjoin ℚ {H.sqrtMinusD} := by
    have h1 : IsIntegral ℚ H.sqrtMinusD := Algebra.IsIntegral.isIntegral _
    have : (x : H.E) ∈ IntermediateField.adjoin ℚ {H.sqrtMinusD} := x.2
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h1.isAlgebraic] at this
    exact this
  have hle : Algebra.adjoin ℚ {H.sqrtMinusD} ≤ AlgHom.equalizer f.toRatAlgHom g.toRatAlgHom :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 h)
  show f (x : H.E) = g (x : H.E)
  exact hle hx

theorem upIdele_eq (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (t : (Af K)ˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.upIdele K E t = Units.map (GlobalTheory.AdeleBaseChange.adMap K E).toMonoidHom t :=
  Units.ext (FiniteAdeleRing.ext _ fun P => (GlobalTheory.CharTransport.locMap_eq K E P _).symm)

theorem countable_of_isAlgClosure (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    Countable Ω := by
  have hK : #K ≤ ℵ₀ := by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
  have : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  rw [← Cardinal.mk_le_aleph0_iff]
  exact (Algebra.IsAlgebraic.cardinalMk_le_max K Ω).trans (max_le hK le_rfl)

end GlobalTheory.ToricRatioBridge

namespace GlobalTheory.ToricRatioBridge

open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols (ToricRatioConjugates IsSymbol classOf conjChar)

theorem ratioConj_of_toricRatioConjugates (hG : ToricRatioConjugates) : GlobalTheory.ToricRational.RatioConj := by
  intro R H I _ φ s κ 𝔣 χ hD Ω _ _ _ j τ₀ hj art ha T₀ hT₀ h0 Q hQ hfin T hT
  have : IsCMField H.E := H.isCMField_hostE
  have hU : UnramFin H.E := GlobalTheory.ToricDenomBridge.host_unramFin H
  let ι : H.K →+* ℂ := (φ τ₀).comp (algebraMap H.K H.E)
  have hι : ∀ i, (φ i).comp (algebraMap H.K H.E) = ι := fun i => comp_eq_of_sqrt H _ _ (hD.2.1 i τ₀)
  let δ : H.K := ⟨H.sqrtMinusD, H.sqd_mem_K⟩
  have hδ : δ ^ 2 = -(H.d : H.K) := Subtype.ext (by push_cast; exact H.sqrtMinusD_sq)
  have hK2 : Module.finrank ℚ H.K = 2 := H.finrank_K
  obtain ⟨T₀', Tw, hT₀', -, hTw, halg, hconj⟩ := hG H.E H.K H.d δ ι I φ s κ 𝔣 Q χ hU hK2 H.hyp.2.1.pos hδ hD.1 hι
    hD.2.2.1 hD.2.2.2.1 hD.2.2.2.2.1 hQ hD.2.2.2.2.2
  have h𝔣 : condQ 𝔣 ∅ = 𝔣 := by simp [condQ]
  have hT₀'' : IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀' := by rw [h𝔣]; exact hT₀'
  have e0 : T₀' = T₀ := hT₀''.unique hT₀
  subst e0
  let up : (PicO (condQ 𝔣 Q) →* Ωˣ) → (PicO (condQ 𝔣 Q) →* ℂˣ) := fun ψ => (Units.map j.toMonoidHom).comp ψ
  have hsum : ∀ ψ', Tw ψ' = ∑ᶠ q, ((ψ' q : ℂˣ) : ℂ)⁻¹ * T q := fun ψ' => by
    obtain ⟨_, S, hS, e⟩ := hTw ψ'
    rw [e]
    refine finsum_congr fun q => ?_
    obtain ⟨S', hS', e'⟩ := hT q
    rw [e', mul_assoc, (hS q).unique hS']
    rfl
  have hΩ : IsAlgClosed Ω := IsAlgClosure.isAlgClosed H.K
  choose ρ hρ using fun ψ => exists_eq_of_isAlgebraic j (halg (up ψ))
  refine ⟨ρ, fun ψ => by rw [hρ, hsum]; rfl, fun g hgE hgl t ht ψ => ?_⟩
  have : Countable Ω := countable_of_isAlgClosure H.K Ω
  obtain ⟨g', hg'⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq j (j.comp g.toRingEquiv.toRingHom)
  have hfix : ∀ z : ℂ, IsAlgebraic ℚ z → (∀ x, j x = z → g x = x) → g' z = z := fun z hz hx => by
    obtain ⟨x, rfl⟩ := exists_eq_of_isAlgebraic j hz
    rw [hg']
    exact congrArg j (hx x rfl)
  have hφ : ∀ i (x : H.E), IsAlgebraic ℚ (φ i x) := fun i x =>
    ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map (φ i).toRatAlgHom).isAlgebraic
  have : Finite (PicO (condQ 𝔣 ∅)) := hT₀.1
  have hl : ∀ y, IsAlgebraic ℚ (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s y) := fun y => by
    have h1 := isAlgebraic_finPart hD.2.2.2.2.2.2.2.1 (c := condQ 𝔣 ∅)
      (OrderUnits.finPart_eq_one H.E I φ hD.1 s κ 𝔣 ∅ χ hU hD.2.2.2.2.1 (fun _ h => absurd h (Finset.notMem_empty _))
        hD.2.2.2.2.2) y
    refine mem_algC.1 (mul_mem (mem_algC.2 h1) ?_)
    rw [Complex.ofReal_pow]
    exact pow_mem (GlobalTheory.ToricRational.modF_mem _ y) s
  have hσ : ∀ x, j (g x) = g' (j x) := fun x => (hg' x).symm
  have hsym : IsSymbol art t g := by rw [IsSymbol, ht, map_inv, inv_inv]
  obtain ⟨e, -⟩ := hconj Ω j art (RingHom.ext hj) ha g' g t (fun i x => hfix _ (hφ i x) fun x' hx' => hgE x' i x hx')
    (fun y => hfix _ (hl y) fun x' hx' => hgl x' y hx') hσ hsym (up ψ)
  have hc : conjChar g' (up ψ) = up ((Units.map g.toRingEquiv.toMonoidHom).comp ψ) :=
    MonoidHom.ext fun q => Units.ext (hg' _)
  have hcls : classOf H.K (condQ 𝔣 Q) t = QuotientGroup.mk (GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.upIdele H.K H.E t) := by
    rw [classOf, upIdele_eq]
  apply j.injective
  rw [hσ, hρ, e, hc, hcls, map_mul, map_inv₀, hρ]
  rfl

end GlobalTheory.ToricRatioBridge
