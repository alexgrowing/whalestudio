import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HkLiftIsPullback
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeUniversalIsogenyOnFibresLinearAtRingPointStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeUniversalIsogenyOnFibresPreservesOriginStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGeneratorHeckeIsogenyLineBundleQuotientStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivHeckeKernelSchemePointsHeckeKernels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsRigIsoOfIsGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTransferPts
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.HeckePoint GlobalTheory.HeckeFrCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

theorem isHkIsog_hkMap (Z : Corr Xo P p i) (hA : admitted l P p) {k : Type} [Field k] [IsAlgClosed k]
    (z : Sp k ⟶ Z.Hk) (C : Subgroup (Over.mk (z ≫ Z.π₁) ⟶ Xo.univ.t.G))
    (hC : Z.toKerScheme.Carries z (z ≫ Z.π₁) C) :
    ∃ ψp, IsHkIsog p (z ≫ Z.π₁) (z ≫ Z.π₂) C ((conj _ _).symm (hkMap Z (h := z) rfl rfl)) ψp := by
  obtain ⟨-, hC⟩ := hC
  have hp : p.Prime := hA.2.2.1
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨⟨hom, hfin, het, hsur, hlin, hiso⟩, hlev⟩ := Z.isog
  have := Xo.smooth
  have := Z.et₁
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  have : IsLocallyNoetherian Z.Hk := LocallyOfFiniteType.isLocallyNoetherian Z.π₁
  obtain ⟨ρ, e₂, e₃, e₄, e₅, e₆⟩ := exists_transfer_pts Z.m₁ z
  obtain ⟨ρ₁, f₂, f₃, f₄, f₅, f₆⟩ := exists_transfer_pts Z.m₂ z
  let σ : (Over.mk z ⟶ Z.o₁.t.G) →* (Over.mk z ⟶ Z.o₂.t.G) :=
    MonoidHom.mk' (fun x => x ≫ Z.ψ) fun a c => MonObj.mul_comp a c Z.ψ
  let ψp := ρ₁.toMonoidHom.comp (σ.comp ρ.symm.toMonoidHom)
  have hψ : ∀ x, ψp (ρ x) = ρ₁ (x ≫ Z.ψ) := fun x => congrArg (fun u => ρ₁ (u ≫ Z.ψ)) (ρ.symm_apply_apply x)
  have c₁ := Z.m₁.cart.1
  let α : pullback Xo.univ.t.G.hom (z ≫ Z.π₁) ⟶ Z.o₁.t.G.left := (swap _).inv ≫ hkLift Z z rfl
  have α₁ : α ≫ Z.m₁.cm.F = pullback.fst _ _ := by
    simp only [α, Category.assoc, hkLift_φ, swap_inv_snd]
  have α₂ : α ≫ Z.o₁.t.G.hom = pullback.snd _ _ ≫ z := by
    simp only [α, Category.assoc, hkLift_hom, swap_inv_fst_assoc]
  have hα : ∀ x, fibPt _ (ρ x) ≫ α = x.left := fun x => c₁.hom_ext
    (by rw [Category.assoc, α₁, fibPt, pullback.lift_fst, e₂])
    (by rw [Category.assoc, α₂, fibPt, pullback.lift_snd_assoc, Over.w x]; exact Category.id_comp _)
  have q₁ : (conj _ _).symm (hkMap Z (h := z) rfl rfl) ≫ pullback.fst _ _ = α ≫ Z.ψ.left ≫ Z.m₂.cm.F := by
    show ((swap _).inv ≫ hkMap Z (h := z) rfl rfl ≫ (swap _).hom) ≫ pullback.fst _ _ = _
    simp only [α, Category.assoc, swap_hom_fst, hkMap_snd, hkMap_snd_assoc]
  have q₂ : (conj _ _).symm (hkMap Z (h := z) rfl rfl) ≫ pullback.snd _ _ = pullback.snd _ _ := by
    show ((swap _).inv ≫ hkMap Z (h := z) rfl rfl ≫ (swap _).hom) ≫ pullback.snd _ _ = _
    simp only [Category.assoc, swap_hom_snd, hkMap_fst, hkMap_fst_assoc, swap_inv_fst]
  refine ⟨ψp, by rw [Category.assoc, Category.assoc, Z.base₂], q₂,
    fun x => ?_, fun a x => ?_, fun v => ?_, Subgroup.ext fun x => ?_, fun n x x' c hn h => ?_, fun p' hp' a => ?_⟩
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    apply pullback.hom_ext
    · rw [Category.assoc, q₁, reassoc_of% hα x, hψ, fibPt, pullback.lift_fst, f₂, Over.comp_left,
        Category.assoc]
    · rw [Category.assoc, q₂, fibPt, fibPt, pullback.lift_snd, pullback.lift_snd]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [← e₃, hψ, hψ, ← f₃, Category.assoc, hlin, Category.assoc]
  · obtain ⟨v, rfl⟩ := ρ₁.surjective v
    obtain ⟨x, rfl⟩ := exists_lift_pt Z.ψ z v
    exact ⟨ρ x, hψ x⟩
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [MonoidHom.mem_ker, hψ, map_eq_one_iff _ ρ₁.injective, Z.ker k z x, hC x _ (e₂ x)]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    obtain ⟨x', rfl⟩ := ρ.surjective x'
    rw [hψ, hψ]
    refine (f₄ _ _ _ _).1 ?_
    replace h := (e₄ _ _ _ _).2 h
    let P₁ := polOf Z.o₁.t Z.o₁.proper Z.o₁.ample Z.o₁.ktriv (ObjDim.smoothOfRelativeDimension Z.o₁)
    let P₂ := polOf Z.o₂.t Z.o₂.proper Z.o₂.ample Z.o₂.ktriv (ObjDim.smoothOfRelativeDimension Z.o₂)
    have hn₀ : 0 < n := Nat.pos_of_ne_zero (by
      rintro rfl
      exact hp.one_lt.ne' ((Nat.coprime_zero_left p).1 hn))
    have : Unique (Over.mk z).left := inferInstanceAs (Unique (PrimeSpectrum k))
    obtain ⟨t₁, t₂⟩ := pow_eq_one_of_weilIs hL.kerPow P₁ hn₀ h
    obtain ⟨c', hc', -⟩ := (hL.weil _ P₂ n _).1 (x ≫ Z.ψ) (x' ≫ Z.ψ)
      (by rw [← MonObj.pow_comp, t₁, MonObj.one_comp]) (by rw [← MonObj.pow_comp, t₂, MonObj.one_comp])
    have e := (weilIs_along_hom hL.globalFns _ _ _ Z.ψ _ _ (p ^ 2) n _ x x' _ _ P₁.isAb P₂.isAb P₁.isLB P₂.isLB hom
      hiso hc').2 h
    rw [unitOn_pow]
    exact e ▸ hc'
  · rw [← e₅, ← e₆, hψ, hψ, Category.assoc, Category.assoc, (hlev p' hp' a).1, (hlev p' hp' a).2, f₅, f₆]
    exact ⟨rfl, rfl⟩

theorem exists_isHeckeFam_carries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i), admitted l P p → ∀ (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X), x = h ≫ Z.π₁ → x' = h ≫ Z.π₂ → ∃ Ψ : Gx x ⟶ Gx x', IsHeckeFam P p i Ψ ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'), IsFib χ Ψ Ψ₁ → Z.toKerScheme.Carries (spMap χ ≫ h) x₁ (transKer Xo.univ.t.G Ψ₁) := by
  intro E _ _ _ H Dw l Xo P p i Z hA T _ h x x' hx hx'
  have hcop : p.Coprime l.M' := (Nat.Prime.coprime_iff_not_dvd hA.2.2.1).2 hA.2.2.2.2
  have hfib : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X)
      (Ψ₁ : Gx x₁ ⟶ Gx x₁'), IsFib χ (hkMap Z hx hx') Ψ₁ →
        Xo.univ.t.HeckeKer (Over.mk x₁) Dw P p i (transKer Xo.univ.t.G Ψ₁) ∧
          IsHeckeIsog p (transKer Xo.univ.t.G Ψ₁) Ψ₁ ∧
            Z.toKerScheme.Carries (spMap χ ≫ h) x₁ (transKer Xo.univ.t.G Ψ₁) := by
    intro Ω _ _ χ x₁ x₁' Ψ₁ hΨ
    obtain ⟨h₁, h₂, rfl⟩ := isFib_hkMap Z χ hx hx' hΨ
    subst h₁ h₂
    obtain ⟨C, hCk, hCc⟩ := exists_carried Z.toKerScheme (spMap χ ≫ h) _ rfl
    obtain ⟨ψp, hψ⟩ := isHkIsog_hkMap Z hA (spMap χ ≫ h) C ((hCc C).2 rfl)
    have hK := GlobalTheory.ThetaTrace.transKer_of_isHkIsog hψ
    have hH := (isog_iff hcop _ _ C _).1 ⟨ψp, hψ⟩
    rw [Equiv.apply_symm_apply] at hK hH
    rw [hK]
    exact ⟨hCk, hH, (hCc C).2 rfl⟩
  refine ⟨hkMap Z hx hx', ⟨GlobalTheory.T.heckeUniversalIsogenyOnFibres_linear_at_ringPoint E H Dw l Xo P p i Z T h x x' hx hx', hkMap_etale Z hx hx',
    hkMap_surjective Z hx hx', ?_, fun Ω _ _ χ x₁ x₁' Ψ₁ hΨ =>
      ⟨(hfib Ω χ x₁ x₁' Ψ₁ hΨ).1, (hfib Ω χ x₁ x₁' Ψ₁ hΨ).2.1⟩⟩,
    fun Ω _ _ χ x₁ x₁' Ψ₁ hΨ => (hfib Ω χ x₁ x₁' Ψ₁ hΨ).2.2⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_generator_heckeIsogeny_lineBundle_quotient E H Dw l Xo P p i Z T h x x' hx hx'
  exact exists_isRigIso_of_isGen _ _ _ _ _ _ _ _ β ⟨hkMap_fst Z hx hx', GlobalTheory.T.heckeUniversalIsogenyOnFibres_preserves_origin E H Dw l Xo P p i Z T h x x' hx hx'⟩ hβ

end GlobalTheory.HeckeEx
