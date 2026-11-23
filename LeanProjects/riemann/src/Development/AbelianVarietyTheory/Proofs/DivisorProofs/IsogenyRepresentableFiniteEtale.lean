import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleTrivializingTorsionAbelianSchem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseIsogenyPairBaseChangeGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteEtaleSurjectiveOfIsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoOfSameKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotGlobalHolds
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientPow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.IsogRep

theorem eq_one_iff_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'}
    [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (z : T ⟶ G') :
    z = 1 ↔ z.left ≫ φ = T.hom ≫ f ≫ η[G].left := by
  have e1 : (1 : T ⟶ G').left ≫ φ = T.hom ≫ f ≫ η[G].left := by
    show (T.hom ≫ η[G'].left) ≫ φ = _
    rw [Category.assoc, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h]
  constructor
  · rintro rfl; exact e1
  · intro hz
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [hz, e1]
    · rw [Over.w, Over.w]

theorem comp_pow_hom {S : Scheme.{0}} {T H A : Over S} [GrpObj A] (z : T ⟶ H) (f : H ⟶ A) (n : ℕ) :
    z ≫ f ^ n = (z ≫ f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, comp_one]
  | succ n ih => rw [pow_succ, pow_succ, comp_mul, ih]

theorem exists_quot_quasiInv {Y : Scheme.{0}} [IsLocallyNoetherian Y] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀]
    (H : Over Y) [GrpObj H] (i : H ⟶ A₀) (k : ℕ) (hA : IsAbelianScheme A₀) (hi : IsMonHom i) (hm : Mono i)
    (hf : IsFinite H.hom) (he : Etale H.hom) (hk : i ^ k = 1) :
    ∃ (B : Over Y) (_ : GrpObj B) (_ : IsCommMonObj B) (ψ : A₀ ⟶ B) (ψ' : B ⟶ A₀), IsAbelianScheme B ∧
      IsQuasiInv k ψ ψ' ∧ ∀ (T : Over Y) (x : T ⟶ A₀), x ≫ ψ = 1 ↔ ∃ z : T ⟶ H, z ≫ i = x := by
  obtain ⟨B, gB, q, hB, hqm, hqfin, hqflat, hqsurj, hq⟩ :=
    GlobalTheory.IwLevel.quotGlobal_holds Y A₀ H i hA hi hm hf inferInstance
  have hcB : IsCommMonObj B := hB.comm
  have hker : ∀ (T : Over Y) (x : T ⟶ A₀), x ≫ q = 1 ↔ ∃ z : T ⟶ H, z ≫ i = x := by
    intro T x
    constructor
    · intro h
      have h' : x ≫ q = (1 : T ⟶ A₀) ≫ q := by rw [h, MonObj.one_comp]
      refine ⟨hq.lift x 1 h' ≫ fst H A₀, ?_⟩
      have h1 := hq.lift_fst x 1 h'
      rw [comp_mul, hq.lift_snd, _root_.mul_one] at h1
      rw [Category.assoc, h1]
    · rintro ⟨y, rfl⟩
      have := lift y (1 : T ⟶ A₀) ≫= hq.w
      simpa [comp_mul, ← Category.assoc] using this
  have hK := GlobalTheory.TranslQuotientPow.isMonHom_id_pow A₀ k
  have hqc : QuasiCompact q.left := inferInstance
  obtain ⟨⟨ψ', hψ', hψ'e⟩, hepi⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective Y A₀ B A₀ q ((𝟙 A₀) ^ k)
    hqm hK hqflat hqsurj hqc (fun T x hx => by
      obtain ⟨z, rfl⟩ := (hker T x).1 hx
      rw [GlobalTheory.TranslQuotientPow.comp_id_pow, ← comp_pow_hom, hk, comp_one])
  refine ⟨B, gB, hcB, q, ψ', hB, ⟨hqm, hψ', hψ'e, ?_⟩, hker⟩
  rw [← cancel_epi q, reassoc_of% hψ'e, GlobalTheory.TranslQuotientPow.comp_id_pow q k,
    GlobalTheory.TranslQuotientPow.pow_comp_hom q (𝟙 A₀) k, Category.id_comp]

theorem ker_iff_of_pullbacks {S Y T : Scheme.{0}} {g₀ : Y ⟶ S} {A : Over S} {A₀ : Over Y}
    {φ₀ : A₀.left ⟶ A.left} (h₀ : IsPullback φ₀ A₀.hom A.hom g₀)
    {H : Over Y} {i : H ⟶ A₀} {B : Over Y} [GrpObj B] {ψ : A₀ ⟶ B}
    (hker : ∀ (T' : Over Y) (x : T' ⟶ A₀), x ≫ ψ = 1 ↔ ∃ z : T' ⟶ H, z ≫ i = x)
    {y : T ⟶ Y} {A₁ : Over T} {θ : A₁.left ⟶ A₀.left} (hθ : θ ≫ A₀.hom = A₁.hom ≫ y)
    {B₁ : Over T} [GrpObj B₁] {θ' : B₁.left ⟶ B.left} (hθ' : IsGrpPullback B₁ B y θ') {ψ₁ : A₁ ⟶ B₁}
    (hc : θ ≫ ψ.left = ψ₁.left ≫ θ') (T' : Over T) (g : T' ⟶ A₁) :
    g ≫ ψ₁ = 1 ↔ ∃ h : T'.left ⟶ H.left, h ≫ H.hom = T'.hom ≫ y ∧ h ≫ i.left ≫ φ₀ = g.left ≫ θ ≫ φ₀ := by
  have hP : (g.left ≫ θ) ≫ A₀.hom = T'.hom ≫ y := by
    rw [Category.assoc, hθ, ← Category.assoc, Over.w g]
  let P : Over.mk (T'.hom ≫ y) ⟶ A₀ := Over.homMk (g.left ≫ θ) hP
  have e : P ≫ ψ = 1 ↔ (g.left ≫ θ) ≫ ψ.left = T'.hom ≫ y ≫ η[B].left := by
    rw [← Category.assoc T'.hom]
    constructor
    · intro h; exact congrArg Over.Hom.left h
    · intro h; exact Over.OverMorphism.ext h
  rw [eq_one_iff_of_isGrpPullback hθ', Over.comp_left, Category.assoc, ← hc, ← Category.assoc, ← e, hker]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z.left, Over.w z, ?_⟩
    have := congrArg Over.Hom.left hz
    rw [Over.comp_left] at this
    rw [← Category.assoc, this]
    rfl
  · rintro ⟨h, hH, hφ⟩
    refine ⟨Over.homMk h hH, Over.OverMorphism.ext ?_⟩
    show h ≫ i.left = g.left ≫ θ
    apply h₀.hom_ext
    · rw [Category.assoc, hφ, Category.assoc]
    · rw [Category.assoc, Over.w i, hH, Category.assoc, hθ, ← Category.assoc, Over.w g]

theorem isogeny_rep : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → ∃ (Y : Over S), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (A₀ : Over Y.left) [GrpObj A₀] [IsCommMonObj A₀] (φ₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A Y.hom φ₀ → ∃ (B : Over Y.left) (_ : GrpObj B) (_ : IsCommMonObj B) (ψ : A₀ ⟶ B) (ψ' : B ⟶ A₀), IsAbelianScheme B ∧ IsQuasiInv k ψ ψ' ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ₁ : A₁.left ⟶ A.left) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsGrpPullback A₁ A x φ₁ → IsAbelianScheme B₁ → IsQuasiInv k ψ₁ ψ₁' → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∃ (θ : A₁.left ⟶ A₀.left) (θ' : B₁.left ⟶ B.left), θ ≫ φ₀ = φ₁ ∧ IsGrpPullback A₁ A₀ y θ ∧ IsGrpPullback B₁ B y θ' ∧ θ ≫ ψ.left = ψ₁.left ≫ θ' := by
  intro S _ A _ _ k hA hk0 hk
  obtain ⟨Y, hYf, hYe, hY⟩ := GlobalTheory.T.exists_finite_etale_trivializing_torsion_abelianScheme S A k hA hk0 hk
  refine ⟨Y, hYf, hYe, ?_⟩
  intro A₀ _ _ φ₀ h₀
  haveI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  obtain ⟨H, _, i, hi, hm, hHf, hHe, hik, hH⟩ := hY A₀ φ₀ h₀
  have hA₀ : IsAbelianScheme A₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h₀
  obtain ⟨B, gB, cB, ψ, ψ', hB, hq, hker⟩ := exists_quot_quasiInv A₀ H i k hA₀ hi hm hHf hHe hik
  refine ⟨B, gB, cB, ψ, ψ', hB, hq, ?_⟩
  intro T x A₁ _ _ φ₁ B₁ _ _ ψ₁ ψ₁' h₁ hB₁ hq₁
  have hkT : IsUnit (k : Γ(T, ⊤)) := by
    have := hk.map x.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨hψ₁m, hψ₁'m, e₁, e₂⟩ := hq₁
  have hkill : ∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ ψ₁ = 1 → g ^ k = 1 := by
    intro T' g hg
    rw [← GlobalTheory.TranslQuotientPow.comp_id_pow, ← e₁, ← Category.assoc, hg, one_comp]
  have hA₁ : IsAbelianScheme A₁ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h₁
  obtain ⟨y, ⟨hyx, hyker⟩, hyu⟩ := hH T x A₁ φ₁ B₁ ψ₁ h₁ hB₁ hψ₁m hkill
  have w : φ₁ ≫ A.hom = (A₁.hom ≫ y) ≫ Y.hom := by rw [h₁.1.w, Category.assoc, hyx]
  let θ := h₀.1.lift φ₁ (A₁.hom ≫ y) w
  have hθφ : θ ≫ φ₀ = φ₁ := h₀.1.lift_fst _ _ _
  have hθs : θ ≫ A₀.hom = A₁.hom ≫ y := h₀.1.lift_snd _ _ _
  have hθ : IsGrpPullback A₁ A₀ y θ := IsGrpPullback.cancel h₀ (h₁.congr hyx.symm hθφ.symm) hθs
  obtain ⟨B₂, _, _, θ₂, ψ₂, ψ₂', hB₂, hθ₂, hq₂, hc₂, -⟩ :=
    GlobalTheory.UPel.HT.ES.pullQuasiInv T Y.left y A₀ B k ψ ψ' A₁ θ hB hq hθ
  obtain ⟨hψ₂f, hψ₂e, hψ₂s⟩ := GlobalTheory.UPel.HT.ES.isFinite_etale_surjective_of_isQuasiInv T A₁ B₂ k ψ₂ ψ₂' hA₁ hB₂ hkT hq₂
  haveI := hψ₂f
  haveI := hψ₂e
  have hk₂ := ker_iff_of_pullbacks h₀.1 hker hθs hθ₂ hc₂
  obtain ⟨β, hβi, hβm, hβ⟩ := GlobalTheory.SameKer.exists_iso_of_sameKer T A₁ B₂ B₁ ψ₂ ψ₁' ψ₁ k hB₁ hkT hq₂.1
    hψ₁'m hψ₁m inferInstance hψ₂s inferInstance e₂ (fun T' g => by rw [hyker, hk₂, hθφ])
  refine ⟨y, ⟨hyx, θ, β.left ≫ θ₂, hθφ, hθ, ?_, ?_⟩, ?_⟩
  · haveI := hβi
    haveI : IsMonHom (asIso β).hom := hβm
    exact ((isGrpPullback_of_iso (asIso β)).comp hθ₂).congr (Category.id_comp _) rfl
  · rw [hc₂, ← hβ, Over.comp_left, Category.assoc]
  · rintro y' ⟨hy'x, θ', θ'', hθ'φ, hθ', hθ'', hc'⟩
    apply hyu
    refine ⟨hy'x, fun T' g => ?_⟩
    rw [ker_iff_of_pullbacks h₀.1 hker hθ'.1.w hθ'' hc', hθ'φ]

end GlobalTheory.UPel.HT.ES.IsogRep
