import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPerLev
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsThetaKeyDatumKnownValueRatStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SqOfCalculus
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionGeneratorsRational
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldTorsionPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam
open GlobalTheory.ZM.SiegPull

theorem polPB_of_keyPB_alg {R R' : Type} [CommRing R] [CommRing R'] {x' : KeyIn R'} {x : KeyIn R} {f : R →+* R'}
    (H : KeyPB x' x f) : ∃ φ, PolPB x'.P x.P (spMap f) φ := by
  obtain ⟨φ, -, w, hg, -, hp, hw, -⟩ := H
  exact ⟨φ, hp, hg, w, hw⟩

theorem Known.of_keyPB {K K' : Type} [Field K] [Field K'] {y' : KeyIn K'} {y : KeyIn K} {f : K →+* K'}
    (H : KeyPB y' y f) (h : Known K y) : Known K' y' := by
  obtain ⟨t, ht⟩ := h
  exact ⟨f t, fun e x hx => ht (e.comp f) x (keyPB_trans _ _ _ _ _ _ _ _ H hx)⟩

theorem exists_secHom_field (hL : Out.Laws) {K k : Type} [Field K] [Field k] {β : K →+* k} {Q : Out.PolAV (Sp K)}
    {Q' : Out.PolAV (Sp k)} {ψ : Q'.A.left ⟶ Q.A.left} (H : PolPB Q' Q (spMap β) ψ) :
    ∃ ρ : (𝟙_ (Over (Sp K)) ⟶ Q.A) →* (𝟙_ (Over (Sp k)) ⟶ Q'.A), Function.Injective ρ ∧
      (∀ x, (ρ x).left ≫ ψ = spMap β ≫ x.left) ∧
      ∀ (n : ℕ) x y (u : Kˣ), x ^ n = 1 → y ^ n = 1 →
        Out.WeilIs Q'.A Q'.L n (ρ x) (ρ y) (unitOn (Units.map β.toMonoidHom u)) →
        Out.WeilIs Q.A Q.L n x y (unitOn u) := by
  have := Q.isAb.comm
  obtain ⟨b, hb⟩ := UnifPoint.exists_pointEquiv H.1
  let e : Over.mk (spMap β) ⟶ 𝟙_ (Over (Sp K)) := Over.homMk (spMap β) (Category.comp_id _)
  let r : (𝟙_ (Over (Sp K)) ⟶ Q.A) →* (Over.mk (spMap β) ⟶ Q.A) :=
    MonoidHom.mk' (fun x => e ≫ x) fun x y => MonObj.comp_mul _ _ _
  have hρ : ∀ x, (b.symm (r x)).left ≫ ψ = spMap β ≫ x.left := fun x => by
    rw [← hb, b.apply_symm_apply]; rfl
  refine ⟨b.symm.toMonoidHom.comp r, b.symm.injective.comp fun x y hxy => ?_, hρ, fun n x y u hx hy hw => ?_⟩
  · have : Epi e.left := TorsionSeparable.epi_specMap β
    have : Epi e := Over.epi_of_epi_left _
    exact (cancel_epi e).1 hxy
  · obtain ⟨c, hc, -⟩ := (hL.weil _ Q n _).1 x y hx hy
    have h₁ := CommPairing.weilIs_pull hL.globalFns Q.isAb Q.isLB e hc
    have h₂ := (weilIs_grpPullback_of_comm _ _ Q.A Q'.A _ ψ Q.L Q'.L Q.isLB Q'.isLB H.1 H.2.2 _ n _ _
      (pushPt H.1.1.w _) (pushPt H.1.1.w _) _ rfl rfl).1 hw
    have h₃ : Out.WeilIs Q.A Q.L n (e ≫ x) (e ≫ y) (unitOn (Units.map β.toMonoidHom u)) :=
      UnifPoint.weilIs_congr (Category.id_comp _) (hρ x) (hρ y) h₂
    have h₄ := CommutatorPairing.weilIs_unique hL.globalFns Q.isAb Q.isLB h₁ h₃
    obtain ⟨v, rfl⟩ : ∃ v : Kˣ, unitOn v = c :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom c,
        Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of K)) c.val)⟩
    have e' : Units.map e.left.appTop.hom.toMonoidHom (unitOn v) = unitOn (Units.map β.toMonoidHom v) :=
      Units.ext (congrArg (fun q => q.hom v.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
    have h₅ := congrArg Units.val (TorsionGenerators.unitOn_injective (e'.symm.trans h₄))
    obtain rfl : v = u := Units.ext (β.injective h₅)
    exact hc

theorem sqOf_of_iso_of_siegPB {h k : ℕ} {o o' : Type} [CommRing o] [CommRing o'] {ζ : o} {ζ' : o'} {S S' : Scheme.{0}}
    {s : S ⟶ Sp o} {s' : S' ⟶ Sp o'} {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} {f : S' ⟶ S}
    (H : SiegPB c' c f) {P : Out.PolAV S'} (hg : P.g = h) (e : c'.A ≅ P.A) [IsMonHom e.hom]
    (hP : LBIso c'.P ((abelian₂ P.A P.L).pull (lift (fst c'.A c'.A ≫ e.hom) (snd c'.A c'.A ≫ e.hom)).left)) :
    ∃ φ, SqOf P c f φ ∧ ∀ a, (c'.lev a ≫ e.hom).left ≫ φ = f ≫ (c.lev a).left := by
  obtain ⟨φ, φ₂, gp, sq, iP, hlev⟩ := H
  have hinv : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have hΛ : (abelian₂ P.A P.L).IsLB := DVR.linComb_isLB _ P.isLB _ _
  refine ⟨e.inv.left ≫ φ, ⟨((isGrpPullback_of_iso e.symm).comp gp).congr (Category.id_comp _) rfl, hg,
    (e.inv ⊗ₘ e.inv).left ≫ φ₂, isSquare_comp (isSquare_tensor e.inv) sq, ?_⟩, fun a => ?_⟩
  · have k₁ := lbIso_pull_comp hP (e.inv ⊗ₘ e.inv).left
    have k₂ := lbIso_pull_comp iP (e.inv ⊗ₘ e.inv).left
    have k₃ : (e.inv ⊗ₘ e.inv).left ≫ (lift (fst c'.A c'.A ≫ e.hom) (snd c'.A c'.A ≫ e.hom)).left = 𝟙 _ := by
      rw [← Over.comp_left, ← Over.id_left]
      congr 1
      ext1 <;> simp
    rw [k₃] at k₁
    exact LBIso.trans hΛ (pull_isLB c'.isLB _) (pull_isLB c.isLB _)
      (LBIso.trans (pull_isLB c'.isLB _) (pull_isLB hΛ _) hΛ k₁ (GlobalTheory.lbIso_pull_id hΛ)).symm k₂
  · rw [← hlev, ← Category.assoc, ← Over.comp_left, Category.assoc, e.hom_inv_id, Category.comp_id]

theorem PerLev.level {P : Out.PolAV (Sp ℂ)} {g k : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    {lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)} (H : PerLev P τ k lev) (hk : 0 < k) :
    (∀ a b, lev (a + b) = lev a * lev b) ∧ (∀ a, lev a ^ k = 1) ∧
      ∀ z : ℂˣ, (z : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ a b,
        Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn (z ^ omegaStd a b)) := by
  obtain ⟨-, -, -, u, hΛ, hw, hl⟩ := H
  have h0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  refine ⟨fun a b => by rw [hl, hl, hl, per_add, smul_add, u.ex_add], fun a => ?_, fun z hz a b => ?_⟩
  · have hp : ∀ (z) (m : ℕ), u.ex (m • z) = u.ex z ^ m := fun z m => by
      induction m with
      | zero => rw [zero_smul, pow_zero]; exact (u.ker 0).2 (zero_mem _)
      | succ m ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]
    rw [hl, ← hp, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ h0]
    exact (u.ker _).2 ((hΛ _).2 ⟨a, rfl⟩)
  · rw [hl, hl]
    refine hw k a b _ hk ?_
    rw [Units.val_zpow_eq_zpow_val, hz, ← Complex.exp_int_mul]
    congr 1
    ring

theorem exists_known_point : Out.Laws → ThetaUnifAV → ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → NumberField K → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (j : K →+* K₁) (σ₁ : K₁ →+* ℂ) (y : KeyIn K₁) (q : Sp K₁ ⟶ F.X) (φ : y.P.A.left ⟶ F.univ.A.left) (τ : Matrix (Fin h) (Fin h) ℂ), σ₁.comp j = σ ∧ q ≫ F.s = spMap j ∧ Known K₁ y ∧ SqOf y.P F.univ q φ ∧ PtAt F.univ (spMap σ₁ ≫ q) τ := by
  intro hL hT h k K _ ζ σ F hh hk _ hζ hK
  have hk0 : 0 < k := by omega
  obtain ⟨y₀, hg₀, hy₀⟩ := GlobalTheory.T.exists_thetaKeyDatum_known_value_rat hL hT h hh
  let k₀ : IntermediateField ℚ ℂ := σ.toRatAlgHom.fieldRange
  have : FiniteDimensional ℚ k₀ :=
    Module.Finite.of_surjective σ.toRatAlgHom.rangeRestrict.toLinearMap σ.toRatAlgHom.rangeRestrict_surjective
  obtain ⟨y₁, H₁⟩ := exists_keyPB_ring y₀ (algebraMap ℚ k₀)
  obtain ⟨k₁, fin₁, le₁, tors⟩ := exists_numberField_torsion_points hL k₀ y₁.P k hk0
  have : NumberField k₁ := ⟨⟩
  obtain ⟨y, H⟩ := exists_keyPB_ring y₁ (IntermediateField.inclusion le₁).toRingHom
  obtain ⟨x, Hx⟩ := exists_keyPB_ring y (algebraMap k₁ ℂ)
  obtain ⟨φ₀, p₀⟩ := polPB_of_keyPB_alg H₁
  obtain ⟨φ₁, p₁⟩ := polPB_of_keyPB_alg H
  obtain ⟨ψ, pψ⟩ := polPB_of_keyPB_alg Hx
  have hg : y.P.g = h := p₁.2.1.trans (p₀.2.1.trans hg₀)
  obtain ⟨τ, lev, hlev⟩ := exists_perLev hT x.P h k (pψ.2.1.trans hg)
  obtain ⟨ladd, ltors, lweil⟩ := hlev.level hk0
  obtain ⟨ρ, ρinj, hρ, ρw⟩ := exists_secHom_field hL pψ
  have es : spMap (algebraMap k₁ ℂ) ≫ spMap (IntermediateField.inclusion le₁).toRingHom = spMap (algebraMap k₀ ℂ) :=
    (spMap_comp _ _).symm
  obtain ⟨b, hb⟩ := UnifPoint.exists_pointEquiv ((pψ.1.comp p₁.1).congr es rfl)
  obtain ⟨b₁, hb₁⟩ := UnifPoint.exists_pointEquiv p₁.1
  have desc : ∀ a, ∃ t, ρ t = lev a := fun a => by
    obtain ⟨x₂, hx₂, -⟩ := tors k₁ le₁ le_rfl (b (lev a)) (by rw [← map_pow, ltors, map_one])
    refine ⟨b₁.symm x₂, b.injective (Over.OverMorphism.ext ?_)⟩
    rw [← hx₂, hb, ← Category.assoc, hρ, Category.assoc, ← hb₁, b₁.apply_symm_apply]
  choose t ht using desc
  let j : K →+* k₁ := σ.codRestrict k₁.toSubfield fun a => le₁ ⟨a, rfl⟩
  have hj : (algebraMap k₁ ℂ).comp j = σ := rfl
  have hprim : IsPrimitiveRoot (σ ζ) k := by
    rw [hζ, neg_div, Complex.exp_neg]
    exact (Complex.isPrimitiveRoot_exp k hk0.ne').inv
  have hprim₁ : IsPrimitiveRoot (j ζ) k :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap k₁ ℂ) hprim (algebraMap k₁ ℂ).injective
  let ze : k₁ˣ := Units.mk0 (j ζ) (hprim₁.ne_zero hk0.ne')
  have ttors : ∀ a, t a ^ k = 1 := fun a => ρinj (by rw [map_pow, ht, ltors, map_one])
  obtain ⟨c, e, he, pr, iP, hc⟩ := exists_siegPre_of_polAV hL Moduli.cube_of_isLB K k₁ j h k ζ ze y.P t hg
    (Nat.cast_ne_zero.2 hk0.ne') rfl (IsPrimitiveRoot.coe_units_iff.1 hprim₁)
    (fun a a' => ρinj (by rw [map_mul, ht, ht, ht, ladd])) ttors fun a a' =>
      ρw k _ _ _ (ttors a) (ttors a') (by
        rw [ht, ht, map_zpow]
        exact lweil _ hζ a a')
  obtain ⟨q, hq, pb⟩ := F.rep _ _ c inferInstance (fun z => subset_closure (by
    show ((spMap j) z).asIdeal = ⊥
    exact congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (α := PrimeSpectrum K) _ ⊥))) pr
  obtain ⟨φ, sq, hφ⟩ := sqOf_of_iso_of_siegPB pb hg e iP
  refine ⟨k₁, inferInstance, inferInstance, j, algebraMap k₁ ℂ, y, q, φ, τ, hj, hq,
    (hy₀.of_keyPB H₁).of_keyPB H, sq, x.P, lev, ψ ≫ φ, hlev,
    (sqOf_calculus h k K ζ _ _ _ _ F.univ q).1 _ _ _ _ _ sq pψ, fun a => ?_⟩
  rw [← ht, ← Category.assoc, hρ, Category.assoc, Category.assoc, ← hφ, hc]

end GlobalTheory.KeyFam
