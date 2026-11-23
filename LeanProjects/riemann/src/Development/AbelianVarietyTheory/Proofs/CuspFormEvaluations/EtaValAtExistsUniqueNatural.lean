import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FaithfullyFlatPointsBaseChangeDescent
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHomStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNullValueExistsUniqueNaturalLinearStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FullLinearLevelCoverBaseChangeTorsorStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaForm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem finite_latMod (Dw : Datum H) {k : ℕ} (hk : 0 < k) : Finite (LatMod Dw k) := by
  haveI := Dw.fin
  haveI : Module.Finite ℤ (LatMod Dw k) := Module.Finite.trans (𝓞 E) _
  refine Module.finite_of_fg_torsion (M := LatMod Dw k) fun x => ?_
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
  change (k : ℤ) • Submodule.mkQ (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La) x = 0
  rw [natCast_zsmul, ← map_nsmul]
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

theorem finite_levGrp (Dw : Datum H) {k : ℕ} (hk : 0 < k) : Finite (LevGrp Dw k) := by
  haveI := finite_latMod Dw hk
  exact Finite.of_injective (fun g : LevGrp Dw k => (g : LatMod Dw k → LatMod Dw k)) DFunLike.coe_injective

theorem map_etaExpr {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {k : ℕ} (hk : 0 < k) {J : Type} [Fintype J]
    {n : ℕ} (cf : J → ℤ) (x : J → Fin n → LatMod Dw k) (w : LatMod Dw k → S) :
    φ (etaExpr k cf x w) = etaExpr k cf x (fun q => φ (w q)) := by
  haveI := finite_levGrp Dw hk
  haveI := Fintype.ofFinite (LevGrp Dw k)
  simp only [etaExpr, finprod_eq_prod_of_fintype, map_prod, map_sum, map_mul, map_intCast]

theorem etaExpr_comp {S : Type} [CommRing S] {k : ℕ} {J : Type} [Fintype J]
    {n : ℕ} (cf : J → ℤ) (x : J → Fin n → LatMod Dw k) (w : LatMod Dw k → S) (g₀ : LevGrp Dw k) :
    etaExpr k cf x (fun q => w (g₀ q)) = etaExpr k cf x w := by
  unfold etaExpr
  exact finprod_eq_of_bijective (fun g : LevGrp Dw k => g₀ * g) (Group.mulLeft_bijective g₀) fun g => rfl

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_level_baseChange (hL : Laws) {R : ℕ} (hR : Odd R) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T]
    [Algebra c.F T] (ψ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap ψ y z)
    {ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)} {w : LatMod Dw (R ^ 4) → S}
    (hev : IsFullLev Xo (R ^ 4) y.x ev) (hw : ∀ q, IsNullVal Xo c (R ^ 2) y (ev q) (w q)) :
    ∃ ev' : LatMod Dw (R ^ 4) → (ptO Xo z.x ⟶ Xo.univ.t.G), IsFullLev Xo (R ^ 4) z.x ev' ∧
      ∀ q, IsNullVal Xo c (R ^ 2) z (ev' q) (ψ (w q)) := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  let h : ptO Xo z.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hm.1.symm
  refine ⟨fun q => h ≫ ev q,
    ((GlobalTheory.T.fullLinearLevel_cover_baseChange_torsor hL E H Dw l Xo _ hk).2.1 S T ψ.toRingHom y.x z.x h rfl ev hev).1, fun q => ?_⟩
  exact (GlobalTheory.T.thetaNullValue_existsUnique_natural_linear hL E H Dw l Xo c (R ^ 2) hR.pow).2.1 S T ψ y z hm (ev q) (h ≫ ev q) rfl _ (hw q)

theorem existsUnique_nullVal (hL : Laws) {R : ℕ} (hR : Odd R) {S : Type} [CommRing S] [Algebra c.F S]
    {y : FrPt Xo c S} {ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)}
    (hev : IsFullLev Xo (R ^ 4) y.x ev) (q : LatMod Dw (R ^ 4)) : ∃! w, IsNullVal Xo c (R ^ 2) y (ev q) w := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  refine (GlobalTheory.T.thetaNullValue_existsUnique_natural_linear hL E H Dw l Xo c (R ^ 2) hR.pow).1 S y (ev q) ?_
  have h1 := ((GlobalTheory.T.fullLinearLevel_cover_baseChange_torsor hL E H Dw l Xo _ hk).2.1 S S (RingHom.id S) y.x y.x (𝟙 _)
    (by simp [spMap]) ev hev).2 q
  rw [← pow_mul]
  exact h1

theorem etaExpr_eq_of_levels (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw (R ^ 4)) {T : Type} [CommRing T] [Algebra c.F T] {z : FrPt Xo c T}
    {ev ev' : LatMod Dw (R ^ 4) → (ptO Xo z.x ⟶ Xo.univ.t.G)} {w w' : LatMod Dw (R ^ 4) → T}
    (hev : IsFullLev Xo (R ^ 4) z.x ev) (hw : ∀ q, IsNullVal Xo c (R ^ 2) z (ev q) (w q))
    (hev' : IsFullLev Xo (R ^ 4) z.x ev') (hw' : ∀ q, IsNullVal Xo c (R ^ 2) z (ev' q) (w' q)) :
    etaExpr (R ^ 4) cf x w = etaExpr (R ^ 4) cf x w' := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  refine Module.eq_of_localization_maximal (R := T) (fun P _ => Localization.AtPrime P)
    (fun P _ => Algebra.linearMap T (Localization.AtPrime P)) _ _ fun P _ => ?_
  let ψ : T →ₐ[c.F] Localization.AtPrime P := IsScalarTower.toAlgHom c.F T _
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c T _ ψ z
  obtain ⟨e, he, hv⟩ := exists_level_baseChange hL hR ψ hu hev hw
  obtain ⟨e', he', hv'⟩ := exists_level_baseChange hL hR ψ hu hev' hw'
  obtain ⟨g, hg⟩ := ((GlobalTheory.T.fullLinearLevel_cover_baseChange_torsor hL E H Dw l Xo _ hk).2.2.1 _ u.x e he).2 e' he'
  have hww : (fun q => ψ (w' q)) = fun q => ψ (w (g q)) := funext fun q =>
    (existsUnique_nullVal hL hR he (g q)).unique (hg q ▸ hv' q) (hv (g q))
  change algebraMap T (Localization.AtPrime P) (etaExpr (R ^ 4) cf x w) =
    algebraMap T (Localization.AtPrime P) (etaExpr (R ^ 4) cf x w')
  rw [map_etaExpr _ hk, map_etaExpr _ hk]
  exact (etaExpr_comp cf x (fun q => ψ (w q)) g).symm.trans (congrArg _ hww.symm)

theorem map_etaExpr_eq_of_levels (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw (R ^ 4)) {S₁ S₂ T : Type} [CommRing S₁] [Algebra c.F S₁] [CommRing S₂] [Algebra c.F S₂]
    [CommRing T] [Algebra c.F T] (ψ₁ : S₁ →ₐ[c.F] T) (ψ₂ : S₂ →ₐ[c.F] T) {y₁ : FrPt Xo c S₁} {y₂ : FrPt Xo c S₂}
    {z : FrPt Xo c T} (h₁ : FrMap ψ₁ y₁ z) (h₂ : FrMap ψ₂ y₂ z)
    {ev₁ : LatMod Dw (R ^ 4) → (ptO Xo y₁.x ⟶ Xo.univ.t.G)} {w₁ : LatMod Dw (R ^ 4) → S₁}
    {ev₂ : LatMod Dw (R ^ 4) → (ptO Xo y₂.x ⟶ Xo.univ.t.G)} {w₂ : LatMod Dw (R ^ 4) → S₂}
    (hev₁ : IsFullLev Xo (R ^ 4) y₁.x ev₁) (hw₁ : ∀ q, IsNullVal Xo c (R ^ 2) y₁ (ev₁ q) (w₁ q))
    (hev₂ : IsFullLev Xo (R ^ 4) y₂.x ev₂) (hw₂ : ∀ q, IsNullVal Xo c (R ^ 2) y₂ (ev₂ q) (w₂ q)) :
    ψ₁ (etaExpr (R ^ 4) cf x w₁) = ψ₂ (etaExpr (R ^ 4) cf x w₂) := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  obtain ⟨e₁, he₁, hv₁⟩ := exists_level_baseChange hL hR ψ₁ h₁ hev₁ hw₁
  obtain ⟨e₂, he₂, hv₂⟩ := exists_level_baseChange hL hR ψ₂ h₂ hev₂ hw₂
  exact (map_etaExpr ψ₁.toRingHom hk cf x w₁).trans
    ((etaExpr_eq_of_levels hL hR cf x he₁ hv₁ he₂ hv₂).trans (map_etaExpr ψ₂.toRingHom hk cf x w₂).symm)

theorem map_eq_of_etaValAt (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} {cf : J → ℤ}
    {x : J → Fin n → LatMod Dw (R ^ 4)} {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y₀ : FrPt Xo c S} {y : FrPt Xo c T} (hm : FrMap φ y₀ y) {v₀ : S} {v : T}
    (h₀ : EtaValAt Xo c R cf x y₀ v₀) (h : EtaValAt Xo c R cf x y v) : φ v₀ = v := by
  obtain ⟨S', _, _, α, y₀', ev₀, w₀, hα, hmα, hev₀, hw₀, e₀⟩ := h₀
  obtain ⟨T', _, _, β, y', ev, w, hβ, hmβ, hev, hw, e⟩ := h
  obtain ⟨U, _, _, ψ₁, ψ₂, hc, -, hinj⟩ := GlobalTheory.exists_faithfullyFlat_pushout c.F S T' S' (β.comp φ) α hα
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c T' U ψ₁ y'
  have hz₀ : FrMap (ψ₂.comp α) y₀ z :=
    hc ▸ FramedBaseChange.trans _ ψ₁ (FramedBaseChange.trans φ β hm hmβ) hz
  have key := map_etaExpr_eq_of_levels hL hR cf x ψ₁ ψ₂ hz (FramedBaseChange.cancel α ψ₂ hmα hz₀) hev hw hev₀ hw₀
  have hβi : Function.Injective β := hβ.injective
  refine hβi (hinj ?_)
  rw [e, key, ← e₀]
  exact DFunLike.congr_fun hc v₀

theorem exists_etaValAt (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw (R ^ 4)) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ∃ v, EtaValAt Xo c R cf x y v := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  obtain ⟨B, _, φ₀, ev₀, hφ, hev₀⟩ := (GlobalTheory.T.fullLinearLevel_cover_baseChange_torsor hL E H Dw l Xo _ hk).1 S y.x
  letI : Algebra c.F B := (φ₀.comp (algebraMap c.F S)).toAlgebra
  let φ : S →ₐ[c.F] B := { φ₀ with commutes' := fun _ => rfl }
  obtain ⟨y', hm⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c S B φ y
  obtain ⟨ev, hev⟩ : ∃ ev, IsFullLev Xo (R ^ 4) y'.x ev := by
    rw [hm.1]
    exact ⟨ev₀, hev₀⟩
  choose w hw using fun q => (existsUnique_nullVal hL hR hev q).exists
  obtain ⟨v, hv, -⟩ := GlobalTheory.existsUnique_preimage_of_faithfullyFlat c.F S B φ hφ (etaExpr (R ^ 4) cf x w)
    fun T _ _ ψ₁ ψ₂ hc => by
      obtain ⟨z, hz⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c B T ψ₁ y'
      have hz₀ : FrMap (ψ₂.comp φ) y z := hc ▸ FramedBaseChange.trans φ ψ₁ hm hz
      exact map_etaExpr_eq_of_levels hL hR cf x ψ₁ ψ₂ hz (FramedBaseChange.cancel φ ψ₂ hm hz₀) hev hw hev hw
  exact ⟨v, B, inferInstance, inferInstance, φ, y', ev, w, hφ, hm, hev, hw, hv⟩

theorem etaValAt_existsUnique_natural : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : ℕ), Odd R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (x : J → Fin n → LatMod Dw (R ^ 4)), (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃! v, EtaValAt Xo c R cf x y v) ∧ ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ v0 v, EtaValAt Xo c R cf x y0 v0 → EtaValAt Xo c R cf x y v → φ v0 = v := by
  intro hL E _ _ _ H Dw l Xo c R hR J _ n cf x
  refine ⟨fun S _ _ y => ?_, fun S T _ _ _ _ φ y₀ y hm v₀ v h₀ h => map_eq_of_etaValAt hL hR φ hm h₀ h⟩
  obtain ⟨v, hv⟩ := exists_etaValAt hL hR cf x y
  exact ⟨v, hv, fun v' hv' => map_eq_of_etaValAt hL hR (AlgHom.id c.F S) (FramedBaseChange.refl y) hv' hv⟩

end GlobalTheory.EtaForm
