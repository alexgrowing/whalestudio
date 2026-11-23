import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FibreComparison
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FamilyUnifComponentConst
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpEqOfIsometryMatchingMarkingsStatement

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem cmp_congr_of_ex_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty P) (k : ℕ) (hk : 0 < k) (a b : (Fu.Di i).La)
    (hab : Fu.ex i P ((k : ℂ)⁻¹ • P a) = Fu.ex i P ((k : ℂ)⁻¹ • P b)) : ∃ e, a = b + k • e := by
  have h1 : Fu.ex i P ((k : ℂ)⁻¹ • P a - (k : ℂ)⁻¹ • P b) = 1 := by
    have h2 := Fu.ex_add i P hP ((k : ℂ)⁻¹ • P a - (k : ℂ)⁻¹ • P b) ((k : ℂ)⁻¹ • P b)
    rw [sub_add_cancel, hab] at h2
    exact mul_eq_right.1 h2.symm
  obtain ⟨e, he⟩ := (Fu.ex_ker i P hP _).1 h1
  refine ⟨e, hP.2.1 ?_⟩
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [map_add, map_nsmul, he, ← Nat.cast_smul_eq_nsmul ℂ, smul_sub, smul_inv_smul₀ hk', smul_inv_smul₀ hk']
  abel

theorem cmp_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (A : AnArc (𝓞 E)) (w : ℂ) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty P) (y₀ : Sp ℂ ⟶ Xo.X) (hy : Fu.u i P = y₀)
    (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La)
    (hex : ∀ v, (Fu.ex i P (h v)).left = (π v).left) (hPg : ∀ u, P u = h (A.Pw w (gam u)))
    (k : ℕ) (hk : 0 < k) (x : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (a : (Fu.Di i).La) (la : A.La)
    (h1 : toUnit _ ≫ x = Fu.ex i P ((k : ℂ)⁻¹ • P a)) (h2 : toUnit _ ≫ x = π ((k : ℂ)⁻¹ • A.Pw w la)) :
    ∃ e, gam a = la + k • e := by
  subst hy
  have h3 : ∀ v, Fu.ex i P (h v) = π v := fun v => Over.OverMorphism.ext (hex v)
  obtain ⟨e, he⟩ := cmp_congr_of_ex_eq Fu i P hP k hk a (gam.symm la) (by
    rw [← h1, h2, ← h3, map_smul, hPg (gam.symm la), gam.apply_symm_apply])
  exact ⟨gam e, by rw [he, map_add, map_nsmul, gam.apply_symm_apply]⟩

theorem exists_cmp : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (A : AnArc (𝓞 E)) (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ) (T : ℝ) (yw : ℂ → (Sp ℂ ⟶ Xo.X)) (π : ∀ w, A.V → (Over.mk (yw w) ⟶ Xo.univ.t.G)) (fr : ℂ → Xo.univ.t.PP.L.ι → A.V → ℂ) (laA laM : D.La → A.La), (inferInstance : StarRing (𝓞 E)) = H.starRing → (∀ w la la', lin w la (A.Pw w la') - lin w la' (A.Pw w la) = -(2 * Real.pi * Complex.I) * A.EF la la') → Module.finrank ℂ A.V = g → IsHolTo {w : ℂ | T < w.im} yw → (∀ w : ℂ, T < w.im → yw w ≫ Xo.s = spMap σ ∧ IsFibAt A Xo.univ.t lin cst w (yw w) (π w) (fr w) ∧ (Function.Surjective (π w) → (∀ v, toUnit _ ≫ Xo.univ.etaA v = π w ((l.A : ℂ)⁻¹ • A.Pw w (laA v))) ∧ ∀ v ∈ idealPart D l, toUnit _ ≫ Xo.univ.eta v = π w ((l.M : ℂ)⁻¹ • A.Pw w (laM v)))) → ∃ K : Cmp Fu A yw π laA laM, T ≤ K.T := by
  intro hL hL2 E _ _ _ H _ D l Xo σ g ty Fu A lin cst T yw π fr laA laM hstar hlin hrk hhol hw
  obtain ⟨i, hi⟩ := GlobalTheory.familyUnif_component_const E H D l Xo σ g ty Fu T yw hhol fun w h => (hw w h).1
  obtain ⟨T₀, hT₀⟩ := GlobalTheory.fibre_comparison hL hL2 E H D l Xo σ g ty Fu A lin cst hlin hrk
  obtain ⟨T₁, hT₁⟩ := A.exists_BwMat_posDef
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le

  have key : ∀ w : ℂ, max T (max T₀ T₁) < w.im →
      ∃ (P : (Fu.Di i).La →+ (Fin g → ℂ)) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La),
        IsPeriod (Fu.Di i) ty P ∧ Fu.u i P = yw w ∧ (∀ v, (Fu.ex i P (h v)).left = (π w v).left) ∧
        (∀ u, P u = h (A.Pw w (gam u))) ∧ (∀ u v, A.EF (gam u) (gam v) = (Fu.Di i).EF u v) ∧
        (∀ (e : 𝓞 E) v k, h (A.actV e v) k = ty k (e : E) * h v k) ∧
        (∀ v, ∃ e, gam (Fu.t i v) = laA v + l.A • e) ∧
        ∀ v ∈ idealPart D l, ∃ e, gam (Fu.t i v) = laM v + l.M • e := by
    intro w hwT
    have h1 : T < w.im := lt_of_le_of_lt (le_max_left _ _) hwT
    have h2 : T₀ < w.im := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hwT
    obtain ⟨P, hP, hu⟩ := hi w h1
    obtain ⟨-, hfib, hlev⟩ := hw w h1
    obtain ⟨hs, h, gam, hex, hPg, hEF, hact⟩ := hT₀ w i P (yw w) (π w) (fr w) h2 hP hu hfib
    obtain ⟨hA, hMM⟩ := hlev hs
    exact ⟨P, h, gam, hP, hu, hex, hPg, hEF, hact,
      fun v => cmp_level Fu A w i P hP _ hu (π w) h gam hex hPg l.A l.A_pos _ _ _ (Fu.ex_etaA i P hP v) (hA v),
      fun v hv => cmp_level Fu A w i P hP _ hu (π w) h gam hex hPg l.M hM _ _ _ (Fu.ex_eta i P hP v hv) (hMM v hv)⟩
  obtain ⟨-, h₁, gam₁, -, -, -, -, hEF₁, hact₁, hA₁, hM₁⟩ :=
    key (((max T (max T₀ T₁) + 1 : ℝ) : ℂ) * Complex.I) (by simp)
  let Pw : ℂ → ((Fu.Di i).La →+ (Fin g → ℂ)) := fun w =>
    (h₁.toLinearEquiv.toLinearMap.toAddMonoidHom.comp (A.Pw w)).comp gam₁.toLinearMap.toAddMonoidHom
  have hPw : ∀ w u, Pw w u = h₁ (A.Pw w (gam₁ u)) := fun _ _ => rfl
  have hper : ∀ w : ℂ, max T (max T₀ T₁) < w.im → IsPeriod (Fu.Di i) ty (Pw w) := fun w hwT =>
    A.isPeriod (hT₁ w (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hwT)) (Fu.Di i) ty
      h₁.toLinearEquiv hact₁ gam₁.toAddEquiv (fun a x => gam₁.map_smul a x) hEF₁ (Pw w) (hPw w)
  have hmod : ∀ (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La) (k : ℕ) (a : (Fu.Di i).La) (la : A.La),
      (∃ e, gam a = la + k • e) → (∃ e, gam₁ a = la + k • e) → ∃ e, (gam.trans gam₁.symm) a = a + k • e := by
    rintro gam k a la ⟨e, he⟩ ⟨e₁, he₁⟩
    refine ⟨gam₁.symm (e - e₁), gam₁.injective ?_⟩
    rw [LinearEquiv.trans_apply, gam₁.apply_symm_apply, map_add, map_nsmul, gam₁.apply_symm_apply, he, he₁, smul_sub]
    abel
  have hrig : ∀ w : ℂ, max T (max T₀ T₁) < w.im →
      Fu.u i (Pw w) = yw w ∧ ∀ v, (Fu.ex i (Pw w) (h₁ v)).left = (π w v).left := by
    intro w hwT
    obtain ⟨P, h, gam, hP, hu, hex, hPg, hEF, -, hA, hMM⟩ := key w hwT
    obtain ⟨r1, r2⟩ := GlobalTheory.T.exp_eq_of_isometry_matching_markings E H D l Xo σ g ty Fu i P (Pw w) (gam.trans gam₁.symm)
      (h.symm.trans h₁).toLinearEquiv hstar hP (hper w hwT)
      (fun u v => by
        rw [← hEF₁, LinearEquiv.trans_apply, LinearEquiv.trans_apply, gam₁.apply_symm_apply, gam₁.apply_symm_apply, hEF])
      (fun v hv => hmod gam _ _ _ (hMM v hv) (hM₁ v hv)) (fun v => hmod gam _ _ _ (hA v) (hA₁ v))
      (fun u => by rw [hPw, hPg]; simp)
    refine ⟨r1.symm.trans hu, fun v => ?_⟩
    have := r2 (h v)
    rw [hex] at this
    rw [← this]
    simp
  exact ⟨⟨i, max T (max T₀ T₁), gam₁, h₁, hEF₁, hact₁, Pw, hPw, hper, fun w hwT => (hrig w hwT).1,
    fun w hwT => (hrig w hwT).2, hA₁, hM₁⟩, le_max_left _ _⟩

end GlobalTheory.ArcPts
