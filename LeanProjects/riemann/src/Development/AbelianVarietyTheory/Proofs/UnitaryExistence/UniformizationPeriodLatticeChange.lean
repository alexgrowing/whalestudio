import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUniqueStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEqNsmulOfDvdPairing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.InversionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.FamRigid

noncomputable def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct])
    (fun a b w => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c a w => by simp [hermForm, Matrix.mulVec_smul, dotProduct_smul])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    imForm Hm z w = (hermForm Hm z w).im := rfl

theorem re_eq_imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    (hermForm Hm z w).re = imForm Hm (Complex.I • z) w := by
  simp [imForm_apply, hermForm, smul_dotProduct]

theorem isBounded_sublevel {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) (c : ℝ) :
    Bornology.IsBounded {z : Fin g → ℂ | (hermForm Hm z z).re ≤ c} := by
  have hc : Continuous fun z : Fin g → ℂ => (hermForm Hm z z).re := by
    unfold hermForm
    refine Complex.continuous_re.comp ?_
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  obtain ⟨m, hm, hle⟩ := (isCompact_sphere (0 : Fin g → ℂ) 1).exists_forall_le' hc.continuousOn
    (a := 0) (fun b hb => hp b (by rintro rfl; simp at hb))
  refine (Metric.isBounded_closedBall (x := (0 : Fin g → ℂ)) (r := 1 + c / m)).subset ?_
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  rw [mem_closedBall_zero_iff]
  by_cases h0 : z = 0
  · subst h0
    have : 0 ≤ c := by simpa [hermForm] using hz
    have := div_nonneg this hm.le
    simp only [norm_zero]
    linarith
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 h0
    have h1 := hle ((‖z‖⁻¹ : ℝ) • z) (by simp [norm_smul, hn.ne'])
    have h2 : (hermForm Hm ((‖z‖⁻¹ : ℝ) • z) ((‖z‖⁻¹ : ℝ) • z)).re =
        ‖z‖⁻¹ * ‖z‖⁻¹ * (hermForm Hm z z).re := by
      rw [re_eq_imForm, re_eq_imForm, smul_comm, map_smul, map_smul, LinearMap.smul_apply,
        smul_eq_mul, smul_eq_mul, _root_.mul_assoc]
    rw [h2] at h1
    have h3 : m * (‖z‖ * ‖z‖) ≤ c := by
      have := mul_le_mul_of_nonneg_right h1 (mul_pos hn hn).le
      refine this.trans (le_trans (le_of_eq ?_) hz)
      field_simp
    have h4 : ‖z‖ * ‖z‖ ≤ c / m := by
      rw [le_div_iff₀ hm]; linarith
    nlinarith

theorem finite_order {g : ℕ} {L : Type} [AddCommGroup L] [Module.Finite ℤ L] (P : L →+ (Fin g → ℂ))
    (hinj : Function.Injective P) (hd : DiscreteTopology P.range)
    (hsp : Submodule.span ℝ (Set.range P) = ⊤) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) (δ : L ≃ₗ[ℤ] L)
    (k : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hk : ∀ a, P (δ a) = k (P a))
    (hiso : ∀ a b, (hermForm Hm (P (δ a)) (P (δ b))).im = (hermForm Hm (P a) (P b)).im) :
    ∃ n, 0 < n ∧ δ ^ n = 1 := by
  have hB : (imForm Hm).compl₁₂ (k.restrictScalars ℝ) (k.restrictScalars ℝ) = imForm Hm := by
    refine LinearMap.ext_on hsp ?_
    rintro _ ⟨a, rfl⟩
    refine LinearMap.ext_on hsp ?_
    rintro _ ⟨b, rfl⟩
    simp only [LinearMap.compl₁₂_apply, LinearMap.restrictScalars_apply, ← hk, imForm_apply, hiso]
  have hQ : ∀ a, (hermForm Hm (P (δ a)) (P (δ a))).re = (hermForm Hm (P a) (P a)).re := by
    intro a
    rw [re_eq_imForm, re_eq_imForm, hk, ← map_smul]
    conv_rhs => rw [← hB]
    rfl
  have hQn : ∀ (n : ℕ) a, (hermForm Hm (P ((δ ^ n) a)) (P ((δ ^ n) a))).re =
      (hermForm Hm (P a) (P a)).re := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih => intro a; rw [pow_succ', LinearEquiv.mul_apply, hQ, ih]
  have hper : ∀ a, ∃ n, 0 < n ∧ (δ ^ n) a = a := by
    intro a
    have hfin := Metric.finite_isBounded_inter_isClosed (s := (P.range : Set (Fin g → ℂ)))
      DiscreteTopology.isDiscrete (isBounded_sublevel Hm hp (hermForm Hm (P a) (P a)).re)
      AddSubgroup.isClosed_of_discrete
    obtain ⟨m, n, hmn, he⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
      (f := fun n : ℕ => P ((δ ^ n) a)) (t := _ ∩ (P.range : Set (Fin g → ℂ))) (fun n => Set.mem_inter
        (show P ((δ ^ n) a) ∈ {z : Fin g → ℂ | (hermForm Hm z z).re ≤ (hermForm Hm (P a) (P a)).re}
          from (hQn n a).le) ⟨_, rfl⟩) hfin
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hmn
    refine ⟨d + 1, Nat.succ_pos _, ?_⟩
    have := hinj he
    rw [add_assoc, pow_add, LinearEquiv.mul_apply] at this
    exact ((δ ^ m).injective this).symm
  choose N hN hNa using hper
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := L)
  refine ⟨∏ a ∈ S, N a, Finset.prod_pos fun a _ => hN a, ?_⟩
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on hS ?_
  intro a ha
  obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem N (Finset.mem_coe.1 ha)
  rw [hd]
  change (δ ^ (N a * d)) a = a
  clear hd
  induction d with
  | zero => rfl
  | succ d ih => rw [Nat.mul_succ, pow_add, LinearEquiv.mul_apply, hNa, ih]

theorem ex_eq_of_level_group : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P P' : (U.Di i).La →+ (Fin g → ℂ)) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di i).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod (U.Di i) ty P → IsPeriod (U.Di i) ty P' → (∀ a b, (U.Di i).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La), ∃ e, gam a = a + l.M • e) → (∀ a, ∃ e, gam a = a + l.A • e) → (∀ a, P' (gam a) = h₀ *ᵥ P a) → IsUnit h₀.det ∧ U.u i P = U.u i P' ∧ ∀ z, (U.ex i P' (h₀ *ᵥ z)).left = (U.ex i P z).left := by
  intro hMink E _ _ _ H D l Xo σ g ty U i P P' gam h₀ hP hP' hiso hM hA hh
  have hsurj : Function.Surjective h₀.mulVec := by
    have : LinearMap.range (h₀.mulVecLin.restrictScalars ℝ) = ⊤ := by
      rw [eq_top_iff, ← hP'.2.2.2.1, Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact ⟨P (gam.symm a), by simp [← hh]⟩
    exact LinearMap.range_eq_top.1 this
  have hu : IsUnit h₀ := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  have hpt : U.u i P = U.u i P' := (U.fibre i P P' hP hP').2
    ⟨gam, LinearEquiv.ofBijective h₀.mulVecLin ⟨Matrix.mulVec_injective_iff_isUnit.2 hu, hsurj⟩,
      hiso, hM, hA, hh⟩
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).1 hu, hpt, ?_⟩
  obtain ⟨h₁, gam₁, hex, hh₁, hiso₁, hM₁, -⟩ :=
    GlobalTheory.T.familyUnif_exp_unique_alt E H D l Xo σ g ty U i i P P' hP hP' hpt
  have hM₁' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La),
      ∃ e, gam₁ a = a + l.M • e := by
    intro a ha
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro v hv b _
      obtain ⟨c, e, rfl⟩ := U.t_surj i b
      obtain ⟨e₁, he₁⟩ := hM₁ (v • c) (Submodule.smul_mem_smul hv Submodule.mem_top)
      obtain ⟨r, hr⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
      refine ⟨e₁ + r • (gam₁ (v • e) - v • e), ?_⟩
      rw [smul_add, ← map_smul, smul_comm v, map_add, he₁, map_nsmul, hr, smul_add, smul_smul,
        smul_sub]
      abel
    · rintro x y ⟨e, he⟩ ⟨e', he'⟩
      exact ⟨e + e', by rw [map_add, he, he', smul_add]; abel⟩
  have f₀ := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (U.Di i) l gam hiso hM
  have f₁ := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (U.Di i) l gam₁ hiso₁ hM₁'
  haveI := (U.Di i).fin
  haveI : Module.Finite ℤ (U.Di i).La := Module.Finite.trans (𝓞 E) _
  obtain ⟨-, hinj, hd, hsp, Hm, -, hp, hE⟩ := hP'
  haveI : Module.IsTorsionFree ℤ (U.Di i).La :=
    Function.Injective.moduleIsTorsionFree P' hinj (fun r x => map_zsmul P' r x)
  haveI : Module.Free ℤ (U.Di i).La := Module.free_of_finite_type_torsion_free'
  let δ : (U.Di i).La ≃ₗ[ℤ] (U.Di i).La := (gam₁.symm.trans gam).toAddEquiv.toIntLinearEquiv
  have hδ : ∀ a, δ a = gam (gam₁.symm a) := fun a => rfl
  obtain ⟨n, hn, hδn⟩ := finite_order P' hinj hd hsp Hm hp δ
    (h₀.mulVecLin ∘ₗ h₁.symm.toLinearMap)
    (fun a => by
      have := hh₁ (gam₁.symm a)
      rw [gam₁.apply_symm_apply] at this
      rw [hδ, hh, this]
      simp)
    (fun a b => by
      rw [hE, hE, hδ, hδ, hiso, ← hiso₁, gam₁.apply_symm_apply, gam₁.apply_symm_apply])
  have hδ1 := hMink _ δ n l.M hn hδn l.three_le (fun y => by
    obtain ⟨e, he⟩ := f₀ (gam₁.symm y)
    obtain ⟨e', he'⟩ := f₁ (gam₁.symm y)
    rw [gam₁.apply_symm_apply] at he'
    refine ⟨e - e', ?_⟩
    rw [hδ, he, smul_sub]
    conv_rhs => rw [he']
    abel)
  have hg : ∀ a, gam a = gam₁ a := fun a => by
    have := hδ (gam₁ a)
    rw [hδ1, gam₁.symm_apply_apply] at this
    exact this.symm
  have hlin : h₀.mulVecLin.restrictScalars ℝ = h₁.toLinearMap.restrictScalars ℝ := by
    refine LinearMap.ext_on hP.2.2.2.1 ?_
    rintro _ ⟨a, rfl⟩
    change h₀ *ᵥ P a = h₁ (P a)
    rw [← hh, ← hh₁, hg]
  intro z
  have : h₀ *ᵥ z = h₁ z := LinearMap.congr_fun hlin z
  rw [this, hex]

end GlobalTheory.FamRigid
