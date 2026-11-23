import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjugationActsOnCmTorsionByMultiplicationStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CyclotomicCharacterEqCmMultiplierNormStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsConjSplitPointLatticeLinearMapStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.ConjIsometry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply Subtype.ext
  show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem conj_of_sq {ρ : ℂ} (hρ : ρ ^ 2 = -(H.d : ℂ)) : starRingEnd ℂ ρ = -ρ := by
  have h1 : (starRingEnd ℂ ρ) ^ 2 = ρ ^ 2 := by rw [← map_pow, hρ]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h
    rw [hx] at hρ
    have h5 : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast hρ
    have h6 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [sq_nonneg x]
  · exact h

theorem bar_rt : H.bar H.rt = -H.rt := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h4 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun a : 𝓞 E => φ (a : E)) H.rt_sq
    simpa using this
  apply Subtype.ext
  show ((H.bar H.rt : 𝓞 E) : E) = ((-H.rt : 𝓞 E) : E)
  apply φ.injective
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, conj_of_sq h4]
  simp

theorem cmHost_bar_halfIntegerGenerator : H.bar H.w0 = 1 - H.w0 := by
  have h := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, bar_rt, map_ofNat] at h
  apply mul_left_cancel₀ (two_ne_zero (α := 𝓞 E))
  linear_combination h + H.two_weight_eq_one_add_root

theorem bar_mul_wE (s : ℤ × ℤ) :
    H.bar (wE H s) * wE H s = ((s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) : ℤ) : 𝓞 E) := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (H.d : ℤ) + 1 = 4 * m := ⟨((H.d : ℤ) + 1) / 4, by have := H.d_mod; omega⟩
  have e : ((H.d : ℤ) + 1) / 4 = m := by omega
  have hm' : (H.d : 𝓞 E) + 1 = 4 * m := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hm
  have hw : H.w0 * (1 - H.w0) = (m : 𝓞 E) := by
    have h4 : (4 : 𝓞 E) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h4
    linear_combination (-(2 * H.w0 + H.rt - 1)) * H.two_weight_eq_one_add_root - H.rt_sq + hm'
  rw [e, wE, map_add, map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator]
  push_cast
  linear_combination (s.2 : 𝓞 E) ^ 2 * hw

theorem form_smul_smul (D : Datum H) (c : 𝓞 E) (N : ℤ) (h : H.bar c * c = N) (x y : D.La) :
    D.EF (c • x) (c • y) = N * D.EF x y := by
  rw [D.adj, smul_smul, h, Int.cast_smul_eq_zsmul, map_zsmul, smul_eq_mul]

theorem form_skew (D : Datum H) (x y : D.La) : D.EF x y = -D.EF y x := by
  have h := D.alt (x + y)
  simp only [map_add, LinearMap.add_apply, D.alt] at h
  linarith

variable {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem form_lat_eq_zero {D : Datum H} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) {a b : D.La}
    (ha : a ∈ lat hP H.rt0) (hb : b ∈ lat hP (-H.rt0)) : D.EF a b = 0 := by
  obtain ⟨Hm, -, -, hE⟩ := hP.2.2.2.2
  have h1 := hE (H.rt • a) (H.rt • b)
  rw [form_smul_smul D H.rt H.d (by rw [bar_rt]; push_cast; linear_combination -H.rt_sq),
    period_rt_smul hP ha, period_rt_smul hP hb] at h1
  have h2 : hermForm Hm (H.rt0 • P a) ((-H.rt0) • P b) = -(H.d : ℂ) * hermForm Hm (P a) (P b) := by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [star_neg, ← starRingEnd_apply, conj_of_sq H.sqrt_neg_disc_sq, ← H.sqrt_neg_disc_sq]
    ring
  rw [h2] at h1
  simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
    hE] at h1
  push_cast at h1
  have h6 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have : (D.EF a b : ℝ) = 0 := by nlinarith
  exact_mod_cast this

theorem surjective_of_isometry {D D' : Datum H} (hr : D.p + D.q = D'.p + D'.q) (Φ : D.La →ₗ[𝓞 E] D'.La)
    (hi : Function.Injective Φ) (hΦ : ∀ a b, D'.EF (Φ a) (Φ b) = D.EF a b) : Function.Surjective Φ := by
  have := D.fin
  have := D'.fin
  have := D'.proj
  have h0 : Module.finrank (𝓞 E) (D'.La ⧸ LinearMap.range Φ) = 0 := by
    have h1 := (LinearMap.range Φ).finrank_quotient_add_finrank
    rw [LinearMap.finrank_range_of_inj hi, D.rank, D'.rank] at h1
    omega
  intro y
  obtain ⟨x, hx⟩ := D.unimod.2 ((D'.EF y).comp (Φ.restrictScalars ℤ))
  have hx' : ∀ z, D'.EF (y - Φ x) (Φ z) = 0 := fun z => by
    rw [map_sub, LinearMap.sub_apply, hΦ, hx]; simp
  obtain ⟨c, hc, hcw⟩ := Module.finrank_eq_zero_iff.1 h0 (Submodule.Quotient.mk (y - Φ x))
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hcw
  obtain ⟨v, hv⟩ := hcw
  have hv0 : v = 0 := D.unimod.1 (by
    ext z
    rw [← hΦ, hv, D'.adj, ← map_smul, hx']; simp)
  rw [hv0, map_zero] at hv
  exact ⟨x, (sub_eq_zero.1 ((smul_eq_zero.1 hv.symm).resolve_left hc)).symm⟩

theorem exp_eq_zeta (n : ℕ) (m : ℤ) :
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / n) = zeta n ^ (-m) := by
  rw [zeta, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ}

theorem conj_pairing (F : FamilyUnif Xo σ ty) (τ : ℂ ≃+* ℂ) {i i' : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)}
    {P' : (F.Di i').La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di i') ty P')
    (hu : spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P') {n : ℕ} (hn : 0 < n) {x y : (F.Di i).La} {x' y' : (F.Di i').La}
    (hx : spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P x)).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' x')).left)
    (hy : spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P y)).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' y')).left) :
    τ (zeta n) ^ (-(F.Di i).EF x y) = zeta n ^ (-(F.Di i').EF x' y') := by
  let c : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * ((F.Di i).EF x y : ℂ) / n))
  let c' : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * ((F.Di i').EF x' y' : ℂ) / n))
  have W := F.ex_weil i P hP n x y c hn rfl
  have W' := F.ex_weil i' P' hP' n x' y' c' hn rfl
  let h : Over.mk (F.u i' P') ⟶ Over.mk (F.u i P) := Over.homMk (spMap (τ : ℂ →+* ℂ)) hu
  have W₁ := CommPairing.weilIs_pull globalFns_holds
    ⟨Xo.univ.t.semi.comm, Xo.univ.t.semi.smooth, Xo.univ.proper, Xo.univ.t.semi.geomConnected⟩ Xo.univ.t.PP.isLB h W
  have e' : Units.map h.left.appTop.hom.toMonoidHom (unitOn c) =
      unitOn (Units.map (τ : ℂ →+* ℂ).toMonoidHom c) :=
    Units.ext (congrArg (fun q => q.hom c.val)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (τ : ℂ →+* ℂ)))).symm
  have ex : h ≫ F.ex i P ((n : ℂ)⁻¹ • P x) = F.ex i' P' ((n : ℂ)⁻¹ • P' x') := Over.OverMorphism.ext hx
  have ey : h ≫ F.ex i P ((n : ℂ)⁻¹ • P y) = F.ex i' P' ((n : ℂ)⁻¹ • P' y') := Over.OverMorphism.ext hy
  rw [e', ex, ey] at W₁
  have k := congrArg Units.val (weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ _ _ _ _ _ _ W₁ W')
  rw [← map_zpow₀, ← exp_eq_zeta, ← exp_eq_zeta]
  exact k

end GlobalTheory.CompRat.ConjIsometry

namespace GlobalTheory.CompRat

open ConjIsometry in

theorem exists_isometry_of_conj_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P (a + b))).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ (wE H s • a + H.bar (wE H s) • b)))).left := by
  intro E _ _ _ H D l Xo σ g ty F h1 hσ hty hA τ hτ C io hio i P hP i' P' hP' hs hu
  obtain ⟨Φ, hinj, hp, hm, hact⟩ :=
    GlobalTheory.T.exists_conj_split_point_lattice_linear_map E H D l Xo σ g ty F h1 hσ hty hA τ hτ C io hio i P hP i' P' hP' hs hu
  have hiso : ∀ x y, (F.Di i').EF (Φ x) (Φ y) = (F.Di i).EF x y := by
    intro x y
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := x)))
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := y)))
    have key : ∀ n : ℕ, 0 < n →
        (n : ℤ) ∣ (F.Di i').EF (Φ (a + b)) (Φ (a' + b')) - (F.Di i).EF (a + b) (a' + b') := by
      intro n hn
      obtain ⟨⟨s, hs⟩, -⟩ := GlobalTheory.T.conjugation_acts_on_cm_torsion_by_multiplication E H C τ hτ io hio n hn
      have k := conj_pairing F τ hP hP' hu hn (hact n s hn hs a ha b hb) (hact n s hn hs a' ha' b' hb')
      have hN := GlobalTheory.T.cyclotomicCharacter_eq_cmMultiplier_norm E H C τ hτ io n s hn hs
      have hb1 := bar_mul_wE (H := H) s
      generalize s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) = N at hN hb1
      have hb2 : H.bar (H.bar (wE H s)) * H.bar (wE H s) = N := by rw [bar_bar, mul_comm, hb1]
      have o : ∀ u ∈ lat hP H.rt0, ∀ v ∈ lat hP (-H.rt0),
          (F.Di i').EF (Φ u) (Φ v) = 0 ∧ (F.Di i').EF (Φ v) (Φ u) = 0 := fun u hu v hv => by
        have := form_lat_eq_zero hP' ((hp u).2 hu) ((hm v).2 hv)
        exact ⟨this, by rw [form_skew, this, neg_zero]⟩
      have e : (F.Di i').EF (Φ (wE H s • a + H.bar (wE H s) • b)) (Φ (wE H s • a' + H.bar (wE H s) • b')) =
          N * (F.Di i').EF (Φ (a + b)) (Φ (a' + b')) := by
        simp only [map_add, LinearMap.add_apply]
        rw [(o _ (Submodule.smul_mem _ _ ha) _ (Submodule.smul_mem _ _ hb')).1,
          (o _ (Submodule.smul_mem _ _ ha') _ (Submodule.smul_mem _ _ hb)).2, (o _ ha _ hb').1, (o _ ha' _ hb).2]
        simp only [map_smul Φ]
        rw [form_smul_smul _ _ _ hb1, form_smul_smul _ _ _ hb2]
        ring
      rw [e, ← mul_neg, zpow_mul, ← hN] at k
      have prim : IsPrimitiveRoot (τ (zeta n)) n :=
        (Complex.isPrimitiveRoot_exp n hn.ne').map_of_injective τ.injective
      have ne : τ (zeta n) ≠ 0 := prim.ne_zero hn.ne'
      rw [← prim.zpow_eq_one_iff_dvd, sub_eq_add_neg, zpow_add₀ ne, k, ← zpow_add₀ ne, add_neg_cancel, zpow_zero]
    have := key (((F.Di i').EF (Φ (a + b)) (Φ (a' + b')) - (F.Di i).EF (a + b) (a' + b')).natAbs + 1) (by omega)
    exact sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _))
  have hsurj := surjective_of_isometry
    (by rw [(F.sig i).1, (F.sig i).2, (F.sig i').1, (F.sig i').2]) Φ hinj hiso
  exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, hiso, hp, hm, hact⟩

end GlobalTheory.CompRat
