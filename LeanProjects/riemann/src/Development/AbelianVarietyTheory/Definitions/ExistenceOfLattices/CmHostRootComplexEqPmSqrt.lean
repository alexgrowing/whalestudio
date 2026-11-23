import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.EqZeroOfOppositeSign
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCmEllipticCurveWithPeriod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumSumAndAllSignatures
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureType
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRatModel

open CompRat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_curve_model (H : Host E) : ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M)
    (P : Out.PolAV (Sp (𝓞 M))) (C : Curve H) (φ : C.P.A.left ⟶ P.A.left),
    IsGrpPullback C.P.A P.A (spMap ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))) φ := by
  have hm := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg (d := H.d) (by omega)
  obtain ⟨M, hM, w, P, v, hw, hg, -, -, hΛ, -⟩ :=
    cmCurve_closed H.d (by omega) H.d_prime.squarefree (by omega) K h2 hr
  obtain ⟨Q, φ, hq, hφ, hL⟩ :=
    exists_baseChange polBaseChange_holds (spMap ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))) P
  obtain ⟨u, hu⟩ := exists_isThetaUnif thetaUnifAV_all Q
  obtain ⟨c, hc, hl⟩ := hΛ Q φ ⟨hq, hφ, LBIso.symm hL⟩ u
  exact ⟨M, hM, P, ⟨Q, hq.trans hg, u, hu, c, hc, fun z => by rw [hl z, hw]⟩, φ, hφ⟩

instance nonempty_curve (H : Host E) : Nonempty (Curve H) := by
  obtain ⟨_, _, _, C, -⟩ := exists_curve_model H
  exact ⟨C⟩

theorem cmHost_rootComplex_eq_pm_sqrt (H : Host E) : H.rt0 = Complex.I * Real.sqrt H.d ∨ H.rt0 = -(Complex.I * Real.sqrt H.d) := by
  have h : ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 = H.d := by exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg H.d)
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [H.sqrt_neg_disc_sq, mul_pow, h, Complex.I_sq]; ring

theorem cmHost_rootZero_im_ne_zero (H : Host E) : H.rt0.im ≠ 0 := by
  have hd : (0 : ℝ) < Real.sqrt H.d := Real.sqrt_pos.2 (Nat.cast_pos.2 H.d_prime.pos)
  rcases cmHost_rootComplex_eq_pm_sqrt H with h | h <;> rw [h] <;> simp [hd.ne']

theorem map_wE (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0) (s : ℤ × ℤ) : τ (wE H s : E) = wC H s := by
  have h := congrArg (fun a : 𝓞 E => τ (a : E)) H.two_weight_eq_one_add_root
  simp only [map_mul, map_add, map_one, map_ofNat] at h
  have h' : τ (H.w0 : E) = (1 + H.rt0) / 2 := by
    rw [← hτ]; linear_combination h / 2
  simp [wE, wC, h']

theorem wC_injective (H : Host E) : Function.Injective (wC H) := by
  rintro ⟨m, n⟩ ⟨m', n'⟩ h
  have e := congrArg Complex.im h
  simp [wC, cmHost_rootZero_im_ne_zero H] at e
  subst e
  have : (m : ℂ) = m' := add_right_cancel h
  rw [show m = m' by exact_mod_cast this]

theorem pt_eq_iff (C : Curve H) (z z' : ℂ) : C.pt z = C.pt z' ↔ ∃ s, z - z' = wC H s := by
  have e : C.u.ex (fun _ => C.c * z) = C.u.ex (fun _ => C.c * (z - z')) * C.u.ex (fun _ => C.c * z') := by
    rw [← C.u.ex_add]; congr 1; funext i; simp; ring
  have i0 : Fin C.P.g := ⟨0, by rw [C.g_eq]; exact one_pos⟩
  have key : C.pt z = C.pt z' ↔ ∃ m n : ℤ, z - z' = m + n * ((1 + Complex.I * Real.sqrt H.d) / 2) := by
    constructor
    · intro h
      have h' : C.u.ex (fun _ => C.c * z) = C.u.ex (fun _ => C.c * z') := Over.OverMorphism.ext h
      rw [h'] at e
      obtain ⟨m, n, hmn⟩ := (C.lat _).1 ((C.u.ker _).1 (mul_eq_right.1 e.symm))
      exact ⟨m, n, mul_left_cancel₀ C.c_ne (congrFun hmn i0)⟩
    · rintro ⟨m, n, hmn⟩
      have : C.u.ex (fun _ => C.c * (z - z')) = 1 := (C.u.ker _).2 ((C.lat _).2 ⟨m, n, by rw [hmn]⟩)
      unfold Curve.pt
      rw [e, this, _root_.one_mul]
  rw [key]
  rcases cmHost_rootComplex_eq_pm_sqrt H with h | h
  · exact ⟨fun ⟨m, n, e⟩ => ⟨(m, n), by rw [e, wC, h]⟩, fun ⟨s, e⟩ => ⟨s.1, s.2, by rw [e, wC, h]⟩⟩
  · exact ⟨fun ⟨m, n, e⟩ => ⟨(m + n, -n), by rw [e, wC, h]; push_cast; ring⟩,
      fun ⟨s, e⟩ => ⟨s.1 + s.2, -s.2, by rw [e, wC, h]; push_cast; ring⟩⟩

theorem exists_wC_mul (H : Host E) (s a : ℤ × ℤ) : ∃ b, wC H s * wC H a = wC H b := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (H.d : ℤ) + 1 = 4 * k := ⟨((H.d : ℤ) + 1) / 4, by have := H.d_mod; omega⟩
  have hk' : (H.d : ℂ) + 1 = 4 * k := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) hk
  refine ⟨(s.1 * a.1 - k * s.2 * a.2, s.1 * a.2 + s.2 * a.1 + s.2 * a.2), ?_⟩
  simp only [wC]
  push_cast
  linear_combination (s.2 * a.2 / 4 : ℂ) * H.sqrt_neg_disc_sq - (s.2 * a.2 / 4 : ℂ) * hk'

theorem spMap_refl : spMap ((RingEquiv.refl ℂ : ℂ ≃+* ℂ) : ℂ →+* ℂ) = 𝟙 _ := Spec.map_id (CommRingCat.of ℂ)

theorem actsBy_refl (C : Curve H) (n : ℕ) : C.ActsBy (RingEquiv.refl ℂ) (𝟙 _) n (1, 0) := by
  refine ⟨?_, fun a => ?_⟩
  · rw [spMap_refl]; exact @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl C.P.A) (inferInstanceAs (IsMonHom (𝟙 C.P.A)))
  · rw [spMap_refl, Category.comp_id, Category.id_comp]; simp [wC]

theorem fixesCurve_refl (H : Host E) (n : ℕ) : FixesCurve H (RingEquiv.refl ℂ) n :=
  ⟨Classical.arbitrary _, _, actsBy_refl _ n⟩

theorem curveOver_top (H : Host E) (n : ℕ) : CurveOver H ⊤ n := fun τ h => by
  rw [show τ = RingEquiv.refl ℂ from RingEquiv.ext fun x => h x trivial]
  exact fixesCurve_refl H n

theorem actsBy_unique {C : Curve H} {τ : ℂ ≃+* ℂ} {f : C.P.A.left ⟶ C.P.A.left} {n : ℕ} (hn : n ≠ 0) {s s' : ℤ × ℤ}
    (h : C.ActsBy τ f n s) (h' : C.ActsBy τ f n s') : (n : ℤ) ∣ s.1 - s'.1 ∧ (n : ℤ) ∣ s.2 - s'.2 := by
  have : IsIso (spMap (τ : ℂ →+* ℂ)) := inferInstanceAs (IsIso (Spec.map τ.toCommRingCatIso.hom))
  have : IsIso f := h.1.1.isIso_fst_of_isIso
  have e := (cancel_mono f).1 ((h.2 (1, 0)).trans (h'.2 (1, 0)).symm)
  obtain ⟨t, ht⟩ := (pt_eq_iff C _ _).1 e
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have : wC H (s.1 - s'.1, s.2 - s'.2) = wC H (n * t.1, n * t.2) := by
    simp only [wC] at ht ⊢
    push_cast at ht ⊢
    field_simp at ht ⊢
    linear_combination ht / 2
  have e := wC_injective H this
  exact ⟨⟨t.1, congrArg Prod.fst e⟩, ⟨t.2, congrArg Prod.snd e⟩⟩

theorem not_actsBy_neg (C : Curve H) : ¬ C.ActsBy (RingEquiv.refl ℂ) (𝟙 _) 3 (-1, 0) := fun h => by
  have := (actsBy_unique (by norm_num) h (actsBy_refl C 3)).1
  norm_num at this

theorem actsBy_of_dvd {C : Curve H} {τ : ℂ ≃+* ℂ} {f : C.P.A.left ⟶ C.P.A.left} {m n : ℕ} (hn : n ≠ 0) (hmn : m ∣ n)
    {s : ℤ × ℤ} (h : C.ActsBy τ f n s) : C.ActsBy τ f m s := by
  obtain ⟨k, rfl⟩ := hmn
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (left_ne_zero_of_mul hn)
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (right_ne_zero_of_mul hn)
  refine ⟨h.1, fun a => ?_⟩
  have e : wC H (k * a.1, k * a.2) = k * wC H a := by simp only [wC]; push_cast; ring
  have := h.2 (k * a.1, k * a.2)
  rw [e] at this
  convert this using 3 <;> push_cast <;> field_simp

theorem pt_wC (C : Curve H) (a : ℤ × ℤ) : C.pt (wC H a) = η[C.P.A].left := by
  rw [(pt_eq_iff C _ 0).2 ⟨a, sub_zero _⟩]
  have : C.u.ex (fun _ => C.c * 0) = 1 := (C.u.ker _).2 (by
    rw [show (fun _ => C.c * 0 : Fin C.P.g → ℂ) = 0 from funext fun _ => mul_zero _]; exact zero_mem _)
  unfold Curve.pt
  rw [this, Hom.one_def]; simp

theorem actsBy_one {C : Curve H} {τ : ℂ ≃+* ℂ} {f : C.P.A.left ⟶ C.P.A.left}
    (h : IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) f) (s : ℤ × ℤ) : C.ActsBy τ f 1 s := by
  refine ⟨h, fun a => ?_⟩
  obtain ⟨b, hb⟩ := exists_wC_mul H s a
  rw [Nat.cast_one, div_one, div_one, hb, pt_wC, pt_wC]
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over (Sp ℂ)))))
  have e₁ : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ C.P.A) = η[C.P.A] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[C.P.A]).left = _
  simp

theorem fixesCurve_zero_iff (τ : ℂ ≃+* ℂ) : FixesCurve H τ 0 ↔ FixesCurve H τ 1 := by
  refine ⟨fun ⟨C, f, h⟩ => ⟨C, f, actsBy_one h.1 _⟩, fun ⟨C, f, h⟩ => ⟨C, f, h.1, fun a => ?_⟩⟩
  simpa [wC] using h.2 (0, 0)

theorem exists_curveOver_one (H : Host E) : ∃ F : IntermediateField ℚ ℂ, FiniteDimensional ℚ F ∧ CurveOver H F 1 := by
  obtain ⟨M, _, P, C, φ, h⟩ := exists_curve_model H
  refine ⟨M, inferInstance, fun τ hτ => ?_⟩
  have e : spMap (τ : ℂ →+* ℂ) ≫ spMap ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) =
      spMap ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact hτ _ (x : M).2
  have w : φ ≫ P.A.hom = (C.P.A.hom ≫ spMap (τ : ℂ →+* ℂ)) ≫ spMap ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) := by
    rw [Category.assoc, e, h.1.w]
  exact ⟨C, h.1.lift _ _ w, actsBy_one
    (h.cancel (h.congr e.symm (h.1.lift_fst _ _ w).symm) (h.1.lift_snd _ _ w)) _⟩

section Split

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)

theorem sign_lat {ρ : ℂ} (hρ : ρ.im ≠ 0) {a : D.La} (ha : a ∈ lat hP ρ) (h0 : a ≠ 0) :
    0 < ρ.im * D.EF (H.rt • a) a := by
  obtain ⟨Hm, -, hpos, hE⟩ := hP.2.2.2.2
  have hz : P a ≠ 0 := fun h => h0 (hP.2.1 (h.trans (map_zero P).symm))
  have h1 := hE (H.rt • a) a
  have h2 := hE a a
  rw [D.alt] at h2
  have h3 : hermForm Hm (P (H.rt • a)) (P a) = ρ * hermForm Hm (P a) (P a) := by
    rw [period_rt_smul hP ha, hermForm, hermForm, smul_dotProduct, smul_eq_mul]
  rw [h3, Complex.mul_im, h2] at h1
  rw [← h1]
  have := mul_pos (mul_self_pos.2 hρ) (hpos _ hz)
  simp only [Int.cast_zero, mul_zero, zero_add]
  linarith

theorem signs : (∀ a ∈ lat hP H.rt0, a ≠ 0 → 0 < H.rt0.im * D.EF (H.rt • a) a) ∧
    ∀ a ∈ lat hP (-H.rt0), a ≠ 0 → H.rt0.im * D.EF (H.rt • a) a < 0 := by
  refine ⟨fun a ha h0 => sign_lat hP (cmHost_rootZero_im_ne_zero H) ha h0, fun a ha h0 => ?_⟩
  have := sign_lat hP (by simpa using cmHost_rootZero_im_ne_zero H) ha h0
  rw [Complex.neg_im] at this
  linarith

end Split

theorem splitLat_of_q_zero (D : Datum H) (hq : D.q = 0) : SplitLat D ∧
    ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P),
      IsTypeFn H D.p D.q ty → IsSplit hP := by
  refine ⟨?_, fun g ty P hP hty => by rw [IsSplit, lat_eq_top hP (hq ▸ hty), top_sup_eq]⟩
  obtain ⟨g, ty, hty⟩ := PureTypeModel.exists_isTypeFn H D.p D.q
  obtain ⟨P, hP⟩ := PeriodNonempty.exists_isPeriod E H D g ty hty
  refine ⟨⊤, ⊥, top_sup_eq _, fun a _ b hb => ?_, by rw [finrank_top, D.rank, hq, add_zero], by rw [finrank_bot, hq],
    fun a _ h0 => (signs hP).1 a (lat_eq_top hP (hq ▸ hty) ▸ Submodule.mem_top) h0, fun a ha h0 => absurd ha h0⟩
  rw [(Submodule.mem_bot _).1 hb, map_zero]

theorem exists_splitLat : ∃ D : Datum CM.LatModel.host, D.p = 1 ∧ D.q = 0 ∧ SplitLat D := by
  obtain ⟨D, hp, hq⟩ := CM.LatModel.exists_datum
  exact ⟨D, hp, hq, (splitLat_of_q_zero D hq).1⟩

theorem neg_of_p_zero (D : Datum H) (hp : D.p = 0) (a : D.La) (h0 : a ≠ 0) : H.rt0.im * D.EF (H.rt • a) a < 0 := by
  obtain ⟨g, ty, hty⟩ := PureTypeModel.exists_isTypeFn H D.p D.q
  obtain ⟨P, hP⟩ := PeriodNonempty.exists_isPeriod E H D g ty hty
  refine (signs hP).2 a (fun j hj => ?_) h0
  have h2 : (ty j (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    have := congrArg (fun a : 𝓞 E => ty j (a : E)) H.rt_sq
    simp only [map_pow, map_neg, map_natCast] at this
    rw [H.sqrt_neg_disc_sq]; exact this
  have h := (hty (ty j)).1 ((sq_eq_sq_iff_eq_or_eq_neg.1 h2).resolve_right hj)
  have : Nonempty {i // ty i = ty j} := ⟨⟨j, rfl⟩⟩
  exact absurd (h.trans hp) Nat.card_pos.ne'

theorem splitLat_sum (D D' : Datum H) (hq : D.q = 0) (hp : D'.p = 0) :
    ∃ D'' : Datum H, D''.p = D.p ∧ D''.q = D'.q ∧ SplitLat D'' := by
  obtain ⟨D'', e, h1, h2, hE⟩ := exists_datum_sum_and_all_signatures.1 E H D D'
  obtain ⟨g, ty, hty⟩ := PureTypeModel.exists_isTypeFn H D.p D.q
  obtain ⟨P, hP⟩ := PeriodNonempty.exists_isPeriod E H D g ty hty
  have pos := fun a h0 => (signs hP).1 a (lat_eq_top hP (hq ▸ hty) ▸ Submodule.mem_top) h0
  let i₁ : D.La →ₗ[𝓞 E] D''.La := e.symm.toLinearMap ∘ₗ LinearMap.inl _ _ _
  let i₂ : D'.La →ₗ[𝓞 E] D''.La := e.symm.toLinearMap ∘ₗ LinearMap.inr _ _ _
  have j₁ : Function.Injective i₁ := e.symm.injective.comp LinearMap.inl_injective
  have j₂ : Function.Injective i₂ := e.symm.injective.comp LinearMap.inr_injective
  refine ⟨D'', by omega, by omega, LinearMap.range i₁, LinearMap.range i₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine top_le_iff.1 fun x _ => Submodule.mem_sup.2 ⟨_, ⟨(e x).1, rfl⟩, _, ⟨(e x).2, rfl⟩, e.injective ?_⟩
    simp [i₁, i₂]
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp [hE, i₁, i₂]
  · rw [LinearMap.finrank_range_of_inj j₁, D.rank]; omega
  · rw [LinearMap.finrank_range_of_inj j₂, D'.rank]; omega
  · rintro _ ⟨a, rfl⟩ h0
    simpa [hE, i₁] using pos a fun h => h0 (by rw [h, map_zero])
  · rintro _ ⟨a, rfl⟩ h0
    simpa [hE, i₂] using neg_of_p_zero D' hp a fun h => h0 (by rw [h, map_zero])

theorem exists_splitLat_indefinite : ∃ D : Datum CM.LatModel.host, D.p = 1 ∧ D.q = 1 ∧ SplitLat D := by
  obtain ⟨D, hp, hq⟩ := CM.LatModel.exists_datum
  obtain ⟨D'', a, b, c⟩ := splitLat_sum D (CM.LatModel.negDatum D) hq hq
  exact ⟨D'', a.trans hp, b.trans hp, c⟩

end GlobalTheory.CompRatModel
