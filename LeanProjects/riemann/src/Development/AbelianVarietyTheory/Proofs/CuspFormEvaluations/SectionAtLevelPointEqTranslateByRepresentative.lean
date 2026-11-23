import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FockLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppellHumbertFrameSemicharacter
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SectionReadingExistsUniqueIsTheta
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExpNsmulEqPowVt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HalfIntegralGeneratorTraceEqOne

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal.VtLevel

theorem tyAct_natCast_mul {E : Type} [Field E] [NumberField E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (n : ℕ) (a : 𝓞 E)
    (z : Fin g → ℂ) : tyAct ty ((n : 𝓞 E) * a) z = (n : ℂ) • tyAct ty a z := by
  funext k
  simp [tyAct, _root_.mul_assoc]

theorem tyAct_natCast {E : Type} [Field E] [NumberField E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (n : ℕ)
    (z : Fin g → ℂ) : tyAct ty (n : 𝓞 E) z = (n : ℂ) • z := by
  funext k
  simp [tyAct]

theorem hermForm_smul_left' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (c • z) w = c * hermForm Hm z w := by
  simp [hermForm]

theorem hermForm_two_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z ((2 : ℂ) • w) = 2 * hermForm Hm z w := by
  simp [hermForm, Matrix.mulVec_smul]

theorem hermForm_add_left' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm]

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem e_natCast_smul (n : ℕ) (z : Fin g → ℂ) : Φ.e ((n : ℂ) • z) = Φ.e z ^ n := by
  induction n with
  | zero => simpa using (Φ.e_ker 0).2 Φ.lat.zero_mem
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, Φ.e_add, ih, pow_succ]

theorem sub_mem_of_e_eq {z w : Fin g → ℂ} (h : Φ.e z = Φ.e w) : z - w ∈ Φ.lat := by
  rw [← Φ.e_ker]
  have h1 := Φ.e_add (z - w) w
  rw [sub_add_cancel, h] at h1
  exact (mul_eq_right.1 h1.symm)

end

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply Subtype.ext
  have h1 := H.bar_eq (H.bar a)
  rw [H.bar_eq a, IsCMField.complexConj_apply_apply] at h1
  exact h1

theorem bar_mem {r : 𝓞 E} (hr : r ∈ Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) :
    ∃ α ∈ l.Mb ^ 2, H.bar r = ((2 : ℕ) : 𝓞 E) * α := by
  have h1 := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hr
  have h2 : (H.bar : 𝓞 E →+* 𝓞 E).comp (H.bar : 𝓞 E →+* 𝓞 E) = RingHom.id _ :=
    RingHom.ext fun a => bar_bar a
  rw [Ideal.map_mul, Ideal.map_pow, Ideal.map_map, h2, Ideal.map_id, Ideal.map_span, Set.image_singleton,
    map_ofNat, Ideal.mem_span_singleton_mul] at h1
  obtain ⟨α, hα, h⟩ := h1
  exact ⟨α, hα, by rw [Nat.cast_ofNat, h]; rfl⟩

theorem smul_eq_of_mem {x2 : Dw.La}
    (hx : x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La))
    {α : 𝓞 E} (hα : α ∈ l.Mb ^ 2) : ∃ w : Dw.La, α • x2 = ((l.M ^ 2 : ℕ) : 𝓞 E) • w := by
  have h1 := Submodule.smul_mem_smul hα hx
  rw [← Submodule.mul_smul] at h1
  have h2 : l.Mb ^ 2 * (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) ≤
      Ideal.span {((l.M ^ 2 : ℕ) : 𝓞 E)} := by
    rw [mul_left_comm, ← mul_pow, l.prod, Ideal.span_singleton_pow, Nat.cast_pow]
    exact Ideal.mul_le_right
  have h3 := Submodule.smul_mono_left h2 h1
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨w, -, hw⟩ := h3
  exact ⟨w, hw.symm⟩

theorem eq_two_smul_of_mem {x2 : Dw.La}
    (hx : x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ w : Dw.La, x2 = w + w := by
  have h3 := Submodule.smul_mono_left (Ideal.mul_le_left) hx
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨w, -, hw⟩ := h3
  exact ⟨w, by rw [← hw, two_smul]⟩

variable {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

theorem killedBy_iff (I : Ideal (𝓞 E)) (z : Fin g → ℂ) :
    KilledBy Xo I (Φ.e z) ↔ ∀ α ∈ I, tyAct ty α z ∈ Φ.lat := by
  refine forall₂_congr fun α _ => ?_
  rw [← Φ.lin, Φ.e_ker]

theorem levPt_eq {x x2 : Dw.La} (h : x2 - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    levPt Xo y.x x2 = levPt Xo y.x x := by
  have h1 := Xo.univ.eta_add (x2 - x) x
  rw [sub_add_cancel, Xo.univ.eta_ker _ h, _root_.one_mul] at h1
  unfold levPt
  rw [h1]

theorem im_even (mk : Dw.La →+ (Fin g → ℂ)) (hmk : ∀ a, mk a ∈ Φ.lat)
    (hlin : ∀ (α : 𝓞 E) a, mk (α • a) = tyAct ty α (mk a)) {u : Fin g → ℂ}
    (hu : ∀ α ∈ l.Mb ^ 2, tyAct ty α u ∈ Φ.lat) {x2 : Dw.La}
    (hx : x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ k : ℤ, (hermForm Φ.Hm (mk x2) u).im = 2 * k := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr w _
    obtain ⟨α, hα, h⟩ := bar_mem hr
    obtain ⟨k, hk⟩ := ((anFr_semichar _ _ _ _ _ Φ.toAnFr).1 _ (hmk w) _ (hu α hα)).1
    refine ⟨k, ?_⟩
    rw [hlin, Φ.adj, h, tyAct_natCast_mul, Nat.cast_ofNat, hermForm_two_right, ← hk]
    simp
  · rintro a b ⟨k, hk⟩ ⟨k', hk'⟩
    refine ⟨k + k', ?_⟩
    rw [map_add, hermForm_add_left', Complex.add_im, hk, hk']
    push_cast
    ring

end

end GlobalTheory.AnVal.VtLevel

open GlobalTheory.AnVal.VtLevel in
theorem GlobalTheory.AnVal.rd_vt_levPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ mk : Dw.La →+ (Fin g → ℂ), (∀ a, mk a ∈ Φ.lat) → (∀ (α : 𝓞 E) a, mk (α • a) = tyAct ty α (mk a)) → (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo y.x a = Φ.e ((l.M : ℂ)⁻¹ • mk a)) → ∀ θ, Φ.toAnFr.Rd 1 y.s θ → ∀ x x2 : Dw.La, x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La) → x2 - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) → (KilledBy Xo (l.Mb ^ 2) (Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk x2)) ∧ Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk x2) ^ l.M = levPt Xo y.x x) ∧ ∀ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)), IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y.s (levPt Xo y.x x) F → Φ.toAnFr.Rd ((l.M : ℤ) ^ 2) F (fock Φ.Hm ((l.M : ℤ) ^ 2) (((l.M : ℂ) ^ 2)⁻¹ • mk x2) fun z => θ ((l.M : ℂ) • z)) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ mk hmk hlin hlev θ hθ x x2 hx2 hx
  have hM : (l.M : ℂ) ≠ 0 := by
    have := l.three_le
    exact Nat.cast_ne_zero.2 (by omega)
  have hk : ∀ α ∈ l.Mb ^ 2, tyAct ty α (((l.M : ℂ) ^ 2)⁻¹ • mk x2) ∈ Φ.lat := by
    intro α hα
    obtain ⟨w, hw⟩ := smul_eq_of_mem hx2 hα
    rw [map_smul, ← hlin, hw, hlin, tyAct_natCast, smul_smul, Nat.cast_pow, inv_mul_cancel₀ (pow_ne_zero 2 hM),
      one_smul]
    exact hmk w
  have hp : Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk x2) ^ l.M = levPt Xo y.x x := by
    have hm : x2 ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) :=
      Submodule.smul_mono_left (Ideal.mul_le_right.trans (Ideal.pow_le_self two_ne_zero)) hx2
    rw [← levPt_eq hx, hlev x2 hm, ← e_natCast_smul, smul_smul]
    congr 2
    field_simp
  refine ⟨⟨(killedBy_iff Φ _ _).2 hk, hp⟩, fun F hF => ?_⟩
  have hχ : ∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1 := fun a ha => (chi_eq_sign E H Dw l Xo c y g ty el Φ a ha).1
  have hMm : ((l.M ^ 2 : ℕ) : 𝓞 E) ∈ l.Mb ^ 2 := by
    rw [Nat.cast_pow]
    refine Ideal.pow_mem_pow ?_ 2
    refine (Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) ?_
    rw [l.prod]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨x', δ, hδ, h2, hok, hpow, hrd⟩ :=
    (rd_vt_and_uu _ _ _ _ _ Φ.toAnFr hχ l.M l.odd y.s θ hθ).1 _ _ F hF (by
      intro t' ht' _
      obtain ⟨z, rfl⟩ := Φ.e_onto t'
      have h1 := (killedBy_iff Φ _ _).1 ht' _ hMm
      rw [tyAct_natCast] at h1
      rw [← e_natCast_smul, Φ.e_ker]
      exact h1)
  set a : Fin g → ℂ := ((l.M : ℂ) ^ 2)⁻¹ • mk x2 with ha
  have hu : ∀ α ∈ l.Mb ^ 2, tyAct ty α (x' - a) ∈ Φ.lat := fun α hα => by
    rw [map_sub]
    exact Φ.lat.sub_mem ((killedBy_iff Φ _ _).1 hok α hα) (hk α hα)
  have hb : (l.M : ℂ) • (x' - a) ∈ Φ.lat := by
    rw [smul_sub]
    apply sub_mem_of_e_eq
    rw [e_natCast_smul, e_natCast_smul, hpow, hp]
  obtain ⟨w, hw⟩ := eq_two_smul_of_mem hx2
  obtain ⟨k, hk2⟩ := l.odd
  have hMa : ((l.M : ℂ) ^ 2) • a = mk w + mk w := by
    rw [ha, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hM), one_smul, hw, map_add]
  have hb2 : (l.M : ℂ) • (x' - a) = (2 : ℂ) • (δ - mk w - k • ((l.M : ℂ) • (x' - a))) := by
    have h3 : (l.M : ℂ) • ((l.M : ℂ) • (x' - a)) = (2 : ℂ) • δ - (mk w + mk w) := by
      rw [smul_smul, ← sq, smul_sub, h2, hMa]
    generalize (l.M : ℂ) • (x' - a) = b at h3 ⊢
    rw [hk2] at h3
    funext i
    have := congrFun h3 i
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at this ⊢
    rw [nsmul_eq_mul]
    push_cast at this
    linear_combination this
  have hχb : Φ.χ ((l.M : ℂ) • (x' - a)) = 1 := by
    rw [hb2]
    exact (anFr_semichar _ _ _ _ _ Φ.toAnFr).2.2 hχ _
      (Φ.lat.sub_mem (Φ.lat.sub_mem hδ (hmk w)) (Φ.lat.nsmul_mem hb k))
  obtain ⟨f1, f2, f3⟩ := fock_laws _ _ _ _ _ Φ.toAnFr
  have hth := (reading_existsUnique_isTh _ _ _ _ _ Φ.toAnFr 1 y.s).2.1 θ hθ
  obtain ⟨m, hm⟩ := im_even Φ mk hmk hlin hu hx2
  have hx' : x' = a + (x' - a) := by abel
  rw [hx', f1, f2 l.M (x' - a), f3 θ hth _ hb, hχb] at hrd
  have he : Complex.exp (((((l.M : ℤ) ^ 2 : ℤ) : ℂ)) * Real.pi * Complex.I *
      ((hermForm Φ.Hm a (x' - a)).im : ℂ)) = 1 := by
    have h4 : (hermForm Φ.Hm a (x' - a)).im = ((l.M : ℝ) ^ 2)⁻¹ * (2 * m) := by
      rw [← hm]
      nth_rewrite 1 [ha]
      rw [hermForm_smul_left', ← Complex.im_ofReal_mul]
      push_cast
      rfl
    rw [h4, ← Complex.exp_int_mul_two_pi_mul_I m]
    congr 1
    push_cast
    field_simp
  rw [he] at hrd
  simpa only [_root_.one_mul] using hrd
