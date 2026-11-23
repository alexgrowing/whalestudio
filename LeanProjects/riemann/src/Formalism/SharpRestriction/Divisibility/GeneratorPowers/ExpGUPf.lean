import Formalism.SharpRestriction.Divisibility.GeneratorPowers.UnitIdSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdAd

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU

open NumberField MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB.Canon Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdAd
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FB)

section Generic

theorem map_id_apply {S σ : Type} [CommRing S] (f : MvPowerSeries σ S) : MvPowerSeries.map (algebraMap S S) f = f := by
  ext n
  simp [MvPowerSeries.coeff_map]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {S : Type} [CommRing S] [Algebra ℚ S] {d n : ℕ} [StarRing (𝓞 E)] (B : FB S d (𝓞 E)) {h : PS S 2 d}
  (hg : B.IsCanonGauge S h)

theorem sb_expS {m : ℕ} (b : Fin m → Q S d n) {f : PS S m d} (hf : constantCoeff f = 0) :
    sb b (FB.expS S f) = FB.expS S (sb b f) := by
  rw [sb_apply, sb_apply]; exact TB.WickVanishing.gt_ev_expS _ (fun j => (b j).2) _ hf

include hg

theorem const_coeff_pair_form_zero (u v : Q S d n) : constantCoeff (E2 h u v) = 0 := by
  have := TB.LogPf.cc_ev (czQ ![(0 : Q S d 1), gen 0]) h
  rw [← sb_apply, show sb ![(0 : Q S d 1), gen 0] h = 0 from (formalSeriesValueAtTwoPoints_eq_ev h 0 (gen 0)).trans hg.ax0, map_zero] at this
  exact (congrArg constantCoeff (sb_apply _ _)).trans (TB.LogPf.constantCoeff_ev (czQ _) this.symm)

theorem cocycle_first_face_exp (u v w : Q S d n) : E3 B.ph1 u v w = FB.expS S (E2 h u w + E2 h v w - E2 h (op (FQ B.G) u v) w) := by
  have e : B.ph1 = FB.expS S (E2 h (gen 0) (gen 2) + E2 h (gen 1) (gen 2) - E2 h (op (FQ B.G) (gen 0) (gen 1)) (gen 2)) := by
    simp only [formalSeriesValueAtTwoPoints_eq_ev, op_val]; exact (map_id_apply _).symm.trans (hg.ph1.trans (by rw [show B.FK S = B.G.F from funext fun _ => map_id_apply _]; rfl))
  rw [e, E3, sb_expS _ (by simp [const_coeff_pair_form_zero B hg])]
  simp only [map_sub, map_add, formalPointSubstitutionSeries_valueAtTwoPoints, sq_op, sq_gen]; rfl

theorem cocycle_second_face_exp (u v w : Q S d n) : E3 B.ph2 u v w = FB.expS S (E2 h u v + E2 h u w - E2 h u (op (FQ B.G) v w)) := by
  have e : B.ph2 = FB.expS S (E2 h (gen 0) (gen 1) + E2 h (gen 0) (gen 2) - E2 h (gen 0) (op (FQ B.G) (gen 1) (gen 2))) := by
    simp only [formalSeriesValueAtTwoPoints_eq_ev, op_val]; exact (map_id_apply _).symm.trans (hg.ph2.trans (by rw [show B.FK S = B.G.F from funext fun _ => map_id_apply _]; rfl))
  rw [e, E3, sb_expS _ (by simp [const_coeff_pair_form_zero B hg])]
  simp only [map_sub, map_add, formalPointSubstitutionSeries_valueAtTwoPoints, sq_op, sq_gen]; rfl

omit hg [Algebra ℚ S] in
theorem actK_eq (a : 𝓞 E) : B.actK S a = B.A.act a := by
  first
  | rfl
  | (simp [FB.actK]; done)
  | (unfold FB.actK; rfl)

theorem g_ad (a : 𝓞 E) (u v : Q S d n) :
    E2 (B.ad a) u v = FB.expS S (E2 h (ac (AQ B.A a) u) v - E2 h u (ac (AQ B.A (star a)) v)) := by
  have e : B.ad a = FB.expS S (E2 h (ac (AQ B.A a) (gen 0)) (gen 1) - E2 h (gen 0) (ac (AQ B.A (star a)) (gen 1))) := by
    simp only [formalSeriesValueAtTwoPoints_eq_ev, ac_val]; exact (map_id_apply _).symm.trans ((hg.ad a).trans (by rw [actK_eq, actK_eq]; rfl))
  rw [e, E2, sb_expS _ (by simp [const_coeff_pair_form_zero B hg])]
  simp only [map_sub, formalPointSubstitutionSeries_valueAtTwoPoints, sq_ac, sq_gen]; rfl

omit hg in
theorem g_hL (w : 𝓞 E) (u : Q S d n) : sb ![u] (B.hL S h w) = E2 h u (ac (AQ B.A w) u) := by
  have e : B.hL S h w = E2 h (gen 0) (ac (AQ B.A w) (gen 0)) := by rw [formalSeriesValueAtTwoPoints_eq_ev, ac_val, FB.hL, actK_eq]; rfl
  rw [e, formalPointSubstitutionSeries_valueAtTwoPoints, sq_ac, sq_gen]; rfl

theorem generic (w a : 𝓞 E) :
    FB.expS S (-sb ![AQ B.A (1 + a * star a)] (B.hL S h w)) * E2 (B.ad (star a)) (AQ B.A a) (AQ B.A w) =
      E3 B.ph1 (AQ B.A 1) (AQ B.A (a * star a)) (AQ B.A ((1 + a * star a) * w)) *
        E3 B.ph2 (AQ B.A 1) (AQ B.A w) (AQ B.A (a * star a * w)) *
        E3 B.ph2 (AQ B.A (a * star a)) (AQ B.A w) (AQ B.A (a * star a * w)) * E2 (B.ad a) (AQ B.A 1) (AQ B.A (a * w)) *
        FB.expS S (-sb ![AQ B.A a] (B.hL S h w)) ^ 2 * FB.expS S (-sb ![AQ B.A 1] (B.hL S h w)) *
        FB.expS S (-sb ![AQ B.A (a * star a)] (B.hL S h w)) := by
  have g : ∀ c, ac (AQ B.A c) (gen 0 : Q S d 1) = AQ B.A c := fun c => Subtype.ext (funext fun i =>
    (congrArg (sb · (B.A.act c i)) (funext fun j => by fin_cases j; rfl)).trans (sb_gen _))
  have m : ∀ c c', ac (AQ B.A c) (AQ B.A c') = AQ B.A (c * c') := fun c c' => by rw [← g c', ← ac_mul, g]
  have p : ∀ c c', op (FQ B.G) (AQ B.A c) (AQ B.A c') = AQ B.A (c + c') := fun c c' => by rw [← g c, ← g c', ← ac_add, g]
  have cc := fun u v : Q S d 1 => const_coeff_pair_form_zero B hg u v
  simp only [cocycle_first_face_exp B hg, cocycle_second_face_exp B hg, g_ad B hg, g_hL, m, p, star_star, pow_two]
  repeat rw [← TB.WickVanishing.gt_expS_add _ _ (by simp [cc]) (by simp [cc])]
  congr 1
  ring_nf

end Generic

theorem unitId : UnitIdSt := by
  intro E _ _ _ H Dw l Xo c _ hs S _ _ _ y C φ hφ hact a
  have hsub : HasSubst fun p : Fin 1 × Fin C.d => φ p.2 := hasSubst_of_constantCoeff_zero fun p => hφ.const p.2
  let σ : PS S 1 C.d →ₐ[S] _ := substAlgHom (R := S) hsub
  have hσ : ∀ f, σ f = subst (fun p : Fin 1 × Fin C.d => φ p.2) f := fun f => congrFun (coe_substAlgHom hsub) f
  have pa : ∀ b, φa c φ b = fun j => σ (C.B.A.act b j) := fun b => funext fun j => ((hσ _).trans (hact b j)).symm
  have p1 : φ = fun j => σ (C.B.A.act 1 j) := funext fun j => by
    rw [C.B.A.one_act, hσ]; exact (subst_X hsub ((0 : Fin 1), j)).symm
  have at' : ∀ {m} (b : Fin m → Q S C.d 1) (f : PS S m C.d), σ (sb b f) = subst (fun p : Fin m × Fin C.d => σ ((b p.1).1 p.2)) f :=
    fun b f => by
      rw [hσ, sb_apply, ev, subst_comp_subst_apply (czQ b).hasSubst hsub]; simp only [hσ]
  have ex : ∀ b, σ (FB.expS S (-sb ![AQ C.B.A b] (C.B.hL S C.h H.w0))) =
      FB.expS S (-(compL (fun j => σ (C.B.A.act b j)) (C.B.hL S C.h H.w0))) := fun b => by
    have c0 : constantCoeff (-sb ![AQ C.B.A b] (C.B.hL S C.h H.w0)) = 0 := by rw [g_hL, map_neg, const_coeff_pair_form_zero C.B C.gauge, neg_zero]
    rw [hσ, FB.expS, TB.WickVanishing.subst_exp _ (fun p => hφ.const p.2) c0, ← hσ, map_neg, at']
    exact congrArg (fun q => FB.expS S (-subst q (C.B.hL S C.h H.w0))) (funext fun ⟨i, j⟩ => by fin_cases i; rfl)
  have a2 : ∀ b b' f, σ (E2 f (AQ C.B.A b) (AQ C.B.A b')) =
      atP ![fun j => σ (C.B.A.act b j), fun j => σ (C.B.A.act b' j)] f := fun b b' f =>
    (at' _ f).trans (congrArg (subst · f) (funext fun ⟨i, j⟩ => by fin_cases i <;> rfl))
  have a3 : ∀ b b' b'' f, σ (E3 f (AQ C.B.A b) (AQ C.B.A b') (AQ C.B.A b'')) =
      atP ![fun j => σ (C.B.A.act b j), fun j => σ (C.B.A.act b' j), fun j => σ (C.B.A.act b'' j)] f := fun b b' b'' f =>
    (at' _ f).trans (congrArg (subst · f) (funext fun ⟨i, j⟩ => by fin_cases i <;> rfl))
  have := congrArg σ (generic C.B C.gauge H.w0 a)
  simp only [map_mul, map_pow, ex, a2, a3, ← pa, hs] at this
  rwa [pa 1, ← p1] at this

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU
