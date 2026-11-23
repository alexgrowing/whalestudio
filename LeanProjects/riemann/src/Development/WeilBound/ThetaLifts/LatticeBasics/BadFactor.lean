import Development.WeilBound.ThetaLifts.LatticeBasics.CommuteTheta
import Development.WeilBound.ThetaLifts.LatticeBasics.BadStmt
import Development.WeilBound.ThetaLifts.LatticeBasics.SchrUnit
import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.AdelInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive

noncomputable section

namespace GlobalTheory.ThK.Dbl.Bad

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc (idem)
open PositivityTheory.ThKG.Loc.Cone

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

variable {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem orth (P : IsPair B M χX χW om r s r' s') {ν} (hν : @Measure.IsAddHaarMeasure _ _ _ (borel _) ν) {Φ} (h : Φ ∈ schA F _)
    (h0 : Φ ≠ 0) {g u} {c c' : ℂ} (hc : c ≠ c') (h1 : M.co.rho B.ψ u Φ = c • Φ) (h2 : M.co.rho B.ψ (mat g * u) Φ = c' • Φ) :
    coef om ν Φ g = 0 := by
  by_contra hn
  have i := P.weil.isUSplitting.impl (g, 1) u Φ h
  rw [h1, map_smul, show actAB (cA σ) (g, 1) u = mat g * u from (congrArg _ Matrix.transpose_one).trans (Matrix.mul_one _)] at i
  have a1 := schr_unit P.base.std ν hν (M.co.e (mat g * u)) (om (g, 1) Φ) Φ
  have a2 := schr_unit P.base.std ν hν (M.co.e (mat g * u)) Φ Φ
  have k : ∀ (A : Fn F n d) (t : ℂ), ∫ x, (t • A) x * star ((c' • Φ) x) ∂ν = t * star c' * ∫ x, A x * star (Φ x) ∂ν := fun A t => by
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun x => by simp only [Pi.smul_apply, smul_eq_mul, star_mul']; ring)
  rw [show schr B.ψ (M.co.e (mat g * u)) Φ = _ from h2] at a1 a2
  rw [show schr B.ψ (M.co.e (mat g * u)) (om (g, 1) Φ) = _ from i.symm, k] at a1
  rw [k] at a2
  have b1 := (mul_eq_right₀ hn).1 a1
  have b2 := (mul_eq_right₀ (sq_ne ν hν h h0)).1 a2
  exact hc (mul_right_cancel₀ (right_ne_zero_of_mul_eq_one b1) (b1.trans b2.symm))

theorem fix_of_parts (P : IsPair B M χX χW om r s r' s') {Φ} (h : Φ ∈ schA F _) {g : UA σ X.J}
    (h1 : om (partU real_mul_self g, 1) Φ = Φ) (h2 : ∀ v, om (partU (idem_mul_self v) g, 1) Φ = Φ) : om (g, 1) Φ = Φ := by
  classical
  have step : ∀ S : Finset (Pl F), om (partU (aS_mul_self S) g, 1) Φ = Φ := fun S => by
    induction S using Finset.induction_on with
    | empty => rwa [show partU (aS_mul_self ∅) g = partU real_mul_self g from
        mat_inj (by rw [mat_partU, mat_partU, aS, Finset.sum_empty, add_zero])]
    | insert v S hv ih =>
      have e : partU (aS_mul_self (insert v S)) g = partU (idem_mul_self v) g * partU (aS_mul_self S) g := by
        rw [← partU_add (idem_mul_self v) (aS_mul_self S) (idem_mul_aS hv) (aS_insert hv ▸ aS_mul_self (insert v S))]
        exact mat_inj (by rw [mat_partU, mat_partU, aS_insert hv])
      rw [e, ← mul_one (1 : UA σ W.J), ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, ih, h2]
  funext x
  have t := ((P.weil.2.2 _ (ev_adm x) _ h).continuousAt (x := (g, 1))).tendsto.comp
    ((tendsto_partU g).prodMk_nhds tendsto_const_nhds)
  exact tendsto_nhds_unique t (tendsto_const_nhds.congr fun S => (congrFun (step S) x).symm)

theorem prj_eq (v : Pl F) (g : UA σ X.J) : partU (idem_mul_self v) g = Euler.prj v g := mat_inj (add_comm _ _)

theorem cont_emb {e : UA σ X.J × UA σ X.J →* G2 σ X} (he : ∀ g g', IsEmb g g' (e (g, g'))) : Continuous fun g => e (g, 1) := by
  have c : Continuous fun g => mat2 (e (g, 1)) :=
    (Euler.cont_mat.matrix_fromBlocks continuous_const continuous_const continuous_const).congr fun g => (he g 1).symm
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨c, (c.comp continuous_inv).congr fun g => ?_⟩)
  change mat2 (e (g⁻¹, 1)) = mat2 (e (g, 1))⁻¹
  rw [← map_inv, Prod.inv_mk, inv_one]

theorem par_one : IsPar (1 : G2 σ X) 1 := (Matrix.one_mul _).trans (Matrix.mul_one _).symm

theorem hgt_mul {K : Subgroup (G2 σ X)} {a : G2 σ X → ℝ} (ha : IsHgt K a) (y) {k} (hk : k ∈ K) : a (y * k) = a y := by
  obtain ⟨p, t, hp, k', hk', rfl⟩ := ha.iwa y
  rw [mul_assoc, ha.val p t hp _ (mul_mem hk' hk), ha.val p t hp _ hk']

theorem hgt_one {K : Subgroup (G2 σ X)} {a : G2 σ X → ℝ} (ha : IsHgt K a) {k} (hk : k ∈ K) : a k = 1 := by
  simpa using ha.val 1 1 par_one k hk

theorem law {dd om₂ S l} (hB : B.IsGood σ) (h : IsDbl (σ := σ) (A := W) (Y := X) (κ := (Fin n × Fin d) ⊕ (Fin n × Fin d)) B.ψ dd χW om₂ S l)
    {Ψ} (hΨ : Ψ ∈ schA F _) : Law χW (d / 2) fun x => l (om₂ x Ψ) := fun p t x hp => by
  have := hB.cm.1
  beta_reduce
  rw [map_mul, Module.End.mul_apply, h.weil.2.2 l h.adm h.kill p t hp _ (h.weil.2.1.pres x Ψ hΨ), PositivityTheory.ThKF0.Chr.absE_eq,
    Complex.ofReal_cpow (NNReal.coe_nonneg _), Fintype.card_fin]
  push_cast
  rfl

theorem at_emb {e : UA σ X.J × UA σ X.J →* G2 σ X} (he : ∀ g g', IsEmb g g' (e (g, g'))) {v} {u : UA σ X.J} (hu : u ∈ locGrp σ X v) :
    At (evFin F v) (mat2 (e (u, 1)) - 1) := fun t ht => by
  have : t • (mat u - 1) = 0 := by rw [← Euler.mem_loc.1 hu, ← prj_eq]; exact partU_idem_mem v u t ht
  rw [he u 1, show mat (1 : UA σ X.J) = 1 from rfl, ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg,
    Matrix.fromBlocks_add, Matrix.fromBlocks_smul, ← sub_eq_add_neg, this]
  simp

theorem int_all {v} {u : UA σ X.J} (hu : u ∈ locGrp σ X v) (h : IntAt v u) (w) : IntAt w u := by
  rcases eq_or_ne w v with rfl | hw
  · exact h
  · rw [← mul_one u, Euler.int_mul_ne hw hu]; exact (Euler.intGrp σ X w).one_mem

theorem _root_.GlobalTheory.ThK.Dbl.badFactor_of (hD : DblX) (hS : StabEx) (hV : VacFix2) (hB : Bump) : BadFactor := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' P h0 _ hn _ T hT _ uW f₀ p0 n0 i0 K a e hK ha he ν hν
  classical
  choose! β β1 β2 β3 using hB F E σ B n d X W M χX χW om r s r' s' P hn
  let φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v => if v ∈ T then β v else M.vac v
  have φ1 : ∀ v ∈ T, φ v = β v := fun v h => if_pos h
  have φ2 : ∀ v ∉ T, φ v = M.vac v := fun v h => if_neg h
  have hSB : ∀ v, φ v ∈ SB _ := fun v => by
    by_cases h : v ∈ T
    exacts [φ1 v h ▸ β1 v (hT h), φ2 v h ▸ (P.good.vac v).1]
  have hne : ∀ v, φ v ≠ 0 := fun v => by
    by_cases h : v ∈ T
    exacts [φ1 v h ▸ β2 v (hT h), φ2 v h ▸ (P.good.vac v).2.1]
  have hv : ∀ᶠ v in cofinite, φ v = M.vac v := T.eventually_cofinite_notMem.mono φ2
  have hs := (hv.and P.good.std).mono fun v h => h.1.trans h.2
  refine ⟨pure f₀ φ, Submodule.subset_span ⟨f₀, p0, φ, hSB, hv, rfl⟩, ?_⟩
  have m := GlobalTheory.TensUniq.pure_mem_schA f₀ φ hSB hs
  have m0 := GlobalTheory.EvNonzero.pure_ne_zero f₀ n0 φ hne hs
  obtain ⟨dd, om₂, S, l, d1, d2, d3, d4⟩ := hD F E σ B n d X W M χX χW om r s r' s' P
  obtain ⟨c, c0, hc⟩ := d4 ν hν
  have c1 := Complex.ofReal_ne_zero.2 c0.ne'
  have fx : ∀ v ∉ T, ∀ k ∈ K, At (evFin F v) (mat2 k - 1) → om₂ k (boxFun (pure f₀ φ) (star (pure f₀ φ))) = _ := fun v h k hk h' =>
    fix_box hSB hs (φ2 v h ▸ hV F E σ B n d X W M r s r' s' P.base P.herm P.skew P.good χW P.hW dd om₂ d3 d1.weil K hK v
      (fun w hw => uW w (by show ¬ w.under (𝓞 F) ∈ (T : Set (Pl F)); rw [hw]; exact h)) k hk h')
  have e1 := fun v (h : v ∈ T) S (c : ℂ) (h' : Acts (evFin F v) S (β v) (c • β v)) => eig (f := f₀) hSB hs (φ1 v h ▸ h')
  have e2 := fun S => fix_real (f := f₀) (S := S) hSB hs
  generalize pure f₀ φ = Φ at *
  have bx : ∀ g, om₂ (e (g, 1)) (boxFun Φ (star Φ)) = boxFun (om (g, 1) Φ) (star Φ) := fun g => by
    simpa [detInv, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl] using ((d2 Φ m Φ m).2 1 g 1 _ (he g 1)).2
  have cf : ∀ g, l (om₂ (e (g, 1)) (boxFun Φ (star Φ))) = c * coef om ν Φ g := fun g => by
    rw [bx, hc _ (P.weil.isUSplitting.pres _ _ m) _ m]; rfl
  have N : coef om ν Φ 1 ≠ 0 := by
    rw [coef, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one]; exact sq_ne ν hν m m0
  have a0 : ∀ x, 0 < a x := fun x => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa x
    rw [ha.val p t hp k hk]; exact absE_pos _
  refine ⟨fun z v hvT => ?_, ?_⟩
  · set G := flat a (fun x => l (om₂ x (boxFun Φ (star Φ)))) (((d : ℂ) - n) / 2) z with hG
    have L : Law χW (z + n / 2) G := by
      have := (law P.base d1 (d2 Φ m Φ m).1).flat (s₀ := ((d : ℂ) - n) / 2) ha a0 z
      rwa [show z - ((d : ℂ) - n) / 2 + d / 2 = z + n / 2 by ring] at this
    have R : ∀ k ∈ K, At (evFin F v) (mat2 k - 1) → ∀ y, G (y * k) = G y := fun k hk h y => by
      simp only [hG, flat, hgt_mul ha y hk, map_mul, Module.End.mul_apply, fx v hvT k hk h]
    have Z : ∀ g, G (e (g, 1)) = c * zint om ν a e Φ z g := fun g => by rw [hG, flat, cf, zint]; ring
    have G1 : G 1 ≠ 0 := by
      rw [← map_one e, show (1 : UA σ X.J × UA σ X.J) = (1, 1) from rfl, Z, zint, hgt_one ha (show e (1, 1) ∈ K from map_one e ▸ K.one_mem)]
      simpa using ⟨c0.ne', N⟩
    refine ⟨fun x => G x / G 1, fun p t hp _ k hk h => ?_, fun u hu => ⟨fun hi => ?_, fun g hg => ?_⟩⟩ <;> beta_reduce
    · rw [L p t k hp, ← one_mul k, R k hk h, mul_div_cancel_right₀ _ G1]
    · rw [← one_mul (e (u, 1)), R _ (emb_mem P.base P.herm h0 hK he (int_all hu hi)) (at_emb he hu), div_self G1]
    · obtain ⟨p, t, k, hp, hk, h, e'⟩ := loc_iwa hK ha (at_emb he hu)
      refine mul_left_cancel₀ c1 ?_
      rw [mul_left_comm, ← Z, ← Z, show e (u * g, 1) = e (u, 1) * e (g, 1) by rw [← map_mul, Prod.mk_mul_mk, mul_one], e',
        mul_assoc, L p t _ hp, L p t _ hp, comm_off he hg h, R k hk h, ← one_mul k, R k hk h, mul_div_cancel_right₀ _ G1]
  have key : ∀ g, (∀ v ∉ T, IntAt v g) → coef om ν Φ g ≠ 0 → (∀ v, IntAt v g) ∧ coef om ν Φ g = coef om ν Φ 1 := fun g hg h => by
    have b : ∀ v ∈ T, IntAt v g ∧ om (partU (idem_mul_self v) g, 1) Φ = Φ := fun v hv => by
      rcases β3 v (hT hv) _ (partU_idem_mem v g) with ⟨b1, b2⟩ | ⟨u, c, c', b1, b2, b3, b4⟩
      · exact ⟨Euler.int_prj.1 (prj_eq v g ▸ b1), (e1 v hv _ 1 (by rwa [one_smul])).trans (one_smul _ _)⟩
      · refine absurd (orth P hν m m0 b2 (e1 v hv _ _ b3) (e1 v hv _ _ ?_)) h
        rwa [mat_partU, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, sub_smul, one_smul, idem_smul b1,
          sub_self, add_zero, ← Matrix.mul_smul, idem_smul b1] at b4
    have hi : ∀ v, IntAt v g := fun v => (em (v ∈ T)).elim (fun h => (b v h).1) (hg v)
    refine ⟨hi, ?_⟩
    rw [coef, coef, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one, fix_of_parts P m
      (e2 _ (i0 _ ⟨partU_real_mem g, fun w => commute_theta P.base P.herm h0 w _⟩)) fun v => ?_]
    · rfl
    by_cases h : v ∈ T
    · exact (b v h).2
    have l1 : partU (idem_mul_self v) g ∈ locGrp σ X v := Subgroup.subset_closure (partU_idem_mem v g)
    have := fx v h _ (emb_mem P.base P.herm h0 hK he (int_all l1 (prj_eq v g ▸ Euler.int_prj.2 (hi v)))) (at_emb he l1)
    obtain ⟨y, hy⟩ := Function.ne_iff.1 m0
    rw [bx] at this
    exact funext fun x => mul_right_cancel₀ (star_ne_zero.2 hy) (congrFun this (Sum.elim x y))
  have cl : IsClosed {g : UA σ X.J | ∀ v ∉ T, IntAt v g} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun v => isClosed_iInter fun _ => Euler.isClosed_int P.herm.lat v
  have ct : Continuous (coef om ν Φ) := by
    refine (((d1.weil.2.1.cont l d1.adm _ (d2 Φ m Φ m).1).comp (cont_emb he)).div_const (c : ℂ)).congr fun g => ?_
    exact (congrArg (· / (c : ℂ)) (cf g)).trans (mul_div_cancel_left₀ _ c1)
  have op : IsOpen {g | coef om ν Φ g ≠ 0} := isOpen_ne_fun ct continuous_const
  have val : ∀ z, ∫ g in {g | ∀ v ∉ T, IntAt v g}, zint om ν a e Φ z g ∂M.μ =
      M.μ.real ({g | coef om ν Φ g ≠ 0} ∩ {g | ∀ v ∉ T, IntAt v g}) • coef om ν Φ 1 := fun z => by
    rw [← measureReal_restrict_apply op.measurableSet, ← integral_indicator_const _ op.measurableSet]
    refine setIntegral_congr_fun cl.measurableSet fun g hg => ?_
    by_cases h : coef om ν Φ g = 0
    · rw [zint, h, mul_zero, Set.indicator_of_notMem (not_not.2 h)]
    · rw [zint, hgt_one ha (emb_mem P.base P.herm h0 hK he (key g hg h).1), (key g hg h).2, Set.indicator_of_mem h]
      simp
  simp only [val]
  refine ⟨differentiable_const _, smul_ne_zero (ENNReal.toReal_ne_zero.2 ⟨?_, ?_⟩) N⟩
  · have := P.good.haar
    refine (M.μ.measure_pos_of_mem_nhds (x := 1) (inter_mem (op.mem_nhds N) ?_)).ne'
    exact mem_of_superset (int_nhds P.herm.lat) fun g h v _ => h v
  · have := P.good.haar
    obtain ⟨K₁, -, -, k1, k2, -⟩ := hS F E σ B n X r s P.base P.herm
    exact ((measure_mono fun g h => (stab_iff P.base P.herm h0 k1).2 (key g h.2 h.1).1).trans_lt k2.measure_lt_top).ne

end GlobalTheory.ThK.Dbl.Bad

end
