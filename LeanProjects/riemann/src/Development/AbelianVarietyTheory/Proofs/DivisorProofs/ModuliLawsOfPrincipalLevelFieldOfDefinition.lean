import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralDetSubOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumRankOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnfoldingConstantTermsAgreeAtGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAbelianGaloisHost

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Matrix

namespace GlobalTheory.LevLaws

open GlobalTheory.PrincCore

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eq_one_of_norm_one {E : Type} [Field E] [NumberField E] [IsCMField E] {M : ℕ} (hM : 3 ≤ M) (u : E)
    (hint : IsIntegral ℤ ((u - 1) / M)) (hc : u * IsCMField.complexConj E u = 1) : u = 1 := by
  have hM0 : M ≠ 0 := by omega
  by_contra hne
  have hx : (⟨(u - 1) / M, hint⟩ : 𝓞 E) ≠ 0 := by
    intro h
    have : (u - 1) / (M : E) = 0 := congrArg Subtype.val h
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hM0 (Nat.cast_eq_zero.mp h)
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hx
  have hσ' : 1 ≤ ‖σ ((u - 1) / M)‖ := hσ
  have h1 : ‖σ u‖ = 1 := by
    have := congrArg (fun z => ‖σ z‖) hc
    simp only [map_mul, IsCMField.complexEmbedding_complexConj, norm_mul, map_one, norm_one,
      Complex.norm_conj] at this
    nlinarith [norm_nonneg (σ u)]
  rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast] at hσ'
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h2 : ‖σ u - 1‖ ≤ 2 := by
    have := norm_sub_le (σ u) 1
    rw [h1, norm_one] at this
    linarith
  rw [le_div_iff₀ (by linarith)] at hσ'
  linarith

set_option maxHeartbeats 800000 in

theorem det_eq_one {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (hr0 : 0 < r) {Comp : Type}
    (X : Comp → Data D.host.E r) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (Kf : Subgroup (GA D V)) (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hD : DictIsUnif V dict Kf th hr)
    (hmu : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1)
    (M : ℕ) (hM : 3 ≤ M) (hK : IsLevelK V M Kf) (k : Comp) (γ' : GL (Fin r) D.host.E) (hγ' : γ' ∈ (X k).Γ) :
    (γ' : Matrix (Fin r) (Fin r) D.host.E).det = 1 := by
  classical
  subst hr
  obtain ⟨-, -, ⟨x0, hx0, heq⟩, -, -, hfib⟩ := hD
  obtain ⟨hdom, g, hg⟩ := hx0 k
  obtain ⟨-, hrat, -, hsur⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).2 (X k).Ψ (th k) (X k).cmType (hth k)
  have hact : ∀ h, ∀ τ, mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ = archM V (th k τ) h * mat (x0 k) τ := by
    intro h τ
    show mat (x0 k) τ * ((mat (x0 k) τ)⁻¹ * Matrix.reindex (finCongr rfl) (finCongr rfl) (archM V (th k τ) h) *
      mat (x0 k) τ) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdom τ).1),
      Matrix.one_mul]
    rfl
  have key : ∀ h ∈ GinfC V, ∃ γ'' ∈ (X k).Γ,
      dict (g * h) = ⟨k, lact γ'' (rmul (x0 k) (archMat V th rfl x0 h k))⟩ := by
    have := heq g
    rw [hg] at this
    exact this
  have hun : ∀ τ : (X k).Ψ, ((γ'.1.map τ.1).map (starRingEnd ℂ))ᵀ * V.gram.map τ.1 *
      γ'.1.map τ.1 = V.gram.map τ.1 := by
    intro τ
    refine unitary_of_first_minor hr0 τ.1 (X k).Gm (X k).Gm_herm _ (mat (x0 k) τ) ?_ ?_ ?_ _ ?_
    · ext a b
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply, HSpace.gram]
      rw [← V.herm.eq (V.frame b) (V.frame a)]
      exact (IsCMField.complexEmbedding_complexConj D.host.E τ.1 _).symm
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero_iff _ τ.1.injective).2 (gram_det_ne V)
    · intro w hw
      obtain ⟨h, hh, hw'⟩ := hsur (Function.update (fun _ => 1) τ w) (by
        intro τ'
        by_cases e : τ' = τ
        · subst e
          simpa using hw
        · simp [Function.update_of_ne e])
      obtain ⟨γ'', h1, h2⟩ := key h hh
      have h3 := hmu (g * h)
      rw [h2] at h3
      have h4 := h3 τ ⟨1, by omega⟩
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.dmin_lact (X k) h1] at h4
      unfold dmin at h4
      rw [hact, hw', Function.update_self] at h4
      exact h4
    · have hcc : (γ'.1.map τ.1).map (starRingEnd ℂ) =
          (γ'.1.map cc).map τ.1 := by
        ext a b
        exact (IsCMField.complexEmbedding_complexConj D.host.E τ.1 _).symm
      rw [hcc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
        ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.gramE (X k) hγ']
  obtain ⟨h, hh, hw⟩ := hsur _ hun
  obtain ⟨γ'', h1, h2⟩ := key h hh
  obtain ⟨γ₀, hγ₀, κ, hκ, hdc⟩ := hfib g (g * h) (by
    rw [hg]
    refine ⟨γ'' * γ', mul_mem h1 hγ', ?_⟩
    rw [h2]
    congr 1
    funext τ
    show γ''.1.map τ.1 * mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ =
      (γ'' * γ').1.map τ.1 * mat (x0 k) τ
    rw [hact, hw, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc])
  obtain ⟨δ, hδ1, hδ2⟩ := hrat γ₀ hγ₀
  obtain ⟨hκ1, hκ2⟩ := (hK κ⁻¹).1 (inv_mem hκ)
  have hfin : finHom V γ₀ * finHom V g = finHom V g * finHom V κ⁻¹ := by
    have h0 : finHom V h = 1 := hh
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, h0, mul_one]
  have hinf : infHom V γ₀ * infHom V g = infHom V g * infHom V h := by
    have h0 : infHom V κ⁻¹ = 1 := hκ1
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, h0, mul_one]
  let f : V.V →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := V.frame.equivFun.toLinearMap.restrictScalars _
  have hhat : latHat V = GlobalTheory.AdLat.hat D.host.F (V.L0.map f : Set (Fin V.rank → D.host.E)) := by
    unfold latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, f x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have hspan : Submodule.span D.host.E (V.L0.map f : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have : (V.L0.map f : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, ← Submodule.map_span, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]
  rw [hhat] at hκ2
  obtain ⟨Λ', g1, g2, g3⟩ := exists_lattice_congr D.host.F D.host.E V.rank M (by omega) (V.L0.map f)
    (V.standardTuple_isLattice.fg.map f) hspan (finHom V g) (finHom V κ⁻¹).1 δ.1 hκ2 (by
      rw [← hδ2, ← Units.val_mul, hfin, Units.val_mul])
  obtain ⟨τ⟩ : Nonempty (X k).Ψ := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases e : τ ∈ (X k).Ψ
    · exact ⟨⟨τ, e⟩⟩
    · exact ⟨⟨_, not_not.1 (fun e' => e (((X k).cmType τ).2 e'))⟩⟩
  have hm : ∀ a b, archM V (th k τ) (a * b) = archM V (th k τ) a * archM V (th k τ) b := by
    intro a b
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  have h1' : archM V (th k τ) 1 = 1 := by
    unfold archM
    rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hg0 : (archM V (th k τ) g).det ≠ 0 := by
    have := congrArg Matrix.det (hm g⁻¹ g)
    rw [inv_mul_cancel, h1', Matrix.det_one, Matrix.det_mul] at this
    exact right_ne_zero_of_mul_eq_one this.symm
  have hconj : δ.1.map τ.1 * archM V (th k τ) g = archM V (th k τ) g * γ'.1.map τ.1 := by
    rw [← hw τ, ← hδ1 τ, ← hm, ← hm]
    unfold archM
    rw [map_mul, map_mul, hinf]
  have hdd : γ'.1.det = δ.1.det := by
    have := congrArg Matrix.det hconj
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, ← RingHom.map_det] at this
    exact τ.1.injective (mul_left_cancel₀ hg0 this).symm
  refine eq_one_of_norm_one hM _ ?_
    (GlobalTheory.CongruenceDet.det_mul_conj (X k).Gm _ (X k).Gm_det ((X k).Γ_stab γ' hγ').1)
  rw [hdd]
  refine isIntegral_trans (A := 𝓞 D.host.E) _
    (GlobalTheory.CongruenceDet.isIntegral_det_sub_one (by omega) Λ' _ g1 g2 fun v hv => ?_)
  obtain ⟨y, hy, e⟩ := g3 v hv
  exact ⟨y, hy, by rw [← Nat.cast_smul_eq_nsmul D.host.E, ← e, add_sub_cancel]⟩

open Module GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore in
set_option maxHeartbeats 1000000 in

theorem laws_of_level : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, Formalism.L2.Theta.GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → FnAlgClosed Xo c → (∀ p : ℕ, p.Prime → l.GoodAt p) → GlobalTheory.FlatCore.Laws U (xiR D) ∧ GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H := by
  intro D j H Dw l Xo c U dict h hF hg
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  refine ⟨⟨?_, h.levA, hg, h.unf, hF, h.xiAbs, h.chiTriv, fun σ hσ k γ hγ => ?_, fun σ hσ a n ha hp hn => ?_,
    GlobalTheory.RankOneDatum.exists_datum_of_rt D H h.host.2.1 h.host.2.2.1⟩, GlobalTheory.FlatRow.isHostField D H h.host.1⟩
  · have e : D.R.r = Dw.p + Dw.q := (h.unf c.F.val.toRingHom rfl).1
    omega
  · obtain ⟨Kf, th, hrk, hK, hth, hD, hu⟩ := h.dictU σ hσ
    exact det_eq_one _ hrk hr (U σ).X (dict σ) Kf th hth hD hu l.M l.three_le hK k γ hγ
  · obtain ⟨hrk, hM⟩ := h.modelW σ hσ
    obtain ⟨Kf, th, hrk', hK, hth, hD, hu⟩ := h.dictU σ hσ
    have key := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E H Dw l
      Xo c D.R.r (fun s => Formalism.L2.PjFree.Unf.ofPj (U s)) hr h.levA
      (fun s hs => (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf s hs)) σ hσ
      (fun k k' => ⟨(hM k).1.trans (hM k').1.symm, (hM k).2.trans (hM k').2.symm⟩)
      (fun k γ hγ hc0 => by
        have hc : ∀ x ∈ ((U σ).X k).Λ, ∃ y ∈ ((U σ).X k).Λ,
            Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (l.M : D.host.E) • y := by
          intro x hx
          obtain ⟨y, hy, e⟩ := hc0 x hx
          exact ⟨y, hy, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
        obtain ⟨γ', hγ', u, m, hm, hum, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
          (Formalism.L2.PjFree.Unf.ofPj (U σ)) (h.unf σ hσ) h.levA hr k γ hγ hc
        have h1 := root_eq_one _ hrk' hr (U σ).X (dict σ) (fun _ => 1) Kf th hth hD
          ⟨fun _ _ => (one_mul _).symm, fun _ => norm_one, fun _ _ => rfl, hu⟩ _ l.three_le hK k γ γ' hγ' hc u m hm hum he
        rw [h1, one_smul] at he
        exact Units.ext he ▸ hγ')
      a n ha (fun τ _ h0 => hp τ _ (by omega)) hn (fun k => h.chiTriv σ hσ a n ha k)
    intro P hP
    exact key ⟨hP.1, hP.2⟩

end GlobalTheory.LevLaws
