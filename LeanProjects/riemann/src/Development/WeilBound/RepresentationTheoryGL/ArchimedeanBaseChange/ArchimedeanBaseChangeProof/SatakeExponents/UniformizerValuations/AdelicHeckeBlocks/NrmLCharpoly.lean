import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelRep
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PAdelEqOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PTranslAd
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PPolEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfTwist
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PTestJ
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.ContinuousEmbInf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.HasCompactSupportOfSection

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

open PositivityTheory.Rg.Tf.Loc (twConj)

theorem nrmL_charpoly {w : Pl E} (hw : ¬ IsSplitAt w) {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E)
    (x : GA E n) :
    (nrmL n w (GeneralLinearGroup.map (pLoc E w) (gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹))).val.charpoly
      = (nrm d).val.charpoly.map (algebraMap E (w.adicCompletion E)) := by
  set c := GeneralLinearGroup.map (pFin E) x
  have h1 : GeneralLinearGroup.map (pLoc E w) (gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹) =
      GeneralLinearGroup.map (pLoc E w) (c⁻¹ * ratF E n (d * u⁻¹) * thF E n c) := by
    rw [← adeleqof_cpt translAd_holds hu d x w, cpt, adeleqof_map_cW]
    congr 1
    rw [map_mul, map_inv, adeleqof_pFin_ratGL]
    rfl
  set r := ratF E n (d * u⁻¹) with hr0
  set s := ratF E n (thE E n (d * u⁻¹)) with hs0
  have hr : thF E n r = s := by
    rw [hr0, hs0]
    rw [GlobalTheory.EulerTw.Comm.thF_ratF]
  have h2 : (c⁻¹ * r * thF E n c) * thF E n (c⁻¹ * r * thF E n c) = c⁻¹ * ratF E n (nrm d) * c := by
    rw [← poleq_norm E n u hu d, map_mul (ratF E n), ← hr0, ← hs0, map_mul, map_mul, map_inv,
      GlobalTheory.EulerTw.Comm.thF_thF, hr]
    group
  have h3 : nrmL n w (GeneralLinearGroup.map (pLoc E w) (c⁻¹ * r * thF E n c)) =
      GeneralLinearGroup.map (pLoc E w) (c⁻¹ * ratF E n (nrm d) * c) := by
    have hz : ∀ g, thetaGL n (cj w) (GeneralLinearGroup.map (pLoc E w) g) = GeneralLinearGroup.map (pLoc E w) (thF E n g) := by
      intro g; rw [GlobalTheory.CompanionTheory.SuppFinTw.map_thF_of_not_split hw, thL, if_neg hw]
    rw [nrmL, if_neg hw, hz, ← map_mul, h2]
  rw [h1, h3, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    Matrix.charpoly_units_conj']
  rw [← Matrix.charpoly_map]
  rfl

theorem val_mem {m : ℕ} (y : GL (Fin m) ℂ) : y.val ∈ GLs m := by
  show y.val.det ≠ 0
  exact ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem phiOf_cont {m : ℕ} [MeasurableSpace (G m)] {μ : Measure (G m)} {M : KMod m} (Tθ : M.V →L[ℂ] M.V)
    {k : Mat m → (M.V →L[ℂ] M.V)} {val} {T : ℝ} (hM : IsMult μ M k val T) : Continuous (phiOf M Tθ k) := by
  obtain ⟨l, c, w, g, ks, hks, hk, -⟩ := hM
  set F : GL (Fin m) ℂ → (M.V →L[ℂ] M.V) := fun y => ∑ i, c i • ks i y.val with hFdef
  have hkF : ∀ y : GL (Fin m) ℂ, k y.val = F y := fun y => hk _ (val_mem y)
  have hF : Continuous F := continuous_finsetSum _ fun i _ =>
    (((hks i).2.1.continuousOn).comp_continuous Units.continuous_val fun y => val_mem y).const_smul (c i)
  let L : (M.V →L[ℂ] M.V) →ₗ[ℂ] ℂ := (LinearMap.trace ℂ M.V).comp (ContinuousLinearMap.coeLM ℂ)
  have hphi : phiOf M Tθ k = fun y => L (F y * Tθ) := by
    funext y
    rw [← hkF]
    rfl
  rw [hphi]
  exact L.continuous_of_finiteDimensional.comp (hF.mul continuous_const)

theorem phiOf_lg {m : ℕ} {M : KMod m} (Tθ : M.V →L[ℂ] M.V) {k : Mat m → (M.V →L[ℂ] M.V)} (c T : ℝ)
    (hk : ∀ y ∈ GLs m, c * (1 + T) < lg y → k y = 0) (y : G m) (hy : phiOf M Tθ k y ≠ 0) : lg y.val ≤ c * (1 + T) := by
  by_contra h
  push Not at h
  apply hy
  rw [phiOf, hk _ (val_mem y) h, zero_mul]
  simp

end Reg

open PositivityTheory.Rg.Tf.Loc (twConj) in
theorem regOf : RegOf := by
  intro E _ _ _ a b S u₁ u₂ hu₁ hu₂ φ₁ φ₂ h₁ h₂ hw
  obtain ⟨w, hwS, hns, hreg⟩ := hw
  refine ⟨fun d x h₂' hne => ?_, fun d x h₁' hne => ?_⟩
  · have hf := (GlobalTheory.CompanionTheory.SuppFinTw.factors_ne h₁ h₂ _ hne w hwS).1
    have hs1 := Polynomial.Separable.of_mul_left (hreg _ hf)
    change (nrmL a w (GeneralLinearGroup.map (pLoc E w)
      (gFin (twConj (thetaA E a) x (ratGL E a d)) * (ratF E a u₁)⁻¹))).val.charpoly.Separable at hs1
    rw [Reg.nrmL_charpoly hns hu₁] at hs1
    exact (Polynomial.separable_map _).1 hs1
  · have hf := (GlobalTheory.CompanionTheory.SuppFinTw.factors_ne h₁ h₂ _ hne w hwS).1
    have hs1 := Polynomial.Separable.of_mul_right (hreg _ hf)
    change (nrmL b w (GeneralLinearGroup.map (pLoc E w)
      (gFin (twConj (thetaA E b) x (ratGL E b d)) * (ratF E b u₂)⁻¹))).val.charpoly.Separable at hs1
    rw [Reg.nrmL_charpoly hns hu₂] at hs1
    exact (Polynomial.separable_map _).1 hs1

theorem pTTest (h0 : RegOf) (h1 : FinConv) (h2 : FmTr) (hk : KerEx) : PTTest := by
  intro E _ _ _ B
  have := B.ha
  have := B.hb
  have : BorelSpace (G B.a) := ⟨rfl⟩
  have : BorelSpace (G B.b) := ⟨rfl⟩
  obtain ⟨ca, hca⟩ := hk B.a
  obtain ⟨cb, hcb⟩ := hk B.b
  set c₀ : ℝ := max 0 (max ca cb) with hc₀
  have hc₀0 : 0 ≤ c₀ := le_max_left _ _
  refine ⟨2 * Fintype.card (InfinitePlace E) * c₀, by positivity, ?_⟩
  intro κ _ S P e hS hPS hne u₁ u₂ hu₁ hu₂ Ta Tb N t L hVC ht hL hψ hreg
  set γ : Hf E B.a B.b := (ratF E B.a u₁, ratF E B.b u₂) with hγ
  obtain ⟨hTr, hFm⟩ := h2 E κ S P B e hPS hne L N hL
  obtain ⟨-, hFC⟩ := h1 E B S hS
  obtain ⟨hcs, ⟨U, hUo, hU⟩, -⟩ := hFC (L.tr P N) L.t hTr hL.2
  set Ψ : Hf E B.a B.b → ℂ := fun h => B.vol⁻¹ * finFn S (L.tr P N) L.t (h * γ⁻¹) with hΨ
  have hΨeq : ∀ h, ∑ x, ∑ y, t.ψ x y h * tenN P B e N y x = Ψ h := by
    intro h
    rw [hψ]
    exact hFm (h * γ⁻¹)
  have hT1 : 0 ≤ 1 + t.T := by linarith [ht.T]
  have hR0 : 0 ≤ c₀ * (1 + t.T) := mul_nonneg hc₀0 hT1
  have hfa : ∀ v, Continuous (phiOf (B.Ma v) (Ta v) (t.ka v)) ∧ VeryCusp (phiOf (B.Ma v) (Ta v) (t.ka v)) ∧
      ∀ y, phiOf (B.Ma v) (Ta v) (t.ka v) y ≠ 0 → lg y.val ≤ c₀ * (1 + t.T) := fun v =>
    ⟨Reg.phiOf_cont _ (ht.ka v), hVC.1 v _ _ _ (ht.ka v), fun y hy =>
      (Reg.phiOf_lg _ ca t.T ((hca B.μa (B.Ma v)).2 _ _ t.T ht.T (ht.ka v)) y hy).trans
        (mul_le_mul_of_nonneg_right ((le_max_left ca cb).trans (le_max_right _ _)) hT1)⟩
  have hfb : ∀ v, Continuous (phiOf (B.Mb v) (Tb v) (t.kb v)) ∧ VeryCusp (phiOf (B.Mb v) (Tb v) (t.kb v)) ∧
      ∀ y, phiOf (B.Mb v) (Tb v) (t.kb v) y ≠ 0 → lg y.val ≤ c₀ * (1 + t.T) := fun v =>
    ⟨Reg.phiOf_cont _ (ht.kb v), hVC.2 v _ _ _ (ht.kb v), fun y hy =>
      (Reg.phiOf_lg _ cb t.T ((hcb B.μb (B.Mb v)).2 _ _ t.T ht.T (ht.kb v)) y hy).trans
        (mul_le_mul_of_nonneg_right ((le_max_right ca cb).trans (le_max_right _ _)) hT1)⟩
  have hsz : ∀ h, Ψ h ≠ 0 → logSize (finGL E B.a h.1) ≤ t.r ∧ logSize (finGL E B.b h.2) ≤ t.r := by
    intro h hh
    rw [← hΨeq] at hh
    obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hh
    obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    exact ht.size x y h (left_ne_zero_of_mul hy)
  have hfin : ∀ g, Ψ g ≠ 0 → finFn S (L.tr P N) L.t (g * γ⁻¹) ≠ 0 := fun g hg => right_ne_zero_of_mul hg
  obtain ⟨hr₁, hr₂⟩ := h0 E B.a B.b S u₁ u₂ hu₁ hu₂ (L.tr P N) L.t hTr hL.2 hreg
  set U' : Subgroup (Hf E B.a B.b) := U ⊓ U.comap (MulAut.conj γ).toMonoidHom with hU'
  have hU'o : IsOpen (U' : Set (Hf E B.a B.b)) := by
    rw [hU', Subgroup.coe_inf, Subgroup.coe_comap]
    exact hUo.inter (hUo.preimage (by
      show Continuous fun x : Hf E B.a B.b => γ * x * γ⁻¹
      fun_prop))
  have hΨU : ∀ u ∈ U', ∀ h, Ψ (u * h) = Ψ h ∧ Ψ (h * u) = Ψ h := by
    intro u hu h
    have hc : γ * u * γ⁻¹ ∈ U := hu.2
    have e : h * u * γ⁻¹ = h * γ⁻¹ * (γ * u * γ⁻¹) := by group
    refine ⟨?_, ?_⟩
    · show B.vol⁻¹ * finFn S (L.tr P N) L.t (u * h * γ⁻¹) = B.vol⁻¹ * finFn S (L.tr P N) L.t (h * γ⁻¹)
      rw [mul_assoc u h, (hU u hu.1 _).1]
    · show B.vol⁻¹ * finFn S (L.tr P N) L.t (h * u * γ⁻¹) = B.vol⁻¹ * finFn S (L.tr P N) L.t (h * γ⁻¹)
      rw [e, (hU _ hc _).2]
  have hcsΨ : HasCompactSupport Ψ :=
    (hcs.comp_homeomorph (Homeomorph.mulRight γ⁻¹)).mul_left (f := fun _ => B.vol⁻¹)
  have key := PositivityTheory.Rg.BcB.CG.test2J E B.a B.b (fun v => phiOf (B.Ma v) (Ta v) (t.ka v))
    (fun v => phiOf (B.Mb v) (Tb v) (t.kb v)) Ψ (c₀ * (1 + t.T)) t.r U' hR0 hfa hfb hcsΨ hU'o hΨU hsz
    (fun d x h₂ hne => hr₁ d x h₂ (hfin _ hne)) (fun d x h₁ hne => hr₂ d x h₁ (hfin _ hne))
  have hfun : trM t.Φ (opM Ta Tb (tenN P B e N)) = fun g =>
      (∏ v, phiOf (B.Ma v) (Ta v) (t.ka v) (gInf v g.1)) * (∏ v, phiOf (B.Mb v) (Tb v) (t.kb v) (gInf v g.2)) *
        Ψ (hFin g) := by
    funext g
    rw [PT.Φ, PositivityTheory.Rg.BcB.CG.tensTr, hΨeq]
  rw [hfun]
  exact PositivityTheory.Rg.BcB.CG.isTest2J_mono key (le_of_eq (by ring))

end PositivityTheory.Rg.BcB.F

end
