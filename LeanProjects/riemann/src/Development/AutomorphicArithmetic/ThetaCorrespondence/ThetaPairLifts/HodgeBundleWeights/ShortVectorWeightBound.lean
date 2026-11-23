import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisPeterssonSecond
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ShortGeneratorNormComparison
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisPeterssonSecondStatement

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace GlobalTheory.HSShortRoad
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
theorem short_vector_weight_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => 0 ≤ PP * kap p i ∧ ∀ Z, ∀ j ≤ lenT p i PP, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j)), (∀ q, v q ∈ latOn Y.U Z _) ∧ Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j) 0) σ (v q).1 ≤ Real.exp (PP * kap p i) := by
  intro h2 _hDG hSz hF
  obtain ⟨C₂, c₂, H₂⟩ := _root_.GlobalTheory.T.short_generator_norm_comparison h2
  have H₄ := _root_.GlobalTheory.T.covering_domain_lattice_regularity h2
  refine Closed.imp (Closed.and (Closed.and wtBig_run (GlobalTheory.T.weight_parameter_strict_antitone hSz))
    (Closed.and (GlobalTheory.T.size_bounds_for_family hSz) (Closed.and hSz hF))) ?_
  intro eps Fm CH heps h
  obtain ⟨⟨⟨_, -, a₁⟩, ⟨_, -, a₂⟩⟩, ⟨_, -, a₃⟩, ⟨_, -, a₄⟩, ⟨_, -, a₅⟩⟩ := h
  have e₆ : EvTied Fm fun x _ ι _ => 6 * C₂ ≤ (Fm.L x ι).sc.L := by
    refine ⟨(6 * C₂) ^ eps⁻¹, fun x hx hle ι p _ => ?_⟩
    have hx1 := Fm.L_x x ι hx
    have he := Fm.L_eps x ι
    have h0 : (0 : ℝ) ≤ 6 * C₂ := by positivity
    show _ ≤ (Fm.L x ι).sc.x ^ (Fm.L x ι).sc.eps
    rw [hx1, he]
    calc 6 * C₂ = ((6 * C₂) ^ eps⁻¹) ^ eps := (Real.rpow_inv_rpow h0 heps.ne').symm
      _ ≤ x ^ eps := Real.rpow_le_rpow (by positivity) hle heps.le
  obtain ⟨x0, a⟩ := ((((a₁.and a₂).and a₃).and a₄).and a₅).and e₆
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨⟨⟨⟨b₁, b₂⟩, b₃⟩, b₄⟩, b₅⟩, hCL⟩ := a x hx hle ι p hp
  clear a a₁ a₂ a₃ a₄ a₅ e₆
  have hW := b₁ i hi
  obtain ⟨hp1, hq1, hE, -⟩ := b₂ i hi
  obtain ⟨hLaw, hIn, hL, hM, hFs, hfr, -, -, hf8, hr, hc₁, hκ2, hPP, -, -, -, -, hwt⟩ := b₃ i hi Y hY
  have s1 : 1 ≤ (Fm.L x ι).sc.b := (b₄ i).1
  have s2 : (Fm.L x ι).sc.b ≤ (Fm.parT x hx ι).PP * kap p i := (b₄ i).2.2.2.2.2.1
  have hFl := b₅ i hi Y hY
  have hdim := (GlobalTheory.T.anchoredWeight_indefiniteLift_gaps p (Fm.params x hx ι) i hi).2.1
  clear b₁ b₂ b₃ b₄ b₅
  unfold zBase at hPP hwt
  have hY' : Y.Good _ (391 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 2) := hY.1
  replace H₂ := fun la a b c Z => H₂ _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY' _ hL hM hFs hfr le_rfl _ hFl
    (by rwa [abs_neg]) la a b c Z
  replace H₄ := H₄ _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY'
  have hfr1 : (1 : ℝ) ≤ ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r := by
    exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hgap : ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 : ℕ) : ℤ) ≤ FlagTan.dimFlag (dat p i) + 1 := by
    have : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 ≤ FlagTan.dimFlag (dat p i) + 1 := by
      rw [hdim]
      generalize (Fm.D x ι).R.f = f at hf8 ⊢
      generalize (Fm.D x ι).R.r = r at hr ⊢
      have : 9 * r ≤ r.choose 2 := by
        rw [Nat.choose_two_right]
        exact (Nat.le_div_iff_mul_le two_pos).2 (by nlinarith [Nat.mul_le_mul_left r (show 18 ≤ r - 1 by omega)])
      nlinarith [Nat.mul_le_mul_left f this, Nat.mul_le_mul hf8 hr]
    exact_mod_cast this
  have hLZ : (Fm.L x ι).sc.L ≤ (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) := le_mul_of_one_le_left (by linarith) hfr1
  have hZ : 1 ≤ (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) := hL.trans hLZ
  have hPP0 : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hPP
  have hPk : 1 ≤ (Fm.parT x hx ι).PP * kap p i := s1.trans s2
  have hκpos : 0 < kap p i := by
    by_contra hneg
    have h0 : (Fm.parT x hx ι).PP * kap p i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hPP0 (not_lt.1 hneg)
    exact absurd (hPk.trans h0) (by norm_num)
  have hκ : 1 ≤ kap p i := one_le_sz hκpos
  have hZ3 : 0 ≤ (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 3 := by positivity
  refine ⟨zero_le_one.trans hPk, fun Z j hj => ?_⟩
  have hg := gapGe_wt hW j
  have ha := antitone_of_gapGe (by positivity) hg
  have hb : ∀ τ, ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 : ℕ) : ℤ) ≤ gap ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ : WtPar (dat p i)).wt j τ) ((dat p i).p - 1) :=
    fun τ => hgap.trans (hg τ ((dat p i).p - 1) (by omega))
  have hs := hwt j hj
  have h1 := hs.trans (le_mul_of_one_le_left (by positivity) one_le_two)
  have hX := H₂ ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ : WtPar (dat p i)).wt j) ha hb
    (log_size_le (by positivity) hL hfr hκ hκ2 (by positivity) (le_trans (le_of_eq (sum_univ_inst _)) h1)) Z
  obtain ⟨n, w, Λ, hSG, hΛ, _hn⟩ := hX
  have hY4 := H₄ ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ : WtPar (dat p i)).wt j) ha (fun τ => le_trans (by omega) (hb τ))
  obtain ⟨_hGA, hGO⟩ := hY4
  have hsp := span_of_shortGen hSG (hGO Z).2.2
  obtain ⟨hmem, hspan⟩ := hsp
  refine ⟨n, w, hmem, hspan, fun q σ => ?_⟩
  have hΛ' : Real.log Λ ≤ (Fm.parT x hx ι).PP * kap p i := by
    refine hΛ.trans (le_trans ?_ (bound_le c₂ hZ (hCL.trans hLZ) hPP hκ))
    refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left ?_ hZ3) le_rfl) c₂
    exact le_trans (le_of_eq (sum_univ_inst _)) hs
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hSG.one_le
  calc _ ≤ Λ := hSG.le q σ
    _ = Real.exp (Real.log Λ) := (Real.exp_log hΛ0).symm
    _ ≤ _ := Real.exp_le_exp.2 hΛ'
end GlobalTheory.HSShortRoad
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_path_weight_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => 0 ≤ PP * kap p i ∧ ∀ Z, ∀ j ≤ lenT p i PP, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j)), (∀ q, v q ∈ latOn Y.U Z _) ∧ Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j) 0) σ (v q).1 ≤ Real.exp (PP * kap p i) := by
  first | exact @_root_.GlobalTheory.HSShortRoad.short_vector_weight_bound | exact _root_.GlobalTheory.HSShortRoad.short_vector_weight_bound | (intros; apply _root_.GlobalTheory.HSShortRoad.short_vector_weight_bound <;> assumption)
end
