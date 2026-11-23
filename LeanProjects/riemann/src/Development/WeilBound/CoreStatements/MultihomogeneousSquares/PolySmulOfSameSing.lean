import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
import Development.WeilBound.CoreStatements.FlagImmersions.AevalEqZeroOfMem
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPullB
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmpPairOfInputs
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ImageCptReflOfGenPt
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CmpHodgeTied
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositiveStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarietiesStatement

noncomputable section

namespace SquareStatements

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp RootFieldNumerics.Sq
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

theorem cmp_arith {a b e₁ e₂ d₁ d₂ m : ℝ} (p₁ : e₁ ≠ 0) (p₂ : e₂ ≠ 0) (hm : m ≠ 0) (h : e₁ * (m * d₁) = e₂ * d₂) :
    (a / d₁ - (e₁ * a - e₂ * b) / (e₁ * d₁)) / m = b / d₂ := by
  rw [sub_div (e₁ * a), mul_div_mul_left _ _ p₁, sub_sub_cancel, div_div, show e₁ * d₁ * m = e₂ * d₂ by rw [← h]; ring,
    mul_div_mul_left _ _ p₂]

theorem poly_smul_of_sameSing (hN : SheetDecomposition.NumPull) (hIn : PB.Inputs) (hC : CmpSt) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]
    {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    {κ₁ : K₁ → K} {v₁ : (Σ k, ι₁ k) → Σ k, ι k} {κ₂ : K₂ → K} {v₂ : (Σ k, ι₂ k) → Σ k, ι k}
    {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω} {D : ℕ} {σ : Type} [Fintype σ] {S₁ S₂ : PB.AnSys D σ}
    {P₁ : Ideal (MRing ι₁)} {P₂ : Ideal (MRing ι₂)} (Re₁ : PB.Realis S₁ P₁) (Re₂ : PB.Realis S₂ P₂)
    (h₁ : mCoordIdeal (y ∘ v₁) = P₁) (h₂ : mCoordIdeal (y ∘ v₂) = P₂) {β : MRing ι} {b : K → ℕ}
    (hv₁ : IsBlockMap κ₁ v₁) (hv₂ : IsBlockMap κ₂ v₂) (hy : IsArithVar (mCoordIdeal y) (D + 1))
    (hβ : IsMultiHomog β b) (hβy : β ∉ mCoordIdeal y) (hA₁ : AlgOver Re₁) (hA₂ : AlgOver Re₂)
    (hS : ∀ a, SameSing Re₁ Re₂ (mCoordIdeal y) κ₁ v₁ κ₂ v₂ β a a)
    (hne : IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) ≠ 0)
    {m : ℕ} (hm : m ≠ 0) (hdeg : IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) * (m * Re₁.deg) =
      IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) * Re₂.deg) :
    Re₁.PB II = (m : ℝ) • Re₂.PB II ∧ S₁.degPoly = (m : ℝ) • S₂.degPoly := by
  have hne' : IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) ≠ 0 :=
    left_ne_zero_of_mul (hdeg ▸ mul_ne_zero hne (mul_ne_zero hm Re₁.deg_pos.ne'))
  have hW := PairTop.cmpSt_of_eq hC II hII K ι K₁ ι₁ K₂ ι₂ κ₁ v₁ κ₂ v₂ Ω y D σ S₁ S₂ P₁ P₂ Re₁ Re₂ h₁ h₂ β b hv₁ hv₂ hy hβ hβy
    hA₁ hA₂ hS
  have hG := fun w : Fin D → σ => intNum_cmp hN y hv₁ hv₂ hy hne hne' (fun j => (Re₁.ref (w j)).a) (fun j => (Re₂.ref (w j)).a)
    fun j => (hS (w j)).imp fun f => Exists.imp fun g h => h.1
  rw [h₁, h₂] at hG
  generalize IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) = e₁ at *
  generalize IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) = e₂ at *
  have hdeg' : (e₁ : ℝ) * (m * Re₁.deg) = e₂ * Re₂.deg := by exact_mod_cast hdeg
  have p₁ : (e₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hne
  have p₂ : (e₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hne'
  have q₁ : (Re₁.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Re₁.deg_pos.ne'
  have pm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  constructor
  · rw [PB.Realis.PB, PB.Realis.PB, ← PB.formPoly_const_mul]
    refine congrArg (PB.formPoly (D + 1)) (funext fun w => ?_)
    obtain ⟨C₃, s₀, -, h⟩ := GlobalTheory.T.agreement_positive hIn D σ S₁ 0 (S₁.reg (w 0)).1
    have c₁ := (h II hII _ _ _ Re₁).1 w
    have c₂ : Tendsto (fun t => Re₂.num II t w) (𝓝[>] 0) (𝓝 (Re₁.limNum II w / m)) := by
      have := (c₁.sub ((hW w).div_const ((e₁ : ℝ) * Re₁.deg))).div_const (m : ℝ)
      rw [zero_div, sub_zero] at this
      refine this.congr fun t => ?_
      exact cmp_arith p₁ p₂ pm hdeg'
    rw [show Re₂.limNum II w = _ from c₂.limUnder_eq, mul_div_cancel₀ _ pm]
  · rw [PB.AnSys.degPoly, PB.AnSys.degPoly, ← PB.formPoly_const_mul]
    refine congrArg (PB.formPoly D) (funext fun w => ?_)
    have h := congrArg (Int.cast : ℤ → ℝ) (hG w)
    push_cast at h
    rw [← degNum_eq hIn Re₁, ← degNum_eq hIn Re₂, ← mul_assoc, ← mul_assoc, ← hdeg'] at h
    exact mul_left_cancel₀ (mul_ne_zero p₁ q₁) (h.trans (by ring))

theorem stCmp : StCmp := by
  intro hIn hC II hII E _ _ _ H D l Xo c O _ β Y S n M M' T T' hβ hgen hR hd hd'
  classical
  have hm : T.Fl.deg ≠ 0 := by
    obtain ⟨_, _, -, -, -, -, -, -, -, -, h, -⟩ := T.Fl.generic
    exact h.ne'
  have hsab : SABMap (twistSAB Xo.univ.t (HostAut.refl H)) Xo.univ.t (Iso.refl Xo.X).hom := by
    rw [(twistSAB_symm_refl E H Xo.X Xo.univ.t (HostAut.refl H)).2.2]
    exact (exists_sabMap_id E H Xo.X Xo.univ.t).choose
  obtain ⟨K, hK, ι, hι, κ, v, κ', v', Ω, hΩ, hΩ0, y, b, d, hbv, hbv', hP, hP', harith, hmh, hb, hne, hdeg, hiso⟩ :=
    GlobalTheory.T.twisted_hodge_tie_compare PositivityTheory.UnitarySelfGeneration.cmpHodgeTiedAlt GlobalTheory.T.theta_uniformisation_complex_abelian_varieties E H D l Xo c O β Y (HostAut.refl H) (Iso.refl Xo.X) hsab (Equiv.refl _) S n M M' T T'
      hβ (by simp) (fun τ => by ext; rfl)
      (Indep.imageCpt_refl_of_genPt E H D l Xo c O β Y S _ _ _ _ _ _ _ _ T.A T'.A hβ hgen) hR
  have hJ := GlobalTheory.T.block_pullback_herm_line M.K M.ι K ι κ v hbv
  have hJ' := GlobalTheory.T.block_pullback_herm_line M'.K M'.ι K ι κ' v' hbv'
  have hmpp : IsMultiProjPrime (mCoordIdeal y) := harith.2.1
  obtain ⟨hc1, -, -, hc4⟩ := GlobalTheory.T.iso_line_on_equivalence K ι (mCoordIdeal y)
    {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} hmpp (fun z hz => hz.1)
  choose Lr hLr using fun r => (hJ.1 (T.sing r)).exists
  choose Lr' hLr' using fun r => (hJ'.1 (T'.sing r)).exists
  refine poly_smul_of_sameSing SheetDecomposition.numPull hIn hC II hII T.Re T'.Re hP hP' hbv hbv' harith hmh hb T.alg T'.alg (fun a => ?_) hne hm
    (by rw [hd, hd', mul_one, hdeg])
  exact GlobalTheory.T.realisation_fibre_product_compatible K ι M.K M.ι M'.K M'.ι κ v κ' v' (mCoordIdeal y) M.P M'.P _ _ _ T.Sy T'.Sy T.Re T'.Re b a a _ _ _ _ hbv hbv'
    (hc4 _ _ κ v _ _ _ _ hbv hLr) (hc4 _ _ κ' v' _ _ _ _ hbv' hLr') (T.ref_deg a) (T'.ref_deg a) (T.sing_eq a)
    (T'.sing_eq a) hmpp (hc1 _ Lr Lr' _ fun r => hiso r _ _ (hLr r) (hLr' r))

end SquareStatements
