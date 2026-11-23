import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasures
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfHermEBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantUnipotentTranslate

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.ThetaCoefND

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

variable {D : D7} {r : ℕ}

instance countable_hermE (D : D7) (r : ℕ) : Countable (HermE D r) := by
  haveI := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  haveI : Countable (Matrix (Fin r) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin r → Fin r → D.host.E))
  exact inferInstanceAs (Countable {b : Matrix (Fin r) (Fin r) D.host.E // _})

set_option synthInstance.maxHeartbeats 400000 in

theorem setIntegral_char_eq_zero {lam : Measure (hermA D r)} {𝓖 : Set (hermA D r)} (hl : IsCovolOneH lam 𝓖)
    (e : hermA D r → ℂ) (hadd : ∀ x y, e (x + y) = e x * e y)
    (hΓ : ∀ γ ∈ ratHerm D r, e γ = 1) (b₀ : hermA D r) (hb₀ : e b₀ ≠ 1) :
    ∫ b in 𝓖, e b ∂lam = 0 := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D r) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : BorelSpace (hermA D r) := Subtype.borelSpace _
  haveI : lam.IsAddHaarMeasure := hl.1
  haveI : VAddInvariantMeasure (hermA D r) (hermA D r) lam := ⟨fun c s _ => measure_preimage_add lam c s⟩
  haveI : VAddInvariantMeasure (ratHerm D r) (hermA D r) lam := ⟨fun c s _ => measure_preimage_add lam c.1 s⟩
  haveI : Countable (ratHerm D r) :=
    (GlobalTheory.CompanionTheory.HermPoisson.ofHermE_bijective (D := D) (r := r)).2.countable
  have hF := hl.2.1
  have hF' : IsAddFundamentalDomain (ratHerm D r) (b₀ +ᵥ 𝓖) lam := hF.vadd_of_comm b₀
  have h1 : ∫ b in b₀ +ᵥ 𝓖, e b ∂lam = ∫ b in 𝓖, e b ∂lam := by
    refine hF'.setIntegral_eq hF fun γ x => ?_
    show e (γ.1 + x) = e x
    rw [hadd, hΓ _ γ.2, one_mul]
  have h2 : ∫ b in 𝓖, e (b₀ + b) ∂lam = ∫ b in b₀ +ᵥ 𝓖, e b ∂lam := by
    have := (measurePreserving_add_left lam b₀).setIntegral_preimage_emb
      (measurableEmbedding_addLeft b₀) e (b₀ +ᵥ 𝓖)
    rw [← this]
    congr 2
    ext x
    simp [Set.mem_vadd_set_iff_neg_vadd_mem]
  have h3 : ∫ b in 𝓖, e (b₀ + b) ∂lam = e b₀ * ∫ b in 𝓖, e b ∂lam := by
    simp only [hadd, integral_const_mul]
  have h4 : (e b₀ - 1) * ∫ b in 𝓖, e b ∂lam = 0 := by
    rw [sub_mul, ← h3, h2, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 hb₀)

theorem pairH_add_left (ψ : AddChar (AF D.host.F) ℂ) (S S' x : hermA D r) :
    pairH ψ (S + S') x = pairH ψ S x * pairH ψ S' x := by
  unfold pairH
  rw [show trF (S + S').1 x.1 = trF S.1 x.1 + trF S'.1 x.1 from trF_add_left _ _ _, mul_add,
    AddChar.map_add_eq_mul]

theorem pairH_add_right (ψ : AddChar (AF D.host.F) ℂ) (S x y : hermA D r) :
    pairH ψ S (x + y) = pairH ψ S x * pairH ψ S y := by
  unfold pairH
  rw [show trF S.1 (x + y).1 = trF S.1 x.1 + trF S.1 y.1 from trF_add_right _ _ _, mul_add,
    AddChar.map_add_eq_mul]

theorem pairH_ne_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (S x : hermA D r) :
    pairH ψ S x ≠ 0 := by
  intro h
  have := hψ.2.1 (algebraMap D.host.F (AF D.host.F) (1 / 2) * trF S.1 x.1)
  unfold pairH at h
  rw [h] at this
  simp at this

theorem setIntegral_pairH {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {lam : Measure (hermA D r)} {𝓖 : Set (hermA D r)} (hl : IsCovolOneH lam 𝓖) {T β : HermE D r} (hT : T ≠ β) :
    ∫ b in 𝓖, pairH ψ (GlobalTheory.CompanionTheory.HermPoisson.ofHermE T).1 b * (pairH ψ (GlobalTheory.CompanionTheory.HermPoisson.ofHermE β).1 b)⁻¹ ∂lam = 0 := by
  set S := (GlobalTheory.CompanionTheory.HermPoisson.ofHermE T).1 with hS
  set S' := (GlobalTheory.CompanionTheory.HermPoisson.ofHermE β).1 with hS'
  obtain ⟨h1, h2⟩ := pairH_annih (r := r) hψ
  have hne : S - S' ≠ 0 := fun h => hT
    ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE_bijective (D := D) (r := r)).1 (Subtype.ext (sub_eq_zero.1 h)))
  have hex : ∃ b₀, pairH ψ (S - S') b₀ ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hne (h2 _ (sub_mem (GlobalTheory.CompanionTheory.HermPoisson.ofHermE T).2 (GlobalTheory.CompanionTheory.HermPoisson.ofHermE β).2) hcon)
  obtain ⟨b₀, hb₀⟩ := hex
  have hdec : ∀ b, pairH ψ S b = pairH ψ (S - S') b * pairH ψ S' b := fun b => by
    rw [← pairH_add_left, sub_add_cancel]
  refine setIntegral_char_eq_zero hl _ (fun x y => ?_) (fun γ hγ => ?_) b₀ ?_
  · rw [pairH_add_right, pairH_add_right, mul_inv]
    ring
  · rw [(h1 γ).2 hγ S (GlobalTheory.CompanionTheory.HermPoisson.ofHermE T).2, (h1 γ).2 hγ S' (GlobalTheory.CompanionTheory.HermPoisson.ofHermE β).2]
    simp
  · rw [hdec, mul_assoc, mul_inv_cancel₀ (pairH_ne_zero hψ _ _), mul_one]
    exact hb₀

end GlobalTheory.CompanionTheory.ThetaCoefND

namespace GlobalTheory.CompanionTheory.ThetaCoefND

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND PositivityTheory.PfSWUS
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

variable {D : D7} {r : ℕ}

theorem rat_gramQ (V : HSp D) (x : Matrix (Fin V.rank) (Fin r) D.host.E) :
    ((gramQ V x).map (incA D) : Mx D r r) =
      HMul.hMul (adj (x.map (incA D))) (HMul.hMul (gA V) (x.map (incA D)) : Mx D V.rank r) := by
  have h : gramQ V x = xᴴ * (HSpace.gram V * x) := rfl
  change rat (gramQ V x) = HMul.hMul (adj (rat x)) (HMul.hMul (gA V) (rat x) : Mx D V.rank r)
  rw [h, rat_mul, rat_mul, rat_conjTranspose]
  rfl

theorem inner_invPt (V : HSp D) (h : GA D V) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E) :
    inner V (GlobalTheory.SiegelFormula.invPt V h ξ) (GlobalTheory.SiegelFormula.invPt V h ξ) = (gramQ V ξ).map (incA D) := by
  rw [rat_gramQ]
  unfold GlobalTheory.StdUnn.inner GlobalTheory.SiegelFormula.invPt
  have u := GlobalTheory.MixModel.mt_unitary V h⁻¹
  calc _ = HMul.hMul (adj (ξ.map (incA D))) (HMul.hMul (HMul.hMul (adj (Formalism.L2.Theta.mt V h⁻¹))
        (HMul.hMul (gA V) (Formalism.L2.Theta.mt V h⁻¹) : Mx D V.rank V.rank) : Mx D V.rank V.rank) (ξ.map (incA D)) : Mx D V.rank r) := by
        rw [adj_mul]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [u]

theorem rank_of_gramQ (V : HSp D) (x : Matrix (Fin V.rank) (Fin r) D.host.E)
    (h : (gramQ V x).det ≠ 0) : x.rank = r := by
  refine le_antisymm (Matrix.rank_le_width x) ?_
  have h1 : (gramQ V x).rank = r := by
    have := Matrix.rank_of_isUnit (gramQ V x) ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h))
    simpa using this
  have h2 : gramQ V x = ((x.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose * HSpace.gram V) * x := by
    rw [gramQ, Matrix.mul_assoc]
  calc r = (gramQ V x).rank := h1.symm
    _ ≤ x.rank := by
      rw [h2]
      exact Matrix.rank_mul_le_right _ _

def fibreSum (V : HSp D) (φ : Mx D V.rank r → ℂ) (T : HermE D r) (h : GA D V) : ℂ :=
  ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // gramQ V x = T.1}, φ (GlobalTheory.SiegelFormula.invPt V h x.1)

def fibreMean (V : HSp D) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ) (T : HermE D r) : ℂ :=
  ⨍ q, descend (GQ V) (fibreSum V φ T) q ∂autMeasure V ν

def gramOf (V : HSp D) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E) : HermE D r :=
  ⟨gramQ V ξ, GlobalTheory.CompanionTheory.SplitGram.gramQ_herm V ξ⟩

def allEquiv (V : HSp D) (r : ℕ) :
    (Σ T : HermE D r, {x : Matrix (Fin V.rank) (Fin r) D.host.E // gramQ V x = T.1}) ≃
      Matrix (Fin V.rank) (Fin r) D.host.E where
  toFun p := p.2.1
  invFun x := ⟨gramOf V x, ⟨x, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨b, hb⟩, x, hg⟩
    change gramQ V x = b at hg
    subst hg
    rfl
  right_inv _ := rfl

theorem leftInv_fibreSum (V : HSp D) (φ : Mx D V.rank r → ℂ) (T : HermE D r) :
    LeftInv (GQ V) (fibreSum V φ T) :=
  GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V φ (fun x => gramQ V x = T.1)
    (fun _ hδ ξ h => (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h)

theorem hasSum_twist {V : HSp D} {θ : InfFam D} (hθ : IsInfFam θ) {ν : Measure (GA D V)} (hν : ν.IsHaarMeasure)
    {φ : Mx D V.rank r → ℂ} (hφ : φ ∈ schwartzA θ V.rank r) (habs : GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤)
    (u : HermE D r → ℂ) (hu : ∀ T, ‖u T‖ = 1) :
    HasSum (fun T => u T * fibreMean V ν φ T)
      (⨍ q, descend (GQ V) (fun h => ∑' ξ : Matrix (Fin V.rank) (Fin r) D.host.E,
        u (gramOf V ξ) * φ (GlobalTheory.SiegelFormula.invPt V h ξ)) q ∂autMeasure V ν) := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hν
  haveI := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  haveI : Countable (Matrix (Fin V.rank) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin r → D.host.E))
  have hcont : Continuous φ :=
    (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  have hab : (fun h => ∑' ξ : Matrix (Fin V.rank) (Fin r) D.host.E,
      ‖u (gramOf V ξ) * φ (GlobalTheory.SiegelFormula.invPt V h ξ)‖ₑ) = GlobalTheory.SiegelFormula.absTheta V φ := by
    funext h
    refine tsum_congr fun ξ => ?_
    rw [enorm_mul, ← ofReal_norm_eq_enorm (u _), hu]
    simp
  have hterm : ∀ (T : HermE D r) (k : {x : Matrix (Fin V.rank) (Fin r) D.host.E // gramQ V x = T.1}),
      gramOf V (allEquiv V r ⟨T, k⟩) = T := fun T k => Subtype.ext k.2
  have hfun : ∀ T : HermE D r, (fun h => ∑' k : {x : Matrix (Fin V.rank) (Fin r) D.host.E // gramQ V x = T.1},
      u (gramOf V (allEquiv V r ⟨T, k⟩)) * φ (GlobalTheory.SiegelFormula.invPt V h (allEquiv V r ⟨T, k⟩))) =
      fun h => u T * fibreSum V φ T h := by
    intro T
    funext h
    simp only [hterm]
    rw [fibreSum, tsum_mul_left]
    rfl
  have key := GlobalTheory.CompanionTheory.ThetaOrbit.hasSum_average_descend (Γ := GQ V) (μ := ν) (allEquiv V r)
    (fun h ξ => u (gramOf V ξ) * φ (GlobalTheory.SiegelFormula.invPt V h ξ))
    (fun ξ => (hcont.comp (GlobalTheory.AbsThetaSemi.continuous_invPt V ξ)).measurable.const_mul _)
    (by rw [hab]; exact GlobalTheory.SiegelFormula.leftInv_absTheta V φ)
    (fun T => by
      rw [hfun T]
      intro γ hγ h
      show u T * _ = u T * _
      rw [leftInv_fibreSum V φ T γ hγ h])
    (by rw [hab]; exact habs)
  have e : (fun T => u T * fibreMean V ν φ T) = fun T : HermE D r =>
      ⨍ q, descend (GQ V) (fun h => ∑' k : {x : Matrix (Fin V.rank) (Fin r) D.host.E // gramQ V x = T.1},
        u (gramOf V (allEquiv V r ⟨T, k⟩)) * φ (GlobalTheory.SiegelFormula.invPt V h (allEquiv V r ⟨T, k⟩))) q ∂autMeasure V ν := by
    funext T
    rw [hfun T]
    show _ = ⨍ q, u T * descend (GQ V) (fibreSum V φ T) q ∂autMeasure V ν
    simp only [fibreMean, average_eq, integral_const_mul, mul_smul_comm]
  rw [e]
  exact key

theorem fibreMean_eq_IfrB (V : HSp D) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ) (β : HermE D r)
    (hβ : β.1.det ≠ 0) : fibreMean V ν φ β = IfrB V ν φ β := by
  have h : fibreSum V φ β = fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
      φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D))) := by
    funext h
    let e : {x : Matrix (Fin V.rank) (Fin r) D.host.E // gramQ V x = β.1} ≃
        {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1} :=
      Equiv.subtypeEquivRight fun x => ⟨fun hx => ⟨rank_of_gramQ V x (by rw [hx]; exact hβ), hx⟩, And.right⟩
    exact e.tsum_eq (fun x => φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D))))
  unfold fibreMean IfrB
  rw [h]

theorem theta_mul_nb {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank r)} {ω : G D r →* Module.End ℂ (schwartzA θ V.rank r)} (hω : IsWeilSch ψ χ θ V μ ω)
    {nb : hermA D r → G D r} (hnb : IsNMap nb) (Φ : schwartzA θ V.rank r) (g : G D r) (b : hermA D r) (h : GA D V) :
    theta ω Φ (nb b * g) h = ∑' ξ : Matrix (Fin V.rank) (Fin r) D.host.E,
      pairH ψ (GlobalTheory.CompanionTheory.HermPoisson.ofHermE (gramOf V ξ)).1 b * (ω g Φ).1 (GlobalTheory.SiegelFormula.invPt V h ξ) := by
  refine tsum_congr fun ξ => ?_
  show (ω (nb b * g) Φ).1 (GlobalTheory.SiegelFormula.invPt V h ξ) = _
  rw [map_mul, Module.End.mul_apply, hω.unip (nb b) b.1 (hnb b), inner_invPt]
  congr 1
  unfold pairH trF
  rw [Matrix.trace_mul_comm]
  rfl

theorem continuous_pairH {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (S : hermA D r) :
    Continuous (pairH ψ S) := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  unfold pairH trF
  exact hψ.1.comp (continuous_const.mul (ht.comp
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace)))

theorem thetaCoef : GlobalTheory.Published.WeilThetaConvergence → PositivityTheory.PfSWUS.ThetaCoef := by
  classical
  intro hP D n V ψ χ θ μ ω H l s ν Φ hS hR nb lam 𝓖 hC β hβ g
  have hn : 1 ≤ n := by
    obtain ⟨h1, h2, -⟩ := hR
    omega
  have hψ := hS.hψ
  have hθ := hS.hθ
  have hν := hS.hν
  have hω := hS.hω
  have habs := hP D n V hn (Or.inr hR.2.2) θ hθ ν hν (ω g Φ)
  obtain ⟨hnb, hl⟩ := hC
  set A : HermE D n → ℂ := fibreMean V ν (ω g Φ).1 with hA
  have hsumA : Summable fun T => ‖A T‖ := by
    have h := (hasSum_twist hθ hν (ω g Φ).2 habs (fun _ => 1) (fun _ => norm_one)).summable
    simp only [one_mul] at h
    exact h.norm
  have hexp : ∀ b, HasSum (fun T => pairH ψ (GlobalTheory.CompanionTheory.HermPoisson.ofHermE T).1 b * A T)
      (thetaInt ω ν Φ (nb b * g)) := fun b => by
    have h := hasSum_twist hθ hν (ω g Φ).2 habs (fun T => pairH ψ (GlobalTheory.CompanionTheory.HermPoisson.ofHermE T).1 b)
      (fun T => hψ.2.1 _)
    have e : thetaInt ω ν Φ (nb b * g) = ⨍ q, descend (GQ V) (fun h => ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
        pairH ψ (GlobalTheory.CompanionTheory.HermPoisson.ofHermE (gramOf V ξ)).1 b * (ω g Φ).1 (GlobalTheory.SiegelFormula.invPt V h ξ)) q ∂autMeasure V ν := by
      have hth : theta ω Φ (nb b * g) = fun h => ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
          pairH ψ (GlobalTheory.CompanionTheory.HermPoisson.ofHermE (gramOf V ξ)).1 b * (ω g Φ).1 (GlobalTheory.SiegelFormula.invPt V h ξ) :=
        funext fun h => theta_mul_nb hω hnb Φ g b h
      rw [thetaInt, hth]
    rw [e]
    exact h
  set χβ : hermA D n → ℂ := fun b => (pairH ψ (GlobalTheory.CompanionTheory.HermPoisson.ofHermE β).1 b)⁻¹ with hχβ
  have hχ : ∀ b : hermA D n, ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) = χβ b := fun b => by
    rw [AddChar.map_neg_eq_inv]
    rfl
  have hpn : ∀ (S b : hermA D n), ‖pairH ψ S b‖ = 1 := fun S b => hψ.2.1 _
  have hχc : Continuous χβ :=
    (continuous_pairH hψ _).inv₀ (pairH_ne_zero hψ _)
  haveI : IsFiniteMeasure (lam.restrict 𝓖) :=
    ⟨by rw [Measure.restrict_apply_univ, hl.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
  set F : HermE D n → hermA D n → ℂ := fun T b => pairH ψ (GlobalTheory.CompanionTheory.HermPoisson.ofHermE T).1 b * A T * χβ b with hF
  have hFc : ∀ T, Continuous (F T) := fun T =>
    ((continuous_pairH hψ _).mul continuous_const).mul hχc
  have hFn : ∀ T b, ‖F T b‖ = ‖A T‖ := fun T b => by
    simp only [hF, hχβ, norm_mul, norm_inv, hpn, one_mul, inv_one, mul_one]
  have hvol : (lam.restrict 𝓖).real Set.univ = 1 := by
    rw [measureReal_def, Measure.restrict_apply_univ, hl.2.2]
    norm_num
  have hint : ∀ T, Integrable (F T) (lam.restrict 𝓖) := fun T =>
    Integrable.of_bound (hFc T).aestronglyMeasurable ‖A T‖ (Filter.Eventually.of_forall fun b => (hFn T b).le)
  have hsn : Summable fun T => ∫ b, ‖F T b‖ ∂(lam.restrict 𝓖) := by
    simp only [hFn, integral_const, hvol, one_smul]
    exact hsumA
  have key := hasSum_integral_of_summable_integral_norm hint hsn
  have hval : (fun T => ∫ b, F T b ∂(lam.restrict 𝓖)) = fun T => if T = β then A β else 0 := by
    funext T
    have e1 : ∀ b, F T b = pairH ψ (GlobalTheory.CompanionTheory.HermPoisson.ofHermE T).1 b *
        (pairH ψ (GlobalTheory.CompanionTheory.HermPoisson.ofHermE β).1 b)⁻¹ * A T := fun b => by
      simp only [hF, hχβ]
      ring
    simp only [e1, integral_mul_const]
    split_ifs with h
    · subst h
      have e2 : ∀ b, pairH ψ (GlobalTheory.CompanionTheory.HermPoisson.ofHermE T).1 b *
          (pairH ψ (GlobalTheory.CompanionTheory.HermPoisson.ofHermE T).1 b)⁻¹ = 1 := fun b => mul_inv_cancel₀ (pairH_ne_zero hψ _ _)
      simp only [e2, integral_const, hvol, one_smul, one_mul]
    · rw [setIntegral_pairH hψ hl h, zero_mul]
  rw [hval] at key
  have hfin := key.unique (hasSum_ite_eq β (A β))
  have hlhs : fc ψ lam 𝓖 nb (thetaInt ω ν Φ) β g = ∫ b, ∑' T, F T b ∂(lam.restrict 𝓖) := by
    unfold fc
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    show thetaInt ω ν Φ (nb b * g) * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) = ∑' T, F T b
    rw [hχ b]
    exact (((hexp b).mul_right (χβ b)).tsum_eq).symm
  rw [hlhs, hfin, hA]
  exact fibreMean_eq_IfrB V ν _ β hβ

end GlobalTheory.CompanionTheory.ThetaCoefND

end
