import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ConjAdjWeil

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.PairLift

variable {D : D7}

theorem dagger_eq (S T : HSp D) (x : WO S T) : dagger S T x = adjO T S x := by
  simp only [dagger, adjO, giA, gA, adj, Matrix.mul_assoc]
  rfl

theorem cj_dagger (S T : HSp D) (f : WO S T → ℂ) : cj (dagger T S) f = dag S T f := by
  funext y; simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dag, dagger_eq]

theorem conjAdjoint_apply {S T : HSp D} (om : Rep S T) (g : GA D T) (h : GA D S) (f : WO T S → ℂ) :
    conjAdjoint om (g, h) f = dag S T (om (h, g) (dag T S f)) := by
  show cj (dagger T S) (om (h, g) (cj (dagger S T) f)) = _
  rw [cj_dagger, cj_dagger]

theorem chi_conj {χ : (AE D)ˣ →* Circle} {n : ℕ} (hR : ResEta D χ n) (y : (AE D)ˣ) :
    χ (Units.map (cA D).toMonoidHom y) = (χ y)⁻¹ := by
  obtain ⟨⟨η, hη⟩, hall⟩ := hR
  have hprod : y * Units.map (cA D).toMonoidHom y =
      idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) y) := by
    apply Units.ext
    rw [GlobalTheory.Mem.EtaTilde.idF_norm]
    rfl
  have h1 : χ y * χ (Units.map (cA D).toMonoidHom y) = 1 := by
    rw [← map_mul, hprod, hall η hη, hη.2.2.1, one_pow]
  exact eq_inv_of_mul_eq_one_right h1

theorem isSplitIdem_conj {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hε, by rw [cA_cA, add_comm, h3]⟩

theorem suppAt_conj {e : AE D} {V : HSp D} {g : GA D V} (h : SuppAt e V g) : SuppAt (cA D e) V g := by
  intro i j
  rw [cA_cA, add_comm]
  exact h i j

theorem det_inv_eq (V : HSp D) (g : GA D V) : (mt V g⁻¹).det = cA D (mt V g).det := by
  have h1 : (giA V).det * (gA V).det = 1 := by rw [← Matrix.det_mul, giA_mul_gA, Matrix.det_one]
  rw [mt_inv, Matrix.det_mul, Matrix.det_mul, adj, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
  linear_combination ((mt V g).map (cA D)).det * h1

theorem isDetAt_conj {e : AE D} (he : e * e = e) {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (hx : IsDetAt e V g x) :
    IsDetAt (cA D e) V g (Units.map (cA D).toMonoidHom x⁻¹) := by
  have hd : (mt V g⁻¹).det * (mt V g).det = 1 := by rw [← Matrix.det_mul, mt_inv_mul, Matrix.det_one]
  have hz : ((x⁻¹ : (AE D)ˣ) : AE D) = e * (mt V g⁻¹).det + (1 - e) := by
    apply Units.inv_eq_of_mul_eq_one_left
    rw [hx]
    linear_combination e * hd + ((mt V g⁻¹).det * (mt V g).det - (mt V g⁻¹).det - (mt V g).det + 1) * he
  show cA D ((x⁻¹ : (AE D)ˣ) : AE D) = cA D e * (mt V g).det + (1 - cA D e)
  rw [hz, map_add, map_mul, map_sub, map_one, det_inv_eq, cA_cA]

end GlobalTheory.ConjAdjWeil

namespace GlobalTheory.ConjAdjWeil

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.PairLift

theorem isWeilDatumO_conjAdjoint : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ T S χT χS (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint om) := by
  intro D ψ S T χS χT om hw
  have hS : AdjLaw ψ S T := GlobalTheory.AdjLawPf.adjLaw D ψ hw.std S T
  have hT : AdjLaw ψ T S := GlobalTheory.AdjLawPf.adjLaw D ψ hw.std T S
  have thB : ∀ f : WO T S → ℂ, IsThetaFunO ψ T S f → IsThetaFunO ψ S T (dag T S f) := hT.theta
  have thA : ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ T S (dag S T f) := hS.theta
  have key : ∀ (g : GA D T) (h : GA D S) (f : WO T S → ℂ),
      conjAdjoint om (g, h) f = dag S T (om (h, g) (dag T S f)) := fun g h f => conjAdjoint_apply om g h f
  have dd : ∀ f : WO T S → ℂ, dag S T (dag T S f) = f := fun f => by
    funext y; simp only [dag, hT.invol, Complex.conj_conj]
  have d0 : adjO S T 0 = 0 := by
    have := hS.add 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  have d0' : adjO T S 0 = 0 := by
    have := hT.add 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  refine ⟨hw.std, hw.hecT, hw.hecS, hw.resT, hw.resS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨g, h⟩ f hf
    rw [key]
    exact thA _ (hw.om_pres _ _ (thB f hf))
  · intro g h w₀ f hf
    have e1 : dag T S (heisO ψ T S w₀ f) = heisO ψ S T (adjO S T w₀) (dag T S f) := by
      rw [hT.Heisenberg₂, hT.invol]
    rw [key, key, e1, hw.om_heis _ _ _ _ (thB f hf), ← hS.act, ← hS.Heisenberg₂]
  · intro γ hγ γ' hγ' f hf
    rw [key]
    have := hw.om_aut γ' hγ' γ hγ (dag T S f) (thB f hf)
    simp only [dag] at this ⊢
    rw [d0, this, d0', Complex.conj_conj]
  · intro f hf w
    have e : (fun p : GA D T × GA D S => conjAdjoint om p f w) =
        fun p => starRingEnd ℂ (om (Prod.swap p) (dag T S f) (adjO S T w)) := by
      funext p
      obtain ⟨g, h⟩ := p
      rw [key]
      rfl
    rw [e]
    exact Complex.continuous_conj.comp ((hw.om_cont _ (thB f hf) _).comp continuous_swap)
  · intro μ 𝓕 hμ h𝓕 p f hf
    obtain ⟨g, h⟩ := p
    haveI : BorelSpace (WO S T) := ⟨rfl⟩
    haveI : BorelSpace (WO T S) := ⟨rfl⟩
    let dE : WO T S ≃+ WO S T :=
      { toFun := adjO S T, invFun := adjO T S, left_inv := hT.invol, right_inv := hS.invol, map_add' := hS.add }
    let hE : WO S T ≃ₜ WO T S :=
      { toFun := adjO T S, invFun := adjO S T, left_inv := hS.invol, right_inv := hT.invol,
        continuous_toFun := hT.cont, continuous_invFun := hS.cont }
    set ν : Measure (WO S T) := μ.map dE with hν
    have hνH : ν.IsAddHaarMeasure := dE.isAddHaarMeasure_map μ hS.cont hT.cont
    have hfm : Measurable (adjO T S) := hT.cont.measurable
    have hdm : Measurable (adjO S T) := hS.cont.measurable
    have hmp : MeasurePreserving (adjO T S) ν μ := by
      refine ⟨hfm, ?_⟩
      rw [hν, Measure.map_map hfm (show Measurable dE from hdm)]
      have : adjO T S ∘ dE = id := funext fun w => hT.invol w
      rw [this, Measure.map_id]
    have hemb : MeasurableEmbedding (adjO T S) := hE.measurableEmbedding
    have hfd : IsAddFundamentalDomain (ratL T S) (adjO T S ⁻¹' 𝓕) ν := by
      refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving
        (e := fun γ : ratL S T => (⟨adjO S T γ, (hS.rat γ).2 γ.2⟩ : ratL T S)) ⟨?_, ?_⟩ ?_
      · intro a b hab
        have := congrArg (fun z : ratL T S => adjO T S (z : WO S T)) hab
        simp only [hT.invol] at this
        exact Subtype.ext this
      · intro b
        refine ⟨⟨adjO T S b, (hT.rat b).2 b.2⟩, Subtype.ext ?_⟩
        exact hS.invol b
      · intro γ x
        show adjO T S (adjO S T (γ : WO T S) + x) = (γ : WO T S) + adjO T S x
        rw [hT.add, hT.invol]
    calc ∫⁻ w in 𝓕, ‖conjAdjoint om (g, h) f w‖ₑ ^ 2 ∂μ
        = ∫⁻ w in 𝓕, (fun z => ‖om (h, g) (dag T S f) z‖ₑ ^ 2) (adjO S T w) ∂μ := by
          congr 1
          funext w
          rw [key]
          simp [dag]
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, (fun z => ‖om (h, g) (dag T S f) z‖ₑ ^ 2) (adjO S T (adjO T S z)) ∂ν :=
          (hmp.setLIntegral_comp_preimage_emb hemb (fun w => (fun z => ‖om (h, g) (dag T S f) z‖ₑ ^ 2) (adjO S T w)) 𝓕).symm
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, ‖om (h, g) (dag T S f) z‖ₑ ^ 2 ∂ν := by simp only [hS.invol]
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, ‖dag T S f z‖ₑ ^ 2 ∂ν := hw.om_unit ν _ hνH hfd (h, g) _ (thB f hf)
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, (fun w => ‖f w‖ₑ ^ 2) (adjO T S z) ∂ν := by
          congr 1
          funext z
          simp [dag]
      _ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := hmp.setLIntegral_comp_preimage_emb hemb (fun w => ‖f w‖ₑ ^ 2) 𝓕
  · intro e he g h hsg hsh x y hx hy
    obtain ⟨r, hr, hℓ⟩ := hw.om_split (cA D e) (isSplitIdem_conj he) h g (suppAt_conj hsh) (suppAt_conj hsg) _ _
      (isDetAt_conj he.1 hy) (isDetAt_conj he.1 hx)
    refine ⟨r, hr, fun ℓ hinv f hf => ?_⟩
    have dadd : ∀ a b : WO S T → ℂ, dag S T (a + b) = dag S T a + dag S T b := fun a b => by
      funext z; simp [dag]
    have dsmul : ∀ (c : ℂ) (a : WO S T → ℂ), dag S T (c • a) = starRingEnd ℂ c • dag S T a := fun c a => by
      funext z; simp [dag]
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun F => starRingEnd ℂ (ℓ (dag S T F))
        map_add' := fun a b => by simp only [dadd, map_add]
        map_smul' := fun c a => by
          simp only [dsmul, map_smul, smul_eq_mul, map_mul, RingHom.id_apply, Complex.conj_conj] }
    have hinv' : ∀ u : WO S T, (∀ i j, cA D (cA D e) * u i j = u i j) → ∀ F, IsThetaFunO ψ S T F →
        ℓ' (heisO ψ S T u F) = ℓ' F := by
      intro u hu F hF
      have hu' : IsHalf e u := fun i j => by have := hu i j; rwa [cA_cA] at this
      have e2 : dag S T (heisO ψ S T u F) = heisO ψ T S (adjO T S u) (dag S T F) := by rw [hS.Heisenberg₂, hS.invol]
      show starRingEnd ℂ (ℓ (dag S T (heisO ψ S T u F))) = starRingEnd ℂ (ℓ (dag S T F))
      rw [e2, hinv _ (hT.half e u hu') _ (thA F hF)]
    have main := hℓ ℓ' hinv' (dag T S f) (thB f hf)
    have m2 : starRingEnd ℂ (ℓ (dag S T (om (h, g) (dag T S f)))) =
        (r : ℂ) * (splitFacO χS χT (Units.map (cA D).toMonoidHom y⁻¹) (Units.map (cA D).toMonoidHom x⁻¹) : ℂ) *
          starRingEnd ℂ (ℓ f) := by
      have := main
      simp only [ℓ', LinearMap.coe_mk, AddHom.coe_mk, dd] at this
      exact this
    have hconj := congrArg (starRingEnd ℂ) m2
    rw [Complex.conj_conj] at hconj
    have hfac : (splitFacO χS χT (Units.map (cA D).toMonoidHom y⁻¹) (Units.map (cA D).toMonoidHom x⁻¹))⁻¹ =
        splitFacO χT χS x y := by
      unfold splitFacO
      rw [chi_conj hw.resT, chi_conj hw.resS, map_inv, map_inv, inv_inv, inv_inv, _root_.mul_inv_rev, inv_inv]
    rw [key, hconj, map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal, ← Circle.coe_inv_eq_conj, hfac]

end GlobalTheory.ConjAdjWeil
