import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumPureMemAlgD
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKerCpt

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.RealActs Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

private theorem hecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

private theorem resEta_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

private def indMap {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (π : U →ₗ[ℂ] V)
    (hπ : Function.Surjective π) (D : U →ₗ[ℂ] U) (hD : ∀ u, π u = 0 → π (D u) = 0) : V →ₗ[ℂ] V :=
  (π.quotKerEquivOfSurjective hπ).toLinearMap ∘ₗ (LinearMap.ker π).mapQ (LinearMap.ker π) D (fun u hu => hD u hu) ∘ₗ
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap

private theorem indMap_apply {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (π : U →ₗ[ℂ] V)
    (hπ : Function.Surjective π) (D : U →ₗ[ℂ] U) (hD : ∀ u, π u = 0 → π (D u) = 0) (u : U) :
    indMap π hπ D hD (π u) = π (D u) := by
  have e : (π.quotKerEquivOfSurjective hπ).symm (π u) = Submodule.Quotient.mk u := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [indMap, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e, Submodule.mapQ_apply]
  rfl

private theorem acts_zero' {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) ⇑T ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e, map_zero]

theorem polZero_cpt : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W Bs.emb, ∀ Φ, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (1, k) Φ) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM k hk Φ hZ
  obtain ⟨T, hT, m, f, φ, hf, rfl, hz⟩ := hZ
  have hTr := hM.triple
  have hPV : IsPair Bs G.M Xc.β (Xc.β / Xc.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨hTr.base, hTr.geo.hV, hTr.geo.hW, hTr.geo.hM, hTr.chars.heckeβ,
      hecke_div hTr.chars.heckeβ hTr.chars.heckeα, hTr.chars.resβ,
      resEta_div hTr.chars.resβ hTr.chars.resα rfl, hTr.weil⟩
  have actV := GlobalTheory.T.polynomial_datum_action_of_pair hP F E σ Bs a (a + a') G.V G.W G.M _ _ om _ _ _ _ hPV
  obtain ⟨D, hDm, hDi⟩ := actV.2.2.2 k hk
  have hA : ∀ g ∈ G.M.Pol Bs.ψ Bs.emb, Acts (evI F) (⇑(om (1, k))) (⇑g) (⇑(D g)) := fun g hg =>
    (hDi g hg (D g)).2 rfl

  have hpure : ∀ i, om (1, k) (pure (f i) (φ i)) = pure (D (f i)) (φ i) := by
    intro i
    have hstd : ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [T.finite_toSet.compl_mem_cofinite, hTr.geo.hM.std] with v hv hv'
      rw [(hf i).2.2 v hv, hv']
    exact hA (f i) (hf i).1 _ (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hf i).2.1 hstd)

  let N := G.M.Pol Bs.ψ Bs.emb
  let π : N →ₗ[ℂ] R.Pi := R.p ∘ₗ N.subtype
  have hπ : Function.Surjective π := fun y => by
    have : y ∈ N.map R.p := hM.real.quot.onto ▸ Submodule.mem_top
    obtain ⟨g, hg, e⟩ := Submodule.mem_map.1 this
    exact ⟨⟨g, hg⟩, e⟩
  have ker0 : ∀ u : N, π u = 0 → π ((D.restrict hDm) u) = 0 := by
    intro u hu
    have := hM.real.cpt k hk u.1 u.2 0 (zero_mem _) (D u.1) 0 (hA u.1 u.2) (acts_zero' _)
      (by rw [map_zero]; exact hu)
    rw [map_zero] at this
    exact this
  let ρ := indMap π hπ (D.restrict hDm) ker0
  have hρ : ∀ i, R.p (D (f i)) = ρ (R.p (f i)) := fun i =>
    (indMap_apply π hπ (D.restrict hDm) ker0 ⟨f i, (hf i).1⟩).symm
  refine ⟨T, hT, m, fun i => D (f i), φ, fun i => ⟨hDm _ (hf i).1, (hf i).2⟩, ?_, ?_⟩
  · rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hpure i
  · have := congrArg (LinearMap.rTensor _ ρ) hz
    rw [map_sum, map_zero] at this
    simpa only [LinearMap.rTensor_tmul, hρ] using this

end GlobalTheory.PolKerCpt

end
