import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.GenUniq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}

theorem rows_indep {A K : Type} [CommRing A] [Field K] (φ : A →+* K) {n g : ℕ} (h U : Fin n → Fin g → A)
    (hu : IsUnit (pairDet h U)) (a : Fin n → K) (ha : ∀ b, ∑ i, a i * φ (U i b) = 0) : a = 0 := by
  by_contra ha0
  let M : Matrix (Fin n) (Fin n) K := fun k k' => ∑ b, φ (h k' b) * φ (U k b)
  have hM : φ (pairDet h U) = M.det := by
    rw [pairDet, RingHom.map_det]
    congr 1
    ext k k'
    simp [M, map_sum, map_mul]
  have hdet : M.det = 0 := by
    refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨a, ha0, ?_⟩
    ext k'
    simp only [Matrix.vecMul, dotProduct, M, Pi.zero_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    calc ∑ k, a k * (φ (h k' b) * φ (U k b)) = φ (h k' b) * ∑ k, a k * φ (U k b) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := by rw [ha b, mul_zero]
  exact (hu.map φ).ne_zero (hM.trans hdet)

theorem rows_data (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) {A K : Type} [CommRing A] [Field K] [Algebra c.F K]
    (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A) (φ : A →+* K) {g : ℕ} (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left))
    (hbas : IsTanBasis Y.t ξ e) (yy : Sp K ⟶ Xo'.XF c') (hyy : yy ≫ Y.j = spMap φ ≫ ξ) (y : FrPt Xo c K)
    (hyx : yy ≫ r ≫ pullback.fst _ _ = y.x) (ρ : E →+* ℂ) (U : Fin (Dw.mult ρ) → Fin g → A)
    (heig : EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W ρ))) (bcV Y.t φ e) (fun k b => φ (U k b)))
    (hσ : ∀ a, φ (β (embV c' W ρ a)) = algebraMap c.F K (embK c ρ a)) :
    ∃ (w : Fin (Dw.mult ρ) → (Sp (DualNumber K) ⟶ Y.oF.t.G.left)) (G : Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) K),
      (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t φ e) (fun b => φ (U i b)) (w i ≫ Y.m.φ)) ∧
      (∀ i, IsCombAt y.x (y.u ρ) (G i) (w i ≫ ν.φ)) ∧
      (∀ h : Fin (Dw.mult ρ) → Fin g → A, IsUnit (pairDet h U) → G.det ≠ 0) := by
  have hb := isTanBasis_bc hbas φ
  let Eb : Fin g → PullbackSections.TanM (spMap φ ≫ ξ) Y.t.G := fun b => GlobalTheory.LieMet.tanOf (hb.1 b)
  let C : Fin (Dw.mult ρ) → PullbackSections.TanM (spMap φ ≫ ξ) Y.t.G := fun i => ∑ b, φ (U i b) • Eb b
  let Pm := GlobalTheory.LieMet.pushE Y.m yy hyy
  let Pν := GlobalTheory.LieMet.pushE ν yy hyx
  let N : Fin (Dw.mult ρ) → PullbackSections.TanM y.x Xo.univ.t.G := fun i => Pν (Pm.symm (C i))
  have hCc : ∀ i, IsCombAtG Y.t (spMap φ ≫ ξ) (bcV Y.t φ e) (fun b => φ (U i b)) (PullbackSections.tv (C i)).left :=
    fun i => (GlobalTheory.LieMet.isComb_iff Eb _ (C i)).2 rfl
  have hsm : ∀ (a : K) (v : PullbackSections.TanM (spMap φ ≫ ξ) Y.t.G), (PullbackSections.tv (a • v)).left = spMap (epsMul a) ≫ (PullbackSections.tv v).left :=
    fun _ _ => rfl
  have hact : ∀ (a : 𝓞 E) (v : PullbackSections.TanM (spMap φ ≫ ξ) Y.t.G),
      (PullbackSections.tv (PullbackSections.actR Y.t.act a v)).left = (PullbackSections.tv v).left ≫ (Y.t.act.act a).left := fun _ _ => rfl

  have hCe : ∀ i (a : 𝓞 E), PullbackSections.actR Y.t.act a (C i) = φ (β (embV c' W ρ a)) • C i := fun i a =>
    GlobalTheory.LieMet.tan_ext (by rw [hact, hsm]; exact heig i _ (hCc i) a)
  have hNe : ∀ i (a : 𝓞 E), PullbackSections.actR Xo.univ.t.act a (N i) = φ (β (embV c' W ρ a)) • N i := by
    intro i a
    have h1 : PullbackSections.actR Y.oF.t.act a (Pm.symm (C i)) = φ (β (embV c' W ρ a)) • Pm.symm (C i) := by
      apply Pm.injective
      refine (GlobalTheory.LieMet.pushE_act Y.m yy hyy a _).trans ?_
      rw [map_smul]
      simp only [Pm, LinearEquiv.apply_symm_apply]
      exact hCe i a
    show PullbackSections.actR Xo.univ.t.act a (Pν (Pm.symm (C i))) = _
    refine (GlobalTheory.LieMet.pushE_act ν yy hyx a _).symm.trans ?_
    show Pν _ = _
    rw [h1, map_smul]
  have hN : ∀ i, ∃! a, IsCombAt y.x (y.u ρ) a (PullbackSections.tv (N i)).left := fun i =>
    y.basis ρ _ (GlobalTheory.LieMet.isTan_tv (N i)) fun a => by
      rw [← hσ]
      exact congrArg (fun v => (PullbackSections.tv v).left) (hNe i a)
  choose G hG using fun i => (hN i).exists
  refine ⟨fun i => (PullbackSections.tv (Pm.symm (C i))).left, G, fun i => ?_, fun i => ?_, fun h hu hd => ?_⟩
  · rw [hyy, ← GlobalTheory.LieMet.left_pushE Y.m yy hyy, LinearEquiv.apply_symm_apply]
    exact hCc i
  · rw [← GlobalTheory.LieMet.left_pushE ν yy hyx]
    exact hG i
  · obtain ⟨a, ha0, ha⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    let Ub : Fin (Dw.mult ρ) → PullbackSections.TanM y.x Xo.univ.t.G := fun j => GlobalTheory.LieMet.tanOf (y.tan ρ j)
    have hNi : ∀ i, N i = ∑ j, G i j • Ub j := fun i => (GlobalTheory.LieMet.isComb_iff Ub (G i) (N i)).1 (hG i)
    have h0 : ∑ i, a i • N i = 0 := by
      simp only [hNi, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := congrFun ha j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
      rw [this, zero_smul]
    have h1 : ∑ i, a i • C i = 0 := by
      have : Pν (Pm.symm (∑ i, a i • C i)) = 0 := by
        rw [← h0]; simp only [map_sum, map_smul]; rfl
      exact Pm.symm.injective (Pν.injective (this.trans ((congrArg Pν (map_zero Pm.symm)).trans (map_zero Pν)).symm))
    let cv : Fin g → K := fun b => ∑ i, a i * φ (U i b)
    have h2 : ∑ i, a i • C i = ∑ b, cv b • Eb b := by
      simp only [C, cv, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have h3 : cv = 0 := by
      have hz := (GlobalTheory.LieMet.isComb_iff Eb cv 0).2 (h2.symm.trans h1).symm
      have hz' := (GlobalTheory.LieMet.isComb_iff Eb 0 0).2 (by simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero])
      exact (hbas.2 K φ _ (GlobalTheory.LieMet.isTan_tv 0)).unique hz hz'
    exact ha0 (rows_indep φ h U hu a fun b => congrFun h3 b)

end GlobalTheory.FlatModel.GenUniq

namespace GlobalTheory.FlatModel

theorem secValAt_unique_generic : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∃ (k : Type) (_ : Field k) (φ : A →+* k), Function.Injective φ ∧ ∀ v v', SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k φ v → SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k φ v' → v = v' := by
  intro _ _ _ E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x _ Z τ s la p Xw hp hcov A _ _ _ ξ β _ hξs _ hξX g e U₁
    h₁ U₂ h₂ hbas heig hu₁ hu₂
  let K := FractionRing A
  let φ : A →+* K := algebraMap A K
  refine ⟨K, inferInstance, φ, IsFractionRing.injective A K, fun v v' hv hv' => ?_⟩
  have hsc : ∀ {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂) (f' : R₂ →+* R₃),
      spMap (f'.comp f) = spMap f' ≫ spMap f := fun f f' => by
    rw [spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hinj : ∀ {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (f f' : R₁ →+* R₂), spMap f = spMap f' → f = f' :=
    fun f f' h => congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h)
  have hj : IsOpenImmersion Y.j := GlobalTheory.LocM.BaseMdl.isOpenImmersion_j hp hcov.2.2.1 Y
  have hrange : Set.range (spMap φ ≫ ξ) ⊆ Set.range Y.j := by
    rintro _ ⟨z, rfl⟩
    refine hcov.2.2.2.2.1 ?_
    have hz : (spMap φ).base z = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) := by
      refine PrimeSpectrum.ext ?_
      show Ideal.comap φ (z : PrimeSpectrum K).asIdeal = ⊥
      haveI := (z : PrimeSpectrum K).isPrime
      rw [Ideal.eq_bot_of_prime (z : PrimeSpectrum K).asIdeal, ← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective A K)
    show ξ.base ((spMap φ).base z) ∈ Xw
    rw [hz]
    exact hξX
  let yy := IsOpenImmersion.lift Y.j (spMap φ ≫ ξ) hrange
  have hyy : yy ≫ Y.j = spMap φ ≫ ξ := IsOpenImmersion.lift_fac _ _ _
  let ψ : c'.F →+* K := (Spec.preimage (yy ≫ pullback.snd _ _)).hom
  have hψ : spMap ψ = yy ≫ pullback.snd _ _ := Spec.map_preimage _
  letI : Algebra c.F K := (ψ.comp (IntermediateField.inclusion hle).toRingHom).toAlgebra
  have hψβ : ψ.comp (c'.V W).subtype = φ.comp β := by
    refine hinj _ _ ?_
    rw [hsc, hsc, hψ, Category.assoc, ← GlobalTheory.LocM.BaseMdl.j_s, ← Category.assoc, hyy, Category.assoc, hξs]
  have hsnd : yy ≫ r ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    rw [hcov.1, ← Category.assoc, ← hψ]
    exact (hsc _ _).symm
  have hx : (yy ≫ r ≫ pullback.fst _ _) ≫ Xo.s = sOf c K := by
    rw [sOf, hsc, ← hsnd]
    simp only [Category.assoc, pullback.condition]
  obtain ⟨y, hyx⟩ := GlobalTheory.NonIntegralFrameExample.exists_framed (yy ≫ r ≫ pullback.fst _ _) hx
  have hT : Tested y := GlobalTheory.NonIntegralFrameExample.spread_holds Xo c K y
  have hpt : GlobalTheory.AllWt.ptF y = yy ≫ r := by
    unfold GlobalTheory.AllWt.ptF
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hyx, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc, hsnd]
  have hσ : ∀ (ρ : E →+* ℂ) (a : 𝓞 E), φ (β (embV c' W ρ a)) = algebraMap c.F K (embK c ρ a) := by
    intro ρ a
    rw [← RingHom.comp_apply φ β, ← hψβ]
    show ψ ((embV c' W ρ a : c'.V W) : c'.F) = ψ (IntermediateField.inclusion hle (embK c ρ a))
    congr 1
  obtain ⟨w₁, G₁, hw₁, hg₁, hd₁⟩ :=
    GenUniq.rows_data Y r ν ξ β φ e hbas yy hyy y hyx.symm τ.1 U₁ (heig K φ).1 (hσ τ.1)
  obtain ⟨w₂, G₂, hw₂, hg₂, -⟩ :=
    GenUniq.rows_data Y r ν ξ β φ e hbas yy hyy y hyx.symm (conjEmb τ.1) U₂ (heig K φ).2 (hσ _)
  have e₁ := hv inferInstance yy hyy y hT hpt w₁ w₂ G₁ G₂ hw₁ hw₂ hg₁ hg₂
  have e₂ := hv' inferInstance yy hyy y hT hpt w₁ w₂ G₁ G₂ hw₁ hw₂ hg₁ hg₂
  exact mul_right_cancel₀ (hd₁ h₁ hu₁) (e₁.trans e₂.symm)

end GlobalTheory.FlatModel

end
