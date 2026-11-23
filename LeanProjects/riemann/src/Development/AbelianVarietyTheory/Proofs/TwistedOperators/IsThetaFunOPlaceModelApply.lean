import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PositionOneOfUnique
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchrodingerIntertwinerInjectiveSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceHalfHeisenbergInvariantForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocFrame
open GlobalTheory.EmbChart (idem)
open GlobalTheory.StepData (LatFrame)
open GlobalTheory.RootEx (colE rowE)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (schT schM)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.PlaceThetaVal
open GlobalTheory.PlaceVec GlobalTheory.PlaceModel GlobalTheory.AdelicLatMove

theorem isThetaFunO_placeModel_apply : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) → ∀ (A B : HSp D)
    (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛB : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC B ΛB → ∀ (e : AE D) (f₀ Φ : WO A B → ℂ) (Tm : (WO A B → ℂ) →ₗ[ℂ] (WO A B → ℂ)),
    e * e = e → infPart D e = 0 →
    IsPlaceModel ψ (symplO A B) (heisO ψ A B) e (latO A B (ΛA : Set (Fin A.rank → D.host.E)) (ΛB : Set (Fin B.rank → D.host.E)) fun _ => True) 1 f₀ Tm →
    IsThetaFunO ψ A B f₀ →
    IsSBHalf e (latO A B (ΛA : Set (Fin A.rank → D.host.E)) (ΛB : Set (Fin B.rank → D.host.E)) fun _ => True) Φ →
    IsThetaFunO ψ A B (Tm Φ) := by
  intro D ψ hψ S T ΛS ΛT hS hT a f₀ Φ Tm ha hinf h₁ hf₀ hΦ
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have hmul := exists_nsmul_mem_latO hS.1 hT.1
  have hsm : ∀ {b : AE D}, b * b = b → ∀ u ∈ (latO S T ΛS ΛT fun _ => True),
      b • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T b := fun {b} hb u hu =>
    ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hb])) u hu,
      (mem_half S T).2 (by rw [smul_smul, hb])⟩
  generalize (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) = Λ at *
  have ha' : cA D a * cA D a = cA D a := by rw [← RingHom.map_mul, ha]
  have hb := isBichar_symplO S T ψ
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk x y hxy => by
    rw [← inv_smul_nsmul S T hk x, ← inv_smul_nsmul S T hk y]
    exact congrArg _ hxy
  have hLL' : ∀ u ∈ Λ ⊓ half S T a, ∀ y ∈ Λ, ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (half_infPart hinf hu.2)).1 hu.1 y hy
  have hmem := mem_waveSpan (X := half S T a) (Y := half S T (cA D a)) (L := Λ ⊓ half S T a)
    (L' := Λ ⊓ half S T (cA D a)) hb inf_le_right inf_le_right (fun u hu y hy => hLL' u hu y hy.1)
    (fun x hx h => ⟨(hdual x (half_infPart hinf hx)).2 fun u hu => by
      have := h _ (hsm ha' u hu)
      rwa [← symplO_smul, (mem_half S T).1 hx] at this, hx⟩)
    (half_div S T a) (half_div S T _) tf (fun k hk => by
      obtain ⟨R, hR, h⟩ := hfin k hk
      refine ⟨(fun r => a • r) '' R, hR.image _, fun t ht => ?_⟩
      obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
      refine ⟨_, ⟨r, hr, rfl⟩, a • u, hsm ha u hu, ?_⟩
      have := (mem_half S T).1 ht.2
      rw [← this, htr, smul_add, smul_comm a k u])
    Φ (fun t ht => (isHalf_iff S T).1 (hΦ.1 t ht)) _ hΦ.2.choose_spec.1
      (fun u hu => hΦ.2.choose_spec.2.1 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨hΦ.2.choose_spec.2.2 t ht, (half S T a).nsmul_mem ((isHalf_iff S T).1 (hΦ.1 t ht)) _⟩
  let P : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {g | IsThetaFunO ψ S T (Tm g)}
      add_mem' := fun {g g'} hg hg' => by
        show IsThetaFunO ψ S T (Tm (g + g'))
        rw [map_add]; exact GlobalTheory.OrientedHeis.theta_add hg hg'
      zero_mem' := by
        show IsThetaFunO ψ S T (Tm 0)
        rw [map_zero]; exact GlobalTheory.OrientedHeis.theta_zero
      smul_mem' := fun c g hg => by
        show IsThetaFunO ψ S T (Tm (c • g))
        rw [map_smul]; exact GlobalTheory.OrientedHeis.theta_smul c hg }
  have hsub : waveSpan (fun x y => ψ (symplO S T x y)) (half S T a) (half S T (cA D a)) (Λ ⊓ half S T a) ≤ P := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have hSB : IsSBHalf a Λ fun t => ψ (symplO S T t y) * halfInd a Λ t := by
      obtain ⟨k, hk, hky⟩ := hmul y (half_infPart (infPart_cA hinf) hy)
      have hne : ∀ t, ψ (symplO S T t y) * halfInd a Λ t ≠ 0 → t ∈ Λ ⊓ half S T a := fun t ht => by
        by_contra hn
        rw [halfInd_eq_ind, ind, if_neg hn, mul_zero] at ht
        exact ht rfl
      refine ⟨fun t ht => (isHalf_iff S T).2 (hne t ht).2, k, hk, fun u hu hu' t => ?_,
        fun t ht => nsmul_mem (hne t ht).1 k⟩
      have hu'' : u ∈ Λ ⊓ half S T a := ⟨hu, (isHalf_iff S T).1 hu'⟩
      have e1 := hb.left t (k • u) y
      have e2 := hb.nsmul k u y
      beta_reduce at e1 e2 ⊢
      rw [e1, e2, hLL' u hu'' _ hky, mul_one, halfInd_eq_ind, ind_add _ _ (nsmul_mem hu'' k)]
    have key : Tm (wave (fun x y => ψ (symplO S T x y)) (Λ ⊓ half S T a) x y) = heisO ψ S T x (heisO ψ S T y f₀) := by
      have e1 := h₁.trans _ hSB x ((isHalf_iff S T).2 hx)
      have e2 := h₁.modul _ (GlobalTheory.isSBHalf_halfInd a Λ) y ((isHalf_iff S T).2 hy)
      have e3 := h₁.vac
      rw [one_smul] at e3
      rw [e2, e3, halfInd_eq_ind] at e1
      exact e1
    show IsThetaFunO ψ S T (Tm _)
    rw [key]
    exact GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀ y) x
  exact hsub hmem

end GlobalTheory.PlaceThetaVal
