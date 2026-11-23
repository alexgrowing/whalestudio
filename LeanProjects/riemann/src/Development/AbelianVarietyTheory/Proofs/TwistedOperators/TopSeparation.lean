import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactMeetsBesselTopRationalOrbitsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneAdditiveBoundedCompactStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneSimultaneousRightTranslateStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneRightTranslateUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbRelAtRealPlaceOfUnitaryEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AtRealPlaceMemUnipotentFlagAdelicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

noncomputable section

namespace GlobalTheory.SepRows.SepProof

section
open Classical

theorem atTau_mem_GinfC' {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    atTau θ V τ g ∈ GinfC V := by
  unfold atTau; split_ifs with h
  exacts [h.choose_spec.1, one_mem _]

theorem pairVec_comp_rho {D : D7} {V : HSp D} (c : CoefA V) (ξ : Module.Dual ℂ c.W) (Ψ : Bridge.Gf V → c.W) {a : GA D V}
    (ha : a ∈ GinfC V) : pairVec c (ξ ∘ₗ c.ρ a⁻¹) Ψ = rTr V a (pairVec c ξ Ψ) := by
  funext h
  have e : (finHom V).rangeRestrict (h * a) = (finHom V).rangeRestrict h := by
    rw [map_mul]
    have : (finHom V).rangeRestrict a = 1 := Subtype.ext (MonoidHom.mem_ker.1 ha)
    rw [this, mul_one]
  simp only [rTr, pairVec_apply, e, mul_inv_rev, map_mul, LinearMap.comp_apply, Module.End.mul_apply]

theorem mult_equiv {D : D7} (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) {T : MMap M} (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ) (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.equiv τ g hg v w hw
  | zero => rfl
  | add T₁ T₂ _ _ h₁ h₂ =>
    simp only [MultilinearMap.add_apply, h₁, h₂]; rfl
  | smul c T _ h =>
    simp only [MultilinearMap.smul_apply, h]; rfl

end

theorem Bplus_smul_left {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (a : ℂ)
    (φ : GA D (G.V (.top 0)) → ℂ) (F : GA D (G.V (.grid D.R.m 0)) → ℂ) : Bplus W M (a • φ) F = a * Bplus W M φ F := by
  have e : ∀ h n, besInt W (a • φ) F h n = a * besInt W φ F h n := fun h n => by
    simp only [besInt, Pi.smul_apply, smul_eq_mul]; ring
  simp only [Bplus, e, integral_const_mul]

theorem Bplus_smul_right {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (a : ℂ)
    (φ : GA D (G.V (.top 0)) → ℂ) (F : GA D (G.V (.grid D.R.m 0)) → ℂ) : Bplus W M φ (a • F) = a * Bplus W M φ F := by
  have e : ∀ h n, besInt W φ (a • F) h n = a * besInt W φ F h n := fun h n => by
    simp only [besInt, Pi.smul_apply, smul_eq_mul]; ring
  simp only [Bplus, e, integral_const_mul]

set_option maxHeartbeats 1000000 in
open Classical in

theorem topSep_of_classicalTheorems : GlobalTheory.FunPr.Hypotheses₂ → TopSep := by
  intro _
  unfold TopSep All
  intro D _ T L μ0 _ sc G W M hM S MB F' hF' Ψ hΨ
  have hθ : IsInfFam W.θ := W.θ_is
  set T' : MMap MB := PiTensorProduct.lift.symm F' with hT'
  have hT'm : T' ∈ Mult W.θ MB ∅ 1 := (mem_multT W.θ MB ∅ 1 F').1 hF'
  obtain ⟨Ω, hΩc, hΩ⟩ := GlobalTheory.T.exists_compact_meets_besselTopRationalOrbits W M hM
  have hφ : ∀ ξ, pairVec (coefPlus G W.θ) ξ Ψ ∈ contLeft (G.V (.top 0)) := fun ξ =>
    ⟨GlobalTheory.RowBplus.pairVec_cont G W.θ hθ ξ hΨ, fun γ hγ g => GlobalTheory.RowBplus.pairVec_left G W.θ ξ hΨ hγ g⟩
  have H := fun ξ => GlobalTheory.T.besselPeriodCorankOne_additive_bounded_compact W M hM Ω hΩc hΩ _ (hφ ξ)
  choose C hC using H
  have hadd := fun ξ => (hC ξ).1
  have hadd' := fun ξ => (hC ξ).2.1
  have hbd := fun ξ => (hC ξ).2.2
  have hTt : ∀ u : MB.Vec, F' (PiTensorProduct.tprod ℂ u) = T' u := by
    intro u
    have : F' = PiTensorProduct.lift T' := by rw [hT']; exact (PiTensorProduct.lift.apply_symm_apply F').symm
    rw [this, PiTensorProduct.lift.tprod]
  have hmem : ∀ x : SmT MB, F' x ∈ contLeft (G.V (.grid D.R.m 0)) := by
    intro x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r u =>
      rw [map_smul, hTt]
      exact (contLeft _).smul_mem r (GlobalTheory.Core.Mi.SepPer.mult_mem_contLeft W.θ MB ∅ 1 hT'm u)
    | add x y hx hy =>
      rw [map_add]
      exact (contLeft _).add_mem hx hy
  have pv_add : ∀ ξ ξ', pairVec (coefPlus G W.θ) (ξ + ξ') Ψ = pairVec (coefPlus G W.θ) ξ Ψ + pairVec (coefPlus G W.θ) ξ' Ψ := by
    intro ξ ξ'; funext h; simp [pairVec_apply]
  have pv_smul : ∀ (a : ℂ) ξ, pairVec (coefPlus G W.θ) (a • ξ) Ψ = a • pairVec (coefPlus G W.θ) ξ Ψ := by
    intro a ξ; funext h; simp [pairVec_apply]
  have hBadd : ∀ ξ ξ' F, F ∈ contLeft (G.V (.grid D.R.m 0)) → Bplus W M (pairVec (coefPlus G W.θ) (ξ + ξ') Ψ) F =
      Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) F + Bplus W M (pairVec (coefPlus G W.θ) ξ' Ψ) F := by
    intro ξ ξ' F hF; rw [pv_add]; exact hadd' ξ _ (hφ ξ') F hF
  have hBsmul : ∀ (a : ℂ) ξ F, Bplus W M (pairVec (coefPlus G W.θ) (a • ξ) Ψ) F = a * Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) F := by
    intro a ξ F
    rw [pv_smul]; exact Bplus_smul_left W M a _ F
  have hBsmulR : ∀ (a : ℂ) φ F, Bplus W M φ (a • F) = a * Bplus W M φ F := by
    intro a φ F
    exact Bplus_smul_right W M a φ F
  refine ⟨⟨LinearMap.mk₂ ℂ (fun ξ v => Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) (F' v))
      (fun ξ ξ' v => hBadd ξ ξ' _ (hmem v)) (fun a ξ v => hBsmul a ξ _)
      (fun ξ v v' => (congrArg (Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ)) (F'.map_add v v')).trans (hadd ξ _ (hmem v) _ (hmem v')))
      (fun a ξ v => (congrArg (Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ)) (F'.map_smul a v)).trans (hBsmulR a _ _)), fun ξ v => rfl⟩, ?_⟩
  intro Wt _ _ π e he τ x v
  have hE : ∀ (y y' : Wt τ), e (PiTensorProduct.tprod ℂ (Function.update x τ (y + y'))) =
      e (PiTensorProduct.tprod ℂ (Function.update x τ y)) + e (PiTensorProduct.tprod ℂ (Function.update x τ y')) := by
    intro y y'; rw [MultilinearMap.map_update_add, map_add]
  have hEs : ∀ (a : ℂ) (y : Wt τ), e (PiTensorProduct.tprod ℂ (Function.update x τ (a • y))) =
      a • e (PiTensorProduct.tprod ℂ (Function.update x τ y)) := by
    intro a y; rw [MultilinearMap.map_update_smul, map_smul]
  have hV : ∀ (u u' : MB.sm τ), F' (PiTensorProduct.tprod ℂ (Function.update v τ (u + u'))) =
      F' (PiTensorProduct.tprod ℂ (Function.update v τ u)) + F' (PiTensorProduct.tprod ℂ (Function.update v τ u')) := by
    intro u u'; rw [MultilinearMap.map_update_add, map_add]
  have hVs : ∀ (a : ℂ) (u : MB.sm τ), F' (PiTensorProduct.tprod ℂ (Function.update v τ (a • u))) =
      a • F' (PiTensorProduct.tprod ℂ (Function.update v τ u)) := by
    intro a u; rw [MultilinearMap.map_update_smul, map_smul]
  have hF1 : ∀ (g : Matrix (Fin (G.V (.grid D.R.m 0)).rank) (Fin (G.V (.grid D.R.m 0)).rank) ℂ),
      g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V (.grid D.R.m 0)) τ) → ∀ (x₁ y₁ : MB.sm τ), (y₁ : MB.H τ) = MB.rep τ g x₁ →
      F' (PiTensorProduct.tprod ℂ (Function.update v τ y₁)) =
        rTr _ (atTau W.θ _ τ g) (F' (PiTensorProduct.tprod ℂ (Function.update v τ x₁))) := by
    intro g hg x₁ y₁ hy
    rw [hTt, hTt]
    have := mult_equiv W.θ MB ∅ 1 hT'm τ hg (Function.update v τ x₁) y₁ (by simpa using hy)
    simpa using this
  obtain ⟨Lw, Cu, hL, hb⟩ := GlobalTheory.Core.Mi.SepPer.mult_bound (θ := W.θ) hθ MB (∅ : Set (GA D (G.V (.grid D.R.m 0)))) 1 hT'm Ω hΩc τ v
  refine ⟨LinearMap.mk₂ ℂ (fun y u => Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)
      (F' (PiTensorProduct.tprod ℂ (Function.update v τ u))))
      (fun y y' u => (congrArg (fun ξ => Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) _) (hE y y')).trans (hBadd _ _ _ (hmem _)))
      (fun a y u => (congrArg (fun ξ => Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) _) (hEs a y)).trans (hBsmul _ _ _))
      (fun y u u' => (congrArg (Bplus W M _) (hV u u')).trans (hadd _ _ (hmem _) _ (hmem _)))
      (fun a y u => (congrArg (Bplus W M _) (hVs a u)).trans (hBsmulR _ _ _)), ⟨?_, ?_, ?_⟩, fun y u => rfl⟩
  · intro y
    have hℓ0 := fun (u u' : MB.sm τ) =>
      (congrArg (Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)) (hV u u')).trans
        (hadd _ _ (hmem _) _ (hmem _))
    have hℓ1 := fun (a : ℂ) (u : MB.sm τ) =>
      (congrArg (Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)) (hVs a u)).trans
        (hBsmulR a _ _)
    let ℓ₀ : MB.sm τ →ₗ[ℂ] ℂ :=
      { toFun := fun u => Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)
          (F' (PiTensorProduct.tprod ℂ (Function.update v τ u)))
        map_add' := hℓ0
        map_smul' := hℓ1 }
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
    have hℓw : ∀ u : MB.sm τ, ℓ u = Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)
        (F' (PiTensorProduct.tprod ℂ (Function.update v τ u))) := fun u => congrArg (fun m => m u) hℓ
    refine ⟨ℓ, ⟨Lw, C (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) * Cu, hL, fun w hw => ?_⟩, fun u => hℓw u⟩
    have hw' : w ∈ MB.sm τ := Submodule.subset_span hw
    have e1 : ℓ w = ℓ ((⟨w, hw'⟩ : MB.sm τ) : MB.H τ) := rfl
    rw [e1, hℓw]
    have := hbd (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) _ (hmem _) _
      (fun z hz => by rw [hTt]; exact hb ⟨w, hw'⟩ z hz)
    calc _ ≤ _ := this
      _ = _ := by ring
  · intro h hh g hg hEm w x₁ y₁ hy
    have he1 := he τ h hh (Function.update x τ w) (Function.update x τ (π τ h w)) (by simp) (fun τ' hτ' => by simp [hτ'])
    have hp := pairVec_comp_rho (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ w))) Ψ
      (atTau_mem_GinfC' W.θ _ τ h)
    have hemb : atTau W.θ (G.V (.grid D.R.m 0)) τ g = embTop G (atTau W.θ (G.V (.top 0)) τ h) :=
      (embRel_iff _ _ _).1 (GlobalTheory.T.embRel_atRealPlace_of_unitaryEmbedding D W.θ hθ _ _ _ τ h g hh hg hEm)
    show Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ (π τ h w)))) Ψ)
      (F' (PiTensorProduct.tprod ℂ (Function.update v τ y₁))) =
      Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ w))) Ψ)
      (F' (PiTensorProduct.tprod ℂ (Function.update v τ x₁)))
    rw [he1, hp, hF1 g hg x₁ y₁ hy, hemb]
    exact GlobalTheory.T.besselPeriodCorankOne_simultaneous_rightTranslate W M hM _ (hφ _) _ (hmem _) _
  · intro u hu w x₁ y₁ hy
    show Bplus W M _ (F' (PiTensorProduct.tprod ℂ (Function.update v τ y₁))) = _ * Bplus W M _ (F' (PiTensorProduct.tprod ℂ (Function.update v τ x₁)))
    rw [hF1 u hu.1 x₁ y₁ hy]
    exact GlobalTheory.T.besselPeriodCorankOne_rightTranslate_unipotent W M hM _ _ (hmem _) _ (GlobalTheory.T.atRealPlace_mem_unipotentFlag_adelic D W.θ hθ _ G.besTop.e τ u hu)

end GlobalTheory.SepRows.SepProof

end
