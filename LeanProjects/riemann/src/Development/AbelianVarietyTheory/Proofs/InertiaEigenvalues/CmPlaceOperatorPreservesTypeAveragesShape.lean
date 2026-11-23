import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLocalGenerationInertPlaceOffLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

open GlobalTheory.IdemSupport GlobalTheory.DownLift.GenFinite.Inert

section Op

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def opP (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (c : WO S T →₀ ℂ) (h : GA D T) : Module.End ℂ (WO S T → ℂ) :=
  ∑ y ∈ c.support, c y • (GlobalTheory.SplitScalar.heisL ψ S T y * om (1, h))

theorem opP_apply (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (c : WO S T →₀ ℂ) (h : GA D T)
    (f : WO S T → ℂ) : opP ψ S T om c h f = comb ψ S T c (om (1, h) f) := by
  simp only [opP, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, GlobalTheory.SplitScalar.heisL_apply, comb,
    Finsupp.sum]

theorem opP_comm {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f)) {e : AE D} {c : WO S T →₀ ℂ}
    (hc : ∀ y ∈ c.support, IsHalf e y) (h : GA D T) {B : Module.End ℂ (WO S T → ℂ)} (hB : CommAt ψ S T e B)
    (hBh : ∀ f, IsThetaFunO ψ S T f → B (om (1, h) f) = om (1, h) (B f)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    B (opP ψ S T om c h f) = opP ψ S T om c h (B f) := by
  simp only [opP, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply, (hB _ (hpres _ _ hf)).2 y (hc y hy), hBh f hf]

theorem fin_of_half {e : AE D} (he : infPart D e = 0) {y : WO S T} (hy : IsHalf e y) : y.map (infPart D) = 0 :=
  Matrix.ext fun a b => by
    rw [Matrix.map_apply, ← hy a b, RingHom.map_mul, he, zero_mul]
    rfl

theorem opP_theta {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f)) (hψ : IsStdChar D ψ (-1)) {e : AE D}
    (he : infPart D e = 0) {c : WO S T →₀ ℂ} (hc : ∀ y ∈ c.support, IsHalf e y) (h : GA D T) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (opP ψ S T om c h f) := by
  rw [opP_apply, comb, Finsupp.sum]
  exact theta_sum _ _ f hf fun y hy =>
    theta_smul _ (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_of_half he (hc y hy)) (hpres _ _ hf))

end Op

end GlobalTheory.DownLift.GenSplit

namespace GlobalTheory.DownLift.GenSplit

open GlobalTheory.IdemSupport GlobalTheory.DownLift.GenFinite.Inert

set_option maxHeartbeats 800000 in

theorem placeOp_keep : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (FinPl D)) (v : FinPl D), v ∈ Sb → ∀ (h : GA D (Wc D i)), (∀ a b, idem D (.inl v) * (Formalism.L2.Theta.mt (Wc D i) h - 1) a b = (Formalism.L2.Theta.mt (Wc D i) h - 1) a b) → ∀ (c : WO (Vc D i) (Wc D i) →₀ ℂ), (∀ y ∈ c.support, IsHalf (idem D (.inl v)) y) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → TypeIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ CleanIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ LikeOff R i t Sb (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hω i t Sb v hv h hh c hc f hT hCl hL
  have hW := hω i t
  obtain ⟨-, -, hcA, hfin, -⟩ := GlobalTheory.PlaceTensor.idem_spec D
  have hε := (hfin v).2.2
  have hεe := placeIdem_eq hε
  have hinf := (hfin v).1
  have hce := hcA (.inl v)
  have hpres := hW.om_pres

  have hk : ∀ κ : GA D (Vc D i), SuppIn (dropPl Sb v) (Vc D i) κ → ∀ φ, IsThetaFunO R.ψ (Vc D i) (Wc D i) φ →
      R.ωP i t (κ⁻¹, 1) (opP R.ψ _ _ (R.ωP i t) c h φ) = opP R.ψ _ _ (R.ωP i t) c h (R.ωP i t (κ⁻¹, 1) φ) ∧
      R.ωP i t (κ, 1) (opP R.ψ _ _ (R.ωP i t) c h φ) = opP R.ψ _ _ (R.ωP i t) c h (R.ωP i t (κ, 1) φ) := by
    intro κ hs φ hφ
    have h1 := suppF_of_drop hs hε
    rw [hεe] at h1
    have h2 := (suppGroup _ (1 - idem D (.inl v))).inv_mem h1
    have hcomm : ∀ k : GA D (Vc D i), ∀ ψ', R.ωP i t (k, 1) (R.ωP i t (1, h) ψ') = R.ωP i t (1, h) (R.ωP i t (k, 1) ψ') := by
      intro k ψ'
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one,
        one_mul, mul_one, one_mul]
    exact ⟨opP_comm hpres hc h (commAt_om hW h2) (fun ψ' _ => hcomm _ ψ') hφ,
      opP_comm hpres hc h (commAt_om hW h1) (fun ψ' _ => hcomm _ ψ') hφ⟩
  have hth := opP_theta hpres hW.std hinf hc h hT.1
  rw [← opP_apply]
  refine ⟨⟨hth, fun κ hκ hs => ?_⟩, fun PP a ha tr z hz hov κ hκ hsup => ?_, ⟨hth, fun c' hc' h0 => ?_⟩⟩
  · rw [(hk κ hs f hT.1).2, hT.2 κ hκ (suppIn_of_drop hs), map_smul]
  · obtain ⟨w, hw, how⟩ := hov
    have h0 := hCl PP a ha tr z hz ⟨w, (mem_dropPl.1 hw).2, how⟩ κ hκ fun g hg => suppIn_of_drop (hsup g hg)
    unfold avgW at h0 ⊢
    rw [← map_zero (opP R.ψ _ _ (R.ωP i t) c h), ← h0, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : mirC R i PP a tr z g = 0
    · rw [hg, zero_mul, zero_smul, zero_smul, map_zero]
    · rw [map_smul, (hk (κ g) (hsup g hg) f hT.1).1]
  ·
    have hu : ∀ u ∈ c'.support, ∀ φ, IsThetaFunO R.ψ (Vc D i) (Wc D i) φ →
        heisO R.ψ _ _ u (opP R.ψ _ _ (R.ωP i t) c h φ) = opP R.ψ _ _ (R.ωP i t) c h (heisO R.ψ _ _ u φ) := by
      intro u hu φ hφ
      have hoff := hc' u hu
      have he0 : idem D (.inl v) • u = 0 := Matrix.ext fun a b => by
        rw [Matrix.smul_apply, smul_eq_mul, ← hεe]
        exact hoff.2 v hv _ hε a b
      have hact : actO (Vc D i) (Wc D i) 1 h u = u := by
        have hM : Formalism.L2.Theta.mt (Wc D i) h - 1 = idem D (.inl v) • (Formalism.L2.Theta.mt (Wc D i) h - 1) :=
          Matrix.ext fun a b => (hh a b).symm
        rw [actO, inv_one, mt_one, Matrix.mul_one]
        conv_lhs => rw [← sub_add_cancel (Formalism.L2.Theta.mt (Wc D i) h) 1]
        rw [Matrix.add_mul, Matrix.one_mul, hM, Matrix.smul_mul, ← Matrix.mul_smul, he0, Matrix.mul_zero, zero_add]
      have := opP_comm hpres hc h (commAt_heis hW.std hce hoff.1 he0)
        (fun ψ' hψ' => by rw [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply, hW.om_heis _ _ _ _ hψ', hact]) hφ
      rwa [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply] at this
    have h1 := hL.2 c' hc' h0
    rw [← map_zero (opP R.ψ _ _ (R.ωP i t) c h), ← h1, map_finsuppSum]
    refine Finset.sum_congr rfl fun u hu' => ?_
    dsimp only
    rw [map_smul, hu u hu' f hT.1]

end GlobalTheory.DownLift.GenSplit
