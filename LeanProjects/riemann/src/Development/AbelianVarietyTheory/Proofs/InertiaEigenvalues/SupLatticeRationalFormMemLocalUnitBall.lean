import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValCCuspOfSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGoodOfBddAll
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_locBall_of_mem_MK : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f : NX.FmK S ((j : ℕ) + 1), (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (S.A ((j : ℕ) + 1)).MK → f ∈ locBall YS fw iC b j := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j f hf
  intro z
  obtain ⟨hwk, hb⟩ := ((YS.fi j).mkK _).1 hf
  obtain ⟨T, io, k, hk, y, u, hy, hu, hval⟩ := PtC.exists_valC z (wtA (κ j)) (κ j).n
  obtain ⟨e, ho⟩ := GlobalTheory.ReadingOver.overLa_placeAt _ _ (embC YS iC b) T io k hk
  let v : T0.PtM ((j : ℕ) + 1) (placeC YS iC b) :=
    ⟨vAtV (PtV.mk (cls := algCls (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c) (PY := Unit) (lies := fun _ _ _ _ => True)
      (placeC YS iC b) ho y hy () trivial), ⟨_, rfl⟩⟩
  obtain ⟨w, hw⟩ := (fw.pt j (placeC YS iC b)).surjective v
  have h1 := hb (placeC YS iC b) w
  have e1 : (⟨(YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1, hwk⟩ : (Rl.FW j).WK) = fw.e j (cuspOf YS fw j f) :=
    Subtype.ext (e_cuspOf YS fw j f).symm
  rw [e1, fw.nrm_eq, hw] at h1
  have h2 := (T0.nrmM_le_one_iff _ _ v _).1 h1
  have h3 := (GlobalTheory.GoodPtsModel.inV_iff_nval T ho.1 (evI y (cuspOf YS fw j f : T0.R ((j : ℕ) + 1)))).2 h2
  rw [hval _ (cuspOf_mem_sec YS fw j f), norm_mul, hu, one_mul]
  exact (hk.int _).2 h3

end GlobalTheory.GeoTie
