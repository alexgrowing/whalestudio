import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSpaceTransposeInverseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchSmoothCompTransposeInvStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieActionCompTransposeInvStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModerateGrowthCompTransposeInvStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCompTransposeInvStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCompTransposeInvStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTransformPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInvPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.UnfoldingAlt.LiftTV

theorem arch_ti (F : archSmooth ℚ 3) : IsArchSmooth (fun g : G3 => (F : G3 → ℂ) (ti g)) := by
  simpa using GlobalTheory.T.archSmooth_comp_transposeInv F F.2 1

def S : archSmooth ℚ 3 →ₗ[ℂ] archSmooth ℚ 3 where
  toFun F := ⟨fun g => (F : G3 → ℂ) (ti g), arch_ti F⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem S_apply (F : archSmooth ℚ 3) (g : G3) : (S F : G3 → ℂ) g = (F : G3 → ℂ) (ti g) := rfl

theorem ti_mul (g h : G3) : ti (g * h) = ti g * ti h :=
  (GlobalTheory.T.transposeInv_properties.1 _ _ g h).1

theorem tr_eq (W : G3 → ℂ) : tr W = fun g => W (w3 * ti (dia dl3) * ti g) :=
  funext (GlobalTheory.T.whittaker_transform_properties.1 W)

theorem tr_mem {V : Submodule ℂ (G3 → ℂ)} (W : V) : tr W.1 ∈ tV V :=
  Submodule.mem_map.2 ⟨W.1, W.2, rfl⟩

def e (V : Submodule ℂ (G3 → ℂ)) : V ≃ₗ[ℂ] tV V :=
  Submodule.equivMapOfInjective trL GlobalTheory.T.whittaker_transform_properties.2.2.1 V

def U' {V : Submodule ℂ (G3 → ℂ)} (U : V →ₗ[ℂ] archSmooth ℚ 3) : tV V →ₗ[ℂ] archSmooth ℚ 3 :=
  S ∘ₗ U ∘ₗ (e V).symm.toLinearMap

theorem U'_e {V : Submodule ℂ (G3 → ℂ)} (U : V →ₗ[ℂ] archSmooth ℚ 3) (W : V) :
    U' U (e V W) = S (U W) := by
  simp [U']

theorem U'_tr {V : Submodule ℂ (G3 → ℂ)} (U : V →ₗ[ℂ] archSmooth ℚ 3) (W : V) (h : tr W.1 ∈ tV V) :
    U' U ⟨tr W.1, h⟩ = S (U W) :=
  U'_e U W

theorem exists_e {V : Submodule ℂ (G3 → ℂ)} (X : tV V) : ∃ W : V, X = e V W :=
  ⟨(e V).symm X, by simp⟩

theorem continuous_lift {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) (U : V →ₗ[ℂ] archSmooth ℚ 3)
    (hU : IsLiftU V hV U) (W : V) : Continuous (U W : G3 → ℂ) := by
  refine FourierWhittaker.IsUSmooth.continuous (n := 3) (K := ℚ) ⟨(U W).2, ?_, (hU.1 W).1⟩
  obtain ⟨O, hO⟩ := hV.level W.1 W.2
  refine ⟨O, fun g u hu => ?_⟩
  have h := hU.2.1 W (finEmb ℚ 3 u) g
  have e : (⟨fun x => W.1 (x * finEmb ℚ 3 u), hV.stable _ W.2 _⟩ : V) = W :=
    Subtype.ext (funext fun x => hO x u hu)
  rw [e] at h
  exact h.symm

theorem left_ti {φ : G3 → ℂ} (h : IsLeftInvariant φ) : IsLeftInvariant (fun g : G3 => φ (ti g)) := by
  intro γ g
  show φ (ti (dia γ * g)) = φ (ti g)
  rw [ti_mul, GlobalTheory.T.transposeInv_properties.2.1 γ]
  exact h (ti γ) (ti g)

theorem main : ∀ (V : Submodule ℂ (G3 → ℂ)) (hV : WhA V) (U : V →ₗ[ℂ] archSmooth ℚ 3), IsLiftU V hV U →
  ∃ (hV' : WhA (tV V)) (U' : tV V →ₗ[ℂ] archSmooth ℚ 3), IsLiftU (tV V) hV' U' ∧
    ∀ W : V, ∃ hW : tr W.1 ∈ tV V, (U' ⟨tr W.1, hW⟩ : G3 → ℂ) = fun g : G3 => (U W : G3 → ℂ) (ti g) := by
  intro V hV U hU
  have hV' := GlobalTheory.T.whittaker_space_transpose_inverse V hV
  refine ⟨hV', LiftTV.U' U, ⟨?_, ?_, ?_⟩, fun W => ⟨tr_mem W, ?_⟩⟩
  · intro X
    obtain ⟨W, rfl⟩ := exists_e X
    obtain ⟨h1, h2, h3, h4⟩ := hU.1 W
    rw [U'_e]
    refine ⟨left_ti h1, GlobalTheory.T.moderateGrowth_comp_transposeInv _ h2, GlobalTheory.T.cuspidal_comp_transposeInv _ h1 h3, ?_⟩
    funext g
    have := GlobalTheory.T.whittaker_comp_transposeInv _ h1 (continuous_lift hV U hU W) g
    rw [h4] at this
    exact this
  · intro X h g
    obtain ⟨W, rfl⟩ := exists_e X
    have hW' : (fun x => W.1 (x * ti h)) ∈ V := hV.stable _ W.2 _
    have hfun : (fun x => (e V W).1 (x * h)) = tr (fun x => W.1 (x * ti h)) :=
      funext fun x => GlobalTheory.T.whittaker_transform_properties.2.1 W.1 h x
    have hel : (⟨fun x => (e V W).1 (x * h), hV'.stable _ (e V W).2 h⟩ : tV V)
        = e V ⟨fun x => W.1 (x * ti h), hW'⟩ := Subtype.ext hfun
    rw [hel, U'_e, U'_e, S_apply, S_apply, hU.2.1 W (ti h) (ti g), ti_mul]
  · intro X i j
    obtain ⟨W, rfl⟩ := exists_e X
    have hWa : IsArchSmooth W.1 := hV.arch W.1 W.2
    have hc := GlobalTheory.T.archSmooth_comp_transposeInv W.1 hWa (w3 * ti (dia dl3))
    have hl : ((EA j i ⟨W.1, hWa⟩ : archSmooth ℚ 3) : G3 → ℂ) ∈ V := hV.lie _ W.2 j i
    set W2 : V := ⟨_, hl⟩ with hW2
    have hel : (⟨_, hV'.lie _ (e V W).2 i j⟩ : tV V) = e V (-W2) := by
      apply Subtype.ext
      have a1 : (⟨(e V W).1, hV'.arch _ (e V W).2⟩ : archSmooth ℚ 3) = ⟨_, hc⟩ :=
        Subtype.ext (tr_eq W.1)
      simp only [a1]
      rw [GlobalTheory.T.lie_action_comp_transposeInv ⟨W.1, hWa⟩ _ i j hc]
      funext g
      show _ = tr (-W2.1) g
      rw [GlobalTheory.T.whittaker_transform_properties.1]
      rfl
    rw [hel, U'_e, U'_e, map_neg]
    have h3 : U W2 = EA j i (U W) := hU.2.2 W j i
    rw [h3]
    apply Subtype.ext
    have hb := GlobalTheory.T.archSmooth_comp_transposeInv (U W) (U W).2 1
    have b1 : S (U W) = ⟨fun g : G3 => (U W : G3 → ℂ) (1 * ti g), hb⟩ :=
      Subtype.ext (funext fun g => by simp [S_apply])
    rw [b1, GlobalTheory.T.lie_action_comp_transposeInv (U W) 1 i j]
    funext g
    simp [S_apply]
  · have := U'_tr U W (tr_mem W)
    rw [this]
    rfl

end GlobalTheory.CompanionTheory.UnfoldingAlt.LiftTV
