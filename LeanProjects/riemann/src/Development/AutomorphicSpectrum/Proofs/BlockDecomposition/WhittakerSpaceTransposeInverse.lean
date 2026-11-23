import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchSmoothCompTransposeInvStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieActionCompTransposeInvStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenSubgroupTransposeInvCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerGL3AdelicDecayStatement
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

namespace GlobalTheory.CompanionTheory.UnfoldingAlt.WhatV

theorem tr_eq_fun (W : G3 → ℂ) :
    tr W = fun g : G3 => W ((w3 * ti (dia dl3)) * ti g) :=
  funext (GlobalTheory.T.whittaker_transform_properties.1 W)

theorem EA_tr (W : G3 → ℂ) (hW : IsArchSmooth W) (h : IsArchSmooth (tr W)) (i j : Fin 3) :
    ((EA i j ⟨tr W, h⟩ : archSmooth ℚ 3) : G3 → ℂ) =
      tr (-((EA j i ⟨W, hW⟩ : archSmooth ℚ 3) : G3 → ℂ)) := by
  have e := tr_eq_fun W
  have h' : IsArchSmooth (fun g : G3 => W ((w3 * ti (dia dl3)) * ti g)) := e ▸ h
  have key := GlobalTheory.T.lie_action_comp_transposeInv ⟨W, hW⟩ (w3 * ti (dia dl3)) i j h'
  have hs : (⟨tr W, h⟩ : archSmooth ℚ 3) =
      ⟨fun g : G3 => W ((w3 * ti (dia dl3)) * ti g), h'⟩ := Subtype.ext e
  rw [hs]
  refine key.trans ?_
  rw [tr_eq_fun]
  rfl

theorem whA_tV : ∀ V : Submodule ℂ (G3 → ℂ), WhA V → WhA (tV V) := by
  intro V hV
  have mem : ∀ {W : G3 → ℂ}, W ∈ V → tr W ∈ tV V := fun hW =>
    Submodule.mem_map_of_mem (f := trL) hW
  have arch : ∀ F ∈ tV V, IsArchSmooth F := by
    rintro _ ⟨W, hW, rfl⟩
    change IsArchSmooth (tr W)
    rw [tr_eq_fun]
    exact GlobalTheory.T.archSmooth_comp_transposeInv W (hV.arch W hW) _
  refine ⟨?_, ?_, ?_, arch, ?_, ?_, ?_⟩
  · rintro _ ⟨W, hW, rfl⟩ h
    have e : (fun g => trL W (g * h)) = tr (fun x => W (x * ti h)) :=
      funext fun g => GlobalTheory.T.whittaker_transform_properties.2.1 W h g
    rw [e]
    exact mem (hV.stable W hW (ti h))
  · rintro _ ⟨W, hW, rfl⟩
    exact GlobalTheory.T.whittaker_transform_properties.2.2.2.1 W (hV.psi W hW)
  · rintro _ ⟨W, hW, rfl⟩
    exact GlobalTheory.T.whittaker_transform_properties.2.2.2.2 W (hV.cen W hW)
  · rintro _ ⟨W, hW, rfl⟩
    obtain ⟨U₀, hU₀⟩ := hV.level W hW
    obtain ⟨U₁, hU₁⟩ := GlobalTheory.T.open_subgroup_transposeInv_compat U₀
    refine ⟨U₁, fun g u hu => ?_⟩
    obtain ⟨u', hu', hti⟩ := hU₁ u hu
    change tr W (g * finEmb ℚ 3 u) = tr W g
    rw [GlobalTheory.T.whittaker_transform_properties.1 W, GlobalTheory.T.whittaker_transform_properties.1 W, hti, ← mul_assoc]
    exact hU₀ _ u' hu'
  · rintro _ ⟨W, hW, rfl⟩ i j
    have h : IsArchSmooth (tr W) := arch _ (mem hW)
    change ((EA i j ⟨tr W, h⟩ : archSmooth ℚ 3) : G3 → ℂ) ∈ tV V
    rw [EA_tr W (hV.arch W hW) h i j]
    exact mem (V.neg_mem (hV.lie W hW j i))
  · rintro _ ⟨W, hW, rfl⟩
    exact GlobalTheory.T.whittaker_GL3_adelic_decay W (hV.cen W hW) (hV.gauge W hW)

end GlobalTheory.CompanionTheory.UnfoldingAlt.WhatV
