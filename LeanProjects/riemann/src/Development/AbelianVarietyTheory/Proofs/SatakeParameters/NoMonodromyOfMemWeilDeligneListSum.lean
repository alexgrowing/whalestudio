import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTheRecOfIsRec
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolarizedGaloisRepNarrow2
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnlinkedGLOutright
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameter
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpTwOneNe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMono0LpCharLpSp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NEqZeroOfSumList
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp GlobalTheory.TheRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnlinkedMono

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem noMonodromy_of_mem_weilDeligneListSum : ∀ (l : List (WD h)), (sumList l).mono0 → ∀ y ∈ l, y.mono0
  | [], _, y, hy => by simp at hy
  | z :: l, H, y, hy => by
    have H2 : (z.lpSum (sumList l)).mono0 := H
    obtain ⟨n, a, rfl⟩ := WD.exists_rep z
    obtain ⟨m, b, hb⟩ := WD.exists_rep (sumList l)
    rw [← hb, WD.lpSum_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.sum_N] at H2
    have ha : a.N = 0 := LinearMap.ext fun v => by
      simpa using congrArg Prod.fst (LinearMap.congr_fun H2 (v, 0))
    have hb' : b.N = 0 := LinearMap.ext fun v => by
      simpa using congrArg Prod.snd (LinearMap.congr_fun H2 (0, v))
    rcases List.mem_cons.1 hy with rfl | hy
    · exact (WD.monodromyZero_ofWeilDeligneRepClass_iff a).2 ha
    · exact noMonodromy_of_mem_weilDeligneListSum l (by rw [← hb]; exact (WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 hb') y hy

theorem lpTw_one_ne (x : WD h) (hx : 0 < x.lpDim) : x.lpTw 1 ≠ x := GlobalTheory.WeilDeligne.WD.lpTw_one_ne x hx

def NoTwIne (χ : Ine (F := E) A → ℂ) (X Y : WD h) : Prop :=
  ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (a : WDRep h V) (b : WDRep h V'),
    WD.mk a = X → WD.mk b = Y → ∀ f : V →ₗ[ℂ] V', NoTwHom.IsTw a b f → ∀ v ∈ a.ineEig χ, f v = 0

section
variable {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W']

end

end GlobalTheory.UnlinkedMono
