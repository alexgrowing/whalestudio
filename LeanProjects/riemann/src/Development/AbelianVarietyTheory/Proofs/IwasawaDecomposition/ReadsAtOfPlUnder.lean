import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

open GlobalTheory.Mem.Top.TwChar (plUnder incl embLL_incl mem_plUnder)

theorem readsAt_of_plUnder (X X' : Stages) (h : Enl X.B X'.B) (hc : Carried X.toD7 X'.toD7) (v' : X'.B.places.Pl)
    (i : X.toD7.ntw.Tw) (i' : X'.toD7.ntw.Tw) (b : Bool) (hi : HEq i i')
    (hr : ReadsAt (D := X.toD7) i b (plUnder h v')) : ReadsAt (D := X'.toD7) i' b v' := by
  intro x'

  have hx : X'.B.embLL ((x' : ↥X'.toD7.LL0) : X'.toD7.what₂.LL) ∈ X'.B.embLL '' (X'.B.LL0 : Set X'.B.LL) :=
    ⟨_, (x' : ↥X'.toD7.LL0).2, rfl⟩
  rw [h.2.2.1] at hx
  obtain ⟨y, hy, hye⟩ := hx
  have hint' : IsIntegral ℤ (X.B.embLL y) := by
    rw [hye]
    exact (RingOfIntegers.isIntegral_coe x').map
      ((X'.toD7.what₂.embLL.comp (algebraMap ↥X'.toD7.LL0 X'.toD7.what₂.LL)).toIntAlgHom)
  have hint : IsIntegral ℤ (⟨y, hy⟩ : ↥X.toD7.LL0) := by
    refine (isIntegral_algHom_iff ((X.toD7.what₂.embLL.comp (algebraMap ↥X.toD7.LL0 X.toD7.what₂.LL)).toIntAlgHom) ?_).1 (by exact hint')
    exact X.toD7.what₂.embLL.injective.comp (algebraMap ↥X.toD7.LL0 X.toD7.what₂.LL).injective
  let x : 𝓞 ↥X.toD7.LL0 := ⟨⟨y, hy⟩, hint⟩
  have e : X.toD7.what₂.embLL ((x : ↥X.toD7.LL0) : X.toD7.what₂.LL) =
      X'.toD7.what₂.embLL ((x' : ↥X'.toD7.LL0) : X'.toD7.what₂.LL) := hye

  obtain ⟨h1, h2⟩ := hc.emb i i' hi x x' e
  have hside : HEq (sideEmb i b (x : ↥X.toD7.LL0)) (sideEmb i' b (x' : ↥X'.toD7.LL0)) := by
    cases b
    · simpa [sideEmb] using h2
    · simpa [sideEmb] using h1
  have hleft := ((same_basic hc.exp.gal hc.exp.set hc.exp.frm).2.2.2.2 i i' hi).2.2 _ _ hside

  have hmap : RingOfIntegers.mapRingHom (incl h) (algebraMap (𝓞 ↥X.toD7.LL0) (𝓞 X.toD7.what₂.LL) x) =
      algebraMap (𝓞 ↥X'.toD7.LL0) (𝓞 X'.toD7.what₂.LL) x' := by
    apply RingOfIntegers.ext
    apply X'.B.embLL.injective
    exact (embLL_incl h ((x : ↥X.toD7.LL0) : X.toD7.what₂.LL)).trans e
  have hright : 0 < X.toD7.what₂.places.val (plUnder h v') ((x : ↥X.toD7.LL0) : X.toD7.what₂.LL) ↔
      0 < X'.toD7.what₂.places.val v' ((x' : ↥X'.toD7.LL0) : X'.toD7.what₂.LL) := by
    refine (TwistChoice.val_pos_iff_mem X.toD7 (plUnder h v') x).trans
      (Iff.trans ?_ (TwistChoice.val_pos_iff_mem X'.toD7 v' x').symm)
    have hm := mem_plUnder h v' (algebraMap (𝓞 ↥X.toD7.LL0) (𝓞 X.toD7.what₂.LL) x)
    rw [hmap] at hm
    exact hm
  exact hleft.symm.trans ((hr x).trans hright)

end GlobalTheory.HeightCounting.Up
