import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.OneRatio
import Development.DiscreteGroups.GlobalIrreducibility.DzGalSplit
import Development.DiscreteGroups.GlobalIrreducibility.DzGalKappa

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module ValuativeRel GlobalTheory.SmGL GlobalTheory.Whittaker

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem resIso_holds : ResIso :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ g _ n A v hv w' h' hvN hwN K _ red hr hk =>
    exists_resIso g n A v hv w' h' hvN hwN K red hr hk

theorem pow_prod_eq {ι : Type*} [Fintype ι] (R : ι → ℕ) (F1 F2 : ι → ℂ) (hF : ∀ j, F1 j ^ R j = F2 j ^ R j) :
    (∏ j, F1 j) ^ (∏ j, R j) = (∏ j, F2 j) ^ (∏ j, R j) := by
  rw [← Finset.prod_pow, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem R (Finset.mem_univ j)
  rw [hd, pow_mul, pow_mul, hF]

theorem galEps_of_art (hA : ArtExists) (hT : TameRec) : GalEps := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ _ _ _ g _ A w h w' h' i hi n hn2 hg hN a' ha' K _ _ red hr hk a ha ε hε ψ₀ h₀ ψ
    hψc hψ1 y hirr htame hdim ξ hξ hξf u hu χ₀ χ hχ hlc
  obtain ⟨c, hc⟩ := eps_unr_split h u hu
  rw [hc ε hε ψ hψc hψ1, hc ε hε ψ hψc hψ1]
  have hj := fun j => one_ratio resIso_holds hA hT g A w h w' h' i hi n hn2 hg hN a' ha' K red hr hk a ha ε hε ψ₀ h₀
    ψ hψc hψ1 y hirr htame hdim ξ hξ hξf χ₀ χ hχ hlc (c j)
  choose R hR0 hR using hj
  refine ⟨∏ j, R j, Finset.prod_pos fun j _ => hR0 j, ?_⟩
  have e : ∀ (e' : Fin u.lpDim → ℂˣ) (G : ℂ), ((∏ j, e' j : ℂˣ) : ℂ) * G ^ u.lpDim = ∏ j, ((e' j : ℂ) * G) := by
    intro e' G
    rw [Units.coe_prod, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [e, e]
  exact pow_prod_eq R _ _ hR

theorem artExists_of_LL (hLL : GlobalTheory.Published.LocalLanglandsGL) : ArtExists := by
  intro L Ω _ _ _ _ _ A v h
  obtain ⟨rc, ⟨a, ha, -⟩, -⟩ := hLL.1 L Ω A v h
  exact ⟨a, ha⟩

theorem lGal : LGal := fun hLL hT => galEps_of_art (artExists_of_LL hLL) hT

end DiscreteGroups.sglob.DzType

end
