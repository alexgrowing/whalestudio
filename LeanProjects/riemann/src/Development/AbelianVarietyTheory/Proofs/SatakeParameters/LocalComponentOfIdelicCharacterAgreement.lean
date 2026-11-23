import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.LocMod

theorem Place.isComp_of_chrEq : ∀ (D : D7) (s : SplitPlace D.host.E) (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)), Formalism.L2.JoinChr.IsPlIdem D p.e s.w → (∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (χ : HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → ∀ μw, GlobalTheory.NPin.IsComp χ s.w μw → p.IsComp c μw := by
  intro D s p hpl hpr c χ hc μw hμ
  have he : p.e * p.e = p.e := hpl.1
  have e_ι : ∀ x, p.e * p.ι x = p.ι x := fun x => by rw [← p.ι_π, p.π_ι]
  have hm : ∀ x y, p.ι (x * y) = p.ι x * p.ι y := fun x y => by
    conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, e_ι]
  have ho : p.ι 1 = p.e := by rw [← p.π.map_one, p.ι_π, mul_one]
  let j0 : s.w.adicCompletion D.host.E →* Formalism.L2.Theta.AE D :=
    { toFun := fun x => p.ι x + (1 - p.e)
      map_one' := by rw [ho, add_sub_cancel]
      map_mul' := fun x y => by
        rw [hm]
        linear_combination e_ι x + e_ι y - he }
  have hj0 : Continuous j0 := p.cont_ι.add continuous_const
  let j : (s.w.adicCompletion D.host.E)ˣ →* (Formalism.L2.Theta.AE D)ˣ := Units.map j0
  have hj : Continuous j := by
    refine Units.continuous_iff.2 ⟨hj0.comp Units.continuous_val, ?_⟩
    have : (fun u => ((j u)⁻¹ : (Formalism.L2.Theta.AE D)ˣ).val) =
        fun u : (s.w.adicCompletion D.host.E)ˣ => j0 ((u⁻¹ : (s.w.adicCompletion D.host.E)ˣ) : s.w.adicCompletion D.host.E) := by
      funext u; rw [← map_inv]; rfl
    rw [this]
    exact hj0.comp Units.continuous_coe_inv
  have hcc : Continuous c := hc.1.1
  have hF2 : Continuous fun u => ((c (j u) : Circle) : ℂ) := (continuous_subtype_val.comp hcc).comp hj
  have hμc : Continuous μw := by
    refine continuous_of_continuousAt_one μw ?_
    have hker : (μw.ker : Set (s.w.adicCompletion D.host.E)ˣ) ∈ nhds 1 := hμ.1.mem_nhds (by simp)
    have : (fun _ => (1 : ℂˣ)) =ᶠ[nhds 1] μw := Filter.mem_of_superset hker fun x hx => (MonoidHom.mem_ker.1 hx).symm
    have h2 := (continuousAt_const.congr this).tendsto
    rw [map_one] at h2
    rw [ContinuousAt, map_one]
    exact h2
  have hF1 : Continuous fun u => ((μw u : ℂˣ) : ℂ) := Units.continuous_val.comp hμc
  have hd : Dense (Set.range (Units.map (algebraMap D.host.E (s.w.adicCompletion D.host.E) : D.host.E →* s.w.adicCompletion D.host.E))) := by
    rw [dense_iff_inter_open]
    rintro U hU ⟨u, hu⟩
    have hoe : Topology.IsOpenEmbedding (Units.val : (s.w.adicCompletion D.host.E)ˣ → s.w.adicCompletion D.host.E) :=
      { toIsEmbedding := Units.isEmbedding_val₀
        isOpen_range := by
          have : Set.range (Units.val : (s.w.adicCompletion D.host.E)ˣ → s.w.adicCompletion D.host.E) = {0}ᶜ := by
            ext y
            exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun h => ⟨Units.mk0 y h, rfl⟩⟩
          rw [this]; exact isOpen_compl_singleton }
    obtain ⟨y, hy⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := D.host.E) s.w).exists_mem_open
      (hoe.isOpenMap U hU) ⟨u, u, hu, rfl⟩
    obtain ⟨v, hv, hvy⟩ := hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact v.ne_zero (by simpa using hvy)
    refine ⟨v, hv, Units.mk0 y hy0, Units.ext ?_⟩
    simpa using hvy.symm
  have key : ∀ x : D.host.Eˣ, ((μw (Units.map (algebraMap D.host.E (s.w.adicCompletion D.host.E) : D.host.E →* s.w.adicCompletion D.host.E) x) : ℂˣ) : ℂ)
      = ((c (j (Units.map (algebraMap D.host.E (s.w.adicCompletion D.host.E) : D.host.E →* s.w.adicCompletion D.host.E) x)) : Circle) : ℂ) := by
    intro x
    refine (congrArg Units.val (hμ.2 x)).trans (hc.2 s.w p.e hpl x _ ?_).symm
    change p.ι (algebraMap D.host.E (s.w.adicCompletion D.host.E) x) + (1 - p.e) = _
    rw [← hpr, GlobalTheory.LocMod.Place.pr, p.ι_π, Formalism.L2.JoinChr.locE]
    ring
  have heq := Continuous.ext_on hd hF1 hF2 (by rintro _ ⟨x, rfl⟩; exact key x)
  intro x a ha
  have hja : j x = a := Units.ext ha.symm
  rw [← hja]
  exact congrFun heq x

end GlobalTheory.LocMod
