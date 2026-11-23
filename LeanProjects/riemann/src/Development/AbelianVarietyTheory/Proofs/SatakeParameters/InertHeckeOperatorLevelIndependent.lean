import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteOfTrivOutside
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertLevel

open Classical in

theorem finsum_cosets_eq {G W : Type} [Group G] [AddCommMonoid W] (S K U : Subgroup G)
    (hU : ∀ κ ∈ S, (κ ∈ U ↔ κ ∈ K)) (F : G → W)
    (hF : ∀ x ∈ S, ∀ κ ∈ S, κ ∈ K → F (x * κ) = F x) :
    (∑ᶠ c : G ⧸ U, if hc : ∃ x : G, (x : G ⧸ U) = c ∧ x ∈ S then F hc.choose else 0) =
      ∑ᶠ q : S ⧸ (K.subgroupOf S), F ((q.out : S) : G) := by

  have key : ∀ x y : G, x ∈ S → y ∈ S → (x⁻¹ * y ∈ U ↔ x⁻¹ * y ∈ K) := fun x y hx hy =>
    hU _ (S.mul_mem (S.inv_mem hx) hy)
  let ι : S ⧸ (K.subgroupOf S) → G ⧸ U := fun q => (((q.out : S) : G) : G ⧸ U)
  have hinj : Function.Injective ι := by
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf]
    have h1 := QuotientGroup.eq.1 h
    have h2 := (key _ _ (q.out).2 (q'.out).2).1 h1
    simpa using h2
  have hsupp : (Function.support fun c : G ⧸ U =>
      if hc : ∃ x : G, (x : G ⧸ U) = c ∧ x ∈ S then F hc.choose else 0) ⊆ Set.range ι := by
    intro c hc
    by_cases hc' : ∃ x : G, (x : G ⧸ U) = c ∧ x ∈ S
    · obtain ⟨x, hxc, hxS⟩ := hc'
      refine ⟨((⟨x, hxS⟩ : S) : S ⧸ (K.subgroupOf S)), ?_⟩
      set q : S ⧸ (K.subgroupOf S) := ((⟨x, hxS⟩ : S) : S ⧸ (K.subgroupOf S))
      have h1 := QuotientGroup.eq.1 (QuotientGroup.out_eq' q)
      rw [Subgroup.mem_subgroupOf] at h1
      have h1' : ((q.out : S) : G)⁻¹ * x ∈ K := by simpa using h1
      rw [← hxc]
      exact QuotientGroup.eq.2 ((key _ _ (q.out).2 hxS).2 h1')
    · exact absurd (dif_neg hc') hc
  have hsum := finsum_mem_inter_support (fun c : G ⧸ U =>
      if hc : ∃ x : G, (x : G ⧸ U) = c ∧ x ∈ S then F hc.choose else 0) (Set.range ι)
  rw [Set.inter_eq_right.2 hsupp, finsum_mem_support, finsum_mem_range hinj] at hsum
  rw [hsum]
  refine finsum_congr fun q => ?_
  have hc : ∃ x : G, (x : G ⧸ U) = ι q ∧ x ∈ S := ⟨((q.out : S) : G), rfl, (q.out).2⟩
  rw [dif_pos hc]
  obtain ⟨h1, h2⟩ := hc.choose_spec
  have hm : ((q.out : S) : G)⁻¹ * hc.choose ∈ K :=
    (key _ _ (q.out).2 h2).1 (QuotientGroup.eq.1 h1.symm)
  have e : hc.choose = ((q.out : S) : G) * (((q.out : S) : G)⁻¹ * hc.choose) := by group
  rw [e, hF _ (q.out).2 _ (S.mul_mem (S.inv_mem (q.out).2) h2) hm]

end GlobalTheory.InertLevel

namespace GlobalTheory.InertLevel

theorem heckeFunI_level_indep : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ κ : GAf L n, κ ∈ Umax L n → TrivOutside {v} κ → ∃ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n) → ∀ (U U' : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → (∀ κ, TrivOutside {v} κ → (κ ∈ U' ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h : Formalism.UG.GU Dv.σw n → ℂ), Formalism.UG.IsBiInv (Formalism.UG.KU Dv.σw n) h → ∀ φ : GAf L n → W, (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → heckeFunI L n U Dv h φ = heckeFunI L n U' Dv h φ := by
  intro L _ _ _ n v w Dv hKU U U' hU hU' W _ _ h hbi φ hφ
  funext g

  let F : GAf L n → W := fun x => Dv.hval h (Dv.loc x) • φ (g * x)
  have hF : ∀ x ∈ GlobalTheory.InertSph.Gv L n v, ∀ κ ∈ GlobalTheory.InertSph.Gv L n v, κ ∈ Umax L n → F (x * κ) = F x := by
    intro x _ κ hκS hκU
    obtain ⟨hκ, hk⟩ := hKU κ hκU hκS
    have hloc : Dv.loc (x * κ) = Dv.loc x * Dv.loc κ := (GlobalTheory.SatInd.CosetFin.locHom Dv).map_mul x κ
    have hφκ : φ (g * x * κ) = φ (g * x) := congrFun (hφ κ hκU hκS) (g * x)
    have hval : Dv.hval h (Dv.loc x * Dv.loc κ) = Dv.hval h (Dv.loc x) := by
      unfold InertDatum.hval
      by_cases hy : Dv.loc x ∈ Formalism.UG.GU Dv.σw n
      · have hyk : Dv.loc x * Dv.loc κ ∈ Formalism.UG.GU Dv.σw n := (Formalism.UG.GU Dv.σw n).mul_mem hy hκ
        rw [dif_pos hyk, dif_pos hy]
        have e := hbi 1 ⟨⟨Dv.loc κ, hκ⟩, hk⟩ ⟨Dv.loc x, hy⟩
        simp only [OneMemClass.coe_one, one_mul] at e
        exact e
      · have hyk : Dv.loc x * Dv.loc κ ∉ Formalism.UG.GU Dv.σw n := fun hm => hy (by
          simpa using (Formalism.UG.GU Dv.σw n).mul_mem hm ((Formalism.UG.GU Dv.σw n).inv_mem hκ))
        rw [dif_neg hyk, dif_neg hy]
    show Dv.hval h (Dv.loc (x * κ)) • φ (g * (x * κ)) = Dv.hval h (Dv.loc x) • φ (g * x)
    rw [hloc, hval, ← mul_assoc, hφκ]
  have e1 := finsum_cosets_eq (GlobalTheory.InertSph.Gv L n v) (Umax L n) U (fun κ hκ => hU κ hκ) F hF
  have e2 := finsum_cosets_eq (GlobalTheory.InertSph.Gv L n v) (Umax L n) U' (fun κ hκ => hU' κ hκ) F hF
  exact e1.trans e2.symm

end GlobalTheory.InertLevel
