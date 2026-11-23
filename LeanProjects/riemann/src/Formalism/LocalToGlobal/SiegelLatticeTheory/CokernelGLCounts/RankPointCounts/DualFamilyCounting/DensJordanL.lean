import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NotIntDensOfSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanSplittingExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsAdmissibleIntegralBasisChangeOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalUnimodularHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PerpendicularDefinitionHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUnram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodREp
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnitaryDensityFieldMore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.RingInverseMulEquiv

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section JL

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (L : LocSp D M) (p : PlF D)

theorem jl_bc_smulO (o : 𝓞 D.host.E) (x : (VS D).V) :
    L.bc p (o • x) = (D.s.atP p).ιE (o : D.host.E) • L.bc p x := by
  rw [← L.bc_smul p]
  congr 1
  first
    | rfl
    | exact (algebraMap_smul D.host.E o x).symm

theorem jl_iE_mem (hA : Agree δ M p) (o : 𝓞 D.host.E) : (D.s.atP p).ιE (o : D.host.E) ∈ (M p).L.O := by
  rw [hA.2.2.2.1]
  exact PI.CntNotIntW.iE_mem_O D p o

theorem jl_latP_span (hA : Agree δ M p) (S : Set (VS D).V) :
    lattice₂ L p (Submodule.span (𝓞 D.host.E) S) = Submodule.span (M p).L.O (L.bc p '' S) := by
  unfold lattice₂
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.span_induction
      (p := fun x _ => L.bc p x ∈ Submodule.span (M p).L.O (L.bc p '' S)) ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact Submodule.subset_span ⟨y, hy, rfl⟩
    · rw [map_zero]
      exact zero_mem _
    · intro y z _ _ hy hz
      rw [map_add]
      exact add_mem hy hz
    · intro o y _ hy
      rw [jl_bc_smulO L p o y]
      exact Submodule.smul_mem _ (⟨_, jl_iE_mem p hA o⟩ : (M p).L.O) hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem jl_closure {s : 𝓞 D.host.E}
    (hs : s ∈ Submonoid.closure {s : 𝓞 D.host.E | ∃ t : 𝓞 D.host.F, t ∉ p.asIdeal ∧
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = s}) :
    ∃ t : 𝓞 D.host.F, t ∉ p.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = s := by
  induction hs using Submonoid.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), map_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨t', ht', rfl⟩ := hy
    exact ⟨t * t', fun h => (p.isPrime.mem_or_mem h).elim ht ht', map_mul _ _ _⟩

theorem jl_latP_le (hA : Agree δ M p) {A B : Submodule (𝓞 D.host.E) (VS D).V}
    (h : locF (F := D.host.F) (K := D.host.E) p.asIdeal A ≤ locF (F := D.host.F) (K := D.host.E) p.asIdeal B) :
    lattice₂ L p A ≤ lattice₂ L p B := by
  unfold lattice₂
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  have haA : a ∈ locF (F := D.host.F) (K := D.host.E) p.asIdeal A :=
    ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
  obtain ⟨s, hs, hsb⟩ := h haA
  obtain ⟨t, ht, rfl⟩ := jl_closure p hs
  have hne := Formalism.L2.SG.Pf.LocUnramP.iotaF_ne p t ht
  have hcc : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F))⁻¹ *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F)) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hne, map_one]
  have hE : (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E)) =
      ((t : D.host.F) : D.host.E) := rfl
  have hbc : L.bc p (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • a) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F)) • L.bc p a := by
    rw [jl_bc_smulO, hE, Formalism.L2.SG.Pf.LocUnramP.iotaE_alg]
  have hmem : L.bc p (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • a) ∈
      Submodule.span (M p).L.O (L.bc p '' (B : Set (VS D).V)) :=
    Submodule.subset_span ⟨_, hsb, rfl⟩
  have hy : ((D.s.atP p).ιF (t : D.host.F))⁻¹ ∈ 𝒪[(D.s.atP p).Fp] :=
    Formalism.L2.SG.Pf.LocUnramP.iotaF_inv_mem p t ht
  have hc'O : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F))⁻¹ ∈ (M p).L.O := by
    rw [hA.2.2.2.1, (D.s.atP p).O_def]
    have hI : IsIntegral 𝒪[(D.s.atP p).Fp] ((D.s.atP p).ιF (t : D.host.F))⁻¹ :=
      isIntegral_algebraMap (x := (⟨_, hy⟩ : 𝒪[(D.s.atP p).Fp]))
    exact hI.algebraMap
  have e : L.bc p a = (⟨_, hc'O⟩ : (M p).L.O) • L.bc p (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • a) := by
    rw [hbc, Subring.smul_def, smul_smul]
    simp only [hcc, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ hmem

end JL

section BaseDensityIntegrable

variable {D : Formalism.BasicNotions.D7} (p : PlF D)

theorem jl_not_inv_mem (t : 𝓞 D.host.F) (ht : t ∈ p.asIdeal) (ht0 : (D.s.atP p).ιF (t : D.host.F) ≠ 0) :
    ((D.s.atP p).ιF (t : D.host.F))⁻¹ ∉ 𝒪[(D.s.atP p).Fp] := by
  intro hmem
  have hc := (D.s.atP p).val 1 (t : D.host.F)
  rw [map_one, map_one] at hc
  have h1 : (1 : (D.s.atP p).Fp) ≤ᵥ (D.s.atP p).ιF (t : D.host.F) := by
    rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (D.s.atP p).Fp)]
    rw [Valuation.mem_integer_iff] at hmem
    calc ValuativeRel.valuation _ 1 = ValuativeRel.valuation _
          ((D.s.atP p).ιF (t : D.host.F) * ((D.s.atP p).ιF (t : D.host.F))⁻¹) := by
          rw [mul_inv_cancel₀ ht0]
      _ = ValuativeRel.valuation _ ((D.s.atP p).ιF (t : D.host.F)) *
          ValuativeRel.valuation _ ((D.s.atP p).ιF (t : D.host.F))⁻¹ := map_mul _ _ _
      _ ≤ ValuativeRel.valuation _ ((D.s.atP p).ιF (t : D.host.F)) * 1 := mul_le_mul' le_rfl hmem
      _ = ValuativeRel.valuation _ ((D.s.atP p).ιF (t : D.host.F)) := mul_one _
  have h2 := hc.mp h1
  have h3 := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.F) p t).mpr ht
  exact absurd h2 (not_le.mpr h3)

theorem jl_unit_iff (t : 𝓞 D.host.F) :
    IsUnit (⟨(D.s.atP p).ιF (t : D.host.F), Formalism.L2.SG.Pf.LocUnramP.iotaF_mem p t⟩ : 𝒪[(D.s.atP p).Fp]) ↔
      t ∉ p.asIdeal := by
  constructor
  · intro hu ht
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
    have hy' : (D.s.atP p).ιF (t : D.host.F) * (y : (D.s.atP p).Fp) = 1 := by
      have h := congrArg Subtype.val hy
      simpa using h
    have hne : (D.s.atP p).ιF (t : D.host.F) ≠ 0 := left_ne_zero_of_mul_eq_one hy'
    apply jl_not_inv_mem p t ht hne
    rw [inv_eq_of_mul_eq_one_right hy']
    exact y.2
  · intro ht
    have hne := Formalism.L2.SG.Pf.LocUnramP.iotaF_ne p t ht
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, Formalism.L2.SG.Pf.LocUnramP.iotaF_inv_mem p t ht⟩, ?_⟩
    apply Subtype.ext
    simp [mul_inv_cancel₀ hne]

theorem jl_dvd_iff (ϖ : 𝒪[(D.s.atP p).Fp]) (hϖ : Irreducible ϖ) (t : 𝓞 D.host.F) :
    ϖ ∣ (⟨(D.s.atP p).ιF (t : D.host.F), Formalism.L2.SG.Pf.LocUnramP.iotaF_mem p t⟩ : 𝒪[(D.s.atP p).Fp]) ↔
      t ∈ p.asIdeal := by
  haveI := (D.s.atP p).lf
  rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    jl_unit_iff, not_not]

end BaseDensityIntegrable

theorem jordan_decomposition_holds : DualityBasisChange.JordanL := by
  intro D δ M hA L u u' hT F0 what₂ hR F' hz hP hI p ϖ hϖ
  obtain ⟨hKc, hFc, -⟩ := field_dictionary_holds D
  obtain ⟨hC, -, hUr, -⟩ := perpendicular_definition_holds D u u' hT F0 what₂ hR _ F' hz rfl hP
  obtain ⟨hLat, -⟩ := (mmChar_of local_unimodular_holds) D u u' hT F0 what₂ hR _ F' hz rfl hP
  have hNd : NondegOn (VS D).hT (UPair D F0 F') := by
    intro x hx hxy
    have hxo : x ∈ orthK (VS D).hT (UPair D F0 F') := by
      simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker]
      intro y hy
      rw [← (VS D).herm.eq x y, hxy y hy, map_zero]
    exact (Submodule.disjoint_def.1 hC.disjoint) x hx hxo
  obtain ⟨hJ1, -⟩ := jordan_splitting_exists D.host.E D.host.F (VS D).V hKc hFc (VS D).hT (VS D).herm
  have hne : {c | ∃ b a, IsJordanIn (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal b a ∧
      c = cJof p.asIdeal a}.Nonempty := by
    obtain ⟨b, a, hba⟩ := hJ1 _ _ hNd hLat hI p.asIdeal p.isMaximal
    exact ⟨_, b, a, hba, rfl⟩
  obtain ⟨b, a, hba, hc⟩ := Nat.sInf_mem hne
  have hcJ : cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal = cJof p.asIdeal a := hc
  obtain ⟨hbU, hloc, horth, hdiag, ha0⟩ := hba
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hcard : D.R.rS + 1 + (D.R.rS + 1) = finrank D.host.E (UPair D F0 F') := by rw [hUr, hm]; ring
  let e : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) ≃ Fin (finrank D.host.E (UPair D F0 F')) :=
    finSumFinEquiv.trans (finCongr hcard)
  refine ⟨fun i => L.bc p (b (e i)),
    fun i => ⟨(D.s.atP p).ιF ((a (e i) : 𝓞 D.host.F) : D.host.F), Formalism.L2.SG.Pf.LocUnramP.iotaF_mem p (a (e i))⟩,
    ?_, ?_, ?_, ?_⟩
  ·
    have h1 : Submodule.span (M p).L.O (Set.range fun i => L.bc p (b (e i))) =
        lattice₂ L p (Submodule.span (𝓞 D.host.E) (Set.range b)) := by
      rw [jl_latP_span L p (hA p), ← Set.range_comp]
      congr 1
      ext y
      simp only [Set.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨e i, rfl⟩
      · rintro ⟨j, rfl⟩; exact ⟨e.symm j, by simp⟩
    rw [h1]
    exact le_antisymm (jl_latP_le L p (hA p) hloc.le) (jl_latP_le L p (hA p) hloc.ge)
  ·
    intro i j hij
    rw [L.bc_form p]
    show (D.s.atP p).ιE ((VS D).hT (b (e i)) (b (e j))) = 0
    rw [horth _ _ (fun h => hij (e.injective h)), map_zero]
  ·
    intro i
    rw [L.bc_form p]
    show (D.s.atP p).ιE ((VS D).hT (b (e i)) (b (e i))) = _
    rw [hdiag, ← Formalism.L2.SG.Pf.LocUnramP.iotaE_alg p]
    rfl
  ·
    rw [hcJ]
    unfold cJof
    refine Finset.card_equiv e (fun i => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [jl_dvd_iff p ϖ hϖ (a (e i))]
    have h0 := ha0 (e i)
    have hm1 := unitaryAbsoluteValueBounds.mem_pow_iff_le_vF (F := D.host.F) p.isMaximal h0 1
    rw [pow_one] at hm1
    rw [hm1]
    constructor <;> intro h <;> omega

end Formalism.L2.SG.Pf.Cnt
