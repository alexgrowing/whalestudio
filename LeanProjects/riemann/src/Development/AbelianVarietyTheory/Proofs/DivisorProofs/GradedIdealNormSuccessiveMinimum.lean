import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedIdealFgNeBot
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.HnStepEqOfNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

namespace GlobalTheory.LieSmooth

theorem grSup_norm_int_le {K : Type} [Field K] {C : Type} [NormedField C] [IsUltrametricDist C] (j : K →+* C)
    (a : 𝓞 K) : ‖j (algebraMap (𝓞 K) K a)‖ ≤ 1 := by
  have hx : _root_.IsIntegral ℤ (j (algebraMap (𝓞 K) K a)) := map_isIntegral_int j a.isIntegral_coe
  have h : _root_.IsIntegral (NormedField.valuation (K := C)).integer (j (algebraMap (𝓞 K) K a)) := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral h
  have h3 : NormedField.valuation (K := C) (j (algebraMap (𝓞 K) K a)) ≤ 1 := h2
  exact_mod_cast h3

theorem grSup_exists_max {K : Type} [Field K] {C : Type} [NormedField C] [IsUltrametricDist C] (j : K →+* C)
    (I : Submodule (𝓞 K) K) (hfg : I.FG) (hne : I ≠ ⊥) :
    ∃ a ∈ I, a ≠ 0 ∧ ∀ b ∈ I, ‖j b‖ ≤ ‖j a‖ := by
  obtain ⟨s, rfl⟩ := hfg
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hne (by simp)
  obtain ⟨a, ha, hmax⟩ := s.exists_max_image (fun b => ‖j b‖) hs
  have hle : ∀ b ∈ Submodule.span (𝓞 K) (s : Set K), ‖j b‖ ≤ ‖j a‖ := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem y hy => exact hmax y hy
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy hz)
    | smul c y _ hy =>
      rw [Algebra.smul_def, map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (grSup_norm_int_le j c)).trans hy
  refine ⟨a, Submodule.subset_span ha, ?_, hle⟩
  rintro rfl
  apply hne
  rw [eq_bot_iff]
  intro b hb
  have h := hle b hb
  rw [map_zero, norm_zero, norm_le_zero_iff, map_eq_zero] at h
  simp [h]

theorem grSup_exists_form {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) {r : ℕ} (v : Fin r → V) (i : Fin r)
    (hL : L.FG) (hv : LinearIndependent K v) :
    ∃ f : V →ₗ[K] K, (∀ k, k ≤ i → f (v k) = if k = i then 1 else 0) ∧ ∀ x ∈ L, f x ∈ grIdeal L v i := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hv).coord i)
  have hgv : ∀ k, g (v k) = if k = i then 1 else 0 := by
    intro k
    have h1 : g (v k) = (Module.Basis.span hv).coord i (Module.Basis.span hv k) := by
      rw [← hg, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply]
    rw [h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  let S : Submodule K (Fin r → K) := Submodule.pi {k | i < k} (fun _ => ⊥)
  let W₀ : Submodule K V := S.map (Fintype.linearCombination K v)
  obtain ⟨Cm, -, hdec, hCW⟩ := Formalism.L2.Geo.ExtensionFiltration.ExtInvS7cd.exists_compl_inf L hL W₀
  have hdis : Disjoint (Submodule.span K (Cm : Set V)) W₀ :=
    Submodule.disjoint_def.2 hCW
  obtain ⟨U, hU, hc⟩ := hdis.exists_isCompl
  refine ⟨LinearMap.ofIsCompl hc 0 (g.comp W₀.subtype), fun k hk => ?_, fun x hx => ?_⟩
  · have hmem : v k ∈ W₀ := by
      refine ⟨Pi.single k 1, fun m hm => ?_, by simp⟩
      have hm' : i < m := hm
      have : m ≠ k := (lt_of_le_of_lt hk hm').ne'
      simp [this]
    have := LinearMap.ofIsCompl_apply_right hc (φ := 0) (ψ := g.comp W₀.subtype) ⟨v k, hmem⟩
    exact this.trans (hgv k)
  · obtain ⟨a, ⟨haL, haW⟩, c, hcC, rfl⟩ := hdec x hx
    have h1 := LinearMap.ofIsCompl_apply_right hc (φ := 0) (ψ := g.comp W₀.subtype) ⟨a, haW⟩
    have h2 := LinearMap.ofIsCompl_apply_left hc (φ := 0) (ψ := g.comp W₀.subtype)
      ⟨c, hU (Submodule.subset_span hcC)⟩
    rw [map_add]
    erw [h1, h2]
    obtain ⟨d, hdS, rfl⟩ := haW
    rw [Fintype.linearCombination_apply] at haL
    refine ⟨d, ?_, fun k hk => hdS k hk, haL⟩
    simp [Fintype.linearCombination_apply, hgv]

theorem grNorm_latC_eq_inv_iSup : ∀ {K : Type} [Field K] [NumberField K] {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (j : K →+* C) {n r : ℕ} (L : Submodule (𝓞 K) (Fin n → K)) (v : Fin r → Fin n → K) (i : Fin r), Full L → LinearIndependent K v → 0 < (⨆ a : grIdeal L v i, ‖j a‖) ∧ sInf {ρ : ℝ | ∃ d : Fin r → C, d i ≠ 0 ∧ (∀ k, i < k → d k = 0) ∧ (∑ k, d k • fun m => j (v k m)) ∈ latC j L ∧ ρ = ‖d i‖⁻¹} = (⨆ a : grIdeal L v i, ‖j a‖)⁻¹ := by
  intro K _ _ C _ _ j n r L v i hL hv
  obtain ⟨hfg, hne⟩ := grIdeal_fg_ne_bot K (Fin n → K) L r v i hL.1 hv (by rw [hL.2]; exact le_top)
  obtain ⟨a, haI, ha0, hmax⟩ := grSup_exists_max j _ hfg hne
  have hja : j a ≠ 0 := by simpa using ha0
  have hpos : 0 < ‖j a‖ := norm_pos_iff.2 hja
  have hsup : (⨆ a : grIdeal L v i, ‖j a‖) = ‖j a‖ := by
    apply le_antisymm
    · exact ciSup_le fun b => hmax b b.2
    · exact le_ciSup (f := fun b : grIdeal L v i => ‖j b‖) ⟨‖j a‖, by rintro _ ⟨b, rfl⟩; exact hmax b b.2⟩ ⟨a, haI⟩
  rw [hsup]
  refine ⟨hpos, IsLeast.csInf_eq ⟨?_, ?_⟩⟩
  · obtain ⟨c, rfl, hc0, hcL⟩ := haI
    refine ⟨fun k => j (c k), hja, fun k hk => by simp [hc0 k hk], Submodule.subset_span ⟨_, hcL, ?_⟩, rfl⟩
    funext m
    simp [map_sum]
  · rintro _ ⟨d, hdi, hd0, hdL, rfl⟩
    obtain ⟨f, hf1, hf2⟩ := grSup_exists_form L v i hL.1 hv
    let F : (Fin n → C) →ₗ[C] C := Fintype.linearCombination C (fun m => j (f (Pi.single m 1)))
    have hF : ∀ x : Fin n → K, F (fun m => j (x m)) = j (f x) := by
      intro x
      conv_rhs => rw [pi_eq_sum_univ' x]
      simp [F, Fintype.linearCombination_apply, map_sum]
    have hb : ∀ y ∈ latC j L, ‖F y‖ ≤ ‖j a‖ := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        rw [hF]
        exact hmax _ (hf2 x hx)
      | zero => simp
      | add y z _ _ hy hz =>
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy hz)
      | smul c y _ hy =>
        have hc : ‖(c : C)‖ ≤ 1 := c.2
        rw [Subring.smul_def, map_smul, smul_eq_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans hy
    have hval : F (∑ k, d k • fun m => j (v k m)) = d i := by
      rw [map_sum, Finset.sum_eq_single i]
      · rw [map_smul, hF, hf1 i le_rfl]
        simp
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · rw [map_smul, hF, hf1 k h.le]
          simp [hk]
        · simp [hd0 k h]
      · simp
    have := hb _ hdL
    rw [hval] at this
    exact inv_anti₀ (norm_pos_iff.2 hdi) this

end GlobalTheory.LieSmooth
