import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMeasLevW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMeasDef

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid Matrix
open scoped TensorProduct Topology

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem natCast_smul_mem_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) {𝔪 : Ideal (𝓞 E)} {N : ℕ} (hN : (N : 𝓞 E) ∈ 𝔪) {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) : N • z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    refine Submodule.subset_span ⟨(N : 𝓞 E) • l, Submodule.smul_mem_smul hN hl, ?_⟩
    funext i
    simp [Nat.cast_smul_eq_nsmul, ← nsmul_eq_mul, TensorProduct.smul_tmul']
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

theorem eventually_cong_mat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Af F)) {N : ℕ} (hN : N ≠ 0) {X : Type} [TopologicalSpace X] {x₀ : X}
    {φ : X → GL (Fin n) (Af F ⊗[F] E)} (hf : Continuous φ) (h₀ : φ x₀ = 1) :
    ∀ᶠ κ in 𝓝 x₀, ∃ z : Matrix (Fin n) (Fin n) (E ⊗[F] Af F), (∀ i j, z i j ∈ Formalism.L2.Herm.intAf F E) ∧
      (β⁻¹ * Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Af F) : _ →+* _) (φ κ) * β).1 - 1 = N • z := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have ho := (GlobalTheory.Mass.intTens_open_compact F E).1
  set s := GlobalTheory.Mass.swapTens F E (Af F)
  let β' : GL (Fin n) (Af F ⊗[F] E) := Formalism.UG.bc (s.symm : _ →+* _) β
  have hβ : Formalism.UG.bc (s : _ →+* _) β' = β := Units.ext (Matrix.ext fun i j => s.apply_symm_apply _)
  let m : X → GL (Fin n) (Af F ⊗[F] E) := fun κ => β'⁻¹ * φ κ * β'
  have hm : Continuous m := (continuous_const.mul hf).mul continuous_const
  have hm1 : m x₀ = 1 := by simp only [m, h₀, mul_one, inv_mul_cancel]
  have hs : ∀ κ, β⁻¹ * Formalism.UG.bc (s : _ →+* _) (φ κ) * β = Formalism.UG.bc (s : _ →+* _) (m κ) := fun κ => by
    simp only [m, map_mul, map_inv, hβ]
  let c : Af F ⊗[F] E := algebraMap F _ (N : F)⁻¹
  have hc : (N : Af F ⊗[F] E) * c = 1 := by
    rw [← map_natCast (algebraMap F (Af F ⊗[F] E)), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN), map_one]
  have e3 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, c * ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j) ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    have h : Continuous fun κ => c * ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) :=
      continuous_const.mul (((Units.continuous_val.comp hm).matrix_elem i j).sub continuous_const)
    refine (ho.preimage h).mem_nhds ?_
    rw [Set.mem_preimage, hm1, Units.val_one, sub_self, mul_zero]
    exact (GlobalTheory.Mass.intTens F E).zero_mem
  filter_upwards [e3] with κ h3
  refine ⟨Matrix.of fun i j => s (c * ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j)), h3, Matrix.ext fun i j => ?_⟩
  rw [hs, Matrix.smul_apply, Matrix.of_apply, ← map_nsmul, nsmul_eq_mul, ← mul_assoc, hc, one_mul, Matrix.sub_apply, map_sub]
  congr 1
  simp only [Matrix.one_apply]; split_ifs <;> simp

theorem mem_congLev_of_cong {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {Λ : Submodule (𝓞 E) (Fin n → E)} {𝔪 : Ideal (𝓞 E)} {N : ℕ}
    (hN : (N : 𝓞 E) ∈ 𝔪) {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hβ : IsFrame β Λ) (h1 : x ∈ UA hc J) (h2 : x ∈ St β)
    {z : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hz : ∀ i j, z i j ∈ Formalism.L2.Herm.intAf F E)
    (e : (β⁻¹ * x * β).1 - 1 = N • z) : x ∈ congLev hc J Λ 𝔪 := by
  have h3 := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ _).1 h2
  refine ⟨h1, fun y => ⟨h3.1 y, fun hy => ?_⟩, fun y hy => ?_⟩
  · have := h3.2 _ hy
    rwa [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
  · have e1 : x.1 *ᵥ y - y = N • (β.1 *ᵥ (z *ᵥ ((β⁻¹).1 *ᵥ y))) := by
      rw [← mulVec_smul, ← smul_mulVec, ← e, mulVec_mulVec, mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Units.mul_inv, ← Units.val_mul, ← Units.val_mul, sub_mulVec, one_mulVec]
      congr 3
      group
    rw [e1]
    refine natCast_smul_mem_hatL Λ hN ((hβ _).2 fun i => ?_)
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
    show ∑ j : Fin n, _ * _ ∈ _
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hz i j) ((hβ y).1 hy j)

variable {D : D7}

theorem congLev_open_compact (V : HSp D) {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : Submodule.IsLattice D.host.E Λ) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) :
    IsOpen (((congLev D.sp.cm V.gram Λ 𝔪).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) ∧
      IsCompact ((levA V (congLev D.sp.cm V.gram Λ 𝔪) : Subgroup (GA D V)) : Set (GA D V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨β, hβ⟩ := frame_exists_alt D.host.F D.host.E V.rank Λ hΛ
  have ho : IsOpen (((congLev D.sp.cm V.gram Λ 𝔪).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
    obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
    have hf : Continuous (finHom V) := (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β ∅,
      eventually_cong_mat β (Ideal.absNorm_eq_zero_iff.not.2 h𝔪) hf (map_one _)] with κ ⟨h1, h2, _⟩ ⟨z, hz, e⟩
    exact mem_congLev_of_cong (Ideal.absNorm_mem 𝔪) hβ h1 h2 hz e
  refine ⟨ho, ?_⟩
  obtain ⟨C, hC, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact V β
  exact hC.of_isClosed_subset ((GlobalTheory.Ker.CongTop.isClosed_GfC V).inter (Subgroup.isClosed_of_isOpen _ ho))
    fun k hk => hCm k hk.1 ((GlobalTheory.LevSplit.mem_St_iff β Λ hβ _).2
      ⟨fun y => (hk.2.2.1 y).1, fun y => (Subgroup.inv_mem _ hk.2.2.1 y).1⟩)

theorem exists_meas (V : HSp D) (hV : V.SigOK) {q : ℕ} (hq : ∀ τ, (V.sig τ).2 = q) (K : Subgroup (GL (Fin V.rank) (EAf D)))
    (hK : IsOpen ((K.comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) ∧
      IsCompact ((levA V K : Subgroup (GA D V)) : Set (GA D V))) :
    ∃ μ 𝓕, if q = 0 then IsMeasDef V K μ 𝓕 else IsMeasFD V K μ 𝓕 := by
  split_ifs with h
  · choose ν hν hg using fun ρ : D.what₂.Tau =>
      GlobalTheory.Mem.DefiniteMeasure.exists_probHaar (V.sig (tauE D ρ)).1 _ (Or.inr ((hq (tauE D ρ)).trans h))
    obtain ⟨μ, hμ⟩ := GlobalTheory.LevelMeasure.exists_isMeasLevW D V hV K hK.1 hK.2
      (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m) ν hν (fun ρ => (hg ρ _).2 rfl) fun ρ _ => (hg ρ _).1
    obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμ.1
    exact ⟨μ, 𝓕, hμ, h𝓕⟩
  · choose m hm using GlobalTheory.MinfMeasure.exists_isMinf
    obtain ⟨μ, hμ⟩ := GlobalTheory.LevelMeasure.exists_isMeasLevW D V hV K hK.1 hK.2 (fun _ m => IsMinf m) (fun _ => m _ _)
      (fun _ => (hm _ _).1) (fun _ => hm _ _) fun _ _ h => GlobalTheory.LevelMeasure.isMinf_unique (hm _ _) h
    obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμ.1
    exact ⟨μ, 𝓕, hμ, h𝓕⟩

end GlobalTheory.FunObj

end
