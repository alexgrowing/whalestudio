import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthEmb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepRankZeroWittEmbeddingValueAtZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf GlobalTheory.FunObj GlobalTheory.RowUnf GlobalTheory.RowChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RowVolZero

theorem transport_haar_eq {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H]
    (ΓG : Subgroup G) (ΓH : Subgroup H) [Countable ΓG] (e : H ≃ₜ* G)
    (hΓ : ∀ x, x ∈ ΓG → e.symm x ∈ ΓH) (hΓ' : ∀ y, y ∈ ΓH → e y ∈ ΓG) (ν : Measure G) [ν.IsHaarMeasure] (μ : Measure H)
    (hνμ : ν = μ.map e) (𝓕 : Set G) (h𝓕 : IsFundamentalDomain ΓG 𝓕 ν) (𝓕H : Set H)
    (h𝓕H : IsFundamentalDomain ΓH 𝓕H μ) (f : G → ℂ) (hf : ∀ γ ∈ ΓG, ∀ g, f (γ * g) = f g) :
    ∫ g in 𝓕, f g ∂ν = ∫ x in 𝓕H, f (e x) ∂μ := by
  have hmap : ν.map e.symm = μ := by
    ext s hs
    rw [hνμ, Measure.map_apply (map_continuous e.symm).measurable hs,
      Measure.map_apply (map_continuous e).measurable ((map_continuous e.symm).measurable hs)]
    congr 1; ext x; simp
  have hq : Measure.QuasiMeasurePreserving e.symm ν μ :=
    ⟨(map_continuous e.symm).measurable, by rw [hmap]⟩
  let eΓ : ΓH → ΓG := fun g => ⟨e g.1, hΓ' g.1 g.2⟩
  have heΓ : Function.Bijective eΓ := by
    refine ⟨fun a b hab => Subtype.ext (e.injective (congrArg Subtype.val hab)), fun y => ⟨⟨e.symm y.1, hΓ y.1 y.2⟩, ?_⟩⟩
    exact Subtype.ext (e.apply_symm_apply y.1)
  have h𝓕' : IsFundamentalDomain ΓG (e.symm ⁻¹' 𝓕H) ν :=
    h𝓕H.preimage_of_equiv hq heΓ fun g x => by
      change e.symm (e g.1 * x) = g.1 * e.symm x
      rw [map_mul, e.symm_apply_apply]
  rw [h𝓕.setIntegral_eq h𝓕' fun g x => hf g.1 g.2 x, hνμ]
  have hme : MeasurableEmbedding (e : H → G) := e.toHomeomorph.measurableEmbedding
  rw [hme.setIntegral_map]
  have hpre : e ⁻¹' (e.symm ⁻¹' 𝓕H) = 𝓕H := by ext x; simp
  exact congrArg (fun s => ∫ x in s, f (e x) ∂μ) hpre

theorem map_eq_of_one {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H]
    (e : H ≃ₜ* G) (ν : Measure G) [ν.IsHaarMeasure] (μ : Measure H) [μ.IsHaarMeasure] (S : Set G)
    (hS : ν S = 1) (hS' : μ (e ⁻¹' S) = 1) : ν = μ.map e := by
  haveI : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  have hc := Measure.isMulLeftInvariant_eq_smul ν (μ.map e)
  have h1 : (μ.map e) S = 1 := by
    rw [show (μ.map e) = μ.map e.toHomeomorph.toMeasurableEquiv from rfl, MeasurableEquiv.map_apply]
    exact hS'
  have h2 := congrArg (fun m : Measure G => m S) hc
  simp only [Measure.smul_apply, h1, hS, smul_eq_mul, mul_one] at h2
  have h3 : Measure.haarScalarFactor ν (μ.map e) = 1 := by
    have : ((Measure.haarScalarFactor ν (μ.map e) : NNReal) : ENNReal) = 1 := by
      rw [ENNReal.smul_def] at h2; simpa using h2.symm
    exact_mod_cast this
  rw [hc, h3, one_smul]

section Lat

variable {D : D7} {S S₀ : HSp D} (d : HypDec S S₀ 0)

theorem wittHyperbolicRankZero_proj_mul_emb : d.q0 * d.i₀ = 1 := by
  apply rat_injective
  rw [rat_mul, rat_one]
  exact d.p0_j0

theorem wittHyperbolicRankZero_emb_mul_proj : d.i₀ * d.q0 = 1 := by
  apply rat_injective
  rw [rat_mul, rat_one]
  exact GlobalTheory.FinPl.VLast.Transport.rz_j0p0 d

theorem finite_adelic_embedding_matrix (g : GA D S₀) : (Lev.finE S (d.emb0 g)).1 =
    HMul.hMul (HMul.hMul (d.i₀.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) : Matrix (Fin S.rank) (Fin S₀.rank) (Lev.EAf D))
      (Lev.finE S₀ g).1 : Matrix (Fin S.rank) (Fin S₀.rank) (Lev.EAf D))
      (d.q0.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) : Matrix (Fin S₀.rank) (Fin S.rank) (Lev.EAf D)) := by
  have e1 : d.j0.map (GlobalTheory.LevSplit.finSw D) = d.i₀.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := by
    ext i k; exact GlobalTheory.LevSplit.finSw_incA _
  have e2 : d.p0.map (GlobalTheory.LevSplit.finSw D) = d.q0.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := by
    ext i k; exact GlobalTheory.LevSplit.finSw_incA _
  rw [GlobalTheory.LevSplit.finE_val, GlobalTheory.LevSplit.finE_val, GlobalTheory.FinPl.VLast.Transport.unitaryMatrix_rankZeroWittEmbedding_eq, Matrix.map_mul, Matrix.map_mul, e1, e2]

end Lat

theorem hatL_mulVec_rect {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (Λ' : Submodule (𝓞 E) (Fin m → E)) (h : ∀ y ∈ Λ, M *ᵥ y ∈ Λ')
    (x : Fin n → TensorProduct F E (Formalism.L2.Herm.Af F)) (hx : x ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    M.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at *
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨M *ᵥ z, h z hz, ?_⟩
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum]
  | zero => simp
  | add y z _ _ hy hz =>
    rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [Subring.smul_def, Matrix.mulVec_smul]
    exact Submodule.smul_mem _ c hy

theorem inclusion_mulVec_projection_mulVec {D : D7} {S S₀ : HSp D} (d : HypDec S S₀ 0) (y : Fin S.rank → Lev.EAf D) :
    d.i₀.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) *ᵥ
      (d.q0.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, wittHyperbolicRankZero_emb_mul_proj, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

theorem PI_one {D : D7} {S S₀ : HSp D} (d : HypDec S S₀ 0) (y : Fin S₀.rank → Lev.EAf D) :
    d.q0.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) *ᵥ
      (d.i₀.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, wittHyperbolicRankZero_proj_mul_emb, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

theorem wittRankZero_mem_completedLattice_iff_proj_mem {D : D7} {S S₀ : HSp D} (d : HypDec S S₀ 0) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (Λ₀ : Submodule (𝓞 D.host.E) (Fin S₀.rank → D.host.E))
    (hi : ∀ y ∈ Λ₀, d.i₀ *ᵥ y ∈ Λ) (hq : ∀ x ∈ Λ, d.q0 *ᵥ x ∈ Λ₀) (x : Fin S.rank → Lev.EAf D) :
    x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔
      d.q0.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ₀ := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have h1 := hatL_mulVec_rect (F := D.host.F) d.q0 Λ Λ₀ hq x hx
    exact h1
  · have h1 := hatL_mulVec_rect (F := D.host.F) d.i₀ Λ₀ Λ hi
      (d.q0.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) *ᵥ x) hx
    rw [inclusion_mulVec_projection_mulVec] at h1
    exact h1

theorem wittRankZero_finiteAdelic_proj_embedding_mulVec {D : D7} {S S₀ : HSp D} (d : HypDec S S₀ 0) (g : GA D S₀) (x : Fin S.rank → Lev.EAf D) :
    d.q0.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) *ᵥ ((Lev.finE S (d.emb0 g)).1 *ᵥ x) =
      (Lev.finE S₀ g).1 *ᵥ (d.q0.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) *ᵥ x) := by
  rw [finite_adelic_embedding_matrix, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, wittHyperbolicRankZero_proj_mul_emb,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem wittRankZero_embedding_mem_latticeCongruence_iff {D : D7} {S S₀ : HSp D} (d : HypDec S S₀ 0) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (Λ₀ : Submodule (𝓞 D.host.E) (Fin S₀.rank → D.host.E))
    (hi : ∀ y ∈ Λ₀, d.i₀ *ᵥ y ∈ Λ) (hq : ∀ x ∈ Λ, d.q0 *ᵥ x ∈ Λ₀) (g : GA D S₀) :
    Lev.finE S (d.emb0 g) ∈ congLev D.sp.cm S.gram Λ ⊤ ↔ Lev.finE S₀ g ∈ congLev D.sp.cm S₀.gram Λ₀ ⊤ := by
  rw [congLev_top, congLev_top, Subgroup.mem_inf, Subgroup.mem_inf]
  simp only [GlobalTheory.LevSplit.finE_mem_UA, true_and]
  show (∀ x, x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ (Lev.finE S (d.emb0 g)).1 *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) ↔
    ∀ y, y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ₀ ↔ (Lev.finE S₀ g).1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ₀
  constructor
  · intro H y
    have h1 := H (d.i₀.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) *ᵥ y)
    have h2 := (wittRankZero_mem_completedLattice_iff_proj_mem d Λ Λ₀ hi hq (d.i₀.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) *ᵥ y)).trans
      (Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ₀) (PI_one d y)))
    have h3 := (wittRankZero_mem_completedLattice_iff_proj_mem d Λ Λ₀ hi hq
      ((Lev.finE S (d.emb0 g)).1 *ᵥ (d.i₀.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) *ᵥ y))).trans
      (Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ₀)
        ((wittRankZero_finiteAdelic_proj_embedding_mulVec d g (d.i₀.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) *ᵥ y)).trans
          (congrArg (fun z => (Lev.finE S₀ g).1 *ᵥ z) (PI_one d y)))))
    exact h2.symm.trans (h1.trans h3)
  · intro H x
    have h2 := wittRankZero_mem_completedLattice_iff_proj_mem d Λ Λ₀ hi hq x
    have h3 := (wittRankZero_mem_completedLattice_iff_proj_mem d Λ Λ₀ hi hq ((Lev.finE S (d.emb0 g)).1 *ᵥ x)).trans
      (Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ₀) (wittRankZero_finiteAdelic_proj_embedding_mulVec d g x)))
    exact h2.trans ((H _).trans h3.symm)

theorem wittRankZero_proj_comp_incl_mulVec_eq_self {D : D7} {S S₀ : HSp D} (d : HypDec S S₀ 0) (y : Fin S₀.rank → D.host.E) : d.q0 *ᵥ (d.i₀ *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, wittHyperbolicRankZero_proj_mul_emb, Matrix.one_mulVec]

theorem vol_rankZero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) {M : GlobalTheory.FunObj.Vol G}, M.Is t →
    ∀ (n : ℕ) (hn : n + 1 = D.R.m) (f : GA D (G.V (.grid D.R.m n)) → ℂ), (∀ γ ∈ GQ (G.V (.grid D.R.m n)), ∀ g, f (γ * g) = f g) →
      ∫ g in M.fd (.grid D.R.m n), f g ∂M.ν (.grid D.R.m n) =
        ∫ g₀ in M.fd (.top n), f ((rowJac G n (by omega) 0 (by omega)).emb0 g₀) ∂M.ν (.top n) := by
  intro D T L sc G t M hM n hn f hf
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by have := D.R.two_le_m; omega⟩
  have hj : j + 1 < D.R.m := by omega
  have hg0 := hM.vtx (.grid D.R.m (j + 1)) ⟨le_rfl, by omega⟩
  have ht0 := hM.vtx (.top (j + 1)) (show j + 1 ≤ D.R.m by omega)
  have hlev : ∀ i, 0 < i → levJ G t (.grid i (j + 1)) = G.levMax (.grid i (j + 1)) := by
    rintro (_ | i) h
    · omega
    · rfl
  rw [hlev _ (by omega)] at hg0
  have hneg : Node.neg D.R.m (.grid D.R.m (j + 1)) = 0 := by
    show (D.R.m - (j + 1)) / 2 = 0
    omega
  rw [Vol.IsAt, if_pos hneg] at hg0
  rw [Vol.IsAt, if_pos (show Node.neg D.R.m (.top (j + 1)) = 0 from rfl)] at ht0
  obtain ⟨hgm, hgf⟩ := hg0
  obtain ⟨htm, htf⟩ := ht0
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid D.R.m (j + 1)))
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top (j + 1)))
  haveI := hgm.1
  haveI := htm.1
  let d := rowJac G (j + 1) hj 0 (by omega)
  have hi : ∀ y ∈ G.Λ (.top (j + 1)), d.i₀ *ᵥ y ∈ G.Λ (.grid D.R.m (j + 1)) := by
    intro y hy
    show _ ∈ (G.node (.grid D.R.m (j + 1))).lat
    rw [show (G.node (.grid D.R.m (j + 1))).lat = _ from G.sp.rowLat j hj]
    exact ⟨y, hy, 0, fun p => (stairId D.host.AA D.host.AAbar (D.R.m - 1 - (j + 1)) p).zero_mem, by simp; rfl⟩
  have hq : ∀ x ∈ G.Λ (.grid D.R.m (j + 1)), d.q0 *ᵥ x ∈ G.Λ (.top (j + 1)) := by
    intro x hx
    change x ∈ (G.node (.grid D.R.m (j + 1))).lat at hx
    rw [show (G.node (.grid D.R.m (j + 1))).lat = _ from G.sp.rowLat j hj] at hx
    obtain ⟨y, hy, u, -, rfl⟩ := hx
    haveI : IsEmpty (Fin (D.R.m - 1 - (j + 1))) := by
      rw [show D.R.m - 1 - (j + 1) = 0 by omega]; infer_instance
    rw [Subsingleton.elim u 0, Matrix.mulVec_zero, add_zero]
    change d.q0 *ᵥ (d.i₀ *ᵥ y) ∈ _
    have e := wittRankZero_proj_comp_incl_mulVec_eq_self d y
    rw [e]
    exact hy
  let e : GA D (G.V (.top (j + 1))) ≃ₜ* GA D (G.V (.grid D.R.m (j + 1))) :=
    { GlobalTheory.FinPl.VLast.Transport.rzEquiv d with
      continuous_toFun := d.continuous_embed
      continuous_invFun := GlobalTheory.FinPl.VLast.Transport.rzInv_continuous d }
  have hpre : e ⁻¹' (((G.levMax (.grid D.R.m (j + 1))).comap (Lev.finE _) : Subgroup _) : Set _) =
      (((G.levMax (.top (j + 1))).comap (Lev.finE _) : Subgroup _) : Set _) := by
    ext g
    exact wittRankZero_embedding_mem_latticeCongruence_iff d _ _ hi hq g
  have hmeas := map_eq_of_one e _ _ _ (GlobalTheory.Mass.Levels.measure_comap_finE hgm)
    (by rw [hpre]; exact GlobalTheory.Mass.Levels.measure_comap_finE htm)
  exact transport_haar_eq (GQ _) (GQ _) e (fun x hx => GlobalTheory.FinPl.VLast.Transport.rzInv_mem_GQ d hx)
    (fun y hy => d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hy) _ _ hmeas _ hgf _ htf f hf

end GlobalTheory.RowVolZero
