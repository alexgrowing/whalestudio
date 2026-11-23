import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularSemisimpleUnitaryDataOfRegular
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.AnisoCovol

theorem exists_compact_cover {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (Γ : Subgroup G) [CompactSpace (G ⧸ Γ)] :
    ∃ K : Set G, IsCompact K ∧ ∀ x : G, ∃ g ∈ Γ, g * x ∈ K := by
  classical
  choose K hK hK' using fun x : G => exists_compact_mem_nhds x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : G => ((↑) : G → G ⧸ Γ) '' interior (K x))
    (fun x => QuotientGroup.isOpenMap_coe _ isOpen_interior) (fun q _ => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact Set.mem_iUnion.2 ⟨x, x, mem_interior_iff_mem_nhds.2 (hK' x), rfl⟩)
  refine ⟨(⋃ x ∈ t, K x)⁻¹, (t.isCompact_biUnion fun x _ => hK x).inv, fun y => ?_⟩
  obtain ⟨x, hx, z, hz, e⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ ((y⁻¹ : G) : G ⧸ Γ)))
  refine ⟨z⁻¹ * y⁻¹, QuotientGroup.eq.1 e, ?_⟩
  rw [Set.mem_inv, show (z⁻¹ * y⁻¹ * y)⁻¹ = z by group]
  exact Set.mem_iUnion₂.2 ⟨x, hx, interior_subset hz⟩

theorem measure_ne_top_of_cover {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] {K : Set G} (hK : IsCompact K)
    (hcov : ∀ x : G, ∃ g ∈ Γ, g * x ∈ K) (μ : Measure G) [μ.IsHaarMeasure] {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) : μ 𝓕 ≠ ⊤ := by
  have hsub : 𝓕 ⊆ ⋃ g : Γ, ((g • K) ∩ 𝓕) := by
    intro x hx
    obtain ⟨g, hg, hk⟩ := hcov x
    refine Set.mem_iUnion.2 ⟨(⟨g, hg⟩ : Γ)⁻¹, ?_, hx⟩
    rw [Set.mem_inv_smul_set_iff]
    exact hk
  refine ne_of_lt ?_
  calc μ 𝓕 ≤ μ (⋃ g : Γ, ((g • K) ∩ 𝓕)) := measure_mono hsub
    _ ≤ ∑' g : Γ, μ ((g • K) ∩ 𝓕) := measure_iUnion_le _
    _ = μ K := (h𝓕.measure_eq_tsum K).symm
    _ < ⊤ := hK.measure_lt_top

theorem bc_bc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {n : Type} [Fintype n] [DecidableEq n]
    (φ : A →+* B) (φ' : B →+* C) (g : GL n A) :
    Formalism.UG.bc φ' (Formalism.UG.bc φ g) = Formalism.UG.bc (φ'.comp φ) g := rfl

variable {D : D7} {V : HSp D}

abbrev tensFlip (D : D7) : D.host.E ⊗[D.host.F] AF D.host.F ≃+* AF D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.comm D.host.F D.host.E (AF D.host.F)).toRingEquiv

theorem tensFlip_inclE (e : D.host.E) :
    tensFlip D (Formalism.UG.inclE (F := D.host.F) (AF D.host.F) e) = inclR (F := D.host.F) (AF D.host.F) e := by
  simp [Formalism.UG.inclE, inclR]

theorem tensFlip_symm_inclR (e : D.host.E) :
    (tensFlip D).symm (inclR (F := D.host.F) (AF D.host.F) e) = Formalism.UG.inclE (F := D.host.F) (AF D.host.F) e := by
  simp [Formalism.UG.inclE, inclR]

theorem tensFlip_sig (x : D.host.E ⊗[D.host.F] AF D.host.F) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig (tensFlip D x) =
      tensFlip D (Formalism.UG.sigR D.sp.cm.sig (AF D.host.F) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [Formalism.UG.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [RingEquiv.map_add, RingHom.map_add, hx, hy]

theorem tensFlip_symm_sig (x : AF D.host.F ⊗[D.host.F] D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (AF D.host.F) ((tensFlip D).symm x) =
      (tensFlip D).symm (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [Formalism.UG.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [RingEquiv.map_add, RingHom.map_add, hx, hy]

variable {D : D7} (V : HSp D)

theorem tensFlip_gram :
    (V.gram.map (Formalism.UG.inclE (F := D.host.F) (AF D.host.F))).map (tensFlip D).toRingHom = JR (AF D.host.F) V.gram := by
  ext i j
  exact tensFlip_inclE _

theorem tensFlip_symm_gram :
    (JR (AF D.host.F) V.gram).map (tensFlip D).symm.toRingHom = V.gram.map (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)) := by
  ext i j
  exact tensFlip_symm_inclR _

def uFlip : Formalism.UG.UPts D.sp.cm.sig V.gram (AF D.host.F) →* GA D V :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapU (Formalism.UG.sigR D.sp.cm.sig (AF D.host.F)) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig)
    (tensFlip D).toRingHom tensFlip_sig _ _ (tensFlip_gram V)

def uFlipSymm : GA D V →* Formalism.UG.UPts D.sp.cm.sig V.gram (AF D.host.F) :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapU (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (Formalism.UG.sigR D.sp.cm.sig (AF D.host.F))
    (tensFlip D).symm.toRingHom tensFlip_symm_sig _ _ (tensFlip_symm_gram V)

theorem matHom_uFlip (g : Formalism.UG.UPts D.sp.cm.sig V.gram (AF D.host.F)) :
    GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram (uFlip V g) = Formalism.UG.bc (tensFlip D).toRingHom g.1 := rfl

theorem val_uFlipSymm (g : GA D V) :
    ((uFlipSymm V g : Formalism.UG.UPts D.sp.cm.sig V.gram (AF D.host.F)) : GL (Fin V.rank) (D.host.E ⊗[D.host.F] AF D.host.F)) =
      Formalism.UG.bc (tensFlip D).symm.toRingHom (GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram g) := rfl

theorem bc_inclR (γ : GF V) :
    Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ.1 =
      Formalism.UG.bc (tensFlip D).toRingHom (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)) γ.1) := by
  rw [bc_bc]
  congr 1

theorem bc_symm_inclR (γ : GF V) :
    Formalism.UG.bc (tensFlip D).symm.toRingHom (Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ.1) =
      Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)) γ.1 := by
  rw [bc_bc]
  congr 1

variable {D : D7} (V : HSp D)

theorem uFlip_mem (γ : GF V) (g : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centPts D.sp.cm.sig V.gram γ.1 (AF D.host.F)) :
    uFlip V (Subgroup.inclusion inf_le_left g) ∈ cent (rat V γ) := by
  have h3 : Formalism.UG.bc (tensFlip D).toRingHom (g.1 * Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)) γ.1) =
      Formalism.UG.bc (tensFlip D).toRingHom (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)) γ.1 * g.1) :=
    congrArg _ (Subgroup.mem_centralizer_singleton_iff.1 g.2.2)
  rw [MonoidHom.map_mul, MonoidHom.map_mul, ← bc_inclR] at h3
  exact Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext h3)

def centFlip (γ : GF V) :
    GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centPts D.sp.cm.sig V.gram γ.1 (AF D.host.F) →* cent (rat V γ) :=
  ((uFlip V).comp (Subgroup.inclusion inf_le_left)).codRestrict _ (uFlip_mem V γ)

theorem matHom_centFlip (γ : GF V) (g : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centPts D.sp.cm.sig V.gram γ.1 (AF D.host.F)) :
    GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram (centFlip V γ g : GA D V) = Formalism.UG.bc (tensFlip D).toRingHom g.1 :=
  matHom_uFlip V _

theorem centFlip_surjective (γ : GF V) : Function.Surjective (centFlip V γ) := by
  intro y
  have hy : GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram y.1 * Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ.1 =
      Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ.1 * GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram y.1 :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 y.2)
  have hx : ((uFlipSymm V y.1 : Formalism.UG.UPts D.sp.cm.sig V.gram (AF D.host.F)) :
      GL (Fin V.rank) (D.host.E ⊗[D.host.F] AF D.host.F)) ∈
      Subgroup.centralizer {Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)) γ.1} := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have e := congrArg (Formalism.UG.bc (tensFlip D).symm.toRingHom) hy
    rw [MonoidHom.map_mul, MonoidHom.map_mul, bc_symm_inclR] at e
    rw [val_uFlipSymm]
    exact e
  refine ⟨⟨_, (uFlipSymm V y.1).2, hx⟩, Subtype.ext (GlobalTheory.AdelicU.matHom_injective (AF D.host.F) D.sp.cm.sig V.gram ?_)⟩
  rw [matHom_centFlip]
  show Formalism.UG.bc (tensFlip D).toRingHom ((uFlipSymm V y.1 : Formalism.UG.UPts D.sp.cm.sig V.gram (AF D.host.F)) :
      GL (Fin V.rank) (D.host.E ⊗[D.host.F] AF D.host.F)) = _
  rw [val_uFlipSymm, bc_bc]
  ext i j
  simp [Formalism.UG.bc]

theorem centFlip_rat (γ : GF V) (a : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centPts D.sp.cm.sig V.gram γ.1 (AF D.host.F))
    (ha : a ∈ ((GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centRat D.sp.cm.sig V.gram γ.1).map
      (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)))).subgroupOf
        (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centPts D.sp.cm.sig V.gram γ.1 (AF D.host.F))) :
    centFlip V γ a ∈ (GQ V).subgroupOf (cent (rat V γ)) := by
  obtain ⟨δ, hδ, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 ha)
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨δ, hδ.1, ?_⟩))
  show _ = GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram (centFlip V γ a : GA D V)
  rw [matHom_centFlip, ← e, bc_bc]
  congr 1

variable {D : D7} (V : HSp D)

theorem continuous_tensFlip :
    letI := Formalism.BasicNotions.tensTopL (F := D.host.F) (E := D.host.E) (AF D.host.F)
    Continuous (tensFlip D) := by
  letI := Formalism.BasicNotions.tensTopL (F := D.host.F) (E := D.host.E) (AF D.host.F)
  letI : Algebra (AF D.host.F) (D.host.E ⊗[D.host.F] AF D.host.F) := Algebra.TensorProduct.rightAlgebra
  haveI : IsModuleTopology (AF D.host.F) (D.host.E ⊗[D.host.F] AF D.host.F) := ⟨rfl⟩
  haveI : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  let L : D.host.E ⊗[D.host.F] AF D.host.F →ₗ[AF D.host.F] AF D.host.F ⊗[D.host.F] D.host.E :=
    { toFun := tensFlip D
      map_add' := fun x y => (tensFlip D).map_add x y
      map_smul' := fun a x => by
        rw [Algebra.smul_def, RingEquiv.map_mul, Algebra.smul_def]
        rfl }
  exact IsModuleTopology.continuous_of_linearMap L

theorem continuous_centFlip (γ : GF V) :
    letI := Formalism.BasicNotions.tensTopL (F := D.host.F) (E := D.host.E) (AF D.host.F)
    Continuous (centFlip V γ) := by
  letI := Formalism.BasicNotions.tensTopL (F := D.host.F) (E := D.host.E) (AF D.host.F)
  have hf : Continuous (tensFlip D) := continuous_tensFlip
  have hbc : Continuous (Formalism.UG.bc (n := Fin V.rank) (tensFlip D).toRingHom) :=
    Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map hf, Units.continuous_coe_inv.matrix_map hf⟩
  refine Continuous.subtype_mk ?_ _
  refine (GlobalTheory.AdelicU.isEmbedding_matHom (AF D.host.F) D.sp.cm.sig V.gram).continuous_iff.2 ?_
  exact hbc.comp continuous_subtype_val

theorem compactSpace_cent (γ : GF V) (hc : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.AdelicCompact D.sp.cm.sig V.gram γ.1) :
    CompactSpace (cent (rat V γ) ⧸ (GQ V).subgroupOf (cent (rat V γ))) := by
  letI := Formalism.BasicNotions.tensTopL (F := D.host.F) (E := D.host.E) (AF D.host.F)
  have hc' : CompactSpace (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centPts D.sp.cm.sig V.gram γ.1 (AF D.host.F) ⧸
      ((GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centRat D.sp.cm.sig V.gram γ.1).map
        (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)))).subgroupOf
          (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centPts D.sp.cm.sig V.gram γ.1 (AF D.host.F))) := hc
  let q := Quotient.map' (s₁ := QuotientGroup.leftRel (((GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centRat D.sp.cm.sig V.gram γ.1).map
        (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)))).subgroupOf
          (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centPts D.sp.cm.sig V.gram γ.1 (AF D.host.F))))
      (s₂ := QuotientGroup.leftRel ((GQ V).subgroupOf (cent (rat V γ)))) (centFlip V γ) fun a b h => by
    refine QuotientGroup.leftRel_apply.2 ?_
    rw [← MonoidHom.map_inv, ← MonoidHom.map_mul]
    exact centFlip_rat V γ _ (QuotientGroup.leftRel_apply.1 h)
  have hq : Continuous q := (continuous_centFlip V γ).quotient_map' _
  have hs : Function.Surjective q := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨x, rfl⟩ := centFlip_surjective V γ y
    exact ⟨QuotientGroup.mk x, rfl⟩
  exact hs.compactSpace hq

variable {D : D7}

theorem countable_GF (V : HSp D) : Countable (GF V) := by
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin V.rank) (Fin V.rank) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin V.rank → D.host.E))
  haveI : Countable (GL (Fin V.rank) D.host.E) := Units.val_injective.countable
  exact Subtype.countable

theorem countable_GQ (V : HSp D) : Countable (GQ V) := by
  haveI := countable_GF V
  refine Function.Surjective.countable (f := fun δ : GF V => (⟨rat V δ, Subgroup.mem_subgroupOf.2
    (Subgroup.mem_map.2 ⟨δ, δ.2, rfl⟩)⟩ : GQ V)) fun x => ?_
  obtain ⟨δ, hδ, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 x.2)
  exact ⟨⟨δ, hδ⟩, Subtype.ext (Subtype.ext e)⟩

theorem covol_lt_top : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → ∀ (k : ℕ) (Kf : Fin k → Type) [∀ i, Field (Kf i)] [∀ i, Algebra D.host.F (Kf i)], Nonempty (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg D.sp.cm.sig V.gram γ.1.1 ≃ₐ[D.host.F] ∀ i, Kf i) → (∀ i, IsField (TensorProduct D.host.F (Kf i) D.host.E)) → ∀ (dt : Measure (cent (rat V γ))) [dt.IsHaarMeasure] (𝓣 : Set (cent (rat V γ))), IsFundamentalDomain ((GQ V).subgroupOf (cent (rat V γ))) 𝓣 dt → dt 𝓣 < ⊤ := by
  intro hR D V γ hγ k Kf _ _ he hf dt _ 𝓣 h𝓣
  have hreg := GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS γ hγ
  have hc := (hR.2 D.host.F D.host.E (Fin V.rank) D.sp.cm.sig V.gram γ.1 hreg k Kf he).2 hf
  haveI := compactSpace_cent V γ hc
  haveI : LocallyCompactSpace (cent (rat V γ)) := (isClosed_cent (rat V γ)).locallyCompactSpace
  obtain ⟨K, hK, hcov⟩ := exists_compact_cover ((GQ V).subgroupOf (cent (rat V γ)))
  haveI := countable_GQ V
  haveI : Countable ((GQ V).subgroupOf (cent (rat V γ))) :=
    Function.Injective.countable (f := fun x : (GQ V).subgroupOf (cent (rat V γ)) => (⟨x.1.1, x.2⟩ : GQ V))
      fun a b h => by
        have e := Subtype.mk.inj h
        exact Subtype.ext (Subtype.ext e)
  exact lt_top_iff_ne_top.2 (measure_ne_top_of_cover _ hK hcov dt h𝓣)

end GlobalTheory.AnisoCovol

end
