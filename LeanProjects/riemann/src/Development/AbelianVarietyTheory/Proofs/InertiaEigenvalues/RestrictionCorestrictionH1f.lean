import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferCocycleFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferContinuousOfContinuousOn

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct

noncomputable section

namespace GlobalTheory.InducedSectionsSpanStatement

section General

variable {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL]

def trCochain (ι : G →* G') [Fintype (G' ⧸ ι.range)] (T : LocLat G' Qp LL O) :
    (G → T.V) →ₗ[O] (G' → T.V) where
  toFun f g := ∑ q : G' ⧸ ι.range,
    T.ρ (g • q).out (f (Function.invFun ι ((g • q).out⁻¹ * g * q.out)))
  map_add' f f' := by
    funext g
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext g
    simp only [Pi.smul_apply, LinearMap.map_smul_of_tower, RingHom.id_apply, Finset.smul_sum]

theorem trCochain_apply (ι : G →* G') [Fintype (G' ⧸ ι.range)] (T : LocLat G' Qp LL O)
    (f : G → T.V) (g : G') : trCochain ι T f g = ∑ q : G' ⧸ ι.range,
    T.ρ (g • q).out (f (Function.invFun ι ((g • q).out⁻¹ * g * q.out))) := rfl

theorem trCochain_Z1T [IsTopologicalGroup G'] (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [Fintype (G' ⧸ ι.range)]
    (T : LocLat G' Qp LL O) (c : G → T.V) (hc : c ∈ latticeCocycles (LiftingTheory.resLoc ι hι T).L) :
    trCochain ι T c ∈ latticeCocycles T.L := by
  obtain ⟨⟨hcont, hcoc⟩, hT⟩ := hc
  have hj : ∀ g, Function.invFun ι (ι g) = g := Function.leftInverse_invFun he.injective
  haveI : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
  haveI : IsTopologicalAddGroup T.V := IsModuleTopology.topologicalAddGroup LL T.V
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine GlobalTheory.transfer_continuous_of_continuousOn LL G' T.V T.ρ ι.range ho
      (fun g => IsModuleTopology.continuous_of_linearMap (T.ρ g))
      (fun g => c (Function.invFun ι g)) ?_
    have h1 : (ι.range : Set G') = ι '' Set.univ := by
      rw [Set.image_univ]; rfl
    rw [h1, he.isInducing.continuousOn_image_iff]
    have h2 : ((fun g => c (Function.invFun ι g)) ∘ ι) = c := by
      funext g; simp only [Function.comp_apply, hj]
    rw [h2]
    exact hcont.continuousOn
  · refine (GlobalTheory.transfer_cocycle_formula LL G' T.V T.ρ ι.range).2.1
      (fun g => c (Function.invFun ι g)) ?_
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, hj, hj, hj]
    exact hcoc a b
  · intro g _
    rw [trCochain_apply]
    exact Submodule.sum_mem _ fun q _ => T.L.stable _ _ (hT _ (Set.mem_univ _))

theorem trCochain_B1T (ι : G →* G') (hι : Continuous ι) (hinj : Function.Injective ι)
    [Fintype (G' ⧸ ι.range)]
    (T : LocLat G' Qp LL O) (c : G → T.V) (hc : c ∈ latticeCoboundaries (LiftingTheory.resLoc ι hι T).L) :
    trCochain ι T c ∈ latticeCoboundaries T.L := by
  obtain ⟨x, hx, rfl⟩ := hc
  have hj : ∀ g, Function.invFun ι (ι g) = g := Function.leftInverse_invFun hinj
  refine ⟨∑ q : G' ⧸ ι.range, T.ρ q.out x,
    Submodule.sum_mem _ fun q _ => T.L.stable _ _ hx, ?_⟩
  funext g
  symm
  refine (GlobalTheory.transfer_cocycle_formula LL G' T.V T.ρ ι.range).2.2.1
    (fun g => T.ρ (ι (Function.invFun ι g)) x - x) x ?_ g
  rintro _ ⟨a, rfl⟩
  rw [hj]

def corH1 [IsTopologicalGroup G'] (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [Fintype (G' ⧸ ι.range)]
    (T : LocLat G' Qp LL O) : LatticeCohomology (LiftingTheory.resLoc ι hι T).L →ₗ[O] LatticeCohomology T.L :=
  Submodule.mapQ _ _
    (((trCochain ι T).comp (latticeCocycles (LiftingTheory.resLoc ι hι T).L).subtype).codRestrict (latticeCocycles T.L)
      (fun c => trCochain_Z1T ι hι he ho T c c.2))
    (by
      intro c hc
      simp only [Submodule.mem_comap, Submodule.subtype_apply] at hc ⊢
      exact trCochain_B1T ι hι he.injective T c hc)

theorem corH1_res [IsTopologicalGroup G'] (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [Fintype (G' ⧸ ι.range)]
    (T : LocLat G' Qp LL O) (κ : LatticeCohomology T.L) :
    corH1 ι hι he ho T (LiftingTheory.resH1 ι hι T κ) = ((ι.range.index : ℕ) : O) • κ := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  rw [← Submodule.Quotient.mk_smul]
  refine (Submodule.Quotient.eq _).2 ?_
  obtain ⟨c, ⟨hcont, hcoc⟩, hT⟩ := c
  refine ⟨∑ q : G' ⧸ ι.range, c q.out,
    Submodule.sum_mem _ fun q _ => hT _ (Set.mem_univ _), ?_⟩
  funext g
  have H := GlobalTheory.transfer_cocycle_formula LL G' T.V T.ρ ι.range
  have h4 := H.2.2.2 c hcoc g
  have hj : ∀ q : G' ⧸ ι.range, ι (Function.invFun ι ((g • q).out⁻¹ * g * q.out))
      = (g • q).out⁻¹ * g * q.out := fun q => Function.invFun_eq (H.1 g q)
  change T.ρ g (∑ q : G' ⧸ ι.range, c q.out) - ∑ q : G' ⧸ ι.range, c q.out
    = ∑ q : G' ⧸ ι.range, T.ρ (g • q).out
        (c (ι (Function.invFun ι ((g • q).out⁻¹ * g * q.out)))) - ((ι.range.index : ℕ) : O) • c g
  simp only [hj]
  simp only at h4
  rw [h4, Nat.cast_smul_eq_nsmul]
  abel

theorem corH1_natural [IsTopologicalGroup G'] (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [Fintype (G' ⧸ ι.range)]
    (T₁ T₂ : LocLat G' Qp LL O) (F : LatHom T₁.L T₂.L) (κ : LatticeCohomology (LiftingTheory.resLoc ι hι T₁).L) :
    corH1 ι hι he ho T₂ ((LiftingTheory.resHom ι hι F).H1map κ) = F.H1map (corH1 ι hι he ho T₁ κ) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  funext g
  change ∑ q : G' ⧸ ι.range, T₂.ρ (g • q).out
        (F.f (c.1 (Function.invFun ι ((g • q).out⁻¹ * g * q.out))))
    = F.f (∑ q : G' ⧸ ι.range, T₁.ρ (g • q).out
        (c.1 (Function.invFun ι ((g • q).out⁻¹ * g * q.out))))
  rw [map_sum]
  exact Finset.sum_congr rfl fun q _ => (F.equiv _ _).symm

variable {K₀ K K₀' K' : Type} [Field K₀] [Field K] [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B] [Algebra K₀' BdR] [Algebra K' BdR]
    [IsScalarTower Qp K' BdR] [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]

def repVB (PD' : PeriodData G' Qp K₀' K' B BdR) (T : LocLat G' Qp LL O) :
    Representation LL G' (T.V ⊗[Qp] B) where
  toFun g := actVB PD' T.ρ g
  map_one' := by
    refine AlgebraTensorModule.curry_injective ?_
    ext x b
    simp [actVB]
  map_mul' g h := by
    refine AlgebraTensorModule.curry_injective ?_
    ext x b
    simp [actVB]

theorem actVB_tmul_one (PD' : PeriodData G' Qp K₀' K' B BdR) (T : LocLat G' Qp LL O) (g : G')
    (x : T.V) : actVB PD' T.ρ g (x ⊗ₜ[Qp] (1 : B)) = T.ρ g x ⊗ₜ[Qp] (1 : B) := by
  simp [actVB]

theorem actVB_res (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData G' Qp K₀' K' B BdR)
    (ι : G →* G') (hι : Continuous ι) (hact : ∀ g b, PD.actB g b = PD'.actB (ι g) b)
    (T : LocLat G' Qp LL O) (g : G) (x : T.V ⊗[Qp] B) :
    actVB PD (LiftingTheory.resLoc ι hι T).ρ g x = actVB PD' T.ρ (ι g) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, hact]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem coreCor_of_isOpen [IsTopologicalGroup G'] (PD : PeriodData G Qp K₀ K B BdR)
    (PD' : PeriodData G' Qp K₀' K' B BdR) (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [ι.range.FiniteIndex]
    (hact : ∀ g b, PD.actB g b = PD'.actB (ι g) b) :
    LiftingTheory.coreCor PD PD' LL O ι hι ι.range.index := by
  haveI : Fintype (G' ⧸ ι.range) := Fintype.ofFinite _
  refine ⟨?_, corH1 ι hι he ho, corH1_res ι hι he ho, ?_, corH1_natural ι hι he ho⟩
  · rintro T _ ⟨c, ⟨hc, hc', x, hx⟩, rfl⟩
    have hz := LiftingTheory.resFun_Z1T ι hι T c c.2
    refine ⟨⟨LiftingTheory.resFun ι T c, hz⟩, ⟨hz, hz.1, x, fun g => ?_⟩, rfl⟩
    rw [actVB_res PD PD' ι hι hact]
    exact hx (ι g)
  · rintro T _ ⟨c, ⟨hc, hc', x, hx⟩, rfl⟩
    have hz := trCochain_Z1T ι hι he ho T c c.2
    have hj : ∀ g, Function.invFun ι (ι g) = g := Function.leftInverse_invFun he.injective
    refine ⟨⟨trCochain ι T c, hz⟩,
      ⟨hz, hz.1, ∑ q : G' ⧸ ι.range, actVB PD' T.ρ q.out x, fun g => ?_⟩, rfl⟩
    have h3 := (GlobalTheory.transfer_cocycle_formula LL G' _ (repVB PD' T) ι.range).2.2.1
      (fun g => c.1 (Function.invFun ι g) ⊗ₜ[Qp] (1 : B)) x (by
        rintro _ ⟨a, rfl⟩
        have := hx a
        rw [actVB_res PD PD' ι hι hact] at this
        rw [hj]
        exact this) g
    refine Eq.trans ?_ h3
    change trCochain ι T c g ⊗ₜ[Qp] (1 : B) = _
    rw [trCochain_apply, sum_tmul]
    exact Finset.sum_congr rfl fun q _ => (actVB_tmul_one PD' T _ _).symm

end General

open Formalism.BasicNotions.Loc

theorem GK_index_eq_finrank {l : ℕ} [Fact l.Prime] (K : FinExt l) :
    (GK K).index = Module.finrank ℚ_[l] ↥K.1 :=
  (IntermediateField.finrank_eq_fixingSubgroup_index (Om l) K.1).symm

theorem inclusion_GK_index {l : ℕ} [Fact l.Prime] (K K' : FinExt l) (hle : GK K ≤ GK K') :
    (Subgroup.inclusion hle).range.index * Module.finrank ℚ_[l] ↥K'.1
      = Module.finrank ℚ_[l] ↥K.1 := by
  rw [Subgroup.inclusion_range, ← GK_index_eq_finrank, ← GK_index_eq_finrank]
  exact Subgroup.relIndex_mul_index hle

end GlobalTheory.InducedSectionsSpanStatement

namespace GlobalTheory

open Formalism.BasicNotions.Loc

theorem res_cor_H1f : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    LiftingTheory.adm20 D HW F := by
  intro D HW F l _ K K' _ hle LL
  haveI := K.2
  haveI := K'.2
  have hidx := InducedSectionsSpanStatement.inclusion_GK_index K K' hle
  have hpos : 0 < Module.finrank ℚ_[l] ↥K.1 := Module.finrank_pos
  have hpos' : 0 < Module.finrank ℚ_[l] ↥K'.1 := Module.finrank_pos
  have hg : Module.finrank ℚ_[l] ↥K.1 / Module.finrank ℚ_[l] ↥K'.1
      = (Subgroup.inclusion hle).range.index := by
    rw [← hidx, Nat.mul_div_cancel _ hpos']
  haveI : (Subgroup.inclusion hle).range.FiniteIndex := ⟨fun h => by
    rw [h, zero_mul] at hidx; omega⟩
  rw [hg]
  refine InducedSectionsSpanStatement.coreCor_of_isOpen _ _ _ _ (Topology.IsEmbedding.inclusion hle) ?_ ?_
  · rw [Subgroup.inclusion_range]
    exact (IntermediateField.fixingSubgroup_isOpen K.1).preimage continuous_subtype_val
  · intro g b
    rw [(D.loc l).PD_actB, (D.loc l).PD_actB]
    rfl

end GlobalTheory
