import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsComplAtPowerSeriesC
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCDvrTwoEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureMapEqOfSameGenericImageModuliStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalLatticeIdentificationEqIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFibrePowerPointEqOfMatchingLowerDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalCoordsEqOfMatchingDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseOfRefinesPolarisedDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseOfPullbackInjectiveDomainsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointMapOverRingHomUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbacksMatchTorsionPairsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRefinementTautologicalChartFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapCompEqOfCompInjectiveLocalSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodPartMemTautologicalPointTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalPointTransportFieldMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointPairsLowerBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section
namespace GlobalTheory.TInj

theorem tautChart_eq_of_genPt : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left), C.IsFam F G₁ y α₁ → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (θ₁ θ₂ : C.R →+* R'), IsCN R' → Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ (κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing C.R)), κ₁ ≫ jK C.R = jK R' ≫ spMap θ₁ → κ₂ ≫ jK C.R = jK R' ≫ spMap θ₂ → κ₁ ≫ y = κ₂ ≫ y → spMap (θ₁.comp C.iw) ≫ C.u = spMap (θ₂.comp C.iw) ≫ C.u ∧ (θ₁.comp C.iw = θ₂.comp C.iw → ∀ k, θ₁ (C.s k) = θ₂ (C.s k)) := by
  intro g n φ hn F C G₁ _ _ y α₁ hC R' _ _ _ θ₁ θ₂ hR' hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨hsa, -, -, hM, hys⟩ := hC
  have hn1 : 1 ≤ n := by omega
  have hCN : IsCN C.R := hM.isCN
  obtain ⟨R₁, _, _, _, ρ, D, e', hR₁, hρ, hρf, hρl, href⟩ := GlobalTheory.T.exists_refinement_tautologicalChart_finiteExtension hn1 C hCN
  obtain ⟨β, ββ, w, hFrom⟩ := GlobalTheory.T.comesFromBase_of_refines_polarisedData C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n C.R R₁ ρ C.iw C.s C.Q C.e D.toPre e' hρ C.data href
  obtain ⟨G₀, _, _, π, A₀, U₀, hU⟩ := hM.unif R₁ ρ hR₁ hρ hρf D e' href
  obtain ⟨hπ, κρ, πK, α₀, α₂, hκρ, -, hA, hsq, hL, -⟩ := hU
  have hsa₀ : IsSemiAbelian G₀ := GlobalTheory.Mum.EvenDesc.isSemiAbelian_of_isGrpPullback hπ hsa
  obtain ⟨V, _, _, _, _, η', f₁, f₂, hVc, hη', hf₁, hf₂, hlf₁, hlf₂, hc₁, hc₂⟩ :=
    exists_cDvr_two_embeddings C.R R₁ R' ρ hρ hρf hR' θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂
  obtain ⟨κf₁, hκf₁⟩ := exists_genericMap hf₁
  obtain ⟨κf₂, hκf₂⟩ := exists_genericMap hf₂
  obtain ⟨κη, hκη⟩ := exists_genericMap hη'
  have e₁ : κf₁ ≫ κρ = κη ≫ κ₁ := GlobalTheory.T.genericPointMap_over_ringHom_unique (f₁.comp ρ) _ _
    (by rw [Category.assoc, hκρ, ← Category.assoc, hκf₁, Category.assoc, ← spMap_comp])
    (by rw [Category.assoc, hκ₁, ← Category.assoc, hκη, Category.assoc, ← spMap_comp, hc₁])
  have e₂ : κf₂ ≫ κρ = κη ≫ κ₂ := GlobalTheory.T.genericPointMap_over_ringHom_unique (f₂.comp ρ) _ _
    (by rw [Category.assoc, hκρ, ← Category.assoc, hκf₂, Category.assoc, ← spMap_comp])
    (by rw [Category.assoc, hκ₂, ← Category.assoc, hκη, Category.assoc, ← spMap_comp, hc₂])
  have hy₀ : κf₁ ≫ (κρ ≫ y) = κf₂ ≫ (κρ ≫ y) := by
    rw [← Category.assoc, e₁, Category.assoc, hy, ← Category.assoc, ← e₂, Category.assoc]
  have hmap : ∀ f : R₁ →+* V, IsLocalHom f → (maximalIdeal R₁).map f ≤ maximalIdeal V := fun f hf =>
    Ideal.map_le_iff_le_comap.mpr fun x hx => (mem_maximalIdeal _).2 (map_nonunit f x ((mem_maximalIdeal _).1 hx))
  haveI : CharZero R₁ := hR₁.2.2.2
  obtain ⟨D₁, D₂, hD₁, hD₂, j₁, j₂, b, φ', hE₁, hE₂, hMatch, hpairs⟩ :=
    GlobalTheory.T.uniformisation_pullbacks_match_torsionPairs F.univ (GlobalTheory.LowChart.isUnit_zetaAway n hn) hn1 R₁ (maximalIdeal R₁)
      ⟨hR₁.1, inferInstance, hR₁.2.1, hR₁.2.2.1⟩ D A₀ G₀ U₀ hsa₀ (κρ ≫ y) α₀ ⟨hA, α₂, hsq, hL⟩ V hVc f₁ f₂ hf₁ hf₂
      (hmap f₁ hlf₁) (hmap f₂ hlf₂) κf₁ κf₂ hκf₁ hκf₂ hy₀
  obtain ⟨ββ₁, w₁, hFrom₁⟩ := GlobalTheory.T.comesFromBase_of_pullback_injective_domains C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n R₁ V
    (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₁ D₁.toPre hD₁ hf₁ hFrom
  obtain ⟨ββ₂, w₂, hFrom₂⟩ := GlobalTheory.T.comesFromBase_of_pullback_injective_domains C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n R₁ V
    (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₂ D₂.toPre hD₂ hf₂ hFrom
  have hne₀ : ∀ k, ρ (C.s k) ≠ 0 := fun k => (map_ne_zero_iff ρ hρ).2 (C.s_ne_zero k)
  have htaut : ∀ a : Fin C.T.r → ℤ, ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) n)
      (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) n),
      p₁.y = (hD₁.xe.trans (e'.trans C.e)).symm a ∧
      TautPt C.T (f₁.comp (ρ.comp C.iw)) (fun k => f₁ (ρ (C.s k))) (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n
        D₁.toPre (hD₁.xe.trans (e'.trans C.e)) ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
        (AlgebraicClosure (FractionRing V)) a p₁.g ∧
      p₂.y = (hD₂.xe.trans (e'.trans C.e)).symm a ∧
      TautPt C.T (f₂.comp (ρ.comp C.iw)) (fun k => f₂ (ρ (C.s k))) (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n
        D₂.toPre (hD₂.xe.trans (e'.trans C.e)) ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂
        (AlgebraicClosure (FractionRing V)) a p₂.g ∧ QImg b φ' p₁ p₂ := by
    intro a
    obtain ⟨p₀, hp₀y, hp₀⟩ := GlobalTheory.T.periodPart_mem_tautologicalPoint_torsion C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n R₁ D.toPre
      (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w D.tau_bimult hFrom hne₀
      (AlgebraicClosure (FractionRing R₁)) a
    obtain ⟨p₁, p₂, hp₁y, hTr₁, hp₂y, hTr₂, hQ⟩ := hpairs p₀
    refine ⟨p₁, p₂, ?_, ?_, ?_, ?_, hQ⟩
    · rw [hp₁y, hp₀y]; rfl
    · exact GlobalTheory.T.tautologicalPoint_transport_fieldMap C.T _ n R₁ V (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₁
        D₁.toPre hD₁ ββ₁ w₁ hf₁ D₁.tau_bimult hFrom hFrom₁ _ _ j₁ hE₁ a p₀.g p₁.g hp₀ hTr₁
    · rw [hp₂y, hp₀y]; rfl
    · exact GlobalTheory.T.tautologicalPoint_transport_fieldMap C.T _ n R₁ V (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₂
        D₂.toPre hD₂ ββ₂ w₂ hf₂ D₂.tau_bimult hFrom hFrom₂ _ _ j₂ hE₂ a p₀.g p₂.g hp₀ hTr₂
  have hlev := GlobalTheory.T.exists_level_point_pairs_lower_base C.toLowBase hn1 R₁ V (maximalIdeal R₁) (maximalIdeal V) D D₁ D₂ (ρ.comp C.iw) β hFrom.1
    f₁ f₂ hD₁ hD₂ (AlgebraicClosure (FractionRing R₁)) (AlgebraicClosure (FractionRing V)) j₁ j₂ b φ' hE₁ hE₂ hpairs
  have hloc : ∀ f : R₁ →+* V, IsLocalHom f → ∀ x, x ∈ maximalIdeal C.R → f (ρ x) ∈ maximalIdeal V := fun f hf x hx =>
    (mem_maximalIdeal _).2 (map_nonunit f _ (map_nonunit ρ x ((mem_maximalIdeal _).1 hx)))
  have hbd₁ : ∀ k, f₁ (ρ (C.s (.inl k))) ∈ maximalIdeal V ∧ f₁ (ρ (C.s (.inl k))) ≠ 0 := fun k =>
    ⟨hloc f₁ hlf₁ _ (C.bd k), (map_ne_zero_iff f₁ hf₁).2 (hne₀ _)⟩
  have hbd₂ : ∀ k, f₂ (ρ (C.s (.inl k))) ∈ maximalIdeal V ∧ f₂ (ρ (C.s (.inl k))) ≠ 0 := fun k =>
    ⟨hloc f₂ hlf₂ _ (C.bd k), (map_ne_zero_iff f₂ hf₂).2 (hne₀ _)⟩
  have hu₁ : ∀ k, IsUnit (f₁ (ρ (C.s (.inr k)))) := fun k => ((C.tor k).map ρ).map f₁
  have hu₂ : ∀ k, IsUnit (f₂ (ρ (C.s (.inr k)))) := fun k => ((C.tor k).map ρ).map f₂
  have hfin1 := GlobalTheory.T.tautological_lattice_identification_eq_id C.T φ C.m C.N n (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) hn C.cone C.defin V
    D₁.toPre D₂.toPre (f₁.comp (ρ.comp C.iw)) (fun k => f₁ (ρ (C.s k))) (hD₁.xe.trans (e'.trans C.e))
    ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
    (f₂.comp (ρ.comp C.iw)) (fun k => f₂ (ρ (C.s k))) (hD₂.xe.trans (e'.trans C.e))
    ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂ b φ' (AlgebraicClosure (FractionRing V))
    D₁.tau_bimult D₂.tau_bimult hFrom₁ hFrom₂ hbd₁ hu₁ hbd₂ hu₂ hMatch htaut
  have hb := GlobalTheory.T.structureMap_eq_of_same_genericImage_moduli F.s y C.b hys θ₁ θ₂ κ₁ κ₂ hκ₁ hκ₂ hy
  have k₁ : f₁.comp (ρ.comp C.iw) = η'.comp (θ₁.comp C.iw) := by
    rw [← RingHom.comp_assoc, hc₁, RingHom.comp_assoc]
  have k₂ : f₂.comp (ρ.comp C.iw) = η'.comp (θ₂.comp C.iw) := by
    rw [← RingHom.comp_assoc, hc₂, RingHom.comp_assoc]
  have hbase : (f₁.comp (ρ.comp C.iw)).comp C.toLowBase.T.b = (f₂.comp (ρ.comp C.iw)).comp C.toLowBase.T.b := by
    rw [k₁, k₂]
    change η'.comp (θ₁.comp C.b) = η'.comp (θ₂.comp C.b)
    rw [hb]
  obtain ⟨hU', hβeq⟩ := GlobalTheory.T.siegelFibrePower_point_eq_of_matching_lower_data C.toLowBase hn (GlobalTheory.LowChart.isUnit_zetaAway n hn) (isUnit_natCast (by omega))
    (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) V
    D₁.toPre D₂.toPre (f₁.comp (ρ.comp C.iw)) (fun k => f₁ (ρ (C.s k))) (hD₁.xe.trans (e'.trans C.e))
    ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
    (f₂.comp (ρ.comp C.iw)) (fun k => f₂ (ρ (C.s k))) (hD₂.xe.trans (e'.trans C.e))
    ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂ b φ' (AlgebraicClosure (FractionRing V))
    D₁.tau_bimult D₂.tau_bimult hFrom₁ hFrom₂ hbase hMatch hfin1 htaut hlev
  refine ⟨GlobalTheory.T.specMap_comp_eq_of_comp_injective_localScheme C.u (θ₁.comp C.iw) (θ₂.comp C.iw) η' hη' (by rw [← k₁, ← k₂]; exact hU'), fun heq k => ?_⟩
  have hω : f₁.comp (ρ.comp C.iw) = f₂.comp (ρ.comp C.iw) := by rw [k₁, k₂, heq]
  have hβ₂ := hβeq hω
  rw [← hω] at hFrom₂ htaut
  have hs := GlobalTheory.T.tautological_coords_eq_of_matching_data C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n V (f₁.comp (ρ.comp C.iw))
    D₁.toPre D₂.toPre (fun k => f₁ (ρ (C.s k))) (hD₁.xe.trans (e'.trans C.e))
    ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
    (fun k => f₂ (ρ (C.s k))) (hD₂.xe.trans (e'.trans C.e))
    ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂ b φ' (AlgebraicClosure (FractionRing V))
    hn1 ⟨C.ε, fun _ => rfl⟩ D₁.tau_bimult D₂.tau_bimult hFrom₁ hFrom₂ (fun k => (map_ne_zero_iff f₁ hf₁).2 (hne₀ k))
    (fun k => (map_ne_zero_iff f₂ hf₂).2 (hne₀ k)) hMatch hfin1 hβ₂ htaut
  have h1 := congrFun hs k
  have h2 := DFunLike.congr_fun hc₁ (C.s k)
  have h3 := DFunLike.congr_fun hc₂ (C.s k)
  simp only [RingHom.comp_apply] at h1 h2 h3
  exact hη' (by rw [← h2, ← h3]; exact h1)

end GlobalTheory.TInj
