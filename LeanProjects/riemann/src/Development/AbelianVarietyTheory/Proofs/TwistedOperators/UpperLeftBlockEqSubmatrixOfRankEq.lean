import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LevelGroupLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjectiveOfIndep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionMemCuspFormsOfActionLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelActionCuspFormRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionPreservesIntegralCuspForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeStabilizerIffBasisIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdelicCoordinatesLatticeMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupMatrixIsomorphism
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankOneBaseWeightEqCmTheta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalLevelEqHalfMarkingStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelAtEachIndex
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.Pj
  Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoActRoad

section Lattice

variable {D : D7} {V : HSp D}

variable {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}

theorem le_of_half {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : Level H} {Pg : Finset (Pl D.host.E)}
    (h : l.Mb = ∏ w ∈ Pg, w.asIdeal) {w : Pl D.host.E} (hw : w ∈ Pg) : l.Mb ≤ w.asIdeal :=
  h.le.trans (Ideal.prod_le_inf.trans (Finset.inf_le hw))

theorem exists_coord {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {I : Ideal (𝓞 E)}
    (hI : I ≠ ⊥) {M : ℕ} (hM : (M : 𝓞 E) ∈ I) {La : Type} [AddCommGroup La] [Module (𝓞 E) La]
    (ρ : La →+ (Fin n → Formalism.L2.Herm.intAf F E)) (h1 : ∀ (b : 𝓞 E) a, ρ (b • a) = oToS F E b • ρ a)
    (h2 : ∀ s, ∃ a s', s = ρ a + M • s') (h3 : ∀ a, (∀ i, ρ a i ∈ idS F I) → a ∈ I • (⊤ : Submodule (𝓞 E) La)) :
    ∃ φ : (La ⧸ I • (⊤ : Submodule (𝓞 E) La)) ≃ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ I),
      ∀ a i, φ (Submodule.Quotient.mk a) i = GlobalTheory.GeoActCompare.resI F I hI (ρ a i) := by
  let φ₀ : La →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ I) :=
    { toFun := fun a i => GlobalTheory.GeoActCompare.resI F I hI (ρ a i)
      map_add' := fun a b => funext fun i => by rw [map_add, Pi.add_apply, map_add]; rfl
      map_smul' := fun b a => funext fun i => by
        rw [h1, Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.GeoActCompare.resI_oToS]
        exact (Algebra.smul_def _ _).symm }
  have hs : Function.Surjective φ₀ := fun t => by
    choose u hu using fun i => Ideal.Quotient.mk_surjective (t i)
    obtain ⟨a, s', e⟩ := h2 fun i => oToS F E (u i)
    refine ⟨a, funext fun i => ?_⟩
    have e1 := congrArg (GlobalTheory.GeoActCompare.resI F I hI) (congrFun e i)
    have e2 : ((M : ℕ) : 𝓞 E ⧸ I) = 0 := by rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem.2 hM]
    rw [GlobalTheory.GeoActCompare.resI_oToS, hu, Pi.add_apply, map_add, Pi.smul_apply, map_nsmul, nsmul_eq_mul, e2, zero_mul,
      add_zero] at e1
    exact e1.symm
  have hk : I • (⊤ : Submodule (𝓞 E) La) = LinearMap.ker φ₀ := by
    refine le_antisymm (Submodule.smul_le.2 fun b hb a _ => ?_) fun a ha => h3 a fun i => ?_
    · rw [LinearMap.mem_ker, map_smul]
      funext i
      rw [Pi.smul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hb, zero_mul]
      rfl
    · exact (GlobalTheory.GeoActCompare.resI_eq_zero_iff _ hI _).1 (congrFun ha i)
  exact ⟨(Submodule.quotEquivOfEq _ _ hk).trans (φ₀.quotKerEquivOfSurjective hs), fun _ _ => rfl⟩

end Lattice

section Group

variable {D : D7} {V : HSp D} (β : GL (Fin V.rank) (EAf D))

def stab : Subgroup (GA D V) := GfC V ⊓ (St β).comap (finE V)

def redTup (Pg : Finset (Pl D.host.E)) : stab β →* Formalism.L2.DIV.G0 Pg V.rank where
  toFun k := fun w => redFn β w.1 (finE V k)
  map_one' := funext fun w => by
    show redFn β w.1 (finE V 1) = 1
    rw [map_one, redFn_one]
  map_mul' k k' := funext fun w => by
    show redFn β w.1 (finE V (k * k')) = redFn β w.1 (finE V k) * redFn β w.1 (finE V k')
    rw [map_mul, redFn_mul k.2.2 k'.2.2]

def fullDat (n : ℕ) (Pg : Finset (Pl D.host.E)) : LevDat D.host.E ℂ n :=
  ⟨n, le_rfl, 1, 0, Pg, ∅, LevelP.triv _ _ _, fun _ _ => 1, fun _ => 1⟩

variable {β} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

theorem liftsExist_of_half (hβ : IsSDFrame V β Λ 1) (l : Level H) (L : LevDat D.host.E ℂ V.rank) (hQ : L.Q = ∅)
    (h : l.Mb = ∏ w ∈ L.Pg, w.asIdeal) : LiftsExist V β L := by
  obtain ⟨c, hc⟩ := hβ
  refine GlobalTheory.ParahoricLift.liftsExist _ _ _ _ _ hc (fun PP h1 PP' h' => ?_) (hQ ▸ Finset.disjoint_empty_right _)
  rcases h' with h' | h'
  · exact GlobalTheory.LevelAction.not_isConjPl l (le_of_half h h1) (le_of_half h h')
  · exact absurd (hQ ▸ h') (Finset.notMem_empty _)

end Group

section Record

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

open Classical in

theorem exists_half_prod {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H) (hM : l.M = D.host.g 0 * D.host.g 1) :
    (∀ Pg : Finset (Pl D.host.E), (∀ w, w ∈ Pg ↔ l.Mb ≤ w.asIdeal) → l.Mb = ∏ w ∈ Pg, w.asIdeal) ∧
      ∃ Pg : Finset (Pl D.host.E), l.Mb = ∏ w ∈ Pg, w.asIdeal := by
  have hprod := l.prod
  rw [hM] at hprod
  have hs : Squarefree l.Mb := (hprod ▸ GlobalTheory.CoverHalf.squarefree_span_g D : Squarefree (l.Mb * _)).of_mul_left
  refine ⟨fun Pg h => GlobalTheory.CoverHalf.eq_prod_of_squarefree hs _ h,
    (Ideal.finite_factors hs.ne_zero).toFinset, GlobalTheory.CoverHalf.eq_prod_of_squarefree hs _ fun w => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le]

theorem mem_Pg_iff {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (w : Pl D.host.E) :
    w ∈ L.Pg ↔ (GlobalTheory.HalfOnRecord.designLevel L.C.P).Mb ≤ w.asIdeal := by
  rw [hL.Pg, GlobalTheory.HalfOnRecord.designLevel_Mb, GlobalTheory.CoverHalf.prod_map_le_iff]
  rfl

theorem designLevel_prod {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) :
    (GlobalTheory.HalfOnRecord.designLevel L.C.P).Mb = ∏ w ∈ L.Pg, w.asIdeal :=
  (exists_half_prod _ rfl).1 _ (mem_Pg_iff hL)

theorem levelLiftsExist_gridVertexSpaces {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (i : Fin D.R.m) :
    LiftsExist (Wc D i) (L.βW i) (L.datWp i L.triv) :=
  liftsExist_of_half (hL.βW i) (GlobalTheory.HalfOnRecord.designLevel L.C.P) _ rfl (designLevel_prod hL)

theorem exists_root {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (i : Fin D.R.m) {g : Formalism.L2.DIV.G0 L.Pg D.R.r} {k : GA D (Wc D i)}
    (hk : IsLevelLift (Wc D i) (L.βW i) (L.datWp i L.triv) g k) :
    ∃ x, FinUnit x ∧ IsDetRoot (Wc D i) k x ∧
      (∏ P : L.Pg, ((L.chi ((i : ℕ) + 1) P.1 (Matrix.GeneralLinearGroup.det (g P)) : ℂˣ) : ℂ)) *
        ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = 1 := by
  obtain ⟨a, b, s, s', hb, hs, hs', hin, hout⟩ :=
    GlobalTheory.GeoLevel.exists_half_elements (GlobalTheory.HalfOnRecord.designLevel L.C.P) L.Pg (mem_Pg_iff hL)
  obtain ⟨x, h1, h2, h3⟩ := GlobalTheory.GeoLevel.exists_root_char (L := L.datWp i L.triv) (rank_Wc i).symm hk (hL.mu0 i)
    (L.C.isMu0 i).tame (D.host.g 0 * D.host.g 1) (fun P hP => (L.C.isMu0 i).unr P fun k hk => hP (by
      rw [Nat.cast_mul]
      fin_cases k
      · exact Ideal.mul_mem_right _ _ hk
      · exact Ideal.mul_mem_left _ _ hk))
    (fun P => (L.chi ((i : ℕ) + 1) P)⁻¹) (hL.chi i) a b s s' hb hs hs' hin hout
  refine ⟨x, h1, h2, ?_⟩
  rw [h3]
  refine (Finset.prod_mul_distrib (s := (Finset.univ : Finset L.Pg))).symm.trans (Finset.prod_eq_one fun P _ => ?_)
  rw [← Units.val_mul, MonoidHom.inv_apply]
  exact congrArg Units.val (mul_inv_cancel _)

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

end Record

section Main

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

open GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts (LevGrp IsGeoRep UnitConstEquivariant)
open GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv (Cusp IsGeo ReadTwist KeepsIntegral ConstEquiv GeoActAt)

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}

end Main

end GlobalTheory.GeoActRoad
