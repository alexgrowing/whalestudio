import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSkewIdealCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBothStabilisersFixVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerFixesVacuumLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedSphericalVacuumFixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedSphericalVacuumFixedDualStatement
open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)
open scoped Classical

noncomputable section

namespace GlobalTheory.VacFixStab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem evI_eq_zero_of_at {v : Pl F} {a : AF F} (ha : At (evFin F v) a) : evI F a = 0 := by
  rw [← partFin_of_at ha]
  change InfiniteAdeleRing.ringEquiv_mixedSpace F ((GlobalTheory.LatVac.liftV v 1).1 * a.1) = 0
  rw [show (GlobalTheory.LatVac.liftV v 1).1 = 0 from rfl, zero_mul, map_zero]

theorem evFin_eq_zero_of_at {v w : Pl F} (h : w ≠ v) {a : AF F} (ha : At (evFin F v) a) : evFin F w a = 0 := by
  rw [← partFin_of_at ha, partFin, smul_eq_mul, map_mul,
    show evFin F w (GlobalTheory.LatVac.liftV v 1) = 0 from evalV_singleFin_ne h 1, zero_mul]

theorem latAt_le_latHat {n : ℕ} (X : Spc F E n) (v : Pl F) : GlobalTheory.InertSph.latAt X v ≤ latHat X := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro z ⟨a, ha, hint, x, hx, rfl⟩
  refine AddSubgroup.subset_closure ⟨a, evI_eq_zero_of_at ha, fun w => ?_, x, hx, rfl⟩
  by_cases hw : w = v
  · subst hw; exact hint
  · rw [evFin_eq_zero_of_at hw ha]; exact zero_mem _

theorem partFin_mem_latAt {n : ℕ} (X : Spc F E n) (v : Pl F) {z : Fin n → AE F E} (hz : z ∈ latHat X) :
    partFin v z ∈ GlobalTheory.InertSph.latAt X v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, hint, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v 1 * a, at_partFin v a, ?_, x, hx, ?_⟩
    · rw [map_mul, GlobalTheory.LatVac.evFin_liftV, one_mul]; exact hint v
    · rw [partFin, smul_smul]; rfl
  | zero => rw [partFin, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [partFin, smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [partFin, smul_neg]; exact neg_mem hx

theorem at_of_mem_latAt {n : ℕ} (X : Spc F E n) (v : Pl F) {z : Fin n → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt X v) :
    At (evFin F v) z := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, x, -, rfl⟩ := hz
    intro u hu
    rw [smul_smul, ← smul_eq_mul, ha u hu, zero_smul]
  | zero => intro u _; exact smul_zero u
  | add x y _ _ hx hy => intro u hu; rw [smul_add, hx u hu, hy u hu, add_zero]
  | neg x _ hx => intro u hu; rw [smul_neg, hx u hu, neg_zero]

theorem mulVec_mem_latAt {n : ℕ} (X : Spc F E n) (v : Pl F) (m : Matrix (Fin n) (Fin n) (AE F E))
    {z : Fin n → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt X v) (hm : m *ᵥ z ∈ latHat X) :
    m *ᵥ z ∈ GlobalTheory.InertSph.latAt X v := by
  have hat : At (evFin F v) (m *ᵥ z) := fun u hu => by
    rw [← Matrix.mulVec_smul, at_of_mem_latAt X v hz u hu, Matrix.mulVec_zero]
  rw [← partFin_of_at hat]
  exact partFin_mem_latAt X v hm

theorem mem_KAt_of_isStab (B : Base F E) {n : ℕ} {X : Spc F E n} {K : Subgroup (UA σ X.J)} (hK : IsStab B K)
    {v : Pl F} {k : UA σ X.J} (hk : k ∈ KAt K (evFin F v)) : k ∈ GlobalTheory.InertSph.KAt σ X v := by
  obtain ⟨hkK, hkv⟩ := mem_KAt.1 hk
  have hst := ((hK k).1 hkK).2
  exact ⟨hkv, fun z hz => ⟨mulVec_mem_latAt X v _ hz (hst z (latAt_le_latHat X v hz)).1,
    mulVec_mem_latAt X v _ hz (hst z (latAt_le_latHat X v hz)).2⟩⟩

end GlobalTheory.VacFixStab

theorem GlobalTheory.VacFixStab.vac_fixed_both : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {a a' : ℕ} (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ v : Pl F, v ∉ X.T →
    (∀ K : Subgroup (UA σ G.V.J), IsStab B K → ∀ k ∈ KAt K (evFin F v),
      Acts (evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v)) ∧
    (∀ K : Subgroup (UA σ G.V'.J), IsStab B K → ∀ k ∈ KAt K (evFin F v),
      Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv
  rcases GlobalTheory.KFinLoc.split_or_inert F E σ B hT.base v with hs | ⟨w, hw⟩
  · exact ⟨fun K hK k hk => GlobalTheory.T.unramified_spherical_vacuum_fixed F E σ B a a' G X om om' hT v hs hv k (GlobalTheory.VacFixStab.mem_KAt_of_isStab B hK hk),
      fun K hK k hk => GlobalTheory.T.unramified_spherical_vacuum_fixed_dual F E σ B a a' G X om om' hT v hs hv k (GlobalTheory.VacFixStab.mem_KAt_of_isStab B hK hk)⟩
  · exact ⟨fun K hK k hk => GlobalTheory.T.inert_place_both_stabilisers_fix_vacuum F E σ B a a' G X om om' hT v w hw hv k
        (GlobalTheory.VacFixStab.mem_KAt_of_isStab B hK hk) 1 (GlobalTheory.InertSph.one_mem_KAt σ G.W v),
      fun K hK k hk => GlobalTheory.T.inertPlace_stabilizer_fixes_vacuum_left F E σ B a a' G X om om' hT v w hw hv k (GlobalTheory.VacFixStab.mem_KAt_of_isStab B hK hk)⟩
