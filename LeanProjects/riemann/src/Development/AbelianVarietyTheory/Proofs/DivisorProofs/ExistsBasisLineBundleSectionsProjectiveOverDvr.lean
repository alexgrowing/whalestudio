import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyPerfectSectionsComplexOfNoetherian
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianVarietyLineBundleSectionsFinite
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbLaw

theorem sec_eq_zero_of_local {X : Scheme.{0}} {L : LB X} {I : Type} (V : I → X.Opens)
    (hc : ⨆ a, V a = ⊤) (c : I → L.ι) (hV : ∀ a, V a ≤ L.U (c a)) (s : LB.Sec L)
    (h : ∀ a, rs X (hV a) (s.f (c a)) = 0) : s = 0 := by
  apply GlobalTheory.LB.f_injective
  funext i
  refine finSec_eq_zero_of_cover V hc (s.f i) fun a => ?_
  have h₁ : rs X (inf_le_left : L.U i ⊓ V a ≤ L.U i) (s.f i) =
      rs X (inf_le_inf le_rfl (hV a) : L.U i ⊓ V a ≤ L.U i ⊓ L.U (c a)) (L.g i (c a)).val *
        rs X (inf_le_right : L.U i ⊓ V a ≤ V a) (rs X (hV a) (s.f (c a))) := by
    have h := congrArg (rs X (inf_le_inf le_rfl (hV a) : L.U i ⊓ V a ≤ L.U i ⊓ L.U (c a)))
      (s.compat i (c a))
    rw [map_mul] at h
    simp only [rs_rs] at h ⊢
    exact h
  rw [h₁, h a, map_zero, mul_zero]

theorem sec_eq_of_local {X : Scheme.{0}} {L : LB X} {I : Type} (V : I → X.Opens)
    (hc : ⨆ a, V a = ⊤) (c : I → L.ι) (hV : ∀ a, V a ≤ L.U (c a)) (s t : LB.Sec L)
    (h : ∀ a, rs X (hV a) (s.f (c a)) = rs X (hV a) (t.f (c a))) : s = t :=
  sub_eq_zero.1 (sec_eq_zero_of_local V hc c hV _ fun a => by rw [GlobalTheory.LB.sub_f, map_sub, h a, sub_self])

section PerfSec

variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
  {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (Q : Perf f M) {g : R →+* R'} {π : X' ⟶ X}
  {f' : X' ⟶ Spec (CommRingCat.of R')}
  (E : {v : Fin Q.a → R' // (Q.D₀.map g).mulVec v = 0} ≃ LB.Sec (M.pull π))

theorem Perf.iSup_preimage : ⨆ i, π ⁻¹ᵁ Q.W i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, Q.cover]
  exact top_unique fun _ _ => trivial

include Q in

theorem Perf.sec_add
    (hE : ∀ v i, rs X' (le_pull M π (Q.le i)) ((E v).f (fun _ => Q.ch i)) =
        ∑ k, cst f' (π ⁻¹ᵁ Q.W i) (v.1 k) * (π.app (Q.W i)).hom (Q.u k i))
    (v w : {v : Fin Q.a → R' // (Q.D₀.map g).mulVec v = 0}) :
    E ⟨v.1 + w.1, by rw [Matrix.mulVec_add, v.2, w.2, add_zero]⟩ = E v + E w := by
  refine sec_eq_of_local (fun i => π ⁻¹ᵁ Q.W i) Q.iSup_preimage (fun i => fun _ => Q.ch i)
    (fun i => le_pull M π (Q.le i)) _ _ fun i => ?_
  refine (hE _ i).trans (Eq.trans ?_ ((map_add (rs X' (le_pull M π (Q.le i))) ((E v).f fun _ => Q.ch i)
    ((E w).f fun _ => Q.ch i)).trans (congrArg₂ (· + ·) (hE v i) (hE w i))).symm)
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

include Q in

theorem Perf.sec_smul
    (hE : ∀ v i, rs X' (le_pull M π (Q.le i)) ((E v).f (fun _ => Q.ch i)) =
        ∑ k, cst f' (π ⁻¹ᵁ Q.W i) (v.1 k) * (π.app (Q.W i)).hom (Q.u k i))
    (r : R') (v : {v : Fin Q.a → R' // (Q.D₀.map g).mulVec v = 0}) :
    E ⟨r • v.1, by rw [Matrix.mulVec_smul, v.2, smul_zero]⟩ = cst f' ⊤ r • E v := by
  refine sec_eq_of_local (fun i => π ⁻¹ᵁ Q.W i) Q.iSup_preimage (fun i => fun _ => Q.ch i)
    (fun i => le_pull M π (Q.le i)) _ _ fun i => ?_
  have key : rs X' (le_pull M π (Q.le i)) (resG X' le_top (cst f' ⊤ r)) = cst f' (π ⁻¹ᵁ Q.W i) r := by
    change rs X' _ (rs X' le_top _) = _
    rw [rs_rs, rs_cst]
  refine (hE _ i).trans (Eq.trans ?_ ((map_mul (rs X' (le_pull M π (Q.le i))) (resG X' le_top (cst f' ⊤ r))
    ((E v).f fun _ => Q.ch i)).trans (congrArg₂ (· * ·) key (hE v i))).symm)
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, _root_.mul_assoc]

end PerfSec

theorem finSecPullId_add {X : Scheme.{0}} {M : LB X} (s t : LB.Sec M) :
    finSecPullId (s + t) = finSecPullId s + finSecPullId t := by
  apply GlobalTheory.LB.f_injective
  funext j
  exact map_add _ _ _

theorem finSecPullId_smul {X : Scheme.{0}} {M : LB X} (a : Γ(X, ⊤)) (s : LB.Sec M) :
    finSecPullId (a • s) = a • finSecPullId s := by
  apply GlobalTheory.LB.f_injective
  funext j
  exact (map_mul _ _ _).trans (congrArg (· * _) (rs_rs _ _ _))

theorem eq_zero_of_finSecPullId {X : Scheme.{0}} {R : Type} [CommRing R]
    {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (Q : Perf f M) (s : LB.Sec M)
    (hs : finSecPullId s = 0) : s = 0 := by
  refine sec_eq_zero_of_local Q.W Q.cover Q.ch Q.le s fun j => ?_
  have hle : Q.W j ≤ (M.pull (𝟙 X)).U (fun _ => Q.ch j) :=
    le_trans (show Q.W j ≤ (𝟙 X) ⁻¹ᵁ Q.W j from fun _ hx => hx) (le_pull M (𝟙 X) (Q.le j))
  have h := congrArg (fun σ : LB.Sec (M.pull (𝟙 X)) => rs X hle (σ.f (fun _ => Q.ch j))) hs
  refine Eq.trans ?_ (h.trans (map_zero (rs X hle)))
  exact (rs_rs _ _ _).symm

end GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem exists_basis_sec_of_isDiscreteValuationRing : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of W)) (M : LB X), Flat f → GlobalTheory.AbLaw.IsProjBy f → M.IsLB → ∃ (n : ℕ) (t : Fin n → LB.Sec M), ∀ u : LB.Sec M, ∃! c : Fin n → W, u = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (c j) • t j := by
  intro W _ _ _ X f M hf hp hM
  obtain ⟨Q⟩ := nonempty_perf_of_noetherian W X f hf hp M hM
  have hpb : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id W))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.id_horiz f
  obtain ⟨E, hE⟩ := Q.sec W (RingHom.id W) X (𝟙 X) f hpb
  let φ : LB.Sec M → Fin Q.a → W := fun s => (E.symm (finSecPullId s)).1
  have hadd : ∀ s t, φ (s + t) = φ s + φ t := by
    intro s t
    have h := Q.sec_add E hE (E.symm (finSecPullId s)) (E.symm (finSecPullId t))
    rw [E.apply_symm_apply, E.apply_symm_apply, ← finSecPullId_add, ← E.eq_symm_apply] at h
    exact (congrArg Subtype.val h).symm
  have hsmul : ∀ (r : W) s, φ (cst f ⊤ r • s) = r • φ s := by
    intro r s
    have h := Q.sec_smul E hE r (E.symm (finSecPullId s))
    rw [E.apply_symm_apply, ← finSecPullId_smul, ← E.eq_symm_apply] at h
    exact (congrArg Subtype.val h).symm
  have φ0 : φ 0 = 0 := by
    have h := hsmul 0 0
    rwa [smul_zero, zero_smul] at h
  have hinj : ∀ s t, φ s = φ t → s = t := by
    intro s t h
    have hst : finSecPullId s = finSecPullId t := E.symm.injective (Subtype.ext h)
    have e := finSecPullId_add (s - t) t
    rw [sub_add_cancel, hst] at e
    have h2 : finSecPullId (s - t) = 0 := add_right_cancel (e.symm.trans (zero_add _).symm)
    exact sub_eq_zero.1 (eq_zero_of_finSecPullId Q _ h2)
  let N : Submodule W (Fin Q.a → W) :=
    { carrier := Set.range φ
      add_mem' := by
        rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
        exact ⟨s + t, hadd s t⟩
      zero_mem' := ⟨0, φ0⟩
      smul_mem' := by
        rintro r _ ⟨s, rfl⟩
        exact ⟨cst f ⊤ r • s, hsmul r s⟩ }
  have memN : ∀ s, φ s ∈ N := fun s => ⟨s, rfl⟩
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun W (Fin Q.a)) N
  have hb : ∀ j, ∃ s, φ s = (b j).1 := fun j => (b j).2
  choose t ht using hb
  let φh : LB.Sec M →+ (Fin Q.a → W) := { toFun := φ, map_zero' := φ0, map_add' := hadd }
  have hsum : ∀ c : Fin n → W, φ (∑ j, cst f ⊤ (c j) • t j) = ∑ j, c j • (b j).1 := by
    intro c
    change φh _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => (hsmul (c j) (t j)).trans (by rw [ht])
  refine ⟨n, t, fun u => ⟨fun j => b.repr ⟨φ u, memN u⟩ j, ?_, ?_⟩⟩
  · apply hinj
    rw [hsum]
    have h := congrArg Subtype.val (b.sum_repr ⟨φ u, memN u⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  · intro c hc
    have h : (⟨φ u, memN u⟩ : N) = ∑ j, c j • b j := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [← hsum, ← hc]
    funext j
    rw [h, Module.Basis.repr_sum_self]

end GlobalTheory.AbLaw
