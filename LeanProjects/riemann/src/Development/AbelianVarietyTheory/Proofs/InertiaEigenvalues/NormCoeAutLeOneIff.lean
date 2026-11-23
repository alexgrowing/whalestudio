import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

namespace GlobalTheory.EigenCoord

theorem exists_basis_mem_iff {O L V : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L]
    [IsFractionRing O L] [AddCommGroup V] [Module L V] [Module O V] [IsScalarTower O L V]
    (T : Submodule O V) (hfg : T.FG) (hfree : Module.Free O T)
    (hspan : Submodule.span L (T : Set V) = ⊤) :
    ∃ (ρ : ℕ) (t : Module.Basis (Fin ρ) L V),
      ∀ v, v ∈ T ↔ ∀ i, ∃ o : O, algebraMap O L o = t.repr v i := by
  haveI : Module.Finite O T := Module.Finite.iff_fg.mpr hfg
  let c := Module.finBasis O T
  have hli : LinearIndependent O (fun i => (c i : V)) :=
    c.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hli' : LinearIndependent L (fun i => (c i : V)) :=
    (LinearIndependent.iff_fractionRing O L).mp hli
  have hsum : ∀ x : T, (x : V) = ∑ i, algebraMap O L (c.repr x i) • (c i : V) := by
    intro x
    have h := congrArg T.subtype (c.sum_repr x)
    rw [map_sum] at h
    simp only [map_smul, Submodule.subtype_apply] at h
    simp only [algebraMap_smul]
    exact h.symm
  have hsp : ⊤ ≤ Submodule.span L (Set.range fun i => (c i : V)) := by
    rw [← hspan, Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, show x = ((⟨x, hx⟩ : T) : V) from rfl, hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let t := Module.Basis.mk hli' hsp
  have ht : ∀ i, t i = (c i : V) := fun i => Module.Basis.mk_apply hli' hsp i
  refine ⟨_, t, fun v => ⟨fun hv i => ⟨c.repr ⟨v, hv⟩ i, ?_⟩, fun h => ?_⟩⟩
  · have h1 : v = ∑ j, algebraMap O L (c.repr ⟨v, hv⟩ j) • t j := by
      simp only [ht]
      exact hsum ⟨v, hv⟩
    have h2 := congrFun (t.repr_sum_self (fun j => algebraMap O L (c.repr ⟨v, hv⟩ j))) i
    rw [← h1] at h2
    exact h2.symm
  · choose o ho using h
    rw [← t.sum_repr v]
    refine T.sum_mem fun i _ => ?_
    rw [← ho, algebraMap_smul, ht]
    exact T.smul_mem _ (c i).2

theorem norm_coe_aut_le_one_iff {l : ℕ} [Fact l.Prime] (ι : GQ l) (x : Om l) :
    ‖((ι x : Om l) : PadicComplex l)‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplex.norm_extends, ← isIntegral_padicInt_iff_norm_le_one,
    ← isIntegral_padicInt_iff_norm_le_one]
  exact isIntegral_algHom_iff (ι.toAlgHom.restrictScalars ℤ_[l]) ι.injective

theorem exists_matrix_of_basis {F L C V : Type} [NormedField F] [Field L] [NormedField C]
    [Algebra F L] [Algebra F C] [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    (S : Set V) {d ρ : ℕ} (b : Module.Basis (Fin d) F V) (t : Module.Basis (Fin ρ) L V)
    (φ : L →ₐ[F] C) (hb : ∀ v, v ∈ S ↔ ∀ i, ‖b.repr v i‖ ≤ 1)
    (hmem : ∀ v, v ∈ S ↔ ∀ i, ‖φ (t.repr v i)‖ ≤ 1) :
    ∃ Pr : Matrix (Fin ρ) (Fin d) C, (∀ i j, ‖Pr i j‖ ≤ 1) ∧
      (∀ a : L, Pr * Matrix.of (fun i k : Fin d => algebraMap F C (b.repr (a • b k) i)) =
        φ a • Pr) ∧
      ∀ y : Fin d → F, (∀ i, ‖Pr.mulVec (fun a => algebraMap F C (y a)) i‖ ≤ 1) →
        ∀ a, ‖y a‖ ≤ 1 := by
  have key : ∀ (y : Fin d → F) (i : Fin ρ),
      ∑ j, φ (t.repr (b j) i) * algebraMap F C (y j) = φ (t.repr (∑ j, y j • b j) i) := by
    intro y i
    rw [map_sum, Finsupp.finset_sum_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul L (y j), map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
      AlgHom.commutes, mul_comm]
  refine ⟨Matrix.of fun i j => φ (t.repr (b j) i), fun i j => ?_, fun a => ?_, fun y hy a => ?_⟩
  · refine (hmem _).mp ((hb _).mpr fun k => ?_) i
    rw [b.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  · ext i k
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Matrix.smul_apply]
    rw [key, b.sum_repr, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, smul_eq_mul]
  · have hv : (∑ j, y j • b j) ∈ S := by
      refine (hmem _).mpr fun i => ?_
      rw [← key]
      exact hy i
    have := (hb _).mp hv a
    rwa [congrFun (b.repr_sum_self y) a] at this

theorem exists_matrix : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (b : Module.Basis (Fin d) ℚ_[l] T.V), (∀ v : T.V, v ∈ T.L.T ↔ ∀ i, ‖b.repr v i‖ ≤ 1) → ∀ ι : GQ l, ∃ (ρ : ℕ) (Pr : Matrix (Fin ρ) (Fin d) (PadicComplex l)), (∀ i j, ‖Pr i j‖ ≤ 1) ∧ (∀ a : ↥LL.1, Pr * Matrix.of (fun i k : Fin d => algebraMap ℚ_[l] (PadicComplex l) (b.repr (a • b k) i)) = ((ι (a : Om l) : Om l) : PadicComplex l) • Pr) ∧ ∀ y : Fin d → ℚ_[l], (∀ i, ‖Pr.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) i‖ ≤ 1) → ∀ a, ‖y a‖ ≤ 1 := by
  intro l _ K LL T d b hb ι
  haveI := LL.2
  haveI : IsFractionRing (OL LL) LL.1 := isFractionRing_integralClosure_padicInt l LL.1
  obtain ⟨ρ, t, ht⟩ := exists_basis_mem_iff (L := LL.1) T.L.T T.L.fg T.L.free T.L.span
  let φ : LL.1 →ₐ[ℚ_[l]] PadicComplex l :=
    (IsScalarTower.toAlgHom ℚ_[l] (Om l) (PadicComplex l)).comp (ι.toAlgHom.comp LL.1.val)
  have hφ : ∀ x : LL.1, φ x = ((ι (x : Om l) : Om l) : PadicComplex l) := fun _ => rfl
  have hmem : ∀ v, v ∈ T.L.T ↔ ∀ i, ‖φ (t.repr v i)‖ ≤ 1 := by
    intro v
    rw [ht]
    refine forall_congr' fun i => ?_
    rw [hφ, norm_coe_aut_le_one_iff, ← mem_integralClosure_padicInt_iff]
    exact ⟨fun ⟨o, ho⟩ => ho ▸ o.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  exact ⟨ρ, exists_matrix_of_basis (T.L.T : Set T.V) b t φ hb hmem⟩

end GlobalTheory.EigenCoord
