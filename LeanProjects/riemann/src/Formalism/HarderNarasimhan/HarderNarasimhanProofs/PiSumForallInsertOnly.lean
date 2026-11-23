import Formalism.HarderNarasimhan.DegSupermodZ
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermod
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
import Formalism.LatticeSlopes.LatticeSlopesProofs.ShortVector

open Module Submodule

noncomputable section

namespace Formalism.HN

section

variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

def piSum_emb (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    (i : ι) : E i →ₗ[ℝ] PiLp 2 E :=
  (WithLp.linearEquiv 2 ℝ (∀ j, E j)).symm.toLinearMap.comp (LinearMap.single ℝ E i)

theorem piSum_emb_apply (i : ι) (v : E i) (j : ι) : (piSum_emb E i v) j = Pi.single i v j := rfl

theorem piSum_emb_inner (i : ι) (u v : E i) :
    inner ℝ (piSum_emb E i u) (piSum_emb E i v) = inner ℝ u v := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · rw [piSum_emb_apply, piSum_emb_apply, Pi.single_eq_same, Pi.single_eq_same]
  · intro j _ hj
    rw [piSum_emb_apply, piSum_emb_apply, Pi.single_eq_of_ne hj, inner_zero_left]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem piSum_emb_injective (i : ι) : Function.Injective (piSum_emb E i) := by
  intro u v h
  have h' := congrArg (fun x : PiLp 2 E => x i) h
  simpa [piSum_emb_apply] using h'

variable (ρ : ∀ i, V i →+ E i)

private theorem piLp_ext {x y : PiLp 2 E} (h : ∀ j, x j = y j) : x = y := by
  exact PiLp.ext h

private theorem piReal_apply (ρ : ∀ i, V i →+ E i) (x : ∀ i, V i) (j : ι) :
    piReal ρ x j = ρ j (x j) := by
  rfl

theorem piSum_piReal_single (i : ι) (x : V i) :
    piReal ρ (LinearMap.single R V i x) = piSum_emb E i (ρ i x) := by
  refine piLp_ext fun j => ?_
  rw [piReal_apply, piSum_emb_apply]
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

theorem piSum_zl_single (i : ι) (N : Submodule R (V i)) :
    zl (piReal ρ) (N.map (LinearMap.single R V i)) =
      (zl (ρ i) N).map ((piSum_emb E i).restrictScalars ℤ) := by
  ext y
  rw [hnSum_mem_zl (piReal ρ) (N.map (LinearMap.single R V i)) y,
    Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hx
    exact ⟨ρ i v, (hnSum_mem_zl (ρ i) N (ρ i v)).2 ⟨v, hv, rfl⟩,
      (piSum_piReal_single ρ i v).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv, rfl⟩ := (hnSum_mem_zl (ρ i) N w).1 hw
    exact ⟨LinearMap.single R V i v, Submodule.mem_map_of_mem hv, piSum_piReal_single ρ i v⟩

variable [∀ i, FiniteDimensional ℝ (E i)]

theorem piSum_transfer (i : ι) (M : Submodule ℤ (E i)) [DiscreteTopology M] :
    DiscreteTopology (M.map ((piSum_emb E i).restrictScalars ℤ)) ∧
    Formalism.F.rk (M.map ((piSum_emb E i).restrictScalars ℤ)) = Formalism.F.rk M ∧
    Formalism.F.covol (M.map ((piSum_emb E i).restrictScalars ℤ)) = Formalism.F.covol M := by
  have hfi : Function.Injective ((piSum_emb E i).restrictScalars ℤ) := piSum_emb_injective i
  let e := Submodule.equivMapOfInjective _ hfi M
  have he : ∀ x : M, ((e x : M.map ((piSum_emb E i).restrictScalars ℤ)) : PiLp 2 E) =
      piSum_emb E i x := by
    intro x
    rfl
  have key : ∀ y : M.map ((piSum_emb E i).restrictScalars ℤ),
      ((e.symm y : M) : E i) = (y : PiLp 2 E) i := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [LinearEquiv.symm_apply_apply]
    rw [he, piSum_emb_apply, Pi.single_eq_same]
  have hcoord : Continuous fun y : M.map ((piSum_emb E i).restrictScalars ℤ) => (y : PiLp 2 E) i := by
    exact (PiLp.continuous_apply 2 E i).comp continuous_subtype_val
  have hc : Continuous fun y : M.map ((piSum_emb E i).restrictScalars ℤ) => e.symm y :=
    continuous_induced_rng.2 (hcoord.congr fun y => (key y).symm)
  have hdisc : DiscreteTopology (M.map ((piSum_emb E i).restrictScalars ℤ)) := by
    exact DiscreteTopology.of_continuous_injective hc e.symm.injective
  refine ⟨hdisc, ?_, ?_⟩
  · exact (LinearEquiv.finrank_eq e).symm
  · refine Formalism.F.covol_eq_of_linearEquiv_inner M _ e fun x y => ?_
    rw [he, he]
    exact piSum_emb_inner i (x : E i) (y : E i)

theorem piSum_single (i : ι) (N : Submodule R (V i)) (hN : IsLat (ρ i) N) :
    IsLat (piReal ρ) (N.map (LinearMap.single R V i)) ∧
    rk (piReal ρ) (N.map (LinearMap.single R V i)) = rk (ρ i) N ∧
    deg (piReal ρ) (N.map (LinearMap.single R V i)) = deg (ρ i) N := by
  have himg := piSum_zl_single ρ i N
  have := hN.2
  obtain ⟨hd, hr, hc⟩ := piSum_transfer i (zl (ρ i) N)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hy
    rw [piSum_piReal_single, piSum_piReal_single] at hxy
    rw [hN.1 ha hb (piSum_emb_injective i hxy)]
  · rw [himg]
    exact hd
  · unfold rk
    rw [himg]
    exact hr
  · unfold deg
    rw [himg]
    unfold Formalism.F.deg
    rw [hc]

def piSumS (L : ∀ i, Submodule R (V i)) (i : ι) : Submodule R (∀ i, V i) :=
  (L i).map (LinearMap.single R V i)

def piSumT (L : ∀ i, Submodule R (V i)) (s : Finset ι) : Submodule R (∀ i, V i) :=
  ⨆ i ∈ s, piSumS L i

private theorem linearMap_single_injective (i : ι) : Function.Injective (LinearMap.single R V i) := by
  intro a b h
  have h' := congrFun h i
  simpa using h'

private theorem exists_eq_map_single_of_le_map_single {i : ι} {P : Submodule R (V i)} {N : Submodule R (∀ i, V i)}
    (h : N ≤ P.map (LinearMap.single R V i)) :
    ∃ N' : Submodule R (V i), N' ≤ P ∧ N = N'.map (LinearMap.single R V i) := by
  refine ⟨N.comap (LinearMap.single R V i), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 (h (Submodule.mem_comap.1 hx))
    exact (linearMap_single_injective (R := R) (V := V) i hyx) ▸ hy
  · apply le_antisymm
    · intro x hx
      obtain ⟨y, -, rfl⟩ := Submodule.mem_map.1 (h hx)
      exact Submodule.mem_map_of_mem (Submodule.mem_comap.2 hx)
    · exact Submodule.map_comap_le _ _

theorem piSum_single_mu (L : ∀ i, Submodule R (V i)) (i : ι) (hL : IsLat (ρ i) (L i))
    (hL0 : L i ≠ ⊥) :
    piSumS L i ≠ ⊥ ∧ ∀ θ : ℝ,
      (muMax (piReal ρ) (piSumS L i) ≤ θ ↔ muMax (ρ i) (L i) ≤ θ) ∧
      (θ ≤ muMin (piReal ρ) (piSumS L i) ↔ θ ≤ muMin (ρ i) (L i)) := by
  have hcomp : IsLat (piReal ρ) (piSumS L i) ∧
      rk (piReal ρ) (piSumS L i) = rk (ρ i) (L i) ∧
      deg (piReal ρ) (piSumS L i) = deg (ρ i) (L i) :=
    piSum_single ρ i (L i) hL
  have hc0 : piSumS L i ≠ ⊥ := by
    intro h
    apply hL0
    apply Submodule.map_injective_of_injective (linearMap_single_injective (R := R) (V := V) i)
    rw [Submodule.map_bot]
    exact h
  have hsub : ∀ N : Submodule R (V i), N ≤ L i → IsLat (ρ i) N :=
    fun N hN => hnSum_isLat_mono (ρ i) hL hN
  refine ⟨hc0, fun θ => ?_⟩
  have EP := slope_characterization R (∀ i, V i) (PiLp 2 E) (piReal ρ) (piSumS L i)
    hcomp.1 hc0
  have EL := slope_characterization R (V i) (E i) (ρ i) (L i) hL hL0
  rw [EP.1 θ, EL.1 θ, EP.2.1 θ, EL.2.1 θ]
  refine ⟨⟨fun H N hN => ?_, fun H N hN => ?_⟩, ⟨fun H N hN => ?_, fun H N hN => ?_⟩⟩
  · have h := H (N.map (LinearMap.single R V i)) (Submodule.map_mono hN)
    obtain ⟨-, hr, hd⟩ := piSum_single ρ i N (hsub N hN)
    rw [hr, hd] at h
    exact h
  · obtain ⟨N', hN', rfl⟩ := exists_eq_map_single_of_le_map_single (i := i) (P := L i) hN
    obtain ⟨-, hr, hd⟩ := piSum_single ρ i N' (hsub N' hN')
    rw [hr, hd]
    exact H N' hN'
  · have h := H (N.map (LinearMap.single R V i)) (Submodule.map_mono hN)
    obtain ⟨-, hr, hd⟩ := piSum_single ρ i N (hsub N hN)
    rw [hcomp.2.1, hcomp.2.2, hr, hd] at h
    exact h
  · obtain ⟨N', hN', rfl⟩ := exists_eq_map_single_of_le_map_single (i := i) (P := L i) hN
    obtain ⟨-, hr, hd⟩ := piSum_single ρ i N' (hsub N' hN')
    rw [hcomp.2.1, hcomp.2.2, hr, hd]
    exact H N' hN'

end

section

variable {R : Type*} [Ring R] {ι : Type*} [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

theorem piSum_T_vanish (L : ∀ i, Submodule R (V i)) (s : Finset ι) {x : ∀ i, V i}
    (hx : x ∈ piSumT L s) (j : ι) (hj : j ∉ s) : x j = 0 := by
  have hle : piSumT L s ≤ LinearMap.ker (LinearMap.proj j : (∀ i, V i) →ₗ[R] V j) := by
    refine iSup₂_le fun i hi => ?_
    intro y hy
    obtain ⟨v, -, rfl⟩ := Submodule.mem_map.1 hy
    have hij : j ≠ i := fun h => hj (h ▸ hi)
    rw [LinearMap.mem_ker]
    simp [hij]
  exact LinearMap.mem_ker.1 (hle hx)

theorem piSum_inf (L : ∀ i, Submodule R (V i)) (a : ι) (s : Finset ι) (ha : a ∉ s) :
    piSumS L a ⊓ piSumT L s = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
  obtain ⟨v, -, rfl⟩ := Submodule.mem_map.1 hx1
  have h := piSum_T_vanish L s hx2 a ha
  have hv : v = 0 := by
    simpa using h
  rw [Submodule.mem_bot, hv, map_zero]

theorem piSum_forall_insert (s : Finset ι) (a : ι) (q p : ι → Prop) (hq : q a) :
    (∀ i ∈ insert a s, q i → p i) ↔ p a ∧ ∀ i ∈ s, q i → p i := by
  constructor
  · intro h
    exact ⟨h a (Finset.mem_insert_self a s) hq,
      fun i hi hqi => h i (Finset.mem_insert_of_mem hi) hqi⟩
  · rintro ⟨ha, h⟩ i hi hqi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ha
    · exact h i hi hqi

theorem piSum_forall_insert_neg (s : Finset ι) (a : ι) (q p : ι → Prop) (hq : ¬ q a) :
    (∀ i ∈ insert a s, q i → p i) ↔ ∀ i ∈ s, q i → p i := by
  constructor
  · intro h i hi hqi
    exact h i (Finset.mem_insert_of_mem hi) hqi
  · intro h i hi hqi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact absurd hqi hq
    · exact h i hi hqi

theorem piSum_forall_insert_only (s : Finset ι) (a : ι) (q p : ι → Prop) (hq : q a)
    (hs : ∀ i ∈ s, ¬ q i) : (∀ i ∈ insert a s, q i → p i) ↔ p a := by
  rw [piSum_forall_insert s a q p hq]
  exact ⟨fun h => h.1, fun h => ⟨h, fun i hi hqi => absurd hqi (hs i hi)⟩⟩

end

section

variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

theorem piSum_orth (ρ : ∀ i, V i →+ E i) (L : ∀ i, Submodule R (V i)) (a : ι) (s : Finset ι)
    (ha : a ∉ s) : ∀ x ∈ piSumS L a, ∀ y ∈ piSumT L s,
      inner ℝ (piReal ρ x) (piReal ρ y) = 0 := by
  intro x hx y hy
  obtain ⟨v, -, rfl⟩ := Submodule.mem_map.1 hx
  have hya : y a = 0 := piSum_T_vanish L s hy a ha
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [piReal_apply, piReal_apply]
  by_cases h : j = a
  · subst h
    rw [hya, map_zero, inner_zero_right]
  · rw [LinearMap.single_apply, Pi.single_eq_of_ne h, map_zero, inner_zero_left]

end

end Formalism.HN

namespace Formalism.HN

universe uR uι uV uE uS

theorem piSum_of (hS : HNSum.{uR, max uι uV, max uι uE, uS}) : PiSum.{uR, uι, uV, uE} := by
  intro R ι _ _ _ V E _ _ _ _ _ ρ L hL
  obtain ⟨-, hbin⟩ := hS R (∀ i, V i) (PiLp 2 E) (piReal ρ)
  have key : ∀ s : Finset ι, IsLat (piReal ρ) (piSumT L s) ∧
      rk (piReal ρ) (piSumT L s) = ∑ i ∈ s, rk (ρ i) (L i) ∧
      deg (piReal ρ) (piSumT L s) = ∑ i ∈ s, deg (ρ i) (L i) ∧
      ((∃ i ∈ s, L i ≠ ⊥) → piSumT L s ≠ ⊥ ∧ ∀ θ : ℝ,
        (muMax (piReal ρ) (piSumT L s) ≤ θ ↔ ∀ i ∈ s, L i ≠ ⊥ → muMax (ρ i) (L i) ≤ θ) ∧
        (θ ≤ muMin (piReal ρ) (piSumT L s) ↔ ∀ i ∈ s, L i ≠ ⊥ → θ ≤ muMin (ρ i) (L i))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have hT0 : piSumT L (∅ : Finset ι) = ⊥ := by simp [piSumT]
      rw [hT0]
      have hbot : IsLat (piReal ρ) (⊥ : Submodule R (∀ i, V i)) := by
        refine ⟨?_, ?_⟩
        · rw [Submodule.bot_coe]; exact Set.injOn_singleton _ _
        · rw [satBasic_zl_bot]; infer_instance
      obtain ⟨-, -, -, B4, B5, -⟩ := saturation_basic_properties _ _ _ (piReal ρ) _ hbot
      refine ⟨hbot, ?_, ?_, ?_⟩
      · rw [Finset.sum_empty]; exact (B4 ⊥ le_rfl).2 rfl
      · rw [Finset.sum_empty]; exact B5
      · rintro ⟨i, hi, -⟩
        exact absurd hi (Finset.notMem_empty i)
    | insert a s ha ih =>
      obtain ⟨ihL, ihr, ihd, ihm⟩ := ih
      have hT : piSumT L (insert a s) = piSumS L a ⊔ piSumT L s := Finset.iSup_insert a s _
      have hSa := piSum_single ρ a (L a) (hL a)
      have horth := piSum_orth ρ L a s ha
      obtain ⟨hLat, hdeg, hmu⟩ := hbin (piSumS L a) (piSumT L s) hSa.1 ihL horth
      have hrk := (degree_supermodular _ _ _ (piReal ρ) (piSumS L a ⊔ piSumT L s) (piSumS L a)
        (piSumT L s) hLat le_sup_left le_sup_right).1
      have hbot0 : rk (piReal ρ) (⊥ : Submodule R (∀ i, V i)) = 0 :=
        ((saturation_basic_properties _ _ _ (piReal ρ) _ hLat).2.2.2.1 ⊥ bot_le).2 rfl
      rw [piSum_inf L a s ha, hbot0] at hrk
      rw [hT]
      refine ⟨hLat, ?_, ?_, ?_⟩
      · have hra : rk (piReal ρ) (piSumS L a) = rk (ρ a) (L a) := hSa.2.1
        rw [Finset.sum_insert ha, ← ihr, ← hra]
        omega
      · rw [Finset.sum_insert ha, hdeg, ← ihd, ← hSa.2.2]
        rfl
      · intro hex
        by_cases ha0 : L a = ⊥
        · have hSa0 : piSumS L a = ⊥ := by
            show (L a).map _ = ⊥
            rw [ha0, Submodule.map_bot]
          have hex' : ∃ i ∈ s, L i ≠ ⊥ := by
            obtain ⟨i, hi, hi0⟩ := hex
            rcases Finset.mem_insert.1 hi with rfl | hi
            · exact absurd ha0 hi0
            · exact ⟨i, hi, hi0⟩
          obtain ⟨hT0, hm⟩ := ihm hex'
          rw [hSa0, bot_sup_eq]
          refine ⟨hT0, fun θ => ⟨?_, ?_⟩⟩
          · exact (hm θ).1.trans
              (piSum_forall_insert_neg s a (fun i => L i ≠ ⊥) _ (fun h => h ha0)).symm
          · exact (hm θ).2.trans
              (piSum_forall_insert_neg s a (fun i => L i ≠ ⊥) _ (fun h => h ha0)).symm
        · obtain ⟨hSa0, hma⟩ := piSum_single_mu ρ L a (hL a) ha0
          have hne : piSumS L a ⊔ piSumT L s ≠ ⊥ := fun h =>
            hSa0 (eq_bot_iff.2 (h ▸ le_sup_left))
          by_cases hs : ∃ i ∈ s, L i ≠ ⊥
          · obtain ⟨hT0, hm⟩ := ihm hs
            obtain ⟨emax, emin⟩ := hmu hSa0 hT0
            refine ⟨hne, fun θ => ⟨?_, ?_⟩⟩
            · rw [emax, max_le_iff, (hma θ).1, (hm θ).1]
              exact (piSum_forall_insert s a (fun i => L i ≠ ⊥)
                (fun i => muMax (ρ i) (L i) ≤ θ) ha0).symm
            · rw [emin, le_min_iff, (hma θ).2, (hm θ).2]
              exact (piSum_forall_insert s a (fun i => L i ≠ ⊥)
                (fun i => θ ≤ muMin (ρ i) (L i)) ha0).symm
          · push Not at hs
            have hTs : piSumT L s = ⊥ := by
              refine eq_bot_iff.2 (iSup₂_le fun i hi => ?_)
              show (L i).map _ ≤ ⊥
              rw [hs i hi, Submodule.map_bot]
            rw [hTs, sup_bot_eq]
            refine ⟨hSa0, fun θ => ⟨?_, ?_⟩⟩
            · exact (hma θ).1.trans (piSum_forall_insert_only s a (fun i => L i ≠ ⊥)
                (fun i => muMax (ρ i) (L i) ≤ θ) ha0
                (fun i hi h => h (hs i hi))).symm
            · exact (hma θ).2.trans (piSum_forall_insert_only s a (fun i => L i ≠ ⊥)
                (fun i => θ ≤ muMin (ρ i) (L i)) ha0
                (fun i hi h => h (hs i hi))).symm
  obtain ⟨h1, h2, h3, h4⟩ := key Finset.univ
  have hU : piSumT L Finset.univ = Submodule.pi Set.univ L := by
    simp only [piSumT, piSumS, Finset.mem_univ, iSup_pos]
    exact Submodule.iSup_map_single
  rw [hU] at h1 h2 h3 h4
  refine ⟨h1, h2, h3, fun hex θ => ?_⟩
  obtain ⟨i, hi⟩ := hex
  obtain ⟨-, hm⟩ := h4 ⟨i, Finset.mem_univ i, hi⟩
  simpa using hm θ

theorem product_slope_sum : PiSum.{uR, uι, uV, uE} := piSum_of.{uR, uι, uV, uE, 0} polygon_slope_sum

end Formalism.HN
