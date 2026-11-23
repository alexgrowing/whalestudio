import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
import GroundTheory.GlobalFields.IdeleGroups.Restricted
import GroundTheory.GlobalFields.TateThesis.LocalConductor

open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Global

noncomputable section

namespace IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

def finiteComponent (v : HeightOneSpectrum (𝓞 K)) :
    (FiniteAdeleRing (𝓞 K) K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (_root_.RestrictedProduct.evalMonoidHom
    (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletion K) v)

@[simp]
theorem coe_finiteComponent (v : HeightOneSpectrum (𝓞 K)) (x : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((finiteComponent v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      (x : FiniteAdeleRing (𝓞 K) K) v :=
  rfl

theorem continuous_finiteComponent (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteComponent (K := K) v) :=
  Units.continuous_map (_root_.RestrictedProduct.continuous_eval v)

def finiteUnitsSingle (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  Units.map (finiteAdeleSingle v)

theorem continuous_finiteUnitsSingle (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteUnitsSingle (K := K) v) :=
  Units.continuous_map (continuous_finiteAdeleSingle v)

@[simp]
theorem finiteComponent_finiteUnitsSingle (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : finiteComponent v (finiteUnitsSingle v x) = x := by
  ext
  simp [finiteUnitsSingle]

theorem finiteComponent_finiteUnitsSingle_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (x : (v.adicCompletion K)ˣ) : finiteComponent w (finiteUnitsSingle v x) = 1 := by
  ext
  simp [finiteUnitsSingle, finiteAdeleSingle_apply_of_ne h]

def finiteLevel (n : HeightOneSpectrum (𝓞 K) → ℕ) : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ :=
  ⨅ v, (unitsLevel v (n v)).comap (finiteComponent v)

theorem mem_finiteLevel {n : HeightOneSpectrum (𝓞 K) → ℕ} {x : (FiniteAdeleRing (𝓞 K) K)ˣ} :
    x ∈ finiteLevel n ↔ ∀ v, finiteComponent v x ∈ unitsLevel v (n v) := by
  simp only [finiteLevel, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem finiteLevel_antitone {m n : HeightOneSpectrum (𝓞 K) → ℕ} (h : m ≤ n) :
    finiteLevel n ≤ finiteLevel m := fun _ hx ↦
  mem_finiteLevel.2 fun v ↦ unitsLevel_antitone v (h v) (mem_finiteLevel.1 hx v)

theorem finiteLevel_le_finiteLevel_zero (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    finiteLevel n ≤ finiteLevel 0 :=
  finiteLevel_antitone fun v ↦ Nat.zero_le (n v)

theorem finiteUnitsSingle_mem_finiteLevel {n : HeightOneSpectrum (𝓞 K) → ℕ}
    {v : HeightOneSpectrum (𝓞 K)} {x : (v.adicCompletion K)ˣ} (hx : x ∈ unitsLevel v (n v)) :
    finiteUnitsSingle v x ∈ finiteLevel n := by
  refine mem_finiteLevel.2 fun w ↦ ?_
  by_cases h : w = v
  · subst h
    simpa using hx
  · rw [finiteComponent_finiteUnitsSingle_of_ne h]
    exact one_mem _

theorem finiteUnitsEquiv_apply_eq (x : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    finiteUnitsEquiv K x v = finiteComponent v x :=
  Units.ext rfl

theorem isOpen_finiteLevel_zero :
    IsOpen (finiteLevel (K := K) 0 : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
  have h := (_root_.RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (A := fun v ↦ ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ))
    (fun v ↦ isOpen_units_adicCompletionIntegers K v)).preimage (finiteUnitsEquiv K).continuous
  convert h using 1
  ext x
  simp only [SetLike.mem_coe, mem_finiteLevel, Pi.zero_apply, unitsLevel_zero, Set.mem_preimage,
    Set.mem_ofPred_eq]
  exact forall_congr' fun v ↦ by rw [← finiteUnitsEquiv_apply_eq]; rfl

theorem isOpen_finiteLevel {n : HeightOneSpectrum (𝓞 K) → ℕ} (hn : (support n).Finite) :
    IsOpen (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
  have : (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) =
      (finiteLevel (K := K) 0 : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ∩
      ⋂ v ∈ hn.toFinset, finiteComponent v ⁻¹'
        (unitsLevel (K := K) v (n v) : Set (v.adicCompletion K)ˣ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    refine ⟨fun hx ↦ ⟨finiteLevel_le_finiteLevel_zero n hx, fun v _ ↦ mem_finiteLevel.1 hx v⟩,
      fun ⟨h0, h⟩ ↦ mem_finiteLevel.2 fun v ↦ ?_⟩
    by_cases hv : n v = 0
    · rw [hv]
      exact mem_finiteLevel.1 h0 v
    · exact h v (by simpa using hv)
  rw [this]
  exact isOpen_finiteLevel_zero.inter (isOpen_biInter_finset fun v _ ↦
    (isOpen_unitsLevel v (n v)).preimage (continuous_finiteComponent v))

theorem exists_finiteLevel_subset {W : Set (FiniteAdeleRing (𝓞 K) K)ˣ} (hW : W ∈ 𝓝 1) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧
        (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ⊆ W := by
  classical
  let e := finiteUnitsEquiv K
  let es := ContinuousMulEquiv.symm e
  have hS : (cofinite : Filter (HeightOneSpectrum (𝓞 K))) ≤ 𝓟 Set.univ := by simp
  have hW1 : es ⁻¹' W ∈ 𝓝 (1 : Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]) :=
    es.continuous.continuousAt.preimage_mem_nhds (by change W ∈ 𝓝 (es 1); rwa [map_one es])
  have hW2 := (_root_.RestrictedProduct.continuous_inclusion
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (A := fun v ↦ ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ)) hS).continuousAt.preimage_mem_nhds (x := 1) hW1
  rw [_root_.RestrictedProduct.isEmbedding_coe_of_principal.nhds_eq_comap, mem_comap] at hW2
  obtain ⟨t, ht, htW⟩ := hW2
  rw [nhds_pi, Filter.mem_pi'] at ht
  obtain ⟨I, u, hu, hIu⟩ := ht
  choose N hN hNu using fun v ↦ exists_unitsLevel_subset v (hu v)
  refine ⟨I, fun v ↦ if v ∈ I then N v else 0, fun v hv ↦ by simp [hv, hN v],
    fun v hv ↦ by simp [hv], ?_⟩
  intro x hx
  rw [SetLike.mem_coe, mem_finiteLevel] at hx
  have hx0 : ∀ v, e x v ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := fun v ↦ by
    rw [finiteUnitsEquiv_apply_eq, ← unitsLevel_zero]
    exact unitsLevel_antitone v (Nat.zero_le _) (hx v)
  let z : Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]_[𝓟 Set.univ] :=
    ⟨fun v ↦ e x v, Filter.eventually_principal.2 fun v _ ↦ hx0 v⟩
  have hz := htW (show (z : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) ∈ t from
    hIu fun v hv ↦ by
      have := hx v
      simp only [Finset.mem_coe.1 hv, if_true] at this
      exact hNu v (by rw [← finiteUnitsEquiv_apply_eq] at this; exact this))
  have hzx : _root_.RestrictedProduct.inclusion _ _ hS z = e x := rfl
  rw [Set.mem_preimage, Set.mem_preimage, hzx] at hz
  rwa [show es (e x) = x from ContinuousMulEquiv.symm_apply_apply e x] at hz

section Character

variable {H : Type*} [Group H] [TopologicalSpace H]

theorem exists_finiteLevel_le_ker (hH : NoSmallSubgroups H)
    (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) (hχ : Continuous χ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧ finiteLevel n ≤ χ.ker := by
  obtain ⟨L, ⟨S, n, h1, h0, rfl⟩, hL⟩ := exists_le_ker_of_noSmallSubgroups
    (P := fun L ↦ ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧ L = finiteLevel n)
    (fun W hW ↦ by
      obtain ⟨S, n, h1, h0, h⟩ := exists_finiteLevel_subset hW
      exact ⟨_, ⟨S, n, h1, h0, rfl⟩, h⟩) hH χ hχ
  exact ⟨S, n, h1, h0, hL⟩

theorem exists_finiteLevel_le_ker_circle (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* Circle)
    (hχ : Continuous χ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧ finiteLevel n ≤ χ.ker :=
  exists_finiteLevel_le_ker Circle.noSmallSubgroups χ hχ

theorem isOpen_ker_of_continuous (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) : IsOpen (χ.ker : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
  obtain ⟨S, n, -, h0, hn⟩ := exists_finiteLevel_le_ker hH χ hχ
  refine Subgroup.isOpen_mono hn (isOpen_finiteLevel (S.finite_toSet.subset fun v hv ↦ ?_))
  by_contra hvS
  exact hv (h0 v hvS)

def conductorExponentAt (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  conductorExponent v (χ.comp (finiteUnitsSingle v))

theorem finiteLevel_le_ker_iff (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    finiteLevel n ≤ χ.ker ↔ ∀ v, conductorExponentAt χ v ≤ n v := by
  have hloc : ∀ v, Continuous (χ.comp (finiteUnitsSingle v)) := fun v ↦
    hχ.comp (continuous_finiteUnitsSingle v)
  constructor
  · intro h v
    rw [conductorExponentAt, ← unitsLevel_le_ker_iff v hH _ (hloc v)]
    intro x hx
    exact h (finiteUnitsSingle_mem_finiteLevel hx)
  · intro h x hx
    classical
    obtain ⟨S, n₀, -, h0, hker⟩ := exists_finiteLevel_le_ker hH χ hχ
    set p := ∏ v ∈ S, finiteUnitsSingle v (finiteComponent v x) with hp
    have hcomp : ∀ w, finiteComponent w p = if w ∈ S then finiteComponent w x else 1 := by
      intro w
      rw [hp, map_prod]
      split_ifs with hw
      · rw [Finset.prod_eq_single_of_mem w hw fun v _ hv ↦
          finiteComponent_finiteUnitsSingle_of_ne (Ne.symm hv) _,
          finiteComponent_finiteUnitsSingle]
      · exact Finset.prod_eq_one fun v hv ↦
          finiteComponent_finiteUnitsSingle_of_ne (fun h ↦ hw (by rw [h]; exact hv)) _
    have hy : x * p⁻¹ ∈ finiteLevel n₀ := by
      refine mem_finiteLevel.2 fun w ↦ ?_
      rw [map_mul, map_inv, hcomp]
      split_ifs with hw
      · rw [mul_inv_cancel]
        exact one_mem _
      · rw [inv_one, mul_one, h0 w hw]
        exact unitsLevel_antitone w (Nat.zero_le _) (mem_finiteLevel.1 hx w)
    have hpk : p ∈ χ.ker := Subgroup.prod_mem _ fun v _ ↦
      (unitsLevel_le_ker_iff v hH _ (hloc v)).2 (h v) (mem_finiteLevel.1 hx v)
    have hxp : x = x * p⁻¹ * p := by rw [inv_mul_cancel_right]
    rw [hxp]
    exact mul_mem (hker hy) hpk

theorem finite_support_conductorExponentAt (hH : NoSmallSubgroups H)
    (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) (hχ : Continuous χ) :
    (support (conductorExponentAt χ)).Finite := by
  obtain ⟨S, n, -, h0, hker⟩ := exists_finiteLevel_le_ker hH χ hχ
  have h := (finiteLevel_le_ker_iff hH χ hχ n).1 hker
  refine S.finite_toSet.subset fun v hv ↦ ?_
  by_contra hvS
  exact hv (Nat.eq_zero_of_le_zero ((h v).trans (h0 v hvS).le))

theorem conductorExponentAt_eq_zero_iff (hH : NoSmallSubgroups H)
    (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 K)) :
    conductorExponentAt χ v = 0 ↔
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤
        (χ.comp (finiteUnitsSingle v)).ker :=
  conductorExponent_eq_zero_iff v hH _ (hχ.comp (continuous_finiteUnitsSingle v))

end Character

end IdeleGroup

end

end GroundTheory.Global
