import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StMixedTwistShift
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StRestrLenEuler
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StSubsetDiffConst
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapper
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace MixedTwistShiftAlt

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem foldl_twist_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (I : Chart x) :
    ∀ (l : List (Fin n)) (F : SubSystem k x Ω),
      (l.foldl (fun F i => F.twist (L i)) F).sub I = F.sub I * (l.map fun i => (L i).sub I).prod
  | [], F => by simp
  | i :: l, F => by
    rw [List.foldl_cons, foldl_twist_sub L I l, SubSystem.twist_sub_eq_mul_of_line, List.map_cons,
      List.prod_cons]
    ring

theorem prod_map_filter {R : Type*} [CommMonoid R] {n : ℕ} (g : Fin n → R) (T : Finset (Fin n)) :
    ∀ l : List (Fin n),
      ((l.filter (· ∈ T)).map g).prod = (l.map fun j => g j ^ (if j ∈ T then 1 else 0)).prod
  | [] => rfl
  | j :: l => by
    by_cases hj : j ∈ T <;> simp [hj, prod_map_filter g T l]

theorem tensorSub_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (T : Finset (Fin n)) (I : Chart x) :
    (tensorSub L T).sub I = ∏ j, (L j).sub I ^ (if j ∈ T then 1 else 0) := by
  have h0 : (twistSys k x 0).sub I = 1 := (SubSystem.pow_sub (twistSys k x 0) 0 I).trans (pow_zero _)
  rw [tensorSub, foldl_twist_sub, h0, one_mul, prod_map_filter, Fin.prod_univ_def]

theorem twistPows_snoc_sub {n : ℕ} (L : Fin n → LineBundle k x) (M : LineBundle k x) (T : Finset (Fin n))
    (m : ℕ) (I : Chart x) :
    ((twistSys k x 0).twistPows (n + 1)
        (fun j => (Fin.snoc (α := fun _ => LineBundle k x) L M j).toSubSystem)
        (Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m)).sub I =
      M.sub I ^ m * (tensorSub (fun i => (L i).toSubSystem) T).sub I := by
  have h0 : (twistSys k x 0).sub I = 1 := (SubSystem.pow_sub (twistSys k x 0) 0 I).trans (pow_zero _)
  rw [SnapperSections.twistPows_sub, tensorSub_sub, h0, one_mul, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

end MixedTwistShiftAlt

open MixedTwistShiftAlt in

theorem MixedTwistShift.proof (hH : SnapperHyperplane.Statement.{u, w}) (hS : SnapperSection.Statement.{u, w})
    (hP : SnapperDiffPoly.Statement) (hR : RestrLenEuler.Statement.{u, w}) (hD : SubsetDiffConst.Statement) :
    MixedTwistShift.Statement.{u, w} := by
  intro k _ Ω _ _ N x n qq hp hh hle hdim L M d
  set L' : Fin (n + 1) → LineBundle k x := Fin.snoc (α := fun _ => LineBundle k x) L M with hL'
  set ν : Finset (Fin n) → ℕ → Fin (n + 1) → ℕ :=
    fun T m => Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m with hν
  set f : (Fin (n + 1) → ℕ) → ℤ → ℚ := fun e c => (pieceChar k qq 0 L' e c : ℚ) with hf
  set Ls : Fin n → SubSystem k x Ω := fun i => (L i).toSubSystem with hLs

  have hA : ∀ T (c : ℤ), ((tensorSub Ls T).twist M.toSubSystem).twist (twistSys k x c) =
      ((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T 1)).twist (twistSys k x c) := by
    intro T c
    congr 1
    refine SubSystem.ext_sub fun I => ?_
    rw [twistPows_snoc_sub, SubSystem.twist_sub_eq_mul_of_line, pow_one]
  have hB : ∀ T (c : ℤ), (tensorSub Ls T).twist (twistSys k x c) =
      ((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T 0)).twist (twistSys k x c) := by
    intro T c
    congr 1
    refine SubSystem.ext_sub fun I => ?_
    rw [twistPows_snoc_sub, pow_zero, one_mul]

  have hev : ∀ m : ℕ, ∀ᶠ c : ℤ in atTop, ∀ T : Finset (Fin n),
      restrLen qq (((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T m)).twist
        (twistSys k x c)) = pieceChar k qq 0 L' (ν T m) c :=
    fun m => eventually_all.2 fun T => hR k Ω N x qq hh hle (n + 1) L' (ν T m)
  have hsum : ∀ (m : ℕ) (c : ℤ), (∀ T : Finset (Fin n),
      restrLen qq (((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T m)).twist
        (twistSys k x c)) = pieceChar k qq 0 L' (ν T m) c) →
      ((∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
        restrLen qq (((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T m)).twist
          (twistSys k x c)) : ℤ) : ℚ) = subsetDiff n f m c := by
    intro m c h
    rw [subsetDiff]
    push_cast
    exact Finset.sum_congr rfl fun T _ => by rw [h T]
  obtain ⟨hconst, hzero⟩ := hD n f (pieceChar_isNumPolyLT hH hS hP L' (n + 1) qq hp hh hle hdim 0)
  have hT1 : Tendsto (fun c : ℕ => (c : ℤ) + d) atTop atTop :=
    tendsto_atTop_add_const_right _ d tendsto_natCast_atTop_atTop
  have hLhs : ∀ᶠ c : ℕ in atTop, ((∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
      restrLen qq (((tensorSub Ls T).twist M.toSubSystem).twist (twistSys k x ((c : ℤ) + d))) : ℤ) : ℚ) =
        subsetDiff n f 1 ((c : ℤ) + d) := by
    filter_upwards [hT1.eventually (hev 1)] with c hc
    simp only [hA]
    exact hsum 1 _ hc
  split_ifs with hW
  ·
    have hI : ∀ᶠ c : ℕ in atTop, (interSum qq Ls c : ℚ) = subsetDiff n f 0 (c : ℤ) := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (hev 0)] with c hc
      rw [interSum]
      simp only [hB]
      exact hsum 0 _ hc
    obtain ⟨c₀, hc₀⟩ := hI.exists_forall_of_atTop
    have hκ : ∀ᶠ c : ℕ in atTop, interSum qq Ls c = interSum qq Ls c₀ := by
      filter_upwards [eventually_ge_atTop c₀] with c hc
      exact_mod_cast (hc₀ c hc).trans ((hconst 0 0 c c₀).trans (hc₀ c₀ le_rfl).symm)
    have hlim : interNum qq Ls = interSum qq Ls c₀ :=
      (tendsto_const_nhds.congr' (hκ.mono fun _ hc => hc.symm)).limUnder_eq
    rw [hlim]
    filter_upwards [hLhs] with c hc
    exact_mod_cast hc.trans ((hconst 1 0 _ c₀).trans (hc₀ c₀ le_rfl).symm)
  ·
    have hlow : IsNumPolyLT (n + 1) n f := by
      by_cases hrel : ∃ i, (X i : Poly k N) ∉ qq
      · have := hp
        obtain ⟨e, he⟩ := SnapperSections.exists_dim_eq qq hh hrel
        have hen : e ≠ n := fun h => hW ⟨hp, hh, hle, hrel, by subst h; exact he⟩
        have hle' : e + 1 ≤ n + 1 := by
          rw [he] at hdim
          exact_mod_cast hdim
        refine pieceChar_isNumPolyLT hH hS hP L' n qq hp hh hle ?_ 0
        rw [he]
        exact_mod_cast (by omega : e + 1 ≤ n)
      · push Not at hrel
        exact ⟨0, Or.inl rfl, fun e c => by simp [hf, pieceChar_of_irrelevant qq hrel]⟩
    filter_upwards [hLhs] with c hc
    exact_mod_cast hc.trans (hzero hlow 1 _)

end

end GroundTheory.Heights₂.Heights.Kleiman
