import Mathlib
import GroundTheory.GlobalFields.KummerTheory.KummerIndexLemma.PowerPlaces
import GroundTheory.GlobalFields.SUnits

noncomputable section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh

namespace KummerIndex

variable {K : Type*} [Field K] [NumberField K]

def unitsPowAt (p : ℕ) (T : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup Kˣ :=
  ⨅ v ∈ T, unitsPowIn K p (v.adicCompletion K)

theorem mem_unitsPowAt {p : ℕ} {T : Finset (HeightOneSpectrum (𝓞 K))} {x : Kˣ} :
    x ∈ unitsPowAt p T ↔ ∀ v ∈ T, x ∈ unitsPowIn K p (v.adicCompletion K) := by
  simp only [unitsPowAt, Subgroup.mem_iInf]

theorem unitsPowAt_empty (p : ℕ) : unitsPowAt (K := K) p ∅ = ⊤ := by
  ext x
  simp [mem_unitsPowAt]

theorem unitsPowAt_insert [DecidableEq (HeightOneSpectrum (𝓞 K))] (p : ℕ)
    (v : HeightOneSpectrum (𝓞 K)) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    unitsPowAt p (insert v T) = unitsPowIn K p (v.adicCompletion K) ⊓ unitsPowAt p T := by
  ext x
  simp only [mem_unitsPowAt, Finset.mem_insert, forall_eq_or_imp, Subgroup.mem_inf]

theorem unitsPow_le_unitsPowAt (p : ℕ) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    unitsPow K p ≤ unitsPowAt p T := fun _ hx ↦
  mem_unitsPowAt.2 fun _ _ ↦ unitsPow_le_unitsPowIn K p _ hx

variable {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity K p]

theorem exists_localClass_eq (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hpT : ∀ v ∈ T, (p : 𝓞 K) ∉ v.asIdeal)
    (hidx : (unitsPowAt p T).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) =
      p ^ T.card)
    (z : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ)
    (hz : ∀ v ∈ T, z v ∈ localUnits v) :
    ∃ δ ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, ∀ v ∈ T,
      localClass v p δ = QuotientGroup.mk (z v) := by
  classical
  set Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K
  have hvS : ∀ v ∈ T, v ∉ (S : Set (HeightOneSpectrum (𝓞 K))) := fun v hv hvS ↦
    Finset.disjoint_left.1 hST (Finset.mem_coe.1 hvS) hv
  let _ : ∀ v : T, Group (UnitsModPow (v.1.adicCompletion K) p) := fun _ ↦ inferInstance
  let ψ : Δ →* ((v : T) → UnitsModPow (v.1.adicCompletion K) p) :=
    MonoidHom.pi fun v ↦ (localClass v.1 p).comp Δ.subtype
  have hker : ψ.ker = (unitsPowAt p T).subgroupOf Δ := by
    ext δ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_unitsPowAt, funext_iff]
    constructor
    · intro h v hv
      rw [← ker_localClass]
      exact h ⟨v, hv⟩
    · intro h v
      have := h v.1 v.2
      rw [← ker_localClass] at this
      exact this
  let U : Subgroup ((v : T) → UnitsModPow (v.1.adicCompletion K) p) :=
    Subgroup.pi Set.univ fun v ↦ localUnitClasses v.1 p
  have hU : Nat.card U = p ^ T.card := by
    have e : U ≃ ∀ v : T, localUnitClasses v.1 p :=
      (Equiv.subtypeEquivRight fun f ↦ by simp [U, Subgroup.mem_pi]).trans
        (Equiv.subtypePiEquivPi)
    rw [Nat.card_congr e, Nat.card_pi,
      Finset.prod_congr rfl fun v _ ↦ natCard_localUnitClasses v.1 p (hpT v.1 v.2),
      Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  have hrange : Nat.card ψ.range = p ^ T.card := by
    rw [← Subgroup.index_ker, hker, ← Subgroup.relIndex, hidx]
  have hle : ψ.range ≤ U := by
    rintro _ ⟨δ, rfl⟩
    rw [Subgroup.mem_pi]
    intro v _
    exact localClass_mem_localUnitClasses v.1 p (Set.unit_valuation_eq_one (S := (S : Set (HeightOneSpectrum (𝓞 K)))) (K := K) δ (hvS v.1 v.2))
  have : Finite U := Nat.finite_of_card_ne_zero (by
    rw [hU]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have heq : ψ.range = U := Subgroup.eq_of_le_of_card_ge hle (by rw [hU, hrange])
  have hf : (fun v : T ↦ (QuotientGroup.mk (z v.1) : UnitsModPow (v.1.adicCompletion K) p)) ∈
      ψ.range := by
    rw [heq, Subgroup.mem_pi]
    intro v _
    exact Subgroup.mem_map_of_mem _ (hz v.1 v.2)
  obtain ⟨δ, hδ⟩ := hf
  refine ⟨δ, δ.2, fun v hv ↦ ?_⟩
  exact congrFun hδ ⟨v, hv⟩

universe u

variable {K : Type u} [Field K] [NumberField K] [HasEnoughRootsOfUnity K p]

omit [Fact p.Prime] [HasEnoughRootsOfUnity K p] in

theorem valuation_eq_one_of_mem_unit {S : Set (HeightOneSpectrum (𝓞 K))} {x : Kˣ}
    (hx : x ∈ S.unit K) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    v.valuation K (x : K) = 1 :=
  Set.unit_valuation_eq_one (S := S) (K := K) ⟨x, hx⟩ hv

omit [HasEnoughRootsOfUnity K p] in

theorem relIndex_unitsPow_sUnit_ne_zero (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (unitsPow K p).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) ≠ 0 := by
  set Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K
  have hfi := Subgroup.finiteIndex_range_powMonoidHom_of_fg Δ (Fact.out : p.Prime).ne_zero
  have hle : (powMonoidHom p : Δ →* Δ).range ≤ (unitsPow K p).subgroupOf Δ := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨(y : Kˣ), rfl⟩
  exact fun h ↦ hfi.index_ne_zero (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le hle))

theorem _root_.GroundTheory.Global.FirstInequality.exists_place_relIndex_unitsPowAt_insert
    (hFI : FirstInequality.{u}) [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S) {a : Kˣ}
    (ha : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) {T : Finset (HeightOneSpectrum (𝓞 K))}
    (hidx : (unitsPowAt p T).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) =
      p ^ T.card)
    {x : Kˣ} (hxΔ : x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hxT : x ∈ unitsPowAt p T)
    (hxa : x ∉ radicalGroup K p a) :
    ∃ v, v ∉ S ∧ v ∉ T ∧ a ∈ unitsPowIn K p (v.adicCompletion K) ∧
      (unitsPowAt p (insert v T)).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) =
        p ^ (T.card + 1) := by
  set Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K
  have hfin : ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T).Finite :=
    (S.finite_toSet).union T.finite_toSet
  obtain ⟨v, hv, hav, hxv⟩ := hFI.exists_place_mem_unitsPowIn_not_mem hxa hfin
    (fun v hv ↦ Or.inl (hpS v hv))
    (fun v hv ↦ valuation_eq_one_of_mem_unit ha (fun h ↦ hv (Or.inl h)))
    (fun v hv ↦ valuation_eq_one_of_mem_unit hxΔ (fun h ↦ hv (Or.inl h)))
  have hvS : v ∉ S := fun h ↦ hv (Or.inl h)
  have hvT : v ∉ T := fun h ↦ hv (Or.inr h)
  refine ⟨v, hvS, hvT, hav, ?_⟩
  have hpv : (p : 𝓞 K) ∉ v.asIdeal := fun h ↦ hvS (hpS v h)
  rw [unitsPowAt_insert, ← Subgroup.relIndex_inf_mul_relIndex, hidx, pow_succ, mul_comm]
  congr 1
  rw [← ker_localClass, Subgroup.relIndex_ker]
  set H := (unitsPowAt p T ⊓ Δ).map (localClass v p)
  have hle : H ≤ localUnitClasses v p := by
    rintro _ ⟨y, hy, rfl⟩
    exact localClass_mem_localUnitClasses v p (valuation_eq_one_of_mem_unit hy.2 hvS)
  have hdvd : Nat.card H ∣ p := by
    have := Subgroup.card_dvd_of_le hle
    rwa [natCard_localUnitClasses v p hpv] at this
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h1 | hp
  · exfalso
    have hbot := Subgroup.card_eq_one.1 h1
    have hmem : localClass v p x ∈ H := Subgroup.mem_map_of_mem _ ⟨hxT, hxΔ⟩
    rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_localClass] at hmem
    exact hxv hmem
  · exact hp

theorem _root_.GroundTheory.Global.FirstInequality.exists_places_unitsPowAt
    (hFI : FirstInequality.{u}) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S) {a : Kˣ}
    (ha : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint S T ∧
      (∀ v ∈ T, a ∈ unitsPowIn K p (v.adicCompletion K)) ∧
      (unitsPowAt p T).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) = p ^ T.card ∧
      ∀ x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, x ∈ unitsPowAt p T →
        x ∈ radicalGroup K p a := by
  classical
  set Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K
  let Good : Finset (HeightOneSpectrum (𝓞 K)) → Prop := fun T ↦ Disjoint S T ∧
    (∀ v ∈ T, a ∈ unitsPowIn K p (v.adicCompletion K)) ∧
    (unitsPowAt p T).relIndex Δ = p ^ T.card
  have key : ∀ n : ℕ, ∃ T, Good T ∧
      (n ≤ T.card ∨ ∀ x ∈ Δ, x ∈ unitsPowAt p T → x ∈ radicalGroup K p a) := by
    intro n
    induction n with
    | zero =>
      refine ⟨∅, ⟨Finset.disjoint_empty_right S, by simp, ?_⟩, Or.inl le_rfl⟩
      rw [unitsPowAt_empty, Subgroup.relIndex_top_left, Finset.card_empty, pow_zero]
    | succ n ih =>
      obtain ⟨T, hT, h | h⟩ := ih
      · by_cases hfin : ∀ x ∈ Δ, x ∈ unitsPowAt p T → x ∈ radicalGroup K p a
        · exact ⟨T, hT, Or.inr hfin⟩
        · simp only [not_forall, exists_prop] at hfin
          obtain ⟨x, hxΔ, hxT, hxa⟩ := hfin
          obtain ⟨v, hvS, hvT, hav, hidx⟩ :=
            hFI.exists_place_relIndex_unitsPowAt_insert S hpS ha hT.2.2 hxΔ hxT hxa
          refine ⟨insert v T, ⟨?_, ?_, ?_⟩, Or.inl ?_⟩
          · exact Finset.disjoint_insert_right.2 ⟨hvS, hT.1⟩
          · intro w hw
            rcases Finset.mem_insert.1 hw with rfl | hw
            · exact hav
            · exact hT.2.1 w hw
          · rw [Finset.card_insert_of_notMem hvT, hidx]
          · rw [Finset.card_insert_of_notMem hvT]
            omega
      · exact ⟨T, hT, Or.inr h⟩
  set B := (unitsPow K p).relIndex Δ
  have hB : B ≠ 0 := relIndex_unitsPow_sUnit_ne_zero S
  obtain ⟨T, hT, h | h⟩ := key B
  · exfalso
    have hdvd : p ^ T.card ∣ B :=
      hT.2.2 ▸ Subgroup.relIndex_dvd_of_le_left Δ (unitsPow_le_unitsPowAt p T)
    have h1 : p ^ T.card ≤ B := Nat.le_of_dvd (Nat.pos_of_ne_zero hB) hdvd
    have h2 : T.card < p ^ T.card := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
    omega
  · exact ⟨T, hT.1, hT.2.1, hT.2.2, h⟩

end KummerIndex

end GroundTheory.Global
