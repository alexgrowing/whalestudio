import Mathlib
import GroundTheory.TateCohomology.CohTrivialPGroup
import GroundTheory.TateCohomology.TateGroupIso
import GroundTheory.TateCohomology.CoresRes
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

section Index

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem index_smul_tateCohomology_eq_zero (A : Rep.{u} k G) (n : ℤ) (P : Subgroup G) [Fintype P]
    (hP : IsZero (tateCohomology (res P.subtype A) n)) (x : tateCohomology A n) :
    P.index • x = 0 := by
  have hm : P.index • 𝟙 (tateCohomology A n) = 0 := by
    rw [← tateRes_app_comp_tateCores_app P A n, hP.eq_of_tgt ((tateRes P n).app A) 0, zero_comp]
  have h := congrArg (fun φ : tateCohomology A n ⟶ tateCohomology A n => φ.hom x) hm
  simpa using h

theorem isZero_tateCohomology_of_index (A : Rep.{u} k G) (n : ℤ)
    (h : ∀ p : ℕ, p.Prime → p ∣ Fintype.card G → ∃ P : Subgroup G, ¬ p ∣ P.index ∧
      ∀ [Fintype P], IsZero (tateCohomology (res P.subtype A) n)) :
    IsZero (tateCohomology A n) := by
  have hx : ∀ x : tateCohomology A n, x = 0 := by
    intro x
    by_contra hne
    have ho : addOrderOf x ∣ Fintype.card G :=
      addOrderOf_dvd_of_nsmul_eq_zero (card_smul_tateCohomology A n x)
    have ho1 : addOrderOf x ≠ 1 := fun h1 => hne (AddMonoid.addOrderOf_eq_one_iff.1 h1)
    obtain ⟨P, hidx, hP⟩ := h _ (Nat.minFac_prime ho1) ((Nat.minFac_dvd _).trans ho)
    let _ : Fintype P := Fintype.ofFinite P
    exact hidx ((Nat.minFac_dvd _).trans
      (addOrderOf_dvd_of_nsmul_eq_zero (index_smul_tateCohomology_eq_zero A n P hP x)))
  have : Subsingleton (tateCohomology A n) := ⟨fun a b => by rw [hx a, hx b]⟩
  exact ModuleCat.isZero_of_subsingleton _

end Index

section Subgroups

variable {k G : Type u} [CommRing k] [Group G]

theorem tateAcyclic_res_res_iff (A : Rep.{u} k G) (S : Subgroup G) (T : Subgroup S) [Fintype T]
    (U : Subgroup G) [Fintype U] (hU : T.map S.subtype = U) :
    TateAcyclic (res T.subtype (res S.subtype A)) ↔ TateAcyclic (res U.subtype A) := by
  subst hU
  let U := T.map S.subtype
  let φ : T →* U := (S.subtype.comp T.subtype).codRestrict U fun t =>
    Subgroup.mem_map.2 ⟨t, t.2, rfl⟩
  have hinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun x : U => (x : G)) hab))
  have hsurj : Function.Surjective φ := by
    rintro ⟨u, hu⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hu
    exact ⟨⟨x, hx⟩, rfl⟩
  rw [← tateAcyclic_res_iff φ ⟨hinj, hsurj⟩ (res U.subtype A)]
  have e : U.subtype.comp φ = S.subtype.comp T.subtype := rfl
  rw [res_res φ U.subtype A, e, res_res]

theorem tateAcyclic_res_of_le {A : Rep.{u} k G} {P : Subgroup G} (hP : CohTrivial (res P.subtype A))
    {V : Subgroup G} [Fintype V] (hV : V ≤ P) : TateAcyclic (res V.subtype A) := by
  classical
  let _ : Fintype (V.subgroupOf P) :=
    Fintype.ofInjective (fun x : V.subgroupOf P => (⟨(x : P), Subgroup.mem_subgroupOf.1 x.2⟩ : V))
      fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun y : V => (y : G)) hab))
  refine (tateAcyclic_res_res_iff A P (V.subgroupOf P) V ?_).1 (hP _)
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hV]

end Subgroups

section Sylow

variable {G : Type} [Group G] [Fintype G]

theorem cohTrivial_of_sylow (A : Rep ℤ G)
    (h : ∀ p : ℕ, p.Prime → ∃ (P : Sylow p G) (q : ℤ), ∀ [Fintype (P : Subgroup G)],
      IsZero (tateCohomology (res (P : Subgroup G).subtype A) q) ∧
        IsZero (tateCohomology (res (P : Subgroup G).subtype A) (q + 1))) :
    CohTrivial A := by
  classical

  have hSyl : ∀ p : ℕ, p.Prime → ∃ P : Sylow p G, CohTrivial (res (P : Subgroup G).subtype A) := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, q, hPq⟩ := h p hp
    let _ : Fintype (P : Subgroup G) := Fintype.ofFinite _
    exact ⟨P, cohTrivial_of_isZero_of_isZero P.isPGroup' _ q (hPq).1 (hPq).2⟩

  have hp_sub : ∀ (p : ℕ), p.Prime → ∀ (U : Subgroup G) [Fintype U], IsPGroup p U →
      TateAcyclic (res U.subtype A) := by
    intro p hp U _ hU
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, hP⟩ := hSyl p hp
    obtain ⟨Q, hUQ⟩ := hU.exists_le_sylow
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
    let V : Subgroup G := U.comap (MulAut.conj g).toMonoidHom
    let _ : Fintype V := Fintype.ofFinite _
    have hVP : V ≤ P := by
      intro y hy
      have h1 : g * y * g⁻¹ ∈ ((g • P : Sylow p G) : Subgroup G) := hUQ hy
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
      simpa [mul_assoc] using h1
    refine tateAcyclic_res_conj U V g (fun x => ?_) (tateAcyclic_res_of_le hP hVP)
    simp [V, mul_assoc]
  intro S _ n
  refine isZero_tateCohomology_of_index (res S.subtype A) n fun p hp _ => ?_
  have : Fact p.Prime := ⟨hp⟩
  let T : Sylow p S := default
  refine ⟨T, T.not_dvd_index, fun {_} => ?_⟩
  let _ : Fintype ((T : Subgroup S).map S.subtype) := Fintype.ofFinite _
  refine ((tateAcyclic_res_res_iff A S T _ rfl).2 ?_) n
  exact hp_sub p hp _ (T.isPGroup'.map S.subtype)

theorem cohTrivial_of_forall_subgroup (A : Rep ℤ G) (q : ℤ)
    (h : ∀ (S : Subgroup G) [Fintype S], IsZero (tateCohomology (res S.subtype A) q) ∧
      IsZero (tateCohomology (res S.subtype A) (q + 1))) :
    CohTrivial A := by
  classical
  refine cohTrivial_of_sylow A fun p hp => ?_
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨default, q, fun {_} => h _⟩

end Sylow

end GroundTheory.GroupCoh
