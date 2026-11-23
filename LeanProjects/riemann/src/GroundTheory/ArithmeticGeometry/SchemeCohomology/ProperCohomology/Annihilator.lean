import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Support
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {X : Scheme.{u}}

def annihilatorIdeal (F : X.Modules) (U : X.Opens) : Ideal Γ(X, U) :=
  Module.annihilator Γ(X, U) Γ(F, U)

lemma mem_annihilatorIdeal {F : X.Modules} {U : X.Opens} {a : Γ(X, U)} :
    a ∈ annihilatorIdeal F U ↔ ∀ m : Γ(F, U), a • m = 0 :=
  Module.mem_annihilator

lemma eq_zero_of_isUnit_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {a : R}
    (ha : IsUnit a) {m : M} (h : a • m = 0) : m = 0 := by
  rw [← one_smul R m, ← ha.unit.inv_mul, mul_smul, IsUnit.unit_spec, h, smul_zero]

lemma exists_pow_mul_mem_annihilatorIdeal (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) [Module.Finite Γ(X, U) Γ(F, U)] (f a : Γ(X, U))
    (h : ∀ m : Γ(F, U), resF F (X.basicOpen_le f) (a • m) = 0) :
    ∃ E : ℕ, f ^ E * a ∈ annihilatorIdeal F U := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Γ(X, U)) (M := Γ(F, U))
  have : ∀ m ∈ s, ∃ e : ℕ, f ^ e • (a • m) = 0 := fun m _ =>
    qcoh_exists_pow_smul_eq_zero F hU f (a • m) (h m)
  choose! e he using this
  refine ⟨s.sup e, ?_⟩
  rw [annihilatorIdeal, ← Submodule.annihilator_top, ← hs, Submodule.mem_annihilator_span]
  rintro ⟨m, hm⟩
  have hle : e m ≤ s.sup e := Finset.le_sup hm
  change (f ^ s.sup e * a) • m = 0
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, mul_smul, mul_smul, he m hm, smul_zero]

theorem map_annihilatorIdeal_basicOpen (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) [Module.Finite Γ(X, U) Γ(F, U)] (f : Γ(X, U)) :
    (annihilatorIdeal F U).map (resO (X.basicOpen_le f)) = annihilatorIdeal F (X.basicOpen f) := by
  have hunit : IsUnit (resO (X.basicOpen_le f) f) := X.toRingedSpace.isUnit_res_basicOpen f
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_annihilatorIdeal]
    intro m
    obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq F hU f m
    refine eq_zero_of_isUnit_smul (hunit.pow e) ?_
    rw [smul_smul, mul_comm, ← smul_smul, ← hm', ← resF_smul, mem_annihilatorIdeal.1 ha m',
      map_zero]
  · intro b hb
    rw [mem_annihilatorIdeal] at hb
    have := hU.isLocalization_basicOpen f
    obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, hab⟩ := IsLocalization.surj (Submonoid.powers f) b
    change b * resO (X.basicOpen_le f) (f ^ k) = resO (X.basicOpen_le f) a at hab
    obtain ⟨E, hE⟩ := exists_pow_mul_mem_annihilatorIdeal F hU f a (fun m => by
      rw [resF_smul, ← hab, mul_smul, hb])
    have hmem : resO (X.basicOpen_le f) (f ^ E * a) ∈
        (annihilatorIdeal F U).map (resO (X.basicOpen_le f)) := Ideal.mem_map_of_mem _ hE
    have hu : IsUnit (resO (X.basicOpen_le f) (f ^ (E + k))) := by
      rw [map_pow]; exact hunit.pow _
    have hb' : b = resO (X.basicOpen_le f) (f ^ E * a) * ↑hu.unit⁻¹ := by
      rw [Units.eq_mul_inv_iff_mul_eq, IsUnit.unit_spec, pow_add, map_mul, map_mul, ← hab]
      ring
    rw [hb']
    exact Ideal.mul_mem_right _ _ hmem

def annihilatorIdealSheaf (F : X.Modules) (hF : IsCoherent F) : X.IdealSheafData where
  ideal U := annihilatorIdeal F U
  map_ideal_basicOpen U f := by
    have := hF.1
    have := hF.2 U U.2
    exact map_annihilatorIdeal_basicOpen F U.2 f

theorem support_annihilatorIdealSheaf_subset (F : X.Modules) (hF : IsCoherent F) {T : Set X}
    (hT : IsClosed T) (hFT : Scheme.Modules.SupportedIn F T) :
    ((annihilatorIdealSheaf F hF).support : Set X) ⊆ T := by
  intro x hx
  by_contra hxT
  have := hF.1
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U : X.affineOpens := ⟨U₀, hU₀⟩
  have := hF.2 U U.2
  let V : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  obtain ⟨f, hfV, hxf⟩ := U.2.exists_basicOpen_le (V := V) ⟨x, hxT⟩ hxU
  obtain ⟨E, hE⟩ := exists_pow_mul_mem_annihilatorIdeal F U.2 f 1 (fun m =>
    hFT _ (Set.disjoint_left.2 fun y hy hyT => hfV hy hyT) _)
  rw [mul_one] at hE
  have hE' : f ^ (E + 1) ∈ (annihilatorIdealSheaf F hF).ideal U := by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ hE
  have hx' : x ∈ (annihilatorIdealSheaf F hF).support := hx
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (show x ∈ U.1 from hxU),
    Scheme.mem_zeroLocus_iff] at hx'
  exact hx' _ hE' (by rwa [Scheme.basicOpen_pow _ _ (Nat.succ_pos E)])

end

end GroundTheory.Arith.SchemeCoh
