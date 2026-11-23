import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusInduction.MemOrbitIff
import GroundTheory.AutomorphicForms.WhittakerOrbit

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker MulAction

open scoped Pointwise

namespace PositivityTheory.RgUd.T.Nil.Orb.BStep

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

attribute [local instance] t2Sp lcSp tdSp contSMul lcH tdH scH contSMulH

theorem piece_count (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hξ : Inv Z ξ)
    {C U₁ : Set (Sp k n)} (hC : IsClosed C) (hU₁ : IsOpen U₁) (hU₁UU : U₁ ⊆ UU) {p : Sp k n}
    (hCinv : ∀ h ∈ Gz Z, ∀ q ∈ C, act h q ∈ C)
    (hO : U₁ ∩ C = orb Z p) (hξC : SuppU ξ C)
    {J A : Subgroup (GzS Z)} (hJc : IsCompact (J : Set (GzS Z))) (hAo : IsOpen (A : Set (GzS Z))) (hAJ : A ≤ J)
    (hn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A)
    {fJ fA : Sp k n → ℂ} (hfJ : fJ ∈ supportedIn U₁) (hfA : fA ∈ supportedIn U₁)
    (hfJO : ∀ x ∈ orb Z p, fJ x = (orbitPiece J (toT p)).indicator 1 (toT x))
    (hfAO : ∀ x ∈ orb Z p, fA x = (orbitPiece A (toT p)).indicator 1 (toT x)) :
    ξ fJ * ((A ⊓ stabilizer (GzS Z) (toT p)).relIndex (J ⊓ stabilizer (GzS Z) (toT p)) : ℂ) =
      (A.relIndex J : ℂ) * ξ fA := by
  classical
  have hOorb : orbit (GzS Z) (toT p) = orb Z p := Set.ext fun q => mem_orbit_iff' Z (p := p) (q := q)
  have hO' : ((U₁ : Set (SpT k n)) ∩ C) = orbit (GzS Z) (toT p) := by rw [hOorb]; exact hO
  have hOl : IsLocallyClosed (orbit (GzS Z) (toT p)) := ⟨U₁, C, hU₁, hC, hO'.symm⟩
  obtain ⟨𝒮, -, h𝒮, hsum⟩ := exists_finset_orbitPiece (X := SpT k n) hOl hJc hAo hAJ hn (mem_orbit_self (toT p))
  choose! j hjJ hjS using h𝒮
  have hPsub : ∀ B : Subgroup (GzS Z), ∀ x, toT x ∈ orbitPiece B (toT p) → x ∈ orb Z p := by
    intro B x hx
    exact (mem_orbit_iff' Z).1 (orbitPiece_subset_orbit (mem_orbit_self (toT p)) hx)
  have hfAUU : fA ∈ supportedIn UU := supportedIn_mono hU₁UU hfA
  have htr : ∀ S ∈ 𝒮, ξ (fun q => fA (act (((j S)⁻¹ : GzS Z) : GL (Fin n) k) q)) = ξ fA := by
    intro S _
    exact hξ _ ((j S)⁻¹).2 fA (supportedIn_mono (Set.subset_univ _) hfA)
  have hsumξ : ξ fJ = ∑ S ∈ 𝒮, ξ (fun q => fA (act (((j S)⁻¹ : GzS Z) : GL (Fin n) k) q)) := by
    rw [← map_sum]
    refine xi_eq hξC (supportedIn_mono hU₁UU hfJ)
      (Submodule.sum_mem _ fun S _ => comp_act_memUU ((j S)⁻¹ : GzS Z).1 hfAUU) fun x hx => ?_
    rw [lift_on_C' hO (hPsub J) hfJ hfJO x hx, hsum (toT x), Finset.sum_apply]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hx' : act (((j S)⁻¹ : GzS Z) : GL (Fin n) k) x ∈ C := hCinv _ ((j S)⁻¹).2 x hx
    rw [lift_on_C' hO (hPsub A) hfA hfAO _ hx']
    conv_lhs => rw [hjS S hS]
    by_cases hxS : toT (act (((j S)⁻¹ : GzS Z) : GL (Fin n) k) x) ∈ orbitPiece A (toT p)
    · rw [Set.indicator_of_mem (Set.mem_smul_set_iff_inv_smul_mem.2 (show (j S)⁻¹ • toT x ∈ _ from hxS)),
        Set.indicator_of_mem hxS]
      rfl
    · rw [Set.indicator_of_notMem (fun h' => hxS (Set.mem_smul_set_iff_inv_smul_mem.1 h')),
        Set.indicator_of_notMem hxS]
  have hcard : ξ fJ = (𝒮.card : ℂ) * ξ fA := by
    rw [hsumξ, Finset.sum_congr rfl htr, Finset.sum_const, nsmul_eq_mul]
  have hset : ((𝒮 : Set (Set (SpT k n)))) =
      (fun i : GzS Z => i • orbitPiece A (toT p)) '' (J : Set (GzS Z)) := by
    ext P
    constructor
    · intro hP
      exact ⟨j P, hjJ P hP, (hjS P hP).symm⟩
    · rintro ⟨i, hi, rfl⟩
      have hx : i • toT p ∈ orbitPiece J (toT p) := ⟨i, hi, rfl⟩
      have h1 := hsum (i • toT p)
      rw [Set.indicator_of_mem hx] at h1
      obtain ⟨S, hS, hiS⟩ : ∃ S ∈ 𝒮, i • toT p ∈ S := by
        by_contra hcon
        push Not at hcon
        rw [Finset.sum_eq_zero (fun S hS => Set.indicator_of_notMem (hcon S hS) _)] at h1
        exact one_ne_zero h1
      have e1 : i • orbitPiece A (toT p) = orbitPiece A (i • toT p) :=
        smul_orbitPiece (hn i hi) (fun a ha => by simpa using hn i⁻¹ (J.inv_mem hi) a ha) _
      have e2 : S = orbitPiece A (j S • toT p) := (hjS S hS).trans
        (smul_orbitPiece (hn _ (hjJ S hS)) (fun a ha => by simpa using hn _ (J.inv_mem (hjJ S hS)) a ha) _)
      have e3 : orbitPiece A (i • toT p) = orbitPiece A (j S • toT p) :=
        orbitPiece_eq_of_mem (e2 ▸ hiS)
      show i • orbitPiece A (toT p) ∈ (𝒮 : Set (Set (SpT k n)))
      rw [Finset.mem_coe, e1, e3, ← e2]
      exact hS
  have hc := count J A hAJ hn (toT p)
  change Nat.card ((fun i : GzS Z => i • orbitPiece A (toT p)) '' (J : Set (GzS Z))) * _ = _ at hc
  rw [← hset, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hc
  rw [hcard, mul_assoc, mul_comm (ξ fA), ← mul_assoc]
  exact_mod_cast congrArg (fun N : ℕ => (N : ℂ) * ξ fA) hc

end PositivityTheory.RgUd.T.Nil.Orb.BStep
