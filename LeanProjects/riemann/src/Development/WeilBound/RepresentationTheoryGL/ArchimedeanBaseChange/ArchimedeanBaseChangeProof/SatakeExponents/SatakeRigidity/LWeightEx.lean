import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.ThetaOfCsdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicWeightOfAutomorphicDefiniteUnitarStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedHolds2

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.F

namespace PositivityTheory.Rg.BcB.F.Rig

theorem weight_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (π : Submodule ℂ (UA E 0 → ℂ))
    (hπ : IsAutRepU π) (τ : E →+* ℂ) : ∃ lam : DomWeight 0, HasWeightAt π τ lam := by
  let lam : DomWeight 0 := ⟨fun i => i.elim0, fun i => i.elim0⟩
  refine ⟨lam, GlobalTheory.DefU.isIrreducible_sqRep 0 lam, ?_⟩
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hπ.ne_bot
  obtain ⟨v, hv⟩ := exists_ne (0 : nablaSq ℂ 0 lam)
  obtain ⟨c, hc⟩ : ∃ c : Module.Dual ℂ (nablaSq ℂ 0 lam), c v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
  have hg : ∀ g : GL (Fin 0) ℂ, g = 1 := fun g => Units.ext (funext fun i => i.elim0)
  have hu : ∀ y : UA E 0, y = 1 := fun y => Subtype.ext (Units.ext (funext fun i => i.elim0))
  refine ⟨LinearMap.smulRight c φ, fun h => ?_, fun w => π.smul_mem _ hφ, fun x w => ?_⟩
  · have h1 := LinearMap.congr_fun h v
    rw [LinearMap.smulRight_apply, LinearMap.zero_apply, smul_eq_zero] at h1
    exact h1.elim hc hφ0
  · rw [hg (((cEmb τ).comp (embU 0 τ).subtype) x), hu (x : UA E 0), map_one, map_one]
    rfl

theorem weightEx : WeightEx := by
  intro E _ _ _ n π hπ τ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact weight_zero π hπ τ
  · exact GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E n hn π hπ τ

theorem infOfWeight_reg {n : ℕ} (lam : DomWeight n) : (infOfWeight lam).Nodup ∧
    ∀ x ∈ infOfWeight lam, ∃ k : ℤ, x = k + ((n : ℂ) - 1) / 2 := by
  refine ⟨Multiset.Nodup.map (fun k k' h => ?_) Finset.univ.nodup, fun x hx => ?_⟩
  · have h2 : ((lam.w k - ((k : ℕ) : ℤ) : ℤ) : ℂ) = ((lam.w k' - ((k' : ℕ) : ℤ) : ℤ) : ℂ) := by
      push_cast
      linear_combination h
    have h3 : lam.w k - ((k : ℕ) : ℤ) = lam.w k' - ((k' : ℕ) : ℤ) := by exact_mod_cast h2
    rcases le_total k k' with hk | hk
    · have h4 := lam.anti hk
      have h5 : (k : ℕ) ≤ k' := hk
      exact Fin.ext (by omega)
    · have h4 := lam.anti hk
      have h5 : (k' : ℕ) ≤ k := hk
      exact Fin.ext (by omega)
  · obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
    exact ⟨lam.w k - ((k : ℕ) : ℤ), by push_cast; ring⟩

theorem regPart : RegPart := by
  intro E _ _ _ n D hr i τ
  obtain ⟨lam, hlam⟩ := hr τ
  have hle : D.m i τ ≤ infOfWeight lam := by
    rw [← hlam, ← Finset.add_sum_erase Finset.univ (fun j => D.m j τ) (Finset.mem_univ i)]
    exact Multiset.le_add_right _ _
  obtain ⟨h1, h2⟩ := infOfWeight_reg lam
  exact ⟨D.m i τ, D.inf i τ, Multiset.nodup_of_le hle h1, fun x hx => h2 x (Multiset.subset_of_le hle hx)⟩

theorem rStrings : RStrings := by
  intro hR E _ _ _ n D hr i
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨m, hm, hnd, hx⟩ := hR E n D hr i τ
  have hRI : RegInt (D.V i) τ := ⟨m, hm, hnd, fun x hx' y hy => by
    obtain ⟨k, rfl⟩ := hx x hx'
    obtain ⟨k', rfl⟩ := hx y hy
    exact ⟨k - k', by push_cast; ring⟩⟩
  obtain ⟨a, d, P, hu, hn, he⟩ := ascSeed_holds2.1 E (D.N i) (D.pos i) (D.V i) (D.discrete i) τ hRI
  obtain ⟨h, -⟩ := he P (Setoid.refl (α := CuspSub E a) P)
  have hda : d * a = D.N i := by simpa using h
  have hpos := D.pos i
  refine ⟨a, d, P, ?_, ?_, hu, hn, he⟩
  · rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha, Nat.mul_zero] at hda
      omega
    · exact ha
  · rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd, Nat.zero_mul] at hda
      omega
    · exact hd

end PositivityTheory.Rg.BcB.F.Rig

end
