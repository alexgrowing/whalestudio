import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.MixSeedPAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.ExistsSplittingAuxiliaryCharacterForTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.SeedSym
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
open UpperTheory.V.Z.Win.Birth

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

private theorem finOrd_kills {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {l : ℕ} [Fact l.Prime] {M : ℕ} (hM : 1 ≤ M) {φ : G ℚ Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) : IsOfFinOrder φ := by
  have ho : IsOpen (φ.ker : Set (G ℚ Ω)) := by
    have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
      classical
      refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
      simpa [Polynomial.mem_nthRoots hM] using hζ
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)
    · simp only [Set.mem_iInter]
      exact fun ζ _ => Subgroup.one_mem _
    · simp only [Set.mem_iInter] at hs
      exact hφ s fun ζ hζ => hs ζ hζ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hfi : Finite (G ℚ Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  have hpos : 0 < φ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨_, hpos, MonoidHom.ext fun s => ?_⟩
  rw [MonoidHom.pow_apply, ← map_pow]
  exact φ.ker.pow_index_mem s

private theorem cong_iff {l : ℕ} [Fact l.Prime] {c : Coef l} (a : c.Oˣ) :
    Cong (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom a) 1 ↔ residue c.O a = 1 := by
  rw [← map_one (residue c.O), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, (UpperTheory.V.Fr.sc_norm l c _).2]
  rfl

private theorem toB_chi {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l)
    (g : G ℚ Ω) : toB (chiO ℚ Ω l c.O) g = cycBar ℚ Ω l g := by
  ext
  rfl

theorem rhoExP (h1 : ExistsSplittingAuxiliaryCharacterForTower) (h2 : PhiFacts) (h3 : ModEx4) : RhoExP := by
  intro hP Ω _ _ _ l _ c D T₀ hctx hok hfour ι B c₀
  obtain ⟨N, w, θ, haux, hsp, hw⟩ := h1 Ω l c D T₀ hctx hfour
  obtain ⟨hcc, hev, hk⟩ := h2 Ω l c D T₀ hctx hok hfour
  have hodd : Odd l := (Fact.out : l.Prime).odd_of_ne_two haux.odd
  have hcc' : toB (phi D T₀.pr) D.cc = -1 := by
    show Units.map _ (phi D T₀.pr D.cc) = _
    rw [hcc]
    ext
    simp
  have hne : toB (phi D T₀.pr) ≠ 1 := by
    intro h
    have h' := congrArg (fun u : (Qbar l)ˣ => (u : Qbar l)) hcc'
    rw [h] at h'
    simp only [MonoidHom.one_apply, Units.val_one, Units.val_neg] at h'
    have h2' : (2 : Qbar l) = 0 := by linear_combination h'
    exact two_ne_zero h2'
  have hfin : IsOfFinOrder (toB (phi D T₀.pr)) := finOrd_kills haux.pos hsp.1
  obtain ⟨k₀, hk₀⟩ := hP l Ω ι D.cc hctx.1.isCC N w (toB (phi D T₀.pr)) θ haux hsp hne
  obtain ⟨n, hn⟩ : ∃ n, n = B + k₀ + 2 := ⟨_, rfl⟩
  have hl1 : 1 ≤ l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  have hle : n ≤ (l - 1) * n := Nat.le_mul_of_pos_left n hl1
  have hev' : Even ((l - 1) * n) := (Nat.Odd.sub_odd hodd odd_one).mul_right n
  obtain ⟨k, hkdef⟩ : ∃ k, k = D.e + 1 + (l - 1) * n := ⟨_, rfl⟩
  have hkodd : Odd k := by
    rw [hkdef, add_assoc, add_comm 1, ← add_assoc]
    exact (hev.add hev').add_one
  have hk1 : 1 ≤ k := by omega
  have hcong : k - 1 ≡ D.e [MOD l - 1] := by
    unfold Nat.ModEq
    rw [show k - 1 = D.e + (l - 1) * n by omega, Nat.add_mul_mod_self_left]
  obtain ⟨ρ, hρ, hrw⟩ := hk₀ k (by omega) (by rw [hcc', hkodd.neg_one_pow])
  obtain ⟨hsq, hdec⟩ := hk k hk1 hcong
  have e : ∀ g, (cycBar ℚ Ω l ^ (k - 1) * toB (phi D T₀.pr)) g =
      Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (Phi D T₀.pr k g) := by
    intro g
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, Phi, map_mul, map_pow]
    rw [← toB_chi c g]
    rfl
  have hI : IrrOpen ρ := by
    refine (sI l haux.odd Ω ι _ θ k (by omega) hfin ρ hρ).2 ⟨resQ T₀.F T₀.g0, fun h => hsq ?_⟩
    rw [e] at h
    have := (cong_iff (Phi D T₀.pr k (resQ T₀.F T₀.g0) ^ 2)).1 (by rw [map_pow]; exact h)
    rwa [Units.val_pow_eq_pow_val, map_pow] at this
  have hg1 : Raw.bar (Phi D T₀.pr k) (resQ T₀.F T₀.g0) ≠ 1 := fun h => hsq (by rw [h, one_pow])
  obtain ⟨c₁, h, ρ₁, x, hc₀, hM⟩ := h3 Ω l ι c D T₀.pr θ k hk1 ρ hρ hdec (resQ T₀.F T₀.g0) hg1 c₀
  exact ⟨w, θ, k, ρ, c₁, h, ρ₁, x, haux.prime, hw, haux.pow, haux.mu, by omega, hcong, hρ, ⟨hI, hrw⟩, hc₀, hM⟩

end UpperTheory.V.Cu2

end
