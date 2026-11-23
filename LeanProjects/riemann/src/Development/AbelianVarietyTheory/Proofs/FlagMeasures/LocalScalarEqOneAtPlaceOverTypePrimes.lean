import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HL

theorem GCoord.c_eq_one_of_gS_mem : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) {T T' : D.host.E} (F00 : LFlag (VS D) D.R.rS T) (F'0 : LFlag (VS D) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS) (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → G.c (below D P) = 1 := by
  intro D X Y T T' F00 F'0 FP G c P hP
  set p : PlF D := below D P with hp
  have hmem : ∀ n : ℕ, ((n : 𝓞 D.host.F) ∈ p.asIdeal ↔ ((n : 𝓞 D.host.E)) ∈ P.asIdeal) := by
    intro n
    show (n : 𝓞 D.host.F) ∈ Ideal.comap _ P.asIdeal ↔ _
    rw [Ideal.mem_comap, map_natCast]
  have hg : ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
    have h1 : ((gS D : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := (hmem _).2 hP
    simp only [gS, Nat.cast_mul] at h1
    rcases p.isPrime.mem_or_mem h1 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hg
  have hchar : Loc.resChar p = D.host.g i := by
    have hz : ((D.host.g i : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
      exact hi
    have hd : ringChar (𝓞 D.host.F ⧸ p.asIdeal) ∣ D.host.g i := ringChar.dvd hz
    exact (Nat.prime_dvd_prime_iff_eq (D.s.atP p).ellPrime.out (D.host.g_prime i)).1 hd
  have hgp : gpart p = D.host.g i := by
    have hne := D.host.g_ne
    fin_cases i
    · simp [gpart, hchar]
    · simp [gpart, hchar, Ne.symm hne]
  have hδ := Y.δ_pin p i hi
  have hne : ∀ j, ((D.host.g j : ℕ) : D.host.E) ≠ 0 := fun j => Nat.cast_ne_zero.2 (D.host.g_prime j).ne_zero
  have hneF : ∀ j, ((D.host.g j : ℕ) : D.host.F) ≠ 0 := fun j => Nat.cast_ne_zero.2 (D.host.g_prime j).ne_zero
  have key := c.c_eq p
  have hone : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((G.c p).val) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep 1 := by
    rw [key]
    change algebraMap _ _ (Y.δ p) * _ = _
    rw [hδ, ← (D.s.atP p).compat, ← map_mul, map_one]
    have h1 : algebraMap D.host.F D.host.E ((D.host.g 0 : D.host.F) * D.host.g 1 / D.host.g i) *
        ((uP p : ℚ) : D.host.E) = 1 := by
      simp only [uP, hgp, gS, map_div₀, map_mul, map_natCast]
      push_cast
      have := hne 0; have := hne 1; have := hne i
      field_simp
    rw [h1, map_one]
  haveI : Nontrivial (D.s.atP p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  have hv : ((G.c p).val : (D.s.atP p).Fp) = 1 :=
    (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective hone
  exact Units.ext hv

end GlobalTheory.HL
