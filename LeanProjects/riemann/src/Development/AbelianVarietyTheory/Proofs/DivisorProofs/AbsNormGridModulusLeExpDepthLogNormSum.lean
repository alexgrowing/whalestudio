import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HBdNonneg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

noncomputable section

namespace GlobalTheory.ModulNorm

open GlobalTheory.SumSize

theorem absNorm_map_of_finrank_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (I : Ideal (𝓞 F)) :
    Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) I) = Ideal.absNorm I ^ 2 := by
  rw [Ideal.absNorm_algebraMap, ← h2]
  congr 1
  exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm

theorem absNorm_le_sq_of_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (P : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm P.asIdeal ≤ Ideal.absNorm (P.under (𝓞 F)).asIdeal ^ 2 := by
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal ≤ P.asIdeal :=
    Ideal.map_le_iff_le_comap.2 le_rfl
  have hd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [absNorm_map_of_finrank_two h2] at hd
  refine Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero ?_) 2) hd
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact (P.under (𝓞 F)).ne_bot

theorem absNorm_modul_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), D.host.F = maximalRealSubfield D.host.E → (Ideal.absNorm G.modul : ℝ) ≤ Real.exp (2 * sig G) := by
  intro D T L sc G hF
  have h2 : Module.finrank D.host.F D.host.E = 2 := by
    rw [hF]; exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hmod : G.modul = ∏ v ∈ G.pl.S0, (G.pl.w v).asIdeal ^ G.pl.depth sc v := rfl
  rw [hmod, map_prod, Nat.cast_prod, sig, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod (fun v _ => by positivity) fun v hv => ?_
  have hw : Ideal.absNorm (G.pl.w v).asIdeal ≤ Ideal.absNorm v.asIdeal ^ 2 := by
    have := absNorm_le_sq_of_under h2 (G.pl.w v)
    rwa [G.pl.under_w hv] at this
  have hpos : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [map_pow, Nat.cast_pow]
  calc ((Ideal.absNorm (G.pl.w v).asIdeal : ℕ) : ℝ) ^ G.pl.depth sc v
      ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ 2) ^ G.pl.depth sc v := by
        gcongr
        exact_mod_cast hw
    _ = Real.exp (2 * ((G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal))) := by
        rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos hpos]
        congr 1
        push_cast
        ring

end GlobalTheory.ModulNorm
