import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

variable {l : ℕ} [Fact l.Prime]

theorem map_linv (f : Per.AinfP l →+* Per.AinfP l) : f (linv l) = linv l := by
  have h := congrArg f (mul_linv (l := l))
  rw [map_mul, map_natCast, map_one] at h
  have h2 := mul_linv (l := l)
  linear_combination (linv l) * h - f (linv l) * h2

theorem beta_mem_kerP (ϖ : Per.Fl l) (hu : ϖ.untilt = ((l : ℕ) : Per.OC l)) : beta ϖ ∈ Per.kerP l := by
  rw [← ThetaD.fontaineTheta_eq_zero]
  have h := congrArg (Per.θP l) (l_mul_beta ϖ)
  rw [map_mul, map_sub, map_natCast, ThetaD.fontaineTheta_algebraMap₂, WittVector.fontaineTheta_teichmuller, hu] at h
  have hl : ((l : ℕ) : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  refine (mul_eq_zero.1 (h.trans ?_)).resolve_left hl
  simp

theorem gal_beta (g : GQ l) (ϖ e : Per.Fl l) (h : Per.σF g ϖ = ϖ * e) :
    Per.extP (Per.σA g) (beta ϖ) = beta ϖ + algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.mu e) +
      beta ϖ * algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.mu e) := by
  have e1 : Per.σA g (Per.tm ϖ) = Per.tm ϖ * Per.tm e := by
    have h1 := gal_quot g ϖ e h 1
    simp only [map_one, mul_one, map_sub] at h1
    exact sub_left_injective h1
  rw [beta, map_sub, map_mul, map_one, map_linv, GlobalTheory.RingBasics.awayMap_algebraMap₂, e1, map_mul]
  simp only [GlobalTheory.MemLoc.mu, map_sub, map_one]
  ring

theorem isLogP_map {e : Per.Fl l} (he : e.untilt = 1) {t : Per.Acris l} (ht : IsLogA e t)
    {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) :
    IsLogP (algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.mu e)) (j t) := by
  intro n
  have hu : ∀ k : ℕ, ∃ u : Per.AinfP l, ((k + 1 : ℕ) : Per.AinfP l) * u = 1 := fun k =>
    (GlobalTheory.RingBasics.isUnit_nat l _ k.succ_ne_zero).exists_right_inv
  choose u hu using hu
  have hf : ∀ k : ℕ, IsUnit ((k.factorial : ℕ) : Per.AinfP l) := fun k =>
    GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero
  obtain ⟨d, hd⟩ := (hf n).exists_right_inv
  obtain ⟨c, hc⟩ : ∃ c : Per.AinfP l, ((n.factorial : ℕ) : Per.AinfP l) * c =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.mu e)) ^ (k + 1) :=
    ⟨d * _, by rw [← mul_assoc, hd, one_mul]⟩
  have key := (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l j hj).2.2 n t (algebraMap (Per.AinfP l) (Per.BdRp l) c) (by
    intro r
    obtain ⟨N, hN⟩ := ht r
    obtain ⟨s, hs, z, hz⟩ := hN (max N n) (le_max_left _ _)
    refine ⟨s, z, 0, by rw [← hz]; ring, ?_⟩
    rw [map_zero, mul_zero, map_zero, ← map_sub, LogFun.ev_alg, Ideal.Quotient.eq_zero_iff_mem,
      LogFun.partial_eq u hu _ _ _ (hf _) hs, LogFun.partial_eq u hu _ _ _ (hf _) hc, ← neg_sub]
    exact neg_mem (LogFun.partial_sub_mem _ u _ (LogFun.mu_mem he) (le_max_right _ _)))
  rw [key, LogFun.ev_alg, ← map_natCast (Ideal.Quotient.mk (Per.kerP l ^ n)), ← map_mul, hc]

theorem gal_log : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (Co : Core l), Co.ζ = P.ζQ → ∀ ϖ : Per.Fl l,
  (∀ m : ℕ, (rootT ϖ m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (lRoot l m)) → ϖ.untilt = ((l : ℕ) : Per.OC l) →
  ∀ u : Per.BdRp l, IsLogP (beta ϖ) u → ∀ g : GQ l,
    Per.σDp g u = u + Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t) := by
  intro l _ P Co hζ ϖ hr hu u hlog g
  have hd : ∀ m, g (lRoot l m) = Co.ζ m ^ (PadicInt.toZModPow m (kummer P g)).val * lRoot l m := fun m => by
    rw [hζ]; exact isKummer_kummer P g m
  have hd' : ∀ m, g (lRoot l m) / lRoot l m = Co.ζ m ^ (PadicInt.toZModPow m (kummer P g)).val := fun m => by
    rw [hd, mul_div_cancel_right₀ _ (lRoot_ne_zero l m)]
  obtain ⟨e, he⟩ := exists_tilt (fun m => Co.ζ m ^ (PadicInt.toZModPow m (kummer P g)).val)
    (fun m => by rw [← hd', ← hd', div_pow, ← map_pow, lRoot_succ]) 1 (by simp [Co.ζ_zero])
  have he1 : e.untilt = 1 := Subtype.ext (by
    have := he 0
    rw [Co.ζ_zero, one_pow, map_one] at this
    exact this)
  have hxe : Per.σF g ϖ = ϖ * e := gal_eq_mul g ϖ e fun m => by
    rw [hr, he, ← map_mul, mul_comm, ← hd]
    exact GlobalTheory.RingBasics.σC_coe g _
  obtain ⟨y, -, hy, -⟩ := exists_isLogA l e he1
  rw [← log_eq Co e (kummer P g) y he hy]
  refine IsLogP.add (beta_mem_kerP ϖ hu) (LogFun.mu_mem he1) hlog (isLogP_map he1 hy Co.j_cris) ?_
  have h := IsLogP.gal hlog g
  rwa [gal_beta g ϖ e hxe] at h

end GlobalTheory.Pst.StLat
