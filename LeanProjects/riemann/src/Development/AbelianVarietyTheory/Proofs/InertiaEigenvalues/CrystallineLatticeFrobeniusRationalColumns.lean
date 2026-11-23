import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionOfPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitClosedDiscFrobeniusEisenstein
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBoundsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedDiscLinearDisjointOverPowerSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsFrobeniusEqMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.FrobRational

theorem core {S A D D' : Type} [CommRing S] [IsDomain S] [CommRing A] [IsDomain A] [CommRing D] [CommRing D']
    (ev : S →+* A) (t : S →+* D) (i : A →+* D') (j : D →+* D') (hi : Function.Injective i)
    (hj : ∀ a, j (t a) = i (ev a)) (φ : A →+* A) (Φ : D' →+* D') (Ψ : D →+* D)
    (hΦ : ∀ a, Φ (i a) = i (φ a)) (hΨ : ∀ x, Φ (j x) = j (Ψ x))
    (disj : ∀ (x y : A) (f g : D), g ≠ 0 → y ≠ 0 → i x * j g = i y * j f →
      ∃ δ a : S, δ ≠ 0 ∧ ev δ * x = ev a * y)
    {d : ℕ} (lam : S) (hlam : lam ≠ 0) (W : Matrix (Fin d) (Fin d) D') (B : Matrix (Fin d) (Fin d) S)
    (hW : i (ev lam) • W.map Φ = W * B.map (i.comp ev))
    (Y : Matrix (Fin d) (Fin d) A) (Z : Matrix (Fin d) (Fin d) D) (hY : Y.det ≠ 0)
    (hYZ : W * Z.map j = Y.map i) :
    ∃ (δ : S) (A1 : Matrix (Fin d) (Fin d) S), δ ≠ 0 ∧ ev δ • Y.map φ = Y * A1.map ev := by
  classical
  set x : Matrix (Fin d) (Fin d) D := B.map t * Z.map Ψ with hx
  set P : Matrix (Fin d) (Fin d) A := ev lam • Y.map φ with hP
  have hPx : P.map i = W * x.map j := by
    have h1 : (Y.map φ).map i = (Y.map i).map Φ := by ext a b; simp [hΦ]
    have h2 : (Z.map j).map Φ = (Z.map Ψ).map j := by ext a b; simp [hΨ]
    have h3 : (B.map t).map j = B.map (i.comp ev) := by ext a b; simp [hj]
    have h4 : P.map i = i (ev lam) • (Y.map φ).map i := by ext a b; simp [hP]
    rw [h4, h1, ← hYZ, Matrix.map_mul, ← Matrix.smul_mul, hW, h2, hx, Matrix.map_mul, h3, Matrix.mul_assoc]
  have hdet : W.det * j Z.det = i Y.det := by
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← hYZ, Matrix.det_mul]
  have hZ : Z.det ≠ 0 := fun h => hY (hi (by rw [← hdet, h, map_zero, mul_zero, map_zero]))
  have hadjY : (Y.adjugate).map i = (Y.map i).adjugate := RingHom.map_adjugate i Y
  have hadjZ : (Z.adjugate).map j = (Z.map j).adjugate := RingHom.map_adjugate j Z
  have key : (Y.adjugate * P).map i = W.det • (Z.adjugate * x).map j := by
    rw [Matrix.map_mul, Matrix.map_mul, hadjY, hadjZ, hPx, ← hYZ, Matrix.adjugate_mul_distrib, Matrix.mul_assoc,
      ← Matrix.mul_assoc W.adjugate, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
  have hent : ∀ p : Fin d × Fin d, ∃ δ a : S, δ ≠ 0 ∧ ev δ * (Y.adjugate * P) p.1 p.2 = ev a * Y.det := by
    intro p
    refine disj _ _ ((Z.adjugate * x) p.1 p.2) Z.det hZ hY ?_
    have h := congrFun (congrFun key p.1) p.2
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h
    rw [h, ← hdet]; ring
  choose δ a hδ ha using hent
  refine ⟨(∏ p, δ p) * lam, Matrix.of fun r c => (∏ p ∈ Finset.univ.erase (r, c), δ p) * a (r, c),
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun p _ => hδ p) hlam, ?_⟩
  have h5 : ev (∏ p, δ p) • (Y.adjugate * P) =
      Y.det • (Matrix.of fun r c => (∏ p ∈ Finset.univ.erase (r, c), δ p) * a (r, c)).map ev := by
    ext r c
    rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, smul_eq_mul,
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ (r, c)), map_mul, map_mul, mul_assoc, ha (r, c)]
    ring
  have h6 := congrArg (fun M => Y * M) h5
  simp only [Matrix.mul_smul] at h6
  rw [← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul, smul_comm] at h6
  ext r c
  have h7 := congrFun (congrFun h6 r) c
  rw [Matrix.smul_apply, Matrix.smul_apply Y.det, smul_eq_mul, smul_eq_mul] at h7
  rw [← mul_left_cancel₀ hY h7, hP, smul_smul, map_mul]

theorem isDiscMap_comp {l : ℕ} {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] {u : A} {u' : A'}
    {u'' : A''} {ρ ρ' ρ'' : ℝ≥0} {f : A →+* A'} {g : A' →+* A''} {F : Disc l u ρ →+* Disc l u' ρ'}
    {G : Disc l u' ρ' →+* Disc l u'' ρ''} (hF : IsDiscMap f F) (hG : IsDiscMap g G) :
    IsDiscMap (g.comp f) (G.comp F) :=
  ⟨fun a => by rw [RingHom.comp_apply, hF.ext, hG.ext, RingHom.comp_apply],
    fun x => (hG.norm_le _).trans (hF.norm_le x)⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y1.det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∃ (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), δ ≠ 0 ∧ bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev := by
  intro l hl K bk τ hτ d ρ hρ s Y1 Z1 hY hYZ
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have h0 : 0 < bk.ρ₀ := NNReal.rpow_pos (zero_lt_one.trans hl1)
  have h1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg hl1
    (neg_lt_zero.2 (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))
  have hpow : bk.ρ₀ ^ l ≤ bk.ρ₀ := pow_le_of_le_one h0.le h1.le hl.out.ne_zero
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1).1
  have hi : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk _ bk.ev ι TB bk.ρ₀ h0 h1).1
  haveI : IsDomain (Ainf l) := hi.isDomain _
  obtain ⟨j, hj⟩ := exists_discMap_of_pow_dvd l _ _ bk.ev (X : bk.S) (bk.ev X) bk.ρ₀ bk.ρ₀ 1 h0
    (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨Ψ, hΨ⟩ := exists_discMap_of_pow_dvd l _ _ (frobS l bk.a) (X : bk.S) (X : bk.S) bk.ρ₀ bk.ρ₀ l h0
    (by rw [frobS_X]) hpow
  obtain ⟨Φ, hΦ⟩ := exists_discMap_of_pow_dvd l _ _ (WittVector.frobenius : Ainf l →+* Ainf l) (bk.ev X) (bk.ev X)
    bk.ρ₀ bk.ρ₀ l h0 (by rw [← bk.ev_frob, frobS_X, map_pow]) hpow
  have hcomm : Φ.comp j = j.comp Ψ := by
    have e : (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev = bk.ev.comp (frobS l bk.a) :=
      RingHom.ext fun x => (bk.ev_frob x).symm
    exact (isDiscMap_comp hj hΦ).unique (e ▸ isDiscMap_comp hΨ hj)
  have hlam : bk.iA (bk.ev ((l : bk.S) ^ (s.c₁ + s.c₂) * frobS l bk.a bk.E ^ s.N)) =
      (l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N := by
    simp only [map_mul, map_pow, map_natCast, RingHom.comp_apply]
  have hu : IsUnit (bk.iS (frobS l bk.a bk.E)) := by
    have h := (isUnit_toDisc_frobS_E l K bk).map j
    rwa [hj.ext] at h
  have hne : (l : bk.S) ^ (s.c₁ + s.c₂) * frobS l bk.a bk.E ^ s.N ≠ 0 := fun h => by
    rw [h, map_zero, map_zero] at hlam
    exact (((isUnit_l_disc l _ _).pow _).mul (hu.pow _)).ne_zero hlam.symm
  exact core bk.ev (toDisc l (X : bk.S) bk.ρ₀) bk.iA j hi hj.ext WittVector.frobenius Φ Ψ hΦ.ext
    (fun x => RingHom.congr_fun hcomm x) (GlobalTheory.T.ainf_closedDisc_linearDisjoint_over_powerSeries l K bk _ bk.ev ι TB j hj) _ hne s.W _
    (by rw [hlam]; exact GlobalTheory.T.discPeriods_map_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ) Y1 Z1 hY (hYZ j hj)

end GlobalTheory.BSP.FrobRational
