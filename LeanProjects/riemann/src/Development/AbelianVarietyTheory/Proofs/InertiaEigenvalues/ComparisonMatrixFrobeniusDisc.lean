import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BasisMatrixMapCancelLeftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBreuilKisinHomUniformizerFrobeniusLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTwoHomsERegularAssociatedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomsAgreeOnWittStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitClosedDiscFrobeniusEisensteinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeBasisFrobeniusEquationDiscStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Height

private theorem map_smul_ringHom' {n : Type} {α β : Type} [CommRing α] [CommRing β] (F : α →+* β) (c : α)
    (M : Matrix n n α) : (c • M).map F = F c • M.map F :=
  Matrix.map_smul' F c M (map_mul F)

private theorem smul_cancel' {n : Type} {D : Type} [CommRing D] {c : D} (hc : c ∈ nonZeroDivisors D)
    {M M' : Matrix n n D} (h : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact (mul_cancel_left_mem_nonZeroDivisors hc).1 this

private theorem alg' {n : Type} [Fintype n] [DecidableEq n] {D : Type} [CommRing D] (Φ : D →+* D)
    (L pf pg fE gE : D) (a N : ℕ) (xf xg Af Ag ε Fm : Matrix n n D)
    (h1f : (L * pf ^ N) • (xf * Af) = fE ^ (a + 2 * N) • (Fm * xf.map Φ))
    (h1g : (L * pg ^ N) • (xg * Ag) = gE ^ (a + 2 * N) • (Fm * xg.map Φ))
    (hR : gE ^ N • (xf * ε) = fE ^ N • xg) (hpf : Φ fE = pf) (hpg : Φ gE = pg) :
    (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (gE ^ (a + N) • (Af * ε.map Φ))) =
      (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (fE ^ (a + N) • (ε * Ag))) := by
  have hΦR : pg ^ N • (xf.map Φ * ε.map Φ) = pf ^ N • xg.map Φ := by
    have := congrArg (fun M => M.map Φ) hR
    simpa only [map_smul_ringHom', Matrix.map_mul, map_pow, hpf, hpg] using this
  calc (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (gE ^ (a + N) • (Af * ε.map Φ)))
      = (pg ^ N * gE ^ (a + 2 * N)) • (((L * pf ^ N) • (xf * Af)) * ε.map Φ) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (pg ^ N * gE ^ (a + 2 * N)) • ((fE ^ (a + 2 * N) • (Fm * xf.map Φ)) * ε.map Φ) := by rw [h1f]
    _ = (gE ^ (a + 2 * N) * fE ^ (a + 2 * N)) • (Fm * (pg ^ N • (xf.map Φ * ε.map Φ))) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (gE ^ (a + 2 * N) * fE ^ (a + 2 * N)) • (Fm * (pf ^ N • xg.map Φ)) := by rw [hΦR]
    _ = (fE ^ (a + 2 * N) * pf ^ N) • (gE ^ (a + 2 * N) • (Fm * xg.map Φ)) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (fE ^ (a + 2 * N) * pf ^ N) • ((L * pg ^ N) • (xg * Ag)) := by rw [h1g]
    _ = (fE ^ (a + N) * L * pf ^ N * pg ^ N) • ((fE ^ N • xg) * Ag) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (fE ^ (a + N) * L * pf ^ N * pg ^ N) • ((gE ^ N • (xf * ε)) * Ag) := by rw [hR]
    _ = (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (fE ^ (a + N) • (ε * Ag))) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring

theorem rel_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B), toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) → ∀ (f g : Hom bk.prism B) (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε → ∀ Φ : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀ X) bk.ρ₀, IsDiscMap B.D.φ Φ → toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf g bk.E) ^ (ht.a + s.N) • ((ht.A.map (BK.hf f)).map (toDisc l (BK.hf f₀ X) bk.ρ₀) * ε.map Φ) = toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f bk.E) ^ (ht.a + s.N) • (ε * (ht.A.map (BK.hf g)).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := by
  intro l _ K bk d ρ τ s ht hτ B f₀ hE f g ε hR Φ hΦ

  have hρpos : 0 < bk.ρ₀ := by
    unfold BK.ρ₀; exact NNReal.rpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos)
  have hρle : bk.ρ₀ ≤ 1 := by
    unfold BK.ρ₀
    exact NNReal.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)
      (by have : (0 : ℝ) ≤ 1 / (bk.Ep.natDegree : ℝ) := by positivity
          linarith)

  have hnS : ‖toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a X)‖ ≤ bk.ρ₀ := by
    rw [frobS_X]
    refine (norm_toDisc_pow_le (l := l) (u := (X : bk.S)) l hρpos).trans ?_
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρle) (Fact.out : l.Prime).ne_zero
  have hΦS := isDiscMap_map (frobS l bk.a) hnS

  have key : ∀ (h : Hom bk.prism B) (Fh : Disc l (X : bk.S) bk.ρ₀ →+* Disc l (BK.hf f₀ X) bk.ρ₀), IsDiscMap (BK.hf h) Fh →
      (((l : Disc l (BK.hf f₀ X) bk.ρ₀) ^ s.c₁ * toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E)) ^ s.N) •
        (ht.bas.map Fh * (ht.A.map (BK.hf h)).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) =
      toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) ^ (ht.a + 2 * s.N) • (s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf h).comp C)) * (ht.bas.map Fh).map Φ)) := by
    intro h Fh hFh
    have hφ : ∀ x, BK.hf h (frobS l bk.a x) = B.D.φ (BK.hf h x) := fun x => h.f_φ x
    have c1 : IsDiscMap (B.D.φ.comp (BK.hf h)) (Φ.comp Fh) :=
      ⟨fun x => by simp [hFh.ext, hΦ.ext], fun x => (hΦ.norm_le _).trans (hFh.norm_le _)⟩
    have c2 : IsDiscMap (B.D.φ.comp (BK.hf h)) (Fh.comp (Disc.map (frobS l bk.a) hnS)) :=
      ⟨fun x => by simp [hFh.ext, hΦS.ext, hφ], fun x => (hFh.norm_le _).trans (hΦS.norm_le _)⟩
    have hc : Φ.comp Fh = Fh.comp (Disc.map (frobS l bk.a) hnS) := c1.unique c2
    have hP := congrArg (fun M => M.map Fh) (GlobalTheory.T.latticeBasis_frobenius_equation_disc l K bk d ρ τ s ht hτ _ hΦS)
    simp only [map_smul_ringHom', Matrix.map_mul, Matrix.map_map, map_mul, map_pow, map_natCast] at hP
    have eA : (ht.A.map (BK.hf h)).map (toDisc l (BK.hf f₀ X) bk.ρ₀) = ht.A.map (Fh ∘ toDisc l (X : bk.S) bk.ρ₀) := by
      ext i j; exact (hFh.ext _).symm
    have eF : s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf h).comp C)) =
        s.F.map (Fh ∘ (toDisc l (X : bk.S) bk.ρ₀).comp C) := by
      ext i j; exact (hFh.ext _).symm
    have eB : (ht.bas.map Fh).map Φ = ht.bas.map (Fh ∘ Disc.map (frobS l bk.a) hnS) := by
      ext i j; exact RingHom.congr_fun hc _
    have e1 : toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E)) = Fh (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) :=
      ((hFh.ext _).trans (congrArg _ (hφ _))).symm
    have e2 : toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) = Fh (toDisc l (X : bk.S) bk.ρ₀ bk.E) := (hFh.ext _).symm
    simp only [eA, eF, eB, e1, e2]
    exact hP

  have hn := GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀
  have hFf := isDiscMap_map (BK.hf f) (hn f).1
  have hFg := isDiscMap_map (BK.hf g) (hn g).1
  have h1f := key f _ hFf
  have h1g := key g _ hFg
  have hFm : s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf g).comp C)) = s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf f).comp C)) := by
    congr 1; funext w; simp [GlobalTheory.T.breuilKisin_prism_homs_agree_on_witt l K bk B f g w]
  simp only [hFm] at h1g

  have hreg : ∀ h : Hom bk.prism B, toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) := by
    intro h
    obtain ⟨v, hv⟩ := (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f₀ h).2.1
    have e : toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) = toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) * toDisc l (BK.hf f₀ X) bk.ρ₀ (v : B.A) :=
      (congrArg _ hv).symm.trans (map_mul _ _ _)
    exact (congrArg (· ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀)) e).mpr
      (Submonoid.mul_mem _ hE ((v.isUnit.map (toDisc l (BK.hf f₀ X) bk.ρ₀)).mem_nonZeroDivisors))
  have hunit : ∀ (h : Hom bk.prism B) (Fh : Disc l (X : bk.S) bk.ρ₀ →+* Disc l (BK.hf f₀ X) bk.ρ₀), IsDiscMap (BK.hf h) Fh →
      IsUnit (toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E))) := by
    intro h Fh hFh
    have := (GlobalTheory.T.isUnit_closedDisc_frobenius_eisenstein l K bk).map Fh
    have e : Fh (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) = toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E)) :=
      (hFh.ext _).trans (congrArg _ (h.f_φ _))
    exact (congrArg IsUnit e).mp this
  have hpf : Φ (toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f bk.E)) = toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf f bk.E)) := hΦ.ext _
  have hpg : Φ (toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf g bk.E)) = toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf g bk.E)) := hΦ.ext _
  have hAlg := alg' Φ _ _ _ _ _ _ _ _ _ _ _ _ _ h1f h1g (hR _ _ hFf hFg) hpf hpg
  have hc : ((l : Disc l (BK.hf f₀ X) bk.ρ₀) ^ s.c₁ * toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf f bk.E)) ^ s.N *
      toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf g bk.E)) ^ s.N * toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf g bk.E) ^ s.N) ∈ nonZeroDivisors _ := by
    refine Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ ?_) ?_) (pow_mem (hreg g) _)
    · exact ((isUnit_l_disc l (BK.hf f₀ X) bk.ρ₀).pow _).mem_nonZeroDivisors
    · exact ((hunit f _ hFf).pow _).mem_nonZeroDivisors
    · exact ((hunit g _ hFg).pow _).mem_nonZeroDivisors
  have hM := smul_cancel' hc hAlg
  have hF0 : Disc.map (BK.hf f) (hn f).1 (toDisc l (X : bk.S) bk.ρ₀ bk.E) ∈ nonZeroDivisors _ :=
    (congrArg (· ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀)) (hFf.ext bk.E)).mpr (hreg f)
  have := GlobalTheory.T.basis_matrix_map_cancel_left l K bk d ρ τ s ht _ _ hF0 _ _ hM
  exact this

end GlobalTheory.BSP.Height
