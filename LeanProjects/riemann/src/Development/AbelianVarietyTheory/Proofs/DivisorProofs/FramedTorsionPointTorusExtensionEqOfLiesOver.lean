import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusPairOfTorsionPointOverStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumFCalculus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAddInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Sep.LiesUniq

theorem frame_unique {R : Type} [CommRing R] [IsDomain R] [CharZero R] {I : Ideal R} (hA : AdmBase R I)
    {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (U : Unif I D A G) {w₀ : W0 U.toUnifPre} (hw₀ : w₀.IsGen) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {g : GtPtF D.toPre F} {w w' : Frm D.toPre F 1 g.b} {x : TFK (R := R) F ⟶ A.A}
    {fr : FrAt x} (hw : w.IsGen) (hw' : w'.IsGen) (hfr : fr.IsGen) (h : LiesOver U.toUnifPre w₀ g w x fr)
    (h' : LiesOver U.toUnifPre w₀ g w' x fr) :
    ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J = val w' (𝟙 _) z J := by
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hbij := (expBijF_and_expandsF_lin hL R _ hA D A G hG U).1 F
  obtain ⟨lam, -, hlam⟩ := CoefBasic.exists_frame_ratio hw hw'
  have hk : ∀ k : ℕ, 4 ≤ k → lam ^ k = 1 := fun k hk => by
    obtain ⟨W, hW, hWv⟩ := TorsionValue.exists_frm_pow w hw k
    obtain ⟨W', hW', hWv'⟩ := TorsionValue.exists_frm_pow w' hw' k
    obtain ⟨s, e, he, hs⟩ := NonVan.exists_sec_ne_zero hL R A F k hk x fr hfr
    obtain ⟨s', hs', -⟩ := (hbij k (by omega) w₀ hw₀).1 s
    have S₁ := h k (by omega) W hWv hW s s' e hs' hs
    have S₂ := h' k (by omega) W' hWv' hW' s s' e hs' hs
    have sc := TorsionValue.coef_scale (w' := W') hW (c := lam ^ k) (fun z J hJ => by
      rw [hWv z J hJ, hWv' z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hlam z J hJ, mul_pow,
        CoefBasic.cst_eq, CoefBasic.cst_eq, map_pow]) s'
    have S₃ := (GlobalTheory.AdicSum.sumF_calculus R I hA F _ _ _ e e).2.1 S₁ S₁ (lam ^ k - 1)
    have e₁ : (fun i => (lam ^ k - 1) * coef s' g W i + coef s' g W i) = coef s' g W' := funext fun i => by
      rw [sc]; ring
    rw [e₁] at S₃
    have e₂ := (GlobalTheory.AdicSum.sumF_calculus R I hA F _ _ (coef s' g W') _ _).1 S₃ S₂
    exact sub_eq_zero.1 ((mul_eq_zero.1 (add_eq_right.1 e₂)).resolve_right he)
  have h1 : lam = 1 := by
    have := hk 5 (by norm_num)
    rwa [pow_succ, hk 4 le_rfl, _root_.one_mul] at this
  intro z J hJ
  have := hlam z J hJ
  rw [h1, CoefBasic.cst_eq, map_one, _root_.one_mul] at this
  exact Units.ext this.symm

theorem eq_of_liesOver : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g g' : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (w' : Frm D.toPre (FractionRing V) 1 g'.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → (∃ o, GtPtF.IsNsmul N g' o ∧ o.IsZero) → w.IsGen → w'.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → LiesOver U.toUnifPre w₀ g' w' x fr → g = g' ∧ ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J = val w' (𝟙 _) z J := by
  intro V _ _ _ hCN D A G _ _ hG U w₀ hw₀ N hN g g' w w' x fr hg hg' hw hw' hfr h h'
  haveI : CharZero V := hCN.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩
  have hB := D.tau_bimult
  obtain ⟨p, hy, rfl, hp⟩ := GlobalTheory.T.exists_torus_pair_of_torsion_point_over V hCN D A G hG U w₀ hw₀ N hN g w x fr hg hw hfr h
  obtain ⟨p', hy', rfl, hp'⟩ := GlobalTheory.T.exists_torus_pair_of_torsion_point_over V hCN D A G hG U w₀ hw₀ N hN g' w' x fr hg' hw' hfr h'
  have hf : (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (algebraMap (FractionRing V) (FractionRing V)) = algebraMap _ _ := RingHom.comp_id _
  have hq := (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow U hN
    ((GlobalTheory.TorusExt.qkExt_iff hB _ hf p _).2 rfl) x).1 hp
  have hq' := (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow U hN
    ((GlobalTheory.TorusExt.qkExt_iff hB _ hf p' _).2 rfl) x).1 hp'
  have he := GlobalTheory.TorsionMapInj.qkToAk_injective hL.1 hL.2.1 V _ hA D A G hG U _ N hN _ _ _ hq hq'
  obtain ⟨z, hz, hz'⟩ := (GlobalTheory.TorusExt.equiv_iff hB _ _).1 he
  have e : p.g = p'.g := by
    letI := GlobalTheory.TorusExt.gtGroup D.toPre (AlgebraicClosure (FractionRing V))
    have hz₁ : p'.y = p.y + N • z := hz
    rw [hy, hy', zero_add, ← natCast_zsmul] at hz₁
    obtain rfl : z = 0 := (smul_eq_zero.1 hz₁.symm).resolve_left (by exact_mod_cast (by omega : N ≠ 0))
    rw [map_zero, add_zero] at hz'
    exact GlobalTheory.Balanced.gtExt_injective _ hf D.toPre hz'.symm
  obtain ⟨y, g, hg₁⟩ := p
  obtain ⟨y', g', hg₁'⟩ := p'
  dsimp only at e
  subst e
  exact ⟨rfl, frame_unique hA hG U hw₀ hw hw' hfr h h'⟩

end GlobalTheory.Poinc.Sep.LiesUniq
