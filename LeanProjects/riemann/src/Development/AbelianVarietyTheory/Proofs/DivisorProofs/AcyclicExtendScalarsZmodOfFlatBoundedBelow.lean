import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocallyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyFlatEtaleSheafLocallyDivisibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleComplexStaircaseLocallyExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafExtendScalarsZmodSectionLocallyTmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafExtendScalarsZmodKernelLocallyMultipleStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.FlatExtAcyc

variable {R : Type} [CommRing R]

lemma sres_comp {F : Shv R} {U V W : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) (s : Sec F U) :
    Sec.res k (Sec.res g s) = Sec.res (k ≫ g) s := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

lemma sres_map {F G : Shv R} (a : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map a x) = Sec.map a (Sec.res g x) := by
  have := a.hom.naturality g.op
  exact congrArg (fun t => t.hom x) this.symm

lemma sres_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 :=
  (F.obj.map g.op).hom.map_zero

lemma nsmul_self_eq_zero (q : ℕ) {F : Shv (ZMod q)} {U : Scheme.{0}} (z : Sec F U) : q • z = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by ext; simp
  rw [this, zero_smul]

end GlobalTheory.EtC.FlatExtAcyc

open GlobalTheory.EtC.FlatExtAcyc in

theorem GlobalTheory.EtC.flatExtAcyc.main : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (K : Cx (ZMod Q)) (a : ℤ) [K.IsStrictlyGE a], (∀ n, FlatS (K.X n)) → K.Acyclic → (extCx (ZMod.castHom hq (ZMod q)) K).Acyclic := by
  intro Q q _ hq K a _ hflat hK
  have hqe : q * (Q / q) = Q := Nat.mul_div_cancel' hq
  have hKloc : ∀ (n : ℤ) (U : Scheme.{0}) (b : Sec (K.X n) U), Sec.map (K.d n (n + 1)) b = 0 → Loc U fun V g => ∃ c : Sec (K.X (n - 1)) V, Sec.map (K.d (n - 1) n) c = Sec.res g b := by
    intro n U b hb
    have hex : (K.sc' (n - 1) n (n + 1)).Exact := (K.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).1 (hK n)
    exact ((GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally _ _).1 hex) U b hb
  have hz : ∀ n, n < a → ∀ (U : Scheme.{0}) (x : Sec (K.X n) U), x = 0 := by
    intro n hn U x
    have hZ : IsZero (K.X n) := K.isZero_of_isStrictlyGE a n hn
    have e1 : 𝟙 (K.X n) = 0 := hZ.eq_of_src _ _
    have h1 : Sec.map (𝟙 (K.X n)) x = x := rfl
    rw [← h1, e1]; rfl
  have hQ : ∀ (n : ℤ) (U : Scheme.{0}) (y : Sec (K.X n) U), (q * (Q / q)) • y = 0 := by
    intro n U y
    rw [hqe, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod Q))]
    have : ((Q : ℕ) : ULift.{1} (ZMod Q)) = 0 := by ext; simp
    rw [this, zero_smul]
  have hst := GlobalTheory.T.etaleComplex_staircase_locally_exact (ZMod Q) q (Q / q) K a hz hQ
    (fun n U x hx => GlobalTheory.T.locallyFlatEtaleSheaf_locally_divisible Q q (Q / q) hqe (K.X n) (hflat n) U x hx)
    (fun n U x hx => GlobalTheory.T.locallyFlatEtaleSheaf_locally_divisible Q (Q / q) q (by rw [mul_comm]; exact hqe) (K.X n) (hflat n) U x hx) hKloc
  intro n
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp), GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]

  suffices H : ∀ (U : Scheme.{0}) (z : Sec ((extSh (ZMod.castHom hq (ZMod q))).obj (K.X n)) U),
      Sec.map ((extSh (ZMod.castHom hq (ZMod q))).map (K.d n (n + 1))) z = 0 →
      Loc U fun V g => ∃ b : Sec ((extSh (ZMod.castHom hq (ZMod q))).obj (K.X (n - 1))) V,
        Sec.map ((extSh (ZMod.castHom hq (ZMod q))).map (K.d (n - 1) n)) b = Sec.res g z from H
  intro U z hzz
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.1 U _ ?_
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ (GlobalTheory.T.etaleSheafExtendScalars_zmod_section_locally_tmul Q q hq (K.X n) U z) ?_
  rintro V g ⟨x, hx⟩
  have hdx : extSh.sec (ZMod.castHom hq (ZMod q)) (K.X (n + 1)) V (Sec.map (K.d n (n + 1)) x) = 0 := by
    rw [← extSh.sec_map, hx, ← sres_map, hzz, sres_zero]
  have hloc := GlobalTheory.T.etaleSheafExtendScalars_zmod_kernel_locally_multiple Q q hq (K.X (n + 1)) V _ hdx
  have hloc' : Loc V fun W k => ∃ y : Sec (K.X (n + 1)) W, Sec.map (K.d n (n + 1)) (Sec.res k x) = q • y := by
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 V _ _ hloc ?_
    rintro W k ⟨y, hy⟩
    exact ⟨y, by rw [← sres_map, hy]⟩
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 V _ _ (hst n V x hloc') ?_
  rintro W k ⟨u, y, hy⟩
  refine ⟨extSh.sec (ZMod.castHom hq (ZMod q)) (K.X (n - 1)) W u, ?_⟩
  rw [extSh.sec_map, ← sres_comp, ← hx, extSh.sec_res, hy, map_add, map_nsmul, nsmul_self_eq_zero, add_zero]
