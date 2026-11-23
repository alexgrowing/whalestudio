import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.FlatLoc

theorem zmod_dvd_of_mul_eq_zero (Q q e : ℕ) [NeZero Q] (hQ : q * e = Q) (r : ZMod Q)
    (hr : (e : ZMod Q) * r = 0) : ∃ s : ZMod Q, r = (q : ZMod Q) * s := by
  have he : e ≠ 0 := by
    rintro rfl; exact NeZero.ne Q (by rw [← hQ, mul_zero])
  have h1 : ((e * r.val : ℕ) : ZMod Q) = 0 := by push_cast; rw [ZMod.natCast_zmod_val]; exact hr
  rw [ZMod.natCast_eq_zero_iff] at h1
  have h2 : e * q ∣ e * r.val := by rw [mul_comm e q, hQ]; exact h1
  obtain ⟨t, ht⟩ := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero he) h2
  refine ⟨t, ?_⟩
  rw [← ZMod.natCast_zmod_val r, ht]; push_cast; ring

theorem flat_dvd (Q q e : ℕ) [NeZero Q] (hQ : q * e = Q) (N : Type*) [AddCommGroup N]
    [Module (ULift.{1} (ZMod Q)) N] [Module.Flat (ULift.{1} (ZMod Q)) N] (n : N) (hn : e • n = 0) :
    ∃ n' : N, n = q • n' := by
  have hs : ∑ _i : Unit, (e : ULift.{1} (ZMod Q)) • n = 0 := by
    simpa [Nat.cast_smul_eq_nsmul] using hn
  obtain ⟨k, a, y, hx, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (f := fun _ : Unit => (e : ULift.{1} (ZMod Q))) (x := fun _ : Unit => n) hs
  have hb : ∀ j, ∃ s : ZMod Q, (a () j).down = (q : ZMod Q) * s := fun j => by
    refine zmod_dvd_of_mul_eq_zero Q q e hQ _ ?_
    have := congrArg ULift.down (ha j)
    simpa using this
  choose s hs using hb
  refine ⟨∑ j, (ULift.up (s j) : ULift.{1} (ZMod Q)) • y j, ?_⟩
  rw [show n = ∑ j, a () j • y j from hx (), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod Q)), smul_smul]
  congr 1
  apply ULift.ext
  simp [hs j]

theorem flat_loc : ∀ (Q q e : ℕ) [NeZero Q], q * e = Q → ∀ (M : Shv (ZMod Q)), FlatS M → ∀ (U : Scheme.{0}) (x : Sec M U),
    e • x = 0 → Loc U fun V g => ∃ y : Sec M V, Sec.res g x = q • y := by
  intro Q q e _ hQ M hM U x hx
  obtain ⟨P, φ, hsurj, hinj, hflat⟩ := hM
  have hnat : ∀ {W V : Scheme.{0}} (k : W ⟶ V) (p : P.obj (op V)),
      (φ.app (op W)).hom ((P.map k.op).hom p) = Sec.res k ((φ.app (op V)).hom p) := fun k p => by
    have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.naturality k.op)) p
    simpa using this
  have hres : ∀ {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (s : Sec M U),
      Sec.res k (Sec.res g s) = Sec.res (k ≫ g) s := by
    intro W V U k g s
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  refine loc_trans U _ (loc_mono U _ _ (hsurj U x) fun V g hpg => ?_)
  obtain ⟨p, hp⟩ := hpg
  have hep : (φ.app (op V)).hom (e • p) = 0 := by
    rw [map_nsmul, hp]
    show e • (M.obj.map g.op).hom x = 0
    rw [← map_nsmul, hx, map_zero]
  refine loc_mono V _ _ (hinj V (e • p) hep) fun W k hk => ?_
  by_cases hW : Nonempty W
  · haveI := hflat W hW
    obtain ⟨p', hp'⟩ := flat_dvd Q q e hQ _ ((P.map k.op).hom p) (by rw [← map_nsmul]; exact hk)
    refine ⟨(φ.app (op W)).hom p', ?_⟩
    rw [← hres, ← hp, ← hnat, hp', map_nsmul]
  · haveI : IsEmpty W := not_nonempty_iff.mp hW
    refine ⟨0, ?_⟩
    rw [smul_zero]
    exact (sec_ext_glue (ZMod Q) M W).1 _ _ (loc_of_isEmpty W _)

end GlobalTheory.EtC.FlatLoc
