import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.Published.PoitouTate GlobalTheory.ResSel

namespace GlobalTheory.ResTrivConj

theorem map_eq_one_of_dual {R S n : Type} [CommRing R] [CommRing S] [Fintype n] [DecidableEq n] (f : R →+* S)
    (A T' : GL n R) (T : Matrix n n R) (e : R) (t : ℕ) (hT : T.map f = 1) (he : f e = 1)
    (h : e • (T' : Matrix n n R)⁻¹.transpose =
      (A : Matrix n n R) * (e ^ t • T) * ((A⁻¹ : GL n R) : Matrix n n R)) :
    (T' : Matrix n n R).map f = 1 := by
  have hs : ∀ (c : R) (M : Matrix n n R), (c • M).map f = f c • M.map f := fun c M => by
    ext a b; simp
  have h1 := congrArg (fun M : Matrix n n R => M.map f) h
  simp only [Matrix.map_mul, hs, map_pow, he, hT, one_pow, one_smul, Matrix.mul_one] at h1
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero f) (map_one f), Matrix.transpose_map,
    Matrix.transpose_eq_one, ← Matrix.coe_units_inv] at h1
  have h2 : ((T'⁻¹ : GL n R) : Matrix n n R).map f * (T' : Matrix n n R).map f = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero f) (map_one f)]
  rwa [h1, Matrix.one_mul] at h2

theorem resTriv_conj : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), SelfDual i s → ∀ g g' : GE N, IsCj X g g' → ResTriv i s g → ResTriv i s g' := by
  intro D N X i s hsd g g' h hg
  have he : eps0 X i g' = eps0 X i g := by
    haveI := X.lPrime i
    have e : MulSemiringAction.toRingAut (GE N) N.Om g' =
        (X.cc : RingAut N.Om) * MulSemiringAction.toRingAut (GE N) N.Om g * (X.cc : RingAut N.Om)⁻¹ := by
      ext x; exact h x
    have : cycZ D.host.E N.Om (X.l i) g' = cycZ D.host.E N.Om (X.l i) g := by
      simp only [cycZ, MonoidHom.comp_apply]
      rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    simp only [eps0, MonoidHom.comp_apply, this]
  obtain ⟨h1, h2⟩ := hg
  refine ⟨?_, by rw [he]; exact h2⟩
  obtain ⟨A, hA⟩ := hsd
  have hA' := hA g g' h
  rw [Tdual, he, ← Tgl_coe i s g'] at hA'
  rw [← Tgl_coe i s g']
  exact map_eq_one_of_dual _ A _ _ _ _ h1 h2 hA'

end GlobalTheory.ResTrivConj
