import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.OmRes

variable {R : Type} [CommRing R]

theorem val_map_coc {X : Scheme.{0}} {s : X ⟶ Sp R} (E E' : SqExt R) (φ : E.C →ₐ[R] E'.C) (φ₀ : E.B →ₐ[R] E'.B)
    (hπ : ∀ c, φ₀ (E.π c) = E'.π (φ c))
    (hi : ∀ b, φ (E.i b) = E'.i (φ₀ b)) (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C))
    (y' : Sp E'.C ⟶ X) (hy' : y' ≫ s = spMap (algebraMap R E'.C))
    (a : Thick.triv E.C y hy ⟶ Thick.triv E'.C y' hy') (ha : ∀ c, a.φ c = φ c)
    (e : spMap (φ : E.C →+* E'.C) ≫ y = y') (f : Z1 (O (dp0 R) s)) :
    ∃ b : E'.B, E'.val y' hy' f = φ (E.val y hy f) + (ev f a : E'.C) - E'.i b := by
  have e₀ : spMap (φ₀ : E.B →+* E'.B) ≫ spMap (E.π : E.C →+* E.B) ≫ y =
      spMap (E'.π : E'.C →+* E'.B) ≫ y' := by
    rw [← e, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    exact RingHom.ext hπ
  let Φ := E.thickHom E' φ φ₀ hπ (E.red_w hy) (E'.red_w hy') e₀
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ Thick.triv E'.B _ (E'.red_w hy') := Thick.trivHom φ₀ e₀
  have k1 := ev_sq f a (E'.idHom hy') (E.idHom hy) Φ ha
  have k2 := ev_sq f b (E'.secHom (E'.red_w hy') E'.i E'.π_i) (E.secHom (E.red_w hy) E.i E.π_i)
    Φ fun c ↦ (hi c).symm
  refine ⟨ev f b, ?_⟩
  rw [SqExt.val_apply, SqExt.val_apply, map_sub]
  have k1' : (ev f a : E'.C) + (ev f (E'.idHom hy') : E'.C) = φ (ev f (E.idHom hy)) + (ev f Φ : E'.C) := k1
  have k2' : E'.i (ev f b) + (ev f (E'.secHom (E'.red_w hy') E'.i E'.π_i) : E'.C) =
    φ (ev f (E.secHom (E.red_w hy) E.i E.π_i)) + (ev f Φ : E'.C) := k2
  linear_combination k2' - k1'

attribute [local instance] cotOp cotCentral cotTower

variable {D D' : Type} [CommRing D] [Bialgebra R D] [CommRing D'] [Bialgebra R D']

def rho (φ : D →ₐc[R] D') : (cotExt R D).C →ₐ[R] (cotExt R D').C := TrivSqZeroExt.map (cotMap φ)

theorem cotSnd_cotPt (a : D) : cotSnd R D (cotPt R D a) = dUnit R a := by
  simp [cotSnd, cotPt, TrivSqZeroExt.algebraMap_eq_inl, dUnit]

theorem cotSnd_rho (φ : D →ₐc[R] D') (c : (cotExt R D).C) : cotSnd R D' (rho φ c) = cotMap φ (cotSnd R D c) :=
  TrivSqZeroExt.snd_map _ _

theorem rho_cotPt (φ : D →ₐc[R] D') (a : D) : rho φ (cotPt R D a) = cotPt R D' (φ a) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · refine (TrivSqZeroExt.fst_map _ _).trans ?_
    simp [cotPt, TrivSqZeroExt.algebraMap_eq_inl]
  · exact (cotSnd_rho φ _).trans (by rw [cotSnd_cotPt, cotMap_d]; exact (cotSnd_cotPt _).symm)

theorem cotVal_map {X : Over (Sp R)} (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (φ : D →ₐc[R] D') (y : Pt X D) :
    cotVal f (spOver (φ : D →ₐ[R] D') ≫ y) =
      cotMap φ (cotVal f y) + dUnit R (fv f D D' (φ : D →ₐ[R] D') y) := by
  let z : Pt X (cotExt R D).C := spOver (cotPt R D) ≫ y
  let z' : Pt X (cotExt R D').C := spOver (cotPt R D') ≫ spOver (φ : D →ₐ[R] D') ≫ y
  have e : spMap (rho φ : (cotExt R D).C →+* (cotExt R D').C) ≫ z.left = z'.left := by
    change spMap _ ≫ spMap _ ≫ y.left = spMap _ ≫ spMap _ ≫ y.left
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    exact RingHom.ext (rho_cotPt φ)
  let a : trivAt z ⟶ trivAt z' := Thick.trivHom (rho φ) e
  obtain ⟨b, hb⟩ := val_map_coc (cotExt R D) (cotExt R D') (rho φ) (AlgHom.id R R)
    (fun c ↦ (TrivSqZeroExt.fst_map _ _).symm) (fun r ↦ TrivSqZeroExt.map_inl _ _) z.left z.w z'.left z'.w a
    (fun _ ↦ rfl) e f
  have k : rho φ (fv f D _ (cotPt R D) y) + (ev f a : (cotExt R D').C) =
      cotPt R D' (fv f D D' (φ : D →ₐ[R] D') y) + fv f D' _ (cotPt R D') (spOver (φ : D →ₐ[R] D') ≫ y) :=
    ev_sq f (trivMap (cotPt R D) y) a (trivMap (φ : D →ₐ[R] D') y) (trivMap (cotPt R D') _) (rho_cotPt φ)
  have h0 : cotSnd R D' ((cotExt R D').i b) = 0 := rfl
  change cotSnd R D' ((cotExt R D').val z'.left z'.w f - _) =
    cotMap φ (cotSnd R D ((cotExt R D).val z.left z.w f - _)) + _
  rw [← cotSnd_rho, ← cotSnd_cotPt, ← map_add, ← sub_zero (cotSnd R D' (_ + _)), ← h0, ← map_sub, hb, map_sub (rho φ)]
  congr 1
  linear_combination k

theorem cotMap_res_om (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ) :
    cotMap (G.res n) (d.om (n + 1)) = d.om n := by
  have h := cotVal_map d.f (G.res n) (t.y (n + 1))
  rw [t.res n, d.res n] at h
  rw [Dat.om, Dat.om, h, map_sub, cotMap_d]
  simp only [dUnit, map_sub]
  abel

end GlobalTheory.PtExt.OmRes
