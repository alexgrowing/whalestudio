import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.UU
namespace SecMod
variable {F : Type} [CommRing F] {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of F)} {N : LB Y}

@[simp] theorem sec_mk (s : LB.Sec N) : (mk p s).sec = s := rfl
@[simp] theorem mk_sec (s : SecMod p N) : mk p s.sec = s := rfl

@[simp] theorem add_f (s t : SecMod p N) (j : N.ι) : (s + t).sec.f j = s.sec.f j + t.sec.f j := rfl

@[simp] theorem neg_f (s : SecMod p N) (j : N.ι) : (-s).sec.f j = - s.sec.f j := rfl

@[simp] theorem smul_f (c : F) (s : SecMod p N) (j : N.ι) :
    (c • s).sec.f j = resTop _ (scal p c) * s.sec.f j := rfl

@[simp] theorem zero_f (j : N.ι) : (0 : SecMod p N).sec.f j = 0 := rfl

@[ext] theorem ext {s t : SecMod p N} (h : ∀ j, s.sec.f j = t.sec.f j) : s = t :=
  DVR.SecOps.sec_ext h

theorem eq_zero_iff (s : SecMod p N) : s = 0 ↔ ∀ j, s.sec.f j = 0 :=
  ⟨fun h _ => h ▸ rfl, fun h => ext h⟩

@[simp] theorem sub_f (s t : SecMod p N) (j : N.ι) : (s - t).sec.f j = s.sec.f j - t.sec.f j := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_f, neg_f]

theorem sum_f {I : Type*} (S : Finset I) (s : I → SecMod p N) (j : N.ι) :
    (∑ i ∈ S, s i).sec.f j = ∑ i ∈ S, (s i).sec.f j := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, ih]

section Val
variable {X Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
  {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (r : Z ⟶ Y)
include hJ

theorem sval_add (s t : SecMod p (LB.LinComb L φ ε)) :
    sval (s + t).sec r z J = sval s.sec r z J + sval t.sec r z J :=
  gs_add r z _ (hJ.mem φ r) _ _

theorem sval_smul (c : F) (s : SecMod p (LB.LinComb L φ ε)) :
    sval (c • s).sec r z J = gs r z ⊤ (scal p c) * sval s.sec r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans
    (congrArg (· * sval s.sec r z J) (gs_res r z le_top (hJ.mem φ r) _))

theorem sval_zero : sval (0 : SecMod p (LB.LinComb L φ ε)).sec r z J = 0 :=
  (gs_eq r z _ (hJ.mem φ r) _).trans (by erw [map_zero, map_zero])

theorem sval_sum {I : Type*} (S : Finset I) (s : I → SecMod p (LB.LinComb L φ ε)) :
    sval (∑ i ∈ S, s i).sec r z J = ∑ i ∈ S, sval (s i).sec r z J := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, sval_zero hJ]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sval_add hJ, ih]
end Val

theorem resTop_top (c : Γ(Y, ⊤)) : resTop ⊤ c = c := by
  show (Y.presheaf.map (𝟙 _)).hom c = c
  rw [CategoryTheory.Functor.map_id]; rfl

variable (p) in

def ofFun (a : Γ(Y, ⊤)) : SecMod p (Inh.trivLB Y) :=
  mk p ⟨fun _ => a, fun _ _ => by erw [Units.val_one, _root_.one_mul]; rfl⟩

@[simp] theorem ofFun_f (a : Γ(Y, ⊤)) (j) : (ofFun p a).sec.f j = a := rfl

theorem smul_ofFun (c : F) (a : Γ(Y, ⊤)) : c • ofFun p a = ofFun p (scal p c * a) :=
  ext fun _ => congrArg (· * a) (resTop_top (scal p c))

theorem ofFun_injective : Function.Injective (ofFun p) :=
  fun _ _ h => congrArg (fun s : SecMod p (Inh.trivLB Y) => s.sec.f PUnit.unit) h

theorem ofFun_surjective : Function.Surjective (ofFun p) :=
  fun s => ⟨s.sec.f PUnit.unit, ext fun _ => rfl⟩

theorem scal_specMap {A : Type} [CommRing A] (f : F →+* A) (c : F) :
    scal (Spec.map (CommRingCat.ofHom f)) c = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (f c) := by
  have := congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  exact this.symm

def trivEquiv (F A : Type) [CommRing F] [CommRing A] [Algebra F A] :
    A ≃ₗ[F] SecMod (Spec.map (CommRingCat.ofHom (algebraMap F A))) (Inh.trivLB (Spec (CommRingCat.of A))) :=
  LinearEquiv.ofBijective
    { toFun := fun a => ofFun _ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
      map_add' := fun a b => ext fun _ => map_add _ a b
      map_smul' := fun c a => by
        rw [RingHom.id_apply, smul_ofFun, scal_specMap, ← map_mul, Algebra.smul_def] }
    (Function.Bijective.comp (g := ofFun (Spec.map (CommRingCat.ofHom (algebraMap F A))))
      (f := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) ⟨ofFun_injective, ofFun_surjective⟩
      (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.bijective)

theorem one_ne_zero_spec [Nontrivial F] :
    ofFun (𝟙 (Spec (CommRingCat.of F))) 1 ≠ 0 := by
  intro h
  have h1 : (1 : Γ(Spec (CommRingCat.of F), ⊤)) = 0 := (eq_zero_iff _).1 h PUnit.unit
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom h1
  rw [map_one, map_zero] at h2
  exact one_ne_zero h2

theorem finrank_complex_real :
    Module.finrank ℝ (SecMod (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ)))
      (Inh.trivLB (Spec (CommRingCat.of ℂ)))) = 2 := by
  rw [← (trivEquiv ℝ ℂ).finrank_eq, Complex.finrank_real_complex]

theorem conj_smul :
    (Complex.I • ofFun (Spec.map (CommRingCat.ofHom (starRingEnd ℂ))) 1) =
      ofFun _ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom (-Complex.I)) := by
  rw [smul_ofFun, scal_specMap, _root_.mul_one, Complex.conj_I]

end SecMod
end GlobalTheory.UU
end
