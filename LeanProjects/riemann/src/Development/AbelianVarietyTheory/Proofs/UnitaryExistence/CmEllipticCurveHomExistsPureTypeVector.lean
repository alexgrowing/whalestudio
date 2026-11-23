import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueLinearLiftUniformisedFibres
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUnique

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CurveHomLift

open UniformLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem exists_linear_lift_of_isHolTo (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) {m : ℕ} (e : (Fin m → ℂ) → (Over.mk (F.u i P) ⟶ Xo.univ.t.G))
    (he : ∀ z w, e (z + w) = e z * e w) (hol : IsHolTo Set.univ fun z => (e z).left) :
    ∃ L : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, F.ex i P (L z) = e z := by
  have hsm : Smooth Xo.univ.t.G.hom := Xo.univ.t.semi.smooth
  have hsm' : Smooth (pullback.snd Xo.univ.t.G.hom (F.u i P)) := inferInstance
  have hol' := ExpUniqFamily.isHolTo_ex F i P hP
  have he' := F.ex_add i P hP
  have hd := isDerivAt0_fibre _ Xo.univ.t.G (F.u i P) g (F.ex i P) _ _ _ (fun z => fibPt _ (F.ex i P z))
    (IsPullback.of_hasPullback Xo.univ.t.G.hom (F.u i P))
    (fun z => ⟨fibPt_fst _ _, fibPt_snd _ _⟩) hol' (F.ex_diff i P hP)
  obtain ⟨k, k0, hka, hk⟩ := LocalLift.exists_local_lift _ (pullback.snd Xo.univ.t.G.hom (F.u i P)) m g
    (fun z => fibPt _ (e z)) (fun z => fibPt _ (F.ex i P z)) hsm'
    (fun z => fibPt_snd _ _) (fun z => fibPt_snd _ _)
    (HolFibre.isHolTo_fibPt isOpen_univ _ _ e hol) (HolFibre.isHolTo_fibPt isOpen_univ _ _ _ hol') hd
    (by simp only [map_zero_eq_one e he, map_zero_eq_one _ he'])
  have hker : ((toAddHom (F.ex i P) he').ker : Set (Fin g → ℂ)) = P.range := Set.ext fun z => F.ex_ker i P hP z
  exact (existsUnique_linearMap_lift_of_germ (ex := toAddHom e he) (ex' := toAddHom (F.ex i P) he')
    (hker ▸ isDiscrete_iff_discreteTopology.2 hP.2.2.1) hka.differentiableAt k0
    (hk.mono fun z hz => fibPt_injective _ hz)).exists

theorem isHolTo_pt (C : Curve H) : IsHolTo Set.univ fun z : Fin 1 → ℂ => C.pt (z 0) := by
  intro U f
  obtain ⟨h1, h2⟩ := C.u.hol U f
  have hd : Differentiable ℂ (fun (z : Fin 1 → ℂ) (_ : Fin C.P.g) => C.c * z 0) := by fun_prop
  refine ⟨?_, h2.comp hd.differentiableOn fun z hz => hz.2⟩
  exact isOpen_univ.inter (h1.preimage hd.continuous)

theorem pt_one (C : Curve H) : C.pt 1 = C.pt 0 := by
  have h1 := (C.u.ker _).2 ((C.lat fun _ => C.c * 1).2 ⟨1, 0, by simp⟩)
  have h0 := (C.u.ker _).2 ((C.lat fun _ => C.c * 0).2 ⟨0, 0, by simp⟩)
  rw [Curve.pt, Curve.pt, h1, h0]

theorem exists_pure_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (φ : C.P.A.left ⟶ Xo.univ.t.G.left) (x : ℂ → (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ε : ℤˣ), (∀ z, (x z).left = C.pt z ≫ φ) → (∀ z w, x (z + w) = x z * x w) → (∀ z, x ((1 + ((ε : ℤ) : ℂ) * H.rt0) / 2 * z) = x z ≫ Xo.univ.t.act.act H.w0) → ∃ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∀ z : ℂ, x z = F.ex i P (z • P a) := by
  intro E _ _ _ H D l Xo σ g ty F _ _ _ _ C i P hP φ x ε hx hadd hw
  obtain ⟨L, hL⟩ := exists_linear_lift_of_isHolTo F i P hP (m := 1) (fun z => x (z 0)) (fun z w => hadd _ _) (by
    simp only [hx]
    exact HolFibre.isHolTo_comp (isHolTo_pt C) φ)
  have hv : ∀ z : ℂ, x z = F.ex i P (z • L fun _ => 1) := fun z => by
    rw [← map_smul, hL]
    simp
  have h1 : x 1 = 1 := by
    rw [← map_zero_eq_one x hadd]
    exact Over.OverMorphism.ext (by rw [hx, hx, pt_one])
  rw [hv, one_smul, F.ex_ker i P hP] at h1
  obtain ⟨a, ha⟩ := h1
  rw [← ha] at hv
  refine ⟨a, fun j hj => ?_, hv⟩
  set w : ℂ := (1 + ((ε : ℤ) : ℂ) * H.rt0) / 2 with hwdef
  have key : ∀ z : ℂ, z • (w • P a - P (H.w0 • a)) ∈ P.range := fun z => by
    have e1 := hw z
    rw [hv, hv, ← F.ex_lin i P hP] at e1
    have e2 : (fun k => ty k (H.w0 : E) * (z • P a) k) = z • P (H.w0 • a) := by
      funext k
      simp only [Pi.smul_apply, smul_eq_mul, hP.1]
      ring
    have e3 := F.ex_add i P hP (z • (w • P a - P (H.w0 • a))) (z • P (H.w0 • a))
    rw [← smul_add, sub_add_cancel, smul_smul, mul_comm z w, e1, e2] at e3
    exact (F.ex_ker i P hP _).1 (mul_eq_right.1 e3.symm)
  obtain ⟨b, hb⟩ := key 1
  rw [one_smul] at hb
  have hb0 : b = 0 := eq_zero_of_line hP (hb ▸ key)
  rw [hb0, map_zero] at hb
  have e4 := congrFun hb j
  simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hP.1] at e4
  have e5 : 2 * ty j (H.w0 : E) = 1 + ty j (H.rt : E) := by
    have := congrArg (fun s : 𝓞 E => ty j (s : E)) H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  by_contra hne
  apply hj
  have e6 : w = ty j (H.w0 : E) := mul_right_cancel₀ hne (sub_eq_zero.1 e4.symm)
  rw [hwdef] at e6
  linear_combination -e5 - 2 * e6

end GlobalTheory.CurveHomLift
