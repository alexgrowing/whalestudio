import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace LevelPoints

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem section_ext [IsReduced S] {G : Over S} [IsSeparated G.hom] (f g : 𝟙_ (Over S) ⟶ G)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      toUnit (Over.mk x) ≫ f = toUnit (Over.mk x) ≫ g) : f = g := by
  have : IsReduced (𝟙_ (Over S)).left := ‹IsReduced S›
  refine Over.OverMorphism.ext (hom_ext_of_geometricPoints_dense G.hom f.left g.left
    ((Over.w f).trans (Over.w g).symm) Set.univ dense_univ fun k _ _ x _ => ?_)
  have e : (toUnit (Over.mk (Y := Sp k) (X := S) x)).left = x :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (Y := Sp k) (X := S) x)))
  have := congrArg CommaMorphism.left (h k x)
  simp only [Over.comp_left] at this
  rw [e] at this
  exact this

theorem eta_zero (o : Obj D l b s) : o.eta 0 = 1 := o.eta_ker 0 (Submodule.zero_mem _)

theorem eta_nsmul (o : Obj D l b s) (n : ℕ) (a : D.La) : o.eta (n • a) = o.eta a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, eta_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem natCast_mem (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
  rw [← l.prod] at h
  exact Ideal.mul_le_left h

theorem eta_pow (o : Obj D l b s) (a : D.La) : o.eta a ^ l.M = 1 := by
  rw [← eta_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact o.eta_ker _ (Submodule.smul_mem_smul (natCast_mem l) Submodule.mem_top)

theorem eta_smul [IsReduced S] (o : Obj D l b s) (c : 𝓞 E) (a : D.La) :
    o.eta (c • a) = o.eta a ≫ o.t.act.act c := by
  have := o.proper
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (l.coprime ▸ Submodule.mem_top :
    (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  have key : ∀ a : D.La, o.eta a = o.eta (v • a) := fun a => by
    conv_lhs => rw [← one_smul (𝓞 E) a, ← huv, add_smul, o.eta_add,
      o.eta_ker _ (Submodule.smul_mem_smul hu Submodule.mem_top), _root_.one_mul]
  refine section_ext _ _ fun k _ _ x => ?_
  obtain ⟨-, I, -, -, hI⟩ := o.geom k x (Spec.preimage (x ≫ s)).hom (by
    rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage])
  rw [key a, key (c • a), ← Category.assoc, hI _ (Submodule.smul_mem_smul hv Submodule.mem_top),
    hI _ (Submodule.smul_mem_smul hv Submodule.mem_top), smul_comm v c a, I.lin]

end LevelPoints

theorem moduli_univ_eta_killed :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (a : Dw.La), (∀ b ∈ l.Mb, Xo.univ.eta a ≫ Xo.univ.t.act.act b = 1) ∧ (∀ b : 𝓞 E, Xo.univ.eta (b • a) = Xo.univ.eta a ≫ Xo.univ.t.act.act b) ∧ Xo.univ.eta a ^ l.M = 1 := by
  intro _ E _ _ _ H Dw l Xo a
  have := UnivPol.isReduced Xo
  refine ⟨fun c hc => ?_, fun c => LevelPoints.eta_smul _ c a, LevelPoints.eta_pow _ a⟩
  rw [← LevelPoints.eta_smul]
  exact Xo.univ.eta_ker _ (Submodule.smul_mem_smul hc Submodule.mem_top)

end GlobalTheory
