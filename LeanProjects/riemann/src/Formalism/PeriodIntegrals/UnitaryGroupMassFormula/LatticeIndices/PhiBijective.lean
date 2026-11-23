import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfParts

noncomputable section

namespace MassDataIdxSplit

open scoped TensorProduct

variable {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]

def phi (σ : E →ₐ[F] E) (ι : E →ₐ[F] K) : K ⊗[F] E →ₐ[K] K × K :=
  Algebra.TensorProduct.lift (Algebra.ofId K (K × K)) (ι.prod (ι.comp σ)) (fun _ _ => Commute.all _ _)

theorem phi_tmul (σ : E →ₐ[F] E) (ι : E →ₐ[F] K) (x : K) (e : E) :
    phi σ ι (x ⊗ₜ[F] e) = (x * ι e, x * ι (σ e)) := by
  simp [phi, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Prod.algebraMap_apply]

theorem phi_bijective (σ : E →ₐ[F] E) (ι : E →ₐ[F] K) (h2 : Module.finrank F E = 2) (a : E) (ha : σ a ≠ a) :
    Function.Bijective (phi σ ι) := by
  have hne : ι a - ι (σ a) ≠ 0 := by
    intro h
    exact ha (ι.injective (sub_eq_zero.mp h)).symm
  have hsurj : Function.Surjective (phi σ ι) := by
    rintro ⟨u, v⟩
    refine ⟨((u - v) / (ι a - ι (σ a))) ⊗ₜ[F] a + (u - (u - v) / (ι a - ι (σ a)) * ι a) ⊗ₜ[F] (1 : E), ?_⟩
    rw [map_add, phi_tmul, phi_tmul]
    simp only [map_one, mul_one, Prod.mk_add_mk, Prod.mk.injEq]
    constructor
    · ring
    · field_simp
      ring
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have hr : Module.finrank K (K ⊗[F] E) = Module.finrank K (K × K) := by
    rw [Module.finrank_baseChange, h2, Module.finrank_prod, Module.finrank_self]
  have key := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr
    (f := (phi σ ι).toLinearMap)).mpr (by exact hsurj)
  exact ⟨by exact key, hsurj⟩

theorem phi_sig (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (ι : E →ₐ[F] K) (t : K ⊗[F] E) :
    phi σ ι (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR K σ t) = (phi σ ι t).swap := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, phi_tmul, hσ, Prod.swap_prod_mk]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]
    rfl

end MassDataIdxSplit

namespace MassDataIdxSteps

open Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting

def EmbP {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : Prop :=
  Nonempty (X.B.I.E →ₐ[X.B.I.F] FpX X p)

theorem splitTheta_of {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) (h : EmbP X p) :
    ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ := by
  obtain ⟨ι⟩ := h
  have hσ : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have h2 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have hex : ∃ a, X.B.I.cm.sig a ≠ a := by
    by_contra hne
    push_neg at hne
    have htop : (⊥ : Subalgebra X.B.I.F X.B.I.E) = ⊤ := by
      refine eq_top_iff.mpr fun x _ => Algebra.mem_bot.mpr ?_
      obtain ⟨y, hy⟩ := (X.B.I.cm.fixed x).1 (hne x)
      exact ⟨y, hy⟩
    have := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp htop
    omega
  obtain ⟨a, ha⟩ := hex
  exact ⟨AlgEquiv.ofBijective (MassDataIdxSplit.phi X.B.I.cm.sig ι)
    (MassDataIdxSplit.phi_bijective _ ι h2 a ha), fun t => MassDataIdxSplit.phi_sig _ hσ ι t⟩

end MassDataIdxSteps
