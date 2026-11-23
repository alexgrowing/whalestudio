import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff

noncomputable section

namespace GlobalTheory.TwV.Xc.Unif

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV
  Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

section OneAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def oneAt (w : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] w.adicCompletion F) : AfE F E :=
  Formalism.UG.P.afsplitIE w a + (1 - Formalism.UG.P.afsplitEps E w)

theorem prV_oneAt_self (w : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] w.adicCompletion F) :
    prV (E := E) w (oneAt w a) = a := by
  rw [oneAt, map_add, map_sub, map_one, Formalism.UG.P.afsplit_prV_IE, Formalism.UG.P.afsplit_prV_eps, sub_self, add_zero]

theorem prV_oneAt_ne (w w' : HeightOneSpectrum (𝓞 F)) (h : w' ≠ w) (a : E ⊗[F] w.adicCompletion F) :
    prV (E := E) w' (oneAt w a) = 1 := by
  rw [oneAt, map_add, map_sub, map_one, Formalism.UG.P.afsplit_prV_IE_ne w w' h, Formalism.UG.P.afsplit_prV_eps_ne w w' h,
    sub_zero, zero_add]

theorem ext_prV {x y : AfE F E} (h : ∀ w : HeightOneSpectrum (𝓞 F), prV (E := E) w x = prV (E := E) w y) : x = y := by
  rw [← sub_eq_zero]
  exact Formalism.UG.P.afsplit_inj _ fun w => by rw [map_sub, h, sub_self]

theorem oneAt_mul (w : HeightOneSpectrum (𝓞 F)) (a b : E ⊗[F] w.adicCompletion F) :
    oneAt w a * oneAt w b = oneAt w (a * b) := ext_prV fun w' => by
  by_cases h : w' = w
  · subst h; rw [map_mul, prV_oneAt_self, prV_oneAt_self, prV_oneAt_self]
  · rw [map_mul, prV_oneAt_ne w w' h, prV_oneAt_ne w w' h, prV_oneAt_ne w w' h, one_mul]

theorem oneAt_one (w : HeightOneSpectrum (𝓞 F)) : oneAt (E := E) w 1 = 1 := ext_prV fun w' => by
  by_cases h : w' = w
  · subst h; rw [prV_oneAt_self, map_one]
  · rw [prV_oneAt_ne w w' h, map_one]

theorem sigR_oneAt (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] w.adicCompletion F) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (oneAt w a) = oneAt w (sigR σ (w.adicCompletion F) a) := by
  rw [oneAt, oneAt, map_add, map_sub, map_one, Formalism.UG.P.afsplit_sigR_IE, Formalism.UG.P.afsplit_sigR_eps]

def oneAtU (w : HeightOneSpectrum (𝓞 F)) (a : (E ⊗[F] w.adicCompletion F)ˣ) : (AfE F E)ˣ :=
  ⟨oneAt w a, oneAt w (a⁻¹ : (E ⊗[F] w.adicCompletion F)ˣ),
    by rw [oneAt_mul, Units.mul_inv, oneAt_one], by rw [oneAt_mul, Units.inv_mul, oneAt_one]⟩

theorem oneAtU_coe (w : HeightOneSpectrum (𝓞 F)) (a : (E ⊗[F] w.adicCompletion F)ˣ) :
    (oneAtU w a : AfE F E) = oneAt w a := rfl

end OneAt

theorem exists_unif : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) [Fact p.Prime],
    LocGood σ J A → ∀ v, ∃ π ∈ U1 σ, OneOff (A.pl v).1 π ∧ ordA A v π = 1 := by
  intro F E _ _ _ _ _ σ n p G A J _ H v
  have hp0 : (p : (A.pl v).1.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F ((A.pl v).1.adicCompletion F))]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  let c : ((A.pl v).1.adicCompletion F × (A.pl v).1.adicCompletion F)ˣ :=
    ⟨((p : (A.pl v).1.adicCompletion F), (p : (A.pl v).1.adicCompletion F)⁻¹),
      ((p : (A.pl v).1.adicCompletion F)⁻¹, (p : (A.pl v).1.adicCompletion F)),
      Prod.ext (mul_inv_cancel₀ hp0) (inv_mul_cancel₀ hp0), Prod.ext (inv_mul_cancel₀ hp0) (mul_inv_cancel₀ hp0)⟩
  let a : (E ⊗[F] (A.pl v).1.adicCompletion F)ˣ := Units.map (A.spl v).symm.toMonoidHom c
  have ha : A.spl v (a : E ⊗[F] (A.pl v).1.adicCompletion F) =
      ((p : (A.pl v).1.adicCompletion F), (p : (A.pl v).1.adicCompletion F)⁻¹) := by
    show A.spl v ((A.spl v).symm _) = _
    rw [RingEquiv.apply_symm_apply]
  refine ⟨oneAtU (A.pl v).1 a, ?_, fun w' hw' => prV_oneAt_ne _ w' hw' _, ?_⟩
  · rw [U1, MonoidHom.mem_ker]
    apply Units.ext
    show oneAt (A.pl v).1 (a : E ⊗[F] (A.pl v).1.adicCompletion F) *
        sigR σ (FiniteAdeleRing (𝓞 F) F) (oneAt (A.pl v).1 (a : E ⊗[F] (A.pl v).1.adicCompletion F)) = 1
    rw [sigR_oneAt, oneAt_mul, ← oneAt_one (E := E) (A.pl v).1]
    congr 1
    apply (A.spl v).injective
    rw [map_mul, H.sig v, ha, map_one]
    show (((p : (A.pl v).1.adicCompletion F), (p : (A.pl v).1.adicCompletion F)⁻¹) *
      ((p : (A.pl v).1.adicCompletion F)⁻¹, (p : (A.pl v).1.adicCompletion F)) :
        (A.pl v).1.adicCompletion F × (A.pl v).1.adicCompletion F) = 1
    exact Prod.ext (mul_inv_cancel₀ hp0) (inv_mul_cancel₀ hp0)
  · have := (G.P.setting v).frac_alt
    have hp := (G.P.setting v).p_unif
    have h1 := ordP_eq (Qq := G.P.Qq v) hp 1 1
    have h2 : phiA A v (oneAtU (A.pl v).1 a : AfE F E) = (p : G.P.Qq v) := by
      simp only [phiA, RingHom.comp_apply, oneAtU_coe, prV_oneAt_self]
      show (A.eQ v).symm ((A.spl v (a : E ⊗[F] (A.pl v).1.adicCompletion F)).1) = _
      rw [ha, map_natCast]
    unfold ordA
    rw [h2]
    simpa using h1

end GlobalTheory.TwV.Xc.Unif

end
