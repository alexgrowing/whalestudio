import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolSplit

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {r : ℕ}

theorem map_sigR {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (p : A →ₐ[F] B) (z : A ⊗[F] E) :
    (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom (sigR A σ z) =
      sigR B σ ((Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_JR {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (p : A →ₐ[F] B)
    (J : Matrix (Fin r) (Fin r) E) :
    (JR A J).map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = JR B J := by
  ext i j; simp [JR, inclR]

theorem map_unit {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (p : A →ₐ[F] B)
    (J : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (A ⊗[F] E)) :
    (Formalism.UG.cT (sigR A σ) g * JR A J * g).map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom =
      Formalism.UG.cT (sigR B σ) (g.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom) * JR B J *
        g.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom := by
  rw [Matrix.map_mul, Matrix.map_mul, map_JR]
  congr 2
  ext i j
  exact map_sigR σ p _

end Gen

theorem exists_adelic_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), ∃ e : HA (AF F) σ J ≃ₜ* HA (Ainf F) σ J × HA (Af F) σ J, ∀ h, ((HA.mat (Af F) σ J (e h).2 : GL (Fin M) (Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) = finMat σ J h ∧ ((HA.mat (Ainf F) σ J (e h).1 : GL (Fin M) (Ainf F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)) = ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) := by
  intro F E _ _ _ _ _ σ r J
  let pInf : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  let pFin : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  obtain ⟨e, he, hc, hc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have ext : ∀ {M N : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}, M.map pInf = N.map pInf → M.map pFin = N.map pFin →
      M = N := fun {M N} h1 h2 => by
    ext i j
    refine e.injective (Prod.ext ?_ ?_)
    · rw [(he _).1, (he _).1]; exact congrFun (congrFun h1 i) j
    · rw [(he _).2, (he _).2]; exact congrFun (congrFun h2 i) j
  let gl : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E) → Matrix (Fin r) (Fin r) (Af F ⊗[F] E) →
      Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := fun M N => Matrix.of fun i j => e.symm (M i j, N i j)
  have g1 : ∀ M N, (gl M N).map pInf = M := fun M N => by
    ext i j
    exact ((he _).1.symm.trans (congrArg Prod.fst (e.apply_symm_apply _)))
  have g2 : ∀ M N, (gl M N).map pFin = N := fun M N => by
    ext i j
    exact ((he _).2.symm.trans (congrArg Prod.snd (e.apply_symm_apply _)))
  let χ : HA (AF F) σ J →* HA (Ainf F) σ J × HA (Af F) σ J :=
    { toFun := fun h => ((⟨Formalism.UG.bc pInf (HA.mat _ _ _ h), (by
          have := congrArg (fun M => M.map pInf) (show Formalism.UG.cT _ _ * _ * _ = _ from h.2)
          rw [map_unit σ (fstA F), map_JR (fstA F)] at this
          exact this)⟩ : HR (Ainf F) σ J),
        (⟨Formalism.UG.bc pFin (HA.mat _ _ _ h), (by
          have := congrArg (fun M => M.map pFin) (show Formalism.UG.cT _ _ * _ * _ = _ from h.2)
          rw [map_unit σ (sndA F), map_JR (sndA F)] at this
          exact this)⟩ : HR (Af F) σ J))
      map_one' := Prod.ext (Subtype.ext (map_one (Formalism.UG.bc pInf))) (Subtype.ext (map_one (Formalism.UG.bc pFin)))
      map_mul' := fun a b => Prod.ext (Subtype.ext (map_mul (Formalism.UG.bc pInf) _ _))
        (Subtype.ext (map_mul (Formalism.UG.bc pFin) _ _)) }
  let ω : HA (Ainf F) σ J × HA (Af F) σ J → HA (AF F) σ J := fun g =>
    (⟨⟨gl g.1.1.val g.2.1.val, gl g.1.1.inv g.2.1.inv,
      ext (by rw [Matrix.map_mul, g1, g1, g.1.1.val_inv]; simp) (by rw [Matrix.map_mul, g2, g2, g.2.1.val_inv]; simp),
      ext (by rw [Matrix.map_mul, g1, g1, g.1.1.inv_val]; simp) (by rw [Matrix.map_mul, g2, g2, g.2.1.inv_val]; simp)⟩,
      ext ((map_unit σ (fstA F) J _).trans (Eq.trans (by
        rw [g1]
        exact g.1.2) (map_JR (fstA F) J).symm)) ((map_unit σ (sndA F) J _).trans (Eq.trans (by
        rw [g2]
        exact g.2.2) (map_JR (sndA F) J).symm))⟩ : HR (AF F) σ J)
  have l1 : Function.LeftInverse ω χ := fun h => Subtype.ext (Units.ext (ext (g1 _ _) (g2 _ _)))
  have l2 : Function.RightInverse ω χ := fun g =>
    Prod.ext (Subtype.ext (Units.ext (g1 _ _))) (Subtype.ext (Units.ext (g2 _ _)))
  let ψ : HA (AF F) σ J ≃* HA (Ainf F) σ J × HA (Af F) σ J :=
    { χ with invFun := ω, left_inv := l1, right_inv := l2 }
  have hp1 : Continuous pInf := (continuous_fst.comp hc).congr fun z => (he z).1
  have hp2 : Continuous pFin := (continuous_snd.comp hc).congr fun z => (he z).2
  have hv : Continuous fun h : HA (AF F) σ J => HA.mat _ _ _ h := continuous_subtype_val
  have c1 : Continuous ψ := by
    refine Continuous.prodMk (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _)
      (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _)
    · exact (Units.continuous_val.comp hv).matrix_map hp1
    · exact (Units.continuous_coe_inv.comp hv).matrix_map hp1
    · exact (Units.continuous_val.comp hv).matrix_map hp2
    · exact (Units.continuous_coe_inv.comp hv).matrix_map hp2
  have c2 : Continuous ψ.symm := by
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · refine continuous_matrix fun i j => hc'.comp (Continuous.prodMk ?_ ?_)
      · exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)).matrix_elem i j
      · exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_elem i j
    · refine continuous_matrix fun i j => hc'.comp (Continuous.prodMk ?_ ?_)
      · exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst)).matrix_elem i j
      · exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_snd)).matrix_elem i j
  exact ⟨{ ψ with continuous_toFun := c1, continuous_invFun := c2 }, fun h => ⟨rfl, rfl⟩⟩

end GlobalTheory.Mem.VolSplit
