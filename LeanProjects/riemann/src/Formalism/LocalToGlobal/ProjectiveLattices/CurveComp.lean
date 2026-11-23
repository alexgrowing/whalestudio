import Formalism.LocalToGlobal.ProjectiveLattices.CurveInstSt
import Formalism.LocalToGlobal.ProjectiveLattices.CurveFr

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def evCAlg (hG : GenFrEx Xo c) (hT : GenFromTest Xo c hG) (Z : Comp Xo c) : Rul Xo c →ₐ[c.F] Om Z where
  toFun := evC hG Z
  map_one' := evalAt_one _ _ (genFr hG Z) (hT Z)
  map_mul' f g := evalAt_mul _ _ f g (genFr hG Z)
  map_zero' := evalAt_zero _ _ (genFr hG Z)
  map_add' f g := evalAt_add _ _ f g (genFr hG Z)
  commutes' a := by
    show evC hG Z (algebraMap c.F (Rul Xo c) a) = algebraMap c.F (Om Z) a
    rw [Algebra.algebraMap_eq_smul_one]
    show evalAt _ _ (a • (1 : Rul Xo c)) (genFr hG Z) = _
    rw [evalAt_smul, evalAt_one _ _ _ (hT Z), mul_one]

lemma evCAlg_apply (hG : GenFrEx Xo c) (hT : GenFromTest Xo c hG) (Z : Comp Xo c) (f : Rul Xo c) :
    evCAlg hG hT Z f = evC hG Z f := rfl

end Gen

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) (Ω : Type) [CommRing Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)

abbrev RZ : Type := Kp X la N ⊗[X.Kl la] (X.Kl la ⊗[B.KO] Ω)

def rzMap : Rp X la N →ₐ[Kp X la N] RZ X la N Ω :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (Algebra.TensorProduct.map (AlgHom.id _ _) gF)

lemma rzMap_emb (F : X.Forms) :
    rzMap X la N Ω gF (emb X la N F) = (1 : Kp X la N) ⊗ₜ ((1 : X.Kl la) ⊗ₜ gF F) := by
  show Algebra.TensorProduct.map (AlgHom.id _ _) (Algebra.TensorProduct.map (AlgHom.id _ _) gF)
      ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] F)) = _
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
  rfl

variable {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

abbrev RZs : Type := Localization.Away (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))

def lwZ : Lw X la w →+* RZs X la N Ω gF w :=
  Localization.awayMap (rzMap X la N Ω gF).toRingHom (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)

lemma lwZ_alg (r : Rp X la N) :
    lwZ X la N Ω gF w (algebraMap (Rp X la N) (Lw X la w) r) =
      algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF r) := by
  show (Localization.awayMap (rzMap X la N Ω gF).toRingHom (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))
      (algebraMap (Rp X la N) (Localization.Away (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) r) = _
  exact IsLocalization.map_eq _ _

def phiZ : ↥(Frac0 X la w) →ₐ[Kp X la N] RZs X la N Ω gF w where
  toRingHom := (lwZ X la N Ω gF w).comp (Frac0 X la w).val.toRingHom
  commutes' k := by
    show lwZ X la N Ω gF w (algebraMap (Kp X la N) (Lw X la w) k) = _
    rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), lwZ_alg, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]

lemma phiZ_apply (x : ↥(Frac0 X la w)) : phiZ X la N Ω gF w x = lwZ X la N Ω gF w (x : Lw X la w) := rfl

end Rec

section Inst

variable {D : D7} {T : Top D} (j : ℕ)
  (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (Z : Comp (T.Q.Xo j) T.Q.c)

def formsEvR : AddMonoidAlgebra (T.R j) (Deg D j) →ₐ[T.Q.c.F] Om Z :=
  AddMonoidAlgebra.liftNCAlgHom (evCAlg hG hT Z) 1 (fun _ _ => Commute.all _ _)

lemma formsEvR_single (d : Deg D j) (f : T.R j) :
    formsEvR j hG hT Z (AddMonoidAlgebra.single d f) = evC hG Z f := by
  show AddMonoidAlgebra.liftNC (((evCAlg hG hT Z : T.R j →+* Om Z)) : T.R j →+ Om Z)
      ((1 : Multiplicative (Deg D j) →* Om Z) : Multiplicative (Deg D j) → Om Z) (AddMonoidAlgebra.single d f) = _
  rw [AddMonoidAlgebra.liftNC_single]
  simp [evCAlg_apply]

end Inst

end Formalism.L2.Pj
