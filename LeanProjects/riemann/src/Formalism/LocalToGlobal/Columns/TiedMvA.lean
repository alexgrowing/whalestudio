import Formalism.LocalToGlobal.Columns.HermitianFormLastCoordinateUniformizerVectorSelf

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SameOffC {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : Ideal (𝓞 E))
    (A B : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ (q : Ideal (𝓞 E)) (hq : q.IsMaximal), q ≠ P → q ≠ Formalism.HermitianLatticesTheory.conjIdeal (K := E) P →
    haveI := hq.isPrime
    Formalism.HermitianLatticesTheory.localization₂ q A = Formalism.HermitianLatticesTheory.localization₂ q B

variable {D : ColRec} {u : D.what₂.Word} (A : CF.AtTTied u) (P : ∀ i hi, CF.LvTied u A i hi)

set_option maxHeartbeats 4000000 in

structure AtTMovesC where

  upG : ∀ i hi v (c : (D.mem u).C.cls i), ↥(CF.Ld D u i hi c) → UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)

  up_tie : ∀ i hi v c (y : ↥(CF.Ld D u i hi c)), (D.fm u).fv i v c ((P i hi).pr v c y) = 1 →
    SameOffC (A.Pv v) (Formalism.L2.Forms.mulLat (upG i hi v c y).1.1 (CF.clsCrd D u i hi ((D.fm u).up i v c ((P i hi).pr v c y))))
        (CF.clsCrd D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.mulLat (upG i hi v c y).1.1 (CF.clsCrd D u i hi ((D.fm u).up i v c ((P i hi).pr v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CF.Ld D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.mulLat (upG i hi v c y).1.1 (CF.Ld D u i hi ((D.fm u).up i v c ((P i hi).pr v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CF.Ld D u i hi c ⊔
          Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • y.1}) ∧
      (∀ (z : ↥(CF.Ld D u i hi ((D.fm u).up i v c ((P i hi).pr v c y))))
        (hz : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((upG i hi v c y).1.1 *ᵥ z.1) ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v _ ((P i hi).pr v _ z) = (D.fm u).fv i v c ((P i hi).pr v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : ↥(CF.Ld D u i hi ((D.fm u).up i v c ((P i hi).pr v c y))))
        (hz : (upG i hi v c y).1.1 *ᵥ z.1 ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v' _ ((P i hi).pr v' _ z) = (D.fm u).fv i v' c ((P i hi).pr v' c ⟨_, hz⟩))

  dnG : ∀ i hi v (c : (D.mem u).C.cls i), Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) →
    UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)

  dn_tie : ∀ i hi v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ≠ 0 →
    SameOffC (A.Pv v) (Formalism.L2.Forms.mulLat (dnG i hi v c g).1.1 (CF.clsCrd D u i hi ((D.fm u).dn i v c g))) (CF.clsCrd D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.mulLat (dnG i hi v c g).1.1 (CF.Ld D u i hi ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CF.clsCrd D u i hi c) ∧
      (∀ (z : ↥(CF.Ld D u i hi ((D.fm u).dn i v c g))) (hz : (dnG i hi v c g).1.1 *ᵥ z.1 ∈ CF.Lk A i hi v c),
        (D.fm u).fv i v _ ((P i hi).pr v _ z) = g ((P i hi).prk v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : ↥(CF.Ld D u i hi ((D.fm u).dn i v c g))) (hz : (dnG i hi v c g).1.1 *ᵥ z.1 ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v' _ ((P i hi).pr v' _ z) = (D.fm u).fv i v' c ((P i hi).pr v' c ⟨_, hz⟩))

  dilG : ∀ i hi v, ((D.mem u).A.Fv v)ˣ → (D.mem u).C.cls i → UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)

  dil_tie : ∀ i hi v (a : ((D.mem u).A.Fv v)ˣ) c,
      Formalism.L2.Forms.mulLat (dilG i hi v a c).1.1 (CF.clsCrd D u i hi ((D.fm u).dil i v a c)) = CF.clsCrd D u i hi c ∧
      (∀ (z : ↥(CF.Ld D u i hi ((D.fm u).dil i v a c))) (hz : (dilG i hi v a c).1.1 *ᵥ z.1 ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v _ ((P i hi).pr v _ z) = (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c ((P i hi).pr v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : ↥(CF.Ld D u i hi ((D.fm u).dil i v a c))) (hz : (dilG i hi v a c).1.1 *ᵥ z.1 ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v' _ ((P i hi).pr v' _ z) = (D.fm u).fv i v' c ((P i hi).pr v' c ⟨_, hz⟩))

end Formalism.L2.Col
