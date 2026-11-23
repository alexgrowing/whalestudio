import Formalism.LocalToGlobal.GlobalTheory.GL6.FrameTranslate
import Formalism.LocalToGlobal.GlobalTheory.GL6.AdmissibleOfSplitAndRoundTrips

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem rnd_cls (S : StepLevel F E σ J T f bad) (γ0 : GL (Fin n) E) (hγ0 : γ0 ∈ UJ (σ : E →+* E) J)
    (y1 y2 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (k : S.U)
    (h : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ0 * y1.1 = y2.1 * k.1) :
    (Quotient.mk'' y1 : Cls S) = Quotient.mk'' y2 := by
  have hkU : k.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := ((S.U_eq k.1).1 k.2).1
  have e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ0 = y2.1 * k.1 * y1.1⁻¹ := by
    rw [← h]; group
  have hb : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ0 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
    rw [e]; exact Subgroup.mul_mem _ (Subgroup.mul_mem _ y2.2 hkU) (Subgroup.inv_mem _ y1.2)
  refine (DoubleCoset.eq _ _ y1 y2).2 ⟨⟨bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ0, hb⟩,
    ?_, ⟨k.1⁻¹, Subgroup.inv_mem _ hkU⟩, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 ⟨γ0, hγ0, rfl⟩
  · exact Subgroup.mem_subgroupOf.2 (S.U.inv_mem k.2)
  · apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [h]; group

theorem rnd_chi (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hb : v ∉ bad)
    (η η' : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hη : ∀ v', v' ≠ v → bc (prV (E := E) v') η.1 = 1) (hη' : ∀ v', v' ≠ v → bc (prV (E := E) v') η'.1 = 1)
    (κ κ' k : S.U) (hk : k.1 = η.1 * κ.1 * η'.1 * κ'.1) : S.chi k = S.chi κ * S.chi κ' := by
  have key : S.chi ((κ * κ')⁻¹ * k) = 1 := by
    apply S.chi_triv
    intro v'' hv''
    have hne : v'' ≠ v := fun e => hb (e ▸ hv'')
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hk, map_mul, map_inv, hη v'' hne, hη' v'' hne, mul_one, one_mul]
    group
  rw [map_mul, map_inv, inv_mul_eq_one] at key
  rw [← key, map_mul]

end Gen

variable {D : D7} {u : D.what₂.Word}

def RndStab (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) c, RndStabTriv (Tf.cls i hi).lev ((Tf.cls i hi).y c)

set_option maxHeartbeats 2000000 in

def RUpLoc (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (z : ↥(Ld D u i hi c)), (D.fm u).fv i v c ((Tf.lv i hi).pr v c z) = 1 →
    ∃ e : (D.fm u).lk i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lv i v c,
      e ((D.fm u).te i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))) = (Tf.lv i hi).pr v c z ∧
      ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
        (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
          ((Tf.cls i hi).y ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))).1 = ((Tf.cls i hi).y c).1 * η.1 * κ.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c) →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c ⊔
            Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))))
          (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u i hi c),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = (D.fm u).fv i v c ((Tf.lv i hi).pr v c ⟨_, hx⟩)) →
      ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
        (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
          ((Tf.cls i hi).y ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))
            (((D.fm u).fv i v c).comp e.toLinearMap))).1 =
          ((Tf.cls i hi).y ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))).1 * η'.1 * κ'.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))
                  (((D.fm u).fv i v c).comp e.toLinearMap)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))
            (((D.fm u).fv i v c).comp e.toLinearMap))))
          (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) =
            (((D.fm u).fv i v c).comp e.toLinearMap)
              ((Tf.lv i hi).prk v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) ⟨_, hx⟩)) →
      η.1 * κ.1 * η'.1 * κ'.1 ∈ (Tf.cls i hi).lev.U

set_option maxHeartbeats 2000000 in

def RDnLoc (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ((D.fm u).te i v c) = 1 →
    ∃ e : (D.fm u).lv i v ((D.fm u).dn i v c g) ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lk i v c,
      (D.fm u).fv i v ((D.fm u).dn i v c g) = g.comp e.toLinearMap ∧
      ∀ (z : ↥(Ld D u i hi ((D.fm u).dn i v c g))),
        (Tf.lv i hi).pr v ((D.fm u).dn i v c g) z = e.symm ((D.fm u).te i v c) →
      ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
        (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
          ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 = ((Tf.cls i hi).y c).1 * η'.1 * κ'.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v c g))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c g))) (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = g ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
      ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
        (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
          ((Tf.cls i hi).y ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z))).1 =
          ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 * η.1 * κ.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v)
                  (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi ((D.fm u).dn i v c g)) →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v)
                  (mulLat γ.1.1 (Ld D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi ((D.fm u).dn i v c g) ⊔
            Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z))))
          (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u i hi ((D.fm u).dn i v c g)),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) =
            (D.fm u).fv i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v ((D.fm u).dn i v c g) ⟨_, hx⟩)) →
      η'.1 * κ'.1 * η.1 * κ.1 ∈ (Tf.cls i hi).lev.U

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
