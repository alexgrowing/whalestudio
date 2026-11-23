import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.AdelicOrbit

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem parts_inj (x y : AF F ⊗[F] E)
    (h1 : (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom x =
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom y)
    (h2 : (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom x =
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom y) : x = y := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  exact e.injective (Prod.ext (((he x).1.trans h1).trans (he y).1.symm) (((he x).2.trans h2).trans (he y).2.symm))

theorem mem_parts (g : GL (Fin M) (AF F ⊗[F] E)) :
    g ∈ HR (AF F) σ J ↔
      Formalism.UG.bc (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom g ∈ HR (Ainf F) σ J ∧
      Formalism.UG.bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom g ∈ HR (Af F) σ J := by
  have := GlobalTheory.UnitarySplit.mem_iff _ _ (parts_inj (F := F) (E := E)) (sigR _ σ) (sigR _ σ) (sigR _ σ)
    (GlobalTheory.UnitarySplit.map_sig _ _) (GlobalTheory.UnitarySplit.map_sig _ _) (JR _ J) g
  rw [GlobalTheory.UnitarySplit.map_JR, GlobalTheory.UnitarySplit.map_JR] at this
  exact this

theorem exists_fin (h : HA (AF F) σ J) :
    ∃ k : HA (Af F) σ J, (HA.mat (Af F) σ J k).1 = finMat σ J h :=
  ⟨(⟨_, ((mem_parts σ J (HA.mat (AF F) σ J h)).1 h.2).2⟩ : HR (Af F) σ J), rfl⟩

theorem exists_lift (k : HA (Af F) σ J) :
    ∃ h : HA (AF F) σ J, finMat σ J h = (HA.mat (Af F) σ J k).1 ∧
      (HA.mat (AF F) σ J h).1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom = 1 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have hs : ∀ a b, ∃ x, (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom x = a ∧
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom x = b := fun a b => by
    refine ⟨e.symm (a, b), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp
  obtain ⟨g, g1, g2⟩ := GlobalTheory.UnitarySplit.gl_glue _ _ parts_inj hs 1 (HA.mat (Af F) σ J k)
  have hg : g ∈ HR (AF F) σ J := (mem_parts σ J g).2 ⟨g1 ▸ one_mem _, g2 ▸ k.2⟩
  exact ⟨(⟨g, hg⟩ : HR (AF F) σ J), congrArg Units.val g2, congrArg Units.val g1⟩

omit [NumberField E] in
theorem projFin_smul (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) :
    projFin (h • ratTup (F := F) (AF F) x) 0 = finMat σ J h *ᵥ fun i => inclR (F := F) (Af F) (x 0 i) := by
  funext i
  have := RingHom.map_mulVec (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
    (HA.mat (AF F) σ J h).1 (fun i => inclR (F := F) (AF F) (x 0 i)) i
  refine this.trans ?_
  congr 1

omit [NumberField E] in
theorem projInf_smul (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) (i : Fin M) :
    (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom ((h • ratTup (F := F) (AF F) x) 0 i) =
      ((HA.mat (AF F) σ J h).1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom *ᵥ
        fun i => inclR (F := F) (Ainf F) (x 0 i)) i := by
  have := RingHom.map_mulVec (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
    (HA.mat (AF F) σ J h).1 (fun i => inclR (F := F) (AF F) (x 0 i)) i
  refine this.trans ?_
  congr 1

end SlopeTestRemainingChoices

theorem mem_latHat_iff : StabTransitive → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ L : Submodule (𝓞 E) (Fin M → E), IsSelfDualLat σ J L → ∀ β : F, (β = 1 ∨ β = -1) → ∀ x : Fin 1 → Fin M → E, x 0 ∈ L → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ h : HA (AF F) σ J, projFin (h⁻¹ • ratTup (F := F) (AF F) x) 0 ∈ latHat F E (L : Set (Fin M → E)) ↔ ∃ a ∈ Hstab (AF F) σ J x, a⁻¹ * h ∈ stab σ J (L : Set (Fin M → E)) := by
  intro hT F E _ _ _ _ _ σ hcm hur M J hJ L hL β hβ x hx hq h
  constructor
  · intro hm
    have hO := (hT F E σ hcm hur M J hJ L hL β hβ (x 0) hx hq).2.1
    obtain ⟨k', hk'⟩ := exists_fin σ J h⁻¹
    have h1 : k'⁻¹ ∈ {h : HA (Af F) σ J | actV (Af F) σ J h⁻¹ (fun i => inclR (F := F) (Af F) (x 0 i)) ∈
        latHat F E (L : Set (Fin M → E))} := by
      rw [Set.mem_setOf_eq, inv_inv, actV_eq, hk', ← projFin_smul]
      exact hm
    rw [hO] at h1
    obtain ⟨af, haf, kf, hkf, e⟩ := h1
    obtain ⟨a, ha1, ha2⟩ := exists_lift σ J af
    refine ⟨a, ?_, ?_⟩
    · change a • ratTup (F := F) (AF F) x = ratTup (F := F) (AF F) x
      funext c i
      obtain rfl : c = 0 := Subsingleton.elim _ _
      refine parts_inj _ _ ?_ ?_
      · rw [projInf_smul, ha2, Matrix.one_mulVec]
        rfl
      · have h2 := congrFun (projFin_smul σ J a x) i
        rw [ha1] at h2
        refine h2.trans ?_
        have h3 : af • ratTup (F := F) (Af F) (fun _ : Fin 1 => x 0) = ratTup (F := F) (Af F) (fun _ => x 0) := haf
        exact congrFun (congrFun h3 0) i
    · have e' : k' * af = kf⁻¹ := by
        have e2 : af * kf = k'⁻¹ := e
        rw [← inv_inv k', ← e2]
        group
      have h2 : h⁻¹ * a ∈ stab σ J (L : Set (Fin M → E)) := by
        intro y
        rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, ha1, ← hk', ← Matrix.mulVec_mulVec, ← actV_eq, ← actV_eq, ← actV_mul, e']
        exact (inv_mem hkf : kf⁻¹ ∈ stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E)))) y
      have h3 := inv_mem h2
      rwa [_root_.mul_inv_rev, inv_inv] at h3
  · rintro ⟨a, ha, hk⟩
    have h1 : a⁻¹ • ratTup (F := F) (AF F) x = ratTup (F := F) (AF F) x := inv_mem ha
    have h2 : h⁻¹ • ratTup (F := F) (AF F) x = (a⁻¹ * h)⁻¹ • ratTup (F := F) (AF F) x := by
      conv_rhs => rw [← h1, ← mul_smul]
      congr 1
      group
    rw [h2, projFin_smul]
    exact ((inv_mem hk : (a⁻¹ * h)⁻¹ ∈ stab σ J (L : Set (Fin M → E))) _).1
      (AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, x 0, hx, rfl⟩)

end GlobalTheory.AdelicOrbit
