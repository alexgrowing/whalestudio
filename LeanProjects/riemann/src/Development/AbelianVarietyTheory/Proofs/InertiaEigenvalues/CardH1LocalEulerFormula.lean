import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesMulInvariantsDiscrete
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

namespace GlobalTheory.EulerFree

theorem card_Z1_of_invariants_eq_bot {O G M : Type} [CommRing O] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module O M] (π : Representation O G M)
    (hlc : ∀ m, IsLocallyConstant fun g => π g m) (h0 : π.invariants = ⊥) :
    Nat.card (ReciprocityTheory.Def.Z1 π ⊤) = Nat.card (ReciprocityTheory.Def.H1 π ⊤) * Nat.card M := by
  have hle : ReciprocityTheory.Def.B1 π ⊤ ≤ ReciprocityTheory.Def.Z1 π ⊤ := by
    rintro _ ⟨m, -, rfl⟩
    refine ⟨⟨(hlc m).comp (fun x => x - m), fun _ => Submodule.mem_top⟩, ?_⟩
    funext x
    change π x.1 (π x.2 m - m) - (π (x.1 * x.2) m - m) + (π x.1 m - m) = 0
    simp only [map_mul, Module.End.mul_apply, map_sub]
    abel
  have h1 := Submodule.card_eq_card_quotient_mul_card
    ((ReciprocityTheory.Def.B1 π ⊤).submoduleOf (ReciprocityTheory.Def.Z1 π ⊤))
  have h2 : Nat.card ((ReciprocityTheory.Def.B1 π ⊤).submoduleOf (ReciprocityTheory.Def.Z1 π ⊤)) =
      Nat.card (ReciprocityTheory.Def.B1 π ⊤) := Nat.card_congr (Submodule.comapSubtypeEquivOfLe hle).toEquiv
  have hinj : Function.Injective (ReciprocityTheory.Def.d0 π) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff, ← h0]
    intro m hm g
    exact sub_eq_zero.1 (congrFun (LinearMap.mem_ker.1 hm) g)
  have h3 : Nat.card (ReciprocityTheory.Def.B1 π ⊤) = Nat.card M :=
    (Nat.card_congr (Submodule.topEquiv.symm.trans
      (Submodule.equivMapOfInjective _ hinj ⊤)).toEquiv).symm
  rw [h1, h2, h3, mul_comm]

theorem card_H1_of_euler (R O G G' : Type) [CommRing R] [CommRing O] [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] (φ : G' ≃* G) (hφ : Continuous φ ∧ Continuous φ.symm)
    (M : Type) [AddCommGroup M] [Module R M] [Module O M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation R G M) (hrho : ReciprocityTheory.Gal.ContAction rho) (d : ℕ)
    (hEu : Nat.card (ReciprocityTheory.Gal.H1 rho) =
      Nat.card (ReciprocityTheory.Gal.H0 rho) * Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ d)
    (π : Representation O G' M) (ha : ∀ g m, rho g m = π (φ.symm g) m)
    (hlc : ∀ m, IsLocallyConstant fun g => π g m) (h0 : π.invariants = ⊥)
    (h2 : Subsingleton (ReciprocityTheory.Def.H2 π ⊤)) :
    Nat.card (ReciprocityTheory.Def.H1 π ⊤) = Nat.card M ^ d := by
  have ha' : ∀ g m, rho (φ g) m = π g m := fun g m => by rw [ha, φ.symm_apply_apply]
  have hH0 : Nat.card (ReciprocityTheory.Gal.H0 rho) = 1 := by
    have : ReciprocityTheory.Gal.H0 rho = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have : m ∈ π.invariants := fun g => by rw [← ha']; exact hm (φ g)
      rw [h0] at this
      exact this
    rw [this]
    exact Nat.card_unique
  have hH2 : Nat.card (ReciprocityTheory.Gal.H2 rho) = 1 := by
    have : Subsingleton (ReciprocityTheory.Gal.H2 rho) := by
      refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun z _ => ?_)
      let z' : ReciprocityTheory.Def.Z2 π ⊤ := ⟨fun x => z.1 (φ x.1, φ x.2),
        ⟨(IsLocallyConstant.iff_continuous _).2 (z.2.1.comp
          ((hφ.1.comp continuous_fst).prodMk (hφ.1.comp continuous_snd))), fun _ => Submodule.mem_top⟩, by
        funext x
        have := z.2.2 (φ x.1) (φ x.2.1) (φ x.2.2)
        rw [ha', ← map_mul, ← map_mul] at this
        exact this⟩
      have hz' : z' ∈ (ReciprocityTheory.Def.B2 π ⊤).submoduleOf (ReciprocityTheory.Def.Z2 π ⊤) := by
        rw [Submodule.Quotient.subsingleton_iff.1 h2]
        exact Submodule.mem_top
      obtain ⟨b, hb, hbz⟩ := hz'
      refine ⟨fun g => b (φ.symm g), hb.1.continuous.comp hφ.2, ?_⟩
      funext x
      have h : π (φ.symm x.1) (b (φ.symm x.2)) - b (φ.symm x.1 * φ.symm x.2) + b (φ.symm x.1) =
          z.1 (φ (φ.symm x.1), φ (φ.symm x.2)) := congrFun hbz (φ.symm x.1, φ.symm x.2)
      rw [φ.apply_symm_apply, φ.apply_symm_apply, ← map_mul, ← ha] at h
      exact h
    exact Nat.card_unique
  have hZ := GlobalTheory.CocycleCount.card_cocycles_mul_invariants_discrete _ _ M rho hrho
  let E : ↥(ReciprocityTheory.Def.Z1 π ⊤) ≃ ↥(ReciprocityTheory.Gal.Z1 rho) :=
    { toFun := fun c => ⟨fun g => c.1 (φ.symm g), c.2.1.1.continuous.comp hφ.2, fun g h => by
        beta_reduce
        rw [ha, map_mul, cocycle_mul]⟩
      invFun := fun c => ⟨fun g => c.1 (φ g),
        ⟨(IsLocallyConstant.iff_continuous _).2 (c.2.1.comp hφ.1), fun _ => Submodule.mem_top⟩, by
          funext x
          have := c.2.2 (φ x.1) (φ x.2)
          rw [ha', ← map_mul] at this
          change π x.1 (c.1 (φ x.2)) - c.1 (φ (x.1 * x.2)) + c.1 (φ x.1) = 0
          rw [this]
          abel⟩
      left_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.symm_apply_apply g))
      right_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.apply_symm_apply g)) }
  have hM : 0 < Nat.card M := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hM
  rw [← card_Z1_of_invariants_eq_bot π hlc h0, Nat.card_congr E]
  rw [hEu, hH0, hH2] at hZ
  simpa using hZ

theorem card_H1_eq_pow :
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Finite M] (π : Representation O ↥(GK K) M), (∀ m : M, l • m = 0) → (∀ m, IsLocallyConstant fun g => π g m) → π.invariants = ⊥ → Subsingleton (ReciprocityTheory.Def.H2 π ⊤) → Nat.card (ReciprocityTheory.Def.H1 π ⊤) = Nat.card M ^ Module.finrank ℚ_[l] ↥K.1 := by
  intro hE l _ K O M _ _ _ _ π hl hlc h0 h2
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  have hr' : ∀ m : M, l ^ 1 • m = 0 := fun m => by rw [pow_one, hl]
  have _ : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let _ : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule hr'
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ 1)) (Formalism.GaloisCohomology.GK l K.1) M :=
    GlobalTheory.CocycleCount.repOfAction _ (fun g => (π (φ.symm g)).toAddMonoidHom)
      (fun m => by simp) (fun g h m => by simp)
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (hlc m).continuous.comp hφ.2
  exact card_H1_of_euler _ O _ _ φ hφ M rho hrho _ (hE l K.1 hK 1 M rho Nat.one_pos hrho) π
    (fun _ _ => rfl) hlc h0 h2

end GlobalTheory.EulerFree
