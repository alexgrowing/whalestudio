import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.ConjOn
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Coset

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem twistOf_schur {k H : Type} [Field k] [IsAlgClosed k] [Group H] {n : ℕ} (R : H →* GL (Fin n) k)
    (hR : IsIrr R) (A : Matrix (Fin n) (Fin n) k)
    (hA : ∀ h, A * (R h : Matrix (Fin n) (Fin n) k) = (R h : Matrix (Fin n) (Fin n) k) * A) :
    ∃ c : k, A = c • (1 : Matrix (Fin n) (Fin n) k) := by
  obtain ⟨h0, -, h2⟩ := hR
  haveI : Nontrivial (Fin n → k) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact h0 (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A)
  refine ⟨c, ?_⟩
  have hinv : IsInv R (Module.End.eigenspace (Matrix.toLin' A) c) := by
    intro g v hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  rcases h2 _ le_top hinv with h | h
  · exact absurd h hc
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have hv : v ∈ Module.End.eigenspace (Matrix.toLin' A) c := by rw [h]; trivial
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv]
    simp

private theorem twistOf_ratio {k Γ : Type} [Field k] [IsAlgClosed k] [Group Γ] {n : ℕ} (R S : Γ →* GL (Fin n) k)
    (H : Subgroup Γ) (hN : H.Normal) (hR : IsIrr (R.comp H.subtype)) (hS : ∀ h ∈ H, S h = R h) :
    ∃ ξ : Γ →* kˣ, H ≤ ξ.ker ∧ ∀ g, S g = tw R ξ g := by
  have hn : Nonempty (Fin n) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    exact hR.1 (Subsingleton.elim _ _)
  have inj : ∀ (X : GL (Fin n) k) (a b : k),
      a • (X : Matrix (Fin n) (Fin n) k) = b • (X : Matrix (Fin n) (Fin n) k) → a = b := by
    intro X a b hab
    exact smul_left_injective k X.ne_zero hab
  have key : ∀ g, ∃ u : kˣ, (S g : Matrix (Fin n) (Fin n) k) = (u : k) • (R g : Matrix (Fin n) (Fin n) k) := by
    intro g
    obtain ⟨c, hc⟩ := twistOf_schur (R.comp H.subtype) hR ((R g)⁻¹ * S g : GL (Fin n) k) (by
      intro h
      have e : (R g)⁻¹ * S g * R h = R h * ((R g)⁻¹ * S g) := by
        have e1 := hS _ (hN.conj_mem h h.2 g)
        have e2 := hS _ h.2
        simp only [map_mul, map_inv, e2] at e1
        calc (R g)⁻¹ * S g * R h = (R g)⁻¹ * (S g * R h * (S g)⁻¹) * S g := by group
          _ = _ := by rw [e1]; group
      exact congrArg Units.val e)
    have h1 : (S g : Matrix (Fin n) (Fin n) k) = c • (R g : Matrix (Fin n) (Fin n) k) := by
      have : S g = R g * ((R g)⁻¹ * S g) := by group
      rw [this, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one]
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at h1
      exact (S g).ne_zero h1
    exact ⟨Units.mk0 c hc0, h1⟩
  choose u hu using key
  have hmul : ∀ a b, u (a * b) = u a * u b := by
    intro a b
    apply Units.ext
    apply inj (R (a * b))
    rw [← hu, map_mul, map_mul, Units.val_mul, Units.val_mul, Units.val_mul, hu, hu, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
  refine ⟨MonoidHom.mk' u hmul, ?_, ?_⟩
  · intro h hh
    rw [MonoidHom.mem_ker]
    apply Units.ext
    apply inj (R h)
    have := hu h
    rw [hS h hh] at this
    simpa using this.symm
  · intro g
    apply Units.ext
    rw [tw_val, hu]
    rfl

theorem UpperTheory.V.Z.Sym.Ga.twistOf :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (n : ℕ) (R R' : Γ →* GL (Fin n) (Qbar l)), IrrOpen R → ∀ V : Set Γ, IsOpen V → V.Nonempty → (∀ g ∈ V, Ga.tr (R' g) = Ga.tr (R g)) → ∃ ξ : Γ →* (Qbar l)ˣ, IsOpen (ξ.ker : Set Γ) ∧ RepIso (tw R ξ) R' := by
  intro l _ Γ _ _ _ _ _ n R R' hR V hV hne htr
  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨H, hN, hO, hH⟩ := Ga.coset Γ V hV g₀ hg₀
  obtain ⟨P, hP⟩ := Ga.conjOn (Qbar l) H n (R.comp H.subtype) (R'.comp H.subtype) (hR H hO) (R g₀) (R' g₀) (by
    intro h
    have := htr _ (hH h h.2)
    rw [map_mul, map_mul] at this
    exact this.symm)
  obtain ⟨ξ, h1, h2⟩ := twistOf_ratio R ((MulAut.conj P⁻¹).toMonoidHom.comp R') H hN (hR H hO) (by
    intro h hh
    have : R' h = P * R h * P⁻¹ := hP ⟨h, hh⟩
    change P⁻¹ * R' h * P⁻¹⁻¹ = R h
    rw [this]; group)
  refine ⟨ξ, Subgroup.isOpen_mono h1 hO, P, fun s => ?_⟩
  rw [← h2]
  change R' s = P * (P⁻¹ * R' s * P⁻¹⁻¹) * P⁻¹
  group
