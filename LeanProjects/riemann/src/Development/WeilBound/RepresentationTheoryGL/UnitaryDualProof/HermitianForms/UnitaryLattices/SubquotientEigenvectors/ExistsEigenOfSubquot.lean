import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.DerKer
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.DerFin
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ComapTwKer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfFiniteLengthSubquotients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedPiTensor
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Form.U.Eig

theorem exists_eigen_of_subquot {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (Z : G) (c : ℂ) (hσ : ∀ w, σ Z w = c • w)
    (S : Subrepresentation ρ) (f : S.toRepresentation.IntertwiningMap σ) (s : S.toSubmodule) (hs : f s ≠ 0)
    (F : Submodule ℂ V) (hfin : FiniteDimensional ℂ F) (hF : ∀ x ∈ F, ρ Z x ∈ F) (hsF : (s : V) ∈ F) :
    ∃ x : V, x ≠ 0 ∧ ρ Z x = c • x := by
  let U : Submodule ℂ V := F ⊓ S.toSubmodule
  have : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le inf_le_left
  let E : V →ₗ[ℂ] V := ρ Z - c • LinearMap.id
  have hEU : ∀ x ∈ U, E x ∈ U := by
    intro x hx
    obtain ⟨hxF, hxS⟩ := Submodule.mem_inf.1 hx
    exact Submodule.mem_inf.2 ⟨Submodule.sub_mem _ (hF x hxF) (Submodule.smul_mem _ _ hxF),
      Submodule.sub_mem _ (S.apply_mem_toSubmodule _ hxS) (Submodule.smul_mem _ _ hxS)⟩
  let E' : U →ₗ[ℂ] U := E.restrict hEU
  have hsU : (s : V) ∈ U := Submodule.mem_inf.2 ⟨hsF, s.2⟩
  have hns : ¬ Function.Surjective E' := by
    intro hsur
    obtain ⟨y, hy⟩ := hsur ⟨_, hsU⟩
    have hyS : (y : V) ∈ S.toSubmodule := (Submodule.mem_inf.1 y.2).2
    have hEy : E y = (s : V) := congrArg Subtype.val hy
    have hs' : s = S.toRepresentation Z ⟨y, hyS⟩ - c • ⟨y, hyS⟩ := by
      apply Subtype.ext
      rw [← hEy]
      rfl
    apply hs
    rw [hs', map_sub, map_smul, Representation.IntertwiningMap.isIntertwining, hσ, sub_self]
  have hni : LinearMap.ker E' ≠ ⊥ := fun h =>
    hns (LinearMap.injective_iff_surjective.1 (LinearMap.ker_eq_bot.1 h))
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hni
  refine ⟨(x : V), fun h => hx0 (Subtype.ext h), ?_⟩
  have hEx : ρ Z x - c • (x : V) = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hx)
  exact sub_eq_zero.1 hEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isAdmissible_derivB (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n i : ℕ) (π : GRep k (n + i))
    (hs : IsSmooth π.ρ) (hi : π.ρ.IsIrreducible) : IsAdmissible (derivB ψ i π).ρ := by
  cases i with
  | zero => exact PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k n _ π.ρ hs hi
  | succ j =>
    have hD : IsSmooth (GlobalTheory.BZMir.deriv k ψ j π.ρ) := GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ j hs
    exact GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength _ hD
      (PositivityTheory.RgGu.NR.derFin_of k (PositivityTheory.RgGu.NR.derEquiv k) ψ hc h1 n j _ π.ρ hs hi)
      fun Y _ _ τ hq hirr => PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k n Y τ (hq.isSmooth hD) hirr

variable (k) in

theorem uAdm : UAdm k := fun ψ hc h1 n i π hs hi => isAdmissible_derivB ψ hc h1 n i π hs hi

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem scalar_comm (n : ℕ) (z : kˣ) (g : GL (Fin n) k) :
    g * GeneralLinearGroup.scalar (Fin n) z = GeneralLinearGroup.scalar (Fin n) z * g := by
  ext : 1
  simp only [Units.val_mul]
  exact (Algebra.commutes _ _).symm

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (x : V) : x ∈ fixed ρ K ↔ ∀ h : K, ρ h x = x := by
  show (∀ h : K, ρ h x = ((1 : K →* ℂˣ) h : ℂ) • x) ↔ _
  simp

variable (k) in

theorem uEig : UEig k := by
  intro ψ hc h1 n i π hs hi t W _ _ σ ω hW hsub hω z
  have hadm := uAdm k ψ hc h1 n i π hs hi
  obtain ⟨S, f, hf⟩ := hsub
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨s, rfl⟩ := hf w
  obtain ⟨K, hKo, hKc, hKsub⟩ := GlobalTheory.ContraProd.exists_compactOpen_GL (k := k) (Fin n)
    {g | (derivB ψ i π).ρ g s.1 = s.1}
    ((hadm.1 s.1).mem_nhds (by show (derivB ψ i π).ρ 1 s.1 = s.1; rw [map_one]; rfl))
  have hfixZ : ∀ x ∈ fixed (derivB ψ i π).ρ K, (derivB ψ i π).ρ (GeneralLinearGroup.scalar (Fin n) z) x ∈ fixed (derivB ψ i π).ρ K := by
    intro x hx
    rw [mem_fixed_iff] at hx ⊢
    intro h
    rw [← Module.End.mul_apply, ← map_mul, scalar_comm, map_mul, Module.End.mul_apply, hx h]
  have hF : ∀ x ∈ fixed (derivB ψ i π).ρ K,
      ((derivB ψ i π).tw t).ρ (GeneralLinearGroup.scalar (Fin n) z) x ∈ fixed (derivB ψ i π).ρ K := by
    intro x hx
    show ((dpow n t (GeneralLinearGroup.scalar (Fin n) z) : ℂˣ) : ℂ) • (derivB ψ i π).ρ (GeneralLinearGroup.scalar (Fin n) z) x ∈ fixed (derivB ψ i π).ρ K
    exact Submodule.smul_mem _ _ (hfixZ x hx)
  exact exists_eigen_of_subquot ((derivB ψ i π).tw t).ρ σ (GeneralLinearGroup.scalar (Fin n) z) (ω z : ℂ) (hω z) S f s hw
    (fixed (derivB ψ i π).ρ K) (hadm.2 K hKo hKc) hF ((mem_fixed_iff _ _ _).2 fun h => hKsub h.2)

end PositivityTheory.RgUd.Form.U.Eig
