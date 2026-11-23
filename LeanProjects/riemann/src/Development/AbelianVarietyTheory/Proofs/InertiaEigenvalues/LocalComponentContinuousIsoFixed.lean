import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalIrreducibleFixedVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEigenFamily
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EigLocalSum

open GlobalTheory.PRep

theorem exists_eigen_family {G V W ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype ι]
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G} (hK : IsCompact (K : Set G))
    {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) (θ : G → ℂ) (hθU : ∀ g ∈ U, g ∈ K → θ g = 1)
    (hmul : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b)
    (T : ι → V →ₗ[ℂ] W) (y : ι → V)
    (hinv : ∀ k ∈ K, ∑ i, T i (ρ k (y i)) = θ k • ∑ i, T i (y i)) :
    ∃ u : ι → V, (∀ j, ∀ h ∈ K, ρ h (u j) = θ h • u j) ∧ ∑ i, T i (u i) = ∑ i, T i (y i) := by
  first
  | exact @_root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family
  | exact _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family
  | (apply _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family ..)

set_option maxHeartbeats 1000000 in

theorem exists_eigen_local_sum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.w.adicCompletion L))) (θ : GL (Fin n) (s.w.adicCompletion L) → ℂ) (U : Set (GL (Fin n) (s.w.adicCompletion L))), K ≤ GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n) → GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n) ≤ K → IsOpen U → (1 : GL (Fin n) (s.w.adicCompletion L)) ∈ U → (∀ g ∈ U, g ∈ K → θ g = 1) → ∀ f ∈ NG.isoTyp a.ρ S, (∀ x : GAf L n, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ K → NG.rt L n x f = θ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) • f) → ∀ (ι : Type) [Fintype ι] (xs : ι → GAf L n) (z : ι → ℂ), (∀ j, TrivOutside {s.v} (xs j)) → ∑ j, z j • NG.rt L n (xs j) f ≠ 0 → ∃ y : σ.V, (∀ h ∈ K, σ.ρ h y = θ h • y) ∧ ∑ j, z j • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs j))) y ≠ 0 := by
  intro L _ _ _ n a S hS s σ hloc c hc hci K θ U hK hKOne hU hU1 hθU f hf hθ ι _ xs z hxs hz
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hz
    simp
  have hrt : ∀ h ∈ K, ∃ x : GAf L n, TrivOutside {s.v} x ∧
      Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h ∧ NG.rt L n x f = θ h • f := by
    intro h hh
    obtain ⟨x, hx, e⟩ := GlobalTheory.EigLocal.exists_trivOutside_map_loc n s c h
    exact ⟨x, hx, e, by rw [hθ x hx (e ▸ hh), e]⟩
  have hmul : ∀ k ∈ K, ∀ k' ∈ K, θ (k * k') = θ k * θ k' := by
    intro k hk k' hk'
    obtain ⟨x, hx, e, hfx⟩ := hrt k hk
    obtain ⟨x', hx', e', hfx'⟩ := hrt k' hk'
    have hxx : TrivOutside {s.v} (x * x') := GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hx'
    have e2 : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (x * x')) = k * k' := by
      rw [map_mul, map_mul, e, e']
    have h2 := hθ (x * x') hxx (e2 ▸ mul_mem hk hk')
    rw [e2] at h2
    have h3 : NG.rt L n (x * x') f = NG.rt L n x (NG.rt L n x' f) := by
      funext g; simp [NG.rt, mul_assoc]
    rw [h3, hfx', map_smul, hfx, smul_smul] at h2
    have h4 : (θ (k * k') - θ k' * θ k) • f = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.1 h4 with h5 | h5
    · rw [sub_eq_zero.1 h5, mul_comm]
    · exact absurd h5 hf0
  have hmem := GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent L n a S hS s σ hloc c hc hci hf
  rw [iSup_subtype'] at hmem
  obtain ⟨F, hF, hFsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hmem
  choose y hy using fun i => LinearMap.mem_range.1 (hF i)
  have hsum : ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)) (y j.1) = f := by
    rw [← hFsum, Finsupp.sum, ← Finset.sum_attach F.support]
    exact Finset.sum_congr rfl fun j _ => hy j.1
  have hKo : IsOpen (K : Set (GL (Fin n) (s.w.adicCompletion L))) :=
    Subgroup.isOpen_mono hKOne GlobalTheory.StepData.isOpen_KOne
  have hKc : IsCompact (K : Set (GL (Fin n) (s.w.adicCompletion L))) :=
    GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (K.isClosed_of_isOpen hKo) hK
  have hint : ∀ (j : F.support) (x : GAf L n), TrivOutside {s.v} x → ∀ v,
      (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
        (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) =
      NG.rt L n x ((j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)) v) := fun j x hx v => j.1.2.2 x hx v
  obtain ⟨u, hu, hus⟩ := exists_eigen_family σ.smooth hKc hU hU1 θ hθU hmul
    (fun j : F.support => (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))) (fun j => y j.1) (by
      intro k hk
      obtain ⟨x, hx, e, hfx⟩ := hrt k hk
      subst e
      rw [Finset.sum_congr rfl fun j _ => hint j x hx (y j.1), ← map_sum, hsum, hfx])
  rw [hsum] at hus
  by_contra hall
  push_neg at hall
  apply hz
  have key : ∀ j, ∑ m, z m • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs m))) (u j) = 0 := by
    intro j
    by_contra hne
    exact hne (hall (u j) (hu j))
  calc ∑ m, z m • NG.rt L n (xs m) f
      = ∑ m, z m • ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
          (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs m))) (u j)) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← hus, map_sum]
        congr 1
        exact Finset.sum_congr rfl fun j _ => (hint j (xs m) (hxs m) (u j)).symm
    _ = ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
          (∑ m, z m • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs m))) (u j)) := by
        simp only [map_sum, map_smul, Finset.smul_sum]
        exact Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun j _ => by rw [key j, map_zero]

end GlobalTheory.EigLocalSum
