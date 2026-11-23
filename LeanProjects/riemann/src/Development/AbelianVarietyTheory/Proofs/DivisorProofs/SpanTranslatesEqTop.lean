import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeLeSmoothVectors

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open Classical

noncomputable section
namespace GlobalTheory.LowSpan

theorem span_translates_eq_top : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S) (v : M.Vec), IsExtVec M v → ∀ τ : D.what₂.Tau, Formalism.MainNotions.S.IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ)) → Submodule.span ℂ {u : lowT M τ | ∃ k ∈ Formalism.REAL.Kset (M.ε τ), ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ)} = ⊤ := by
  intro D V S M v hv τ hK
  obtain ⟨_hfd, hst, hirr, -, -⟩ := hK
  obtain ⟨-, -, hU, -⟩ := M.ds τ
  obtain ⟨S₀, hS₀, hS₀sm⟩ := GlobalTheory.SmoothLowType.exists_lowK_le_sm D V S M τ
  have hle : S₀ ≤ Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ) :=
    le_sSup (s := {T | Formalism.MainNotions.S.IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) T}) hS₀
  have hS₀ne : S₀ ≠ ⊥ := by
    obtain ⟨w, hw, hw0, -⟩ := hS₀.2.2.2.1
    intro h; rw [h] at hw; exact hw0 ((Submodule.mem_bot ℂ).1 hw)
  have hLsm : Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ≤ M.sm τ := by
    rcases hirr S₀ hle hS₀.2.1 with h | h
    · exact absurd h hS₀ne
    · rw [← h]; exact hS₀sm

  set L := Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ) with hLdef
  set v0 : M.H τ := ((v τ : M.sm τ) : M.H τ) with hv0def
  have hv0L : v0 ∈ L := (hv τ).2.1
  have hv00 : v0 ≠ 0 := by
    intro h; have h1 := (hv τ).1; rw [← hv0def, h, norm_zero] at h1; exact zero_ne_one h1
  set T : Set (M.H τ) := {x | ∃ k ∈ Formalism.REAL.Kset (M.ε τ), x = M.σ τ k v0} with hTdef
  have hWL : Submodule.span ℂ T ≤ L := by
    rw [Submodule.span_le]; rintro _ ⟨k, hk, rfl⟩; exact hst k hk _ hv0L
  have hWst : Formalism.MainNotions.S.IsKStableOn (M.ε τ) (M.σ τ) (Submodule.span ℂ T) := by
    intro g hg x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨g * k, Formalism.REAL.Kset_mul _ hg hk, ?_⟩
      rw [hU.1.2 g (kset_uj hg) k (kset_uj hk)]; rfl
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have h1K : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.REAL.Kset (M.ε τ) := by
    have := diag_mem (ε := M.ε τ) (fun _ => (0 : ℝ))
    simpa using this
  have hW0 : Submodule.span ℂ T ≠ ⊥ := by
    intro h
    have : v0 ∈ Submodule.span ℂ T := Submodule.subset_span ⟨1, h1K, by rw [hU.1.1]; rfl⟩
    rw [h] at this; exact hv00 ((Submodule.mem_bot ℂ).1 this)
  have hWeq : Submodule.span ℂ T = L := (hirr _ hWL hWst).resolve_left hW0
  let f : lowT M τ →ₗ[ℂ] M.H τ := (M.sm τ).subtype ∘ₗ (lowT M τ).subtype
  have hf : Function.Injective f := (M.sm τ).injective_subtype.comp (lowT M τ).injective_subtype
  apply Submodule.map_injective_of_injective hf
  rw [Submodule.map_span, Submodule.map_top]
  have himg : f '' {u : lowT M τ | ∃ k ∈ Formalism.REAL.Kset (M.ε τ), ((u : M.sm τ) : M.H τ) = M.σ τ k v0} = T := by
    ext x; constructor
    · rintro ⟨u, ⟨k, hk, hu⟩, rfl⟩; exact ⟨k, hk, hu⟩
    · rintro ⟨k, hk, rfl⟩
      have hxL : M.σ τ k v0 ∈ L := hst k hk _ hv0L
      exact ⟨⟨⟨_, hLsm hxL⟩, hxL⟩, ⟨k, hk, rfl⟩, rfl⟩
  rw [himg, hWeq]
  ext y; constructor
  · intro hy; exact ⟨⟨⟨y, hLsm hy⟩, hy⟩, rfl⟩
  · rintro ⟨x, rfl⟩; exact x.2

end GlobalTheory.LowSpan
