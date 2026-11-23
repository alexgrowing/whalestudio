import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicOpenSectionScaled
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc

namespace GlobalTheory.ChainDesc

theorem exists_pow_smul_mem_of_mem_span_image {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : Function.Injective φ) (a : A) (ha : ∀ x : B, ∃ (n : ℕ) (r : A), φ r = φ a ^ n * x) {ι : Type}
    (N : Submodule A (ι → A)) (v : ι → A)
    (hv : piMap φ ι v ∈ Submodule.span B (piMap φ ι '' (N : Set (ι → A)))) : ∃ n : ℕ, a ^ n • v ∈ N := by
  have key : ∀ w ∈ Submodule.span B (piMap φ ι '' (N : Set (ι → A))),
      ∃ (n : ℕ) (u : ι → A), u ∈ N ∧ ∀ i, φ (u i) = φ a ^ n * w i := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      exact ⟨0, u, hu, fun i => by simp⟩
    | zero => exact ⟨0, 0, N.zero_mem, fun i => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, u, hu, e⟩ := hx
      obtain ⟨m, u', hu', e'⟩ := hy
      refine ⟨n + m, a ^ m • u + a ^ n • u', N.add_mem (N.smul_mem _ hu) (N.smul_mem _ hu'), fun i => ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, map_pow, e, e']
      ring
    | smul c x _ hx =>
      obtain ⟨n, u, hu, e⟩ := hx
      obtain ⟨m, r, hr⟩ := ha c
      refine ⟨n + m, r • u, N.smul_mem _ hu, fun i => ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, e, hr]
      ring
  obtain ⟨n, u, hu, e⟩ := key _ hv
  refine ⟨n, ?_⟩
  have : a ^ n • v = u := funext fun i => hφ (by
    rw [e i]; simp)
  rwa [this]

theorem mem_of_locally_mem_span : ∀ (X : Scheme.{0}) [IsIntegral X] (U : AffOp X) (h : ℕ) (N : Submodule U.Bp (Fin h → U.Bp)) (v : Fin h → U.Bp), (∀ z ∈ U.1, ∃ (U' : AffOp X) (hle : U'.1 ≤ U.1), z ∈ U'.1 ∧ piMap (AffOp.res hle) (Fin h) v ∈ Submodule.span U'.Bp (piMap (AffOp.res hle) (Fin h) '' (N : Set (Fin h → U.Bp)))) → v ∈ N := by
  intro X _ U h N v hv
  let S : Set Γ(X, U.1) := {a | ∃ n : ℕ, (algebraMap Γ(X, U.1) U.Bp a) ^ n • v ∈ N}
  have hS : Ideal.span S = ⊤ := by
    rw [← U.2.1.self_le_iSup_basicOpen_iff]
    intro z hz
    obtain ⟨U', hle, hzU', hmem⟩ := hv z hz
    obtain ⟨a, haU', hza⟩ := U.2.1.exists_basicOpen_le ⟨z, hzU'⟩ hz
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ?_⟩, hza⟩
    let V : AffOp X := ⟨X.basicOpen a, U.2.1.basicOpen a, ⟨⟨z, hza⟩⟩⟩
    refine exists_pow_smul_mem_of_mem_span_image (AffOp.res hle) (fun x y e => Subtype.ext ?_) _ (fun x => ?_) N v hmem
    · exact congrArg (fun t : U'.Bp => (t : GlobalTheory.GroupBplus.Kbar X)) e
    · obtain ⟨n, r, hr⟩ := GlobalTheory.BplusDescent.exists_pow_mul_mem_of_eq_basicOpen X U V a rfl
        (AffOp.res (U := U') (U' := V) haU' x)
      exact ⟨n, r, Subtype.ext hr⟩
  have hS' : Ideal.span (algebraMap Γ(X, U.1) U.Bp '' S) = ⊤ := by
    rw [← Ideal.map_span, hS, Ideal.map_top]
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem N _ hS' v ?_
  rintro ⟨_, a, ha, rfl⟩
  exact ha

end GlobalTheory.ChainDesc
