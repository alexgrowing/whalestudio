import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviPartsCommuteStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviEqISupPartsStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicHaarFiniteInfiniteProductStatement
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.FiniteSlicesUPart
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.FiniteSlicesGlPart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Rg

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem finiteDimensional_of_parts {G : Type} [Group G] {ι : Type} [Fintype ι] [DecidableEq ι] (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y) (L : Subgroup G) (hgen : L = ⨆ i, H i)
    (𝓒 : Set (G → ℂ)) (B : Finset G)
    (hB : ∀ φ ∈ Submodule.span ℂ 𝓒, (∀ b ∈ B, ∀ g ∈ L, φ (g * b) = 0) → φ = 0)
    (hcore : ∀ i b, FiniteDimensional ℂ (Submodule.span ℂ (sliceSet 𝓒 (H i) L b))) :
    FiniteDimensional ℂ (Submodule.span ℂ 𝓒) := by
  let P : (∀ i, H i) →* G := Subgroup.noncommPiCoprod hcomm
  have hrange : P.range = L := by rw [Subgroup.noncommPiCoprod_range, hgen]
  have hP : ∀ i (t : H i), P (Pi.mulSingle i t) = t := fun i t => Subgroup.noncommPiCoprod_mulSingle i t

  let R : G → (G → ℂ) →ₗ[ℂ] ((∀ i, H i) → ℂ) := fun b => LinearMap.funLeft ℂ ℂ fun x => P x * b
  have hfin : ∀ b, FiniteDimensional ℂ (Submodule.span ℂ (R b '' 𝓒)) := fun b => by
    haveI := fun i => hcore i b
    refine finiteDimensional_of_slices (fun i => Submodule.span ℂ (sliceSet 𝓒 (H i) L b)) _ ?_
    rintro _ ⟨φ, hφ, rfl⟩ i x
    have e : ∀ t : H i, Function.update x i t = Pi.mulSingle i t * Function.update x i 1 := fun t => by
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    have e' : ∀ t : H i, Function.update x i t = Function.update x i 1 * Pi.mulSingle i t := fun t => by
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    refine Submodule.subset_span ⟨φ, hφ, P (Function.update x i 1), hrange ▸ ⟨_, rfl⟩, fun t ht => ?_, ?_⟩
    · have h1 := congrArg P ((e ⟨t, ht⟩).symm.trans (e' ⟨t, ht⟩))
      rwa [map_mul, map_mul, hP] at h1
    · funext t
      change φ (P (Function.update x i t) * b) = φ ((t : G) * P (Function.update x i 1) * b)
      rw [e t, map_mul, hP]
  have hmap : ∀ b, ∀ φ ∈ Submodule.span ℂ 𝓒, R b φ ∈ Submodule.span ℂ (R b '' 𝓒) := fun b φ hφ => by
    rw [← Submodule.map_span]
    exact Submodule.mem_map_of_mem hφ
  let Ψ : Submodule.span ℂ 𝓒 →ₗ[ℂ] (∀ b : B, Submodule.span ℂ (R b.1 '' 𝓒)) :=
    LinearMap.pi fun b => ((R b.1).comp (Submodule.span ℂ 𝓒).subtype).codRestrict _ fun φ => hmap b.1 φ.1 φ.2
  haveI := fun b : B => hfin b.1
  refine FiniteDimensional.of_injective Ψ ((injective_iff_map_eq_zero Ψ).2 fun φ hφ => ?_)
  refine Subtype.ext (hB φ.1 φ.2 fun b hb g hg => ?_)
  obtain ⟨x, rfl⟩ : g ∈ P.range := hrange ▸ hg
  exact congrFun (congrArg Subtype.val (congrFun hφ ⟨b, hb⟩)) x

theorem finite_cuspOn : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) → ∀ (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), T.Nonempty → FiniteDimensional ℂ (Submodule.span ℂ {φ | φ ∈ formsOn θ V X Y T U ε fr ρ c ∧ ∀ T' : Finset (Fin m), T ⊂ T' → IsConstAlong D.sp.cm.sig V.gram X T' φ 0}) := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c m X Y hW T hT
  classical
  have hh := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  obtain ⟨B, hB⟩ := GlobalTheory.T.archimedean_frame_K_type_decomposition D θ hθ V U hU ε fr hfr W ρ hρ c m X Y hW T hT
  refine finiteDimensional_of_parts (part D.sp.cm.sig V.gram X Y T)
    (GlobalTheory.T.levi_parts_commute D.host.F D.host.E D.sp.cm.sig hh.1 V.rank V.gram (hh.2 V) m X Y hW T) (levi D.sp.cm.sig V.gram X Y T)
    (GlobalTheory.T.levi_eq_iSup_parts D.host.F D.host.E D.sp.cm.sig hh.1 V.rank V.gram (hh.2 V) m X Y hW T) (cuspOn θ V X Y T U ε fr ρ c) B
    (fun φ hφ h => hB φ (mem_formsOn_of_mem_span hθ (Submodule.span_mono (fun f hf => hf.1) hφ)) h) ?_
  rintro (_ | k) b
  · exact UCore.Rg.finite_slices_uPart D θ hθ V U hU ε fr hfr W ρ hρ c m X Y hW T hT b
  · exact CoreGL.Rg.finite_slices_glPart D θ hθ V U hU ε fr hfr W ρ hρ c m X Y hW T hT k.1 k.2 b

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Rg
