import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoI

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 8000000

open RhoH in
theorem lIrho : LIrho := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  classical
  obtain ⟨𝓕, hμ⟩ := hC.hμ
  have hΨ0m : psi0 θ V n l s τ ∈ awayA θ V n l s τ := unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V l s τ
  have hl0 : ∀ τ, l τ ≠ 0 := l_ne_zero D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl
  have hmem : ∀ P : PX V.rank n, tens θ τ fr (fP (cLoc l τ) P) (psi0 θ V n l s τ) ∈ schwartzA θ V.rank n ∧
      tens θ τ fr (fP (cLoc l τ) P) (psi0 θ V n l s τ) ∈ fockA θ V n l s :=
    fun P => hT D n V θ l s τ ε fr hC.hθ hl0 hC.hs hC.hfr _ hΨ0m P
  have hfP0 : fP (cLoc l τ) (0 : PX V.rank n) = 0 := by
    funext u
    simp [fP, evX]
  have htens0 : tens θ τ fr (0 : (Fin V.rank → Fin n → ℂ) → ℂ) (psi0 θ V n l s τ) = 0 := by
    funext x
    show (0 : ℂ) * _ = 0
    exact zero_mul _
  have hphi0 : phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) 0 = 0 := by
    apply Subtype.ext
    rw [phiS_val (hmem 0).1, hfP0, htens0]
    rfl
  have hlin : ∀ (a : ℂ) (P Q : PX V.rank n), phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) (a • P + Q) =
      a • phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) P + phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) Q := by
    intro a P Q
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_smul, phiS_val (hmem _).1, phiS_val (hmem _).1, phiS_val (hmem _).1,
      fP_add_smul, tens_add_smul]
  let jL : PX V.rank n →ₗ[ℂ] schwartzA θ V.rank n :=
    { toFun := phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ)
      map_add' := fun P Q => by simpa using hlin 1 P Q
      map_smul' := fun a P => by
        have := hlin a P 0
        rw [add_zero, hphi0, add_zero] at this
        exact this }
  have hjinj : Function.Injective jL := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro R hR
    have h1 : (jL R).1 = 0 := by rw [hR]; rfl
    change (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) R).1 = 0 at h1
    rw [phiS_val (hmem R).1, ← htens0, ← hfP0] at h1
    exact fP_inj _ (tensor_gaussian_vacuum_injective hC.hθ hC.hfr l h1)
  have hexist : ∀ k : GR n, InK (mR k) → ∀ P, ∃ Q, L k (fP (cLoc l τ) P) = fP (cLoc l τ) Q := by
    intro k hk P
    have hΦ : (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) P).1 ∈ fockA θ V n l s := by
      rw [phiS_val (hmem P).1]
      exact (hmem P).2
    have hst := fock_stable D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl s hC.hs _ hΦ (ι k)
      (iota_mem_K hC.hθ hC.hι k hk)
    rw [hL k _ hΨ0m P] at hst
    exact tens_slice hC.hθ hC.hfr l _ hst
  have hLlin : ∀ k : GR n, InK (mR k) → ∀ (a : ℂ) (P Q : PX V.rank n),
      L k (fP (cLoc l τ) (a • P + Q)) = a • L k (fP (cLoc l τ) P) + L k (fP (cLoc l τ) Q) := by
    intro k hk a P Q
    apply tensor_gaussian_vacuum_injective hC.hθ hC.hfr l
    rw [tens_add_smul, ← hL k _ hΨ0m, ← hL k _ hΨ0m, ← hL k _ hΨ0m, hlin, map_add, map_smul]
    rfl
  let ρ0 : GR n → PX V.rank n → PX V.rank n := fun k P => if hk : InK (mR k) then (hexist k hk P).choose else P
  have hρ0 : ∀ (k : GR n) (hk : InK (mR k)) P, L k (fP (cLoc l τ) P) = fP (cLoc l τ) (ρ0 k P) := by
    intro k hk P
    simp only [ρ0, dif_pos hk]
    exact (hexist k hk P).choose_spec
  have hρlin : ∀ (k : GR n) (a : ℂ) (P Q : PX V.rank n), ρ0 k (a • P + Q) = a • ρ0 k P + ρ0 k Q := by
    intro k a P Q
    by_cases hk : InK (mR k)
    · apply fP_inj (cLoc l τ)
      rw [fP_add_smul, ← hρ0 k hk, ← hρ0 k hk, ← hρ0 k hk, hLlin k hk]
    · simp only [ρ0, dif_neg hk]
  have hρ00 : ∀ k : GR n, ρ0 k 0 = 0 := by
    intro k
    have := hρlin k 1 0 0
    simp only [one_smul, add_zero] at this
    have h2 : ρ0 k 0 + ρ0 k 0 = ρ0 k 0 + 0 := by rw [← this, add_zero]
    exact add_left_cancel h2
  let ρ : GR n → PX V.rank n →ₗ[ℂ] PX V.rank n := fun k =>
    { toFun := ρ0 k
      map_add' := fun P Q => by simpa using hρlin k 1 P Q
      map_smul' := fun a P => by
        have := hρlin k a P 0
        rw [add_zero, hρ00, add_zero] at this
        exact this }
  have hρ : ∀ (k : GR n) P, InK (mR k) → L k (fP (cLoc l τ) P) = fP (cLoc l τ) (ρ k P) :=
    fun k P hk => hρ0 k hk P
  have hjρ : ∀ (k : GR n), InK (mR k) → ∀ Q, jL (ρ k Q) = ω (ι k) (jL Q) := by
    intro k hk Q
    apply Subtype.ext
    show (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) (ρ0 k Q)).1 =
      (ω (ι k) (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) Q)).1
    rw [hL k _ hΨ0m Q, phiS_val (hmem _).1, ← hρ0 k hk Q]
  refine ⟨ρ, hρ, fun P => ?_⟩
  have hjmem : ∀ R, (jL R).1 ∈ fockA θ V n l s := by
    intro R
    show (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) R).1 ∈ fockA θ V n l s
    rw [phiS_val (hmem R).1]
    exact (hmem R).2
  have hfd := GlobalTheory.T.fockVector_schrodingerModel_isKFinite D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl s hC.hs (jL P) (hjmem P)
  set S := Submodule.span ℂ {Ψ' : schwartzA θ V.rank n | ∃ k ∈ K D n, Ψ' = ω k (jL P)} with hS
  have hSstab : ∀ κ ∈ K D n, ∀ x ∈ S, ω κ x ∈ S := by
    intro κ hκ x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k', hk', rfl⟩ := hx
      refine Submodule.subset_span ⟨κ * k', (K D n).mul_mem hκ hk', ?_⟩
      rw [map_mul, Module.End.mul_apply]
    | zero => rw [map_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact S.smul_mem a hx
  let W : Submodule ℂ (PX V.rank n) := S.comap jL
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · have : FiniteDimensional ℂ S := hfd
    exact Module.Finite.of_injective (jL.restrict (p := W) (q := S) fun x hx => hx)
      (fun x y h => Subtype.ext (hjinj (congrArg Subtype.val h)))
  · show jL P ∈ S
    exact Submodule.subset_span ⟨1, (K D n).one_mem, by rw [map_one]; rfl⟩
  · intro k hk Q hQ
    show jL (ρ k Q) ∈ S
    rw [hjρ k hk Q]
    exact hSstab _ (iota_mem_K hC.hθ hC.hι k hk) _ hQ
  · intro Q _ l'
    let e := LinearEquiv.ofInjective jL hjinj
    obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend (l' ∘ₗ e.symm.toLinearMap)
    have hΛj : ∀ R, Λ (jL R) = l' R := by
      intro R
      have := congrArg (fun F => F ⟨jL R, LinearMap.mem_range_self jL R⟩) hΛ
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe] at this
      rw [this]
      exact congrArg l' (e.symm_apply_eq.2 (Subtype.ext (LinearEquiv.ofInjective_apply jL (h := hjinj) R).symm))
    have hcont := orbit_cont D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl s hC.hs (jL Q) (hjmem Q) Λ
    have hιc : ContinuousOn (fun k : GR n => ι k) {k | InK (mR k)} := hC.hι.1.continuousOn
    have hmaps : Set.MapsTo (fun k : GR n => ι k) {k | InK (mR k)} (K D n : Set (G D n)) :=
      fun k hk => iota_mem_K hC.hθ hC.hι k hk
    refine (hcont.comp hιc hmaps).congr ?_
    intro k hk
    simp only [Function.comp_apply]
    rw [← hΛj, hjρ k hk Q]

end PositivityTheory.Rg.Sw.Glob
