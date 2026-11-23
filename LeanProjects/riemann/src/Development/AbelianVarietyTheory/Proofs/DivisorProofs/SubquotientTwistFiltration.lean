import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SmGL

theorem exists_step_subquotient_ne_zero_of_filtration : ∀ {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (χ : G →* ℂˣ) (φ : H →* G) (n : ℕ) (S : Fin (n + 1) → Subrepresentation ρ), Monotone S → S 0 = ⊥ →
    S (Fin.last n) = ⊤ → ∀ {W' Vy : Type} [AddCommGroup W'] [Module ℂ W'] [AddCommGroup Vy] [Module ℂ Vy]
    (Q : Representation ℂ H W') (Y : Representation ℂ H Vy),
    GlobalTheory.SmGL.IsSubquotient Q ((GlobalTheory.SmGL.twist ρ χ).comp φ) → ∀ F : Q.IntertwiningMap Y, F ≠ 0 →
    ∃ (t : Fin n) (V' : Type) (_ : AddCommGroup V') (_ : Module ℂ V') (Q' : Representation ℂ H V'),
      GlobalTheory.SmGL.IsSubquotient Q' ((GlobalTheory.SmGL.twist (GlobalTheory.SmGL.subQuot (S t.succ) (S t.castSucc)) χ).comp φ) ∧
      ∃ F' : Q'.IntertwiningMap Y, F' ≠ 0 := by
  intro G H V _ _ _ _ ρ χ φ n S hS h0 htop W' Vy _ _ _ _ Q Y hQ F hF
  classical
  obtain ⟨T, f, hf⟩ := hQ
  let g : T.toSubmodule →ₗ[ℂ] Vy := F.toLinearMap ∘ₗ f.toLinearMap
  have hg : ∃ x, g x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hF
    apply Representation.IntertwiningMap.ext
    ext w
    obtain ⟨x, rfl⟩ := hf w
    exact h x
  let P : ℕ → Prop := fun k => ∃ hk : k < n + 1, ∃ x : T.toSubmodule,
    (x : V) ∈ (S ⟨k, hk⟩).toSubmodule ∧ g x ≠ 0
  have hex : ∃ k, P k := by
    obtain ⟨x, hx⟩ := hg
    refine ⟨n, Nat.lt_succ_self n, x, ?_, hx⟩
    have : S ⟨n, Nat.lt_succ_self n⟩ = ⊤ := htop
    rw [this]
    trivial
  have hmin : ∀ k < Nat.find hex, ¬ P k := fun k hk => Nat.find_min hex hk
  obtain ⟨hun, x0, hx0S, hx0⟩ := Nat.find_spec hex
  have hu0 : Nat.find hex ≠ 0 := by
    intro h
    have hS0 : S ⟨Nat.find hex, hun⟩ = ⊥ := by
      rw [← h0]; congr 1; exact Fin.ext h
    rw [hS0] at hx0S
    have hx : x0 = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 hx0S)
    exact hx0 (by rw [hx, map_zero])
  obtain ⟨t0, ht0⟩ := Nat.exists_eq_succ_of_ne_zero hu0
  let t : Fin n := ⟨t0, by omega⟩
  have hts : t.succ = ⟨Nat.find hex, hun⟩ := Fin.ext (by simp [t, ht0])
  have hvan : ∀ x : T.toSubmodule, (x : V) ∈ (S t.castSucc).toSubmodule → g x = 0 := by
    intro x hx
    by_contra hne
    exact hmin t0 (by omega) ⟨by omega, x, hx, hne⟩
  let M := (S t.succ).toSubmodule
  let N : Submodule ℂ M := (S t.castSucc).toSubmodule.comap M.subtype
  let B : Submodule ℂ M := T.toSubmodule.comap M.subtype
  let Rm : Representation ℂ H M := (twist (S t.succ).toRepresentation χ).comp φ
  let Bs : Subrepresentation Rm := ⟨B, fun h v hv => T.apply_mem_toSubmodule h hv⟩
  let NB : Submodule ℂ B := N.comap B.subtype
  have hNB : ∀ h : H, NB ≤ NB.comap (Bs.toRepresentation h) := by
    intro h x hx
    exact Submodule.smul_mem _ _ ((S t.castSucc).apply_mem_toSubmodule (φ h) hx)
  let Q' : Representation ℂ H (B ⧸ NB) := Bs.toRepresentation.quotient NB hNB
  refine ⟨t, B ⧸ NB, inferInstance, inferInstance, Q', ?_, ?_⟩
  · let ι : Q'.IntertwiningMap ((twist (subQuot (S t.succ) (S t.castSucc)) χ).comp φ) :=
      ⟨NB.mapQ N B.subtype le_rfl, fun h => by
        ext b
        rfl⟩
    refine IsSubquotient.of_injective ι ?_
    intro a b hab
    induction a using Submodule.Quotient.induction_on with | _ a => ?_
    induction b using Submodule.Quotient.induction_on with | _ b => ?_
    change NB.mapQ N B.subtype le_rfl (Submodule.Quotient.mk a)
      = NB.mapQ N B.subtype le_rfl (Submodule.Quotient.mk b) at hab
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hab
    rw [Submodule.Quotient.eq]
    simpa [NB] using hab
  · let j : B →ₗ[ℂ] T.toSubmodule :=
      LinearMap.codRestrict T.toSubmodule (M.subtype ∘ₗ B.subtype) (fun b => b.2)
    let ψ : B →ₗ[ℂ] Vy := g ∘ₗ j
    have hψ : NB ≤ LinearMap.ker ψ := by
      intro x hx
      exact hvan (j x) hx
    let F' : Q'.IntertwiningMap Y := ⟨NB.liftQ ψ hψ, fun h => by
      ext b
      change F (f (T.toRepresentation h (j b))) = Y h (F (f (j b)))
      rw [f.isIntertwining, F.isIntertwining]⟩
    refine ⟨F', fun hF0 => ?_⟩
    have hx0S' : (x0 : V) ∈ M := by
      change (x0 : V) ∈ (S t.succ).toSubmodule
      rw [hts]; exact hx0S
    let b0 : B := ⟨⟨x0, hx0S'⟩, x0.2⟩
    have h1 : F' (Submodule.Quotient.mk b0) = 0 := by rw [hF0]; rfl
    apply hx0
    exact h1

end GlobalTheory.SmGL
