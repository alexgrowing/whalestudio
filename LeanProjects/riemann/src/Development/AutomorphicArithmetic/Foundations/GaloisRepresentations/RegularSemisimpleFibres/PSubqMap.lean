import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContractNeZero
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PIndDetK

namespace UpperTheory.Gal.InertialTypesAlt.SubquotientMaps

section SlopeTestRemainingChoices

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori
open GlobalTheory.Parabolic (mem_fixed)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N s : ℕ} {d : Fin s → ℕ} {hd : ∑ a, d a = N} {W V Z : Type} [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]
  {ρ : Representation ℂ (Levi k fun a => Fin (d a)) W}

private theorem isSmooth_sub (S : Subrepresentation (parInd (stdBlocks d hd) ρ)) :
    IsSmooth S.toRepresentation := fun y => by
  have : {g : GL (Fin N) k | S.toRepresentation g y = y} =
      {g : GL (Fin N) k | parInd (stdBlocks d hd) ρ g y.1 = y.1} := by
    ext g; exact Subtype.ext_iff
  rw [this]; exact isSmooth_parInd _ _ y.1

private theorem levelZeroMap_surjective {S : Subrepresentation (parInd (stdBlocks d hd) ρ)}
    {π : Representation ℂ (GL (Fin N) k) V} (f : S.toRepresentation.IntertwiningMap π)
    (hf : Function.Surjective f) : Function.Surjective (levelZeroMap f) := by
  intro v
  obtain ⟨u0, hu0⟩ := hf v.1
  obtain ⟨u, hu, e⟩ := IwahoriOnto.exists_fixed_map_eq (isSmooth_sub S) DepthZero.isCompact_KOne₁
    f.toLinearMap u0 fun h hh => by
      show f (S.toRepresentation h u0) = f u0
      rw [f.isIntertwining, hu0]
      exact mem_fixed.1 v.2 h hh
  exact ⟨⟨u, hu⟩, Subtype.ext (e.trans hu0)⟩

private def evalOne (S : Subrepresentation (parInd (stdBlocks d hd) ρ)) :
    fixed S.toRepresentation (KOne k (Fin N)) →ₗ[ℂ] W where
  toFun u := (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem evalOne_redK (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (κ : KO k (Fin N)) (u : fixed S.toRepresentation (KOne k (Fin N))) :
    evalOne S (levelZero S.toRepresentation (redK k (Fin N) κ) u) =
      (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 κ := by
  show ((levelZero S.toRepresentation (redK k (Fin N) κ) u).1.1 : IndSp (stdBlocks d hd) ρ).1.1 1 = _
  rw [levelZero_apply]
  show ((parInd (stdBlocks d hd) ρ (κ : GL (Fin N) k) u.1.1 : IndSp (stdBlocks d hd) ρ)).1.1 1 = _
  rw [parInd_apply, one_mul]

private theorem val_mul_of_mem (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (u : fixed S.toRepresentation (KOne k (Fin N))) (x : GL (Fin N) k) {c : GL (Fin N) k}
    (hc : c ∈ KOne k (Fin N)) :
    (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 (x * c) = (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 x := by
  have h : S.toRepresentation c u.1 = u.1 := mem_fixed.1 u.2 c hc
  have h2 : parInd (stdBlocks d hd) ρ c u.1.1 = u.1.1 := congrArg Subtype.val h
  exact congrArg (fun F : IndSp (stdBlocks d hd) ρ => F.1.1 x) h2

private theorem leviKOne_le_leviK {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {s : ℕ} {d : Fin s → ℕ} :
    leviKOne k (fun a => Fin (d a)) ≤ leviK k (fun a => Fin (d a)) := by
  intro l hl
  unfold leviKOne at hl
  unfold leviK
  rw [Subgroup.mem_pi] at hl ⊢
  exact fun a ha => GlobalTheory.StepData.KOne_le_KO (hl a ha)

private theorem evalOne_mem_fixed (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (u : fixed S.toRepresentation (KOne k (Fin N))) :
    evalOne S u ∈ fixed ρ (leviKOne k fun a => Fin (d a)) := by
  rw [mem_fixed]
  intro l hl
  have hpar := leviEmb_mem_parab k (stdBlocks d hd) l
  have hlaw := parInd_law (stdBlocks d hd) ρ (u.1.1 : IndSp (stdBlocks d hd) ρ) ⟨_, hpar⟩ 1
  have hK : leviEmb k (stdBlocks d hd) l ∈ KOne k (Fin N) := jLevi_le_KOne _ ⟨l, hl, rfl⟩
  have h4 := val_mul_of_mem S u 1 hK
  rw [one_mul] at h4
  simp only [mul_one, leviProj_leviEmb, deltaHalf_of_mem_leviK (leviKOne_le_leviK hl)] at hlaw
  show ρ l ((u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 1) = (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 1
  rw [h4] at hlaw
  simpa using hlaw.symm

private theorem val_of_redK_mem (hPF : ParaFactor) (F : IndSp (stdBlocks d hd) ρ)
    (hF : ∀ x, ∀ c ∈ KOne k (Fin N), F.1.1 (x * c) = F.1.1 x)
    (κ₀ : KO k (Fin N)) (hκ : redK k (Fin N) κ₀ ∈ parab 𝓀[k] (stdBlocks d hd)) :
    ∃ x : leviK k fun a => Fin (d a),
      redLevi k _ x = leviProj 𝓀[k] (stdBlocks d hd) ⟨redK k (Fin N) κ₀, hκ⟩ ∧
      F.1.1 κ₀ = ρ (x : Levi k fun a => Fin (d a)) (F.1.1 1) := by
  have hg : (κ₀ : GL (Fin N) k) ∈ parahoric k (stdBlocks d hd) := (coe_mem_levelPre κ₀).2 hκ
  obtain ⟨p, x, -, hpx, hred, c, hc, hgp⟩ := (hPF k (stdBlocks d hd)).1 ⟨κ₀, hg⟩
  have h3 := parInd_law (stdBlocks d hd) ρ F p 1
  rw [mul_one, hpx, deltaHalf_of_mem_leviK x.2, Units.val_one, one_smul] at h3
  have h4 : (κ₀ : GL (Fin N) k) = p * c := hgp
  refine ⟨x, hred, ?_⟩
  rw [h4, hF _ c hc]
  exact h3

set_option maxHeartbeats 1000000 in

private theorem evalOne_parab (hPF : ParaFactor)
    {κ : Representation ℂ (Levi 𝓀[k] fun a => Fin (d a)) Z} {Φ : W →ₗ[ℂ] Z}
    (hΦ : ∀ (x : leviK k fun a => Fin (d a)) (w : W),
      Φ (ρ (x : Levi k fun a => Fin (d a)) w) = κ (redLevi k _ x) (Φ w))
    (S : Subrepresentation (parInd (stdBlocks d hd) ρ)) (h : parab 𝓀[k] (stdBlocks d hd))
    (u : fixed S.toRepresentation (KOne k (Fin N))) :
    Φ (evalOne S (levelZero S.toRepresentation (h : GL (Fin N) 𝓀[k]) u)) =
      κ (leviProj 𝓀[k] (stdBlocks d hd) h) (Φ (evalOne S u)) := by
  rcases h with ⟨h, hmem⟩
  obtain ⟨κ₀, rfl⟩ := redK_surjective h
  obtain ⟨x, hx1, hx2⟩ := val_of_redK_mem hPF (u.1.1 : IndSp (stdBlocks d hd) ρ)
    (fun y c hc => val_mul_of_mem S u y hc) κ₀ hmem
  exact (congrArg Φ ((evalOne_redK S κ₀ u).trans hx2)).trans
    ((hΦ x _).trans (congrArg (fun g => κ g (Φ (evalOne S u))) hx1))

private theorem eq_zero_of_evalOne (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (u : fixed S.toRepresentation (KOne k (Fin N)))
    (hu : ∀ γ : GL (Fin N) 𝓀[k], evalOne S (levelZero S.toRepresentation γ u) = 0) : u = 0 := by
  have hF : (u.1.1 : IndSp (stdBlocks d hd) ρ) = 0 :=
    UpperTheory.TNZ.step_indDetK k s N d hd W ρ _ 0 fun κ hκ => by
      have := hu (redK k (Fin N) ⟨κ, hκ⟩)
      rw [evalOne_redK] at this
      exact this
  exact Subtype.ext (Subtype.ext hF)

private theorem main (hPF : ParaFactor) {π : Representation ℂ (GL (Fin N) k) V}
    {κ : Representation ℂ (Levi 𝓀[k] fun a => Fin (d a)) Z} {Φ : W →ₗ[ℂ] Z}
    (hΦ : ∀ (x : leviK k fun a => Fin (d a)) (w : W),
      Φ (ρ (x : Levi k fun a => Fin (d a)) w) = κ (redLevi k _ x) (Φ w))
    (hinj : ∀ w ∈ fixed ρ (leviKOne k fun a => Fin (d a)), Φ w = 0 → w = 0)
    (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (sec : fixed π (KOne k (Fin N)) →ₗ[ℂ] fixed S.toRepresentation (KOne k (Fin N)))
    (hs : ∀ g x, sec (levelZero π g x) = levelZero S.toRepresentation g (sec x))
    (hinv : Function.Injective sec)
    (hfix : fixed π (KOne k (Fin N)) ≠ ⊥) :
    ∃ ψ : fixed π (KOne k (Fin N)) →ₗ[ℂ] Z, ψ ≠ 0 ∧
      ∀ (p : parab 𝓀[k] (stdBlocks d hd)) (x : fixed π (KOne k (Fin N))),
        ψ (levelZero π p x) = κ (leviProj 𝓀[k] (stdBlocks d hd) p) (ψ x) := by
  obtain ⟨x0, hx0mem, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
  let y0 : fixed π (KOne k (Fin N)) := ⟨x0, hx0mem⟩
  have hsx : sec y0 ≠ 0 := by
    intro h0
    apply hx0
    have h1 := hinv (h0.trans (map_zero sec).symm)
    exact congrArg Subtype.val h1
  have hγ : ∃ γ, evalOne S (levelZero S.toRepresentation γ (sec y0)) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hsx (eq_zero_of_evalOne S _ hc)
  obtain ⟨γ, hγ⟩ := hγ
  refine ⟨Φ ∘ₗ (evalOne S ∘ₗ sec), ?_, ?_⟩
  · intro h0
    apply hγ
    apply hinj _ (evalOne_mem_fixed S _)
    have h1 := LinearMap.congr_fun h0 (levelZero π γ y0)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hs] at h1
    exact h1
  · intro p x
    have h3 := evalOne_parab hPF hΦ S p (sec x)
    calc (Φ ∘ₗ (evalOne S ∘ₗ sec)) (levelZero π p x)
        = Φ (evalOne S (levelZero S.toRepresentation p (sec x))) :=
          congrArg (fun w => Φ (evalOne S w)) (hs _ _)
      _ = _ := h3

end SlopeTestRemainingChoices

end UpperTheory.Gal.InertialTypesAlt.SubquotientMaps

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.Gal.InertialTypesAlt.SubquotientMaps in
set_option synthInstance.maxHeartbeats 400000 in
theorem UpperTheory.Gal.InertialTypesAlt.subqMap :
    FinSec → UpperTheory.Gal.TypesAndIwahori.ParaFactor → SubqMap := by
  intro hSec hPF k _ _ _ _ N s d hd W V Z _ _ _ _ _ _ ρ π κ Φ hΦ hinj hsq hfix
  obtain ⟨S, f, hf⟩ := hsq
  have : Finite (GL (Fin N) 𝓀[k]) := inferInstance
  obtain ⟨sec, hs, hfs⟩ := hSec (GL (Fin N) 𝓀[k])
    (fixed S.toRepresentation (KOne k (Fin N))) (fixed π (KOne k (Fin N)))
    (levelZero S.toRepresentation) (levelZero π) (levelZeroMap f).toLinearMap
    (fun g x => Representation.IntertwiningMap.isIntertwining _ _ (levelZeroMap f) g x) (levelZeroMap_surjective f hf)
  exact main hPF hΦ hinj S sec hs (Function.LeftInverse.injective hfs) hfix
