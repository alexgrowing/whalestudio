import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaschkeProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsomorphismProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducible

open CategoryTheory ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.FromMackey

section Gen

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem repIso_of_constituent {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : FDRep ℂ Γ) (ρ : Representation ℂ Γ V) (hτ : Simple τ) (hρ : IsIrr ρ)
    (hc : IsConstituent τ ρ) : RepIso τ.ρ ρ := by
  have hM : ReciprocityTheory.Ty.Fin.St.MaschkeFacts := GlobalTheory.CompanionTheory.TyFin.Maschke.maschkeFacts
  have hS : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := GlobalTheory.CompanionTheory.TyFin.simpleIffIrr
  obtain ⟨φ, hφ, hne⟩ := hc
  have hpos : 0 < Module.finrank ℂ (Intw τ.ρ ρ) :=
    Module.finrank_pos_iff_exists_ne_zero.2
      ⟨⟨φ, hφ⟩, fun h => hne (congrArg Subtype.val h)⟩
  exact hM.2.2.2 Γ _ _ τ.ρ ρ ((hS.1 Γ τ).1 hτ) hρ hpos.ne'

theorem iso_of_repIso {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ τ' : FDRep ℂ Γ) (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W)
    (h₁ : RepIso τ.ρ ρ) (h₂ : RepIso ρ σ) (h₃ : RepIso τ'.ρ σ) : Nonempty (τ ≅ τ') := by
  have hS : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := GlobalTheory.CompanionTheory.TyFin.simpleIffIrr
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  obtain ⟨e₃, he₃⟩ := h₃
  refine (hS.2 Γ τ τ').2 ⟨(e₁.trans e₂).trans e₃.symm, fun γ v => ?_⟩
  apply e₃.injective
  simp [he₁, he₂, he₃]

end Gen

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

theorem cuspIso_refl {α : Type} [Fintype α] [DecidableEq α] (lam : FDRep ℂ (GL α K)) :
    CuspIso K lam lam :=
  (GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts : ReciprocityTheory.Ty.Fin.St.CuspIsoFacts) K α α α lam lam lam lam
    (Equiv.refl α) |>.2.2.1 ⟨Iso.refl _⟩

theorem cuspIso_symm {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)} (h : CuspIso K lam mu) : CuspIso K mu lam := by
  obtain ⟨e, -⟩ := id h
  exact ((GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts : ReciprocityTheory.Ty.Fin.St.CuspIsoFacts) K α β β lam lam mu mu e).1 h

theorem cuspIso_trans {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)}
    {nu : FDRep ℂ (GL γ K)} (h : CuspIso K lam mu) (h' : CuspIso K mu nu) : CuspIso K lam nu := by
  obtain ⟨e, -⟩ := id h
  exact ((GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts : ReciprocityTheory.Ty.Fin.St.CuspIsoFacts) K α β γ lam lam mu nu e).2.1 h h'

variable {K}

theorem supportUnique (hMk : MackeyCusp K) : SupportUnique K := by
  intro n s s' b b' lam mu τ hτ hl hm
  have hM : ReciprocityTheory.Ty.Fin.St.MaschkeFacts := GlobalTheory.CompanionTheory.TyFin.Maschke.maschkeFacts
  have h := hM.2.1 (GL (Fin n) K) τ _ _ (hcRep K b lam) (hcRep K b' mu) hτ hl.2.2 hm.2.2
  rw [hMk n s s' b b' lam mu hl.1 hm.1 hl.2.1 hm.2.1] at h
  obtain ⟨⟨π, hπ⟩⟩ := (Nat.card_ne_zero.1 h).1
  exact ⟨π, hπ⟩

theorem sqfreeIrr (hMk : MackeyCusp K) : SqfreeIrr K := by
  intro n s b lam hb hl hd
  have hM : ReciprocityTheory.Ty.Fin.St.MaschkeFacts := GlobalTheory.CompanionTheory.TyFin.Maschke.maschkeFacts
  have hcard := hMk n s s b b lam lam hb hb hl hl
  haveI : Unique {π : Fin s ≃ Fin s // ∀ c, CuspIso K (lam c) (lam (π c))} :=
    { default := ⟨Equiv.refl _, fun c => cuspIso_refl K (lam c)⟩
      uniq := fun ⟨π, h⟩ => Subtype.ext (Equiv.ext fun c => (hd c (π c) (h c)).symm) }
  rw [Nat.card_unique] at hcard
  exact hM.2.2.1 (GL (Fin n) K) _ (hcRep K b lam) hcard

theorem sqfreeUnique (hMk : MackeyCusp K) : SqfreeUnique K := by
  intro n s s' b b' lam mu τ τ' hτ hτ' hl hm hd ⟨π, hπ⟩
  have hM : ReciprocityTheory.Ty.Fin.St.MaschkeFacts := GlobalTheory.CompanionTheory.TyFin.Maschke.maschkeFacts
  have hd' : ∀ c c', CuspIso K (mu c) (mu c') → c = c' := by
    intro c c' h
    obtain ⟨d, rfl⟩ := π.surjective c
    obtain ⟨d', rfl⟩ := π.surjective c'
    exact congrArg π
      (hd d d' (cuspIso_trans K (hπ d) (cuspIso_trans K h (cuspIso_symm K (hπ d')))))
  have hI : IsIrr (hcRep K b lam) := sqfreeIrr hMk n s b lam hl.1 hl.2.1 hd
  have hI' : IsIrr (hcRep K b' mu) := sqfreeIrr hMk n s' b' mu hm.1 hm.2.1 hd'
  have hne : Module.finrank ℂ (Intw (hcRep K b lam) (hcRep K b' mu)) ≠ 0 := by
    rw [hMk n s s' b b' lam mu hl.1 hm.1 hl.2.1 hm.2.1]
    haveI : Nonempty {π : Fin s ≃ Fin s' // ∀ c, CuspIso K (lam c) (mu (π c))} := ⟨⟨π, hπ⟩⟩
    exact Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  exact iso_of_repIso τ τ' (hcRep K b lam) (hcRep K b' mu)
    (repIso_of_constituent τ _ hτ hI hl.2.2)
    (hM.2.2.2 (GL (Fin n) K) _ _ _ _ hI hI' hne)
    (repIso_of_constituent τ' _ hτ' hI' hm.2.2)

theorem fromMackey : ReciprocityTheory.Ty.Fin.St.FromMackey :=
  fun _ _ _ _ hMk => ⟨supportUnique hMk, sqfreeIrr hMk, sqfreeUnique hMk⟩

end GlobalTheory.CompanionTheory.TyFin.FromMackey
