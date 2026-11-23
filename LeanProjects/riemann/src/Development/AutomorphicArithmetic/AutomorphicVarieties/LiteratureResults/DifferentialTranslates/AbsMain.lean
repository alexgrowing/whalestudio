import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Acyclic
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ShiftUp
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ShiftOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ShiftZero
open UpperTheory.V.Lit.Dr

private def UpperTheory.V.Lit.Dr.kerRep {Γ A B : Type} [Group Γ] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (ρ : Representation ℂ Γ A) (σ : Representation ℂ Γ B) (f : A →ₗ[ℂ] B) (hf : ∀ γ x, f (ρ γ x) = σ γ (f x)) :
    Representation ℂ Γ (LinearMap.ker f) where
  toFun γ := (ρ γ).restrict (fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hf, hx, map_zero])
  map_one' := by ext x; simp
  map_mul' γ δ := by ext x; simp

private theorem UpperTheory.V.Lit.Dr.absPos (q : ℕ) :
    ∀ (Γ M : Type) (Ω : ℕ → Type) [Group Γ] [AddCommGroup M] [Module ℂ M] [∀ q, AddCommGroup (Ω q)] [∀ q, Module ℂ (Ω q)]
    (ρM : Representation ℂ Γ M) (ρ : ∀ q, Representation ℂ Γ (Ω q)) (ι : M →ₗ[ℂ] Ω 0) (d : ∀ q, Ω q →ₗ[ℂ] Ω (q + 1)),
    (∀ γ m, ι (ρM γ m) = ρ 0 γ (ι m)) → (∀ q γ x, d q (ρ q γ x) = ρ (q + 1) γ (d q x)) → Function.Injective ι →
    Function.Exact ι (d 0) → (∀ q, Function.Exact (d q) (d (q + 1))) → (∀ q, HasAverage (ρ q)) →
    ∀ (n : ℕ) (w : Fin n → Ω (q + 1)), (∀ i γ, ρ (q + 1) γ (w i) = w i) → (∀ i, d (q + 1) (w i) = 0) →
    (∀ c : Fin n → ℂ, (∃ y, (∀ γ, ρ q γ y = y) ∧ d q y = ∑ i, c i • w i) → c = 0) →
    (n : Cardinal) ≤ Module.rank ℂ (groupCohomology (Rep.of ρM) (q + 1)) := by
  induction q with
  | zero =>
    intro Γ M Ω _ _ _ _ _ ρM ρ ι d hι hd hinj hex0 hex hav n w hw hdw hind
    let π : Ω 0 →ₗ[ℂ] LinearMap.ker (d 1) := (d 0).codRestrict _ (fun x => (hex 0).apply_apply_eq_zero x)
    refine shiftOne Γ M (Ω 0) (LinearMap.ker (d 1)) ρM (ρ 0) (kerRep (ρ 1) (ρ 2) (d 1) (hd 1)) ι π hι
      (fun γ x => Subtype.ext (hd 0 γ x)) hinj
      (fun z => by obtain ⟨y, hy⟩ := (hex 0 z.1).1 z.2; exact ⟨y, Subtype.ext hy⟩)
      (fun x => by rw [← hex0 x, Subtype.ext_iff]; rfl) n (fun i => ⟨w i, hdw i⟩)
      (fun i γ => Subtype.ext (hw i γ)) ?_
    rintro c ⟨y, hy, hy'⟩
    refine hind c ⟨y, hy, ?_⟩
    have h : (π y).1 = ∑ i, c i • w i := by rw [hy']; simp
    exact h
  | succ q ih =>
    intro Γ M Ω _ _ _ _ _ ρM ρ ι d hι hd hinj hex0 hex hav n w hw hdw hind
    let π : Ω 0 →ₗ[ℂ] LinearMap.ker (d 1) := (d 0).codRestrict _ (fun x => (hex 0).apply_apply_eq_zero x)
    refine le_trans (ih Γ (LinearMap.ker (d 1)) (fun k => Ω (k + 1)) (kerRep (ρ 1) (ρ 2) (d 1) (hd 1))
      (fun k => ρ (k + 1)) (LinearMap.ker (d 1)).subtype (fun k => d (k + 1)) (fun γ m => rfl)
      (fun k => hd (k + 1)) Subtype.val_injective (LinearMap.exact_subtype_ker_map _) (fun k => hex (k + 1))
      (fun k => hav (k + 1)) n w hw hdw hind) ?_
    exact shiftUp Γ M (Ω 0) (LinearMap.ker (d 1)) ρM (ρ 0) (kerRep (ρ 1) (ρ 2) (d 1) (hd 1)) ι π hι
      (fun γ x => Subtype.ext (hd 0 γ x)) hinj
      (fun z => by obtain ⟨y, hy⟩ := (hex 0 z.1).1 z.2; exact ⟨y, Subtype.ext hy⟩)
      (fun x => by rw [← hex0 x, Subtype.ext_iff]; rfl) (acyclic Γ (Ω 0) (ρ 0) (hav 0)) q

theorem UpperTheory.V.Lit.Dr.absMain :
    AbsMain := by
  intro q Γ M Ω _ _ _ _ _ ρM ρ ι d hι hd hinj hex0 hex hav n w hw hdw hind
  cases q with
  | zero =>
    choose m hm using fun i => (hex0 (w i)).1 (hdw i)
    refine shiftZero Γ M ρM n m (fun i γ => hinj (by rw [hι, hm, hw])) (fun c hc => hind c ?_)
    have := congrArg ι hc
    simpa [InvExact, hm] using this
  | succ q => exact absPos q Γ M Ω ρM ρ ι d hι hd hinj hex0 hex hav n w hw hdw hind
