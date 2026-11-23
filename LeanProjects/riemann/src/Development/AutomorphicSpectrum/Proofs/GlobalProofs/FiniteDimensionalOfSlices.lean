import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart

open GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar

section Groups

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def ptStab (A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)) : Subgroup (GAd σ J) where
  carrier := {g | ∀ y ∈ A, (matHom _ σ J g).1 *ᵥ y = y}
  one_mem' := fun y _ => by simp
  mul_mem' := fun {a b} ha hb y hy => by
    rw [map_mul, Units.val_mul, ← mulVec_mulVec, hb y hy, ha y hy]
  inv_mem' := fun {a} ha y hy => by
    conv_lhs => rw [← ha y hy]
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]

def block (T : Finset (Fin r)) (k : Fin r) : Set (Fin r) := {i | i ≤ k ∧ ∀ t ∈ T, t < k → t < i}

def upTo (T : Finset (Fin r)) : Set (Fin r) := {i | ∃ k ∈ T, i ≤ k}

variable (X Y : Matrix (Fin n) (Fin r) E) (T : Finset (Fin r))

def glPart (k : Fin r) : Subgroup (GAd σ J) :=
  levi σ J X Y T ⊓ ptStab σ J (colPerp σ J X (block T k) ⊓ colPerp σ J Y (block T k))

def uPart : Subgroup (GAd σ J) := ptStab σ J (colSpan F X (upTo T) ⊔ colSpan F Y (upTo T))

def part : Option {k // k ∈ T} → Subgroup (GAd σ J)
  | none => uPart σ J X Y T
  | some k => glPart σ J X Y T k.1

end Groups

def sliceSet {G : Type} [Group G] (𝓒 : Set (G → ℂ)) (H L : Subgroup G) (b : G) : Set (H → ℂ) :=
  {f | ∃ φ ∈ 𝓒, ∃ y ∈ L, (∀ t ∈ H, t * y = y * t) ∧ f = fun t : H => φ ((t : G) * y * b)}

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin in

def cuspOn {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {m : ℕ}
    (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)) (U : Subgroup (GA D V))
    (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
    (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) : Set (GA D V → ℂ) :=
  {φ | φ ∈ formsOn θ V X Y T U ε fr ρ c ∧ ∀ T' : Finset (Fin m), T ⊂ T' → IsConstAlong D.sp.cm.sig V.gram X T' φ 0}

section Slices

theorem exists_finset_sep {X : Type} (A : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ A] :
    ∃ S : Finset X, ∀ f ∈ A, (∀ x ∈ S, f x = 0) → f = 0 := by
  classical
  let ev : X → Module.Dual ℂ A := fun x => (LinearMap.proj x).comp A.subtype
  have hfg : (Submodule.span ℂ (Set.range ev)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, e⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  obtain ⟨s', -, rfl⟩ := Finset.subset_set_image_iff.1 (by rwa [Set.image_univ] : (s : Set (Module.Dual ℂ A)) ⊆ ev '' Set.univ)
  refine ⟨s', fun f hf h0 => ?_⟩
  have h1 : ∀ l ∈ Submodule.span ℂ ((s'.image ev : Finset _) : Set (Module.Dual ℂ A)), l ⟨f, hf⟩ = 0 := fun l hl => by
    induction hl using Submodule.span_induction with
    | mem l h =>
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
      exact h0 x hx
    | zero => rfl
    | add a b _ _ ha hb => simp [ha, hb]
    | smul a b _ hb => simp [hb]
  funext x
  exact h1 (ev x) (e ▸ Submodule.subset_span ⟨x, rfl⟩)

theorem finiteDimensional_of_slices {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule ℂ (X i → ℂ))
    [∀ i, FiniteDimensional ℂ (A i)] (𝓕 : Set ((∀ i, X i) → ℂ))
    (h : ∀ f ∈ 𝓕, ∀ i x, (fun t => f (Function.update x i t)) ∈ A i) :
    FiniteDimensional ℂ (Submodule.span ℂ 𝓕) := by
  let P : Submodule ℂ ((∀ i, X i) → ℂ) :=
    { carrier := {f | ∀ i x, (fun t => f (Function.update x i t)) ∈ A i}
      add_mem' := fun {a b} ha hb i x => (A i).add_mem (ha i x) (hb i x)
      zero_mem' := fun i _ => (A i).zero_mem
      smul_mem' := fun a f hf i x => (A i).smul_mem a (hf i x) }
  choose S hS using fun i => exists_finset_sep (A i)
  let ev : P →ₗ[ℂ] ((∀ i, S i) → ℂ) :=
    { toFun := fun f s => f.1 fun i => (s i).1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have key : ∀ f : P, ev f = 0 → ∀ I : Finset ι, ∀ x : ∀ i, X i, (∀ i, i ∉ I → x i ∈ S i) → f.1 x = 0 := by
    intro f hf I
    induction I using Finset.induction_on with
    | empty =>
      intro x hx
      exact congrFun hf fun i => ⟨x i, hx i (by simp)⟩
    | insert a I _ ih =>
      intro x hx
      have := hS a _ (f.2 a x) fun t ht => ih _ fun i hi => by
        by_cases e : i = a
        · subst e; simpa using ht
        · rw [Function.update_of_ne e]
          exact hx i (by simp [e, hi])
      simpa using congrFun this (x a)
  have hinj : Function.Injective ev := (injective_iff_map_eq_zero ev).2 fun f hf =>
    Subtype.ext (funext fun x => key f hf Finset.univ x (by simp))
  haveI : FiniteDimensional ℂ P := FiniteDimensional.of_injective ev hinj
  exact Submodule.finiteDimensional_of_le (S₂ := P) (Submodule.span_le.2 fun f hf i x => h f hf i x)

end Slices

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
