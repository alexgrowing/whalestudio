import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

open Formalism.L2.DIV GlobalTheory.FinGL Matrix

variable {F : Type} [Field F] {r d : ℕ}

def incl (F : Type) [Field F] (e : Fin d → Fin r) : Matrix (Fin r) (Fin d) F :=
  (1 : Matrix (Fin r) (Fin r) F).submatrix id e

theorem incl_transpose_mul (e : Fin d ↪ Fin r) : (incl F e)ᵀ * incl F e = 1 := by
  ext a a'
  simp [incl, Matrix.mul_apply, Matrix.one_apply, eq_comm]

def extendMat (e : Fin d ↪ Fin r) : Matrix (Fin d) (Fin d) F →* Matrix (Fin r) (Fin r) F where
  toFun g := 1 + incl F e * (g - 1) * (incl F e)ᵀ
  map_one' := by simp
  map_mul' g h := by
    have key : incl F e * (g - 1) * (incl F e)ᵀ * (incl F e * (h - 1) * (incl F e)ᵀ)
        = incl F e * ((g - 1) * (h - 1)) * (incl F e)ᵀ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (incl F e)ᵀ, incl_transpose_mul, Matrix.one_mul]
    have e2 : g * h - 1 = (h - 1) + (g - 1) + (g - 1) * (h - 1) := by noncomm_ring
    rw [add_mul, mul_add, mul_add, key, e2]
    simp only [Matrix.mul_add, Matrix.add_mul, one_mul, mul_one, add_assoc]

theorem extendMat_apply (e : Fin d ↪ Fin r) (g : Matrix (Fin d) (Fin d) F) (i j : Fin r) :
    extendMat e g i j = (1 : Matrix (Fin r) (Fin r) F) i j +
      ∑ a', (∑ a, (if i = e a then 1 else 0) * (g - 1) a a') * (if j = e a' then 1 else 0) := by
  simp only [extendMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.add_apply, Matrix.mul_apply, incl,
    Matrix.transpose_apply, Matrix.submatrix_apply, id, Matrix.one_apply]

theorem extendMat_in (e : Fin d ↪ Fin r) (g : Matrix (Fin d) (Fin d) F) (a a' : Fin d) :
    extendMat e g (e a) (e a') = g a a' := by
  rw [extendMat_apply]
  simp [Matrix.one_apply]

theorem extendMat_out (e : Fin d ↪ Fin r) (g : Matrix (Fin d) (Fin d) F) (i j : Fin r)
    (h : i ∉ Set.range e ∨ j ∉ Set.range e) : extendMat e g i j = (1 : Matrix (Fin r) (Fin r) F) i j := by
  rw [extendMat_apply]
  rcases h with h | h
  · have : ∀ a, i ≠ e a := fun a ha => h ⟨a, ha.symm⟩
    simp [this]
  · have : ∀ a, j ≠ e a := fun a ha => h ⟨a, ha.symm⟩
    simp [this]

def block (b : Fin r → ℕ) (c : ℕ) : Finset (Fin r) := Finset.univ.filter fun i => b i = c

def blockEnum (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) : Fin d ↪ Fin r :=
  ((block b c).orderEmbOfFin h).toEmbedding

theorem blockEnum_mem (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (a : Fin d) :
    b (blockEnum b c h a) = c := by
  exact (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem (block b c) h a)).2

def blockHom (F : Type) [Field F] (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) :
    GL (Fin d) F →* blockTri (κ := F) b :=
  (Units.map (extendMat (blockEnum b c h))).codRestrict _ fun g => by
    refine mem_blockTri.2 fun i j hij => ?_
    show extendMat (blockEnum b c h) (g : Matrix (Fin d) (Fin d) F) i j = 0
    rw [extendMat_out, Matrix.one_apply_ne]
    · rintro rfl
      exact lt_irrefl _ hij
    · by_contra hc
      push Not at hc
      obtain ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩ := hc
      rw [blockEnum_mem b c h, blockEnum_mem b c h] at hij
      exact lt_irrefl _ hij

def IsIsotypicOf {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ G V) (ρ : Representation ℂ G W) : Prop :=
  (⨆ f : Representation.IntertwiningMap ρ τ, LinearMap.range f.toLinearMap) = ⊤

def IsFactor {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (c : ℕ)
    (ρ : Representation ℂ (GL (Fin d) F) W) : Prop :=
  ρ.IsIrreducible ∧ ∃ h : (block b c).card = d,
    IsIsotypicOf (show Representation ℂ (GL (Fin d) F) V from σ.comp (blockHom F b c h)) ρ

def IsoGL {d d' : ℕ} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ (GL (Fin d) F) W) (ρ' : Representation ℂ (GL (Fin d') F) W') : Prop :=
  ∃ h : d' = d, Nonempty (Representation.Equiv ρ (h ▸ ρ' : Representation ℂ (GL (Fin d) F) W'))

theorem isoGL_iff {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ (GL (Fin d) F) W) (ρ' : Representation ℂ (GL (Fin d) F) W') :
    IsoGL ρ ρ' ↔ Nonempty (Representation.Equiv ρ ρ') :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨rfl, h⟩⟩

def IsRegularCusp {V : Type} [AddCommGroup V] [Module ℂ V]
    (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V)
    (d : ℕ → ℕ) (W : ℕ → Type) [∀ c, AddCommGroup (W c)] [∀ c, Module ℂ (W c)]
    (ρ : ∀ c, Representation ℂ (GL (Fin (d c)) F) (W c)) : Prop :=
  IsCuspDatum b σ ∧ (∀ c ∈ Set.range b, IsFactor b σ c (ρ c)) ∧
    ∀ c ∈ Set.range b, ∀ c' ∈ Set.range b, c ≠ c' → ¬ IsoGL (ρ c) (ρ c')

def ProductIrreducible : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (r : ℕ) (b : Fin r → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (blockTri (κ := F) b) V)
    (d : ℕ → ℕ) (W : ℕ → Type) [∀ c, AddCommGroup (W c)] [∀ c, Module ℂ (W c)]
    (ρ : ∀ c, Representation ℂ (GL (Fin (d c)) F) (W c)),
    IsRegularCusp b σ d W ρ → (parInd b σ).IsIrreducible

def ProductIsoIff : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (r : ℕ)
    (b : Fin r → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (blockTri (κ := F) b) V)
    (d : ℕ → ℕ) (W : ℕ → Type) [∀ c, AddCommGroup (W c)] [∀ c, Module ℂ (W c)]
    (ρ : ∀ c, Representation ℂ (GL (Fin (d c)) F) (W c))
    (b' : Fin r → ℕ) (V' : Type) [AddCommGroup V'] [Module ℂ V'] (σ' : Representation ℂ (blockTri (κ := F) b') V')
    (d' : ℕ → ℕ) (W' : ℕ → Type) [∀ c, AddCommGroup (W' c)] [∀ c, Module ℂ (W' c)]
    (ρ' : ∀ c, Representation ℂ (GL (Fin (d' c)) F) (W' c)),
    IsRegularCusp b σ d W ρ → IsRegularCusp b' σ' d' W' ρ' →
    (Nonempty (Representation.Equiv (parInd b σ) (parInd b' σ')) ↔
      (∀ c ∈ Set.range b, ∃ c' ∈ Set.range b', IsoGL (ρ c) (ρ' c')) ∧
      (∀ c' ∈ Set.range b', ∃ c ∈ Set.range b, IsoGL (ρ c) (ρ' c')))

def IrrPar : Prop := ProductIrreducible ∧ ProductIsoIff

theorem isIsotypicOf_self {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) :
    IsIsotypicOf τ τ := by
  refine top_le_iff.1 (le_trans ?_ (le_iSup _ (Representation.IntertwiningMap.id τ)))
  intro v _
  exact ⟨v, rfl⟩

theorem trivial_irreducible (G : Type) [Group G] : (Representation.trivial ℂ G ℂ).IsIrreducible := by
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun h => ?_⟩⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule ℂ ℂ) this
  · rcases eq_bot_or_eq_top (α := Submodule ℂ ℂ) S.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.ext h)
    · exact Or.inr (Subrepresentation.ext h)

example : IsRegularCusp (F := F) (fun _ : Fin 1 => 0) (Representation.trivial ℂ _ ℂ) (fun _ => 1) (fun _ => ℂ)
    (fun _ => Representation.trivial ℂ _ ℂ) := by
  refine ⟨⟨monotone_const, trivial_irreducible _, fun _ _ => rfl, ?_⟩, ?_, ?_⟩
  · rintro S ⟨i, j, -, hi, hj⟩
    exact absurd (Subsingleton.elim i j ▸ hi) hj
  · rintro c ⟨_, rfl⟩
    exact ⟨trivial_irreducible _, by simp [block], isIsotypicOf_self _⟩
  · rintro c ⟨_, rfl⟩ c' ⟨_, rfl⟩ h
    exact absurd rfl h

end GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
