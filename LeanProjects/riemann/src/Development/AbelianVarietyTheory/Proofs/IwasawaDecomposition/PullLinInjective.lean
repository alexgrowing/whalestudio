import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

namespace CarDim

section Pull

variable {O : Type} [CommRing O] {bar : O → O} {ψ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
  [AddCommGroup X₁] [Module O X₁] {m : ℕ}

theorem isCell_pull_equiv [Module.Finite O X] [Module.Finite O X₁] {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : IsCell bar ψ γ) (e : X ≃ₗ[O] X₁) : IsCell bar ψ fun i => pull e.toLinearMap (γ i) :=
  ⟨fun i => pull_mem _ (h.mem i), fun i _ => h.nonneg i _, (linearOn_pull_iff e.surjective).2 h.linear,
    IsStrict.of_pull (r := e.symm.toLinearMap) e.symm.surjective (by simpa using h.strict)⟩

def pullLin (r : X →ₗ[O] X₁) : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pull r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pullLin_apply (r : X →ₗ[O] X₁) (β : LinearMap.BilinForm ℤ X₁) : pullLin r β = pull r β := rfl

theorem pullLin_injective {r : X →ₗ[O] X₁} (hr : Function.Surjective r) : Function.Injective (pullLin r) :=
  fun β β' h => LinearMap.ext₂ fun a b => by
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    exact LinearMap.congr_fun₂ h a b

theorem genRank_pull {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (γ : Fin m → LinearMap.BilinForm ℤ X₁) :
    genRank (fun i => pull r (γ i)) = genRank γ := by
  unfold genRank
  have e : Submodule.span ℤ (Set.range fun i => pull r (γ i)) = (Submodule.span ℤ (Set.range γ)).map (pullLin r) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [e]
  exact (Submodule.equivMapOfInjective _ (pullLin_injective hr) _).finrank_eq.symm

theorem inRCone_pull_iff {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    {β : LinearMap.BilinForm ℤ X₁} : InRCone (fun i => pull r (γ i)) (pull r β) ↔ InRCone γ β := by
  refine exists_congr fun c => and_congr_right fun _ => ?_
  constructor
  · intro h
    refine LinearMap.ext₂ fun a b => ?_
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    have := LinearMap.congr_fun₂ h a b
    simpa [LinearMap.sum_apply] using this
  · intro h
    refine LinearMap.ext₂ fun a b => ?_
    have := LinearMap.congr_fun₂ h (r a) (r b)
    simpa [LinearMap.sum_apply] using this

end Pull

section Rad

variable {O : Type} [CommRing O] {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]

def orad (β : LinearMap.BilinForm ℤ X) : Submodule O X where
  carrier := {x | ∀ (a : O) (y : X), β (a • x) y = 0}
  add_mem' := by
    intro x x' hx hx' a y
    rw [smul_add, map_add, LinearMap.add_apply, hx a y, hx' a y, add_zero]
  zero_mem' := by
    intro a y
    rw [smul_zero, map_zero, LinearMap.zero_apply]
  smul_mem' := by
    intro c x hx a y
    rw [smul_smul]
    exact hx _ y

theorem mem_orad {β : LinearMap.BilinForm ℤ X} {x : X} : x ∈ orad (O := O) β ↔ ∀ (a : O) (y : X), β (a • x) y = 0 :=
  Iff.rfl

theorem orad_pull {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (β : LinearMap.BilinForm ℤ X₁) :
    orad (pull r β) = (orad β).comap r := by
  ext x
  simp only [Submodule.mem_comap, mem_orad, pull_apply, map_smul]
  constructor
  · intro h a y
    obtain ⟨y, rfl⟩ := hr y
    exact h a y
  · intro h a y
    exact h a (r y)

def qEquiv {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (N : Submodule O X₁) : (X ⧸ N.comap r) ≃ₗ[O] (X₁ ⧸ N) :=
  (Submodule.quotEquivOfEq _ _ (by rw [LinearMap.ker_comp, Submodule.ker_mkQ])).trans
    ((N.mkQ ∘ₗ r).quotKerEquivOfSurjective (N.mkQ_surjective.comp hr))

theorem qEquiv_mk {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (N : Submodule O X₁) (x : X) :
    qEquiv hr N (Submodule.Quotient.mk x) = Submodule.Quotient.mk (r x) := rfl

end Rad

section Def

variable {O : Type} [CommRing O] (bar : O → O) (ψ : InvFun O)

def cdimSet (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (N : Submodule O X) (β : LinearMap.BilinForm ℤ X) :
    Set ℕ :=
  {k | ∃ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ (X ⧸ N)), IsCell bar ψ δ ∧ InRCone (fun i => pull N.mkQ (δ i)) β ∧
    genRank δ = k}

def cdimQ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (N : Submodule O X) (β : LinearMap.BilinForm ℤ X) : ℕ :=
  sInf (cdimSet bar ψ X N β)

variable {bar ψ}

theorem cdimSet_pull {X X₁ : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup X₁] [Module O X₁]
    [Module.Finite O X₁] {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (β : LinearMap.BilinForm ℤ X₁) :
    cdimSet bar ψ X (orad (pull r β)) (pull r β) = cdimSet bar ψ X₁ (orad β) β := by
  rw [orad_pull hr]
  set N := orad (O := O) β
  let e := qEquiv hr N
  have key : ∀ δ : LinearMap.BilinForm ℤ (X₁ ⧸ N),
      pull (N.comap r).mkQ (pull e.toLinearMap δ) = pull r (pull N.mkQ δ) := fun δ => rfl
  ext k
  constructor
  · rintro ⟨m, δ', h1, h2, rfl⟩
    refine ⟨m, fun i => pull e.symm.toLinearMap (δ' i), isCell_pull_equiv h1 e.symm, ?_,
      genRank_pull e.symm.surjective _⟩
    rw [← inRCone_pull_iff hr]
    convert h2 using 2 with i
    rw [← key, pull_pull_symm]
  · rintro ⟨m, δ, h1, h2, rfl⟩
    refine ⟨m, fun i => pull e.toLinearMap (δ i), isCell_pull_equiv h1 e, ?_, genRank_pull e.surjective _⟩
    simp only [key]
    exact (inRCone_pull_iff hr).2 h2

theorem zero_mem_cdimSet {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Subsingleton X] (N : Submodule O X)
    (β : LinearMap.BilinForm ℤ X) : 0 ∈ cdimSet bar ψ X N β := by
  haveI : Subsingleton (X ⧸ N) := ⟨fun a b => by
    induction a using Submodule.Quotient.induction_on
    induction b using Submodule.Quotient.induction_on
    rename_i a b
    rw [Subsingleton.elim a b]⟩
  refine ⟨0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0, fun c _ => ?_, ?_⟩,
    ⟨Fin.elim0, fun i => i.elim0, ?_⟩, ?_⟩
  · rw [ψ.eval_of_subsingleton]
    simp
  · refine ⟨1, 0, one_pos, fun i => i.elim0, fun β' _ _ => ?_, fun β' _ _ _ => ⟨1, Fin.elim0, one_pos, ?_⟩⟩
    · simp [InvFun.evalZ, ψ.eval_of_subsingleton]
    · rw [Fin.sum_univ_zero, one_smul]
      exact LinearMap.ext₂ fun a b => by rw [Subsingleton.elim a 0]; simp
  · exact LinearMap.ext₂ fun a b => by rw [Subsingleton.elim a 0]; simp
  · simp [genRank]

end Def

section Fun

variable {O : Type} [CommRing O] (bar : O → O) (ψ : InvFun O)

open Classical in

def carFun : InvFun O where
  toFun n B := if h : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
      ∀ a b, B a b = β a b then (cdimQ bar ψ (Fin n → O) (orad h.choose) h.choose : ℝ) else 0
  inv n m r hr B := by
    obtain ⟨s, hs⟩ := Module.projective_lifting_property r LinearMap.id hr
    have hrs : ∀ a, r (s a) = a := fun a => LinearMap.congr_fun hs a
    by_cases h : ∃ β : LinearMap.BilinForm ℤ (Fin m → O), β ∈ balForms bar (Fin m → O) ∧ (∀ y, 0 ≤ β y y) ∧
        ∀ a b, B a b = β a b
    · have h' : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
          ∀ a b, B (r a) (r b) = β a b :=
        ⟨pull r h.choose, pull_mem r h.choose_spec.1, fun y => h.choose_spec.2.1 _, fun a b => h.choose_spec.2.2 _ _⟩
      rw [dif_pos h, dif_pos h']
      have e : h'.choose = pull r h.choose := LinearMap.ext₂ fun a b => by
        have h1 := h'.choose_spec.2.2 a b
        have h2 := h.choose_spec.2.2 (r a) (r b)
        rw [pull_apply]
        exact_mod_cast h1.symm.trans h2
      rw [e]
      unfold cdimQ
      rw [cdimSet_pull hr]
    · have h' : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
          ∀ a b, B (r a) (r b) = β a b := by
        rintro ⟨β, h1, h2, h3⟩
        exact h ⟨pull s β, pull_mem s h1, fun y => h2 _, fun a b => by rw [pull_apply, ← h3, hrs, hrs]⟩
      rw [dif_neg h, dif_neg h']
  zero B := by
    split_ifs with h
    · have := Nat.sInf_eq_zero.2 (Or.inl (zero_mem_cdimSet (bar := bar) (ψ := ψ) (orad h.choose) h.choose))
      unfold cdimQ
      rw [this, Nat.cast_zero]
    · rfl

variable {bar ψ}

theorem evalZ_carFun {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms bar X) (hp : ∀ y, 0 ≤ β y y) :
    (carFun bar ψ).evalZ β = cdimQ bar ψ X (orad β) β := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.evalZ, (carFun bar ψ).eval_eq hs]
  dsimp only [carFun]
  split_ifs with h
  · have e : h.choose = pull s β := LinearMap.ext₂ fun a b => by
      have := h.choose_spec.2.2 a b
      rw [pull_apply]
      exact_mod_cast this.symm
    rw [e]
    unfold cdimQ
    rw [cdimSet_pull hs]
  · exact absurd ⟨pull s β, pull_mem s hβ, fun y => hp _, fun a b => rfl⟩ h

end Fun

end CarDim

end GlobalTheory.PolFan
