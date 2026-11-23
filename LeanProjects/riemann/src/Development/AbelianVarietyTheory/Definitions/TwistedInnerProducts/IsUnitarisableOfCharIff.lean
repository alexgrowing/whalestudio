import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.SmGL

section General

variable {F G H V W U : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]

def twist (ρ : Representation F G V) (χ : G →* Fˣ) : Representation F G V where
  toFun g := (χ g : F) • ρ g
  map_one' := by simp
  map_mul' a b := by
    ext v
    simp [smul_smul, mul_comm]

@[simp] theorem twist_apply (ρ : Representation F G V) (χ : G →* Fˣ) (g : G) (v : V) :
    twist ρ χ g v = (χ g : F) • ρ g v := rfl

theorem twist_twist (ρ : Representation F G V) (χ ψ : G →* Fˣ) :
    twist (twist ρ χ) ψ = twist ρ (ψ * χ) := by
  ext g v; simp [smul_smul]

@[simp] theorem twist_one (ρ : Representation F G V) : twist ρ 1 = ρ := by
  ext g v; simp

def ofChar (χ : G →* Fˣ) : Representation F G F := twist (Representation.trivial F G F) χ

@[simp] theorem ofChar_apply (χ : G →* Fˣ) (g : G) (x : F) : ofChar χ g x = (χ g : F) * x := by
  simp [ofChar]

theorem isIrreducible_ofChar (χ : G →* Fˣ) : (ofChar χ).IsIrreducible := by
  have : Nontrivial (Subrepresentation (ofChar χ)) := ⟨⊥, ⊤, fun h => by
    have := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule F F) this⟩
  refine ⟨fun S => ?_⟩
  rcases eq_bot_or_eq_top S.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

def twistMap {ρ : Representation F G V} {σ : Representation F G W} (f : ρ.IntertwiningMap σ)
    (χ : G →* Fˣ) : (twist ρ χ).IntertwiningMap (twist σ χ) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    ext v
    simp [f.isIntertwining]

def compMap {ρ : Representation F G V} {σ : Representation F G W} (f : ρ.IntertwiningMap σ)
    (s : H →* G) : Representation.IntertwiningMap (ρ.comp s) (σ.comp s) where
  toLinearMap := f.toLinearMap
  isIntertwining' h := f.isIntertwining' (s h)

def IsSubquotient (σ : Representation F G W) (ρ : Representation F G V) : Prop :=
  ∃ (S : Subrepresentation ρ) (f : S.toRepresentation.IntertwiningMap σ), Function.Surjective f

theorem IsSubquotient.of_surjective {σ : Representation F G W} {ρ : Representation F G V}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) : IsSubquotient σ ρ := by
  refine ⟨⊤, ⟨f.toLinearMap ∘ₗ (⊤ : Subrepresentation ρ).toSubmodule.subtype, fun g => ?_⟩, fun w => ?_⟩
  · ext v
    exact f.isIntertwining _ _ g v
  · obtain ⟨v, rfl⟩ := hf w
    exact ⟨⟨v, trivial⟩, rfl⟩

theorem IsSubquotient.refl (ρ : Representation F G V) : IsSubquotient ρ ρ :=
  .of_surjective (.id ρ) Function.surjective_id

theorem IsSubquotient.trans {τ : Representation F G U} {σ : Representation F G W}
    {ρ : Representation F G V} (h₁ : IsSubquotient τ σ) (h₂ : IsSubquotient σ ρ) :
    IsSubquotient τ ρ := by
  obtain ⟨S, f, hf⟩ := h₁
  obtain ⟨T, g, hg⟩ := h₂
  let R : Subrepresentation ρ :=
    ⟨(S.toSubmodule.comap g.toLinearMap).map T.toSubmodule.subtype, by
      rintro x _ ⟨v, hv, rfl⟩
      refine ⟨T.toRepresentation x v, ?_, rfl⟩
      show g (T.toRepresentation x v) ∈ S.toSubmodule
      rw [g.isIntertwining]
      exact S.apply_mem_toSubmodule x hv⟩
  have hRT : R.toSubmodule ≤ T.toSubmodule := by
    rintro _ ⟨v, -, rfl⟩; exact v.2
  have hmem : ∀ v : R.toSubmodule, (g.toLinearMap ∘ₗ Submodule.inclusion hRT) v ∈ S.toSubmodule := by
    rintro ⟨_, v, hv, rfl⟩; exact hv
  refine ⟨R, ⟨f.toLinearMap ∘ₗ LinearMap.codRestrict S.toSubmodule _ hmem, fun x => ?_⟩, fun u => ?_⟩
  · ext v
    show f _ = τ x (f _)
    rw [← f.isIntertwining]
    congr 1
    apply Subtype.ext
    exact g.isIntertwining _ _ x (Submodule.inclusion hRT v)
  · obtain ⟨w, rfl⟩ := hf u
    obtain ⟨v, hv⟩ := hg w
    refine ⟨⟨v, v, by show g v ∈ S.toSubmodule; rw [hv]; exact w.2, rfl⟩, ?_⟩
    show f _ = f w
    congr 1
    exact Subtype.ext hv

theorem IsSubquotient.of_injective {σ : Representation F G W} {ρ : Representation F G V}
    (f : σ.IntertwiningMap ρ) (hf : Function.Injective f) : IsSubquotient σ ρ := by
  let R : Subrepresentation ρ := ⟨LinearMap.range f.toLinearMap, by
    rintro x _ ⟨v, rfl⟩
    exact ⟨σ x v, f.isIntertwining _ _ x v⟩⟩
  let e := LinearEquiv.ofInjective f.toLinearMap hf
  refine ⟨R, ⟨e.symm.toLinearMap, fun x => ?_⟩, e.symm.surjective⟩
  ext v
  obtain ⟨w, rfl⟩ := e.surjective v
  show e.symm _ = σ x (e.symm (e w))
  rw [e.symm_apply_apply, LinearEquiv.symm_apply_eq]
  exact Subtype.ext (f.isIntertwining _ _ x w).symm

def HasFiniteLength (ρ : Representation F G V) : Prop :=
  IsFiniteLength (MonoidAlgebra F G) ρ.asModule

def subQuot {ρ : Representation F G V} (S T : Subrepresentation ρ) :
    Representation F G (S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) :=
  S.toRepresentation.quotient _ (fun g _ hv => T.apply_mem_toSubmodule g hv)

def OccursTimes (σ : Representation F G W) (ρ : Representation F G V) (r : ℕ) : Prop :=
  ∃ S T : Fin r → Subrepresentation ρ, (∀ i, T i ≤ S i) ∧ (∀ i j, i < j → S i ≤ T j) ∧
    ∀ i, Nonempty ((subQuot (S i) (T i)).Equiv σ)

def jhMult (σ : Representation F G W) (ρ : Representation F G V) : ℕ∞ :=
  ⨆ (r : ℕ) (_ : OccursTimes σ ρ r), (r : ℕ∞)

def extTensor (ρ : Representation F G V) (σ : Representation F H W) :
    Representation F (G × H) (V ⊗[F] W) :=
  Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))

@[simp] theorem extTensor_tmul (ρ : Representation F G V) (σ : Representation F H W) (g : G × H)
    (v : V) (w : W) : extTensor ρ σ g (v ⊗ₜ w) = ρ g.1 v ⊗ₜ σ g.2 w := by
  simp [extTensor]

def piTensor {α : Type} {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module F (X a)] (ρ : ∀ a, Representation F (Γ a) (X a)) :
    Representation F (∀ a, Γ a) (⨂[F] a, X a) :=
  PiTensorProduct.mapMonoidHom.comp
    (MonoidHom.pi fun a => (ρ a).comp (Pi.evalMonoidHom Γ a))

@[simp] theorem piTensor_tprod {α : Type} {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module F (X a)] (ρ : ∀ a, Representation F (Γ a) (X a))
    (g : ∀ a, Γ a) (x : ∀ a, X a) :
    piTensor ρ g (PiTensorProduct.tprod F x) = PiTensorProduct.tprod F fun a => ρ a (g a) (x a) := by
  exact PiTensorProduct.map_tprod _ _

def jacquetMap {ρ : Representation F G V} {σ : Representation F G W} (f : ρ.IntertwiningMap σ)
    (N : Subgroup G) (s : H →* G) (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) :
    (jacquet ρ N s hs).IntertwiningMap (jacquet σ N s hs) where
  toLinearMap := (twKer ρ N 1).mapQ (twKer σ N 1) f.toLinearMap (Submodule.span_le.2 (by
    rintro _ ⟨n, v, rfl⟩
    refine Submodule.subset_span ⟨n, f v, ?_⟩
    simp [f.isIntertwining]))
  isIntertwining' m := by
    ext v
    exact congrArg Submodule.Quotient.mk (f.isIntertwining _ _ (s m) v)

theorem jacquet_mk (ρ : Representation F G V) (N : Subgroup G) (s : H →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) (m : H) (v : V) :
    jacquet ρ N s hs m (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ (s m) v) := rfl

section Top

variable [TopologicalSpace G]

theorem isSmooth_iff_isSmoothRep {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X) :
    IsSmooth ρ ↔ IsSmoothRep ρ := Iff.rfl

def IsSmoothChar (χ : G →* Fˣ) : Prop := IsOpen (χ.ker : Set G)

theorem isSmooth_comp [TopologicalSpace H] {ρ : Representation F G V} (hρ : IsSmooth ρ) (s : H →* G)
    (hs : Continuous s) : IsSmooth (ρ.comp s : Representation F H V) :=
  fun v => (hρ v).preimage hs

theorem IsSmoothChar.comp [TopologicalSpace H] {χ : G →* Fˣ} (hχ : IsSmoothChar χ) (s : H →* G)
    (hs : Continuous s) : IsSmoothChar (χ.comp s) :=
  IsOpen.preimage hs hχ

theorem IsSmoothChar.inv {χ : G →* Fˣ} (hχ : IsSmoothChar χ) : IsSmoothChar χ⁻¹ := by
  have : (χ⁻¹.ker : Set G) = χ.ker := by ext g; simp
  unfold IsSmoothChar; rw [this]; exact hχ

variable [IsTopologicalGroup G]

theorem mem_smoothPart_of_nhds {ρ : Representation F G V} {v : V}
    (h : {g : G | ρ g v = v} ∈ nhds (1 : G)) : v ∈ smoothPart ρ :=
  Subgroup.isOpen_of_mem_nhds
    { carrier := {g | ρ g v = v}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul]; simp } h

theorem isSmooth_of_nhds {ρ : Representation F G V}
    (h : ∀ v, {g : G | ρ g v = v} ∈ nhds (1 : G)) : IsSmooth ρ := fun v =>
  mem_smoothPart_of_nhds (h v)

theorem IsSmoothChar.mul {χ ψ : G →* Fˣ} (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) :
    IsSmoothChar (χ * ψ) :=
  Subgroup.isOpen_mono (H₁ := χ.ker ⊓ ψ.ker)
    (fun g hg => by simp [MonoidHom.mem_ker.1 hg.1, MonoidHom.mem_ker.1 hg.2]) (IsOpen.inter hχ hψ)

theorem isSmooth_twist {ρ : Representation F G V} (hρ : IsSmooth ρ) {χ : G →* Fˣ}
    (hχ : IsSmoothChar χ) : IsSmooth (twist ρ χ) :=
  isSmooth_of_nhds fun v => Filter.mem_of_superset (((hρ v).inter hχ).mem_nhds (by simp)) (by
    rintro g ⟨h1, h2⟩
    have h1' : ρ g v = v := h1
    have h2' : χ g = 1 := h2
    simp [h1', h2'])

theorem isSmooth_ofChar_iff (χ : G →* Fˣ) : IsSmooth (ofChar χ) ↔ IsSmoothChar χ := by
  refine ⟨fun h => ?_, fun h => isSmooth_twist (fun v => by simp) h⟩
  have : (χ.ker : Set G) = {g | ofChar χ g 1 = 1} := by ext g; simp
  unfold IsSmoothChar; rw [this]; exact h 1

theorem IsSubquotient.isSmooth {σ : Representation F G W} {ρ : Representation F G V}
    (h : IsSubquotient σ ρ) (hρ : IsSmooth ρ) : IsSmooth σ := by
  obtain ⟨S, f, hf⟩ := h
  refine isSmooth_of_nhds fun w => ?_
  obtain ⟨v, rfl⟩ := hf w
  refine Filter.mem_of_superset ((hρ v).mem_nhds (by simp)) fun g hg => ?_
  show σ g (f v) = f v
  rw [← f.isIntertwining]
  congr 1
  exact Subtype.ext hg

theorem isSmooth_smoothRep (ρ : Representation F G V) : IsSmooth (smoothRep ρ) := fun v => by
  have : {g : G | smoothRep ρ g v = v} = {g : G | ρ g v = v} := by
    ext g; exact Subtype.ext_iff
  rw [this]; exact v.2

theorem isSmooth_jacquet [TopologicalSpace H] [IsTopologicalGroup H] {ρ : Representation F G V}
    (hρ : IsSmooth ρ) (N : Subgroup G) (s : H →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) (hc : Continuous s) :
    IsSmooth (jacquet ρ N s hs) := by
  refine isSmooth_of_nhds fun w => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  refine Filter.mem_of_superset (((hρ v).preimage hc).mem_nhds (by simp)) fun g hg => ?_
  have hg' : ρ (s g) v = v := hg
  show jacquet ρ N s hs g _ = _
  rw [jacquet_mk, hg']

theorem isSmooth_extTensor [TopologicalSpace H] [IsTopologicalGroup H] {ρ : Representation F G V}
    {σ : Representation F H W} (hρ : IsSmooth ρ) (hσ : IsSmooth σ) : IsSmooth (extTensor ρ σ) := by
  intro x
  show x ∈ smoothPart (extTensor ρ σ)
  induction x with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul v w =>
    refine mem_smoothPart_of_nhds (Filter.mem_of_superset
      (((hρ v).prod (hσ w)).mem_nhds (by simp)) fun g hg => ?_)
    have h1 : ρ g.1 v = v := hg.1
    have h2 : σ g.2 w = w := hg.2
    simp [h1, h2]

theorem isSmooth_piTensor {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module F (X a)] {ρ : ∀ a, Representation F (Γ a) (X a)} (hρ : ∀ a, IsSmooth (ρ a)) :
    IsSmooth (piTensor ρ) := by
  intro x
  show x ∈ smoothPart (piTensor ρ)
  induction x using PiTensorProduct.induction_on with
  | add x y hx hy => exact add_mem hx hy
  | smul_tprod c x =>
    refine Submodule.smul_mem _ c (mem_smoothPart_of_nhds (Filter.mem_of_superset
      ((isOpen_set_pi Set.finite_univ fun a _ => hρ a (x a)).mem_nhds (by simp)) fun g hg => ?_))
    have h : ∀ a, ρ a (g a) (x a) = x a := fun a => hg a trivial
    simp [h]

def contra (ρ : Representation F G V) : Representation F G (smoothPart ρ.dual) := smoothRep ρ.dual

@[simp] theorem contra_apply (ρ : Representation F G V) (g : G) (l : smoothPart ρ.dual) (v : V) :
    (contra ρ g l : Module.Dual F V) v = (l : Module.Dual F V) (ρ g⁻¹ v) := rfl

theorem isSmooth_contra (ρ : Representation F G V) : IsSmooth (contra ρ) := isSmooth_smoothRep _

def smIndMap {P : Subgroup G} {σ : Representation F P W} {τ : Representation F P U}
    (f : σ.IntertwiningMap τ) : (smInd P σ).IntertwiningMap (smInd P τ) where
  toLinearMap :=
    { toFun := fun φ => ⟨⟨fun g => f (φ.1.1 g), fun h g => by
          show f (φ.1.1 (h * g)) = τ h (f (φ.1.1 g))
          rw [φ.1.2 h g, f.isIntertwining]⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds φ.2 (by simp)) fun g hg => by
          have hg' : ind P σ g φ.1 = φ.1 := hg
          apply Subtype.ext
          funext x
          exact congrArg f (congrFun (congrArg Subtype.val hg') x))⟩
      map_add' := fun φ ψ => by ext g; simp
      map_smul' := fun c φ => by ext g; simp }
  isIntertwining' g := by ext φ x; rfl

end Top

def IsUnitarisable {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X) : Prop :=
  ∃ B : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ, (∀ v w, B w v = starRingEnd ℂ (B v w)) ∧ (∀ v, v ≠ 0 → 0 < (B v v).re) ∧
    ∀ g v w, B (ρ g v) (ρ g w) = B v w

def IsUnitaryChar (χ : G →* ℂˣ) : Prop := ∀ g, ‖(χ g : ℂ)‖ = 1

theorem isUnitarisable_ofChar_iff (χ : G →* ℂˣ) : IsUnitarisable (ofChar χ) ↔ IsUnitaryChar χ := by
  constructor
  · rintro ⟨B, -, hp, hi⟩ g
    have h := hi g 1 1
    have h0 : B 1 1 ≠ 0 := fun h => by simpa [h] using hp 1 one_ne_zero
    rw [ofChar_apply, ← smul_eq_mul, B.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul,
      smul_eq_mul, ← mul_assoc, Complex.mul_conj, mul_eq_right₀ h0] at h
    have h2 : ‖(χ g : ℂ)‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]; exact_mod_cast h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  · intro h
    refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => x * starRingEnd ℂ y)
      (fun _ _ _ => add_mul _ _ _) (fun _ _ _ => by simp [mul_assoc])
      (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp [mul_left_comm]), ?_, ?_, ?_⟩
    · intro v w; simp [mul_comm]
    · intro v hv; simpa [Complex.mul_conj] using hv
    · intro g v w
      have : (χ g : ℂ) * starRingEnd ℂ (χ g) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h g]; simp
      simp only [LinearMap.mk₂'ₛₗ_apply, ofChar_apply, map_mul]
      linear_combination (v * starRingEnd ℂ w) * this

def IsSphericalFor (ρ : Representation F G V) (K : Subgroup G) : Prop := fixed ρ K ≠ ⊥

def IsZonal (ρ : Representation F G V) (K : Subgroup G) (ω : G → F) : Prop :=
  ∃ v ∈ fixed ρ K, ∃ l ∈ fixed ρ.dual K, l v = 1 ∧ ∀ g, ω g = l (ρ g v)

end General

end GlobalTheory.SmGL
