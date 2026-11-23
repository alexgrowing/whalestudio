import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

def fibM (X Z : Type) [TopologicalSpace X] [AddCommGroup Z] [Module ℂ Z] : Submodule ℂ (X → Z) where
  carrier := {φ | IsLocallyConstant φ ∧ HasCompactSupport φ}
  add_mem' ha hb := ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c φ hφ := ⟨hφ.1.comp (fun z => c • z), hφ.2.comp_left (g := fun z => c • z) (smul_zero c)⟩

section Cols

variable {k : Type}

def topP (i t : ℕ) (y : Fin (i + t) → k) : Fin i → k := fun j => y (Fin.castAdd t j)

def middlePart (i t : ℕ) (y : Fin (i + t) → k) : Fin t → k := fun j => y (Fin.natAdd i j)

theorem middlePart_add [Add k] (i t : ℕ) (a b : Fin (i + t) → k) : middlePart i t (a + b) = middlePart i t a + middlePart i t b := rfl

theorem continuous_topP [TopologicalSpace k] (i t : ℕ) : Continuous (topP (k := k) i t) :=
  continuous_pi fun _ => continuous_apply _

theorem continuous_midP [TopologicalSpace k] (i t : ℕ) : Continuous (middlePart (k := k) i t) :=
  continuous_pi fun _ => continuous_apply _

end Cols

section Act

variable {k Z : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k] [AddCommGroup Z] [Module ℂ Z]

def fibAct {i : ℕ} (t : ℕ) (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) :
    Representation ℂ (Multiplicative (Fin (i + t) → k)) (fibM (Fin t → k) Z) where
  toFun y :=
    { toFun := fun φ => ⟨fun v => ρ₀ (Multiplicative.ofAdd (topP i t y.toAdd)) (φ.1 (v + middlePart i t y.toAdd)), by
        have hh : Continuous fun v : Fin t → k => v + middlePart i t y.toAdd := continuous_id.add continuous_const
        have hl : IsLocallyConstant fun v : Fin t → k => φ.1 (v + middlePart i t y.toAdd) := φ.2.1.comp_continuous hh
        have hc : HasCompactSupport fun v : Fin t → k => φ.1 (v + middlePart i t y.toAdd) :=
          φ.2.2.comp_homeomorph (Homeomorph.addRight (middlePart i t y.toAdd))
        exact ⟨hl.comp _, hc.comp_left (map_zero _)⟩⟩
      map_add' := fun a b => by
        apply Subtype.ext
        funext v
        exact map_add _ _ _
      map_smul' := fun c a => by
        apply Subtype.ext
        funext v
        exact map_smul _ _ _ }
  map_one' := by
    ext φ v
    show ρ₀ (Multiplicative.ofAdd (topP i t 0)) (φ.1 (v + middlePart i t 0)) = φ.1 v
    have h1 : Multiplicative.ofAdd (topP (k := k) i t 0) = 1 := rfl
    have h2 : middlePart (k := k) i t 0 = 0 := rfl
    rw [h1, h2, map_one, add_zero]
    rfl
  map_mul' a b := by
    ext φ v
    show ρ₀ (Multiplicative.ofAdd (topP i t (a.toAdd + b.toAdd))) (φ.1 (v + middlePart i t (a.toAdd + b.toAdd))) =
      ρ₀ (Multiplicative.ofAdd (topP i t a.toAdd)) (ρ₀ (Multiplicative.ofAdd (topP i t b.toAdd)) (φ.1 (v + middlePart i t a.toAdd + middlePart i t b.toAdd)))
    have h1 : Multiplicative.ofAdd (topP i t (a.toAdd + b.toAdd)) =
        Multiplicative.ofAdd (topP i t a.toAdd) * Multiplicative.ofAdd (topP i t b.toAdd) := rfl
    rw [h1, map_mul, middlePart_add, add_assoc]
    rfl

theorem fibAct_apply {i : ℕ} (t : ℕ) (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z)
    (y : Multiplicative (Fin (i + t) → k)) (φ : fibM (Fin t → k) Z) (v : Fin t → k) :
    (fibAct t ρ₀ y φ).1 v = ρ₀ (Multiplicative.ofAdd (topP i t y.toAdd)) (φ.1 (v + middlePart i t y.toAdd)) := rfl

end Act

section Field

variable {k : Type} [Field k]

def uMh (k : Type) [Field k] (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n where
  toFun y := uM k n y.toAdd
  map_one' := uM_zero k n
  map_mul' a b := uM_add k n a.toAdd b.toAdd

def mulH {n : ℕ} (κ : GL (Fin n) k) : Multiplicative (Fin n → k) →* Multiplicative (Fin n → k) where
  toFun y := Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec y.toAdd)
  map_one' := by
    show Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec 0) = 1
    rw [Matrix.mulVec_zero]
    rfl
  map_mul' a b := by
    show Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec (a.toAdd + b.toAdd)) = _
    rw [Matrix.mulVec_add]
    rfl

def topRep {i : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k i) V)
    (W : Type) [AddCommGroup W] [Module ℂ W] :
    Representation ℂ (Multiplicative (Fin i → k)) (V ⊗[ℂ] W) where
  toFun x := LinearMap.rTensor W (τ (uM k i x.toAdd))
  map_one' := by
    show LinearMap.rTensor W (τ (uM k i 0)) = 1
    rw [uM_zero, map_one]
    exact LinearMap.rTensor_id _ _
  map_mul' a b := by
    show LinearMap.rTensor W (τ (uM k i (a.toAdd + b.toAdd))) = _
    rw [uM_add, map_mul]
    exact LinearMap.rTensor_mul _ _ _

end Field

section Lat

variable {k : Type} [Field k] [ValuativeRel k]

def Lc (n : ℕ) (c : k) : Subgroup (Multiplicative (Fin n → k)) where
  carrier := {y | ∀ j, c * y.toAdd j ∈ 𝒪[k]}
  mul_mem' := by
    intro a b ha hb j
    have : c * (a * b).toAdd j = c * a.toAdd j + c * b.toAdd j := mul_add _ _ _
    rw [this]
    exact add_mem (ha j) (hb j)
  one_mem' := by
    intro j
    have : c * (1 : Multiplicative (Fin n → k)).toAdd j = 0 := mul_zero _
    rw [this]
    exact zero_mem _
  inv_mem' := by
    intro a ha j
    have : c * (a⁻¹).toAdd j = - (c * a.toAdd j) := by
      show c * (- a.toAdd j) = _
      ring
    rw [this]
    exact neg_mem (ha j)

theorem mem_Lc {n : ℕ} {c : k} {y : Multiplicative (Fin n → k)} : y ∈ Lc n c ↔ ∀ j, c * y.toAdd j ∈ 𝒪[k] := Iff.rfl

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_Lc (n : ℕ) (c : k) : IsOpen (Lc n c : Set (Multiplicative (Fin n → k))) := by
  have hset : (Lc n c : Set (Multiplicative (Fin n → k))) =
      ⋂ j, (fun y : Multiplicative (Fin n → k) => c * y.toAdd j) ⁻¹' (𝒪[k] : Set k) := by
    ext y
    simp only [SetLike.mem_coe, mem_Lc, Set.mem_iInter, Set.mem_preimage]
  rw [hset]
  have hO : IsOpen (𝒪[k] : Set k) := by exact Valuation.isOpen_integer
  exact isOpen_iInter_of_finite fun j =>
    hO.preimage (continuous_const.mul ((continuous_apply j).comp continuous_toAdd))

theorem isCompact_Lc (n : ℕ) {c : k} (hc : c ≠ 0) : IsCompact (Lc n c : Set (Multiplicative (Fin n → k))) := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin n => {x : k | valuation k x ≤ 1}) :=
    isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hf : Continuous fun x : Fin n → k => Multiplicative.ofAdd (c⁻¹ • x) :=
    continuous_ofAdd.comp (continuous_const_smul _)
  convert hK.image hf using 1
  ext y
  constructor
  · intro hy
    refine ⟨c • y.toAdd, fun j _ => ?_, ?_⟩
    · have h := mem_Lc.1 hy j
      rw [Valuation.mem_integer_iff] at h
      simpa using h
    · simp [smul_smul, hc]
  · rintro ⟨x, hx, rfl⟩
    refine mem_Lc.2 fun j => ?_
    rw [Valuation.mem_integer_iff]
    simpa [smul_smul, hc] using hx j trivial

end Lat

section Coset

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]

def cosetSet (t : ℕ) (c : k) (a : Fin t → k) : Set (Fin t → k) :=
  {v | Multiplicative.ofAdd (v - a) ∈ Lc t c}

theorem isClopen_cosetSet (t : ℕ) (c : k) (a : Fin t → k) : IsClopen (cosetSet t c a) := by
  have hcont : Continuous fun v : Fin t → k => Multiplicative.ofAdd (v - a) :=
    continuous_ofAdd.comp (continuous_id.sub continuous_const)
  have h1 : IsOpen (Lc t c : Set (Multiplicative (Fin t → k))) := isOpen_Lc t c
  exact ⟨(Subgroup.isClosed_of_isOpen _ h1).preimage hcont, h1.preimage hcont⟩

theorem isCompact_cosetSet (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) : IsCompact (cosetSet t c a) := by
  have h := (isCompact_Lc t hc).image (f := fun y : Multiplicative (Fin t → k) => y.toAdd + a)
    ((continuous_toAdd).add continuous_const)
  convert h using 1
  ext v
  constructor
  · intro hv
    exact ⟨Multiplicative.ofAdd (v - a), hv, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    show Multiplicative.ofAdd (y.toAdd + a - a) ∈ Lc t c
    simpa using hy

def cosetFn (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) (z : Z) : fibM (Fin t → k) Z :=
  ⟨(cosetSet t c a).indicator fun _ => z, by
      classical
      rw [IsLocallyConstant.iff_exists_open]
      intro x
      by_cases hx : x ∈ cosetSet t c a
      · exact ⟨_, (isClopen_cosetSet t c a).2, hx, fun y hy => by
          rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
      · exact ⟨_, (isClopen_cosetSet t c a).1.isOpen_compl, hx, fun y hy => by
          rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩,
    by
      haveI : T2Space k := inferInstance
      exact HasCompactSupport.intro (isCompact_cosetSet t hc a) fun x hx => Set.indicator_of_notMem hx _⟩

end Coset

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

end
