import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaOpenMirabolic

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Grp

section Alg

variable {k : Type} [Field k]

theorem mirProj_eq_one_of_mem {n : ℕ} (u : Mir k n) (hu : u ∈ MirUin k n) : mirabolicProjection k n u = 1 := by
  obtain ⟨v, hv⟩ := (Subgroup.mem_subgroupOf.1 hu : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  apply Units.ext
  ext a b
  show ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = _
  rw [← hv]
  simp [unip, colMat, one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one' {n : ℕ} (u : Mir k n) (hu : mirabolicProjection k n u = 1) : u ∈ MirUin k n := by
  have hb : ∀ a b : Fin n, ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = if a = b then 1 else 0 := by
    intro a b
    have := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) a b) hu
    exact (this : ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = _).trans (by simp [one_apply])
  have hl := (mem_Mir_iff k (u : GL (Fin (n + 1)) k)).1 u.2
  refine Subgroup.mem_subgroupOf.2 ⟨Multiplicative.ofAdd fun a => ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.last n), ?_⟩
  apply Units.ext
  ext a b
  have hlb := congrFun hl b
  induction a using Fin.lastCases with
  | last =>
    rw [hlb]
    induction b using Fin.lastCases <;> simp [unip, colMat, one_apply, eLast, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  | cast a =>
    induction b using Fin.lastCases with
    | last => simp [unip, colMat, one_apply, Fin.castSucc_ne_last]
    | cast b =>
      rw [hb]
      simp [unip, colMat, one_apply, Fin.castSucc_ne_last]

theorem mirUin_normal (n : ℕ) : (MirUin k n).Normal := by
  refine ⟨fun u hu g => mem_of_mirProj_eq_one' _ ?_⟩
  rw [map_mul, map_mul, mirProj_eq_one_of_mem u hu, mul_one, map_inv, mul_inv_cancel]

theorem mirUin_comm {n : ℕ} {a b : Mir k n} (ha : a ∈ MirUin k n) (hb : b ∈ MirUin k n) : a * b = b * a := by
  obtain ⟨v, hv⟩ := (Subgroup.mem_subgroupOf.1 ha : ((a : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 hb : ((b : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  apply Subtype.ext
  show (a : GL (Fin (n + 1)) k) * (b : GL (Fin (n + 1)) k) = (b : GL (Fin (n + 1)) k) * (a : GL (Fin (n + 1)) k)
  rw [← hv, ← hw, ← map_mul, mul_comm, map_mul]

def prodSub {n : ℕ} (L₁ L₂ : Subgroup (Mir k n)) (h₁ : L₁ ≤ MirUin k n) (h₂ : L₂ ≤ MirUin k n) : Subgroup (Mir k n) where
  carrier := (L₁ : Set (Mir k n)) * (L₂ : Set (Mir k n))
  one_mem' := ⟨1, L₁.one_mem, 1, L₂.one_mem, one_mul 1⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    refine ⟨a * c, L₁.mul_mem ha hc, b * d, L₂.mul_mem hb hd, ?_⟩
    show a * c * (b * d) = a * b * (c * d)
    rw [mul_assoc a c, ← mul_assoc c b, mirUin_comm (h₁ hc) (h₂ hb)]
    simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, L₁.inv_mem ha, b⁻¹, L₂.inv_mem hb, ?_⟩
    show a⁻¹ * b⁻¹ = (a * b)⁻¹
    rw [_root_.mul_inv_rev]
    exact mirUin_comm (MirUin k n |>.inv_mem (h₁ ha)) (MirUin k n |>.inv_mem (h₂ hb))

theorem hpg_entry {i t : ℕ} (g : Mir k ((i + 1) + t + 1)) (hg : g ∈ HPG k (i + 1) (t + 1))
    (l : Fin ((i + 1) + t + 2)) (hl : i < l.val) (hl2 : l.val ≠ (i + 1) + t + 1) (c : Fin (i + 1)) :
    ((g : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) l
      (Fin.castLE (by omega) c) = 0 := by
  have hp : (g : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ GlobalTheory.SmGL.parab k (ePG (i + 1) (t + 1)) := hg
  have hlt := l.isLt
  have h0 := mem_parab_iff.1 hp true false (⟨l.val - (i + 1), by omega⟩ : Fin (t + 1)) (Fin.castSucc c : Fin (i + 1 + 1)) (by decide)
  have e1 : ePG (i + 1) (t + 1) ⟨true, (⟨l.val - (i + 1), by omega⟩ : Fin (t + 1))⟩ = l := by
    apply Fin.ext
    simp [ePG, two]
    omega
  have e2 : ePG (i + 1) (t + 1) ⟨false, (Fin.castSucc c : Fin (i + 1 + 1))⟩ = Fin.castLE (by omega) c := by
    apply Fin.ext
    simp [ePG, two]
  rw [e1, e2] at h0
  exact h0

theorem Cl_left {i t : ℕ} (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1)) (x : Mir k ((i + 1) + t + 1))
    (hx : x ∈ Cl k i t) : h * x ∈ Cl k i t := by
  intro c
  rw [_root_.mul_inv_rev]
  simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h1 : l.val ≤ i
  · have := hx ⟨l.val, by omega⟩
    have e : Fin.castLE (by omega) (⟨l.val, by omega⟩ : Fin (i + 1)) = l := Fin.ext rfl
    rw [e] at this
    rw [this, zero_mul]
  · by_cases h2 : l.val = (i + 1) + t + 1
    · have e : l = Fin.last _ := Fin.ext h2
      have hm := (mem_Mir_iff k ((h⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k)).1 (h⁻¹).2
      have hc := congrFun hm (Fin.castLE (by omega) c)
      rw [e, hc]
      have : Fin.castLE (by omega) c ≠ Fin.last ((i + 1) + t + 1) := by
        intro e'
        have := congrArg Fin.val e'
        simp at this
        omega
      simp [eLast, Pi.single_apply, this]
    · rw [hpg_entry _ ((HPG k (i + 1) (t + 1)).inv_mem hh) l (by omega) h2 c, mul_zero]

theorem Cl_right {i t : ℕ} (x : Mir k ((i + 1) + t + 1)) (hx : x ∈ Cl k i t) (u : Mir k ((i + 1) + t + 1))
    (hu : u ∈ MirUin k ((i + 1) + t + 1)) : x * u ∈ Cl k i t := by
  intro c
  obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 ((MirUin k ((i + 1) + t + 1)).inv_mem hu) :
    ((u⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) ∈ MirU k ((i + 1) + t + 1))
  rw [_root_.mul_inv_rev]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [← hw]
  have hv : ((unip k ((i + 1) + t + 1) w : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) = 1 + colMat k _ w.toAdd := rfl
  rw [hv, add_mul, one_mul, Matrix.add_apply, hx c, zero_add, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l = Fin.last _
  · have hm := (mem_Mir_iff k ((x⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k)).1 (x⁻¹).2
    have hc := congrFun hm (Fin.castLE (by omega) c)
    rw [hl, hc]
    have : Fin.castLE (by omega) c ≠ Fin.last ((i + 1) + t + 1) := by
      intro e'
      have := congrArg Fin.val e'
      simp at this
      omega
    simp [eLast, Pi.single_apply, this]
  · simp [colMat, hl]

end Alg

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mirChar_ker_open (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) :
    IsOpen ((mirChar k ψ n).ker : Set (MirUin k (n + 1))) := by
  have he : ((mirChar k ψ n).ker : Set (MirUin k (n + 1))) =
      (fun u : MirUin k (n + 1) => GlobalTheory.CompanionTheory.BZFun.lastCol k u (Fin.last n)) ⁻¹' {x : k | ψ x = 1} := by
    ext u
    obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 u.2 : ((u : Mir k (n + 1)) : GL (Fin (n + 2)) k) ∈ MirU k (n + 1))
    have hl : GlobalTheory.CompanionTheory.BZFun.lastCol k u (Fin.last n) = w.toAdd (Fin.last n) := by
      simp only [GlobalTheory.CompanionTheory.BZFun.lastCol, ← hw]
      exact unip_apply_castSucc_last k (n + 1) w _
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_setOf_eq, hl,
      mirChar_eq k ψ n u w hw.symm]
    constructor
    · intro h
      apply Circle.ext
      simpa using congrArg Units.val h
    · intro h
      rw [h, map_one]
  rw [he]
  exact (GlobalTheory.CompanionTheory.BZFun.isOpen_addChar_eq_one k ψ hψ).preimage
    ((continuous_apply _).comp (GlobalTheory.CompanionTheory.BZFun.continuous_lastCol k (n + 1)))

theorem isClosed_Cl (i t : ℕ) : IsClosed (Cl k i t) := by
  have hc : Continuous fun p : Mir k ((i + 1) + t + 1) =>
      (((p⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)
  have he : Cl k i t = ⋂ c : Fin (i + 1), {p : Mir k ((i + 1) + t + 1) |
      (((p⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
        (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castLE (by omega) c) = 0} := by
    ext p
    simp [Cl]
  rw [he]
  exact isClosed_iInter fun c => isClosed_eq (hc.matrix_elem _ _) continuous_const

end Top

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) (i t : ℕ),
  (MirUin k ((i + 1) + t + 1)).Normal ∧ IsOpen ((mirChar k ψ ((i + 1) + t)).ker : Set (MirUin k ((i + 1) + t + 1))) ∧
    IsClosed (Cl k i t) ∧ (∀ h ∈ HPG k (i + 1) (t + 1), ∀ x ∈ Cl k i t, h * x ∈ Cl k i t) ∧
    (∀ x ∈ Cl k i t, ∀ u ∈ MirUin k ((i + 1) + t + 1), x * u ∈ Cl k i t) ∧
    ∀ L₁ L₂ : Subgroup (Mir k ((i + 1) + t + 1)), L₁ ≤ MirUin k ((i + 1) + t + 1) → L₂ ≤ MirUin k ((i + 1) + t + 1) →
      IsCompact (L₁ : Set (Mir k ((i + 1) + t + 1))) → IsCompact (L₂ : Set (Mir k ((i + 1) + t + 1))) →
      ∃ L : Subgroup (Mir k ((i + 1) + t + 1)), L ≤ MirUin k ((i + 1) + t + 1) ∧ IsCompact (L : Set (Mir k ((i + 1) + t + 1))) ∧
        L₁ ≤ L ∧ L₂ ≤ L := by
  intro k _ _ _ _ ψ hψ i t
  refine ⟨mirUin_normal _, mirChar_ker_open ψ hψ _, isClosed_Cl i t, fun h hh x hx => Cl_left h hh x hx,
    fun x hx u hu => Cl_right x hx u hu, fun L₁ L₂ h₁ h₂ c₁ c₂ => ⟨prodSub L₁ L₂ h₁ h₂, ?_, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact (MirUin k _).mul_mem (h₁ ha) (h₂ hb)
  · exact (c₁.mul c₂ : IsCompact ((L₁ : Set (Mir k ((i + 1) + t + 1))) * (L₂ : Set (Mir k ((i + 1) + t + 1)))))
  · intro a ha
    exact ⟨a, ha, 1, L₂.one_mem, mul_one a⟩
  · intro b hb
    exact ⟨1, L₁.one_mem, b, hb, one_mul b⟩

end GlobalTheory.CompanionTheory.BZPhiPG.Grp

end
