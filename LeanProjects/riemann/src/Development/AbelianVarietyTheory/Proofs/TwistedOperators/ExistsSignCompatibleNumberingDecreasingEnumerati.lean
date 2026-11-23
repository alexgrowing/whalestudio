import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section
namespace GlobalTheory.ArchRec.EnumBlocks

theorem signed_eq {p q : ℕ} {l₁ l₂ : List ℚ} (c : ℚ) (h₁ : l₁.length = p) (h₂ : l₂.length = q) :
    signed l₁ l₂ c = Finset.univ.image fun a : Ix p q => (ofBlocks l₁ l₂ a + c, a.isLeft) := by
  subst h₁ h₂
  ext ⟨x, b⟩
  simp only [signed, Finset.mem_union, List.mem_toFinset, List.mem_map, Prod.mk.injEq, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨y, hy, rfl, rfl⟩ | ⟨y, hy, rfl, rfl⟩)
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hy
      exact ⟨.inl i, by simp [ofBlocks], rfl⟩
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hy
      exact ⟨.inr i, by simp [ofBlocks], rfl⟩
  · rintro ⟨a | a, rfl, rfl⟩
    · exact Or.inl ⟨_, by simp [ofBlocks], rfl, by simp⟩
    · exact Or.inr ⟨_, by simp [ofBlocks], rfl, by simp⟩

theorem sameBlock_iff {p q : ℕ} (a b : Ix p q) : sameBlock a b ↔ b.isLeft = a.isLeft := by
  rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock]

theorem card_filter_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (P : β → Prop) (Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ b, P (e b) ↔ Q b) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card :=
  (Finset.card_equiv e (fun b => by simp [h])).symm

theorem lowK_numbered {n p q : ℕ} {ε : Fin n → Bool} {lamM : Fin n → ℝ} (e : Ix p q ≃ Fin n)
    (hε : ∀ a, ε (e a) = a.isLeft) (R : Ix p q → Ix p q → Prop) (hR : ∀ a b, e a < e b ↔ R a b) (a : Ix p q)
    [DecidableRel R] :
    Formalism.QuantumDeterminants.lowK ε lamM (e a) = lamM (e a) +
      ((((Finset.univ.filter fun b => ¬ sameBlock a b ∧ R a b).card : ℝ) -
        ((Finset.univ.filter fun b => ¬ sameBlock a b ∧ R b a).card : ℝ)) / 2 -
       (((Finset.univ.filter fun b => sameBlock a b ∧ R a b).card : ℝ) -
        ((Finset.univ.filter fun b => sameBlock a b ∧ R b a).card : ℝ)) / 2) := by
  classical
  have hs : ∀ b, ε (e b) = ε (e a) ↔ sameBlock a b := fun b => by rw [hε, hε, sameBlock_iff]
  have hn : ∀ b, ε (e b) ≠ ε (e a) ↔ ¬ sameBlock a b := fun b => not_congr (hs b)
  have n1 := card_filter_equiv e (fun j => e a < j ∧ ε j ≠ ε (e a)) (fun b => ¬ sameBlock a b ∧ R a b)
    fun b => by rw [hR, hn]; exact and_comm
  have n2 := card_filter_equiv e (fun j => j < e a ∧ ε j ≠ ε (e a)) (fun b => ¬ sameBlock a b ∧ R b a)
    fun b => by rw [hR, hn]; exact and_comm
  have c1 := card_filter_equiv e (fun j => e a < j ∧ ε j = ε (e a)) (fun b => sameBlock a b ∧ R a b)
    fun b => by rw [hR, hs]; exact and_comm
  have c2 := card_filter_equiv e (fun j => j < e a ∧ ε j = ε (e a)) (fun b => sameBlock a b ∧ R b a)
    fun b => by rw [hR, hs]; exact and_comm
  simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Formalism.REAL.rhoN, Formalism.REAL.rhoC]
  rw [n1, n2, c1, c2]
  ring

theorem core {n p q : ℕ} {L : Ix p q → ℚ} (hL : Function.Injective L) {c s : ℚ} (hs : s = 1 ∨ s = -1)
    {ε : Fin n → Bool} {lamM : Fin n → ℝ}
    (hE : IsEnum (Finset.univ.image fun a : Ix p q => (s * (L a + c), a.isLeft)) lamM ε) :
    ∃ e : Ix p q ≃ Fin n, IsOrd ε lamM L c (s : ℝ) e := by
  classical
  obtain ⟨hanti, r, hr, hS⟩ := hE
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hf : Function.Injective fun a : Ix p q => (s * (L a + c), a.isLeft) := fun a b h =>
    hL (add_right_cancel (mul_left_cancel₀ hs0 (congrArg Prod.fst h)))
  have hg : Function.Injective fun i => (r i, ε i) := fun i j h =>
    hanti.injective (by rw [hr, hr, show r i = r j from congrArg Prod.fst h])
  have ex : ∀ a : Ix p q, ∃ i, (r i, ε i) = (s * (L a + c), a.isLeft) := fun a => by
    have : (s * (L a + c), a.isLeft) ∈ Finset.univ.image fun i => (r i, ε i) := by
      rw [← hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 this
    exact ⟨i, hi⟩
  choose f hfi using ex
  have finj : Function.Injective f := fun a b h => hf (by
    show (s * (L a + c), a.isLeft) = (s * (L b + c), b.isLeft)
    rw [← hfi a, ← hfi b, h])
  have fsurj : Function.Surjective f := fun i => by
    have : (r i, ε i) ∈ Finset.univ.image fun a : Ix p q => (s * (L a + c), a.isLeft) := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 this
    exact ⟨a, hg ((hfi a).trans ha)⟩
  let e : Ix p q ≃ Fin n := Equiv.ofBijective f ⟨finj, fsurj⟩
  have he : ∀ a, (r (e a), ε (e a)) = (s * (L a + c), a.isLeft) := hfi
  have hε : ∀ a, ε (e a) = a.isLeft := fun a => congrArg Prod.snd (he a)
  have hr' : ∀ a, r (e a) = s * (L a + c) := fun a => congrArg Prod.fst (he a)
  have hlam : ∀ a, lamM (e a) = (s : ℝ) * ((L a + c : ℚ) : ℝ) := fun a => by
    rw [hr, hr']; push_cast; ring
  have hlt : ∀ a b, e a < e b ↔ s * L b < s * L a := fun a b => by
    have h0 : e a < e b ↔ lamM (e b) < lamM (e a) := ⟨fun h => hanti h, fun h => by
      by_contra hn
      exact absurd (hanti.antitone (not_lt.1 hn)) (not_le.2 h)⟩
    rw [h0, hlam, hlam]
    rw [← Rat.cast_mul, ← Rat.cast_mul, Rat.cast_lt, mul_add, mul_add, add_lt_add_iff_right]
  refine ⟨e, hε, hlam, fun a => ?_⟩
  rcases hs with rfl | rfl
  · rw [lowK_numbered e hε (fun a b => L b < L a) (fun a b => by simpa using hlt a b) a, hlam]
    simp only [blattner, rhoNC]
    push_cast
    ring
  · rw [lowK_numbered e hε (fun a b => L a < L b) (fun a b => by simpa using hlt a b) a, hlam]
    simp only [blattner, rhoNC]
    push_cast
    ring

theorem parOf_eq {p q : ℕ} {l₁ l₂ : List ℚ} (br cj : Bool) (c : ℚ) (h₁ : l₁.length = p) (h₂ : l₂.length = q) :
    parOf br cj l₁ l₂ c = Finset.univ.image fun a : Ix p q =>
      ((if br = cj then 1 else -1 : ℚ) * (ofBlocks l₁ l₂ a + c), a.isLeft) := by
  classical
  unfold parOf dualPar
  rw [signed_eq c h₁ h₂]
  split_ifs
  · simp
  · rw [Finset.image_image]
    refine Finset.image_congr fun a _ => ?_
    simp

theorem exists_isOrd (n p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ) (br cj : Bool) (ε : Fin n → Bool) (lamM : Fin n → ℝ)
    (h₁ : l₁.length = p) (h₂ : l₂.length = q) (hP : IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ))
    (hE : IsEnum (parOf br cj l₁ l₂ c) lamM ε) :
    ∃ e : Ix p q ≃ Fin n, IsOrd ε lamM (ofBlocks l₁ l₂) c (sg br cj) e := by
  rw [parOf_eq br cj c h₁ h₂] at hE
  have hs : (if br = cj then 1 else -1 : ℚ) = 1 ∨ (if br = cj then 1 else -1 : ℚ) = -1 := by
    split_ifs <;> simp
  have := core hP.1 hs hE
  have hc : (((if br = cj then 1 else -1 : ℚ)) : ℝ) = sg br cj := by
    unfold sg; split_ifs <;> simp
  rwa [hc] at this

end GlobalTheory.ArchRec.EnumBlocks
end
