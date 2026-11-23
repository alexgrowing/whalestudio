import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviEmbMulSingle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCovBySubmodule
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.ProdSupport

theorem piTensor_mulSingle {α : Type} [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (a : α) (g : Γ a) (c : ℂ) (h : ∀ v, ρ a g v = c • v) (y : ⨂[ℂ] a, X a) :
    piTensor ρ (Pi.mulSingle a g) y = c • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, smul_comm, piTensor_tprod]
    congr 1
    have h1 : (fun b => ρ b (Pi.mulSingle (M := Γ) a g b) (x b)) = Function.update x a (c • x a) := by
      funext b
      by_cases hb : b = a
      · subst hb
        simp [h]
      · simp [Pi.mulSingle_eq_of_ne hb, Function.update_of_ne hb]
    rw [h1, MultilinearMap.map_update_smul, Function.update_eq_self]

theorem nontrivial_piTensor {α : Type} [Fintype α] (X : α → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (h : ∀ a, Nontrivial (X a)) : Nontrivial (⨂[ℂ] a, X a) := by
  have h1 : ∀ a, ∃ (x : X a) (l : Module.Dual ℂ (X a)), l x = 1 := fun a => by
    obtain ⟨x, hx⟩ := exists_ne (0 : X a)
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hx
    exact ⟨x, l, hl⟩
  choose x l hl using h1
  refine ⟨PiTensorProduct.tprod ℂ x, 0, fun h0 => ?_⟩
  have := congrArg
    (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap l)) h0
  simp [hl] at this

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem det_scalar_one {d : ℕ} (hd : d = 1) (z : kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin d) z) = z := by
  ext; simp [GeneralLinearGroup.scalar, hd]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem eq_scalar_det {d : ℕ} (hd : d = 1) (g : GL (Fin d) k) :
    g = GeneralLinearGroup.scalar (Fin d) (GeneralLinearGroup.det g) := by
  subst hd
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp [GeneralLinearGroup.scalar, GeneralLinearGroup.val_det_apply]

theorem hasCentralChar_multiProd {α n : Type} [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n]
    {c : α → Type} [∀ a, Fintype (c a)] [∀ a, DecidableEq (c a)] (e : (Σ a, c a) ≃ n)
    {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (c a) k) (X a)) (a : α) (ha : ∀ b, b ≠ a → IsEmpty (c b))
    {ω : kˣ →* ℂˣ} (hω : HasCentralChar (σ a) ω) : HasCentralChar (multiProd e σ) ω := by
  intro z f
  have h1 : leviEmb k e (Pi.mulSingle a (GeneralLinearGroup.scalar (c a) z)) =
      GeneralLinearGroup.scalar n z := by
    ext i j
    obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b', y'⟩, rfl⟩ := e.surjective j
    obtain rfl : b = a := by_contra fun h => (ha b h).elim y
    obtain rfl : b' = b := by_contra fun h => (ha b' h).elim y'
    rw [leviEmb_apply_same]
    simp [GeneralLinearGroup.scalar, diagonal_apply]
  have h2 : modExp c a = 0 := by
    unfold modExp
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
    · intro b hb
      have := ha b (Finset.mem_filter.1 hb).2.ne
      simp
    · intro b hb
      have := ha b (Finset.mem_filter.1 hb).2.ne'
      simp
  have h3 : deltaHalf k c (Pi.mulSingle a (GeneralLinearGroup.scalar (c a) z)) = 1 := by
    rw [deltaHalf_apply]
    refine Finset.prod_eq_one fun b _ => ?_
    by_cases hb : b = a
    · subst hb
      simp [h2]
    · rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one]
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  have h4 := parInd_law e (piTensor σ) f
    ⟨_, leviEmb_mem_parab k e (Pi.mulSingle a (GeneralLinearGroup.scalar (c a) z))⟩ x
  rw [leviProj_leviEmb, h3, piTensor_mulSingle σ a _ _ (hω z)] at h4
  have hc : x * GeneralLinearGroup.scalar n z = GeneralLinearGroup.scalar n z * x := by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  show f.1.1 (x * GeneralLinearGroup.scalar n z) = (ω z : ℂ) • f.1.1 x
  rw [hc, ← h1]
  simpa using h4

theorem exists_inSupport_of_multiProd : GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α]
    (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (n : Type) [Fintype n] [DecidableEq n]
    (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (χ : kˣ →* ℂˣ),
    (∀ a, IsSmooth (ρ a)) → (∀ a, (ρ a).IsIrreducible) → InSupport (multiProd e ρ) χ →
      ∃ a, InSupport (ρ a) χ := by
  intro hG k _ _ _ _ α _ _ m _ _ n _ _ e X _ _ ρ χ hs hi
  rintro ⟨r, d, e', a, ha, Y, _, _, τ, hτ, hsub, hact⟩
  obtain ⟨b, f, g, s, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2 e e' hs
    (fun i => hasFiniteLength_of_isIrreducible (hi i)) hτ hsub
  have hsum : ∑ i, b.1 i a = 1 := by simpa [ha] using b.2.2 a
  obtain ⟨i, -, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => b.1 j a) (Finset.mem_univ i)
  have hi1 : b.1 i a = 1 := by simp only at hsplit; omega
  have hz : ∀ j, j ≠ i → IsEmpty (Fin (b.1 j a)) := fun j hj => by
    have h0 : ∑ j ∈ Finset.univ.erase i, b.1 j a = 0 := by simp only at hsplit; omega
    rw [Finset.sum_eq_zero_iff.1 h0 j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)]
    infer_instance
  obtain ⟨ω, -, hω⟩ := LocGL.exists_smooth_hasCentralChar (s i a).smooth (s i a).irr
  have hcen := hasCentralChar_multiProd (g a) (fun j => (s j a).ρ) i hz hω
  obtain rfl : χ = ω := by
    have := Model.nontrivial_of_isIrreducible hτ
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    refine MonoidHom.ext fun z => ?_
    have h1 := Model.scalar_of_isSubquotient hcol
      (piTensor_mulSingle (fun j => multiProd (g j) fun i => (s i j).ρ) a _ _ (hcen z)) y
    rw [hact, det_scalar_one ha] at h1
    exact Units.ext (smul_left_injective ℂ hy h1)
  obtain ⟨Z, _, _, υ, hυ, hυs⟩ := IrrSubquot.exists_irreducible_subquotient _ _
    (piTensor fun j => (s i j).ρ)
    (nontrivial_piTensor _ fun j => Model.nontrivial_of_isIrreducible (s i j).irr)
  refine ⟨i, r, b.1 i, f i, a, hi1, Z, _, _, υ, hυ, hυs.trans (hrow i), fun h y => ?_⟩
  refine Model.scalar_of_isSubquotient hυs (piTensor_mulSingle (fun j => (s i j).ρ) a h _ fun v => ?_) y
  conv_lhs => rw [eq_scalar_det hi1 h]
  exact hω _ v

end GlobalTheory.ProdSupport
