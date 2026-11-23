import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.VacuumTranslateSumSelfDualLatticeFixedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualLatticeOfIntegralGramMatrixStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGramClassRepsSelfDualLatticeGroupStatement
open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem sum_charSum_eq_card_filter {B ι M : Type} [AddCommGroup B] [Fintype B] [AddCommGroup M] [Module ℂ M]
    (Y : Finset ι) (x : ι) (hx : x ∈ Y) (χ : B → ι → ℂ)
    (hmul : ∀ b b', ∀ y ∈ Y, χ (b + b') y = χ b y * χ b' y) (hne : ∀ b, ∀ y ∈ Y, χ b y ≠ 0) (v : ι → M)
    [DecidablePred (fun y => ∀ b, χ b y = χ b x)] :
    ∑ b, (χ b x)⁻¹ • ∑ y ∈ Y, χ b y • v y =
      (Fintype.card B : ℂ) • ∑ y ∈ Y.filter (fun y => ∀ b, χ b y = χ b x), v y := by
  have h0 : ∀ y ∈ Y, χ 0 y = 1 := by
    intro y hy
    have e := hmul 0 0 y hy
    rw [add_zero] at e
    exact mul_left_cancel₀ (hne 0 y hy) (by rw [mul_one]; exact e.symm)
  have key : ∀ y ∈ Y, ∑ b, (χ b x)⁻¹ * χ b y =
      if (∀ b, χ b y = χ b x) then (Fintype.card B : ℂ) else 0 := by
    intro y hy
    split_ifs with hP
    · simp [hP, inv_mul_cancel₀ (hne _ x hx)]
    · let φ : AddChar B ℂ :=
        { toFun := fun b => (χ b x)⁻¹ * χ b y
          map_zero_eq_one' := by simp [h0 x hx, h0 y hy]
          map_add_eq_mul' := by
            intro b b'
            show (χ (b + b') x)⁻¹ * χ (b + b') y = ((χ b x)⁻¹ * χ b y) * ((χ b' x)⁻¹ * χ b' y)
            rw [hmul b b' x hx, hmul b b' y hy, mul_inv]
            ring }
      have hφ : φ ≠ 1 := by
        intro h1
        apply hP
        intro b
        have e : φ b = 1 := by rw [h1, AddChar.one_apply]
        exact ((inv_mul_eq_one₀ (hne b x hx)).mp e).symm
      show ∑ b, φ b = 0
      exact AddChar.sum_eq_zero_of_ne_one hφ
  calc ∑ b, (χ b x)⁻¹ • ∑ y ∈ Y, χ b y • v y = ∑ y ∈ Y, (∑ b, (χ b x)⁻¹ * χ b y) • v y := by
        simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]; exact Finset.sum_comm
    _ = ∑ y ∈ Y, (if (∀ b, χ b y = χ b x) then (Fintype.card B : ℂ) else 0) • v y :=
        Finset.sum_congr rfl (fun y hy => by rw [key y hy])
    _ = _ := by
        rw [Finset.smul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        split_ifs <;> simp

end GlobalTheory.Hk3.HoweG

namespace GlobalTheory.Hk3.HoweG

open GlobalTheory.Hk3

theorem gramClass_sum_mem_span_selfDual_vac : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ C : Finset (Matrix (Fin n') (Fin n) L), ∃ c : Matrix (Fin n') (Fin n) L → ℂ, x ∈ C ∧
      (∀ y ∈ C, c y ≠ 0 ∧ GlobalTheory.Hk3.HoweG.HomA σ JS JT x y ∧ GlobalTheory.Hk3.HoweG.GramEq σ JT x y) ∧
      (∀ y ∈ C, ∀ y' ∈ C, y ≠ y' → y - y' ∉ GlobalTheory.Hk3.HoweDuality.intMat L n' n) ∧
      ∑ y ∈ C, c y • ρ y s ∈ Submodule.span ℂ {w : M | ∃ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
        ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w} := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac x hx
  classical
  have hP' := hP
  obtain ⟨hU, hodd, hSint, hTint, hS, hT, hδ, hpsi_int, hpsi_ne, -, hρ, -, -, -⟩ := hP'
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := GlobalTheory.T.selfDual_lattice_of_integral_gramMatrix L ϖ σ q n n' JS JT hU hodd hSint hTint hS hT x hx
  obtain ⟨Y, hxY, hYA, hYd, B, _, _, b0, l, hb0, hl, hcov, hmul, hsep⟩ :=
    GlobalTheory.T.exists_gramClass_reps_selfDualLattice_group L ϖ σ q δ n n' JS JT ψ hU hodd hSint hTint hS hT hδ hpsi_int hpsi_ne x hx a ⟨ha1, ha2, ha3, ha4⟩
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hshift : ∀ y u, u ∈ HoweDuality.intMat L n' n →
      ρ (y + u) s = ψ (-((locH σ δ JS JT y u + σ (locH σ δ JS JT y u)) / 2)) • ρ y s := by
    intro y u hu
    have h1 : ρ y s = ψ ((locH σ δ JS JT y u + σ (locH σ δ JS JT y u)) / 2) • ρ (y + u) s := by
      have := congrArg (fun f => f s) (hρ y u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [hvac u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  set χ : B → Matrix (Fin n') (Fin n) L → ℂ :=
    fun b y => ψ (-((locH σ δ JS JT y (l b y) + σ (locH σ δ JS JT y (l b y))) / 2)) with hχ
  have hne : ∀ b, ∀ y ∈ Y, χ b y ≠ 0 := by
    intro b y _ h0
    have := hψinv (-((locH σ δ JS JT y (l b y) + σ (locH σ δ JS JT y (l b y))) / 2))
    rw [show ψ (-((locH σ δ JS JT y (l b y) + σ (locH σ δ JS JT y (l b y))) / 2)) = χ b y from rfl, h0,
      zero_mul] at this
    exact zero_ne_one this
  set Spn := Submodule.span ℂ {w : M | ∃ a : GL (Fin n) L, SelfDual σ JS a ∧
        ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
          ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w} with hSpn

  have hvacb : ∀ b, ∑ y ∈ Y, χ b y • ρ y s ∈ Spn := by
    intro b
    have hinj : Set.InjOn (fun y => y + l b y) Y := by
      intro y hy y' hy' e
      refine hYd y hy y' hy' ?_
      have e' : y - y' = l b y' - l b y := by
        have := congrArg (fun z => z - l b y - y') e
        simp only at this
        rw [show y + l b y - l b y - y' = y - y' by abel, show y' + l b y' - l b y - y' = l b y' - l b y by abel] at this
        exact this
      rw [e']
      exact (HoweDuality.intMat L n' n).sub_mem (hl b y' hy').1 (hl b y hy).1
    have hsum : ∑ y ∈ Y, χ b y • ρ y s = ∑ z ∈ Y.image (fun y => y + l b y), ρ z s := by
      rw [Finset.sum_image hinj]
      exact Finset.sum_congr rfl (fun y hy => (hshift y (l b y) (hl b y hy).1).symm)
    rw [hsum]
    refine Submodule.subset_span ⟨b0 b, hb0 b, ?_⟩
    refine GlobalTheory.T.vacuumTranslateSum_selfDualLattice_fixed L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac (b0 b) (hb0 b) _ ?_ ?_ ?_
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact (hl b y hy).2
    · intro z hz z' hz' hzz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hz'
      have : y = y' := by
        refine hYd y hy y' hy' ?_
        have e : y - y' = (y + l b y - (y' + l b y')) + (l b y' - l b y) := by abel
        rw [e]
        exact (HoweDuality.intMat L n' n).add_mem hzz
          ((HoweDuality.intMat L n' n).sub_mem (hl b y' hy').1 (hl b y hy).1)
      rw [this]
    · intro u hu
      obtain ⟨y, hy, hm⟩ := hcov b u hu
      exact ⟨y + l b y, Finset.mem_image_of_mem _ hy, hm⟩
  have hF := sum_charSum_eq_card_filter Y x hxY χ hmul hne (fun y => ρ y s)
  have hcard : (Fintype.card B : ℂ) ≠ 0 := by
    have : 0 < Fintype.card B := Fintype.card_pos
    exact_mod_cast this.ne'
  refine ⟨Y.filter (fun y => ∀ b, χ b y = χ b x), fun _ => 1, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hxY, fun _ => rfl⟩
  · intro y hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
    exact ⟨one_ne_zero, hYA y hy1, (hsep y hy1).mpr hy2⟩
  · intro y hy y' hy' hne' hm
    exact hne' (hYd y (Finset.mem_filter.mp hy).1 y' (Finset.mem_filter.mp hy').1 hm)
  · simp only [one_smul]
    have e : ∑ y ∈ Y.filter (fun y => ∀ b, χ b y = χ b x), ρ y s =
        (Fintype.card B : ℂ)⁻¹ • ∑ b, (χ b x)⁻¹ • ∑ y ∈ Y, χ b y • ρ y s := by
      rw [hF, smul_smul, inv_mul_cancel₀ hcard, one_smul]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hvacb b))

end GlobalTheory.Hk3.HoweG
