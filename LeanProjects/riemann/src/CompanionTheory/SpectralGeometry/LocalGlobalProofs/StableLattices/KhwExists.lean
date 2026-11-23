import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import CompanionTheory.HarishChandraModules.NonemptyRepresentations.TypeExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.KHighestExists

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P CompanionTheory.D.Inhab CompanionTheory.D.DSIC

theorem gl_exists (n : ℕ) (ν : Fin n → ℤ) (hν : Antitone ν) :
    ∃ (U : Type) (_ : NormedAddCommGroup U) (_ : InnerProductSpace ℂ U) (_ : FiniteDimensional ℂ U)
      (E : Fin n → Fin n → Module.End ℂ U) (u : U),
      GlRel E ∧ (∀ a b x y, ⟪E a b x, y⟫_ℂ = ⟪x, E b a y⟫_ℂ) ∧ u ≠ 0 ∧ IsHW E (fun a => (ν a : ℂ)) u := by
  obtain ⟨R⟩ := HWRep.nonempty_of_antitone ν hν
  obtain ⟨hz, h1⟩ := base_vector_exists n 0
  have hT : 0 < Tz n 0 (bvec (wI n 0 (Fin.last n))) := by rw [h1]; exact one_pos
  obtain ⟨B, hB⟩ := Qx8.frame_exists hz hT
  have hπ := TypeExists.πR_isRepW R hz hT hB
  exact ⟨EuclideanSpace ℂ R.I, inferInstance, inferInstance, inferInstance, EB (TypeExists.πR R B) B,
    WithLp.toLp 2 R.v0, (frame_general_linear _ n 0 n _ _ B hπ hB).1,
    Formalism.FourierDecayAlt.P5.Kfp.EB_adj hπ.1 hπ.2 (TypeExists.πR_unitary R hz hT hB) hB,
    fun h => R.v0_ne (congrArg WithLp.ofLp h), TypeExists.isHW_πR R hz hT hB⟩

theorem reorder (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℤ) (hγ : ∀ c d, c < d → ε c = ε d → γ d ≤ γ c) :
    ∃ (σ : Fin n ≃ Fin n) (N : ℤ), (∀ c d, c < d → ε c = ε d → σ.symm c < σ.symm d) ∧
      Antitone fun i => γ (σ i) + if ε (σ i) then N else 0 := by
  let f : Fin n → ℕ := fun c => if ε c then (c : ℕ) else n + c
  have hm : Monotone (f ∘ Tuple.sort f) := Tuple.monotone_sort f
  have hb : ∀ c, |γ c| ≤ ∑ d, |γ d| := fun c =>
    Finset.single_le_sum (f := fun d => |γ d|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c)
  refine ⟨Tuple.sort f, 2 * ∑ d, |γ d|, fun c d hcd he => ?_, fun i j hij => ?_⟩
  · by_contra h
    have := hm (not_lt.1 h)
    simp only [Function.comp, Equiv.apply_symm_apply, f, he] at this
    have h' : (c : ℕ) < d := hcd
    split_ifs at this <;> omega
  · have h := hm hij
    simp only [Function.comp, f] at h
    show γ (Tuple.sort f j) + _ ≤ γ (Tuple.sort f i) + _
    generalize Tuple.sort f i = a at *
    generalize Tuple.sort f j = b at *
    have ha := abs_le.1 (hb a)
    have hb' := abs_le.1 (hb b)
    have key : ε a = ε b → (a : ℕ) ≤ b → γ b ≤ γ a := fun he hab => by
      rcases (show a ≤ b from hab).lt_or_eq with h | h
      · exact hγ a b h he
      · rw [h]
    have := b.2
    cases h1 : ε a <;> cases h2 : ε b <;> simp only [h1, h2] at h key ⊢ <;> simp at h ⊢
    · exact key trivial h
    · omega
    · linarith [ha.1, hb'.2]
    · exact key trivial h

theorem khwExists : CompanionTheory.D.DSIC.KHWExists := by
  intro n ε γ hγ
  obtain ⟨σ, N, hσ, hν⟩ := reorder n ε γ hγ
  obtain ⟨U, _, _, _, E, u, hgl, hadj, hu, hw⟩ := gl_exists n _ hν
  let s : Fin n → ℤ := fun c => if ε c then N else 0
  refine ⟨U, inferInstance, inferInstance, inferInstance,
    fun c d => E (σ.symm c) (σ.symm d) - (if c = d then (s c : ℂ) else 0) • 1, u, ?_, ?_, hu, ?_, ?_⟩
  · intro a b c d hab _
    have h := hgl (σ.symm a) (σ.symm b) (σ.symm c) (σ.symm d)
    simp only [EmbeddingLike.apply_eq_iff_eq] at h
    have e : ∀ (X Y : Module.End ℂ U) (p q : ℂ),
        (X - p • 1) * (Y - q • 1) - (Y - q • 1) * (X - p • 1) = X * Y - Y * X := by
      intro X Y p q
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_smul]
      module
    show (_ - _ • 1) * (_ - _ • 1) - (_ - _ • 1) * (_ - _ • 1) = _
    rw [e, h]
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · subst h1; subst h2
      have : s d = s b := by simp only [s, hab]
      simp [this]
    · simp [h1, h2, Ne.symm h2]
    · simp [h1, h2, Ne.symm h1]
    · simp [h1, h2]
  · intro a b _ x y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, hadj]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  · intro a
    have h := hw.1 (σ.symm a)
    simp only [Equiv.apply_symm_apply] at h
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, h, if_true, s, ← sub_smul]
    congr 1
    push_cast
    ring
  · intro a b hab he
    simp [hw.2 _ _ (hσ a b hab he), hab.ne]

end GlobalTheory.CompanionTheory.KHighestExists
