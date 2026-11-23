import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHighestWeightIrreducibleUnitaryRepU
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarishChandraTypeDualWeylModuleFockNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasModelOfAntitone
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsGoodFamily

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.UnitaryContainsType

def permMat {n : ℕ} (s : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if s i = j then 1 else 0

theorem permMat_mul_diag_mul {n : ℕ} (s : Equiv.Perm (Fin n)) (d : Fin n → ℂ) :
    permMat s * Matrix.diagonal d * permMat s.symm = Matrix.diagonal (d ∘ s) := by
  ext i j
  simp only [permMat, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, one_mul]
  rw [Finset.sum_eq_single (s i)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem permMat_mul {n : ℕ} (s : Equiv.Perm (Fin n)) : permMat s * permMat s.symm = 1 := by
  ext i j
  simp only [permMat, Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (s i)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem star_permMat {n : ℕ} (s : Equiv.Perm (Fin n)) : star (permMat s) = permMat s.symm := by
  ext i j
  simp only [permMat, Matrix.star_apply, Matrix.of_apply]
  by_cases h : s j = i
  · rw [if_pos h, if_pos (by rw [← h]; simp)]; simp
  · rw [if_neg h, if_neg (by rintro rfl; simp at h)]; simp

theorem permMat_mem {n : ℕ} (s : Equiv.Perm (Fin n)) : permMat s ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_permMat, permMat_mul]

open Formalism.MainNotions.S in

theorem weight_int_dom {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hπ : IsURepOn (UJset (allPos n)) π) {Λ : Fin n → ℝ}
    (hK : IsKTypeOf (allPos n) π Λ ⊤) :
    (∀ a, ∃ z : ℤ, Λ a = z) ∧ ∀ a b : Fin n, a.val + 1 = b.val → Λ b ≤ Λ a := by
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hπ
  rw [GlobalTheory.CompactDS.ujset_eq] at hmul hiso
  obtain ⟨-, -, -, ⟨v, -, hv0, hvw⟩, hdom⟩ := hK
  rw [GlobalTheory.CompactDS.kset_eq] at hvw hdom
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · have hd : Matrix.diagonal (fun c => Complex.exp
        ((((Pi.single a (2 * Real.pi) : Fin n → ℝ) c : ℝ) : ℂ) * Complex.I)) = 1 := by
      rw [← Matrix.diagonal_one]
      congr 1
      funext c
      by_cases hc : c = a
      · subst hc
        simp only [Pi.single_eq_same]
        push_cast
        exact Complex.exp_two_pi_mul_I
      · simp [hc]
    have h := hvw (Pi.single a (2 * Real.pi)) (by rw [hd]; exact one_mem _)
    rw [hd, h1] at h
    simp only [ContinuousLinearMap.one_apply] at h
    have hs : (∑ c, Λ c * (Pi.single a (2 * Real.pi) : Fin n → ℝ) c) = Λ a * (2 * Real.pi) := by
      simp [Pi.single_apply]
    rw [hs] at h
    set z := Complex.exp (((Λ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) with hz
    have he : z = 1 := by
      by_contra hne
      apply hv0
      have : (z - 1) • v = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 he
    refine ⟨k, ?_⟩
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h3 : ((Λ a : ℝ) : ℂ) = ((k : ℝ) : ℂ) := by
      apply mul_right_cancel₀ h2
      push_cast at hk ⊢
      linear_combination hk
    exact_mod_cast h3
  · have hab' : a ≠ b := fun e => by rw [e] at hab; omega
    set s := Equiv.swap a b with hs
    have hPm := permMat_mem s
    have hss : s.symm = s := Equiv.symm_swap a b
    have hPP : permMat s * permMat s = 1 := by have := permMat_mul s; rwa [hss] at this
    have hw : IsWtOn (Matrix.unitaryGroup (Fin n) ℂ : Set _) π (Λ ∘ s) (π (permMat s) v) := by
      intro θ hθ
      have e0 := permMat_mul_diag_mul s (fun c => Complex.exp ((θ c : ℂ) * Complex.I))
      rw [hss] at e0
      have hD' : Matrix.diagonal (fun c => Complex.exp ((((θ ∘ s) c : ℝ) : ℂ) * Complex.I)) ∈
          (Matrix.unitaryGroup (Fin n) ℂ : Set _) := by
        have : Matrix.diagonal (fun c => Complex.exp ((((θ ∘ s) c : ℝ) : ℂ) * Complex.I)) =
            permMat s * Matrix.diagonal (fun c => Complex.exp ((θ c : ℂ) * Complex.I)) * permMat s := by
          rw [e0]; rfl
        rw [this]
        exact mul_mem (mul_mem hPm hθ) hPm
      have e1 : Matrix.diagonal (fun c => Complex.exp ((θ c : ℂ) * Complex.I)) * permMat s =
          permMat s * Matrix.diagonal (fun c => Complex.exp ((((θ ∘ s) c : ℝ) : ℂ) * Complex.I)) := by
        have : Matrix.diagonal (fun c => Complex.exp ((((θ ∘ s) c : ℝ) : ℂ) * Complex.I)) =
            permMat s * Matrix.diagonal (fun c => Complex.exp ((θ c : ℂ) * Complex.I)) * permMat s := by
          rw [e0]; rfl
        rw [this, ← mul_assoc, ← mul_assoc, hPP, one_mul]
      rw [← ContinuousLinearMap.comp_apply, ← hmul _ hθ _ hPm, e1, hmul _ hPm _ hD',
        ContinuousLinearMap.comp_apply, hvw (θ ∘ s) hD', map_smul]
      congr 4
      rw [← Equiv.sum_comp s (fun c => (Λ ∘ s) c * θ c)]
      simp [hs]
    have hne : π (permMat s) v ≠ 0 := by
      intro h
      have := hiso _ hPm v
      rw [h, norm_zero] at this
      exact hv0 (norm_eq_zero.1 this.symm)
    have hc := hdom (Λ ∘ s) (π (permMat s) v) trivial hne hw
    have hle := (GlobalTheory.UnitaryHighestWeightUnique.height_le hc).1
    have hsum : ∑ x : Fin n, ((x : ℕ) : ℝ) * (Λ ∘ s) x = ∑ x : Fin n, ((s x : ℕ) : ℝ) * Λ x := by
      rw [← Equiv.sum_comp s (fun x => ((s x : ℕ) : ℝ) * Λ x)]
      simp [hs]
    have hb : ((b : ℕ) : ℝ) = (a : ℕ) + 1 := by exact_mod_cast hab.symm
    have hdiff : ∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x - ∑ x : Fin n, ((s x : ℕ) : ℝ) * Λ x = Λ b - Λ a := by
      rw [← Finset.sum_sub_distrib, Fintype.sum_eq_add a b hab']
      · simp only [hs, Equiv.swap_apply_left, Equiv.swap_apply_right, hb]
        ring
      · rintro x ⟨hxa, hxb⟩
        simp [hs, Equiv.swap_apply_of_ne_of_ne hxa hxb]
    linarith

def restr {G V : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (S : Submodule ℂ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) : Representation ℂ G S where
  toFun g := (ρ g).restrict (fun v hv => hS g v hv)
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

@[simp] theorem restr_apply {G V : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (S : Submodule ℂ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (g : G) (v : S) :
    ((restr ρ S hS g v : S) : V) = ρ g v := rfl

theorem exists_minimal {G V : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Nontrivial V] (ρ : Representation ℂ G V) :
    ∃ S : Submodule ℂ V, S ≠ ⊥ ∧ (∀ g, ∀ v ∈ S, ρ g v ∈ S) ∧
      ∀ S' : Submodule ℂ V, S' ≤ S → (∀ g, ∀ v ∈ S', ρ g v ∈ S') → S' = ⊥ ∨ S' = S := by
  classical
  let P : Submodule ℂ V → Prop := fun S => S ≠ ⊥ ∧ ∀ g, ∀ v ∈ S, ρ g v ∈ S
  have hex : ∃ k, ∃ S, P S ∧ Module.finrank ℂ S = k :=
    ⟨_, ⊤, ⟨top_ne_bot, fun _ _ _ => trivial⟩, rfl⟩
  obtain ⟨S, hS, e⟩ := Nat.find_spec hex
  refine ⟨S, hS.1, hS.2, fun S' hle hst => ?_⟩
  by_cases h0 : S' = ⊥
  · exact Or.inl h0
  right
  exact Submodule.eq_of_le_of_finrank_le hle (e ▸ Nat.find_min' hex ⟨S', ⟨h0, hst⟩, rfl⟩)

theorem exists_intertwining_of_minimal {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (hc : ∀ (l : Module.Dual ℂ V) (v : V), Continuous fun u => l (ρ u v))
    (S : Submodule ℂ V) (hS0 : S ≠ ⊥) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S)
    (hmin : ∀ S' : Submodule ℂ V, S' ≤ S → (∀ g, ∀ v ∈ S', ρ g v ∈ S') → S' = ⊥ ∨ S' = S) :
    ∃ (lam : DomWeight n) (f : (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) lam).IntertwiningMap ρ),
      f ≠ 0 := by
  classical
  set σ := restr ρ S hS with hσ
  have hcS : ∀ (l : Module.Dual ℂ S) (v : S), Continuous fun u => l (σ u v) := by
    intro l v
    obtain ⟨L, hL⟩ := LinearMap.exists_extend l
    have e : (fun u => l (σ u v)) = fun u => L (ρ u v) := by
      funext u
      rw [← hL]
      rfl
    rw [e]
    exact hc L v
  obtain ⟨c, hcinv⟩ := GlobalTheory.exists_invariant_core_of_continuous_coeff σ hcS
  letI : NormedAddCommGroup S := c.toNormedAddCommGroup
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore c.toCore
  haveI : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS0
  have hcont : ∀ v : S, Continuous fun u : Matrix.unitaryGroup (Fin n) ℂ => σ u v := by
    intro v
    let b := Module.finBasis ℂ S
    have e : (fun u : Matrix.unitaryGroup (Fin n) ℂ => σ u v) = fun u => ∑ i, b.coord i (σ u v) • b i := by
      funext u
      exact (b.sum_repr (σ u v)).symm
    rw [e]
    exact continuous_finset_sum _ fun i _ => (hcS (b.coord i) v).smul continuous_const
  let π : Matrix (Fin n) (Fin n) ℂ → (S →L[ℂ] S) := fun g =>
    if hg : g ∈ Matrix.unitaryGroup (Fin n) ℂ then LinearMap.toContinuousLinearMap (σ ⟨g, hg⟩) else 0
  have hπu : ∀ g (hg : g ∈ Matrix.unitaryGroup (Fin n) ℂ) (v : S), π g v = σ ⟨g, hg⟩ v := by
    intro g hg v
    simp [π, hg]
  have hπ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n)) π := by
    rw [GlobalTheory.CompactDS.ujset_eq]
    refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
    · ext1 v
      rw [hπu 1 (one_mem _)]
      show (σ 1) v = v
      rw [map_one]
      rfl
    · ext1 v
      rw [ContinuousLinearMap.comp_apply, hπu _ (mul_mem ha hb), hπu _ ha, hπu _ hb]
      show σ (⟨a, ha⟩ * ⟨b, hb⟩) v = _
      rw [map_mul]
      rfl
    · rw [hπu g hg, norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ)]
      congr 2
      exact hcinv _ v v
    · rw [continuousOn_iff_continuous_restrict]
      exact (hcont v).congr fun u => (hπu u.1 u.2 v).symm
  have hirr : ∀ S' : Submodule ℂ S, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos n), ∀ v ∈ S', π g v ∈ S') →
      S' = ⊥ ∨ S' = ⊤ := by
    intro S' hS'
    have hS'' : ∀ (u : Matrix.unitaryGroup (Fin n) ℂ), ∀ v ∈ S', σ u v ∈ S' := by
      intro u v hv
      have hu : (u : Matrix (Fin n) (Fin n) ℂ) ∈ PI.UpqRep.UJset (PI.UpqRep.allPos n) := by
        have e : PI.UpqRep.UJset (PI.UpqRep.allPos n) = Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n) := rfl
        rw [e, GlobalTheory.CompactDS.ujset_eq]
        exact u.2
      have := hS' _ hu v hv
      rwa [hπu _ u.2] at this
    let M := S'.map S.subtype
    have hM : ∀ g, ∀ v ∈ M, ρ g v ∈ M := by
      rintro g _ ⟨y, hy, rfl⟩
      exact ⟨σ g y, hS'' g y hy, rfl⟩
    rcases hmin M (Submodule.map_subtype_le S S') hM with h | h
    · left
      exact Submodule.map_injective_of_injective S.injective_subtype (h.trans (Submodule.map_bot _).symm)
    · right
      exact Submodule.map_injective_of_injective S.injective_subtype (h.trans (Submodule.map_subtype_top S).symm)
  obtain ⟨u, hu⟩ := GlobalTheory.UnitaryHighestWeight.exists_isHCTypeU n S π hπ hirr
  have hu' : Formalism.MainNotions.S.IsHCTypeU n u π := hu
  obtain ⟨hint, hdom⟩ := weight_int_dom hu'.2.2.1 hu'.2.2.2

  choose w hw using hint
  have hadj : ∀ a b : Fin n, a.val + 1 = b.val → w b ≤ w a := fun a b h => by
    have := hdom a b h
    rw [hw, hw] at this
    exact_mod_cast this
  have hanti : Antitone w := by
    intro i j hij
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Fin.le_def.1 hij)
    induction d generalizing j with
    | zero =>
      have : j = i := Fin.ext (by omega)
      rw [this]
    | succ d ih =>
      have hj' : i.val + d < n := by omega
      have h1 := ih (j := ⟨i.val + d, hj'⟩) (Fin.le_def.2 (by simp)) rfl
      have h2 := hadj ⟨i.val + d, hj'⟩ j (by simp only; omega)
      exact h2.trans h1
  let lam : DomWeight n := ⟨w, hanti⟩
  have hul : u = fun i => ((lam.w i : ℤ) : ℝ) + ((rhoVec n i : ℚ) : ℝ) := by
    funext i
    have h := hw i
    rw [show Formalism.MainNotions.S.allPos n = fun _ => true from rfl, GlobalTheory.DefiniteCheck.lowK_const] at h
    simp only [lam, rhoVec]
    push_cast
    linarith
  obtain ⟨H, _, _, π₂, e, hπ₂, he, hmem, hint2⟩ := GlobalTheory.NablaType.exists_isHCTypeU_nablaSq n lam
  rw [← hul] at hπ₂
  obtain ⟨A, hA⟩ := GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU n u S H π π₂ hu' hπ₂
  let G0 : S →ₗ[ℂ] nablaSq ℂ n lam :=
    LinearMap.codRestrict (nablaSq ℂ n lam) (e ∘ₗ A.toLinearMap) (fun x => hmem (A x))
  have hG0 : ∀ (g : Matrix.unitaryGroup (Fin n) ℂ) (x : S),
      G0 (σ g x) = GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) lam g (G0 x) := by
    intro g x
    apply Subtype.ext
    show e (A (σ g x)) = sqAct ℂ n lam (GlobalTheory.Branching.unitaryIncl n g) (e (A x))
    rw [← hint2 (GlobalTheory.Branching.unitaryIncl n g) g.2 (A x), GlobalTheory.Branching.unitaryIncl_coe, ← hA _ g.2 x, hπu _ g.2 x]
  have hinj : Function.Injective G0 := by
    intro x y hxy
    have : e (A x) = e (A y) := congrArg Subtype.val hxy
    exact A.injective (he this)
  let G : σ.IntertwiningMap (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) lam) :=
    G0.intertwiningMap_of_isIntertwiningMap _ _ hG0
  haveI := GlobalTheory.Branching.isIrreducible_smallRep_unitary n lam
  have hsurj : Function.Surjective G := by
    rcases Representation.IsIrreducible.surjective_or_eq_zero G with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (0 : S)
      apply hx
      apply hinj
      rw [map_zero]
      exact congrArg (fun T => T x) (congrArg DFunLike.coe h)
  let F : S ≃ₗ[ℂ] nablaSq ℂ n lam := LinearEquiv.ofBijective G0 ⟨hinj, hsurj⟩
  have hF : ∀ (g : Matrix.unitaryGroup (Fin n) ℂ) (y : nablaSq ℂ n lam),
      F.symm (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) lam g y) = σ g (F.symm y) := by
    intro g y
    apply F.injective
    rw [LinearEquiv.apply_symm_apply]
    show _ = G0 (σ g (F.symm y))
    rw [hG0]
    congr 1
    exact (F.apply_symm_apply y).symm
  let f0 : nablaSq ℂ n lam →ₗ[ℂ] V := S.subtype ∘ₗ F.symm.toLinearMap
  refine ⟨lam, f0.intertwiningMap_of_isIntertwiningMap _ _ fun g y => ?_, ?_⟩
  · show ((F.symm (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) lam g y) : S) : V) = ρ g (F.symm y : V)
    rw [hF]
    rfl
  · intro h0
    obtain ⟨y, hy⟩ := exists_ne (0 : nablaSq ℂ n lam)
    apply hy
    have h1 : f0 y = 0 := congrArg (fun T => T y) (congrArg DFunLike.coe h0)
    have h2 : F.symm y = 0 := by
      apply Subtype.ext
      exact h1
    simpa using congrArg F h2

theorem exists_smallRep_intertwining : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Nontrivial V] (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V),
    (∀ (l : Module.Dual ℂ V) (v : V), Continuous fun u => l (ρ u v)) →
    ∃ (lam : DomWeight n) (f : (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) lam).IntertwiningMap ρ),
      f ≠ 0 := by
  intro n V _ _ _ _ ρ hc
  obtain ⟨S, hS0, hS, hmin⟩ := exists_minimal ρ
  exact exists_intertwining_of_minimal ρ hc S hS0 hS hmin

end GlobalTheory.UnitaryContainsType
