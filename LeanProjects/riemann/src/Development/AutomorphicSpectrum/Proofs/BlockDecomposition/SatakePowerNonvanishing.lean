import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwasawaBruhatDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatWeightDecreasesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFactorizationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriIndexFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantConjugateUnipotentMemStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetRepsOfFactorizationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalZeroOfInjectivePowerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckePowerCosetFormulaStatement
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

theorem aOp_rightInv {G : Type} [Group G] (I : Subgroup G) (t : G) (R : Finset G) (hRI : ∀ r ∈ R, r ∈ I)
    (hR : ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) (φ : G → ℂ) (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g) :
    ∀ g, ∀ i ∈ I, aOp R t φ (g * i) = aOp R t φ g := by
  classical
  intro g i hi
  have key : ∀ r, r ∈ R → ∃ r', r' ∈ R ∧ t⁻¹ * (r'⁻¹ * (i * r)) * t ∈ I := fun r hr => by
    obtain ⟨r', h, -⟩ := hR (i * r) (I.mul_mem hi (hRI r hr))
    exact ⟨r', h⟩
  choose! f hfR hf using key
  have he : ∀ r ∈ R, φ (g * i * r * t) = φ (g * f r * t) := fun r hr => by
    have e : g * i * r * t = (g * f r * t) * (t⁻¹ * ((f r)⁻¹ * (i * r)) * t) := by group
    rw [e, hφ _ _ (hf r hr)]
  have hinj : Set.InjOn f (R : Set G) := fun r₁ h₁ r₂ h₂ e => by
    have h3 : t⁻¹ * (r₁⁻¹ * r₂) * t ∈ I := by
      have := I.mul_mem (I.inv_mem (hf r₁ h₁)) (hf r₂ h₂)
      rw [← e] at this
      have e2 : (t⁻¹ * ((f r₁)⁻¹ * (i * r₁)) * t)⁻¹ * (t⁻¹ * ((f r₁)⁻¹ * (i * r₂)) * t) = t⁻¹ * (r₁⁻¹ * r₂) * t := by
        group
      rwa [e2] at this
    exact (hR r₂ (hRI r₂ h₂)).unique ⟨h₁, h3⟩ ⟨h₂, by simp [I.one_mem]⟩
  have himg : R.image f = R :=
    Finset.eq_of_subset_of_card_le (fun x hx => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hx
      exact hfR r hr) (by rw [Finset.card_image_of_injOn hinj])
  unfold aOp
  rw [Finset.sum_congr rfl he]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image hinj]

theorem abs_main {G : Type} [Group G] (K I : Subgroup G) (hIK : I ≤ K) (hfin : Finite (K ⧸ I.subgroupOf K)) (t : G)
    (R : Finset G) (h1R : (1 : G) ∈ R) (hRI : ∀ r ∈ R, r ∈ I) (hRt : ∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ K)
    (hR : ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I)
    (Wsp : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ Wsp]
    (hWA : ∀ φ ∈ Wsp, aOp R t φ ∈ Wsp) (hinj : ∀ φ ∈ Wsp, aOp R t φ = 0 → φ = 0)
    (φ₀ : G → ℂ) (hφ₀ : φ₀ ∈ Wsp) (hK : ∀ g, ∀ k ∈ K, φ₀ (g * k) = φ₀ g) (h1 : φ₀ 1 = 1)
    (lam : ℕ → ℂ) (hlam : ∀ j, hAct K (dosetInd ℂ K (t ^ j)) φ₀ 1 = lam j) (j₀ : ℕ) : ∃ j ≥ j₀, lam j ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  haveI := Fintype.ofFinite (K ⧸ I.subgroupOf K)
  let A : Wsp →ₗ[ℂ] Wsp :=
    { toFun := fun φ => ⟨aOp R t φ, hWA φ φ.2⟩
      map_add' := fun a b => Subtype.ext (by
        funext g; simp [aOp, Finset.sum_add_distrib])
      map_smul' := fun c a => Subtype.ext (by
        funext g; simp [aOp, Finset.mul_sum]) }
  let l : Wsp →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∑ c : K ⧸ I.subgroupOf K, (φ : G → ℂ) ((c.out : K) : G)
      map_add' := fun a b => by simp [Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [Finset.mul_sum] }
  let v : Wsp := ⟨φ₀, hφ₀⟩
  have hAj : ∀ j, (((A ^ j) v : Wsp) : G → ℂ) = (aOp R t)^[j] φ₀ := fun j => by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply']
      show aOp R t (((A ^ j) v : Wsp) : G → ℂ) = _
      rw [ih]
  have hAinj : Function.Injective A := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact Subtype.ext (hinj a a.2 (congrArg Subtype.val ha))
  have hl0 : l v = 0 := by
    refine GlobalTheory.T.functional_zero_of_injective_power _ A hAinj l v j₀ fun j hj => ?_
    obtain ⟨m, -, hm⟩ := GlobalTheory.T.hecke_power_coset_formula G K I hIK hfin t R h1R hRI hRt hR j
    have := hm φ₀ hK
    rw [hlam, hcon j hj, mul_zero, finsum_eq_sum_of_fintype] at this
    show ∑ c : K ⧸ I.subgroupOf K, (((A ^ j) v : Wsp) : G → ℂ) ((c.out : K) : G) = 0
    rw [hAj, this]
  have hl1 : l v = (Fintype.card (K ⧸ I.subgroupOf K) : ℂ) := by
    show ∑ c : K ⧸ I.subgroupOf K, φ₀ ((c.out : K) : G) = _
    have : ∀ c : K ⧸ I.subgroupOf K, φ₀ ((c.out : K) : G) = 1 := fun c => by
      have := hK 1 _ (c.out : K).2
      rwa [one_mul, h1] at this
    simp [this]
  rw [hl1] at hl0
  exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 hl0)

section U

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem isPermW_unique {w w' : GU σ n} {π : Equiv.Perm (Fin n)} (h : IsPermW w π) (h' : IsPermW w' π) : w = w' :=
  Subtype.ext (Units.ext (Matrix.ext fun a c => by rw [h a c, h' a c]))

theorem chiDeltaU_congr {m : ℕ} (q : ℕ) (α : Fin m → ℂ) {b b' : GU σ n}
    (h : ∀ a : Fin n, ordL (((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a) =
      ordL (((b' : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a)) : chiDeltaU q α b = chiDeltaU q α b' := by
  unfold chiDeltaU
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [h]
  · rfl

theorem chiDeltaU_ne_zero {m : ℕ} {q : ℕ} (hq : (q : ℂ) ≠ 0) {α : Fin m → ℂ} (hα : ∀ i, α i ≠ 0) (b : GU σ n) :
    chiDeltaU q α b ≠ 0 := by
  unfold chiDeltaU
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  split_ifs with hi
  · exact mul_ne_zero (zpow_ne_zero _ (hα i)) (zpow_ne_zero _ hq)
  · exact one_ne_zero

theorem conj_diag {t w : GU σ n} {π : Equiv.Perm (Fin n)} (ht : IsDiagM (t : GL (Fin n) L)) (hw : IsPermW w π) :
    IsBorelU (w * t * w⁻¹) ∧ ∀ a : Fin n, (((w * t * w⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a =
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (π a) (π a) := by
  set s := w * t * w⁻¹ with hs
  have hsw : (((s * w : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      (((w * t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [hs]; congr 2; group
  have key : ∀ a e : Fin n, ((s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a e =
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (π a) (π e) := fun a e => by
    have := congrFun (congrFun hsw a) (π e)
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply] at this
    simpa [hw _ _] using this
  refine ⟨fun i j hij => ?_, fun a => key a a⟩
  rw [key]
  exact ht _ _ fun h => (ne_of_gt hij) (π.injective h)

theorem aOp_inj (q : ℕ) (hq : (q : ℂ) ≠ 0) {m : ℕ} (α : Fin m → ℂ) (hα : ∀ i, α i ≠ 0)
    (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x)
    (t : GU σ n) (htD : IsDiagM (t : GL (Fin n) L)) (htS : IsStrictDom (t : GL (Fin n) L))
    (R : Finset (GU σ n)) (h1R : (1 : GU σ n) ∈ R) (hRI : ∀ r ∈ R, r ∈ IwU σ n)
    (φ : GU σ n → ℂ) (hB : ∀ b g, IsBorelU b → φ (b * g) = chiDeltaU q α b * φ g)
    (hI : ∀ g, ∀ i ∈ IwU σ n, φ (g * i) = φ g) (h0 : aOp R t φ = 0) : φ = 0 := by
  classical
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hdec : ∀ b w i : GU σ n, IsBorelU b → i ∈ IwU σ n → φ (b * w * i) = chiDeltaU q α b * φ w :=
    fun b w i hb hi => by rw [hI _ _ hi, hB _ _ hb]
  set S : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter fun π => ∃ w : GU σ n, IsPermW w π ∧ φ w ≠ 0 with hS
  have hSne : S.Nonempty := by
    obtain ⟨b, w, i, π, hb, hw, hi, e⟩ := GlobalTheory.T.unitary_iwasawa_bruhat_decomposition L σ n hσ hσv g
    refine ⟨π, Finset.mem_filter.2 ⟨Finset.mem_univ _, w, hw, fun h => hg ?_⟩⟩
    rw [e, hdec _ _ _ hb hi, h, mul_zero]
  obtain ⟨π, hπS, hmin⟩ := Finset.exists_min_image S (permWt t) hSne
  obtain ⟨w, hw, hφw⟩ := (Finset.mem_filter.1 hπS).2
  obtain ⟨hsB, hsd⟩ := conj_diag (w := w) htD hw
  set x := chiDeltaU q α (w * t * w⁻¹) * φ w with hx
  have hx0 : x ≠ 0 := mul_ne_zero (chiDeltaU_ne_zero hq hα _) hφw
  have hterm : ∀ r ∈ R, φ (w * r * t) = if φ (w * r * t) = x then x else 0 := fun r hr => by
    split_ifs with h
    · exact h
    obtain ⟨b, w', i, π', hb, hw', hi, e⟩ := GlobalTheory.T.unitary_iwasawa_bruhat_decomposition L σ n hσ hσv (w * r * t)
    rcases GlobalTheory.T.bruhat_weight_decreases L σ n t w w' b r i π π' htD htS hw hw' hb (hRI r hr) hi e with hlt | ⟨rfl, hord⟩
    · have hz : φ w' = 0 := by
        by_contra hz
        exact absurd (hmin π' (Finset.mem_filter.2 ⟨Finset.mem_univ _, w', hw', hz⟩)) (not_le.2 hlt)
      rw [e, hdec _ _ _ hb hi, hz, mul_zero]
    · exfalso
      apply h
      rw [e, hdec _ _ _ hb hi, isPermW_unique hw' hw, hx,
        chiDeltaU_congr q α (b' := w * t * w⁻¹) fun a => by rw [hord, hsd]]
  have h1 : φ (w * 1 * t) = x := by
    have e : w * 1 * t = (w * t * w⁻¹) * w := by group
    rw [e, hB _ _ hsB]
  have hsum := congrFun h0 w
  simp only [aOp, Pi.zero_apply] at hsum
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : (R.filter fun r => φ (w * r * t) = x).card ≠ 0 :=
    Finset.card_ne_zero_of_mem (Finset.mem_filter.2 ⟨h1R, h1⟩)
  exact (mul_ne_zero (Nat.cast_ne_zero.2 hc) hx0) hsum

def iwFix (σ : L →+* L) (n : ℕ) (q : ℕ) (α : Fin (n / 2) → ℂˣ) : Submodule ℂ (GU σ n → ℂ) where
  carrier := {φ | φ ∈ psSpaceU σ q α ∧ ∀ g, ∀ i ∈ IwU σ n, φ (g * i) = φ g}
  add_mem' h h' := ⟨add_mem h.1 h'.1, fun g i hi => by simp [h.2 g i hi, h'.2 g i hi]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ _ => rfl⟩
  smul_mem' c _ h := ⟨Submodule.smul_mem _ c h.1, fun g i hi => by simp [h.2 g i hi]⟩

theorem finiteDimensional_iwFix (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (q : ℕ)
    (α : Fin (n / 2) → ℂˣ) : FiniteDimensional ℂ (iwFix σ n q α) := by
  classical
  let wOf : Equiv.Perm (Fin n) → GU σ n := fun π => if h : ∃ w : GU σ n, IsPermW w π then h.choose else 1
  have hwOf : ∀ (w : GU σ n) π, IsPermW w π → wOf π = w := fun w π hw => by
    have h : ∃ w : GU σ n, IsPermW w π := ⟨w, hw⟩
    simp only [wOf, dif_pos h]
    exact isPermW_unique h.choose_spec hw
  let F : iwFix σ n q α →ₗ[ℂ] (Equiv.Perm (Fin n) → ℂ) :=
    { toFun := fun φ π => (φ : GU σ n → ℂ) (wOf π)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective F ?_
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨b, w, i, π, hb, hw, hi, rfl⟩ := GlobalTheory.T.unitary_iwasawa_bruhat_decomposition L σ n hσ hσv g
  have h1 : (φ : GU σ n → ℂ) w = 0 := by
    have := congrFun hφ π
    rwa [show F φ π = (φ : GU σ n → ℂ) (wOf π) from rfl, hwOf w π hw] at this
  have h2 := φ.2.2 (b * w) i hi
  have h3 := φ.2.1 b w hb
  show (φ : GU σ n → ℂ) (b * w * i) = 0
  rw [h2, h3, h1, mul_zero]

end U

theorem satPowNonvan : PositivityTheory.SphericalProduct.SatPowNonvan := by
  intro L _ _ _ ϖ σ q n hU α t htD htS j₀
  have hσ := hU.1
  have hσv := hU.2.1
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hα : ∀ i, (fun i => (α i : ℂ)) i ≠ 0 := fun i => (α i).ne_zero
  obtain ⟨hKI, hYI⟩ := GlobalTheory.T.unitary_iwahori_index_finite L ϖ σ q n hU
  obtain ⟨R, h1R, hRP, hR⟩ := GlobalTheory.T.coset_reps_of_factorization (GU σ n) (IwU σ n) t (fun u => u ∈ IwU σ n ∧ IsUnipU u)
    ⟨one_mem _, isBorelU_one, fun i => by simp⟩ (hYI t) (fun i hi => by
      obtain ⟨u, hu, hu', y, hy, hy', e⟩ := GlobalTheory.T.unitary_iwahori_factorization L σ n hσ hσv t htD htS i hi
      exact ⟨u, hu, ⟨hu, hu'⟩, y, hy, hy', e⟩)
  have hRI : ∀ r ∈ R, r ∈ IwU σ n := fun r hr => (hRP r hr).1
  have hRt : ∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ KU σ n := fun r hr k =>
    GlobalTheory.T.dominant_conjugate_unipotent_mem L σ n t r htD htS (hRP r hr).1 (hRP r hr).2.2 k
  obtain ⟨φ₀, hsph, h1, -⟩ := Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega) (fun i => (α i : ℂ)) hα
  have hIK := GlobalTheory.CompanionTheory.KUFactsU.iwU_le_KU σ n
  have hK : ∀ g, ∀ k ∈ KU σ n, φ₀ (g * k) = φ₀ g := fun g k hk => by
    simpa [chiDeltaU_one] using hsph 1 g k isBorelU_one hk
  have hφ₀ : φ₀ ∈ iwFix σ n q α :=
    ⟨fun b g hb => by simpa using hsph b g 1 hb (one_mem _), fun g i hi => hK g i (hIK hi)⟩
  haveI := finiteDimensional_iwFix hσ hσv q α
  exact abs_main (KU σ n) (IwU σ n) hIK hKI t R h1R hRI hRt hR (iwFix σ n q α)
    (fun φ hφ => ⟨fun b g hb => by
        show aOp R t φ (b * g) = _ * aOp R t φ g
        simp only [aOp, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [mul_assoc b, mul_assoc b, hφ.1 b _ hb], aOp_rightInv _ t R hRI hR φ hφ.2⟩)
    (fun φ hφ h0 => aOp_inj q hq _ hα hσ hσv t htD htS R h1R hRI φ hφ.1 hφ.2 h0)
    φ₀ hφ₀ hK h1 (fun j => SatU ϖ q (dosetInd ℂ (KU σ n) (t ^ j)) (fun i => (α i : ℂ)))
    (fun j => by
      have e := Final.SatakeInert L ϖ σ q n (n / 2) hU (by omega) (by omega) _ hα
        (dosetInd ℂ (KU σ n) (t ^ j)) (Final.DosetIndMem _ (KU σ n) ℂ _) φ₀ hsph
      have := congrFun e 1
      simpa [h1] using this) j₀

end GlobalTheory.CompanionTheory.SatPow

end
