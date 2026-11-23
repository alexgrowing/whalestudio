import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosure
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependenceAlgebra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section Hsymm

def flagVar (N n k : ℕ) : MvPolynomial (Fin (N + n)) ℤ :=
  if h : k < N then X (Fin.castAdd n ⟨k, h⟩) else 0

def flagHsymm (N n : ℕ) : ℕ → ℕ → MvPolynomial (Fin (N + n)) ℤ
  | 0, c => if c = 0 then 1 else 0
  | k + 1, c => ∑ j ∈ Finset.range (c + 1), flagHsymm N n k (c - j) * flagVar N n k ^ j

theorem flagHsymm_zero_right (N n k : ℕ) : flagHsymm N n k 0 = 1 := by
  induction k with
  | zero => simp [flagHsymm]
  | succ k ih => simp [flagHsymm, ih]

theorem flagHsymm_zero_succ (N n c : ℕ) : flagHsymm N n 0 (c + 1) = 0 := by
  simp [flagHsymm]

theorem flagHsymm_succ_succ (N n k c : ℕ) :
    flagHsymm N n (k + 1) (c + 1) =
      flagHsymm N n k (c + 1) + flagVar N n k * flagHsymm N n (k + 1) c := by
  simp only [flagHsymm]
  rw [Finset.sum_range_succ', Finset.mul_sum]
  have h1 : ∀ j ∈ Finset.range (c + 1), flagHsymm N n k (c + 1 - (j + 1)) * flagVar N n k ^ (j + 1) =
      flagVar N n k * (flagHsymm N n k (c - j) * flagVar N n k ^ j) := fun j _ => by
    rw [Nat.add_sub_add_right, pow_succ]
    ring
  rw [Finset.sum_congr rfl h1, Nat.sub_zero, pow_zero, mul_one]
  exact add_comm _ _

theorem isHomogeneous_flagVar (N n k : ℕ) : (flagVar N n k).IsHomogeneous 1 := by
  unfold flagVar
  split_ifs
  · exact isHomogeneous_X _ _
  · exact isHomogeneous_zero _ _ _

theorem isHomogeneous_flagHsymm (N n : ℕ) : ∀ k c, (flagHsymm N n k c).IsHomogeneous c
  | 0, c => by
    unfold flagHsymm
    split_ifs with h
    · subst h
      exact isHomogeneous_one _ _
    · exact isHomogeneous_zero _ _ _
  | k + 1, c => by
    unfold flagHsymm
    refine IsHomogeneous.sum _ _ _ fun j hj => ?_
    have hj' : j ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h := (isHomogeneous_flagHsymm N n k (c - j)).mul ((isHomogeneous_flagVar N n k).pow j)
    convert h using 1
    rw [one_mul]
    omega

theorem hsymm_option_succ (α : Type*) [Fintype α] [DecidableEq α] (c : ℕ) :
    hsymm (Option α) ℤ (c + 1) =
      X none * hsymm (Option α) ℤ c + rename some (hsymm α ℤ (c + 1)) := by
  have hL : hsymm (Option α) ℤ (c + 1) = ∑ u : Sym (Option α) c ⊕ Sym α (c + 1),
      (((symOptionSuccEquiv (α := α) (n := c)).symm u).1.map X).prod :=
    (Equiv.sum_comp (symOptionSuccEquiv (α := α) (n := c)).symm
      (fun s : Sym (Option α) (c + 1) => (s.1.map X).prod)).symm
  rw [hL, Fintype.sum_sum_type]
  unfold hsymm
  rw [Finset.mul_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    show ((none ::ₘ s.1).map X).prod = _
    rw [Multiset.map_cons, Multiset.prod_cons]
  · refine Finset.sum_congr rfl fun s _ => ?_
    show ((s.1.map Function.Embedding.some).map X).prod = _
    simp only [map_multiset_prod, Multiset.map_map, Function.comp_def, rename_X,
      Function.Embedding.some_apply]

theorem hsymm_fin_succ (k c : ℕ) :
    hsymm (Fin (k + 1)) ℤ (c + 1) =
      X (Fin.last k) * hsymm (Fin (k + 1)) ℤ c + rename Fin.castSucc (hsymm (Fin k) ℤ (c + 1)) := by
  have h := congrArg (rename (finSuccEquivLast (n := k)).symm) (hsymm_option_succ (Fin k) c)
  rw [rename_hsymm, map_add, map_mul, rename_X, rename_hsymm, rename_rename] at h
  rw [h]
  have e1 : (finSuccEquivLast (n := k)).symm none = Fin.last k := finSuccEquivLast_symm_none
  have e2 : (finSuccEquivLast (n := k)).symm ∘ some = Fin.castSucc :=
    funext fun i => finSuccEquivLast_symm_some i
  rw [e1, e2]

theorem hsymm_fin_zero_succ (c : ℕ) : hsymm (Fin 0) ℤ (c + 1) = 0 := by
  rw [hsymm]
  refine Finset.sum_eq_zero fun s _ => ?_
  obtain ⟨a, -⟩ := s.exists_mem
  exact a.elim0

theorem flagHsymm_eq_rename (N n : ℕ) : ∀ (k : ℕ) (hk : k ≤ N) (c : ℕ),
    flagHsymm N n k c = rename (fun i : Fin k => Fin.castAdd n (Fin.castLE hk i)) (hsymm (Fin k) ℤ c)
  | 0, _, 0 => by simp [flagHsymm, hsymm_zero]
  | 0, _, c + 1 => by rw [flagHsymm_zero_succ, hsymm_fin_zero_succ, map_zero]
  | k + 1, _, 0 => by rw [flagHsymm_zero_right, hsymm_zero, map_one]
  | k + 1, hk, c + 1 => by
    rw [flagHsymm_succ_succ, flagHsymm_eq_rename N n k (by omega) (c + 1),
      flagHsymm_eq_rename N n (k + 1) hk c, hsymm_fin_succ, map_add, map_mul, rename_X, rename_rename]
    have hv : flagVar N n k = X (Fin.castAdd n (Fin.castLE hk (Fin.last k))) := by
      unfold flagVar
      rw [dif_pos (by omega)]
      rfl
    rw [hv]
    exact add_comm _ _

end Hsymm

section PairNum

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem pairNum_add_expansion {m : ℕ} (P : Ideal (MRing ι O)) (x x' : Fin m → K → ℤ)
    (f g : Fin m → MRing ι O) (Gs Hs : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℤ) (Q : List (K → ℤ)) :
    pairNum P x x' f g (Gs + Hs) Q = pairNum P x x' f g Gs Q + pairNum P x x' f g Hs Q :=
  (pairNumHom P x x' f g Q).map_add Gs Hs

theorem pairNum_zero_expansion {m : ℕ} (P : Ideal (MRing ι O)) (x x' : Fin m → K → ℤ)
    (f g : Fin m → MRing ι O) (Q : List (K → ℤ)) : pairNum P x x' f g 0 Q = 0 :=
  (pairNumHom P x x' f g Q).map_zero

end PairNum

theorem isPairExpansion_zero_zero {n m : ℕ} : IsPairExpansion m (0 : MvPolynomial (Fin n) ℤ) 0 :=
  ⟨by simp, fun _ => isHomogeneous_zero _ _ _⟩

theorem flagClosurePt_top {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M M' : ℕ} {E : Type*}
    [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ] (y : (Σ k, ι k) → Ω)
    (w e : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E)
    (t : Fin N → Φ) : flagClosurePt y w e φ φ' t N = pairProjCoord y e φ φ' t := by
  have key : ∀ ψ : Module.Dual Ω E, ∑ j, flagCoord w e t N j * algebraMap Ω Φ (ψ (w j)) =
      ∑ i, t i * algebraMap Ω Φ (ψ (e i)) := by
    intro ψ
    have hψ : ∀ i, ψ (e i) = ∑ j, w.repr (e i) j * ψ (w j) := by
      intro i
      calc ψ (e i) = ψ (∑ j, w.repr (e i) j • w j) := by rw [w.sum_repr]
        _ = ∑ j, w.repr (e i) j * ψ (w j) := by simp only [map_sum, map_smul, smul_eq_mul]
    simp only [flagCoord, Fin.is_lt, if_true, hψ, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  funext p
  rcases p with ⟨_ | _ | o, l⟩
  · exact key (φ' l)
  · exact key (φ l)
  · rfl

theorem SegreClosureNumber.proof (hExp : PairNumberExpansionIndependence.Statement)
    (hMod : SegreFlagClosureModel.Statement) (hCut : SegreFlagClosureCut.Statement)
    (hPull : SegreFlagClosurePullback.Statement) : SegreClosureNumber.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ'
    hφ hφ' Φ _ _ _ _ e t ht hZ f₀ g₀ hD₀ hD₀gen n z z' fz gz hz a r R hR As hAs Cs hCs Q hQ
  classical
  have hvert : ∀ i, IsVerticalDivisor (pointIdeal O y) ϖ (Fin.append x z i - Fin.append x' z' i)
      (Fin.append f fz i) (Fin.append g gz i) := fun i =>
    Fin.addCases (fun i => by simpa only [Fin.append_left] using hF.vertical i)
      (fun j => by simpa only [Fin.append_right] using hz j) i

  have hVexp : ∀ (m : ℕ) (G : MvPolynomial (Fin (N + n)) ℤ), G.IsHomogeneous m →
      ∀ Gs Hs, IsPairExpansion m G Gs → IsPairExpansion m G Hs →
      ∀ Q' : List (K → ℤ), Q'.length + m = d + 1 →
      pairNum (pointIdeal O y) (Fin.append x z) (Fin.append x' z') (Fin.append f fz) (Fin.append g gz) Gs Q' =
        pairNum (pointIdeal O y) (Fin.append x z) (Fin.append x' z') (Fin.append f fz) (Fin.append g gz) Hs Q' :=
    fun m G hG Gs Hs hGs hHs Q' hQ' =>
      hExp O ϖ hϖ K ι (pointIdeal O y) d hV (N + n) _ _ _ _ hvert m G hG Gs Hs hGs hHs Q' hQ'

  have stepCore : ∀ (k : ℕ) (hk : k < N) (f₁ g₁ f₂ g₂ : MRing (bundleIdx (bundleIdx ι M) M') O),
      IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) ϖ
        (zetaFirst a₀ - zetaSecond a₀') f₁ g₁ →
      aeval (flagClosurePt y w e φ φ' t (k + 1)) f₁ = aeval (flagClosurePt y w e φ φ' t (k + 1)) g₁ →
      (0 < k → IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t k)) ϖ
          (zetaFirst a₀ - zetaSecond a₀') f₂ g₂ ∧
        aeval (flagClosurePt y w e φ φ' t k) f₂ = aeval (flagClosurePt y w e φ φ' t k) g₂) →
      (∀ (i r : ℕ) (Bf : MvPolynomial (Fin (N + n)) ℤ), Bf.IsHomogeneous r →
        ∀ Ds, IsPairExpansion (i + r)
          (X (Fin.castAdd (N + n) (0 : Fin 1)) ^ i * rename (Fin.natAdd 1) Bf) Ds →
        ∀ Fs, IsPairExpansion (i + 1 - k + r) (flagHsymm N n k (i + 1 - k) * Bf) Fs →
        ∀ Q' : List (K → ℤ), Q'.length + (i + r) = d + k →
        (if k = 0 then (0 : ℤ) else
          pairNum (pointIdeal O (flagClosurePt y w e φ φ' t k))
            (closureDeg (zetaFirst a₀) (Fin.append x z)) (closureDeg (zetaSecond a₀') (Fin.append x' z'))
            (closureForm M M' f₂ (Fin.append f fz)) (closureForm M M' g₂ (Fin.append g gz)) Ds
            (Q'.map liftPairDeg)) =
          if k ≤ i + 1 then (-1) ^ (i + 1 - k) *
            pairNum (pointIdeal O y) (Fin.append x z) (Fin.append x' z') (Fin.append f fz)
              (Fin.append g gz) Fs Q'
          else 0) →
      ∀ (i r : ℕ) (Bf : MvPolynomial (Fin (N + n)) ℤ), Bf.IsHomogeneous r →
        ∀ Es, IsPairExpansion (i + r)
          (X (Fin.castAdd (N + n) (0 : Fin 1)) ^ i * rename (Fin.natAdd 1) Bf) Es →
        ∀ Fs, IsPairExpansion (i - k + r) (flagHsymm N n (k + 1) (i - k) * Bf) Fs →
        ∀ Q' : List (K → ℤ), Q'.length + (i + r) = d + (k + 1) →
        pairNum (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)))
            (closureDeg (zetaFirst a₀) (Fin.append x z)) (closureDeg (zetaSecond a₀') (Fin.append x' z'))
            (closureForm M M' f₁ (Fin.append f fz)) (closureForm M M' g₁ (Fin.append g gz)) Es
            (Q'.map liftPairDeg) =
          if k ≤ i then (-1) ^ (i - k) *
            pairNum (pointIdeal O y) (Fin.append x z) (Fin.append x' z') (Fin.append f fz)
              (Fin.append g gz) Fs Q'
          else 0 := by
    intro k hk f₁ g₁ f₂ g₂ hv₁ hg₁ h₂ outer i
    induction i with
    | zero =>

      intro r Bf hB Es hEs Fs hFs Q' hQ'
      have hEs' : IsPairExpansion r (rename (Fin.natAdd 1) Bf) Es := by
        simpa only [pow_zero, one_mul, zero_add] using hEs
      obtain ⟨Bs, hBs⟩ := exists_isPairExpansion hB
      rw [hPull O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht
        (k + 1) (by omega) (by omega) f₁ g₁ hv₁ hg₁ n z z' fz gz hz r Bf hB Es Bs hEs' hBs Q' (by omega)]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [if_pos rfl, if_pos le_rfl, Nat.sub_self, pow_zero, one_mul]
        refine hVexp r Bf hB Bs Fs hBs ?_ Q' (by omega)
        simpa only [Nat.sub_self, zero_add, flagHsymm_zero_right, one_mul] using hFs
      · rw [if_neg (by omega), if_neg (by omega)]
    | succ i ih =>
      intro r Bf hB Es hEs Fs hFs Q' hQ'
      have hfv : flagVar N n k = X (Fin.castAdd n ⟨k, hk⟩) := by
        unfold flagVar
        rw [dif_pos hk]
      have hxB : (X (Fin.castAdd n ⟨k, hk⟩) * Bf : MvPolynomial (Fin (N + n)) ℤ).IsHomogeneous (r + 1) := by
        have h := (isHomogeneous_X ℤ (Fin.castAdd n ⟨k, hk⟩)).mul hB
        rwa [add_comm 1 r] at h
      have hA : (X (Fin.castAdd (N + n) (0 : Fin 1)) ^ i * rename (Fin.natAdd 1) Bf).IsHomogeneous (i + r) := by
        have h := ((isHomogeneous_X ℤ (Fin.castAdd (N + n) (0 : Fin 1))).pow i).mul
          (hB.rename_isHomogeneous (f := (Fin.natAdd 1 : Fin (N + n) → Fin (1 + (N + n)))))
        convert h using 1
        ring
      have hT : (X (Fin.castAdd (N + n) (0 : Fin 1)) ^ i *
          rename (Fin.natAdd 1) (X (Fin.castAdd n ⟨k, hk⟩) * Bf)).IsHomogeneous (i + (r + 1)) := by
        have h := ((isHomogeneous_X ℤ (Fin.castAdd (N + n) (0 : Fin 1))).pow i).mul
          (hxB.rename_isHomogeneous (f := (Fin.natAdd 1 : Fin (N + n) → Fin (1 + (N + n)))))
        convert h using 1
        ring
      obtain ⟨Ts, hTs⟩ := exists_isPairExpansion hT
      obtain ⟨Ds, hDs⟩ := exists_isPairExpansion hA

      have hsum : IsPairExpansion (i + r + 1)
          ((X (Fin.castAdd (N + n) (0 : Fin 1)) + X (Fin.natAdd 1 (Fin.castAdd n ⟨k, hk⟩))) *
            (X (Fin.castAdd (N + n) (0 : Fin 1)) ^ i * rename (Fin.natAdd 1) Bf)) (Es + Ts) := by
        have hTs' : IsPairExpansion (i + 1 + r) (X (Fin.castAdd (N + n) (0 : Fin 1)) ^ i *
            rename (Fin.natAdd 1) (X (Fin.castAdd n ⟨k, hk⟩) * Bf)) Ts := by
          rw [show i + 1 + r = i + (r + 1) by omega]
          exact hTs
        have h := isPairExpansion_add hEs hTs'
        have hpoly : X (Fin.castAdd (N + n) (0 : Fin 1)) ^ (i + 1) * rename (Fin.natAdd 1) Bf +
            X (Fin.castAdd (N + n) (0 : Fin 1)) ^ i * rename (Fin.natAdd 1) (X (Fin.castAdd n ⟨k, hk⟩) * Bf) =
            (X (Fin.castAdd (N + n) (0 : Fin 1)) + X (Fin.natAdd 1 (Fin.castAdd n ⟨k, hk⟩))) *
              (X (Fin.castAdd (N + n) (0 : Fin 1)) ^ i * rename (Fin.natAdd 1) Bf) := by
          rw [map_mul, rename_X]
          ring
        rw [← hpoly, show i + r + 1 = i + 1 + r by omega]
        exact h
      have hcut := hCut O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht
        k hk f₁ g₁ f₂ g₂ hv₁ hg₁ h₂ n z z' fz gz hz (i + r) _ hA (Es + Ts) Ds hsum hDs Q' (by omega)
      rw [pairNum_add_expansion] at hcut

      obtain ⟨Fs₁, hFs₁⟩ := exists_isPairExpansion ((isHomogeneous_flagHsymm N n (k + 1) (i - k)).mul hxB)
      have hTv := ih (r + 1) _ hxB Ts hTs Fs₁ hFs₁ Q' (by omega)

      obtain ⟨Fs₂, hFs₂⟩ := exists_isPairExpansion ((isHomogeneous_flagHsymm N n k (i + 1 - k)).mul hB)
      have hOv := outer i r Bf hB Ds hDs Fs₂ hFs₂ Q' (by omega)
      have hEv : pairNum (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)))
            (closureDeg (zetaFirst a₀) (Fin.append x z)) (closureDeg (zetaSecond a₀') (Fin.append x' z'))
            (closureForm M M' f₁ (Fin.append f fz)) (closureForm M M' g₁ (Fin.append g gz)) Es
            (Q'.map liftPairDeg) =
          (if k ≤ i + 1 then (-1) ^ (i + 1 - k) *
            pairNum (pointIdeal O y) (Fin.append x z) (Fin.append x' z') (Fin.append f fz)
              (Fin.append g gz) Fs₂ Q' else 0) -
          (if k ≤ i then (-1) ^ (i - k) *
            pairNum (pointIdeal O y) (Fin.append x z) (Fin.append x' z') (Fin.append f fz)
              (Fin.append g gz) Fs₁ Q' else 0) := by
        rw [← hOv, ← hTv, ← hcut]
        ring
      rw [hEv]
      rcases lt_trichotomy k (i + 1) with hlt | heq | hgt
      ·
        have hki : k ≤ i := by omega
        rw [if_pos hlt.le, if_pos hki, if_pos hlt.le]
        have hc : i + 1 - k = i - k + 1 := by omega
        have hFs₁' : IsPairExpansion (i + 1 - k + r) (flagHsymm N n (k + 1) (i - k) *
            (X (Fin.castAdd n ⟨k, hk⟩) * Bf)) Fs₁ := by
          rw [show i + 1 - k + r = i - k + (r + 1) by omega]
          exact hFs₁
        have h12 := isPairExpansion_add hFs₂ hFs₁'
        have hpoly : flagHsymm N n k (i + 1 - k) * Bf +
            flagHsymm N n (k + 1) (i - k) * (X (Fin.castAdd n ⟨k, hk⟩) * Bf) =
            flagHsymm N n (k + 1) (i + 1 - k) * Bf := by
          rw [hc, flagHsymm_succ_succ, hfv]
          ring
        rw [hpoly] at h12
        rw [hVexp _ _ ((isHomogeneous_flagHsymm N n (k + 1) (i + 1 - k)).mul hB) Fs (Fs₂ + Fs₁) hFs h12 Q'
          (by omega), pairNum_add_expansion, hc, pow_succ]
        ring
      ·
        subst heq
        rw [if_pos le_rfl, if_neg (by omega), if_pos le_rfl, Nat.sub_self, pow_zero, one_mul, sub_zero, one_mul]
        refine hVexp _ _ hB Fs₂ Fs ?_ ?_ Q' (by omega)
        · simpa only [Nat.sub_self, zero_add, flagHsymm_zero_right, one_mul] using hFs₂
        · simpa only [Nat.sub_self, zero_add, flagHsymm_zero_right, one_mul] using hFs
      ·
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), sub_zero]

  have claim : ∀ (k : ℕ) (hk : k < N) (f₁ g₁ : MRing (bundleIdx (bundleIdx ι M) M') O),
      IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) ϖ
        (zetaFirst a₀ - zetaSecond a₀') f₁ g₁ →
      aeval (flagClosurePt y w e φ φ' t (k + 1)) f₁ = aeval (flagClosurePt y w e φ φ' t (k + 1)) g₁ →
      ∀ (i r : ℕ) (Bf : MvPolynomial (Fin (N + n)) ℤ), Bf.IsHomogeneous r →
        ∀ Es, IsPairExpansion (i + r)
          (X (Fin.castAdd (N + n) (0 : Fin 1)) ^ i * rename (Fin.natAdd 1) Bf) Es →
        ∀ Fs, IsPairExpansion (i - k + r) (flagHsymm N n (k + 1) (i - k) * Bf) Fs →
        ∀ Q' : List (K → ℤ), Q'.length + (i + r) = d + (k + 1) →
        pairNum (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)))
            (closureDeg (zetaFirst a₀) (Fin.append x z)) (closureDeg (zetaSecond a₀') (Fin.append x' z'))
            (closureForm M M' f₁ (Fin.append f fz)) (closureForm M M' g₁ (Fin.append g gz)) Es
            (Q'.map liftPairDeg) =
          if k ≤ i then (-1) ^ (i - k) *
            pairNum (pointIdeal O y) (Fin.append x z) (Fin.append x' z') (Fin.append f fz)
              (Fin.append g gz) Fs Q'
          else 0 := by
    intro k
    induction k with
    | zero =>
      intro hk f₁ g₁ hv₁ hg₁
      refine stepCore 0 hk f₁ g₁ f₁ g₁ hv₁ hg₁ (fun h => absurd h (lt_irrefl 0)) ?_
      intro i r Bf hB Ds hDs Fs hFs Q' hQ'
      have hFs' : IsPairExpansion (i + 1 - 0 + r) 0 Fs := by
        simpa only [Nat.sub_zero, flagHsymm_zero_succ, zero_mul] using hFs
      rw [if_pos rfl, if_pos (Nat.zero_le _), hVexp _ 0 (isHomogeneous_zero _ _ _) Fs 0 hFs'
        isPairExpansion_zero_zero Q' (by omega), pairNum_zero_expansion, mul_zero]
    | succ k ihk =>
      intro hk f₁ g₁ hv₁ hg₁
      obtain ⟨-, f₂, g₂, hv₂, hg₂⟩ := hMod O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hF M M' a₀ a₀'
        φ φ' hφ hφ' Φ e t ht (k + 1) (by omega) (by omega)
      refine stepCore (k + 1) hk f₁ g₁ f₂ g₂ hv₁ hg₁ (fun _ => ⟨hv₂, hg₂⟩) ?_
      intro i r Bf hB Ds hDs Fs hFs Q' hQ'
      rw [if_neg (Nat.succ_ne_zero k), ihk (by omega) f₂ g₂ hv₂ hg₂ i r Bf hB Ds hDs Fs
        (by simpa only [Nat.add_sub_add_right] using hFs) Q' hQ']
      simp only [Nat.add_sub_add_right, Nat.add_le_add_iff_right]

  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have hpt : flagClosurePt y w e φ φ' t (k + 1) = pairProjCoord y e φ φ' t := flagClosurePt_top y w e φ φ' t
  have hv₀ : IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) ϖ
      (zetaFirst a₀ - zetaSecond a₀') f₀ g₀ := by
    rw [hpt]
    exact hD₀
  have hg₀ : aeval (flagClosurePt y w e φ φ' t (k + 1)) f₀ = aeval (flagClosurePt y w e φ φ' t (k + 1)) g₀ := by
    rw [hpt]
    exact hD₀gen

  let σ : Fin (1 + n) → Fin (1 + (k + 1 + n)) :=
    Fin.append (fun _ : Fin 1 => Fin.castAdd (k + 1 + n) (0 : Fin 1)) (fun j => Fin.natAdd 1 (Fin.natAdd (k + 1) j))
  have hσ0 : σ (Fin.castAdd n (0 : Fin 1)) = Fin.castAdd (k + 1 + n) (0 : Fin 1) := Fin.append_left _ _ _
  have hσ1 : σ ∘ Fin.natAdd 1 = Fin.natAdd 1 ∘ Fin.natAdd (k + 1) := funext fun j => Fin.append_right _ _ _
  have hσR : rename σ (zetaPowTimes n (k + 1 - 1 + a) R) =
      X (Fin.castAdd (k + 1 + n) (0 : Fin 1)) ^ (k + 1 - 1 + a) *
        rename (Fin.natAdd 1) (rename (Fin.natAdd (k + 1)) R) := by
    rw [zetaPowTimes, map_mul, map_pow, rename_X, rename_rename, rename_rename, hσ0, hσ1]
  have hEs := isPairExpansion_push σ hCs
  rw [hσR] at hEs
  have hi : k + 1 - 1 + a - k = a := by omega
  have hcast : (fun i : Fin (k + 1) => Fin.castAdd n (Fin.castLE (le_refl (k + 1)) i)) = Fin.castAdd n :=
    funext fun i => Fin.ext rfl
  have hAs' : IsPairExpansion (k + 1 - 1 + a - k + r)
      (flagHsymm (k + 1) n (k + 1) (k + 1 - 1 + a - k) * rename (Fin.natAdd (k + 1)) R) As := by
    rw [hi, flagHsymm_eq_rename (k + 1) n (k + 1) le_rfl a, hcast]
    exact hAs
  have hcl := claim k (by omega) f₀ g₀ hv₀ hg₀ (k + 1 - 1 + a) r _ hR.rename_isHomogeneous _ hEs As hAs' Q
    (by omega)
  rw [if_pos (by omega), pairNum_pushExpansion, hi, hpt] at hcl
  have e1 : closureDeg (zetaFirst a₀) (Fin.append x z) ∘ σ =
      Fin.append (fun _ : Fin 1 => zetaFirst a₀) (fun j => liftPairDeg (z j)) := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp [σ, closureDeg, Fin.append_left, Fin.append_right]
  have e2 : closureDeg (zetaSecond a₀') (Fin.append x' z') ∘ σ =
      Fin.append (fun _ : Fin 1 => zetaSecond a₀') (fun j => liftPairDeg (z' j)) := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp [σ, closureDeg, Fin.append_left, Fin.append_right]
  have e3 : closureForm M M' f₀ (Fin.append f fz) ∘ σ =
      Fin.append (fun _ : Fin 1 => f₀) (fun j => liftPairForm M M' (fz j)) := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp [σ, closureForm, Fin.append_left, Fin.append_right]
  have e4 : closureForm M M' g₀ (Fin.append g gz) ∘ σ =
      Fin.append (fun _ : Fin 1 => g₀) (fun j => liftPairForm M M' (gz j)) := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp [σ, closureForm, Fin.append_left, Fin.append_right]
  rw [e1, e2, e3, e4] at hcl
  rw [hcl, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
