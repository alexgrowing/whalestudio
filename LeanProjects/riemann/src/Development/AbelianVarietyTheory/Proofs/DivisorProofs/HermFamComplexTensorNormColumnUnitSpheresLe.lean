import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfVectorMultiplicationsMemFiltrationLattiStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort.ColNorm

theorem csq_equiv {K V : Type} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V) (σ : K →+* ℂ)
    {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (c : κ → ℂ) (v : κ → V) :
    csq h σ (fun i => c (e i)) (fun i => v (e i)) = csq h σ c v := by
  unfold csq
  congr 1
  exact Fintype.sum_equiv e _ _ fun i => Fintype.sum_equiv e _ _ fun k => rfl

theorem cnrm_equiv {K V : Type} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V) (σ : K →+* ℂ)
    {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (c : κ → ℂ) (v : κ → V) :
    cnrm h σ (fun i => c (e i)) (fun i => v (e i)) = cnrm h σ c v :=
  congrArg Real.sqrt (csq_equiv h σ e c v)

theorem word_succ {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (u : Fin (t + 1) → Fin N → K) :
    word mul u = mul (u 0) * word mul (Fin.tail u) := by
  simp only [word, List.ofFn_succ, List.prod_cons]
  rfl

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A]
  [IsScalarTower (𝓞 F) F A]

theorem cnrm_words_le (S : Sys F A) (hS : S.Hyp) (σ : F →+* ℂ) (u : Fin (S.D + 1) × Fin S.N → ℂ)
    (hu : ∀ i, frameNorm (S.fr σ) (fun j => u (i, j)) = 1) :
    ∀ (t : ℕ) (β : Fin t → Fin (S.D + 1)) (j l : ℕ), j + t = l → l ≤ S.T →
      ∀ (m : ℕ) (c : Fin m → ℂ) (f : Fin m → S.V j) (g : (Fin t → Fin S.N) × Fin m → S.V l),
      (∀ e i, (g (e, i) : A) = word S.mul (fun q => Pi.single (e q) 1) (f i)) →
      cnrm (S.nm l) σ (fun p => (∏ q, u (β q, p.1 q)) * c p.2) g ≤ Real.sqrt S.beta ^ t * cnrm (S.nm j) σ c f := by
  intro t
  induction t with
  | zero =>
    intro β j l hl _ m c f g hg
    obtain rfl : l = j := by omega
    have e : g = fun p => f p.2 := funext fun p => Subtype.ext (by
      rw [show p = (p.1, p.2) from rfl, hg]
      simp [word])
    subst e
    have := cnrm_equiv (S.nm l) σ (Equiv.uniqueProd (Fin m) (Fin 0 → Fin S.N)).symm
      (fun p => (∏ q, u (β q, p.1 q)) * c p.2) (fun p => f p.2)
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, pow_zero] at this ⊢
    rw [← this]
    rfl
  | succ t ih =>
    intro β j l hl hlT m c f g hg
    obtain rfl : l = j + t + 1 := by omega
    have hmem := (GlobalTheory.T.productOfVectorMultiplications_mem_filtration_lattice F A S hS j t (by omega)).1
    let g' : (Fin t → Fin S.N) × Fin m → S.V (j + t) := fun p =>
      ⟨word S.mul (fun q => Pi.single (p.1 q) 1) (f p.2), hmem _ _ (f p.2).2⟩
    have h₀ := ih (Fin.tail β) j (j + t) rfl (by omega) m c f g' (fun _ _ => rfl)
    let eM : (Fin t → Fin S.N) × Fin m ≃ Fin (Fintype.card ((Fin t → Fin S.N) × Fin m)) := Fintype.equivFin _
    let E : Fin S.N × Fin (Fintype.card ((Fin t → Fin S.N) × Fin m)) ≃ (Fin (t + 1) → Fin S.N) × Fin m :=
      { toFun := fun p => (Fin.cons p.1 (eM.symm p.2).1, (eM.symm p.2).2)
        invFun := fun p => (p.1 0, eM (Fin.tail p.1, p.2))
        left_inv := fun p => by simp
        right_inv := fun p => by simp }
    have hE : ∀ k r, E (k, r) = (Fin.cons k (eM.symm r).1, (eM.symm r).2) := fun k r => rfl
    have hb := hS.bound σ (j + t) (by omega) (fun k => u (β 0, k)) _
      (fun r => (∏ q, u (Fin.tail β q, (eM.symm r).1 q)) * c (eM.symm r).2) (fun r => g' (eM.symm r))
      (fun p => g (E p)) (fun k r => by
        rw [hE, hg, word_succ]
        rfl)
    have hq := cnrm_equiv (S.nm (j + t)) σ eM.symm (fun p => (∏ q, u (Fin.tail β q, p.1 q)) * c p.2) g'
    have h1 := cnrm_equiv (S.nm (j + t + 1)) σ E (fun p => (∏ q, u (β q, p.1 q)) * c p.2) g
    have hc : ∀ p, (∏ q, u (β q, (E p).1 q)) * c (E p).2 =
        u (β 0, p.1) * ((∏ q, u (Fin.tail β q, (eM.symm p.2).1 q)) * c (eM.symm p.2).2) := fun p => by
      obtain ⟨k, r⟩ := p
      rw [hE]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
      ring
    simp only [hc] at h1
    rw [hu, mul_one, hq] at hb
    rw [← h1]
    calc _ ≤ _ := hb
      _ ≤ Real.sqrt S.beta * (Real.sqrt S.beta ^ t * cnrm (S.nm j) σ c f) :=
        mul_le_mul_of_nonneg_left h₀ (Real.sqrt_nonneg _)
      _ = _ := by ring

end GlobalTheory.HSShort.ColNorm

open GlobalTheory.HSShort.ColNorm in

theorem GlobalTheory.HSShort.cnrm_col_le : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ (κ : S.Col) (σ : F →+* ℂ) (u : Fin (S.D + 1) × Fin S.N → ℂ), (∀ i, frameNorm (S.fr σ) (fun j => u (i, j)) = 1) → cnrm (S.nm S.T) σ (fun i => eval₂ σ u (coordP S.mul (c i) κ.β (κ.x : A))) b ≤ Real.sqrt S.beta ^ κ.t * (S.nm κ.j).nrm σ κ.x := by
  intro F A _ _ _ _ _ _ S hS d b c hc κ σ u hu
  obtain ⟨j, t, hjt, β, x⟩ := κ
  have hmem := (GlobalTheory.T.productOfVectorMultiplications_mem_filtration_lattice F A S hS j t (by omega)).1
  let g : (Fin t → Fin S.N) × Fin 1 → S.V S.T := fun p =>
    ⟨word S.mul (fun q => Pi.single (p.1 q) 1) (x : A), by rw [← hjt]; exact hmem _ _ x.2⟩
  have key := cnrm_words_le S hS σ u hu t β j S.T hjt le_rfl 1 (fun _ => 1) (fun _ => x) g (fun _ _ => rfl)
  have hr : cnrm (S.nm j) σ (fun _ : Fin 1 => (1 : ℂ)) (fun _ => x) = (S.nm j).nrm σ x := by
    simp [cnrm, csq, HermFam.nrm]
  rw [hr] at key
  refine le_of_eq_of_le ?_ key
  unfold cnrm
  congr 1
  calc _ = csq (S.nm S.T) σ (fun i => ∑ p, ((∏ q, u (β q, p.1 q)) * 1) * σ (b.repr (g p) i)) b := by
        congr 1
        funext i
        simp only [coordP, eval₂_sum, eval₂_mul, eval₂_C, eval₂_prod, eval₂_X, Fintype.sum_prod_type,
          Finset.univ_unique, Finset.sum_singleton, mul_one]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [← hc i (g (e, default))]
        simp [g, mul_comm]
    _ = csq (S.nm S.T) σ (fun p => (∏ q, u (β q, p.1 q)) * 1) (fun p => ∑ i, b.repr (g p) i • b i) :=
        (csq_comb _ _ _ _ _).symm
    _ = _ := by simp only [b.sum_repr]
