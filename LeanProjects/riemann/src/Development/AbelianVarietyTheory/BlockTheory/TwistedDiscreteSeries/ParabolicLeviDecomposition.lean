import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.SmGL GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.SplitWeil Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped NNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ParabolicLeviDecomposition

structure ParabLevi (k : Type) [Field k] (r : ℕ) where

  s : ℕ

  d : Fin s → ℕ

  e : (Σ a, Fin (d a)) ≃ Fin r

  g : GL (Fin r) k

namespace ParabLevi

variable {k : Type} [Field k] {r : ℕ} (P : ParabLevi k r)

def coord : GL (Fin r) k →* GL (Fin r) k := (MulAut.conj P.g⁻¹).toMonoidHom

theorem coord_apply (x : GL (Fin r) k) : P.coord x = P.g⁻¹ * x * P.g := by simp [coord]

def Q : Subgroup (GL (Fin r) k) := (parab k P.e).comap P.coord

def M : Subgroup (GL (Fin r) k) := (leviEmb k P.e).range.comap P.coord

def N : Subgroup (GL (Fin r) k) := (unipRad k P.e).comap P.coord

def lieN : Submodule k (Matrix (Fin r) (Fin r) k) where
  carrier := {X | ∀ i j, blk P.e j ≤ blk P.e i →
    ((P.g⁻¹ : GL (Fin r) k).1 * X * P.g.1) i j = 0}
  zero_mem' := fun i j _ => by simp
  add_mem' := fun {X Y} hX hY i j h => by
    rw [mul_add, add_mul, Matrix.add_apply, hX i j h, hY i j h, add_zero]
  smul_mem' := fun c X hX i j h => by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, hX i j h, smul_zero]

theorem M_le_Q : P.M ≤ P.Q := by
  rintro x ⟨y, hy⟩
  change P.coord x ∈ parab k P.e
  exact hy ▸ leviEmb_mem_parab k P.e y

theorem exists_mul {q : GL (Fin r) k} (hq : q ∈ P.Q) : ∃ m ∈ P.M, ∃ n ∈ P.N, q = m * n := by
  obtain ⟨u, hu, e⟩ := exists_levi_mul_unip k P.e ⟨P.coord q, hq⟩
  have hc : ∀ y, P.coord (P.g * y * P.g⁻¹) = y := fun y => by rw [coord_apply]; group
  refine ⟨P.g * leviEmb k P.e (leviProj k P.e ⟨P.coord q, hq⟩) * P.g⁻¹, ⟨_, (hc _).symm⟩, P.g * u * P.g⁻¹,
    show P.coord _ ∈ unipRad k P.e from (hc u).symm ▸ hu, ?_⟩
  calc q = P.g * P.coord q * P.g⁻¹ := by rw [coord_apply]; group
    _ = P.g * (leviEmb k P.e (leviProj k P.e ⟨P.coord q, hq⟩) * u) * P.g⁻¹ := congrArg (P.g * · * P.g⁻¹) e
    _ = _ := by group

theorem sub_one_mem_lieN {u : GL (Fin r) k} (hu : u ∈ P.N) : u.1 - 1 ∈ P.lieN := by
  intro i j h
  obtain ⟨h1, h2⟩ := mem_unipRad.1 (show P.coord u ∈ unipRad k P.e from hu)
  have e : (P.g⁻¹ : GL (Fin r) k).1 * (u.1 - 1) * P.g.1 = (P.coord u).1 - 1 := by
    rw [coord_apply, mul_sub, sub_mul, mul_one, Units.inv_mul, Units.val_mul, Units.val_mul]
  rw [e, Matrix.sub_apply, sub_eq_zero]
  obtain ⟨⟨a, i⟩, rfl⟩ := P.e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := P.e.surjective j
  simp only [blk_apply] at h
  rcases h.lt_or_eq with h | rfl
  · rw [mem_parab_iff.1 h1 a b i j h, Matrix.one_apply_ne]
    intro e'
    exact h.ne' (congrArg Sigma.fst (P.e.injective e'))
  · rw [h2]
    simp [Matrix.one_apply]

theorem conj_mem_lieN {q : GL (Fin r) k} (hq : q ∈ P.Q) {X : Matrix (Fin r) (Fin r) k} (hX : X ∈ P.lieN) :
    q.1 * X * (q⁻¹ : GL (Fin r) k).1 ∈ P.lieN := by
  intro i j h
  have e : (P.g⁻¹ : GL (Fin r) k).1 * (q.1 * X * (q⁻¹ : GL (Fin r) k).1) * P.g.1 =
      (P.coord q).1 * ((P.g⁻¹ : GL (Fin r) k).1 * X * P.g.1) * (P.coord q⁻¹).1 := by
    simp only [coord_apply, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]
  have h1 := mem_parab.1 (show P.coord q ∈ parab k P.e from hq)
  have h2 := mem_parab.1 (show P.coord q⁻¹ ∈ parab k P.e from P.Q.inv_mem hq)
  rw [e, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : blk P.e j < blk P.e b
  · rw [h2 b j hb, mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_zero fun a _ => ?_, zero_mul]
    by_cases ha : blk P.e a < blk P.e i
    · rw [h1 i a ha, zero_mul]
    · rw [hX a b (((not_lt.1 hb).trans h).trans (not_lt.1 ha)), mul_zero]

def adN (q : P.M) : P.lieN →ₗ[k] P.lieN :=
  (LinearMap.mulLeftRight k (q.1.1, (q.1⁻¹ : GL (Fin r) k).1)).restrict fun _ hX =>
    P.conj_mem_lieN (P.M_le_Q q.2) hX

theorem coe_adN (q : P.M) (X : P.lieN) :
    (P.adN q X : Matrix (Fin r) (Fin r) k) = q.1.1 * X * (q.1⁻¹ : GL (Fin r) k).1 := rfl

def detOneSubAd (q : P.M) : k := LinearMap.det (1 - P.adN q)

end ParabLevi

def borelLevi (k : Type) [Field k] (r : ℕ) (g : GL (Fin r) k) : ParabLevi k r :=
  ⟨r, fun _ => 1, Equiv.sigmaUnique _ _, g⟩

example (k : Type) [Field k] : !![0, 1; 0, 0] ∈ (borelLevi k 2 1).lieN ∧ !![0, 0; 1, 0] ∉ (borelLevi k 2 1).lieN := by
  refine ⟨fun i j h => ?_, fun h => ?_⟩
  · change j ≤ i at h
    fin_cases i <;> fin_cases j <;> simp_all [borelLevi]
  · have := h 1 0 (show (0 : Fin 2) ≤ 1 by decide)
    simp [borelLevi] at this

variable (F : Type) [Field F] [NumberField F] (r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))

abbrev GS : Type := ∀ v : S, GL (Fin r) (Fv F v.1)

variable {F r S} (P : ∀ v : S, ParabLevi (Fv F v.1) r)

def QS : Subgroup (GS F r S) := Subgroup.pi Set.univ fun v => (P v).Q

def MS : Subgroup (GS F r S) := Subgroup.pi Set.univ fun v => (P v).M

def NS : Subgroup (GS F r S) := Subgroup.pi Set.univ fun v => (P v).N

def absDet (q : MS P) : ℝ := ∏ v : S, ‖(P v).detOneSubAd ⟨q.1 v, q.2 v trivial⟩‖

example {v : HeightOneSpectrum (𝓞 F)} {ϖ : (Fv F v)ˣ} (h : IsUnif ϖ) :
    ‖(ϖ : Fv F v)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, h]
  have : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  rw [WithZeroMulInt.toNNReal_neg_apply _ this]
  have e : WithZero.unzero this = Multiplicative.ofAdd (-1 : ℤ) := WithZero.coe_inj.1 (WithZero.coe_unzero this)
  rw [e]
  simp

def IsLeviPart (K : Subgroup (GS F r S)) (μ : GS F r S → MS P) : Prop :=
  ∀ x, ∃ n ∈ NS P, ∃ k ∈ K, x = μ x * n * k

theorem exists_isLeviPart {K : Subgroup (GS F r S)} (h : ∀ x, ∃ q ∈ QS P, ∃ k ∈ K, x = q * k) :
    ∃ μ, IsLeviPart P K μ := by
  have : ∀ x, ∃ m : MS P, ∃ n ∈ NS P, ∃ k ∈ K, x = m * n * k := fun x => by
    obtain ⟨q, hq, k, hk, rfl⟩ := h x
    choose m hm n hn e using fun v => (P v).exists_mul (hq v trivial)
    exact ⟨⟨m, fun v _ => hm v⟩, n, fun v _ => hn v, k, hk, congrArg (· * k) (funext e)⟩
  choose μ hμ using this
  exact ⟨μ, hμ⟩

section Meas

variable {H : Type} [Group H] [MeasurableSpace H] {T M : Subgroup H}

def measIn (h : T ≤ M) (dt : Measure T) : Measure (T.subgroupOf M) := dt.map (Subgroup.subgroupOfEquivOfLe h).symm

theorem measurable_subgroupOfEquivOfLe_symm (h : T ≤ M) : Measurable (Subgroup.subgroupOfEquivOfLe h).symm :=
  (measurable_subtype_coe.subtype_mk (h := fun t => h t.2)).subtype_mk

end Meas

def innerFn (K : Subgroup (GS F r S)) (γ : MS P) (φ : GS F r S → ℂ) (k : K) (m : MS P) (n : NS P) : ℂ :=
  φ ((k : GS F r S)⁻¹ * (m⁻¹ * γ * m : MS P) * n * k)

def weight (γ : MS P) (b : Quot ((cent (γ : GS F r S)).subgroupOf (MS P)) → ℂ)
    (q : Quot ((cent (γ : GS F r S)).subgroupOf (MS P))) : ℂ :=
  b q * ((absDet P (q.out⁻¹ * γ⁻¹ * q.out) : ℝ) : ℂ)⁻¹

def LeviDescent : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    [MeasurableSpace (GS F r S)] [BorelSpace (GS F r S)]
    (P : ∀ v : S, ParabLevi (Fv F v.1) r) (K : Subgroup (GS F r S)),
    IsCompact (K : Set (GS F r S)) → (∀ x, ∃ q ∈ QS P, ∃ k ∈ K, x = q * k) →
    ∀ (dg : Measure (GS F r S)) (dm : Measure (MS P)) (dn : Measure (NS P)) (dk : Measure K)
      [dg.IsHaarMeasure] [dm.IsHaarMeasure] [dn.IsHaarMeasure] [dk.IsHaarMeasure],
    ∃ c : ℝ, 0 < c ∧
      ∀ (γ : MS P), (∀ v : S, IsRegSS ((γ : GS F r S) v).1) →
      ∀ (hT : cent (γ : GS F r S) ≤ MS P) (dt : Measure (cent (γ : GS F r S))) [dt.IsHaarMeasure]
        (b : Quot ((cent (γ : GS F r S)).subgroupOf (MS P)) → ℂ), Measurable b →
        (∀ C, IsCompact C → ∃ B : ℝ, ∀ q ∈ C, ‖b q‖ ≤ B) →
        (∀ (m m' : MS P), ∀ n ∈ NS P, ∀ n' ∈ NS P, ∀ k ∈ K, ∀ k' ∈ K,
          (m : GS F r S) * n * k = m' * n' * k' → b (mk _ m) = b (mk _ m')) →
        ∀ φ ∈ SB (GS F r S), ∀ μ : GS F r S → MS P, IsLeviPart P K μ →
          Integrable (fun z : K × Quot ((cent (γ : GS F r S)).subgroupOf (MS P)) × NS P =>
              weight P γ b z.2.1 * innerFn P K γ φ z.1 z.2.1.out z.2.2)
            (dk.prod ((quotMeas _ (measIn hT dt) dm).prod dn)) ∧
          HasQuotInt (cent (γ : GS F r S)) dt dg (fun x => φ (x⁻¹ * γ * x) * b (mk _ (μ x)))
            (c * ∫ k, ∫ q, weight P γ b q * ∫ n, innerFn P K γ φ k q.out n ∂dn
              ∂quotMeas _ (measIn hT dt) dm ∂dk)

end GlobalTheory.IndefiniteRowSideFullHecke.ParabolicLeviDecomposition
