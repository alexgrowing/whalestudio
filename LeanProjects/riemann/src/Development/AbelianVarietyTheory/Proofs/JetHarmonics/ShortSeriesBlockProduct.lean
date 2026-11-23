import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.BlockPolyLevelMove
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BlockHarmLevOfBlockHarm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaSumEqOfWitnessesCommonAlgebra
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InZhGeoInjStable
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortBlock

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke
attribute [local instance] Over.cartesianMonoidalCategory

section Poly

variable {T : Type} {r : T → ℕ} {n m : ℕ} {k : Type} [Field k]

def col (g : Fin n → Fin m) (ℓ : Letter T r n) : Letter T r m := ⟨ℓ.1, ℓ.2.1, g ℓ.2.2⟩

theorem col_injective {g : Fin n → Fin m} (hg : Function.Injective g) :
    Function.Injective (col g : Letter T r n → Letter T r m) := by
  rintro ⟨σ, i, b⟩ ⟨σ', i', b'⟩ h
  simp only [col, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  rw [hg h]

theorem notMem_range_col {g : Fin n → Fin m} {b : Fin m} (hb : ∀ x, g x ≠ b) (σ : T) (i : Fin (r σ)) :
    (⟨σ, i, b⟩ : Letter T r m) ∉ Set.range (col g : Letter T r n → Letter T r m) := by
  rintro ⟨⟨σ', i', x⟩, h⟩
  simp only [col, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq, Prod.mk.injEq] at h
  exact hb x h.2

theorem pderiv_rename_col_of_ne {g : Fin n → Fin m} {b : Fin m} (hb : ∀ x, g x ≠ b) (σ : T) (i : Fin (r σ))
    (P : MvPolynomial (Letter T r n) k) : pderiv (⟨σ, i, b⟩ : Letter T r m) (rename (col g) P) = 0 := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p ℓ hp =>
    rw [map_mul, Derivation.leibniz, hp, rename_X, pderiv_X]
    have hne : (col g ℓ) ≠ (⟨σ, i, b⟩ : Formalism.L2.Pj.Letter T r m) := fun h => notMem_range_col hb σ i ⟨ℓ, h⟩
    simp [hne]

theorem mem_harmK_iff (cc : T → T) (isX : T → Prop) (P : MvPolynomial (Letter T r n) k) :
    P ∈ harmK r n k cc isX (fun _ => 1) ↔ ∀ τ, isX τ → ∀ (i : Fin (r τ)) (i' : Fin (r (cc τ))),
      ∑ x : Fin n, pderiv (⟨τ, i, x⟩ : Letter T r n) (pderiv (⟨cc τ, i', x⟩ : Letter T r n) P) = 0 := by
  unfold harmK
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  unfold lap
  simp [Matrix.one_apply]

theorem rowShift_rename_col (g : Fin n → Fin m) (σ : T) (i i' : Fin (r σ)) (t : k)
    (P : MvPolynomial (Letter T r n) k) :
    rowShift r m k σ i i' t (rename (col g) P) = rename (col g) (rowShift r n k σ i i' t P) := by
  unfold rowShift
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  rintro ⟨τ, j, x⟩
  simp only [AlgHom.comp_apply, rename_X, aeval_X, col]
  by_cases h : ∃ b, (⟨τ, (j, x)⟩ : Formalism.L2.Pj.Letter T r n) = ⟨σ, (i, b)⟩
  · obtain ⟨b, hb⟩ := h
    simp only [Sigma.mk.inj_iff] at hb
    obtain ⟨rfl, hb⟩ := hb
    simp only [heq_eq_eq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rw [if_pos ⟨g x, rfl⟩, if_pos ⟨x, rfl⟩]
    simp [col]
  · have h' : ¬ ∃ b, (⟨τ, (j, g x)⟩ : Formalism.L2.Pj.Letter T r m) = ⟨σ, (i, b)⟩ := by
      rintro ⟨b, hb⟩
      simp only [Sigma.mk.inj_iff] at hb
      obtain ⟨rfl, hb⟩ := hb
      simp only [heq_eq_eq, Prod.mk.injEq] at hb
      exact h ⟨x, by rw [hb.1]⟩
    rw [if_neg h, if_neg h']
    simp [col]

variable {n₁ n₂ : ℕ}

theorem castAdd_ne_natAdd (x : Fin n₁) (y : Fin n₂) : Fin.castAdd n₂ x ≠ Fin.natAdd n₁ y := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

theorem natAdd_inj' : Function.Injective (Fin.natAdd n₁ : Fin n₂ → Fin (n₁ + n₂)) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [Fin.val_natAdd] at this
  omega

theorem castAdd_inj' : Function.Injective (Fin.castAdd n₂ : Fin n₁ → Fin (n₁ + n₂)) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa only [Fin.val_castAdd] using this

theorem block_apply_left (m₁ : Letter T r n₁ →₀ ℕ) (m₂ : Letter T r n₂ →₀ ℕ) (σ : T) (i : Fin (r σ)) (b : Fin n₁) :
    (m₁.mapDomain (col (Fin.castAdd n₂)) + m₂.mapDomain (col (Fin.natAdd n₁)) : Letter T r (n₁ + n₂) →₀ ℕ)
      ⟨σ, i, Fin.castAdd n₂ b⟩ = m₁ ⟨σ, i, b⟩ := by
  rw [Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range _ _
    (notMem_range_col (fun x => (castAdd_ne_natAdd b x).symm) σ i), add_zero]
  exact Finsupp.mapDomain_apply (col_injective castAdd_inj') m₁ ⟨σ, (i, b)⟩

theorem block_apply_right (m₁ : Letter T r n₁ →₀ ℕ) (m₂ : Letter T r n₂ →₀ ℕ) (σ : T) (i : Fin (r σ)) (b : Fin n₂) :
    (m₁.mapDomain (col (Fin.castAdd n₂)) + m₂.mapDomain (col (Fin.natAdd n₁)) : Letter T r (n₁ + n₂) →₀ ℕ)
      ⟨σ, i, Fin.natAdd n₁ b⟩ = m₂ ⟨σ, i, b⟩ := by
  rw [Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range _ _
    (notMem_range_col (fun x => castAdd_ne_natAdd x b) σ i), zero_add]
  exact Finsupp.mapDomain_apply (col_injective natAdd_inj') m₂ ⟨σ, (i, b)⟩

theorem mul_mem_HHa (cc : T → T) (isX : T → Prop) {a₁ a₂ : T → ℕ → ℕ}
    {P₁ : MvPolynomial (Letter T r n₁) k} {P₂ : MvPolynomial (Letter T r n₂) k}
    (h₁ : P₁ ∈ HHa r n₁ k cc isX a₁) (h₂ : P₂ ∈ HHa r n₂ k cc isX a₂) :
    rename (col (Fin.castAdd n₂)) P₁ * rename (col (Fin.natAdd n₁)) P₂ ∈
      HHa r (n₁ + n₂) k cc isX (fun τ i => a₁ τ i + a₂ τ i) := by
  unfold HHa at *
  unfold RowInv RowDeg at *
  simp only [Set.mem_ofPred_eq] at *
  obtain ⟨h₁H, h₁I, h₁D⟩ := h₁
  obtain ⟨h₂H, h₂I, h₂D⟩ := h₂
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_harmK_iff] at h₁H h₂H ⊢
    intro τ hτ i i'
    rw [Fin.sum_univ_add]
    have hL : ∀ x : Fin n₁, pderiv (⟨τ, (i, Fin.castAdd n₂ x)⟩ : Formalism.L2.Pj.Letter T r (n₁ + n₂))
        (pderiv (⟨cc τ, (i', Fin.castAdd n₂ x)⟩ : Formalism.L2.Pj.Letter T r (n₁ + n₂))
          (rename (col (Fin.castAdd n₂)) P₁ * rename (col (Fin.natAdd n₁)) P₂)) =
        rename (col (Fin.natAdd n₁)) P₂ *
          rename (col (Fin.castAdd n₂)) (pderiv (⟨τ, (i, x)⟩ : Formalism.L2.Pj.Letter T r n₁)
            (pderiv ⟨cc τ, (i', x)⟩ P₁)) := by
      intro x
      have e1 : ∀ (ρ : T) (j : Fin (r ρ)), (⟨ρ, (j, Fin.castAdd n₂ x)⟩ : Formalism.L2.Pj.Letter T r (n₁ + n₂)) =
          col (Fin.castAdd n₂) ⟨ρ, (j, x)⟩ := fun _ _ => rfl
      have z : ∀ (ρ : T) (j : Fin (r ρ)), pderiv (⟨ρ, (j, Fin.castAdd n₂ x)⟩ : Formalism.L2.Pj.Letter T r (n₁ + n₂))
          (rename (col (Fin.natAdd n₁)) P₂) = 0 :=
        fun ρ j => pderiv_rename_col_of_ne (fun y => (castAdd_ne_natAdd x y).symm) ρ j P₂
      rw [Derivation.leibniz, z, smul_zero, zero_add, smul_eq_mul, Derivation.leibniz, z, smul_zero,
        add_zero, smul_eq_mul, e1 τ i, e1 (cc τ) i', pderiv_rename (col_injective castAdd_inj'),
        pderiv_rename (col_injective castAdd_inj')]
    have hR : ∀ x : Fin n₂, pderiv (⟨τ, (i, Fin.natAdd n₁ x)⟩ : Formalism.L2.Pj.Letter T r (n₁ + n₂))
        (pderiv (⟨cc τ, (i', Fin.natAdd n₁ x)⟩ : Formalism.L2.Pj.Letter T r (n₁ + n₂))
          (rename (col (Fin.castAdd n₂)) P₁ * rename (col (Fin.natAdd n₁)) P₂)) =
        rename (col (Fin.castAdd n₂)) P₁ *
          rename (col (Fin.natAdd n₁)) (pderiv (⟨τ, (i, x)⟩ : Formalism.L2.Pj.Letter T r n₂)
            (pderiv ⟨cc τ, (i', x)⟩ P₂)) := by
      intro x
      have e1 : ∀ (ρ : T) (j : Fin (r ρ)), (⟨ρ, (j, Fin.natAdd n₁ x)⟩ : Formalism.L2.Pj.Letter T r (n₁ + n₂)) =
          col (Fin.natAdd n₁) ⟨ρ, (j, x)⟩ := fun _ _ => rfl
      have z : ∀ (ρ : T) (j : Fin (r ρ)), pderiv (⟨ρ, (j, Fin.natAdd n₁ x)⟩ : Formalism.L2.Pj.Letter T r (n₁ + n₂))
          (rename (col (Fin.castAdd n₂)) P₁) = 0 :=
        fun ρ j => pderiv_rename_col_of_ne (fun y => castAdd_ne_natAdd y x) ρ j P₁
      rw [Derivation.leibniz, z, smul_zero, add_zero, smul_eq_mul, Derivation.leibniz, z, smul_zero,
        add_zero, smul_eq_mul, e1 τ i, e1 (cc τ) i', pderiv_rename (col_injective natAdd_inj'),
        pderiv_rename (col_injective natAdd_inj')]
    rw [Finset.sum_congr rfl (fun x _ => hL x), Finset.sum_congr rfl (fun x _ => hR x),
      ← Finset.mul_sum, ← Finset.mul_sum, ← map_sum, ← map_sum, h₁H τ hτ i i', h₂H τ hτ i i',
      map_zero, map_zero, mul_zero, mul_zero, add_zero]
  · intro σ i i' hii' t
    rw [map_mul, rowShift_rename_col, rowShift_rename_col, h₁I σ i i' hii' t, h₂I σ i i' hii' t]
  · classical
    intro m hm σ i
    obtain ⟨m₁', hm₁, m₂', hm₂, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hm)
    rw [support_rename_of_injective (col_injective castAdd_inj')] at hm₁
    rw [support_rename_of_injective (col_injective natAdd_inj')] at hm₂
    obtain ⟨m₁, hn₁, rfl⟩ := Finset.mem_image.mp hm₁
    obtain ⟨m₂, hn₂, rfl⟩ := Finset.mem_image.mp hm₂
    rw [Fin.sum_univ_add]
    simp only [block_apply_left, block_apply_right]
    rw [h₁D m₁ hn₁ σ i, h₂D m₂ hn₂ σ i]

theorem totalDegree_rename_eq {σ τ : Type} {f : σ → τ} (hf : Function.Injective f) (P : MvPolynomial σ k) :
    (rename f P).totalDegree = P.totalDegree := by
  classical
  unfold totalDegree
  rw [support_rename_of_injective hf, Finset.sup_image]
  congr 1
  ext m
  simp only [Function.comp_apply]
  exact Finsupp.sum_mapDomain_index_inj hf

def pairing {σ S : Type} [CommRing S] [Algebra k S] (G : (σ →₀ ℕ) → S) : MvPolynomial σ k →+ S where
  toFun P := ∑ mo ∈ P.support, algebraMap k S (P.coeff mo) * G mo
  map_zero' := by simp
  map_add' P Q := by
    classical
    have h : ∀ (R : MvPolynomial σ k) (s : Finset (σ →₀ ℕ)), R.support ⊆ s →
        ∑ mo ∈ R.support, algebraMap k S (R.coeff mo) * G mo = ∑ mo ∈ s, algebraMap k S (R.coeff mo) * G mo :=
      fun R s hs => Finset.sum_subset hs fun x _ hx => by rw [notMem_support_iff.1 hx, map_zero, zero_mul]
    rw [h _ _ support_add, h P (P.support ∪ Q.support) Finset.subset_union_left,
      h Q (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    simp only [coeff_add, map_add, add_mul]

theorem pairing_monomial {σ S : Type} [CommRing S] [Algebra k S] (G : (σ →₀ ℕ) → S) (mo : σ →₀ ℕ) (a : k) :
    pairing G (monomial mo a) = algebraMap k S a * G mo := by
  classical
  by_cases ha : a = 0
  · subst ha; simp [pairing]
  · simp [pairing, support_monomial, ha, coeff_monomial]

theorem pairing_mul {σ₁ σ₂ σ S : Type} [CommRing S] [Algebra k S] (f₁ : σ₁ → σ) (f₂ : σ₂ → σ)
    (G₁ : (σ₁ →₀ ℕ) → S) (G₂ : (σ₂ →₀ ℕ) → S) (G : (σ →₀ ℕ) → S)
    (hG : ∀ m₁ m₂, G (m₁.mapDomain f₁ + m₂.mapDomain f₂) = G₁ m₁ * G₂ m₂)
    (P₁ : MvPolynomial σ₁ k) (P₂ : MvPolynomial σ₂ k) :
    pairing G (rename f₁ P₁ * rename f₂ P₂) = pairing G₁ P₁ * pairing G₂ P₂ := by
  classical
  refine MvPolynomial.induction_on' P₁ ?_ ?_
  · intro m₁ a
    refine MvPolynomial.induction_on' P₂ ?_ ?_
    · intro m₂ b
      rw [rename_monomial, rename_monomial, monomial_mul, pairing_monomial, pairing_monomial,
        pairing_monomial, hG, map_mul]
      ring
    · intro p q hp hq
      rw [map_add, mul_add, map_add, hp, hq, map_add, mul_add]
  · intro p q hp hq
    rw [map_add, add_mul, map_add, hp, hq, map_add, add_mul]

end Poly

section Index

theorem index_block {V : Type} [AddCommGroup V] {n₁ n₂ : ℕ} (A₁ B₁ : AddSubgroup (Fin n₁ → V))
    (A₂ B₂ : AddSubgroup (Fin n₂ → V)) (A B : AddSubgroup (Fin (n₁ + n₂) → V))
    (hA : ∀ v, v ∈ A ↔ (fun j => v (Fin.castAdd n₂ j)) ∈ A₁ ∧ (fun j => v (Fin.natAdd n₁ j)) ∈ A₂)
    (hB : ∀ v, v ∈ B ↔ (fun j => v (Fin.castAdd n₂ j)) ∈ B₁ ∧ (fun j => v (Fin.natAdd n₁ j)) ∈ B₂) :
    (A.addSubgroupOf B).index = (A₁.addSubgroupOf B₁).index * (A₂.addSubgroupOf B₂).index := by
  let e : (Fin (n₁ + n₂) → V) →+ (Fin n₁ → V) × (Fin n₂ → V) :=
    { toFun := fun v => (fun j => v (Fin.castAdd n₂ j), fun j => v (Fin.natAdd n₁ j))
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have he : Function.Surjective e := by
    rintro ⟨u₁, u₂⟩
    refine ⟨Fin.append u₁ u₂, ?_⟩
    simp [e, Fin.append_left, Fin.append_right]
  have hA' : A = (A₁.prod A₂).comap e := by
    ext v; simp [hA, AddSubgroup.mem_prod, e]
  have hB' : B = (B₁.prod B₂).comap e := by
    ext v; simp [hB, AddSubgroup.mem_prod, e]
  have key := AddSubgroup.relIndex_comap (A₁.prod A₂) e B
  rw [hA']
  show (AddSubgroup.comap e (A₁.prod A₂)).relIndex B = A₁.relIndex B₁ * A₂.relIndex B₂
  rw [key, hB', AddSubgroup.map_comap_eq_self_of_surjective he]
  rw [AddSubgroup.relIndex, AddSubgroup.relIndex, AddSubgroup.relIndex]
  have hc : (A₁.prod A₂).addSubgroupOf (B₁.prod B₂) =
      ((A₁.addSubgroupOf B₁).prod (A₂.addSubgroupOf B₂)).comap (B₁.prodEquiv B₂).toAddMonoidHom := by
    ext ⟨x, hx⟩
    simp [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_prod, AddSubgroup.prodEquiv]
    exact Iff.rfl
  rw [hc, AddSubgroup.index_comap_of_surjective _ (B₁.prodEquiv B₂).surjective, AddSubgroup.index_prod]

variable {E : Type} [Field E] [NumberField E] {n₁ n₂ : ℕ}

omit [NumberField E] in
theorem mem_span_smul_iff {n : ℕ} (a : 𝓞 E) (M : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E) :
    v ∈ Ideal.span {a} • M ↔ ∃ u ∈ M, a • u = v := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]

theorem mem_smul_std_block (a : 𝓞 E) (v : Fin (n₁ + n₂) → E) :
    v ∈ Ideal.span {a} • stdLat E (n₁ + n₂) ↔ (fun j => v (Fin.castAdd n₂ j)) ∈ Ideal.span {a} • stdLat E n₁ ∧
      (fun j => v (Fin.natAdd n₁ j)) ∈ Ideal.span {a} • stdLat E n₂ := by
  simp only [mem_span_smul_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [GlobalTheory.ShortLawsCompare.mem_std_block] at hu
    exact ⟨⟨_, hu.1, rfl⟩, ⟨_, hu.2, rfl⟩⟩
  · rintro ⟨⟨u₁, hu₁, h₁⟩, ⟨u₂, hu₂, h₂⟩⟩
    refine ⟨Fin.append u₁ u₂, ?_, ?_⟩
    · rw [GlobalTheory.ShortLawsCompare.mem_std_block]
      simpa [Fin.append_left, Fin.append_right] using And.intro hu₁ hu₂
    · funext j
      refine Fin.addCases (fun x => ?_) (fun y => ?_) j
      · have := congrFun h₁ x
        simpa [Fin.append_left] using this
      · have := congrFun h₂ y
        simpa [Fin.append_right] using this

theorem zCard_block (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (N r : ℕ) :
    (BlockLatticeAdmissibility.blockLat Λ₁ Λ₂).zCard N r = Λ₁.zCard N r * Λ₂.zCard N r := by
  unfold GenLat.zCard
  rw [← mul_pow]
  congr 1
  apply index_block
  · intro v
    simp only [Submodule.mem_toAddSubgroup]
    exact mem_smul_std_block _ v
  · intro v
    simp only [Submodule.mem_toAddSubgroup]
    exact Iff.rfl

theorem mIdx_block (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (N r : ℕ) :
    (BlockLatticeAdmissibility.blockLat Λ₁ Λ₂).mIdx N r = Λ₁.mIdx N r * Λ₂.mIdx N r := by
  unfold GenLat.mIdx GenLat.Ln
  rw [← mul_pow]
  congr 1
  apply index_block
  · intro v
    simp only [Submodule.mem_toAddSubgroup]
    exact mem_smul_std_block _ v
  · intro v
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_inf, GlobalTheory.ShortLawsCompare.mem_std_block]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩

end Index

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem rename_mem_symO {n m : ℕ} (g : Fin n → Fin m) (Λ : GenLat E n) (Λ' : GenLat E m)
    (h : ∀ b ∈ Λ.La, ∃ b' ∈ Λ'.La, ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)),
      rename (col g) (letB c σ i b) = letB c σ i b')
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ symO c Λ) : rename (col g) P ∈ symO (Dw := Dw) c Λ' := by
  unfold symO at *
  induction hP using Subring.closure_induction with
  | mem x hx =>
    apply Subring.subset_closure
    rcases hx with ⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩
    · left
      exact ⟨o, by simp⟩
    · right
      obtain ⟨b', hb', e⟩ := h b hb
      exact ⟨σ, i, b', hb', e σ i⟩
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem blockPoly_mem_harmL {n₁ n₂ : ℕ} {Λ₁ : GenLat E n₁} {Λ₂ : GenLat E n₂} {a₁ a₂ : (E →+* ℂ) × ℕ → ℕ}
    {P₁ : MvPolynomial (LtN Dw n₁) c.F} {P₂ : MvPolynomial (LtN Dw n₂) c.F}
    (h₁ : P₁ ∈ harmL c Λ₁ a₁) (h₂ : P₂ ∈ harmL c Λ₂ a₂) :
    BlockLatticeAdmissibility.blockPoly P₁ P₂ ∈ harmL c (BlockLatticeAdmissibility.blockLat Λ₁ Λ₂) (a₁ + a₂) := by
  refine ⟨mul_mem_HHa _ _ h₁.1 h₂.1, ?_⟩
  unfold BlockLatticeAdmissibility.blockPoly
  apply mul_mem
  · refine rename_mem_symO (Fin.castAdd n₂) Λ₁ _ ?_ h₁.2
    intro b hb
    refine ⟨Fin.append b 0, ?_, ?_⟩
    · unfold BlockLatticeAdmissibility.blockLat
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [Submodule.mem_comap]
        convert hb using 1
        funext j
        simp [LinearMap.funLeft_apply, Fin.append_left]
      · rw [Submodule.mem_comap]
        convert Λ₂.La.zero_mem using 1
        funext j
        simp [LinearMap.funLeft_apply, Fin.append_right]
    · intro σ i
      unfold letB
      simp only [map_sum, map_mul, rename_C, rename_X]
      rw [Fin.sum_univ_add]
      simp [Fin.append_left, Fin.append_right, col]
  · refine rename_mem_symO (Fin.natAdd n₁) Λ₂ _ ?_ h₂.2
    intro b hb
    refine ⟨Fin.append 0 b, ?_, ?_⟩
    · unfold BlockLatticeAdmissibility.blockLat
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [Submodule.mem_comap]
        convert Λ₁.La.zero_mem using 1
        funext j
        simp [LinearMap.funLeft_apply, Fin.append_left]
      · rw [Submodule.mem_comap]
        convert hb using 1
        funext j
        simp [LinearMap.funLeft_apply, Fin.append_right]
    · intro σ i
      unfold letB
      simp only [map_sum, map_mul, rename_C, rename_X]
      rw [Fin.sum_univ_add]
      simp [Fin.append_left, Fin.append_right, col]

theorem inZh_row {n : ℕ} {Λ : GenLat E n} {N : ℕ} {T : Over Xo.X} {a : Fin n → (T ⟶ Xo.univ.t.G)}
    (ha : InZh Xo Λ N a) (ρ : Fin n → E) (hρ : ∀ v ∈ Λ.La, ρ ⬝ᵥ v ∈ (1 : Submodule (𝓞 E) E))
    (cm : Fin n → 𝓞 E) (hcm : ∀ j, (cm j : E) = (N : E) * ρ j) :
    ∏ j, a j ≫ Xo.univ.t.act.act (cm j) = 1 := by
  unfold InZh at ha
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have key := ha.2 (Matrix.of fun _ j => ρ j) ?_ (fun _ j => cm j) (fun i j => by simp [hcm]) ⟨0, hn⟩
    · rw [List.prod_ofFn] at key
      simpa using key
    · intro v hv
      unfold stdLat
      rw [Submodule.mem_pi]
      intro i _
      exact hρ v hv

theorem inZh_append {n₁ n₂ : ℕ} {Λ₁ : GenLat E n₁} {Λ₂ : GenLat E n₂} {N : ℕ} {T : Over Xo.X}
    {a₁ : Fin n₁ → (T ⟶ Xo.univ.t.G)} {a₂ : Fin n₂ → (T ⟶ Xo.univ.t.G)}
    (h₁ : InZh Xo Λ₁ N a₁) (h₂ : InZh Xo Λ₂ N a₂) : InZh Xo (BlockLatticeAdmissibility.blockLat Λ₁ Λ₂) N (Fin.append a₁ a₂) := by
  have h₁' := h₁
  have h₂' := h₂
  unfold InZh at *
  refine ⟨?_, ?_⟩
  · intro b
    refine Fin.addCases (fun j => ?_) (fun j => ?_) b
    · rw [Fin.append_left]; exact h₁.1 j
    · rw [Fin.append_right]; exact h₂.1 j
  · intro mu hmu cm hcm i
    rw [List.prod_ofFn, Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have e1 : ∏ j : Fin n₁, a₁ j ≫ Xo.univ.t.act.act (cm i (Fin.castAdd n₂ j)) = 1 := by
      refine inZh_row h₁' (fun j => mu i (Fin.castAdd n₂ j)) ?_ (fun j => cm i (Fin.castAdd n₂ j)) (fun j => hcm i _)
      intro v hv
      have hv' : (Fin.append v 0 : Fin (n₁ + n₂) → E) ∈ (BlockLatticeAdmissibility.blockLat Λ₁ Λ₂).La := by
          unfold BlockLatticeAdmissibility.blockLat
          refine Submodule.mem_inf.2 ⟨?_, ?_⟩
          · rw [Submodule.mem_comap]
            convert hv using 1
            funext j
            simp [LinearMap.funLeft_apply, Fin.append_left]
          · rw [Submodule.mem_comap]
            convert Λ₂.La.zero_mem using 1
            funext j
            simp [LinearMap.funLeft_apply, Fin.append_right]
      have hm := hmu _ hv'
      unfold stdLat at hm
      rw [Submodule.mem_pi] at hm
      have hi := hm i (Set.mem_univ _)
      convert hi using 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    have e2 : ∏ j : Fin n₂, a₂ j ≫ Xo.univ.t.act.act (cm i (Fin.natAdd n₁ j)) = 1 := by
      refine inZh_row h₂' (fun j => mu i (Fin.natAdd n₁ j)) ?_ (fun j => cm i (Fin.natAdd n₁ j)) (fun j => hcm i _)
      intro v hv
      have hv' : (Fin.append 0 v : Fin (n₁ + n₂) → E) ∈ (BlockLatticeAdmissibility.blockLat Λ₁ Λ₂).La := by
          unfold BlockLatticeAdmissibility.blockLat
          refine Submodule.mem_inf.2 ⟨?_, ?_⟩
          · rw [Submodule.mem_comap]
            convert Λ₁.La.zero_mem using 1
            funext j
            simp [LinearMap.funLeft_apply, Fin.append_left]
          · rw [Submodule.mem_comap]
            convert hv using 1
            funext j
            simp [LinearMap.funLeft_apply, Fin.append_right]
      have hm := hmu _ hv'
      unfold stdLat at hm
      rw [Submodule.mem_pi] at hm
      have hi := hm i (Set.mem_univ _)
      convert hi using 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    rw [e1, e2, _root_.one_mul]

theorem geoInj_append {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {n₁ n₂ : ℕ} {J J₁ J₂ : Type} (e : J ≃ J₁ × J₂)
    {z₁ : J₁ → Fin n₁ → (ptO Xo x ⟶ Xo.univ.t.G)} {z₂ : J₂ → Fin n₂ → (ptO Xo x ⟶ Xo.univ.t.G)}
    (h₁ : GeoInj Xo x z₁) (h₂ : GeoInj Xo x z₂) :
    GeoInj Xo x (fun i => Fin.append (z₁ (e i).1) (z₂ (e i).2)) := by
  unfold GeoInj at *
  intro k _ ψ g hg i i' hii
  have h1 := h₁ k ψ g hg
  have h2 := h₂ k ψ g hg
  apply e.injective
  apply Prod.ext
  · apply h1
    funext b
    have := congrFun hii (Fin.castAdd n₂ b)
    simpa [Fin.append_left] using this
  · apply h2
    funext b
    have := congrFun hii (Fin.natAdd n₁ b)
    simpa [Fin.append_right] using this

theorem sum_blockPoly {S : Type} [CommRing S] [Algebra c.F S] {n₁ n₂ : ℕ} {A : Type} (D : A → (Lt1 Dw →₀ ℕ) → S)
    (F₁ : Fin n₁ → A) (F₂ : Fin n₂ → A) (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F) :
    ∑ m ∈ (BlockLatticeAdmissibility.blockPoly P₁ P₂).support, algebraMap c.F S ((BlockLatticeAdmissibility.blockPoly P₁ P₂).coeff m) *
        ∏ b, D (Fin.append F₁ F₂ b) (colOf m b) =
      (∑ m ∈ P₁.support, algebraMap c.F S (P₁.coeff m) * ∏ b, D (F₁ b) (colOf m b)) *
        ∑ m ∈ P₂.support, algebraMap c.F S (P₂.coeff m) * ∏ b, D (F₂ b) (colOf m b) := by
  classical
  have hL : BlockLatticeAdmissibility.letL Dw n₁ n₂ = col (Fin.castAdd n₂) := rfl
  have hR : BlockLatticeAdmissibility.letR Dw n₁ n₂ = col (Fin.natAdd n₁) := rfl
  have key := pairing_mul (k := c.F) (S := S) (BlockLatticeAdmissibility.letL Dw n₁ n₂) (BlockLatticeAdmissibility.letR Dw n₁ n₂)
    (fun m => ∏ b, D (F₁ b) (colOf m b)) (fun m => ∏ b, D (F₂ b) (colOf m b))
    (fun m => ∏ b, D (Fin.append F₁ F₂ b) (colOf m b)) ?_ P₁ P₂
  · exact key
  · intro m₁ m₂
    rw [hL, hR, Fin.prod_univ_add]
    congr 1
    · refine Finset.prod_congr rfl (fun b _ => ?_)
      rw [Fin.append_left]
      congr 1
      ext ℓ
      unfold colOf
      simp only [Finsupp.coe_equivFunOnFinite_symm]
      exact block_apply_left m₁ m₂ ℓ.1 ℓ.2 b
    · refine Finset.prod_congr rfl (fun b _ => ?_)
      rw [Fin.append_right]
      congr 1
      ext ℓ
      unfold colOf
      simp only [Finsupp.coe_equivFunOnFinite_symm]
      exact block_apply_right m₁ m₂ ℓ.1 ℓ.2 b

theorem totalDegree_blockPoly {n₁ n₂ : ℕ} {P₁ : MvPolynomial (LtN Dw n₁) c.F} {P₂ : MvPolynomial (LtN Dw n₂) c.F}
    (h₁ : P₁ ≠ 0) (h₂ : P₂ ≠ 0) : (BlockLatticeAdmissibility.blockPoly P₁ P₂).totalDegree = P₁.totalDegree + P₂.totalDegree := by
  have hL : Function.Injective (BlockLatticeAdmissibility.letL Dw n₁ n₂) := col_injective castAdd_inj'
  have hR : Function.Injective (BlockLatticeAdmissibility.letR Dw n₁ n₂) := col_injective natAdd_inj'
  have h1' : rename (BlockLatticeAdmissibility.letL Dw n₁ n₂) P₁ ≠ 0 := fun h => h₁ (rename_injective _ hL (by rw [h, map_zero]))
  have h2' : rename (BlockLatticeAdmissibility.letR Dw n₁ n₂) P₂ ≠ 0 := fun h => h₂ (rename_injective _ hR (by rw [h, map_zero]))
  unfold BlockLatticeAdmissibility.blockPoly
  rw [totalDegree_mul_of_isDomain h1' h2', totalDegree_rename_eq hL, totalDegree_rename_eq hR]

theorem finsum_block {K S Q J J₁ J₂ : Type} [Field K] [CommRing S] [Algebra K S] [Finite Q] [Fintype J] [Fintype J₁]
    [Fintype J₂] (e : J ≃ J₁ × J₂) {n₁ n₂ : ℕ} (w₁ : (Fin n₁ → Q) → K) (w₂ : (Fin n₂ → Q) → K)
    (A₁ : (Fin n₁ → Q) → J₁ → S) (A₂ : (Fin n₂ → Q) → J₂ → S) :
    ∑ᶠ q : Fin (n₁ + n₂) → Q,
        algebraMap K S (w₁ (fun i => q (Fin.castAdd n₂ i)) * w₂ (fun j => q (Fin.natAdd n₁ j))) *
          ∑ i, A₁ (fun i => q (Fin.castAdd n₂ i)) (e i).1 * A₂ (fun j => q (Fin.natAdd n₁ j)) (e i).2 =
      (∑ᶠ q, algebraMap K S (w₁ q) * ∑ i, A₁ q i) * ∑ᶠ q, algebraMap K S (w₂ q) * ∑ i, A₂ q i := by
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  let eq : (Fin (n₁ + n₂) → Q) ≃ (Fin n₁ → Q) × (Fin n₂ → Q) :=
    { toFun := fun q => (fun i => q (Fin.castAdd n₂ i), fun j => q (Fin.natAdd n₁ j))
      invFun := fun p => Fin.append p.1 p.2
      left_inv := by
        intro q
        funext i
        refine Fin.addCases (fun i => ?_) (fun j => ?_) i
        · simp
        · simp
      right_inv := by
        intro p
        ext i <;> simp }
  refine Fintype.sum_equiv eq _ _ (fun q => ?_)
  simp only [eq, Equiv.coe_fn_mk]
  have hJ : ∀ (a : Fin n₁ → Q) (b : Fin n₂ → Q), ∑ i : J, A₁ a (e i).1 * A₂ b (e i).2 = (∑ i, A₁ a i) * ∑ j, A₂ b j := by
    intro a b
    rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [hJ, map_mul]
  ring

private theorem dualMap_comp_jet_harmonics {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) := by
  unfold dualMap
  ext x <;> simp

private theorem PPx_le_preimage {S T : Type} [CommRing S] [CommRing T] (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X)
    (pm : (Over.mk x' ⊗ Xo.univ.t.G).left ⟶ (Over.mk x ⊗ Xo.univ.t.G).left)
    (h : pm ≫ Over.Hom.left (snd (Over.mk x) Xo.univ.t.G) = Over.Hom.left (snd (Over.mk x') Xo.univ.t.G))
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  unfold PPx LPow LB.LinComb
  dsimp only
  unfold LB.wchart
  intro p hp
  rw [← h] at hp
  simp only [Scheme.Hom.comp_base, TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage] at hp
  simpa using hp

private theorem frMap_comp' {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    [CommRing U] [Algebra c.F U] {φ : S →ₐ[c.F] T} {ψ : T →ₐ[c.F] U} {y : FrPt Xo c S} {y' : FrPt Xo c T}
    {y'' : FrPt Xo c U} (h₁ : FrMap φ y y') (h₂ : FrMap ψ y' y'') : FrMap (ψ.comp φ) y y'' := by
  obtain ⟨hx₁, hu₁, pm₁, hs₁, hf₁, ha₁⟩ := h₁
  obtain ⟨hx₂, hu₂, pm₂, hs₂, hf₂, ha₂⟩ := h₂
  refine ⟨?_, ?_, pm₂ ≫ pm₁, ?_, ?_, ?_⟩
  · rw [hx₂, hx₁, ← Category.assoc, FramedBaseChange.spMap_spMap]
    rfl
  · intro τ i
    rw [hu₂, hu₁, ← Category.assoc, FramedBaseChange.spMap_spMap, ← dualMap_comp_jet_harmonics]
    rfl
  · rw [Category.assoc, hs₁, hs₂]
  · rw [Category.assoc, hf₁, ← Category.assoc, hf₂, Category.assoc, FramedBaseChange.spMap_spMap]
    rfl
  · intro i h
    have e₁ := PPx_le_preimage y.x y'.x pm₁ hs₁ i
    have e₂ := PPx_le_preimage y'.x y''.x pm₂ hs₂ i
    rw [← Scheme.Hom.appLE_comp_appLE pm₂ pm₁ _ _ _ e₁ e₂, CommRingCat.hom_comp, RingHom.comp_apply,
      ha₁ i e₁, ha₂ i e₂]

private theorem frMap_cancel' {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    [CommRing U] [Algebra c.F U] {φ : S →ₐ[c.F] T} {ψ : T →ₐ[c.F] U} {y : FrPt Xo c S} {y' : FrPt Xo c T}
    {y'' : FrPt Xo c U} (h₁ : FrMap φ y y') (h₂ : FrMap (ψ.comp φ) y y'') : FrMap ψ y' y'' := by
  obtain ⟨hx₁, hu₁, pm₁, hs₁, hf₁, ha₁⟩ := h₁
  obtain ⟨hx₂, hu₂, pm₂, hs₂, hf₂, ha₂⟩ := h₂
  have hx : y''.x = spMap ψ.toRingHom ≫ y'.x := by
    rw [hx₂, hx₁, ← Category.assoc, FramedBaseChange.spMap_spMap]
    rfl
  refine ⟨hx, ?_, ?_⟩
  · intro τ i
    rw [hu₂, hu₁, ← Category.assoc, FramedBaseChange.spMap_spMap, ← dualMap_comp_jet_harmonics]
    rfl
  · have tf : ∀ {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X),
        Over.Hom.left (fst (Over.mk x) Xo.univ.t.G) = Limits.pullback.fst x Xo.univ.t.G.hom := fun _ => rfl
    have ts : ∀ {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X),
        Over.Hom.left (snd (Over.mk x) Xo.univ.t.G) = Limits.pullback.snd x Xo.univ.t.G.hom := fun _ => rfl
    rw [tf, tf] at hf₁ hf₂
    rw [ts, ts] at hs₁ hs₂
    let pm : Gx y''.x ⟶ Gx y'.x := Limits.pullback.lift
      (Limits.pullback.fst y''.x Xo.univ.t.G.hom ≫ spMap ψ.toRingHom) (Limits.pullback.snd y''.x Xo.univ.t.G.hom)
      (by
        change (Limits.pullback.fst y''.x Xo.univ.t.G.hom ≫ spMap ψ.toRingHom) ≫ y'.x = _
        rw [Category.assoc, ← hx]
        exact Limits.pullback.condition)
    have hsn : pm ≫ Limits.pullback.snd y'.x Xo.univ.t.G.hom = Limits.pullback.snd y''.x Xo.univ.t.G.hom :=
      Limits.pullback.lift_snd _ _ _
    have hfn : pm ≫ Limits.pullback.fst y'.x Xo.univ.t.G.hom =
        Limits.pullback.fst y''.x Xo.univ.t.G.hom ≫ spMap ψ.toRingHom :=
      Limits.pullback.lift_fst _ _ _
    have hpm : pm ≫ pm₁ = pm₂ := by
      apply Limits.pullback.hom_ext
      · simp only [Over.mk_hom]
        rw [Category.assoc, hf₁, ← Category.assoc, hfn, Category.assoc, FramedBaseChange.spMap_spMap, hf₂]
        rfl
      · simp only [Over.mk_hom]
        rw [Category.assoc, hs₁, hsn, hs₂]
    refine ⟨pm, ?_, ?_, ?_⟩
    · rw [ts, ts]
      exact hsn
    · rw [tf, tf]
      exact hfn
    · intro i h
      have e₁ := PPx_le_preimage y.x y'.x pm₁ (by rw [ts, ts]; exact hs₁) i
      have e₂ := PPx_le_preimage y.x y''.x pm₂ (by rw [ts, ts]; exact hs₂) i
      rw [← ha₁ i e₁, ← ha₂ i e₂, ← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
      have key : ∀ (g : Gx y''.x ⟶ Gx y.x) (hg : g = pm₂) (hh : (PPx y''.x).U i ≤ g ⁻¹ᵁ (PPx y.x).U i),
          (Scheme.Hom.appLE g ((PPx y.x).U i) ((PPx y''.x).U i) hh).hom (y.s.f i) =
            (Scheme.Hom.appLE pm₂ ((PPx y.x).U i) ((PPx y''.x).U i) e₂).hom (y.s.f i) := by
        rintro g rfl hh
        rfl
      exact key _ hpm _

private theorem exists_faithfullyFlat_refinement {S S₁ S₂ : Type} [CommRing S] [Algebra c.F S] [CommRing S₁] [Algebra c.F S₁]
    [CommRing S₂] [Algebra c.F S₂] (φ₁ : S →ₐ[c.F] S₁) (φ₂ : S →ₐ[c.F] S₂) (h₁ : φ₁.FaithfullyFlat)
    (h₂ : φ₂.FaithfullyFlat) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra c.F T) (ψ₁ : S₁ →ₐ[c.F] T) (ψ₂ : S₂ →ₐ[c.F] T),
      ψ₁.comp φ₁ = ψ₂.comp φ₂ ∧ (ψ₁.comp φ₁).FaithfullyFlat := by
  let _ : Algebra S S₁ := φ₁.toRingHom.toAlgebra
  let _ : Algebra S S₂ := φ₂.toRingHom.toAlgebra
  have _ : Module.FaithfullyFlat S S₁ := h₁
  have _ : Module.FaithfullyFlat S S₂ := h₂
  let _ : Algebra c.F (TensorProduct S S₁ S₂) :=
    ((algebraMap S (TensorProduct S S₁ S₂)).comp (algebraMap c.F S)).toAlgebra
  have hl : ∀ s : S, (φ₁ s ⊗ₜ[S] (1 : S₂)) = algebraMap S (TensorProduct S S₁ S₂) s := fun s =>
    (Algebra.TensorProduct.algebraMap_apply s).symm
  have hr : ∀ s : S, ((1 : S₁) ⊗ₜ[S] φ₂ s) = algebraMap S (TensorProduct S S₁ S₂) s := fun s =>
    (Algebra.TensorProduct.algebraMap_apply' s).symm
  let ψ₁ : S₁ →ₐ[c.F] TensorProduct S S₁ S₂ :=
    { Algebra.TensorProduct.includeLeftRingHom with
      commutes' := fun r => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
          Algebra.TensorProduct.includeLeftRingHom_apply]
        rw [← φ₁.commutes r, hl]
        rfl }
  let ψ₂ : S₂ →ₐ[c.F] TensorProduct S S₁ S₂ :=
    { (Algebra.TensorProduct.includeRight : S₂ →ₐ[S] TensorProduct S S₁ S₂).toRingHom with
      commutes' := fun r => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
        rw [← φ₂.commutes r, hr]
        rfl }
  have heq : ψ₁.comp φ₁ = ψ₂.comp φ₂ := by
    ext s
    change φ₁ s ⊗ₜ[S] (1 : S₂) = (1 : S₁) ⊗ₜ[S] φ₂ s
    rw [hl, hr]
  refine ⟨TensorProduct S S₁ S₂, inferInstance, inferInstance, ψ₁, ψ₂, heq, ?_⟩
  have hc : (ψ₁.comp φ₁).toRingHom = algebraMap S (TensorProduct S S₁ S₂) := by
    ext s
    exact hl s
  change RingHom.FaithfullyFlat (ψ₁.comp φ₁).toRingHom
  rw [hc, RingHom.faithfullyFlat_algebraMap_iff]
  exact Module.FaithfullyFlat.trans S S₁ (TensorProduct S S₁ S₂)

theorem shortValAt_mul (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab : NabV Xo c) (hn : IsNab Xo c nab)
    {n₁ n₂ : ℕ} {Λ₁ : GenLat E n₁} {Λ₂ : GenLat E n₂} {N : ℕ} {a₁ a₂ : (E →+* ℂ) × ℕ → ℕ}
    {P₁ : MvPolynomial (LtN Dw n₁) c.F} {P₂ : MvPolynomial (LtN Dw n₂) c.F}
    (p₁ : P₁ ∈ harmL c Λ₁ a₁) (p₂ : P₂ ∈ harmL c Λ₂ a₂)
    (w₁ : (Fin n₁ → LevQ Dw l) → c.F) (w₂ : (Fin n₂ → LevQ Dw l) → c.F)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {v₁ v₂ : S}
    (h₁ : ShortValAt Xo c nab w₁ Λ₁ 1 N P₁ y v₁) (h₂ : ShortValAt Xo c nab w₂ Λ₂ 1 N P₂ y v₂) :
    ShortValAt Xo c nab (BlockLatticeAdmissibility.blockDat w₁ w₂) (BlockLatticeAdmissibility.blockLat Λ₁ Λ₂) 1 N (BlockLatticeAdmissibility.blockPoly P₁ P₂) y (v₁ * v₂) := by
  have hH₁ : P₁ ∈ HHa Dw.mult n₁ c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a₁ (τ, i)) := by
    unfold harmL at p₁
    exact p₁.1
  have hH₂ : P₂ ∈ HHa Dw.mult n₂ c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a₂ (τ, i)) := by
    unfold harmL at p₂
    exact p₂.1
  unfold ShortValAt at h₁ h₂
  obtain ⟨S₁, _, _, φ₁, y₁, z₁, tp₁, F₁, hφ₁, hm₁, hz₁, hg₁, ht₁, hF₁, hv₁⟩ := h₁
  obtain ⟨S₂, _, _, φ₂, y₂, z₂, tp₂, F₂, hφ₂, hm₂, hz₂, hg₂, ht₂, hF₂, hv₂⟩ := h₂
  obtain ⟨T, _, _, ψ₁, ψ₂, heq, hff⟩ := exists_faithfullyFlat_refinement φ₁ φ₂ hφ₁ hφ₂
  obtain ⟨yT, hyT⟩ := FramedBaseChange.exists_frMap abelianSchemeLaws_all.1 E H Dw l Xo c S₁ T ψ₁ y₁
  have hmT : FrMap (ψ₁.comp φ₁) y yT := frMap_comp' hm₁ hyT
  have hyT₂ : FrMap ψ₂ y₂ yT := frMap_cancel' hm₂ (heq ▸ hmT)
  obtain ⟨z₁', tp₁', F₁', hz₁', hg₁', ht₁', hF₁', hs₁'⟩ :=
    ShortCompare.exists_pull hC nab hn Λ₁ N a₁ P₁ hH₁ ψ₁ y₁ yT hyT z₁ tp₁ F₁ hz₁ hg₁ ht₁ hF₁
  obtain ⟨z₂', tp₂', F₂', hz₂', hg₂', ht₂', hF₂', hs₂'⟩ :=
    ShortCompare.exists_pull hC nab hn Λ₂ N a₂ P₂ hH₂ ψ₂ y₂ yT hyT₂ z₂ tp₂ F₂ hz₂ hg₂ ht₂ hF₂
  have hzc := zCard_block Λ₁ Λ₂ N (Dw.p + Dw.q)
  let e : Fin ((BlockLatticeAdmissibility.blockLat Λ₁ Λ₂).zCard N (Dw.p + Dw.q)) ≃
      Fin (Λ₁.zCard N (Dw.p + Dw.q)) × Fin (Λ₂.zCard N (Dw.p + Dw.q)) :=
    (finCongr hzc).trans finProdFinEquiv.symm
  unfold ShortValAt
  refine ⟨T, inferInstance, inferInstance, ψ₁.comp φ₁, yT,
    fun i => Fin.append (z₁' (e i).1) (z₂' (e i).2),
    fun q => Fin.append (tp₁' (fun j => q (Fin.castAdd n₂ j))) (tp₂' (fun j => q (Fin.natAdd n₁ j))),
    fun q i => Fin.append (F₁' (fun j => q (Fin.castAdd n₂ j)) (e i).1) (F₂' (fun j => q (Fin.natAdd n₁ j)) (e i).2),
    hff, hmT, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact inZh_append (hz₁' _) (hz₂' _)
  · exact geoInj_append e hg₁' hg₂'
  · intro q b
    refine Fin.addCases (fun j => ?_) (fun j => ?_) b
    · simp only [Fin.append_left]
      exact ht₁' _ j
    · simp only [Fin.append_right]
      exact ht₂' _ j
  · intro q i b
    refine Fin.addCases (fun j => ?_) (fun j => ?_) b
    · simp only [Fin.append_left]
      exact hF₁' _ _ j
    · simp only [Fin.append_right]
      exact hF₂' _ _ j
  · have hψφ : ∀ s, (ψ₁.comp φ₁) s = ψ₁ (φ₁ s) := fun s => rfl
    have hψφ₂ : ∀ s, ψ₁ (φ₁ s) = ψ₂ (φ₂ s) := fun s => by rw [← hψφ, heq]; rfl
    rw [map_mul, hψφ, hψφ, hψφ₂ v₂, hv₁, hv₂]
    have fin₁ := GlobalTheory.ShortValue.finite_levelQuotient Dw l
    simp only [map_mul ψ₁, map_mul ψ₂, AlgHom.commutes]
    rw [map_finsum ψ₁ (Set.toFinite _), map_finsum ψ₂ (Set.toFinite _)]
    simp only [map_mul ψ₁, map_mul ψ₂, AlgHom.commutes, hs₁', hs₂']
    have key : ∀ (q : Fin (n₁ + n₂) → LevQ Dw l) (i : Fin ((BlockLatticeAdmissibility.blockLat Λ₁ Λ₂).zCard N (Dw.p + Dw.q))),
        (∑ m ∈ (BlockLatticeAdmissibility.blockPoly P₁ P₂).support, algebraMap c.F T ((BlockLatticeAdmissibility.blockPoly P₁ P₂).coeff m) *
          ∏ b, nab yT ((N : ℤ) ^ 2) (Fin.append (F₁' (fun j => q (Fin.castAdd n₂ j)) (e i).1)
            (F₂' (fun j => q (Fin.natAdd n₁ j)) (e i).2) b) (colOf m b)) =
        (∑ m ∈ P₁.support, algebraMap c.F T (P₁.coeff m) *
          ∏ b, nab yT ((N : ℤ) ^ 2) (F₁' (fun j => q (Fin.castAdd n₂ j)) (e i).1 b) (colOf m b)) *
        ∑ m ∈ P₂.support, algebraMap c.F T (P₂.coeff m) *
          ∏ b, nab yT ((N : ℤ) ^ 2) (F₂' (fun j => q (Fin.natAdd n₁ j)) (e i).2 b) (colOf m b) :=
      fun q i => sum_blockPoly (fun F m => nab yT ((N : ℤ) ^ 2) F m) _ _ P₁ P₂
    simp only [key, BlockLatticeAdmissibility.blockDat]
    have hfb := finsum_block (K := c.F) (S := T) e w₁ w₂
      (fun q j => ∑ m ∈ P₁.support, algebraMap c.F T (P₁.coeff m) * ∏ b, nab yT ((N : ℤ) ^ 2) (F₁' q j b) (colOf m b))
      (fun q j => ∑ m ∈ P₂.support, algebraMap c.F T (P₂.coeff m) * ∏ b, nab yT ((N : ℤ) ^ 2) (F₂' q j b) (colOf m b))
    beta_reduce at hfb
    rw [hfb]
    by_cases h0 : P₁ = 0 ∨ P₂ = 0
    · rcases h0 with h0 | h0 <;> subst h0 <;> simp
    · simp only [not_or] at h0
      have hcard : Nat.card (Fin (n₁ + n₂) → LevQ Dw l) =
          Nat.card (Fin n₁ → LevQ Dw l) * Nat.card (Fin n₂ → LevQ Dw l) := by
        simp [Nat.card_fun, pow_add]
      rw [totalDegree_blockPoly h0.1 h0.2, mIdx_block, hcard]
      simp only [map_mul, Nat.cast_mul, pow_add, mul_inv, inv_one, map_one]
      ring

end GlobalTheory.ShortBlock

namespace GlobalTheory

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem shortSeries_blockProduct : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ bad : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.BlockProduct Xo c nab bad := by
  intro hC E _ _ _ H Dw l Xo c _ nab hn bad n₁ n₂ Λ₁ Λ₂ h₁ h₂ N k₁ k₂
  have hA : IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.LatAdm l bad (IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.blockLat Λ₁ Λ₂) := by
    rw [ShortLawsCompare.latAdm_iff, ShortLawsCompare.blockLat_eq]
    exact ShortLawsCompare.latOK_block ((ShortLawsCompare.latAdm_iff bad Λ₁).1 h₁)
      ((ShortLawsCompare.latAdm_iff bad Λ₂).1 h₂)
  have hK : (IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.blockLat Λ₁ Λ₂).LevOK N l.M := by
    rw [ShortLawsCompare.blockLat_eq]
    exact ShortLawsCompare.levOK_block k₁ k₂
  refine ⟨⟨hA, hK⟩, fun a₁ a₂ P₁ P₂ p₁ p₂ => ⟨ShortBlock.blockPoly_mem_harmL p₁ p₂, ?_⟩⟩
  intro w₁ w₂ S _ _ y v₁ v₂ v s₁ s₂
  have hm := ShortBlock.shortValAt_mul hC nab hn p₁ p₂ w₁ w₂ y s₁ s₂
  constructor
  · intro hv
    have hP := ShortBlock.blockPoly_mem_harmL p₁ p₂
    exact ((shortThetaValue_existsUnique_natural abelianSchemeLaws_all.1 hC E H Dw l Xo c nab hn (n₁ + n₂)
      (IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.blockLat Λ₁ Λ₂) N hA.1 hA.2.2 hK (a₁ + a₂) _ hP.1 (IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.blockDat w₁ w₂) 1).1 S y).unique hv hm
  · rintro rfl
    exact hm

end GlobalTheory
