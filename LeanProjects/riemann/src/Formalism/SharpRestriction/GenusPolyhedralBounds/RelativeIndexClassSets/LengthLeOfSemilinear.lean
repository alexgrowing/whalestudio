import Formalism.FilteredPoleLength.LocalDescentLevels.LocalStepClosed
import Formalism.FilteredPoleLength.LocalDescentLevels.LocalStepDescent

noncomputable section

namespace Formalism.MainNotions.Gaps.T0

open Module Formalism.LatticeBaseChangeAlt Formalism.LatticeBaseChangeAlt.BQuot

section General

variable {O V W : Type*} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]

theorem ql_map_le (A S : Submodule O V) (f : V →ₗ[O] W) (P : Submodule O W) (h : S.map f ≤ P) :
    ql (A.map f) P ≤ ql A S := by
  let g : ↥A →ₗ[O] (↥(A.map f) ⧸ P.comap (A.map f).subtype) :=
    (P.comap (A.map f).subtype).mkQ ∘ₗ f.submoduleMap A
  have hk : S.comap A.subtype ≤ LinearMap.ker g := by
    intro x hx
    rw [LinearMap.mem_ker]
    show (P.comap (A.map f).subtype).mkQ (f.submoduleMap A x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h ⟨x, hx, rfl⟩
  refine Module.length_le_of_surjective ((S.comap A.subtype).liftQ g hk) ?_
  intro z
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨x, rfl⟩ := f.submoduleMap_surjective A z
  exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem ql_scaled_le (r : O) (M Mgg NK : Submodule O V) {n : ℕ} (th : Fin n → V) (h1 : Mgg ≤ M)
    (h2 : Mgg ≤ NK) :
    ql (M.map (r • (LinearMap.id : V →ₗ[O] V)))
        ((M.map (r • (LinearMap.id : V →ₗ[O] V)) ⊓ NK) ⊔
          Submodule.span O (Set.range fun j => r • th j)) ≤
      ql M (Mgg ⊔ Submodule.span O (Set.range th)) := by
  refine ql_map_le _ _ _ _ ?_
  rw [Submodule.map_sup]
  refine sup_le_sup ?_ ?_
  · refine le_inf (Submodule.map_mono h1) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact NK.smul_mem r (h2 hx)
  · rw [Submodule.map_span, ← Set.range_comp]
    exact le_of_eq rfl

end General

theorem length_quot_quot {O V : Type*} [CommRing O] [AddCommGroup V] [Module O V]
    (M Mgg : Submodule O V) {n : ℕ} (th : Fin n → V) (h1 : Mgg ≤ M) (h2 : ∀ j, th j ∈ M) :
    Module.length O ((↥M ⧸ Mgg.comap M.subtype) ⧸ Submodule.span O (Set.range fun j =>
        (Submodule.Quotient.mk ⟨th j, h2 j⟩ : ↥M ⧸ Mgg.comap M.subtype))) =
      Module.length O (↥M ⧸ (Mgg ⊔ Submodule.span O (Set.range th)).comap M.subtype) := by
  set S : Submodule O ↥M := Mgg.comap M.subtype with hS
  set T : Submodule O ↥M := Submodule.span O (Set.range fun j => (⟨th j, h2 j⟩ : ↥M)) with hT
  have e1 : Submodule.span O (Set.range fun j => (Submodule.Quotient.mk ⟨th j, h2 j⟩ : ↥M ⧸ S)) =
      T.map S.mkQ := by
    rw [hT, Submodule.map_span, ← Set.range_comp]
    rfl
  have hth : Submodule.span O (Set.range th) ≤ M := Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h2 j)
  have e2 : (Mgg ⊔ Submodule.span O (Set.range th)).comap M.subtype = S ⊔ T := by
    apply Submodule.map_injective_of_injective M.injective_subtype
    rw [Submodule.map_comap_subtype, Submodule.map_sup, hS, Submodule.map_comap_subtype, hT,
      Submodule.map_span, ← Set.range_comp, inf_eq_right.2 (sup_le h1 hth), inf_eq_right.2 h1]
    rfl
  rw [e1, e2]
  exact (Submodule.quotientQuotientEquivQuotientSup S T).length_eq

def LocalStepQ : Prop :=
  ∀ (O K V W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module O W]
    (ϖ : O), Irreducible ϖ → ∀ (M Θ N₁ Z Zm N' Mgg : Submodule O V) (e n q : ℕ) (th : Fin n → V)
    (AA AA' N₁' : Submodule O W) (ρ : ↥N' →ₗ[O] W),
    Formalism.LatticeIndexTer.IsLat O K V M → Formalism.LatticeIndexTer.IsLat O K V Θ →
    N₁ ⊔ Z ≤ Θ → (∀ j, th j ∈ M) → (∀ j, th j ∈ Θ) →
    Mgg ≤ M →
    Submodule.span K (Mgg : Set V) ≤ Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V) →
    Module.length O (↥M ⧸ (Mgg ⊔ Submodule.span O (Set.range th)).comap M.subtype) ≤ (q : ℕ∞) →
    M.map ((ϖ ^ e) • (LinearMap.id : V →ₗ[O] V)) ⊓
      (Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V)).restrictScalars O ≤ N' →
    N₁ ≤ N' → Z ≤ Zm → Zm ≤ N' → (∀ x, ρ x ∈ AA') →
    LinearMap.ker ρ = Zm.comap N'.subtype → (N₁.comap N'.subtype).map ρ = N₁' → N₁' ≤ AA →
    AA ≤ AA' →
    Module.length O (↥AA' ⧸ AA.comap AA'.subtype) ≠ ⊤ →
    Module.length O (↥AA ⧸ N₁'.comap AA.subtype) ≠ ⊤ →
    Module.length O (↥Zm ⧸ Z.comap Zm.subtype) ≠ ⊤ →
    ∀ V' : Submodule K V,
      Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) ≤
        (e : ℤ) * (finrank K V' : ℤ) +
          ((Module.length O (↥AA' ⧸ AA.comap AA'.subtype)).toNat : ℤ) +
          ((Module.length O (↥AA ⧸ N₁'.comap AA.subtype)).toNat : ℤ) +
          ((Module.length O (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℤ) + (q : ℤ)

theorem localStepQ : LocalStepQ := by
  intro O K V W _ _ _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ M Θ N₁ Z Zm N' Mgg e n q th AA AA' N₁'
    ρ hMl hΘl hNΘ _ hthΘ hgg hggK hq hXN hN₁ hZ hZm hρ hkρ himg _ _ hf1 hf2 hf3 V'
  set X : Submodule O V := M.map ((ϖ ^ e) • (LinearMap.id : V →ₗ[O] V)) with hX
  set NK : Submodule O V :=
    (Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V)).restrictScalars O with hNK
  have hsm : ∀ v : V, (algebraMap O K ϖ) ^ e • v = ϖ ^ e • v := by
    intro v
    rw [← map_pow, algebraMap_smul]
  have hIdx := Formalism.IncomingBounds.index_last_reduction_holds O K V ϖ hϖ (e : ℤ) M Θ hMl hΘl V'
  have hbridge : M.map ((((algebraMap O K ϖ) ^ (e : ℤ)) • LinearMap.id : V →ₗ[K] V).restrictScalars O)
      = X := by
    ext x
    simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq, zpow_natCast, X, LinearMap.smul_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, (hsm y).symm⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, hsm y⟩
  rw [hbridge] at hIdx
  let Tj : Submodule O V := Submodule.span O (Set.range fun j => ϖ ^ e • th j)
  have hTΘ : Tj ≤ Θ := Submodule.span_le.2 (by
    rintro _ ⟨j, rfl⟩
    exact Θ.smul_mem _ (hthΘ j))
  have hggNK : Mgg ≤ NK := fun x hx => hggK (Submodule.subset_span hx)
  have r1 := reduction X Θ (N₁ ⊔ Z) Tj NK hNΘ hTΘ
  have r2 := levels N' ((X ⊓ NK) ⊔ (N₁ ⊔ Z)) N₁ Z Zm AA AA' N₁' ρ
    (sup_le hXN (sup_le hN₁ (hZ.trans hZm))) hρ hkρ himg
  have r3 : ql X ((X ⊓ NK) ⊔ Tj) ≤ (q : ℕ∞) := (ql_scaled_le (ϖ ^ e) M Mgg NK th hgg hggNK).trans hq
  set L1 := Module.length O (↥AA' ⧸ AA.comap AA'.subtype)
  set L2 := Module.length O (↥AA ⧸ N₁'.comap AA.subtype)
  set L3 := Module.length O (↥Zm ⧸ Z.comap Zm.subtype)
  set L := Formalism.LatticeIndexTer.qlen O V (X ⊔ Θ) Θ with hL
  have hLA' : L ≤ L1 + L2 + L3 + ((q : ℕ) : ℕ∞) := r1.trans (add_le_add r2 r3)
  have hsum : L1 + L2 + L3 + ((q : ℕ) : ℕ∞) =
      ((L1.toNat + L2.toNat + L3.toNat + q : ℕ) : ℕ∞) := by
    rw [← ENat.natCast_toNat hf1, ← ENat.natCast_toNat hf2, ← ENat.natCast_toNat hf3]
    simp only [ENat.toNat_natCast]
    push_cast; rfl
  rw [hsum] at hLA'
  have hLt : L.toNat ≤ L1.toNat + L2.toNat + L3.toNat + q := by
    have hLne : L ≠ ⊤ := ne_top_of_le_ne_top (by simp) hLA'
    rw [← ENat.natCast_toNat hLne] at hLA'
    exact_mod_cast hLA'
  have h5 : ((L.toNat : ℕ) : ℤ) ≤ (L1.toNat : ℤ) + (L2.toNat : ℤ) + (L3.toNat : ℤ) + (q : ℤ) := by
    exact_mod_cast hLt
  linarith

def LocalStepLevelsQ : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T R I : ℕ),
    (∀ z, 1 ≤ ep z) → 1 ≤ T → 0 ≤ c' → (∀ z, 0 ≤ v z) → (∀ z, ν z ≤ νs + c' * v z) →
  ∀ (O K V W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module O W]
    (ϖ : O), Irreducible ϖ → ∀ (M Θ N₁ Z Zm N' Mgg : Submodule O V) (e n q : ℕ) (th : Fin n → V)
    (AA AA' N₁' : Submodule O W) (ρ : ↥N' →ₗ[O] W),
    Formalism.LatticeIndexTer.IsLat O K V M → Formalism.LatticeIndexTer.IsLat O K V Θ →
    N₁ ⊔ Z ≤ Θ → (∀ j, th j ∈ M) → (∀ j, th j ∈ Θ) →
    Mgg ≤ M →
    Submodule.span K (Mgg : Set V) ≤ Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V) →
    Module.length O (↥M ⧸ (Mgg ⊔ Submodule.span O (Set.range th)).comap M.subtype) ≤ (q : ℕ∞) →
    M.map ((ϖ ^ e) • (LinearMap.id : V →ₗ[O] V)) ⊓
      (Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V)).restrictScalars O ≤ N' →
    N₁ ≤ N' → Z ≤ Zm → Zm ≤ N' → (∀ x, ρ x ∈ AA') →
    LinearMap.ker ρ = Zm.comap N'.subtype → (N₁.comap N'.subtype).map ρ = N₁' → N₁' ≤ AA →
    AA ≤ AA' →
    Module.length O (↥Zm ⧸ Z.comap Zm.subtype) ≠ ⊤ →
    (((T : ℝ) * νs ≤ (e : ℝ) ∧ ∀ z, ∃ m : ℤ, (ep z : ℝ) * ν z = m) ∨ (T : ℝ) * νs + 1 ≤ (e : ℝ)) →
    Module.length O (↥AA' ⧸ AA.comap AA'.subtype) ≤
      ((R * ∑ z, (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat * f z : ℕ) : ℕ∞) →
    Module.length O (↥AA ⧸ N₁'.comap AA.subtype) ≤ ((R * I : ℕ) : ℕ∞) →
    ∀ V' : Submodule K V,
      (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
        (e : ℝ) * (finrank K V' : ℝ) +
            (R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) + (R : ℝ) * (I : ℝ) +
            ((Module.length O (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ) + (q : ℝ)

theorem localStepLevelsQ : LocalStepLevelsQ := by
  intro ι _ ep f ν v νs c' T R I hep hT hc hv hν O K V W _ _ _ _ _ _ _ _ _ _ _ _ _
    ϖ hϖ M Θ N₁ Z Zm N' Mgg e n q th AA AA' N₁' ρ hM hΘ h1 h2 h3 h4 h5 h6 h8 h9 h10
    h11 h12 h13 h14 h15 h16 h17 hcase hA hN V'
  have h := localStepQ O K V W ϖ hϖ M Θ N₁ Z Zm N' Mgg e n q th AA AA' N₁' ρ hM hΘ h1 h2 h3
    h4 h5 h6 h8 h9 h10 h11 h12 h13 h14 h15 h16
    (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hA) (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hN) h17 V'
  have hAn := ENat.toNat_le_of_le_natCast hA
  have hNn := ENat.toNat_le_of_le_natCast hN
  have hlev : ∑ z, ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - ((e : ℤ) : ℝ))⌉ : ℤ) : ℝ) * f z ≤
        T * c' * ∑ z, ((ep z : ℝ) * f z) * v z := by
    rcases hcase with h0 | h0
    · exact levelsChain ι ep f ν v νs c' T (e : ℤ) hep hT hc hv hν (Or.inl (by exact_mod_cast h0))
    · exact levelsChain_of_add_one_le ι ep f ν v νs c' T (e : ℤ) hep hT hc hv hν (by exact_mod_cast h0)
  simp only [Int.cast_natCast] at hlev
  have hsumcast : (((∑ z, (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat * f z : ℕ)) : ℝ) =
      ∑ z, ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉ : ℤ) : ℝ) * f z := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Nat.cast_mul]
    congr 1
    have h0 : (0 : ℤ) ≤ max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉ := le_max_left _ _
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  have hRnn : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have key : ((Module.length O (↥AA' ⧸ AA.comap AA'.subtype)).toNat : ℝ) ≤
      (R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) := by
    calc ((Module.length O (↥AA' ⧸ AA.comap AA'.subtype)).toNat : ℝ)
        ≤ ((R * ∑ z, (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat * f z : ℕ) : ℝ) := by
          exact_mod_cast hAn
      _ ≤ _ := by
          rw [Nat.cast_mul, hsumcast]
          exact mul_le_mul_of_nonneg_left hlev hRnn
  have key2 : ((Module.length O (↥AA ⧸ N₁'.comap AA.subtype)).toNat : ℝ) ≤ (R : ℝ) * (I : ℝ) := by
    exact_mod_cast hNn
  have hR : (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
      (e : ℝ) * (finrank K V' : ℝ) +
          ((Module.length O (↥AA' ⧸ AA.comap AA'.subtype)).toNat : ℝ) +
          ((Module.length O (↥AA ⧸ N₁'.comap AA.subtype)).toNat : ℝ) +
          ((Module.length O (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ) + (q : ℝ) := by
    exact_mod_cast h
  linarith

def LocalStepClosedQ : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T R I : ℕ),
    (∀ z, 1 ≤ ep z) → 1 ≤ T → 0 ≤ c' → (∀ z, 0 ≤ v z) → (∀ z, ν z ≤ νs + c' * v z) →
  ∀ (O K V W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module O W]
    (ϖ : O), Irreducible ϖ → ∀ (M Θ N₁ Z Zm N' Mgg : Submodule O V) (e n q : ℕ) (th : Fin n → V)
    (AA AA' N₁' : Submodule O W) (ρ : ↥N' →ₗ[O] W),
    Formalism.LatticeIndexTer.IsLat O K V M → Formalism.LatticeIndexTer.IsLat O K V Θ →
    N₁ ⊔ Z ≤ Θ → (∀ j, th j ∈ M) → (∀ j, th j ∈ Θ) →
    Mgg ≤ M →
    Submodule.span K (Mgg : Set V) ≤ Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V) →
    Module.length O (↥M ⧸ (Mgg ⊔ Submodule.span O (Set.range th)).comap M.subtype) ≤ (q : ℕ∞) →
    M.map ((ϖ ^ e) • (LinearMap.id : V →ₗ[O] V)) ⊓
      (Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V)).restrictScalars O ≤ N' →
    N₁ ≤ N' → Z ≤ Zm → Zm ≤ N' → (∀ x, ρ x ∈ AA') →
    LinearMap.ker ρ = Zm.comap N'.subtype → (N₁.comap N'.subtype).map ρ = N₁' → N₁' ≤ AA →
    AA ≤ AA' →
    Module.length O (↥Zm ⧸ Z.comap Zm.subtype) ≠ ⊤ →
    (((T : ℝ) * νs ≤ (e : ℝ) ∧ ∀ z, ∃ m : ℤ, (ep z : ℝ) * ν z = m) ∨ (T : ℝ) * νs + 1 ≤ (e : ℝ)) →
    ∀ (Rr Aq : ι → Type) [∀ z, CommRing (Rr z)] [∀ z, IsLocalRing (Rr z)] [∀ z, Algebra O (Rr z)]
      [∀ z, IsLocalHom (algebraMap O (Rr z))] [∀ z, AddCommGroup (Aq z)] [∀ z, Module (Rr z) (Aq z)]
      [∀ z, Module O (Aq z)] [∀ z, IsScalarTower O (Rr z) (Aq z)]
      (xq : ∀ z, Rr z) (nq : ι → ℕ) (Fq : ∀ z, ℕ → Submodule (Rr z) (Aq z)) (rq : ι → ℕ → ℕ),
    (∀ z, Fq z 0 = ⊤) → (∀ z, Fq z (nq z) = ⊥) → (∀ z k, k < nq z → Fq z (k + 1) ≤ Fq z k) →
    (∀ z k, k < nq z → ∀ y ∈ Fq z k, xq z • y ∈ Fq z (k + 1) → y ∈ Fq z (k + 1)) →
    (∀ z k, k < nq z →
      Module.length (Rr z)
          (↥(Fq z k) ⧸ (Fq z (k + 1) ⊔ (Fq z k).map
            ((xq z ^ (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat) •
              (LinearMap.id : Aq z →ₗ[Rr z] Aq z))).comap (Fq z k).subtype) =
        ((rq z k * (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat : ℕ) : ℕ∞)) →
    (∀ z, ∑ k ∈ Finset.range (nq z), rq z k = R) →
    (∀ z, Module.length (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField (Rr z)) = (f z : ℕ∞)) →
    Nonempty ((↥AA' ⧸ AA.comap AA'.subtype) ≃ₗ[O]
      ((z : ι) → Aq z ⧸ (⊤ : Submodule (Rr z) (Aq z)).map
        ((xq z ^ (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat) •
          (LinearMap.id : Aq z →ₗ[Rr z] Aq z)))) →
    ∀ (A0 : Type) [AddCommGroup A0] [Module O A0] (n1 : ℕ) (F1 : ℕ → Submodule O ↥AA) (ι1 : Type)
      [Fintype ι1] [DecidableEq ι1] (deg : ι1 → ℕ) (δ : ℕ) (t : Fin δ → A0)
      (σ : ∀ k, ↥(F1 k) →ₗ[O] ({α : ι1 // deg α = k} → A0)) (u : ι1 → Fin δ → ↥AA),
    F1 0 = ⊤ → F1 n1 = ⊥ → (∀ k, F1 (k + 1) ≤ F1 k) →
    (∀ k, LinearMap.ker (σ k) = (F1 (k + 1)).comap (F1 k).subtype) →
    (∀ k, Function.Surjective (σ k)) → (∀ α, deg α < n1) →
    (∀ α i, ∃ h : u α i ∈ F1 (deg α), σ (deg α) ⟨u α i, h⟩ = Pi.single ⟨α, rfl⟩ (t i)) →
    LinearIndependent O t →
    N₁'.comap AA.subtype = Submodule.span O (Set.range fun p : ι1 × Fin δ => u p.1 p.2) →
    Fintype.card ι1 = R →
    Module.length O (A0 ⧸ Submodule.span O (Set.range t)) = (I : ℕ∞) →
    ∀ V' : Submodule K V,
      (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
        (e : ℝ) * (finrank K V' : ℝ) +
            (R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) + (R : ℝ) * (I : ℝ) +
            ((Module.length O (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ) + (q : ℝ)

theorem localStepClosedQ : LocalStepClosedQ := by
  intro ι _ ep f ν v νs c' T R I hep hT hc' hv hν O K V W _ _ _ _ _ _ _ _ _ _ _ _ _
    ϖ hϖ M Θ N₁ Z Zm N' Mgg e n q th AA AA' N₁' ρ hM hΘ h1 h2 h3 h4 h5 h6 h8 h9
    h10 h11 h12 h13 h14 h15 h16 h17 hcase
    Rr Aq _ _ _ _ _ _ _ _ xq nq Fq rq hF0 hFn hFd hFi hFl hsum hres hequiv
    A0 _ _ n1 F1 ι1 _ _ deg δ t σ u hG0 hGn hGd hker hsurj hdeg hlead hind hspan hcard hI V'
  obtain ⟨eqv⟩ := hequiv
  set mmz : ι → ℕ := fun z => (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat with hmmz
  have hL := levelsLengthSum O ι Rr Aq xq mmz nq Fq rq R hF0 hFn hFd hFi hFl hsum
  have hA : Module.length O (↥AA' ⧸ AA.comap AA'.subtype) ≤
      ((R * ∑ z, mmz z * f z : ℕ) : ℕ∞) := by
    rw [eqv.length_eq, hL]
    refine le_of_eq ?_
    simp only [hres]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  have hN : Module.length O (↥AA ⧸ N₁'.comap AA.subtype) ≤ ((R * I : ℕ) : ℕ∞) := by
    rw [hspan, leadingTermLength O (↥AA) A0 n1 F1 ι1 deg δ t σ u hG0 hGn hGd hker hsurj hdeg hlead hind,
      hcard, hI]
    push_cast
    exact le_rfl
  exact localStepLevelsQ ι ep f ν v νs c' T R I hep hT hc' hv hν O K V W ϖ hϖ M Θ N₁ Z Zm N' Mgg e
    n q th AA AA' N₁' ρ hM hΘ h1 h2 h3 h4 h5 h6 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    hcase hA hN V'

section Semilinear

variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O']
  [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']

theorem length_le_of_semilinear {Q Q' : Type} [AddCommGroup Q] [Module O Q] [AddCommGroup Q']
    [Module O' Q'] (ϖ : O) (hϖ : Irreducible ϖ) (hϖ' : Irreducible (algebraMap O O' ϖ))
    (g : Q →ₛₗ[algebraMap O O'] Q') (hg : Submodule.span O' (Set.range g) = ⊤) :
    Module.length O' Q' ≤ Module.length O Q := by
  by_cases hQ : Module.length O Q = ⊤
  · rw [hQ]; exact le_top
  let _ : Module O Q' := Module.compHom Q' (algebraMap O O')
  have : IsScalarTower O O' Q' := ⟨fun a b x => by
    show (a • b) • x = (algebraMap O O' a) • (b • x)
    rw [Algebra.smul_def, mul_smul]⟩
  let g' : Q →ₗ[O] Q' :=
    { toFun := g, map_add' := g.map_add, map_smul' := fun a x => g.map_smulₛₗ a x }
  have hs : Function.Surjective (g'.liftBaseChange O') := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hg, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨TensorProduct.tmul O 1 x, by rw [LinearMap.liftBaseChange_tmul, one_smul]; rfl⟩
  have h := Module.length_le_of_surjective _ hs
  rw [lengthBaseChangeLocal O O' Q ϖ (algebraMap O O' ϖ) 1 1 hϖ hϖ' (by simp) hQ] at h
  simpa using h

theorem ql_span_le {V V₁ : Type} [AddCommGroup V] [Module O V] [AddCommGroup V₁] [Module O' V₁]
    (ϖ : O) (hϖ : Irreducible ϖ) (hϖ' : Irreducible (algebraMap O O' ϖ))
    (jj : V →ₛₗ[algebraMap O O'] V₁) (A S : Submodule O V) (S₁ : Submodule O' V₁)
    (h : ∀ x ∈ S, jj x ∈ S₁) :
    ql (Submodule.span O' (jj '' (A : Set V))) S₁ ≤ ql A S := by
  set A₁ : Submodule O' V₁ := Submodule.span O' (jj '' (A : Set V)) with hA₁
  let g0 : ↥A →ₛₗ[algebraMap O O'] (↥A₁ ⧸ S₁.comap A₁.subtype) :=
    (S₁.comap A₁.subtype).mkQ.comp
      ((jj.comp A.subtype).codRestrict A₁ fun x => Submodule.subset_span ⟨x, x.2, rfl⟩)
  have hk : S.comap A.subtype ≤ LinearMap.ker g0 := by
    intro x hx
    rw [LinearMap.mem_ker]
    show (S₁.comap A₁.subtype).mkQ _ = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h x hx
  refine length_le_of_semilinear ϖ hϖ hϖ' ((S.comap A.subtype).liftQ g0 hk) ?_
  rw [eq_top_iff]
  intro z hz
  clear hz
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact Submodule.subset_span ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add a b ha hb iha ihb => exact Submodule.add_mem _ iha ihb
  | smul r a ha ih => exact Submodule.smul_mem _ r ih

end Semilinear

def LocalStepClosedQDescUp : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T R I : ℕ),
    (∀ z, 1 ≤ ep z) → 1 ≤ T → 0 ≤ c' → (∀ z, 0 ≤ v z) → (∀ z, ν z ≤ νs + c' * v z) →
  ∀ (O O' K K' V V₁ W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] [AddCommGroup W] [Module O' W]
    (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O O' ϖ) →
    ∀ (M Θ : Submodule O V) (N₁ Z Zm N' Mgg : Submodule O' V₁) (e n q : ℕ) (th : Fin n → V₁)
    (AA AA' N₁' : Submodule O' W) (ρ : ↥N' →ₗ[O'] W),
    Formalism.LatticeIndexTer.IsLat O K V M → Formalism.LatticeIndexTer.IsLat O K V Θ →
    N₁ ⊔ Z ≤ Submodule.span O' (j '' (Θ : Set V)) →
    (∀ i, th i ∈ Submodule.span O' (j '' (M : Set V))) →
    (∀ i, th i ∈ Submodule.span O' (j '' (Θ : Set V))) →
    Mgg ≤ Submodule.span O' (j '' (M : Set V)) →
    Submodule.span K' (Mgg : Set V₁) ≤ Submodule.span K' ((N₁ ⊔ Z : Submodule O' V₁) : Set V₁) →
    Module.length O' (↥(Submodule.span O' (j '' (M : Set V))) ⧸
      (Mgg ⊔ Submodule.span O' (Set.range th)).comap
        (Submodule.span O' (j '' (M : Set V))).subtype) ≤ (q : ℕ∞) →
    (Submodule.span O' (j '' (M : Set V))).map
        ((algebraMap O O' ϖ ^ e) • (LinearMap.id : V₁ →ₗ[O'] V₁)) ⊓
      (Submodule.span K' ((N₁ ⊔ Z : Submodule O' V₁) : Set V₁)).restrictScalars O' ≤ N' →
    N₁ ≤ N' → Z ≤ Zm → Zm ≤ N' → (∀ x, ρ x ∈ AA') →
    LinearMap.ker ρ = Zm.comap N'.subtype → (N₁.comap N'.subtype).map ρ = N₁' → N₁' ≤ AA →
    AA ≤ AA' →
    Module.length O' (↥Zm ⧸ Z.comap Zm.subtype) ≠ ⊤ →
    (((T : ℝ) * νs ≤ (e : ℝ) ∧ ∀ z, ∃ m : ℤ, (ep z : ℝ) * ν z = m) ∨ (T : ℝ) * νs + 1 ≤ (e : ℝ)) →
    ∀ (Rr Aq : ι → Type) [∀ z, CommRing (Rr z)] [∀ z, IsLocalRing (Rr z)] [∀ z, Algebra O' (Rr z)]
      [∀ z, IsLocalHom (algebraMap O' (Rr z))] [∀ z, AddCommGroup (Aq z)] [∀ z, Module (Rr z) (Aq z)]
      [∀ z, Module O' (Aq z)] [∀ z, IsScalarTower O' (Rr z) (Aq z)]
      (xq : ∀ z, Rr z) (nq : ι → ℕ) (Fq : ∀ z, ℕ → Submodule (Rr z) (Aq z)) (rq : ι → ℕ → ℕ),
    (∀ z, Fq z 0 = ⊤) → (∀ z, Fq z (nq z) = ⊥) → (∀ z k, k < nq z → Fq z (k + 1) ≤ Fq z k) →
    (∀ z k, k < nq z → ∀ y ∈ Fq z k, xq z • y ∈ Fq z (k + 1) → y ∈ Fq z (k + 1)) →
    (∀ z k, k < nq z →
      Module.length (Rr z)
          (↥(Fq z k) ⧸ (Fq z (k + 1) ⊔ (Fq z k).map
            ((xq z ^ (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat) •
              (LinearMap.id : Aq z →ₗ[Rr z] Aq z))).comap (Fq z k).subtype) =
        ((rq z k * (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat : ℕ) : ℕ∞)) →
    (∀ z, ∑ k ∈ Finset.range (nq z), rq z k = R) →
    (∀ z, Module.length (IsLocalRing.ResidueField O') (IsLocalRing.ResidueField (Rr z)) = (f z : ℕ∞)) →
    Nonempty ((↥AA' ⧸ AA.comap AA'.subtype) ≃ₗ[O']
      ((z : ι) → Aq z ⧸ (⊤ : Submodule (Rr z) (Aq z)).map
        ((xq z ^ (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat) •
          (LinearMap.id : Aq z →ₗ[Rr z] Aq z)))) →
    ∀ (A0 : Type) [AddCommGroup A0] [Module O' A0] (n1 : ℕ) (F1 : ℕ → Submodule O' ↥AA) (ι1 : Type)
      [Fintype ι1] [DecidableEq ι1] (deg : ι1 → ℕ) (δ : ℕ) (t : Fin δ → A0)
      (σ : ∀ k, ↥(F1 k) →ₗ[O'] ({α : ι1 // deg α = k} → A0)) (u : ι1 → Fin δ → ↥AA),
    F1 0 = ⊤ → F1 n1 = ⊥ → (∀ k, F1 (k + 1) ≤ F1 k) →
    (∀ k, LinearMap.ker (σ k) = (F1 (k + 1)).comap (F1 k).subtype) →
    (∀ k, Function.Surjective (σ k)) → (∀ α, deg α < n1) →
    (∀ α i, ∃ h : u α i ∈ F1 (deg α), σ (deg α) ⟨u α i, h⟩ = Pi.single ⟨α, rfl⟩ (t i)) →
    LinearIndependent O' t →
    N₁'.comap AA.subtype = Submodule.span O' (Set.range fun p : ι1 × Fin δ => u p.1 p.2) →
    Fintype.card ι1 = R →
    Module.length O' (A0 ⧸ Submodule.span O' (Set.range t)) = (I : ℕ∞) →
    ∀ V' : Submodule K V,
      (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
        (e : ℝ) * (finrank K V' : ℝ) +
            (R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) + (R : ℝ) * (I : ℝ) +
            ((Module.length O' (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ) + (q : ℝ)

theorem localStepClosedQDescUp : LocalStepClosedQDescUp := by
  intro ι _ ep f ν v νs c' T R I hep hT hc' hv hν O O' K K' V V₁ W
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj ϖ hϖ hϖ'
    M Θ N₁ Z Zm N' Mgg e n q th AA AA' N₁' ρ hM hΘ h1 h2 h3 h4 h5 h6 h8 h9
    h10 h11 h12 h13 h14 h15 h16 h17 hcase
    Rr Aq _ _ _ _ _ _ _ _ xq nq Fq rq hF0 hFn hFd hFi hFl hsum hres hequiv
    A0 _ _ n1 F1 ι1 _ _ deg δ t σ u hG0 hGn hGd hker hsurj hdeg hlead hind hspan hcard hI V'
  have : FiniteDimensional K' V₁ := Module.Finite.equiv hj.equiv
  have h := localStepClosedQ ι ep f ν v νs c' T R I hep hT hc' hv hν O' K' V₁ W (algebraMap O O' ϖ) hϖ'
    (Submodule.span O' (j '' (M : Set V))) (Submodule.span O' (j '' (Θ : Set V))) N₁ Z Zm N' Mgg e n q
    th AA AA' N₁' ρ (isLattice_span_image_alt O O' K K' V V₁ j hj M hM)
    (isLattice_span_image_alt O O' K K' V V₁ j hj Θ hΘ) h1 h2 h3 h4 h5 h6 h8 h9
    h10 h11 h12 h13 h14 h15 h16 h17 hcase
    Rr Aq xq nq Fq rq hF0 hFn hFd hFi hFl hsum hres hequiv
    A0 n1 F1 ι1 deg δ t σ u hG0 hGn hGd hker hsurj hdeg hlead hind hspan hcard hI
    (Submodule.span K' (j '' (V' : Set V)))
  have hd := localStepDescent O O' K K' V V₁ j hj ϖ hϖ hϖ' M Θ V' hM hΘ 1
    ((R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) + (R : ℝ) * (I : ℝ) +
      ((Module.length O' (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ) + (q : ℝ)) 0 e (by linarith)
  linarith

def LocalStepClosedQDesc : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T R I : ℕ),
    (∀ z, 1 ≤ ep z) → 1 ≤ T → 0 ≤ c' → (∀ z, 0 ≤ v z) → (∀ z, ν z ≤ νs + c' * v z) →
  ∀ (O O' K K' V V₁ W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] [AddCommGroup W] [Module O' W]
    (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O O' ϖ) →
    ∀ (M Θ Mgg : Submodule O V) (N₁ Z Zm N' : Submodule O' V₁) (e n q : ℕ) (th : Fin n → V)
    (AA AA' N₁' : Submodule O' W) (ρ : ↥N' →ₗ[O'] W),
    Formalism.LatticeIndexTer.IsLat O K V M → Formalism.LatticeIndexTer.IsLat O K V Θ →
    N₁ ⊔ Z ≤ Submodule.span O' (j '' (Θ : Set V)) → (∀ i, th i ∈ M) → (∀ i, th i ∈ Θ) →
    Mgg ≤ M →
    (∀ x ∈ Mgg, j x ∈ Submodule.span K' ((N₁ ⊔ Z : Submodule O' V₁) : Set V₁)) →
    Module.length O (↥M ⧸ (Mgg ⊔ Submodule.span O (Set.range th)).comap M.subtype) ≤ (q : ℕ∞) →
    (Submodule.span O' (j '' (M : Set V))).map
        ((algebraMap O O' ϖ ^ e) • (LinearMap.id : V₁ →ₗ[O'] V₁)) ⊓
      (Submodule.span K' ((N₁ ⊔ Z : Submodule O' V₁) : Set V₁)).restrictScalars O' ≤ N' →
    N₁ ≤ N' → Z ≤ Zm → Zm ≤ N' → (∀ x, ρ x ∈ AA') →
    LinearMap.ker ρ = Zm.comap N'.subtype → (N₁.comap N'.subtype).map ρ = N₁' → N₁' ≤ AA →
    AA ≤ AA' →
    Module.length O' (↥Zm ⧸ Z.comap Zm.subtype) ≠ ⊤ →
    (((T : ℝ) * νs ≤ (e : ℝ) ∧ ∀ z, ∃ m : ℤ, (ep z : ℝ) * ν z = m) ∨ (T : ℝ) * νs + 1 ≤ (e : ℝ)) →
    ∀ (Rr Aq : ι → Type) [∀ z, CommRing (Rr z)] [∀ z, IsLocalRing (Rr z)] [∀ z, Algebra O' (Rr z)]
      [∀ z, IsLocalHom (algebraMap O' (Rr z))] [∀ z, AddCommGroup (Aq z)] [∀ z, Module (Rr z) (Aq z)]
      [∀ z, Module O' (Aq z)] [∀ z, IsScalarTower O' (Rr z) (Aq z)]
      (xq : ∀ z, Rr z) (nq : ι → ℕ) (Fq : ∀ z, ℕ → Submodule (Rr z) (Aq z)) (rq : ι → ℕ → ℕ),
    (∀ z, Fq z 0 = ⊤) → (∀ z, Fq z (nq z) = ⊥) → (∀ z k, k < nq z → Fq z (k + 1) ≤ Fq z k) →
    (∀ z k, k < nq z → ∀ y ∈ Fq z k, xq z • y ∈ Fq z (k + 1) → y ∈ Fq z (k + 1)) →
    (∀ z k, k < nq z →
      Module.length (Rr z)
          (↥(Fq z k) ⧸ (Fq z (k + 1) ⊔ (Fq z k).map
            ((xq z ^ (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat) •
              (LinearMap.id : Aq z →ₗ[Rr z] Aq z))).comap (Fq z k).subtype) =
        ((rq z k * (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat : ℕ) : ℕ∞)) →
    (∀ z, ∑ k ∈ Finset.range (nq z), rq z k = R) →
    (∀ z, Module.length (IsLocalRing.ResidueField O') (IsLocalRing.ResidueField (Rr z)) = (f z : ℕ∞)) →
    Nonempty ((↥AA' ⧸ AA.comap AA'.subtype) ≃ₗ[O']
      ((z : ι) → Aq z ⧸ (⊤ : Submodule (Rr z) (Aq z)).map
        ((xq z ^ (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat) •
          (LinearMap.id : Aq z →ₗ[Rr z] Aq z)))) →
    ∀ (A0 : Type) [AddCommGroup A0] [Module O' A0] (n1 : ℕ) (F1 : ℕ → Submodule O' ↥AA) (ι1 : Type)
      [Fintype ι1] [DecidableEq ι1] (deg : ι1 → ℕ) (δ : ℕ) (t : Fin δ → A0)
      (σ : ∀ k, ↥(F1 k) →ₗ[O'] ({α : ι1 // deg α = k} → A0)) (u : ι1 → Fin δ → ↥AA),
    F1 0 = ⊤ → F1 n1 = ⊥ → (∀ k, F1 (k + 1) ≤ F1 k) →
    (∀ k, LinearMap.ker (σ k) = (F1 (k + 1)).comap (F1 k).subtype) →
    (∀ k, Function.Surjective (σ k)) → (∀ α, deg α < n1) →
    (∀ α i, ∃ h : u α i ∈ F1 (deg α), σ (deg α) ⟨u α i, h⟩ = Pi.single ⟨α, rfl⟩ (t i)) →
    LinearIndependent O' t →
    N₁'.comap AA.subtype = Submodule.span O' (Set.range fun p : ι1 × Fin δ => u p.1 p.2) →
    Fintype.card ι1 = R →
    Module.length O' (A0 ⧸ Submodule.span O' (Set.range t)) = (I : ℕ∞) →
    ∀ V' : Submodule K V,
      (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
        (e : ℝ) * (finrank K V' : ℝ) +
            (R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) + (R : ℝ) * (I : ℝ) +
            ((Module.length O' (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ) + (q : ℝ)

theorem localStepClosedQDesc : LocalStepClosedQDesc := by
  intro ι _ ep f ν v νs c' T R I hep hT hc' hv hν O O' K K' V V₁ W
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj ϖ hϖ hϖ'
    M Θ Mgg N₁ Z Zm N' e n q th AA AA' N₁' ρ hM hΘ h1 h2 h3 h4 h5 h6
  let jj : V →ₛₗ[algebraMap O O'] V₁ :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun a x => by
        show j (a • x) = algebraMap O O' a • j x
        rw [← algebraMap_smul K a x, j.map_smul, ← algebraMap_smul K' (algebraMap O K a) (j x),
          ← IsScalarTower.algebraMap_apply O K K', IsScalarTower.algebraMap_apply O O' K',
          algebraMap_smul] }
  have hlen : ql (Submodule.span O' (j '' (M : Set V)))
      (Submodule.span O' (j '' (Mgg : Set V)) ⊔ Submodule.span O' (Set.range fun i => j (th i))) ≤
      ql M (Mgg ⊔ Submodule.span O (Set.range th)) := by
    refine ql_span_le ϖ hϖ hϖ' jj M _ _ ?_
    have hle : Mgg ⊔ Submodule.span O (Set.range th) ≤
        (Submodule.span O' (j '' (Mgg : Set V)) ⊔
          Submodule.span O' (Set.range fun i => j (th i))).comap jj := by
      refine sup_le (fun x hx => ?_) (Submodule.span_le.2 ?_)
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨x, hx, rfl⟩)
      · rintro _ ⟨i, rfl⟩
        exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
    exact fun x hx => hle hx
  refine localStepClosedQDescUp ι ep f ν v νs c' T R I hep hT hc' hv hν O O' K K' V V₁ W j hj ϖ hϖ hϖ'
    M Θ N₁ Z Zm N' (Submodule.span O' (j '' (Mgg : Set V))) e n q (fun i => j (th i)) AA AA' N₁' ρ
    hM hΘ h1 (fun i => Submodule.subset_span ⟨th i, h2 i, rfl⟩)
    (fun i => Submodule.subset_span ⟨th i, h3 i, rfl⟩)
    (Submodule.span_mono (Set.image_mono h4)) ?_ (hlen.trans h6)
  rw [Submodule.span_le]
  have hle : Submodule.span O' (j '' (Mgg : Set V)) ≤
      (Submodule.span K' ((N₁ ⊔ Z : Submodule O' V₁) : Set V₁)).restrictScalars O' := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact h5 x hx
  exact fun x hx => hle hx

end Formalism.MainNotions.Gaps.T0
