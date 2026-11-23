import Formalism.FilteredPoleLength.ReducedBasisBounds.ReductionQuotient
import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxDet

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

namespace BQuot

section General

variable {O V W : Type*} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]

abbrev ql (A B : Submodule O V) : ℕ∞ := Module.length O (↥A ⧸ B.comap A.subtype)

private theorem len_quot_le_lemma {M Q : Type*} [AddCommGroup M] [Module O M] [AddCommGroup Q]
    [Module O Q] (S : Submodule O M) (φ : M →ₗ[O] Q) (h : LinearMap.ker φ ≤ S) :
    Module.length O (M ⧸ S) ≤ Module.length O Q := by
  refine (Module.length_le_of_surjective (Submodule.factor h) ?_).trans
    (Module.length_le_of_injective ((LinearMap.ker φ).liftQ φ le_rfl) ?_)
  · intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  · rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

theorem ql_le_of_map {A S : Submodule O V} {L P : Submodule O W} (f : ↥A →ₗ[O] W)
    (h1 : ∀ x, f x ∈ L) (h2 : ∀ x, f x ∈ P → (x : V) ∈ S) : ql A S ≤ ql L P := by
  refine len_quot_le_lemma _ ((P.comap L.subtype).mkQ ∘ₗ f.codRestrict L h1) ?_
  intro x hx
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at hx
  exact h2 x hx

theorem ql_mono_left {A A' B : Submodule O V} (h : A ≤ A') : ql A B ≤ ql A' B :=
  ql_le_of_map A.subtype (fun x => h x.2) (fun _ hx => hx)

theorem ql_anti_right {A B B' : Submodule O V} (h : B ≤ B') : ql A B' ≤ ql A B :=
  ql_le_of_map A.subtype (fun x => x.2) (fun _ hx => h hx)

theorem ql_sup_le (A B : Submodule O V) : ql (A ⊔ B) B ≤ ql A B := by
  have e := LinearMap.quotientInfEquivSupQuotient A B
  have h1 : ql (A ⊔ B) B ≤ ql A (A ⊓ B) :=
    Module.length_le_of_surjective e.toLinearMap e.surjective
  have h2 : ql A (A ⊓ B) ≤ ql A B :=
    ql_le_of_map (A := A) (S := A ⊓ B) (L := A) (P := B) A.subtype (fun x => x.2)
      (fun x hx => Submodule.mem_inf.2 ⟨x.2, hx⟩)
  exact h1.trans h2

theorem ql_le_of_le_sup {A A' B : Submodule O V} (h : A ≤ A' ⊔ B) : ql A B ≤ ql A' B :=
  (ql_mono_left h).trans (ql_sup_le A' B)

private theorem len_quot_tri_lemma_2 {M : Type*} [AddCommGroup M] [Module O M] (P Q : Submodule O M) :
    Module.length O (M ⧸ Q) ≤ Module.length O (M ⧸ P) + Module.length O (↥P ⧸ Q.comap P.subtype) := by
  set N : Submodule O (M ⧸ Q) := LinearMap.range (Q.mkQ ∘ₗ P.subtype) with hN
  rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N), add_comm]
  gcongr
  · refine Module.length_le_of_surjective
      (P.liftQ (N.mkQ ∘ₗ Q.mkQ) ?_) ?_
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact ⟨⟨x, hx⟩, rfl⟩
    · intro q
      obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      exact ⟨Submodule.Quotient.mk m, rfl⟩
  · refine Module.length_le_of_surjective
      ((Q.comap P.subtype).liftQ (Q.mkQ ∘ₗ P.subtype).rangeRestrict ?_) ?_
    · intro x hx
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.subtype_apply, ZeroMemClass.coe_zero, LinearMap.rangeRestrict,
        Submodule.Quotient.mk_eq_zero]
      exact hx
    · intro q
      obtain ⟨x, hx⟩ := LinearMap.surjective_rangeRestrict (Q.mkQ ∘ₗ P.subtype) q
      exact ⟨Submodule.Quotient.mk x, hx⟩

theorem ql_triangle (A B C : Submodule O V) : ql A C ≤ ql A B + ql B C := by
  refine (len_quot_tri_lemma_2 (B.comap A.subtype) (C.comap A.subtype)).trans ?_
  gcongr
  exact ql_le_of_map (V := ↥A) (A := B.comap A.subtype) (S := C.comap A.subtype)
    (A.subtype ∘ₗ (B.comap A.subtype).subtype) (fun x => x.2) (fun _ hx => hx)

theorem reduction (X Θ N₀ T NK : Submodule O V) (h1 : N₀ ≤ Θ) (h2 : T ≤ Θ) :
    ql (X ⊔ Θ) Θ ≤ ql ((X ⊓ NK) ⊔ N₀) N₀ + ql X ((X ⊓ NK) ⊔ T) := by
  refine (ql_sup_le X Θ).trans ((ql_triangle X ((X ⊓ NK) ⊔ T) Θ).trans ?_)
  rw [add_comm]
  gcongr
  calc ql ((X ⊓ NK) ⊔ T) Θ ≤ ql (X ⊓ NK) Θ := ql_le_of_le_sup (sup_le_sup_left h2 _)
    _ ≤ ql (X ⊓ NK) N₀ := ql_anti_right h1
    _ ≤ ql ((X ⊓ NK) ⊔ N₀) N₀ := ql_mono_left le_sup_left

theorem levels (N' M₁ N₁ Z Zm : Submodule O V) (AA AA' N₁' : Submodule O W) (ρ : ↥N' →ₗ[O] W)
    (hM : M₁ ≤ N') (hρ : ∀ x, ρ x ∈ AA')
    (hker : LinearMap.ker ρ = Zm.comap N'.subtype) (himg : (N₁.comap N'.subtype).map ρ = N₁') :
    ql M₁ (N₁ ⊔ Z) ≤ ql AA' AA + ql AA N₁' + ql Zm Z := by
  set Y : Submodule O V := (AA.comap ρ).map N'.subtype with hYdef
  set Y' : Submodule O V := (N₁'.comap ρ).map N'.subtype with hY'def
  have hYN : Y ≤ N' := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have s1 : ql M₁ Y ≤ ql AA' AA :=
    ql_le_of_map (ρ ∘ₗ Submodule.inclusion hM) (fun x => hρ _)
      (fun x hx => ⟨Submodule.inclusion hM x, hx, rfl⟩)
  have s2 : ql Y Y' ≤ ql AA N₁' := by
    refine ql_le_of_map (ρ ∘ₗ Submodule.inclusion hYN) (fun x => ?_)
      (fun x hx => ⟨Submodule.inclusion hYN x, hx, rfl⟩)
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 x.2
    have hxy : Submodule.inclusion hYN x = y := Subtype.ext hyx.symm
    rw [LinearMap.comp_apply, hxy]
    exact hy
  have s3 : ql Y' (N₁ ⊔ Z) ≤ ql Zm Z := by
    have hsub : Y' ≤ Zm ⊔ (N₁ ⊔ Z) := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : ρ y ∈ (N₁.comap N'.subtype).map ρ := by
        rw [himg]
        exact hy
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 hy'
      have hk : y - z ∈ LinearMap.ker ρ := by
        rw [LinearMap.mem_ker, map_sub, hzy, sub_self]
      rw [hker] at hk
      have hsplit : N'.subtype y = ((y - z : ↥N') : V) + (z : V) := by
        simp
      rw [hsplit]
      exact Submodule.add_mem_sup hk (Submodule.mem_sup_left hz)
    exact (ql_le_of_le_sup hsub).trans (ql_anti_right le_sup_right)
  calc ql M₁ (N₁ ⊔ Z) ≤ ql M₁ Y + ql Y (N₁ ⊔ Z) := ql_triangle _ _ _
    _ ≤ ql M₁ Y + (ql Y Y' + ql Y' (N₁ ⊔ Z)) := by
      gcongr
      exact ql_triangle _ _ _
    _ ≤ ql AA' AA + (ql AA N₁' + ql Zm Z) := by gcongr
    _ = ql AA' AA + ql AA N₁' + ql Zm Z := by rw [add_assoc]

end General

section DVR

variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]

theorem mem_span_basisFun (n : ℕ) (y : Fin n → K) (h : ∀ i, ∃ a : O, y i = algebraMap O K a) :
    y ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin n))) := by
  choose a ha using h
  have hy : y = ∑ i, a i • Pi.basisFun K (Fin n) i := by
    ext j
    simp [ha, Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  rw [hy]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem quot_core (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) (c : V →ₗ[K] (Fin n → K))
    (N : Submodule K V) (hN : LinearMap.ker c ≤ N) (X : Submodule O V) (e be : ℕ)
    (th : Fin n → V)
    (hX : ∀ x ∈ X, ∀ i, ∃ a : O,
      c x i = (algebraMap O K ϖ) ^ ((e : ℤ) - (be : ℤ)) * algebraMap O K a)
    (hth : ∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X)
    (a a' : O) (ha : a ≠ 0)
    (hdet : algebraMap O K a = (Matrix.of fun i j => c (th j) i).det * algebraMap O K a') :
    ql X ((X ⊓ N.restrictScalars O) ⊔
        Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)) +
      IsDiscreteValuationRing.addVal O a' ≤
      IsDiscreteValuationRing.addVal O a + ((n * be : ℕ) : ℕ∞) := by
  set p : K := algebraMap O K ϖ with hp
  have hp0 : p ≠ 0 := by
    rw [hp]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero
  set Tj : Submodule O V := Submodule.span O (Set.range fun j => p ^ e • th j) with hTj
  have hTX : Tj ≤ X := Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hth j)
  let b := Pi.basisFun K (Fin n)
  let f : V →ₗ[O] (Fin n → K) := ((p ^ ((be : ℤ) - (e : ℤ))) • c).restrictScalars O
  have hf : ∀ x, f x = p ^ ((be : ℤ) - (e : ℤ)) • c x := fun x => rfl
  let w : Fin n → (Fin n → K) := fun j => f (p ^ e • th j)
  have hw' : ∀ j, w j = p ^ be • c (th j) := by
    intro j
    show f (p ^ e • th j) = _
    rw [hf, map_smul, smul_smul, ← zpow_natCast p e, ← zpow_add₀ hp0, sub_add_cancel,
      zpow_natCast]
  have hfX : ∀ x ∈ X, f x ∈ Submodule.span O (Set.range b) := by
    intro x hx
    apply mem_span_basisFun
    intro i
    obtain ⟨u, hu⟩ := hX x hx i
    refine ⟨u, ?_⟩
    rw [hf, Pi.smul_apply, hu, smul_eq_mul, ← mul_assoc, ← zpow_add₀ hp0]
    simp
  have hmat : b.toMatrix w = p ^ be • (Matrix.of fun i j => c (th j) i) := by
    ext i j
    rw [Basis.toMatrix_apply, hw']
    simp [b]
  have hC0 : (Matrix.of fun i j => c (th j) i).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact ha ((map_eq_zero_iff _ (IsFractionRing.injective O K)).1 hdet)
  have hdw : (b.toMatrix w).det = (p ^ be) ^ n * (Matrix.of fun i j => c (th j) i).det := by
    rw [hmat, Matrix.det_smul, Fintype.card_fin]
  have hdw0 : (b.toMatrix w).det ≠ 0 := by
    rw [hdw]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hp0)) hC0
  obtain ⟨e0, he0, hlen⟩ := Formalism.LatticeIndexTer.LatticeIndexDeterminant.len_span (O := O) b w
    (fun j => hfX _ (hth j)) hdw0
  have hle : ql X ((X ⊓ N.restrictScalars O) ⊔ Tj) ≤ IsDiscreteValuationRing.addVal O e0 := by
    rw [← hlen]
    refine ql_le_of_map (f ∘ₗ X.subtype) (fun x => hfX _ x.2) ?_
    intro x hx
    have hx' : f (x : V) ∈ Submodule.span O (Set.range w) := hx
    have hmap : Submodule.span O (Set.range w) = Tj.map f := by
      rw [hTj, Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hmap] at hx'
    obtain ⟨t, ht, htx⟩ := hx'
    have hker : (x : V) - t ∈ LinearMap.ker c := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      rw [hf, hf] at htx
      exact (smul_right_injective _ (zpow_ne_zero _ hp0) htx).symm
    have : (x : V) = ((x : V) - t) + t := by abel
    rw [this]
    exact Submodule.add_mem_sup ⟨X.sub_mem x.2 (hTX ht), hN hker⟩ ht
  have hrel : e0 * a' = ϖ ^ (n * be) * a := by
    apply IsFractionRing.injective O K
    rw [map_mul, map_mul, map_pow, he0, hdw, hdet, ← hp, ← pow_mul, mul_comm be n]
    ring
  have hval : IsDiscreteValuationRing.addVal O e0 + IsDiscreteValuationRing.addVal O a' =
      IsDiscreteValuationRing.addVal O a + ((n * be : ℕ) : ℕ∞) := by
    rw [← IsDiscreteValuationRing.addVal_mul, hrel, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ, add_comm]
    simp
  rw [← hval]
  exact add_le_add hle le_rfl

end DVR

end BQuot

open BQuot in
theorem quotientLength : QuotientLength := by
  intro O K V _ _ _ _ _ _ _ _ _ _ ϖ hϖ n c N hN X e be th hX hth a a' ha ha' hdet
  dsimp only
  have hq := quot_core (K := K) ϖ hϖ n c N hN X e be th hX hth a a' ha hdet
  have hva : IsDiscreteValuationRing.addVal O a ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact ha
  have hva' : IsDiscreteValuationRing.addVal O a' ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact ha'
  lift IsDiscreteValuationRing.addVal O a to ℕ using hva with A hA
  lift IsDiscreteValuationRing.addVal O a' to ℕ using hva' with A' hA'
  have hfin : ql X ((X ⊓ N.restrictScalars O) ⊔
      Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at hq
    exact (ENat.coe_ne_top _) (top_le_iff.1 (by exact_mod_cast hq))
  lift ql X ((X ⊓ N.restrictScalars O) ⊔
      Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)) to ℕ using hfin with m hm
  refine ⟨m, rfl, ?_⟩
  have hq' : m + A' ≤ A + n * be := by exact_mod_cast hq
  simp only [ENat.toNat_coe]
  have hq'' : (m : ℤ) + A' ≤ A + n * be := by exact_mod_cast hq'
  linarith

open BQuot in
theorem localAssembly : LocalAssembly := by
  intro O K V W _ _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ M Θ N₁ Z Zm N' e be n th c AA AA' N₁' ρ a a'
  dsimp only
  intro hN1Z hthM hthΘ hkc hMint ha ha' hdet hXNK hN1N' hZZm hZmN' hρ hkerρ himg hN1'AA hAA
  set X : Submodule O V := M.map ((ϖ ^ e) • (LinearMap.id : V →ₗ[O] V)) with hXdef
  set NK : Submodule O V :=
    (Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V)).restrictScalars O with hNKdef
  set Tj : Submodule O V :=
    Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j) with hTjdef
  have hϖ0 : algebraMap O K ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    exact hϖ.ne_zero
  have hTΘ : Tj ≤ Θ := by
    rw [hTjdef, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show (algebraMap O K ϖ) ^ e • th j ∈ Θ
    rw [← map_pow, algebraMap_smul]
    exact Θ.smul_mem _ (hthΘ j)
  have hX' : ∀ x ∈ X, ∀ i, ∃ u : O,
      c x i = (algebraMap O K ϖ) ^ ((e : ℤ) - (be : ℤ)) * algebraMap O K u := by
    intro x hx i
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨u, hu⟩ := hMint m hm i
    refine ⟨u, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, ← algebraMap_smul K (ϖ ^ e) m, map_smul,
      Pi.smul_apply, smul_eq_mul, hu, map_pow, sub_eq_add_neg, zpow_add₀ hϖ0, zpow_natCast]
    ring
  have hth' : ∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X := by
    intro j
    rw [← map_pow, algebraMap_smul]
    exact Submodule.mem_map.2 ⟨th j, hthM j, by simp⟩
  obtain ⟨m, hm, hmΔ⟩ := quotientLength O K V ϖ hϖ n c
    (Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V)) hkc X e be th hX' hth' a a' ha ha' hdet
  have hql : ql X ((X ⊓ NK) ⊔ Tj) = m := hm
  have hlev := levels N' ((X ⊓ NK) ⊔ (N₁ ⊔ Z)) N₁ Z Zm AA AA' N₁' ρ
    (sup_le hXNK (sup_le hN1N' (hZZm.trans hZmN'))) hρ hkerρ himg
  have hred := reduction X Θ (N₁ ⊔ Z) Tj NK hN1Z hTΘ
  have hmle : (m : ℕ∞) ≤ ((((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
      ((IsDiscreteValuationRing.addVal O a').toNat : ℤ) + (n : ℤ) * (be : ℤ)).toNat : ℕ) := by
    have h1 := hmΔ.trans (Int.self_le_toNat _)
    have h2 : m ≤ (((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
      ((IsDiscreteValuationRing.addVal O a').toNat : ℤ) + (n : ℤ) * (be : ℤ)).toNat := by
      exact_mod_cast h1
    exact_mod_cast h2
  calc ql (X ⊔ Θ) Θ ≤ ql ((X ⊓ NK) ⊔ (N₁ ⊔ Z)) (N₁ ⊔ Z) + ql X ((X ⊓ NK) ⊔ Tj) := hred
    _ ≤ (ql AA' AA + ql AA N₁' + ql Zm Z) + (m : ℕ∞) := by
      rw [hql]
      gcongr
    _ ≤ _ := by gcongr

end Formalism.LatticeBaseChangeAlt
