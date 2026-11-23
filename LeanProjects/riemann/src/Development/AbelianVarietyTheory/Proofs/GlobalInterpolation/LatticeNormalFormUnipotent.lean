import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent

noncomputable section

namespace GlobalTheory.Proof.LatticeNormalFormUnipotent

open GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect Module

section Lattice

variable {O F Y : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F]
  [IsFractionRing O F] [AddCommGroup Y] [Module F Y] [Module O Y] [IsScalarTower O F Y]

omit [IsDiscreteValuationRing O] in
theorem span_range_extend {κ : Type} {L : Submodule O Y} [Submodule.IsLattice F L] (b : Basis κ O L) :
    Submodule.span O (Set.range (b.extendOfIsLattice F)) = L := by
  have h1 : Set.range (b.extendOfIsLattice F) = L.subtype '' Set.range b := by
    rw [← Set.range_comp]
    congr 1
    exact funext fun i => b.extendOfIsLattice_apply F i
  rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem exists_equiv_map_eq (M L : Submodule O Y) [Submodule.IsLattice F M] [Submodule.IsLattice F L] :
    ∃ γ : Y ≃ₗ[F] Y, M.map (γ.toLinearMap.restrictScalars O) = L := by
  let bM := Module.Free.chooseBasis O M
  let bL := Module.Free.chooseBasis O L
  let e := (bM.extendOfIsLattice F).indexEquiv (bL.extendOfIsLattice F)
  refine ⟨(bM.extendOfIsLattice F).equiv (bL.extendOfIsLattice F) e, ?_⟩
  refine (congrArg (Submodule.map _) (span_range_extend (F := F) bM).symm).trans
    (Eq.trans ?_ (span_range_extend (F := F) bL))
  rw [Submodule.map_span, ← Set.range_comp, ← e.surjective.range_comp (bL.extendOfIsLattice F)]
  congr 2
  funext i
  exact (bM.extendOfIsLattice F).equiv_apply i (bL.extendOfIsLattice F) e

omit [IsDiscreteValuationRing O] in

theorem exists_smul_mem (Λ : Submodule O Y) [h : Submodule.IsLattice F Λ] (y : Y) :
    ∃ s : O, s ≠ 0 ∧ s • y ∈ Λ := by
  have hy : y ∈ Submodule.span F (Λ : Set Y) := by rw [h.span_eq_top]; trivial
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) F _ y hy
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩

theorem exists_eq_span_zpow {q : O} (hq : Irreducible q) (I : Submodule O F) (hI : I.FG) (h0 : I ≠ ⊥) :
    ∃ e : ℤ, I = Submodule.span O {(algebraMap O F q) ^ e} := by
  have hf : IsFractional (nonZeroDivisors O) I := FractionalIdeal.isFractional_of_fg hI
  have hp : I.IsPrincipal := FractionalIdeal.isPrincipal (⟨I, hf⟩ : FractionalIdeal (nonZeroDivisors O) F)
  obtain ⟨x, rfl⟩ := hp
  have hx : x ≠ 0 := by
    rintro rfl
    simp at h0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hq hx
  exact ⟨n, Submodule.span_singleton_smul_eq u.isUnit _⟩

end Lattice

section Frame

variable {F Y : Type} [Field F] [AddCommGroup Y] [Module F Y] {c : ℕ}

theorem exists_coord {X : Submodule F Y} {a : Fin c → Y} (h : IsFrame X a) :
    ∃ (p : Y →ₗ[F] X) (φ : Fin c → Y →ₗ[F] F), (∀ x : X, p x = x) ∧ (∀ i, p (a i) = 0) ∧
      (∀ i, ∀ x ∈ X, φ i x = 0) ∧ (∀ i j, φ i (a j) = if j = i then 1 else 0) ∧
      ∀ y, y = p y + ∑ i, φ i y • a i := by
  let b := Basis.span h.1
  let p := X.projectionOnto _ h.2
  let p' := (Submodule.span F (Set.range a)).projectionOnto _ h.2.symm
  have ha : ∀ i, a i ∈ Submodule.span F (Set.range a) := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hb : ∀ i, (b i : Y) = a i := fun i => by simp [b]
  refine ⟨p, fun i => b.coord i ∘ₗ p', fun x => by simp [p], fun i => ?_, fun i x hx => ?_, fun i j => ?_,
    fun y => ?_⟩
  · exact Submodule.projectionOnto_apply_right h.2 ⟨_, ha i⟩
  · have : p' x = 0 := Submodule.projectionOnto_apply_right h.2.symm ⟨_, hx⟩
    simp [this]
  · have : p' (a j) = b j := by
      rw [← hb j]
      exact Submodule.projectionOnto_apply_left h.2.symm _
    simp [this, Finsupp.single_apply]
  · have h1 : (p y : Y) + p' y = y := Submodule.projection_add_projection_eq_self h.2 y
    have h2 : (p' y : Y) = ∑ i, b.coord i (p' y) • a i := by
      have := congrArg Subtype.val (b.sum_repr (p' y))
      rw [← this]
      simp only [Submodule.coe_sum, Submodule.coe_smul, hb, Basis.coord_apply]
    rw [h2] at h1
    exact h1.symm

theorem exists_unip [FiniteDimensional F Y] {X : Submodule F Y} {a : Fin c → Y}
    (p : Y →ₗ[F] X) (φ : Fin c → Y →ₗ[F] F)
    (hX : ∀ i, ∀ x ∈ X, φ i x = 0) (ha : ∀ i j, φ i (a j) = if j = i then 1 else 0)
    (hy : ∀ y, y = p y + ∑ i, φ i y • a i)
    (u : Fin c → Y) (hu1 : ∀ i, φ i (u i) = 1) (hu0 : ∀ i j, i < j → φ j (u i) = 0) :
    ∃ n : Y ≃ₗ[F] Y, (∀ x ∈ X, n x = x) ∧ (∀ i, n (u i) = a i) ∧ ∀ i, n (a i) - a i ∈ flag X a i := by
  let m : Y →ₗ[F] Y := LinearMap.id + ∑ i, (φ i).smulRight (u i - a i)
  have hm : ∀ y, m y = y + ∑ i, φ i y • (u i - a i) := fun y => by simp [m]
  have hmX : ∀ x ∈ X, m x = x := fun x hx => by simp [hm, fun i => hX i x hx]
  have hma : ∀ i, m (a i) = u i := fun i => by simp [hm, ha]
  have key : ∀ k : ℕ, ∀ y, (∀ j : Fin c, k ≤ j.1 → φ j y = 0) →
      ∃ x, (∀ j : Fin c, k ≤ j.1 → φ j x = 0) ∧ m x = y := by
    intro k
    induction k with
    | zero =>
      intro y h
      refine ⟨y, h, ?_⟩
      simp [hm, fun j => h j (Nat.zero_le _)]
    | succ k ih =>
      intro y h
      by_cases hk : k < c
      · obtain ⟨x, hx, hxy⟩ := ih (y - φ ⟨k, hk⟩ y • u ⟨k, hk⟩) (fun j hj => by
          rcases hj.eq_or_lt with hj | hj
          · obtain rfl : j = ⟨k, hk⟩ := Fin.ext hj.symm
            simp [hu1]
          · simp [h j hj, hu0 ⟨k, hk⟩ j hj])
        refine ⟨x + φ ⟨k, hk⟩ y • a ⟨k, hk⟩, fun j hj => ?_, ?_⟩
        · have : (⟨k, hk⟩ : Fin c) ≠ j := fun h => by rw [← h] at hj; simp at hj
          simp [hx j (by omega), ha, this]
        · rw [map_add, map_smul, hxy, hma, sub_add_cancel]
      · obtain ⟨x, hx, hxy⟩ := ih y (fun j hj => by have := j.2; omega)
        exact ⟨x, fun j hj => hx j (by omega), hxy⟩
  have hsurj : Function.Surjective m := fun y => by
    obtain ⟨x, -, hx⟩ := key c y (fun j hj => by have := j.2; omega)
    exact ⟨x, hx⟩
  let m' : Y ≃ₗ[F] Y := LinearEquiv.ofBijective m ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩
  have hn : ∀ x, m'.symm (m x) = x := fun x => m'.symm_apply_apply x
  refine ⟨m'.symm, fun x hx => ?_, fun i => ?_, fun i => ?_⟩
  · conv_lhs => rw [← hmX x hx]
    exact hn x
  · rw [← hma, hn]
  · obtain ⟨x, hx, hxy⟩ := key i.1 (a i - u i) (fun j hj => by
      rcases hj.eq_or_lt with hj | hj
      · obtain rfl : j = i := Fin.ext hj.symm
        simp [hu1, ha]
      · have hij : i < j := hj
        simp [hu0 i j hij, ha, hij.ne])
    have h1 : m'.symm (a i) - a i = x := by
      rw [← hn x, hxy, map_sub, ← hma, hn]
    rw [h1, hy x]
    refine add_mem (Submodule.mem_sup_left (p x).2) (Submodule.mem_sup_right (Submodule.sum_mem _ fun j _ => ?_))
    by_cases hj : j < i
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rw [hx j (not_lt.1 hj), zero_smul]
      exact zero_mem _

end Frame

section Main

variable {O F Y : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F]
  [IsFractionRing O F] [AddCommGroup Y] [Module F Y] [Module O Y] [IsScalarTower O F Y] {c : ℕ}

theorem exists_adapted {q : O} (hq : Irreducible q) {X : Submodule F Y} {a : Fin c → Y}
    (p : Y →ₗ[F] X) (φ : Fin c → Y →ₗ[F] F) (ha : ∀ i j, φ i (a j) = if j = i then 1 else 0)
    (hy : ∀ y, y = p y + ∑ i, φ i y • a i) (Λ : Submodule O Y) [hΛ : Submodule.IsLattice F Λ] :
    ∃ (e : Fin c → ℤ) (u : Fin c → Y), (∀ i, φ i (u i) = 1) ∧ (∀ i j, i < j → φ j (u i) = 0) ∧
      Λ = Λ ⊓ X.restrictScalars O ⊔ ⨆ i, Submodule.span O {(algebraMap O F q) ^ (e i) • u i} := by
  have hq0 : algebraMap O F q ≠ 0 := by
    simpa using hq.ne_zero
  let W : Fin c → Submodule O Y := fun i => ⨅ j, ⨅ (_ : i < j), LinearMap.ker ((φ j).restrictScalars O)
  have hW : ∀ i y, y ∈ W i ↔ ∀ j, i < j → φ j y = 0 := fun i y => by simp [W]
  have hI : ∀ i, ∃ e : ℤ, (Λ ⊓ W i).map ((φ i).restrictScalars O) =
      Submodule.span O {(algebraMap O F q) ^ e} := by
    intro i
    refine exists_eq_span_zpow hq _ (Submodule.FG.map _ (hΛ.fg.of_le inf_le_left)) ?_
    obtain ⟨s, hs, hsa⟩ := exists_smul_mem (F := F) Λ (a i)
    rw [Submodule.ne_bot_iff]
    refine ⟨_, ⟨s • a i, ⟨hsa, (hW _ _).2 fun j hj => ?_⟩, rfl⟩, ?_⟩
    · simp [ha, hj.ne]
    · simpa [ha, Algebra.smul_def] using hs
  choose e he using hI
  have hv : ∀ i, ∃ v ∈ Λ, (∀ j, i < j → φ j v = 0) ∧ φ i v = (algebraMap O F q) ^ (e i) := by
    intro i
    have : (algebraMap O F q) ^ (e i) ∈ (Λ ⊓ W i).map ((φ i).restrictScalars O) := by
      rw [he]; exact Submodule.mem_span_singleton_self _
    obtain ⟨v, ⟨h1, h2⟩, h3⟩ := this
    exact ⟨v, h1, (hW _ _).1 h2, h3⟩
  choose v hvΛ hv0 hv1 using hv
  have hz : ∀ i, (algebraMap O F q) ^ (e i) ≠ 0 := fun i => zpow_ne_zero _ hq0
  refine ⟨e, fun i => ((algebraMap O F q) ^ (e i))⁻¹ • v i, fun i => ?_, fun i j hij => ?_, ?_⟩
  · rw [map_smul, hv1, smul_eq_mul, inv_mul_cancel₀ (hz i)]
  · rw [map_smul, hv0 i j hij, smul_zero]
  simp only [fun i => smul_inv_smul₀ (hz i) (v i)]
  refine le_antisymm ?_ (sup_le inf_le_left (iSup_le fun i => ?_))
  swap
  · rw [Submodule.span_singleton_le_iff_mem]; exact hvΛ i
  have key : ∀ k : ℕ, ∀ y ∈ Λ, (∀ j : Fin c, k ≤ j.1 → φ j y = 0) →
      y ∈ Λ ⊓ X.restrictScalars O ⊔ ⨆ i, Submodule.span O {v i} := by
    intro k
    induction k with
    | zero =>
      intro y hyΛ h
      refine Submodule.mem_sup_left ⟨hyΛ, ?_⟩
      have h1 := hy y
      simp only [fun j => h j (Nat.zero_le _), zero_smul, Finset.sum_const_zero, add_zero] at h1
      show y ∈ X
      rw [h1]
      exact (p y).2
    | succ k ih =>
      intro y hyΛ h
      by_cases hk : k < c
      · have : φ ⟨k, hk⟩ y ∈ (Λ ⊓ W ⟨k, hk⟩).map ((φ ⟨k, hk⟩).restrictScalars O) :=
          ⟨y, ⟨hyΛ, (hW _ _).2 fun j hj => h j hj⟩, rfl⟩
        rw [he, Submodule.mem_span_singleton] at this
        obtain ⟨o, ho⟩ := this
        have h2 := ih (y - o • v ⟨k, hk⟩) (sub_mem hyΛ (Λ.smul_mem _ (hvΛ _))) (fun j hj => by
          rcases hj.eq_or_lt with hj | hj
          · obtain rfl : j = ⟨k, hk⟩ := Fin.ext hj.symm
            rw [map_sub, LinearMap.map_smul_of_tower, hv1, ho, sub_self]
          · rw [map_sub, LinearMap.map_smul_of_tower, h j hj, hv0 ⟨k, hk⟩ j hj, smul_zero, sub_self])
        rw [← sub_add_cancel y (o • v ⟨k, hk⟩)]
        exact add_mem h2 (Submodule.mem_sup_right (Submodule.mem_iSup_of_mem ⟨k, hk⟩
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))))
      · exact ih y hyΛ (fun j hj => by have := j.2; omega)
  exact fun y hyΛ => key c y hyΛ (fun j hj => by have := j.2; omega)

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F] in
theorem moveBy_mul (g n : Y ≃ₗ[F] Y) (Λ : Submodule O Y) : moveBy (g * n) Λ = moveBy g (moveBy n Λ) := by
  unfold moveBy
  rw [← Submodule.map_comp]
  rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F] in
theorem moveBy_sup_iSup (g : Y ≃ₗ[F] Y) (M : Submodule O Y) (v : Fin c → Y) :
    moveBy g (M ⊔ ⨆ i, Submodule.span O {v i}) = moveBy g M ⊔ ⨆ i, Submodule.span O {g (v i)} := by
  unfold moveBy
  simp only [Submodule.map_sup, Submodule.map_iSup, Submodule.map_span, Set.image_singleton]
  rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F] in
theorem finiteDimensional_of_isLattice (Λ : Submodule O Y) [hΛ : Submodule.IsLattice F Λ] :
    FiniteDimensional F Y := by
  obtain ⟨s, hs⟩ := hΛ.fg
  refine ⟨⟨s, ?_⟩⟩
  rw [← hΛ.span_eq_top, ← hs, Submodule.span_span_of_tower]

end Main

theorem latticeNormalFormUnip : LatticeNormalFormUnip := by
  intro O F Y _ _ _ _ _ _ _ _ _ _ q hq c X a hfr Λ hΛ
  haveI := finiteDimensional_of_isLattice (F := F) Λ
  obtain ⟨p, φ, hp, hpa, hX, ha, hy⟩ := exists_coord hfr
  obtain ⟨e, u, hu1, hu0, hΛu⟩ := exists_adapted hq p φ ha hy Λ
  obtain ⟨n, hnX, hnu, hnf⟩ := exists_unip p φ hX ha hy (fun i => if i.1 = 0 then a i else u i)
    (fun i => by split_ifs <;> simp [ha, hu1])
    (fun i j hij => by split_ifs <;> simp [ha, hij.ne, hu0 i j hij])
  have hn0 : ∀ i : Fin c, i.1 = 0 → n (a i) = a i := fun i hi => by simpa [hi] using hnu i
  let z : Y := if h : 0 < c then (p (u ⟨0, h⟩) : Y) else 0
  have hz : z ∈ X := by
    simp only [z]
    split_ifs
    · exact (p _).2
    · exact zero_mem _
  refine ⟨n, e, z, ⟨hnX, hn0, hnf⟩, hz, ?_⟩
  conv_lhs => rw [hΛu]
  rw [moveBy_sup_iSup, normalForm]
  congr 1
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : (n.toLinearMap.restrictScalars O) x = x := hnX x hx.2
      rw [this]
      exact hx
    · intro hy'
      exact ⟨y, hy', hnX y hy'.2⟩
  · refine iSup_congr fun i => ?_
    rw [map_smul]
    congr 3
    by_cases hi : i.1 = 0
    · have hc : 0 < c := by have := i.2; omega
      obtain rfl : i = ⟨0, hc⟩ := Fin.ext hi
      have h1 : u ⟨0, hc⟩ = a ⟨0, hc⟩ + z := by
        conv_lhs => rw [hy (u ⟨0, hc⟩)]
        rw [Finset.sum_eq_single ⟨0, hc⟩, hu1, one_smul, add_comm]
        · simp [z, hc]
        · intro j _ hj
          rw [hu0 _ j (Fin.lt_def.2 (Nat.pos_of_ne_zero fun h => hj (Fin.ext h))), zero_smul]
        · simp
      rw [h1, map_add, hn0 _ rfl, hnX z hz]
      simp
    · simpa [hi] using hnu i

theorem latticeNormalForm : LatticeNormalForm := by
  intro O F Y _ _ _ _ _ _ _ _ _ _ q hq c X a hfr L hL Λ hΛ
  obtain ⟨n, e, z, hn, hz, hnΛ⟩ := latticeNormalFormUnip O F Y q hq c X a hfr Λ hΛ
  let M : Submodule O X := Λ.comap (X.subtype.restrictScalars O)
  have hM : inY X M = Λ ⊓ X.restrictScalars O := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨y, h2⟩, h1, rfl⟩
  haveI : Submodule.IsLattice F M := by
    constructor
    · refine Submodule.fg_of_fg_map_injective (X.subtype.restrictScalars O) X.injective_subtype ?_
      have : (inY X M).FG := by
        rw [hM]
        exact hΛ.fg.of_le inf_le_left
      exact this
    · rw [eq_top_iff]
      intro x _
      obtain ⟨s, hs, hsx⟩ := exists_smul_mem (F := F) Λ (x : Y)
      have hs' : algebraMap O F s ≠ 0 := by simpa using hs
      have h1 : s • x ∈ Submodule.span F (M : Set X) := Submodule.subset_span hsx
      rw [← algebraMap_smul F] at h1
      exact (Submodule.smul_mem_iff _ hs').1 h1
  obtain ⟨γ, hγ⟩ := exists_equiv_map_eq (F := F) M L
  let P := Submodule.prodEquivOfIsCompl _ _ hfr.2
  let g : Y ≃ₗ[F] Y := P.symm ≪≫ₗ (γ.prodCongr (LinearEquiv.refl F _)) ≪≫ₗ P
  have hgX : ∀ x : X, g x = (γ x : Y) := fun x => by simp [g, P]
  have hga : ∀ i, g (a i) = a i := fun i => by
    have := Submodule.prodEquivOfIsCompl_symm_apply_right _ _ hfr.2
      ⟨a i, Submodule.subset_span ⟨i, rfl⟩⟩
    simp only at this
    simp [g, P, this]
  refine ⟨g * n, e, γ ⟨z, hz⟩, ⟨γ, g, n, ⟨hgX, hga⟩, hn, rfl⟩, (γ _).2, ?_⟩
  rw [moveBy_mul, hnΛ, normalForm, moveBy_sup_iSup, normalForm, ← hM, ← hγ]
  congr 1
  · unfold moveBy inY
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
    ext x
    exact hgX x
  · refine iSup_congr fun i => ?_
    rw [map_smul, map_add, hga]
    congr 4
    split_ifs
    · exact hgX ⟨z, hz⟩
    · exact map_zero g

end GlobalTheory.Proof.LatticeNormalFormUnipotent
