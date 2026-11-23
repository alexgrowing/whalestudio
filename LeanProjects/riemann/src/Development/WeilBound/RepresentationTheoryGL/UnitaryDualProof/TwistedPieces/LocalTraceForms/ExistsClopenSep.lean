import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.LocChi
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed
import GroundTheory.AutomorphicForms.WhittakerDistribution

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker Set

namespace PositivityTheory.RgUd.TP.Loc.Psplit

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

section Sep

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

theorem exists_clopen_in {S A B : Set X} (hSc : IsCompact S) (hSo : IsOpen S) (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) : ∃ W : Set X, IsClopen W ∧ W ⊆ S ∧ A ∩ S ⊆ W ∧ Disjoint W B := by
  have hK : IsCompact (A ∩ S) := hSc.inter_left hA
  have key : ∀ x ∈ A ∩ S, ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ S \ B := by
    intro x hx
    have hxo : x ∈ S \ B := ⟨hx.2, fun hb => disjoint_left.1 hAB hx.1 hb⟩
    exact loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 ((hSo.sdiff hB).mem_nhds hxo)
  choose V hV using key
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : ↥(A ∩ S) => V x.1 x.2)
    (fun x => (hV x.1 x.2).1.isOpen) (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hV x hx).2.1⟩)
  refine ⟨⋃ i ∈ t, V i.1 i.2, ?_, ?_, ht, ?_⟩
  · exact t.finite_toSet.isClopen_biUnion (fun i _ => (hV i.1 i.2).1)
  · exact iUnion₂_subset fun i _ => ((hV i.1 i.2).2.2).trans diff_subset
  · refine disjoint_left.2 fun y hy hyB => ?_
    obtain ⟨i, -, hyi⟩ := mem_iUnion₂.1 hy
    exact ((hV i.1 i.2).2.2 hyi).2 hyB

variable [SigmaCompactSpace X]

theorem exists_exhaust : ∃ U : ℕ → Set X, (∀ m, IsCompact (U m) ∧ IsOpen (U m)) ∧ ∀ x, ∃ m, x ∈ U m := by
  have hW : ∀ x : X, ∃ W : Set X, IsCompact W ∧ IsOpen W ∧ x ∈ W := by
    intro x
    obtain ⟨C, hC, hxC⟩ := exists_compact_mem_nhds x
    obtain ⟨V, hV, hxV, hVC⟩ :=
      loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 (interior_mem_nhds.2 hxC)
    exact ⟨V, hC.of_isClosed_subset hV.1 (hVC.trans interior_subset), hV.2, hxV⟩
  choose W hWc hWo hxW using hW
  have hU : ∀ m : ℕ, ∃ U : Set X, IsCompact U ∧ IsOpen U ∧ compactCovering X m ⊆ U := by
    intro m
    obtain ⟨t, ht⟩ := (isCompact_compactCovering X m).elim_finite_subcover W hWo
      (fun x _ => mem_iUnion.2 ⟨x, hxW x⟩)
    exact ⟨⋃ i ∈ t, W i, t.isCompact_biUnion (fun i _ => hWc i), isOpen_biUnion (fun i _ => hWo i), ht⟩
  choose U hUc hUo hKU using hU
  refine ⟨U, fun m => ⟨hUc m, hUo m⟩, fun x => ?_⟩
  obtain ⟨m, hm⟩ := exists_mem_compactCovering x
  exact ⟨m, hKU m hm⟩

theorem exists_clopen_sep {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ W : Set X, IsClopen W ∧ A ⊆ W ∧ Disjoint W B := by
  obtain ⟨U, hU, hcov⟩ := exists_exhaust (X := X)
  let D : ℕ → Set X := fun m => U m \ ⋃ j ∈ Finset.range m, U j
  have hD : ∀ m, D m = U m \ ⋃ j ∈ Finset.range m, U j := fun m => rfl
  have hUcl : ∀ j, IsClosed (U j) := fun j => (hU j).1.isClosed
  have hDc : ∀ m, IsCompact (D m) := fun m => by
    rw [hD]
    exact (hU m).1.diff (isOpen_biUnion fun j _ => (hU j).2)
  have hDo : ∀ m, IsOpen (D m) := fun m => by
    rw [hD]
    exact (hU m).2.sdiff (isClosed_biUnion_finset fun j _ => hUcl j)
  choose W hW using fun m => exists_clopen_in (hDc m) (hDo m) hA hB hAB
  have hDdisj : ∀ m m', m ≠ m' → Disjoint (D m) (D m') := by
    have key : ∀ m m', m < m' → Disjoint (D m) (D m') := by
      intro m m' h
      rw [hD, hD]
      refine disjoint_left.2 fun x hx hx' => hx'.2 ?_
      exact mem_iUnion₂.2 ⟨m, Finset.mem_range.2 h, hx.1⟩
    intro m m' h
    rcases lt_or_gt_of_ne h with h | h
    · exact key m m' h
    · exact (key m' m h).symm
  have hmemD : ∀ x, ∃ m, x ∈ D m := by
    intro x
    classical
    have hex : ∃ m, x ∈ U m := hcov x
    refine ⟨Nat.find hex, ?_⟩
    rw [hD]
    refine ⟨Nat.find_spec hex, fun hx => ?_⟩
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hx
    exact Nat.find_min hex (Finset.mem_range.1 hj) hxj
  have hlf : LocallyFinite W := by
    intro x
    obtain ⟨m, hm⟩ := hmemD x
    refine ⟨D m, (hDo m).mem_nhds hm, (Set.finite_singleton m).subset ?_⟩
    rintro j ⟨y, hyW, hyD⟩
    by_contra hj
    exact disjoint_left.1 (hDdisj j m hj) ((hW j).2.1 hyW) hyD
  refine ⟨⋃ m, W m, ⟨hlf.isClosed_iUnion (fun m => (hW m).1.1),
    isOpen_iUnion fun m => (hW m).1.2⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨m, hm⟩ := hmemD x
    exact mem_iUnion.2 ⟨m, (hW m).2.2.1 ⟨hx, hm⟩⟩
  · exact disjoint_iUnion_left.2 fun m => (hW m).2.2.2

end Sep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem exists_clopens {m : ℕ} (F : Fin m → Set (Matrix (Fin n) (Fin n) k)) (hF : ∀ i, IsClosed (F i))
    (hd : ∀ i j, i ≠ j → Disjoint (F i) (F j)) :
    ∃ W : Fin m → Set (Matrix (Fin n) (Fin n) k), (∀ i, IsClopen (W i) ∧ F i ⊆ W i) ∧
      (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧ ∀ i j, i ≠ j → Disjoint (W i) (F j) := by
  classical
  have hna : NonarchimedeanRing k := by
    convert! (ValuativeRel.nonarchimedeanRing k)
    exact Valuation.toTopologicalSpace_eq _
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  haveI : SigmaCompactSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (SigmaCompactSpace (Fin n → Fin n → k))
  let B : Fin m → Set (Matrix (Fin n) (Fin n) k) := fun i => ⋃ j ∈ Finset.univ.filter (· ≠ i), F j
  have hBmem : ∀ i j, j ≠ i → ∀ x ∈ F j, x ∈ B i := fun i j h x hx =>
    mem_iUnion₂.2 ⟨j, by simp [h], hx⟩
  have hBcl : ∀ i, IsClosed (B i) := fun i => isClosed_biUnion_finset fun j _ => hF j
  have hFB : ∀ i, Disjoint (F i) (B i) := by
    intro i
    refine disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hx'
    have hji : j ≠ i := by simpa using hj
    exact disjoint_left.1 (hd i j (Ne.symm hji)) hx hxj
  choose V hV using fun i => Psplit.exists_clopen_sep (hF i) (hBcl i) (hFB i)
  refine ⟨fun i => V i ∩ ⋂ j ∈ Finset.univ.filter (· ≠ i), (V j)ᶜ, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(hV i).1.inter (isClopen_biInter_finset fun j _ => (hV j).1.compl), ?_⟩
    intro x hx
    refine ⟨(hV i).2.1 hx, mem_iInter₂.2 fun j hj => ?_⟩
    have hji : j ≠ i := by simpa using hj
    exact fun hxV => disjoint_left.1 (hV j).2.2 hxV (hBmem j i (Ne.symm hji) x hx)
  · intro i j hij
    refine disjoint_left.2 fun x hx hx' => ?_
    exact mem_iInter₂.1 hx'.2 i (by simp [hij]) hx.1
  · intro i j hij
    refine disjoint_left.2 fun x hx hx' => ?_
    exact disjoint_left.1 (hV i).2.2 hx.1 (hBmem i j (Ne.symm hij) x hx')

private theorem comp_act_mem_supportedIn_univ (g : GL (Fin n) k) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn (univ : Set (Sp k n))) :
    (fun p => f (act g p)) ∈ supportedIn (univ : Set (Sp k n)) := by
  have hc : ∀ h : GL (Fin n) k, Continuous (act h : Sp k n → Sp k n) := by
    intro h
    unfold act
    exact ((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).prodMk
      (continuous_const.matrix_mulVec continuous_snd)
  let e : Sp k n ≃ₜ Sp k n :=
    { toFun := act g
      invFun := act g⁻¹
      left_inv := fun p => by rw [← Nil.Orb.act_mul, inv_mul_cancel, Nil.Orb.act_one]
      right_inv := fun p => by rw [← Nil.Orb.act_mul, mul_inv_cancel, Nil.Orb.act_one]
      continuous_toFun := hc g
      continuous_invFun := hc g⁻¹ }
  have h := (compHomeoL e ⟨f, hf.1⟩).property
  rw [coe_compHomeoL] at h
  exact ⟨h, subset_univ _⟩

theorem split_pf : PositivityTheory.RgUd.TP.Loc.Split k := by
  intro n Z m F hF hd ξ hsupp hinv
  obtain ⟨W, hW, hWd, hWF⟩ := exists_clopens F (fun i => (hF i).1) hd
  have hWp : ∀ i, IsClopen (W i ×ˢ (univ : Set (Fin n → k))) := fun i => (hW i).1.prod isClopen_univ
  let mul : Set (Sp k n) → (Sp k n → ℂ) →ₗ[ℂ] (Sp k n → ℂ) := fun A =>
    { toFun := fun f p => A.indicator 1 p * f p
      map_add' := fun f g => by
        funext p
        simp only [Pi.add_apply, mul_add]
      map_smul' := fun c f => by
        funext p
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  have hmul : ∀ A f p, mul A f p = A.indicator 1 p * f p := fun _ _ _ => rfl
  have hind : ∀ (A : Set (Sp k n)) p, p ∈ A → A.indicator (1 : Sp k n → ℂ) p = 1 :=
    fun A p h => by simp [h]
  have hind0 : ∀ (A : Set (Sp k n)) p, p ∉ A → A.indicator (1 : Sp k n → ℂ) p = 0 :=
    fun A p h => by simp [h]
  refine ⟨fun i => ξ ∘ₗ mul (W i ×ˢ univ), fun i => ⟨?_, ?_⟩, ?_⟩
  · intro f hf hf0
    simp only [LinearMap.comp_apply]
    apply hsupp _ (indicator_mul_mem (hWp i) hf)
    rintro ⟨x, v⟩ ⟨hx, -⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    by_cases hij : i = j
    · subst hij
      show _ * f (x, v) = 0
      rw [hf0 (x, v) ⟨hj, mem_univ _⟩, mul_zero]
    · show _ * _ = 0
      rw [hind0 (W i ×ˢ univ) (x, v) (fun h => disjoint_left.1 (hWF i j hij) h.1 hj), zero_mul]
  · intro g hg f hf
    simp only [LinearMap.comp_apply]
    have hfg := comp_act_mem_supportedIn_univ g hf
    have h1 : ξ (fun p => mul (W i ×ˢ univ) f (act g p)) = ξ (mul (W i ×ˢ univ) f) :=
      hinv g hg _ (indicator_mul_mem (hWp i) hf)
    rw [← h1, ← sub_eq_zero, ← map_sub]
    apply hsupp
    · exact sub_mem (indicator_mul_mem (hWp i) hfg) (comp_act_mem_supportedIn_univ g (indicator_mul_mem (hWp i) hf))
    · rintro ⟨x, v⟩ ⟨hx, -⟩
      obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      have hgx := (hF j).2 g hg x hj
      simp only [Pi.sub_apply, hmul]
      have e : (W i ×ˢ (univ : Set (Fin n → k))).indicator (1 : Sp k n → ℂ) (x, v) =
          (W i ×ˢ (univ : Set (Fin n → k))).indicator 1 (act g (x, v)) := by
        by_cases hij : i = j
        · subst hij
          rw [hind (W i ×ˢ univ) (x, v) ⟨(hW i).2 hj, mem_univ _⟩,
            hind (W i ×ˢ univ) (act g (x, v)) ⟨(hW i).2 hgx, mem_univ _⟩]
        · rw [hind0 (W i ×ˢ univ) (x, v) (fun h => disjoint_left.1 (hWF i j hij) h.1 hj),
            hind0 (W i ×ˢ univ) (act g (x, v)) (fun h => disjoint_left.1 (hWF i j hij) h.1 hgx)]
      rw [e, sub_self]
  · intro f hf
    simp only [LinearMap.comp_apply]
    rw [← sub_eq_zero, ← map_sum, ← map_sub]
    apply hsupp
    · exact sub_mem hf (sum_mem fun i _ => indicator_mul_mem (hWp i) hf)
    · rintro ⟨x, v⟩ ⟨hx, -⟩
      obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      rw [Pi.sub_apply, Finset.sum_apply, Finset.sum_eq_single j]
      · rw [hmul, hind (W j ×ˢ univ) (x, v) ⟨(hW j).2 hj, mem_univ _⟩, one_mul, sub_self]
      · intro i _ hij
        rw [hmul, hind0 (W i ×ˢ univ) (x, v)
          (fun h => disjoint_left.1 (hWd i j hij) h.1 ((hW j).2 hj)), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ j) h

end PositivityTheory.RgUd.TP.Loc.Psplit
