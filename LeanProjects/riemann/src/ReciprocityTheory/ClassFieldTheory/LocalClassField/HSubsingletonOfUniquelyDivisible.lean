import Mathlib
import ReciprocityTheory.NeutralLocalFields.Duality
import ReciprocityTheory.GroupCohomology.ImportsAlt
import ReciprocityTheory.ClassFieldTheory.LocalClassField.QZDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.MemZmultiplesOfAddOrderOf

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function

noncomputable section

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem h_subsingleton_of_uniquely_divisible [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {R : Type} [CommRing R]
    (M : TRep R G) [DiscreteTopology M.V] (hM : ∀ k : ℕ, 0 < k → Bijective fun m : M.V => k • m)
    (n : ℕ) (hn : 0 < n) : Subsingleton (M.H n) := by
  suffices h : ∀ x : M.H n, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨-, h⟩ := finiteLevel_holds R G M n x
  obtain ⟨k, hk, hkx⟩ := h hn
  let e : M.V ≃ₗ[R] M.V := LinearEquiv.ofBijective ((k : R) • LinearMap.id) (by
    have := hM k hk
    convert this using 2 with m
    simp [Nat.cast_smul_eq_nsmul])
  have he : ∀ m, e m = (k : R) • m := fun m => rfl
  let Q : Pair M M := Pair.ofMap e.symm.toLinearMap continuous_of_discreteTopology (by
    intro g m
    apply e.injective
    show e (e.symm _) = e (M.rho g (e.symm m))
    rw [e.apply_symm_apply, he, ← map_smul, ← he, e.apply_symm_apply])
  have hQ : ∀ y : M.H n, (k : R) • Q.hom.H n y = y := by
    intro y
    induction y using Cx.H_ind with
    | h c hc =>
      rw [Cx.Hom.H_cls, Cx.cls_smul]
      refine Cx.cls_congr _ _ (Subtype.ext (funext fun g => ?_))
      exact e.apply_symm_apply _
  rw [← hQ x, ← map_smul, Nat.cast_smul_eq_nsmul, hkx, map_zero]

theorem h_subsingleton_of_divisible [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (M : TRep ℤ G) [DiscreteTopology M.V] (hM : ∀ k : ℕ, 0 < k → Bijective fun m : M.V => k • m)
    (n : ℕ) (hn : 0 < n) : Subsingleton (M.H n) :=
  h_subsingleton_of_uniquely_divisible G M hM n hn

theorem h_rat_subsingleton [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (n : ℕ) (hn : 0 < n) :
    Subsingleton ((trivRep G ℚ).H n) := by
  refine h_subsingleton_of_divisible G (trivRep G ℚ) (fun k hk => ?_) n hn
  show Bijective fun m : ℚ => k • m
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun a b h => ?_, fun y => ⟨y / k, ?_⟩⟩
  · simpa [nsmul_eq_mul, hk'] using h
  · simp only [nsmul_eq_mul]; field_simp

theorem admissible_int_rat_sequence : admitted (trivMap G (Int.castAddHom ℚ)) (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)) where
  i_id := rfl
  p_id := rfl
  emb := by
    have hi : Injective (trivMap G (Int.castAddHom ℚ)).u := Int.cast_injective (α := ℚ)
    exact (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_of_discreteTopology hi
      fun _ _ => isOpen_discrete _).isEmbedding
  exact := by
    intro (y : ℚ)
    show (QuotientAddGroup.mk y : QZ) = 0 ↔ y ∈ Set.range (Int.castAddHom ℚ)
    rw [QuotientAddGroup.eq_zero_iff]; rfl
  sec := ⟨Function.surjInv (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range),
    continuous_of_discreteTopology, Function.surjInv_eq _⟩

theorem conn_int_rat_bijective [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (δ : ∀ n, (trivRep G QZ).H n →ₗ[ℤ] (trivRep G ℤ).H (n + 1))
    (hδ : Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ) (n : ℕ) (hn : 0 < n) :
    Bijective (δ n) := by
  have hs := admissibility_holds ℤ G _ _ _ _ _ (admissible_int_rat_sequence G)
  obtain ⟨⟨δ', h1, h2⟩, hu⟩ := lES_holds ℤ _ _ _ _ _ hs
  obtain rfl := hu δ δ' hδ h1
  have s1 := h_rat_subsingleton G n hn
  have s2 := h_rat_subsingleton G (n + 1) n.succ_pos
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (h2.exC n x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  · intro y
    exact (h2.exA n y).1 (Subsingleton.elim _ _)

def oneCocycleEquivCharacters : Gal.Z1 (trivRep G QZ).rho ≃+ charGrp G where
  toFun c := ⟨AddMonoidHom.mk' (fun a : Additive G => (c.1 a.toMul : QZ)) fun a b => c.2.2 a.toMul b.toMul,
    (@IsLocallyConstant.iff_continuous G (trivRep G QZ).V _ _ _ c.1).2 c.2.1⟩
  invFun χ := ⟨fun g => χ.1 (Additive.ofMul g),
    (@IsLocallyConstant.iff_continuous G (trivRep G QZ).V _ _ _ _).1 χ.2,
    fun g h => map_add χ.1 (Additive.ofMul g) (Additive.ofMul h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem one_coboundaries_trivial_eq_bot (A : Type) [AddCommGroup A] : Gal.B1 (trivRep G A).rho = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨m, rfl⟩
  refine (Submodule.mem_bot _).2 (funext fun g => ?_)
  exact sub_self m

theorem exists_h1_equiv_characters : ∃ e : (trivRep G QZ).H 1 ≃+ charGrp G,
    ∀ x hx g, (e ((trivRep G QZ).coch.cls 1 x hx)).1 (Additive.ofMul g) = x.1 ![g] := by
  obtain ⟨-, -, ⟨e, he⟩, -⟩ := low_holds ℤ G (trivRep G QZ)
  have hB : (Gal.B1 (trivRep G QZ).rho).comap (Gal.Z1 (trivRep G QZ).rho).subtype = ⊥ := by
    rw [one_coboundaries_trivial_eq_bot, Submodule.comap_bot, Submodule.ker_subtype]
  refine ⟨e.toAddEquiv.trans ((Submodule.quotEquivOfEqBot _ hB).toAddEquiv.trans (oneCocycleEquivCharacters G)), ?_⟩
  intro x hx g
  obtain ⟨hz, h⟩ := he x hx
  show (oneCocycleEquivCharacters G (Submodule.quotEquivOfEqBot _ hB (e _))).1 (Additive.ofMul g) = _
  rw [h, Submodule.quotEquivOfEqBot_apply_mk]
  rfl

theorem exists_h2_int_equiv_characters [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    ∃ e : (trivRep G ℤ).H 2 ≃+ charGrp G, ∀ δ, Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ →
      ∀ x hx g, (e (δ 1 ((trivRep G QZ).coch.cls 1 x hx))).1 (Additive.ofMul g) = x.1 ![g] := by
  have hs := admissibility_holds ℤ G _ _ _ _ _ (admissible_int_rat_sequence G)
  obtain ⟨⟨δ', h1, -⟩, hu⟩ := lES_holds ℤ _ _ _ _ _ hs
  obtain ⟨e, he⟩ := exists_h1_equiv_characters G
  let d : (trivRep G QZ).H 1 ≃+ (trivRep G ℤ).H 2 :=
    AddEquiv.ofBijective (δ' 1).toAddMonoidHom (conn_int_rat_bijective G δ' h1 1 one_pos)
  refine ⟨d.symm.trans e, fun δ hδ x hx g => ?_⟩
  obtain rfl := hu δ δ' hδ h1
  show (e (d.symm (d _))).1 _ = _
  rw [d.symm_apply_apply, he]

theorem charGrp_eval_injective (s : G) (hs : Dense (Subgroup.zpowers s : Set G)) :
    Injective fun χ : charGrp G => χ.1 (Additive.ofMul s) := by
  have key : ∀ ψ : charGrp G, ψ.1 (Additive.ofMul s) = 0 → ψ = 0 := by
    intro ψ h
    have hcl : IsClosed {g : G | ψ.1 (Additive.ofMul g) = 0} := (IsLocallyConstant.isClopen_fiber ψ.2 0).1
    have hsub : (Subgroup.zpowers s : Set G) ⊆ {g : G | ψ.1 (Additive.ofMul g) = 0} := by
      rintro _ ⟨k, rfl⟩
      show ψ.1 (Additive.ofMul (s ^ k)) = 0
      rw [ofMul_zpow, map_zsmul, h, smul_zero]
    have hall := closure_minimal hsub hcl
    rw [hs.closure_eq] at hall
    exact Subtype.ext (AddMonoidHom.ext fun a => hall (Set.mem_univ a.toMul))
  intro χ χ' h
  refine sub_eq_zero.1 (key (χ - χ') ?_)
  show χ.1 (Additive.ofMul s) - χ'.1 (Additive.ofMul s) = 0
  exact sub_eq_zero.2 h

theorem charGrp_eval_bijective [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (s : G)
    (hs : IsZHat G s) : Bijective fun χ : charGrp G => χ.1 (Additive.ofMul s) := by
  refine ⟨charGrp_eval_injective G s hs.1, fun (q : (trivRep G QZ).V) => ?_⟩
  obtain ⟨⟨e, he⟩, -⟩ := zHat_holds ℤ G s hs (trivRep G QZ) RationalModIntegerChains.qz_torsion
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk q))
  have h := he c
  rw [hc, e.apply_symm_apply] at h
  obtain ⟨m, hm⟩ := (Submodule.Quotient.eq _).1 h
  have hm' : 0 = q - c.1 s := by rw [← hm]; exact (sub_self m).symm
  exact ⟨oneCocycleEquivCharacters G c, (sub_eq_zero.1 hm'.symm).symm⟩

theorem exists_h2_int_equiv_rat_mod_int [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (s : G)
    (hs : IsZHat G s) : ∃ e : (trivRep G ℤ).H 2 ≃+ QZ, ∀ δ, Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ →
      ∀ x hx, e (δ 1 ((trivRep G QZ).coch.cls 1 x hx)) = x.1 ![s] := by
  obtain ⟨e, he⟩ := exists_h2_int_equiv_characters G
  let ev : charGrp G →+ QZ :=
    { toFun := fun χ => χ.1 (Additive.ofMul s), map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact ⟨e.trans (AddEquiv.ofBijective ev (charGrp_eval_bijective G s hs)),
    fun δ hδ x hx => he δ hδ x hx s⟩

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
