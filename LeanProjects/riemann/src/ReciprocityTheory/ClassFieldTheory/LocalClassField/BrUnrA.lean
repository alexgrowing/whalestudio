import Mathlib
import ReciprocityTheory.GroupCohomology.ImportsAlt
import ReciprocityTheory.ClassFieldTheory.LocalClassField.HSubsingletonOfUniquelyDivisible
import ReciprocityTheory.ClassFieldTheory.LocalClassField.FinCoh

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function

noncomputable section

theorem bijective_H_of_adm {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B C : TRep ℤ G}
    {i : Pair A B} {q : Pair B C} (h : admitted i q) (n : ℕ) (h1 : Subsingleton (A.H n))
    (h2 : Subsingleton (A.H (n + 1))) : Bijective (q.hom.H n) := by
  have hs := admissibility_holds ℤ G _ _ _ _ _ h
  obtain ⟨⟨δ, -, hl⟩, -⟩ := lES_holds ℤ _ _ _ _ _ hs
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (hl.exB n x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  · intro y
    exact (hl.exC n y).1 (Subsingleton.elim _ _)

theorem card_QZ_torsion (n : ℕ) (hn : 0 < n) : Nat.card {a : QZ // n • a = 0} = n := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  let f : ℤ →+ QZ := (QuotientAddGroup.mk' (Int.castAddHom ℚ).range).comp
    ((AddMonoidHom.mulRight (1 / (n : ℚ))).comp (Int.castAddHom ℚ))
  have hf : ∀ k : ℤ, f k = QuotientAddGroup.mk ((k : ℚ) * (1 / (n : ℚ))) := fun _ => rfl
  have hker : f.ker = AddSubgroup.zmultiples (n : ℤ) := by
    ext k
    rw [AddMonoidHom.mem_ker, hf, QuotientAddGroup.eq_zero_iff, Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      have hj' : (j : ℚ) = (k : ℚ) * (1 / (n : ℚ)) := hj
      have : (k : ℚ) = (n : ℚ) * j := by rw [hj']; field_simp
      exact_mod_cast this
    · rintro ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      show (j : ℚ) = (((n : ℤ) * j : ℤ) : ℚ) * (1 / (n : ℚ))
      push_cast
      field_simp
  have hr : ∀ a : QZ, n • a = 0 ↔ a ∈ f.range := by
    intro a
    constructor
    · intro ha
      obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective a
      have h1 : ((n • q : ℚ) : QZ) = 0 := ha
      rw [QuotientAddGroup.eq_zero_iff] at h1
      obtain ⟨j, hj⟩ := h1
      have hj' : (j : ℚ) = n • q := hj
      refine ⟨j, ?_⟩
      rw [hf, hj', nsmul_eq_mul]
      congr 1
      field_simp
    · rintro ⟨k, rfl⟩
      rw [hf]
      show ((n • ((k : ℚ) * (1 / (n : ℚ))) : ℚ) : QZ) = 0
      rw [QuotientAddGroup.eq_zero_iff]
      refine ⟨k, ?_⟩
      show (k : ℚ) = n • ((k : ℚ) * (1 / (n : ℚ)))
      rw [nsmul_eq_mul]
      field_simp
  have hc : Nat.card f.range = n := by
    rw [← AddSubgroup.index_ker, hker, Int.index_zmultiples]
    simp
  exact (Nat.card_congr (Equiv.subtypeEquivRight hr)).trans hc

theorem card_h2_trivial_int_cyclic (C : Type) [Group C] [Finite C] [TopologicalSpace C] [IsTopologicalGroup C]
    [DiscreteTopology C] (g : C) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ((trivRep C ℤ).H 2) = Nat.card C := by
  let _ : CommGroup C :=
    { (inferInstance : Group C) with
      mul_comm := fun a b => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
        rw [← zpow_add, ← zpow_add, add_comm] }
  let _ : Fintype C := Fintype.ofFinite C
  obtain ⟨e⟩ := nonempty_cyclic_even (trivRep C ℤ) g hg 2 two_ne_zero even_two
  rw [Nat.card_congr e.toEquiv]
  have hinv : ∀ k : ℤ, (k : (trivRep C ℤ).V) ∈ (trivRep C ℤ).rho.invariants := fun k _ => rfl
  let f : ℤ →+ ((trivRep C ℤ).rho.invariants ⧸
      (LinearMap.range (trivRep C ℤ).rho.norm).comap (trivRep C ℤ).rho.invariants.subtype) :=
    { toFun := fun k => Submodule.Quotient.mk ⟨k, hinv k⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hnorm : ∀ k : (trivRep C ℤ).V, (trivRep C ℤ).rho.norm k = ((Nat.card C : ℤ) * (show ℤ from k) : ℤ) := by
    intro k
    have h0 : ∀ g : C, (trivRep C ℤ).rho g k = k := fun _ => rfl
    rw [Representation.norm, LinearMap.sum_apply, Finset.sum_congr rfl (fun g _ => h0 g), Finset.sum_const,
      Finset.card_univ, Nat.card_eq_fintype_card]
    exact nsmul_eq_mul (Fintype.card C) (show ℤ from k)
  have hsurj : Surjective f := by
    intro y
    obtain ⟨⟨k, hk⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨k, rfl⟩
  have hker : f.ker = AddSubgroup.zmultiples (Nat.card C : ℤ) := by
    ext k
    rw [AddMonoidHom.mem_ker, Int.mem_zmultiples_iff]
    show Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, ((hnorm j).symm.trans hj).symm⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, (hnorm j).trans hj.symm⟩
  have h1 : Nat.card f.range = Nat.card C := by
    rw [← AddSubgroup.index_ker, hker, Int.index_zmultiples]
    simp
  rw [← h1, AddMonoidHom.range_eq_top.2 hsurj]
  exact (Nat.card_congr (Equiv.Set.univ _)).symm

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G']

def trivInfl (φ : G' →* G) (hφ : Continuous φ) (A : Type) [AddCommGroup A] :
    Pair (trivRep G A) (trivRep G' A) where
  φ := φ
  u := (LinearMap.id : A →ₗ[ℤ] A)
  φ_cont := hφ
  u_cont := continuous_of_discreteTopology
  equiv _ _ := rfl

theorem trivial_inflation_h1_rat_mod_int_injective (φ : G' →* G) (hφ : Continuous φ) (hs : Surjective φ) :
    Injective ((trivInfl φ hφ QZ).hom.H 1) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨x, hx, rfl⟩ := Cx.exists_cls c
  obtain ⟨e, he⟩ := exists_h1_equiv_characters G
  obtain ⟨e', he'⟩ := exists_h1_equiv_characters G'
  apply e.injective
  rw [map_zero]
  refine Subtype.ext (AddMonoidHom.ext fun a => ?_)
  obtain ⟨g', hg'⟩ := hs a.toMul
  rw [Cx.Hom.H_cls] at hc
  have h1 := he' _ ((trivInfl φ hφ QZ).hom.d_f_eq_zero hx) g'
  rw [hc, map_zero] at h1
  have h2 := he x hx (φ g')
  rw [hg'] at h2
  have h3 : (fun i => φ ((![g'] : Fin 1 → G') i)) = ![a.toMul] := by
    funext i; fin_cases i; exact hg'
  have h4 : (((trivInfl φ hφ QZ).hom.f 1 x).1 ![g'] : QZ) = x.1 ![a.toMul] := congrArg x.1 h3
  exact h2.trans (h4.symm.trans h1.symm)

theorem trivial_inflation_h2_int_injective [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [CompactSpace G']
    [T2Space G'] [TotallyDisconnectedSpace G'] (φ : G' →* G) (hφ : Continuous φ) (hs : Surjective φ) :
    Injective ((trivInfl φ hφ ℤ).hom.H 2) := by
  have s := admissibility_holds ℤ G _ _ _ _ _ (admissible_int_rat_sequence G)
  have s' := admissibility_holds ℤ G' _ _ _ _ _ (admissible_int_rat_sequence G')
  obtain ⟨⟨δ, h1, -⟩, -⟩ := lES_holds ℤ _ _ _ _ _ s
  obtain ⟨⟨δ', h1', -⟩, -⟩ := lES_holds ℤ _ _ _ _ _ s'
  have hnat := connNat_holds ℤ _ _ _ _ _ _ _ _ _ _ (trivInfl φ hφ ℤ).hom (trivInfl φ hφ ℚ).hom
    (trivInfl φ hφ QZ).hom δ δ' s s' (fun _ _ => rfl) (fun _ _ => rfl) h1 h1' 1
  intro a b hab
  obtain ⟨a', rfl⟩ := (conn_int_rat_bijective G δ h1 1 one_pos).2 a
  obtain ⟨b', rfl⟩ := (conn_int_rat_bijective G δ h1 1 one_pos).2 b
  have hab' : δ' 1 ((trivInfl φ hφ QZ).hom.H 1 a') = δ' 1 ((trivInfl φ hφ QZ).hom.H 1 b') :=
    (hnat a').trans (hab.trans (hnat b').symm)
  rw [trivial_inflation_h1_rat_mod_int_injective φ hφ hs ((conn_int_rat_bijective G' δ' h1' 1 one_pos).1 hab')]

theorem conn_cls_of_lift (δ)
    (hδ : Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ)
    (t : G → ℚ) (ht : IsLocallyConstant t) (m : (Fin 2 → G) → ℤ)
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) :
    ∃ (x : (trivRep G QZ).coch.X 1) (hx : (trivRep G QZ).coch.d 1 x = 0) (y : (trivRep G ℤ).coch.X 2)
      (hy : (trivRep G ℤ).coch.d 2 y = 0), (∀ g, x.1 g = (QuotientAddGroup.mk (t (g 0)) : QZ)) ∧ y.1 = m ∧
      δ 1 ((trivRep G QZ).coch.cls 1 x hx) = (trivRep G ℤ).coch.cls 2 y hy := by
  have hs := admissibility_holds ℤ G _ _ _ _ _ (admissible_int_rat_sequence G)
  have hb : @Continuous _ (trivRep G ℚ).V _ _ (fun g : Fin 1 → G => t (g 0)) :=
    IsLocallyConstant.continuous (Y := (trivRep G ℚ).V) (ht.comp_continuous (continuous_apply 0))
  let b : (trivRep G ℚ).coch.X 1 := ⟨fun g => t (g 0), hb⟩
  have hmc : IsLocallyConstant m := by
    apply IsLocallyConstant.desc m (Int.cast : ℤ → ℚ) _ Int.cast_injective
    have h0 : ((Int.cast : ℤ → ℚ) ∘ m) = fun g => t (g 0) + t (g 1) - t (g 0 * g 1) := funext hm
    rw [h0]
    exact ((ht.comp_continuous (continuous_apply 0)).add (ht.comp_continuous (continuous_apply 1))).sub
      (ht.comp_continuous ((continuous_apply 0).mul (continuous_apply 1)))
  let a : (trivRep G ℤ).coch.X 2 := ⟨m, hmc.continuous⟩
  have hba : (trivRep G ℚ).coch.d 1 b = (trivMap G (Int.castAddHom ℚ)).hom.f 2 a := by
    apply Subtype.ext
    funext g
    show Gal.dn (trivRep G ℚ).rho 1 b.1 g = ((m (fun i => g i) : ℤ) : ℚ)
    rw [LowDeg.dn_one_apply]
    show t (g 1) - t (g 0 * g 1) + t (g 0) = _
    rw [hm]; ring
  have ha : (trivRep G ℤ).coch.d 2 a = 0 := by
    apply hs.inj 3
    rw [map_zero, (trivMap G (Int.castAddHom ℚ)).hom.comm, ← hba, (trivRep G ℚ).coch.dd]
  have hc : (trivRep G QZ).coch.d 1 ((trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom.f 1 b) = 0 := by
    rw [← (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom.comm, hba]
    exact (hs.exact 2 _).2 ⟨a, rfl⟩
  exact ⟨_, hc, a, ha, fun g => rfl, rfl, hδ 1 b a hc ha hba⟩

theorem exists_cocycle_form [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (c : (trivRep G ℤ).H 2) :
    ∃ (t : G → ℚ) (m : (Fin 2 → G) → ℤ) (y : (trivRep G ℤ).coch.X 2) (hy : (trivRep G ℤ).coch.d 2 y = 0),
      IsLocallyConstant t ∧ (∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) ∧ y.1 = m ∧
      c = (trivRep G ℤ).coch.cls 2 y hy := by
  have s := admissibility_holds ℤ G _ _ _ _ _ (admissible_int_rat_sequence G)
  obtain ⟨⟨δ, h1, -⟩, -⟩ := lES_holds ℤ _ _ _ _ _ s
  obtain ⟨c', rfl⟩ := (conn_int_rat_bijective G δ h1 1 one_pos).2 c
  obtain ⟨x, hx, rfl⟩ := Cx.exists_cls c'
  let sec : QZ → ℚ := Function.surjInv (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range)
  have hsec : ∀ q : QZ, (QuotientAddGroup.mk (sec q) : QZ) = q :=
    Function.surjInv_eq (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range)
  let t : G → ℚ := fun g => sec (x.1 ![g])
  have hx1 : Continuous x.1 := x.2
  have ht : IsLocallyConstant t := by
    have h0 : IsLocallyConstant fun g : G => x.1 ![g] :=
      (IsLocallyConstant.iff_continuous _).2 (hx1.comp (continuous_pi fun i => by fin_cases i; exact continuous_id))
    exact h0.comp sec
  obtain ⟨χ, hχ⟩ : ∃ χ : G → QZ, ∀ g, χ g = x.1 ![g] := ⟨fun g => x.1 ![g], fun _ => rfl⟩
  have ht' : ∀ g, (QuotientAddGroup.mk (t g) : QZ) = χ g := fun g => (hsec _).trans (hχ g).symm
  have hcoc : ∀ g : Fin 2 → G, χ (g 1) - χ (g 0 * g 1) + χ (g 0) = 0 := by
    intro g
    have h0 := congrFun (LowDeg.dn_eq_zero _ hx) g
    rw [LowDeg.dn_one_apply] at h0
    rw [hχ, hχ, hχ]
    exact h0
  have hex : ∀ g : Fin 2 → G, ∃ k : ℤ, (k : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := by
    intro g
    have h0 : (QuotientAddGroup.mk (t (g 0) + t (g 1) - t (g 0 * g 1)) : QZ) = 0 := by
      rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add, ht', ht', ht', ← hcoc g]
      abel
    exact (QuotientAddGroup.eq_zero_iff _).1 h0
  choose m hm using hex
  obtain ⟨x', hx', y, hy, e1, e2, e3⟩ := conn_cls_of_lift δ h1 t ht m hm
  have hxx : x' = x := by
    apply Subtype.ext
    funext g
    exact (e1 g).trans ((ht' (g 0)).trans ((hχ (g 0)).trans (congrArg x.1 (by funext i; fin_cases i; rfl))))
  subst hxx
  exact ⟨t, m, y, hy, ht, hm, e2, e3⟩

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
