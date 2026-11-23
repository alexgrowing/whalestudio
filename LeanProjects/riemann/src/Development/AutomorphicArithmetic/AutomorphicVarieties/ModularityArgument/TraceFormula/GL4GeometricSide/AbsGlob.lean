import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open scoped InnerProductSpace

noncomputable section

namespace UpperTheory.V.Z.GSp4Splitting.AbsoluteGlobal

section Pure

variable {ι : Type} {U : Type} [AddCommGroup U] [Module ℂ U]

private theorem capp {a b : Module.End ℂ U} (h : Commute a b) (x : U) : a (b x) = b (a x) :=
  LinearMap.congr_fun h.eq x

private def fixS (e : ι → Module.End ℂ U) (s : Finset ι) : Submodule ℂ U where
  carrier := {x | ∀ i ∈ s, e i x = x}
  add_mem' {x y} hx hy i hi := by rw [map_add, hx i hi, hy i hi]
  zero_mem' i _ := map_zero _
  smul_mem' c x hx i hi := by rw [map_smul, hx i hi]

private theorem mem_fixS {e : ι → Module.End ℂ U} {s : Finset ι} {x : U} : x ∈ fixS e s ↔ ∀ i ∈ s, e i x = x := Iff.rfl

private theorem compress [Nontrivial U] (A : ι → Subalgebra ℂ (Module.End ℂ U)) (e : ι → Module.End ℂ U)
    (Rs : Set (Module.End ℂ U)) (hee : ∀ i x, e i (e i x) = e i x) (hc : ∀ i j, Commute (e i) (e j))
    (heA : ∀ i j, i ≠ j → ∀ a ∈ A j, Commute (e i) a) (heR : ∀ i, ∀ r ∈ Rs, Commute (e i) r)
    (hAA : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) (hAR : ∀ i, ∀ a ∈ A i, ∀ r ∈ Rs, Commute a r)
    (hs : ∀ W : Submodule ℂ U, (∀ i, ∀ a ∈ A i, ∀ x ∈ W, a x ∈ W) → (∀ r ∈ Rs, ∀ x ∈ W, r x ∈ W) → W = ⊥ ∨ W = ⊤)
    (he0 : ∀ i, ∃ x, e i x ≠ 0) (s : Finset ι) :
    (∃ y ∈ fixS e s, y ≠ 0) ∧ ∀ W ≤ fixS e s, (∀ r ∈ Rs, ∀ x ∈ W, r x ∈ W) →
      (∀ i ∈ s, ∀ a ∈ A i, ∀ x ∈ W, e i (a x) ∈ W) → (∀ i ∉ s, ∀ a ∈ A i, ∀ x ∈ W, a x ∈ W) →
      W = ⊥ ∨ W = fixS e s := by
  classical
  have hK : ∀ i (y : U), y ≠ 0 → ∃ a ∈ A i, e i (a y) ≠ 0 := by
    intro i y hy
    let K : Submodule ℂ U :=
      { carrier := {z | ∀ a ∈ A i, e i (a z) = 0}
        add_mem' := fun {x z} hx hz a ha => by rw [map_add, map_add, hx a ha, hz a ha, add_zero]
        zero_mem' := fun a _ => by rw [map_zero, map_zero]
        smul_mem' := fun c x hx a ha => by rw [map_smul, map_smul, hx a ha, smul_zero] }
    have hKs := hs K (fun j b hb x hx a ha => by
        by_cases hij : i = j
        · subst hij
          exact hx (a * b) (mul_mem ha hb)
        · rw [capp (hAA i j hij a ha b hb), capp (heA i j hij b hb), hx a ha, map_zero])
      (fun r hr x hx a ha => by rw [capp (hAR i a ha r hr), capp (heR i r hr), hx a ha, map_zero])
    by_contra hcon
    push Not at hcon
    rcases hKs with h | h
    · have : y ∈ K := hcon
      rw [h] at this
      exact hy this
    · obtain ⟨x, hx⟩ := he0 i
      have : x ∈ K := h ▸ Submodule.mem_top
      exact hx (this 1 (one_mem _))
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨y, hy⟩ := exists_ne (0 : U)
    refine ⟨⟨y, fun i hi => absurd hi (Finset.notMem_empty i), hy⟩, fun W _ hR _ hA => ?_⟩
    rcases hs W (fun i => hA i (Finset.notMem_empty i)) hR with h | h
    · exact Or.inl h
    · refine Or.inr (h.trans (Submodule.eq_top_iff'.2 fun x i hi => absurd hi (Finset.notMem_empty i)).symm)
  | insert i s hi ih =>
    obtain ⟨⟨y, hy, hy0⟩, ih⟩ := ih
    have hne : ∀ j ∈ s, j ≠ i := fun j hj h => hi (h ▸ hj)
    refine ⟨?_, fun W hW hR h1 h2 => ?_⟩
    · obtain ⟨a, ha, h0⟩ := hK i y hy0
      refine ⟨_, fun j hj => ?_, h0⟩
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact hee _ _
      · rw [capp (hc j i), capp (heA j i (hne j hj) a ha), hy j hj]
    · let M : Submodule ℂ U := Submodule.span ℂ {z | ∃ a ∈ A i, ∃ w ∈ W, a w = z}
      have gen : ∀ a ∈ A i, ∀ w ∈ W, a w ∈ M := fun a ha w hw => Submodule.subset_span ⟨a, ha, w, hw, rfl⟩
      have ind : ∀ (f : Module.End ℂ U) (N : Submodule ℂ U), (∀ a ∈ A i, ∀ w ∈ W, f (a w) ∈ N) → ∀ x ∈ M, f x ∈ N := by
        intro f N h x hx
        have : M ≤ N.comap f := Submodule.span_le.2 (by
          rintro _ ⟨a, ha, w, hw, rfl⟩
          exact h a ha w hw)
        exact this hx
      have hM := ih M (fun x hx => ind 1 (fixS e s) (fun a ha w hw j hj => by
          show e j (a w) = a w
          rw [capp (heA j i (hne j hj) a ha), hW hw j (Finset.mem_insert_of_mem hj)]) x hx)
        (fun r hr => ind r M fun a ha w hw => by
          rw [← capp (hAR i a ha r hr)]
          exact gen a ha _ (hR r hr w hw))
        (fun j hj b hb => ind (e j * b) M fun a ha w hw => by
          show e j (b (a w)) ∈ M
          rw [capp (hAA j i (hne j hj) b hb a ha), capp (heA j i (hne j hj) a ha)]
          exact gen a ha _ (h1 j (Finset.mem_insert_of_mem hj) b hb w hw))
        (fun j hj b hb => ind b M fun a ha w hw => by
          by_cases hji : j = i
          · subst hji
            exact gen (b * a) (mul_mem hb ha) w hw
          · rw [capp (hAA j i hji b hb a ha)]
            exact gen a ha _ (h2 j (by simp [hji, hj]) b hb w hw))
      rcases hM with h | h
      · refine Or.inl (eq_bot_iff.2 fun w hw => ?_)
        rw [← h]
        exact gen 1 (one_mem _) w hw
      · refine Or.inr (le_antisymm hW fun z hz => ?_)
        have hzM : z ∈ M := h ▸ fun j hj => hz j (Finset.mem_insert_of_mem hj)
        rw [← hz i (Finset.mem_insert_self i s)]
        exact ind (e i) W (fun a ha w hw => h1 i (Finset.mem_insert_self i s) a ha w hw) z hzM

variable {F : Submodule ℂ U}

private theorem trOn_map (S : Submodule ℂ F) {f : Module.End ℂ U} {g : Module.End ℂ F}
    (h : ∀ x, (g x : U) = f x) : trOn (S.map F.subtype) f = trOn S g := by
  have hiff : (∀ x ∈ S.map F.subtype, f x ∈ S.map F.subtype) ↔ ∀ x ∈ S, g x ∈ S := by
    constructor
    · intro H x hx
      obtain ⟨z, hz, hzx⟩ := H x ⟨x, hx, rfl⟩
      have : z = g x := Subtype.ext (hzx.trans (h x).symm)
      exact this ▸ hz
    · rintro H _ ⟨x, hx, rfl⟩
      exact ⟨g x, H x hx, h x⟩
  unfold trOn
  by_cases H : ∀ x ∈ S, g x ∈ S
  · rw [dif_pos H, dif_pos (hiff.2 H),
      ← LinearMap.trace_conj' _ (Submodule.equivMapOfInjective F.subtype F.injective_subtype S).symm]
    congr 1
    ext x
    simp only [LinearEquiv.conj_apply, LinearEquiv.symm_symm, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have : (f.restrict (hiff.2 H)) (Submodule.equivMapOfInjective F.subtype F.injective_subtype S x) =
        Submodule.equivMapOfInjective F.subtype F.injective_subtype S (g.restrict H x) := Subtype.ext (h x).symm
    rw [this, LinearEquiv.symm_apply_apply]
  · rw [dif_neg H, dif_neg fun H' => H (hiff.1 H')]

private theorem trOn_self {f : Module.End ℂ U} {g : Module.End ℂ F}
    (h : ∀ x, (g x : U) = f x) : trOn F f = LinearMap.trace ℂ F g := by
  have H : ∀ x ∈ F, f x ∈ F := fun x hx => h ⟨x, hx⟩ ▸ (g ⟨x, hx⟩).2
  unfold trOn
  rw [dif_pos H]
  congr 1
  ext x
  exact (h x).symm

variable (F) in

private def resAlg (B : Subalgebra ℂ (Module.End ℂ U)) : Subalgebra ℂ (Module.End ℂ F) where
  carrier := {g | ∃ b ∈ B, ∀ x, (g x : U) = b x}
  mul_mem' := by
    rintro g g' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    exact ⟨b * b', mul_mem hb hb', fun x => by simp [h, h']⟩
  add_mem' := by
    rintro g g' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    exact ⟨b + b', add_mem hb hb', fun x => by simp [h, h']⟩
  algebraMap_mem' c := ⟨algebraMap ℂ _ c, Subalgebra.algebraMap_mem _ _, fun x => by simp [Module.algebraMap_end_apply]⟩

private theorem list_res {κ : Type} (a : κ → Module.End ℂ U) (g : κ → Module.End ℂ F) (h : ∀ o x, (g o x : U) = a o x)
    (l : List κ) (x : F) : ((l.map g).prod x : U) = (l.map a).prod x := by
  induction l with
  | nil => simp
  | cons o l ih => simp [h, ih]

private theorem descend (hMF : MultiFac) {κ : Type} [Fintype κ] [FiniteDimensional ℂ F] (hF : F ≠ ⊥)
    (B : κ → Subalgebra ℂ (Module.End ℂ U)) (Θ : Module.End ℂ U)
    (hB : ∀ i j, i ≠ j → ∀ a ∈ B i, ∀ b ∈ B j, Commute a b) (hΘ : Θ * Θ = 1) (hΘF : ∀ x ∈ F, Θ x ∈ F)
    (hΘB : ∀ i, ∀ a ∈ B i, Θ * a * Θ ∈ B i)
    (hs : ∀ W ≤ F, (∀ i, ∀ a ∈ B i, (∀ x ∈ F, a x ∈ F) → ∀ x ∈ W, a x ∈ W) → W = ⊥ ∨ W = F) :
    ∃ (S : κ → Submodule ℂ U) (s : ℂ), s ≠ 0 ∧
      (∀ i, S i ≤ F ∧ S i ≠ ⊥ ∧ (∀ a ∈ B i, (∀ x ∈ F, a x ∈ F) → ∀ x ∈ S i, a x ∈ S i) ∧ (∀ x ∈ S i, Θ x ∈ S i) ∧
        ∀ W ≤ S i, (∀ a ∈ B i, (∀ x ∈ F, a x ∈ F) → ∀ x ∈ W, a x ∈ W) → W = ⊥ ∨ W = S i) ∧
      ∀ a : κ → Module.End ℂ U, (∀ i, a i ∈ B i) → (∀ i, ∀ x ∈ F, a i x ∈ F) →
        trOn F (((Finset.univ : Finset κ).toList.map a).prod * Θ) = s * ∏ i, trOn (S i) (a i * Θ) := by
  haveI : Nontrivial F := Submodule.nontrivial_iff_ne_bot.2 hF
  have hinj := Submodule.map_injective_of_injective F.injective_subtype
  obtain ⟨Fi, s, hs1, hFi, htr⟩ := hMF κ F (fun i => resAlg F (B i)) (Θ.restrict hΘF)
    (by
      rintro i j hij g ⟨b, hb, h⟩ g' ⟨b', hb', h'⟩
      ext x
      simp [h, h', capp (hB i j hij b hb b' hb')])
    (by
      intro W hW
      rcases hs (W.map F.subtype) (Submodule.map_subtype_le F W) (by
        rintro i a ha haF _ ⟨x, hx, rfl⟩
        exact ⟨_, hW i (a.restrict haF) ⟨a, ha, fun _ => rfl⟩ x hx, rfl⟩) with h | h
      · exact Or.inl (hinj (h.trans (Submodule.map_bot _).symm))
      · exact Or.inr (hinj (h.trans (Submodule.map_subtype_top F).symm)))
    (by
      ext x
      exact LinearMap.congr_fun hΘ x)
    (by
      rintro i g ⟨b, hb, h⟩
      exact ⟨_, hΘB i b hb, fun x => by simp [h]⟩)
  refine ⟨fun i => (Fi i).map F.subtype, s, by rcases hs1 with rfl | rfl <;> norm_num, fun i => ?_, fun a ha haF => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hFi i
    refine ⟨Submodule.map_subtype_le F _, fun h => h1 (hinj (h.trans (Submodule.map_bot _).symm)), ?_, ?_, ?_⟩
    · rintro a ha haF _ ⟨x, hx, rfl⟩
      exact ⟨_, h2 (a.restrict haF) ⟨a, ha, fun _ => rfl⟩ x hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨_, h3 x hx, rfl⟩
    · intro W hW hst
      have hWF : W ≤ F := hW.trans (Submodule.map_subtype_le F _)
      have hmc : (W.comap F.subtype).map F.subtype = W := by
        rw [Submodule.map_comap_subtype, inf_eq_right.2 hWF]
      rcases h4 (W.comap F.subtype) (fun x hx => by
          obtain ⟨z, hz, hzx⟩ := hW hx
          exact (Subtype.ext hzx : z = x) ▸ hz)
        (by
          rintro g ⟨b, hb, h⟩ x hx
          show (g x : U) ∈ W
          rw [h]
          exact hst b hb (fun y hy => h ⟨y, hy⟩ ▸ (g ⟨y, hy⟩).2) _ hx) with h | h
      · exact Or.inl (by rw [← hmc, h, Submodule.map_bot])
      · exact Or.inr (by rw [← hmc, h])
  · have := htr (fun i => (a i).restrict (haF i)) fun i => ⟨a i, ha i, fun _ => rfl⟩
    rw [trOn_self (g := ((Finset.univ : Finset κ).toList.map fun i => (a i).restrict (haF i)).prod * Θ.restrict hΘF)
      (fun x => list_res a _ (fun _ _ => rfl) _ _), this]
    congr 1
    exact Finset.prod_congr rfl fun i _ => (trOn_map _ fun _ => rfl).symm

private theorem prod_option [Fintype ι] (a : Option ι → Module.End ℂ U) (h : ∀ i j, i ≠ j → Commute (a i) (a j)) :
    ((Finset.univ : Finset (Option ι)).toList.map a).prod =
      ((Finset.univ : Finset ι).toList.map fun i => a (some i)).prod * a none := by
  have hp : (Finset.univ : Finset (Option ι)).toList.Perm ((Finset.univ : Finset ι).toList.map some ++ [none]) := by
    refine (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) ?_).2 fun o => ?_
    · rw [List.nodup_append]
      refine ⟨(Finset.nodup_toList _).map (Option.some_injective _), List.nodup_singleton _, ?_⟩
      simp
    · cases o <;> simp
  rw [(hp.map a).prod_eq' (List.pairwise_map.2 ((Finset.nodup_toList _).imp fun hij => h _ _ hij))]
  simp [List.map_map, Function.comp_def]

end Pure

section Gen

variable {U : Type} [AddCommGroup U] [Module ℂ U]

private theorem adjoin_comm {s t : Set (Module.End ℂ U)} (h : ∀ a ∈ s, ∀ b ∈ t, Commute a b) :
    ∀ a ∈ Algebra.adjoin ℂ s, ∀ b ∈ Algebra.adjoin ℂ t, Commute a b := fun a ha b hb =>
  Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun y hy =>
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha fun x hx => (h x hx y hy).symm).symm

private theorem adjoin_stab {s : Set (Module.End ℂ U)} {N : Submodule ℂ U} (h : ∀ a ∈ s, ∀ x ∈ N, a x ∈ N) :
    ∀ a ∈ Algebra.adjoin ℂ s, ∀ x ∈ N, a x ∈ N := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem z hz => exact h z hz
  | algebraMap c => exact fun x hx => N.smul_mem c hx
  | add u v _ _ hu hv => exact fun x hx => N.add_mem (hu x hx) (hv x hx)
  | mul u v _ _ hu hv => exact fun x hx => hu _ (hv x hx)

private theorem adjoin_conj {s : Set (Module.End ℂ U)} {Θ : Module.End ℂ U} (hΘ : Θ * Θ = 1)
    (h : ∀ a ∈ s, ∃ b ∈ s, Θ * a = b * Θ) : ∀ a ∈ Algebra.adjoin ℂ s, Θ * a * Θ ∈ Algebra.adjoin ℂ s := by
  have key : ∀ a ∈ Algebra.adjoin ℂ s, ∃ b ∈ Algebra.adjoin ℂ s, Θ * a = b * Θ := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem z hz => exact (h z hz).imp fun b hb => ⟨Algebra.subset_adjoin hb.1, hb.2⟩
    | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, (Algebra.commutes c Θ).symm⟩
    | add u v _ _ hu hv =>
      obtain ⟨⟨b, hb, e⟩, b', hb', e'⟩ := And.intro hu hv
      exact ⟨b + b', add_mem hb hb', by rw [mul_add, add_mul, e, e']⟩
    | mul u v _ _ hu hv =>
      obtain ⟨⟨b, hb, e⟩, b', hb', e'⟩ := And.intro hu hv
      exact ⟨b * b', mul_mem hb hb', by rw [← mul_assoc, e, mul_assoc, e', mul_assoc]⟩
  intro a ha
  obtain ⟨b, hb, e⟩ := key a ha
  rwa [e, mul_assoc, hΘ, mul_one]

private def orb (A : Subalgebra ℂ (Module.End ℂ U)) (x : U) : Submodule ℂ U :=
  (Subalgebra.toSubmodule A).map (LinearMap.applyₗ x)

private theorem mem_orb {A : Subalgebra ℂ (Module.End ℂ U)} {x y : U} : y ∈ orb A x ↔ ∃ a ∈ A, a x = y := Iff.rfl

private theorem list_fix {ι : Type} (P : ι → Module.End ℂ U) (e : Module.End ℂ U) (h : ∀ j, Commute e (P j)) (i : ι)
    (hi : ∀ x, e (P i x) = P i x) (l : List ι) (hl : i ∈ l) (x : U) : e ((l.map P).prod x) = (l.map P).prod x := by
  induction l with
  | nil => simp at hl
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rcases List.mem_cons.1 hl with rfl | hl
    · exact hi _
    · rw [capp (h j), ih hl]

end Gen

section Adj

variable {n : ℕ} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

private theorem pair_adj {E1 E2 : Fin n → Fin n → Module.End ℂ U} (h : IsPair E1 E2) (a b : Fin n) :
    (∀ x y : U, ⟪E1 a b x, y⟫_ℂ = ⟪x, E2 b a y⟫_ℂ) ∧ ∀ x y : U, ⟪E2 a b x, y⟫_ℂ = ⟪x, E1 b a y⟫_ℂ := by
  have hK : ∀ x y : U, ⟪E1 a b x, y⟫_ℂ + ⟪E2 a b x, y⟫_ℂ = ⟪x, E1 b a y⟫_ℂ + ⟪x, E2 b a y⟫_ℂ := fun x y => by
    simpa [kF, inner_add_left, inner_add_right] using h.unitK a b x y
  have hP : ∀ x y : U, ⟪E1 a b x, y⟫_ℂ - ⟪E2 a b x, y⟫_ℂ = -(⟪x, E1 b a y⟫_ℂ - ⟪x, E2 b a y⟫_ℂ) := fun x y => by
    simpa only [pF, LinearMap.sub_apply, inner_sub_left, inner_sub_right] using h.unitP a b x y
  exact ⟨fun x y => by linear_combination (hK x y + hP x y) / 2, fun x y => by linear_combination (hK x y - hP x y) / 2⟩

private theorem iso_adj {f g : Module.End ℂ U} (h : ∀ x y : U, ⟪f x, f y⟫_ℂ = ⟪x, y⟫_ℂ) (hfg : f * g = 1) (x y : U) :
    ⟪f x, y⟫_ℂ = ⟪x, g y⟫_ℂ := by
  rw [← h x (g y), ← Module.End.mul_apply, hfg, Module.End.one_apply]

end Adj

end UpperTheory.V.Z.GSp4Splitting.AbsoluteGlobal

open UpperTheory.V.Z.GSp4Splitting.AbsoluteGlobal in
theorem UpperTheory.V.Z.GSp4Splitting.absGlob :
    MultiFac → LieStab → ProjEx → AvgFacts → OnePlace → AbsGlob := by
  intro hMF hLS hPE hAF hOP n ι _ lam hlam E T hT _ _ ν _ hν U _ _ E1 E2 σ Θ P J R hloc havg hEE hσσ hRc hRa hRΘ hΘ
    hsimp hnt hfd hne
  classical
  choose e he using fun i => hPE n U (σ i) (hloc i).isK (E i)
  have hP := fun i => hAF n ν U (σ i) (hloc i).isK (E i) (T i) (P i) (hT i).1 (havg i)
  have hce : ∀ i {x}, AdjComm (σ i) x → Commute (e i) x := fun i x hx => (he i).2.2.2.2.1 x hx
  have hcP : ∀ i {x}, AdjComm (σ i) x → Commute (P i) x := fun i x hx => (hP i).2.2.1 x hx
  have hiso : ∀ i x, x ∈ isoSp (σ i) (E i) ↔ e i x = x :=
    fun i x => ⟨(he i).2.2.1 x, fun h => h ▸ (he i).2.1 x⟩

  let G : ι → Set (Module.End ℂ U) := fun i => {x | ∃ a b, x = E1 i a b ∨ x = E2 i a b}
  let Gs : Option ι → Set (Module.End ℂ U) := fun o => o.elim (Set.range R) fun i => G i ∪ {e i, P i}
  have aσ : ∀ i j, i ≠ j → ∀ k, AdjComm (σ i) (σ j k) := fun i j hij k =>
    ⟨σ j k⁻¹, iso_adj ((hloc j).isK.iso k) (by rw [← map_mul, mul_inv_cancel, map_one]),
      fun k' => ⟨hσσ j i hij.symm _ _, hσσ j i hij.symm _ _⟩⟩
  have aΘ : ∀ i, AdjComm (σ i) Θ := fun i =>
    ⟨Θ, iso_adj (hloc i).Aiso hΘ, fun k => ⟨(hloc i).Aσ k, (hloc i).Aσ k⟩⟩
  have aG : ∀ i j, i ≠ j → ∀ x ∈ G j, AdjComm (σ i) x := by
    rintro i j hij _ ⟨a, b, rfl | rfl⟩
    · exact ⟨_, (pair_adj (hloc j).pair a b).1,
        fun k => ⟨((hEE j i hij.symm a b).2 k).1, ((hEE j i hij.symm b a).2 k).2⟩⟩
    · exact ⟨_, (pair_adj (hloc j).pair a b).2,
        fun k => ⟨((hEE j i hij.symm a b).2 k).2, ((hEE j i hij.symm b a).2 k).1⟩⟩
  have aR : ∀ i j, AdjComm (σ i) (R j) := fun i j =>
    (hRa j).elim fun j' h => ⟨R j', h, fun k => ⟨(hRc j i).2 k, (hRc j' i).2 k⟩⟩
  have ae : ∀ i j, AdjComm (σ i) (e j) := by
    intro i j
    have : ∀ k, e j * σ i k = σ i k * e j := by
      by_cases h : j = i
      · subst h
        exact (he j).2.2.2.1
      · exact fun k => hce j (aσ j i h k)
    exact ⟨e j, (he j).1, fun k => ⟨this k, this k⟩⟩
  have aP : ∀ i j, AdjComm (σ i) (P j) := by
    intro i j
    by_cases h : j = i
    · subst h
      exact (hP j).2.1
    · obtain ⟨P', h1, h2⟩ := (hP j).2.2.2.2
      exact ⟨P', h1, fun k => ⟨hcP j (aσ j i h k), h2 _ (aσ j i h k)⟩⟩
  have aGs : ∀ i j, i ≠ j → ∀ x ∈ Gs (some j), AdjComm (σ i) x := by
    rintro i j hij x (hx | rfl | rfl)
    exacts [aG i j hij x hx, ae i j, aP i j]
  have cGG : ∀ i j, i ≠ j → ∀ x ∈ G i, ∀ y ∈ G j, Commute x y := by
    rintro i j hij _ ⟨a, b, rfl | rfl⟩ _ ⟨c, d, rfl | rfl⟩
    exacts [((hEE i j hij a b).1 c d).1, ((hEE i j hij a b).1 c d).2.1, ((hEE j i hij.symm c d).1 a b).2.1.symm,
      ((hEE i j hij a b).1 c d).2.2]
  have cGR : ∀ i, ∀ x ∈ Gs (some i), ∀ y ∈ Set.range R, Commute x y := by
    rintro i _ (⟨a, b, rfl | rfl⟩ | rfl | rfl) _ ⟨j, rfl⟩
    exacts [((hRc j i).1 a b).1.symm, ((hRc j i).1 a b).2.symm, hce i (aR i j), hcP i (aR i j)]
  have cGs : ∀ o o', o ≠ o' → ∀ x ∈ Gs o, ∀ y ∈ Gs o', Commute x y := by
    rintro (_ | i) (_ | j) h x hx y hy
    · exact absurd rfl h
    · exact (cGR j y hy x hx).symm
    · exact cGR i x hx y hy
    · have hij : i ≠ j := fun h' => h (congrArg some h')
      rcases hx with hx | rfl | rfl
      · rcases hy with hy | rfl | rfl
        exacts [cGG i j hij x hx y hy, (hce j (aG j i hij.symm x hx)).symm, (hcP j (aG j i hij.symm x hx)).symm]
      · exact hce i (aGs i j hij y hy)
      · exact hcP i (aGs i j hij y hy)
  let B : Option ι → Subalgebra ℂ (Module.End ℂ U) := fun o => Algebra.adjoin ℂ (Gs o)
  have cB : ∀ o o', o ≠ o' → ∀ x ∈ B o, ∀ y ∈ B o', Commute x y := fun o o' h => adjoin_comm (cGs o o' h)
  have hAB : ∀ i, alg (E1 i) (E2 i) ≤ B (some i) := fun i => Algebra.adjoin_mono Set.subset_union_left
  have heB : ∀ i, e i ∈ B (some i) := fun i => Algebra.subset_adjoin (Or.inr (Or.inl rfl))
  have hPB : ∀ i, P i ∈ B (some i) := fun i => Algebra.subset_adjoin (Or.inr (Or.inr rfl))
  have hRB : ∀ j, R j ∈ B none := fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  have cij : ∀ i j, i ≠ j → ∀ x ∈ B (some i), ∀ y ∈ B (some j), Commute x y :=
    fun i j h => cB _ _ fun h' => h (Option.some.inj h')
  set F : Submodule ℂ U := ⨅ i, isoSp (σ i) (E i) with hFdef
  have hF : ∀ x, x ∈ F ↔ ∀ i, e i x = x := fun x => by simp only [hFdef, Submodule.mem_iInf, hiso]
  have hFfix : fixS e Finset.univ = F := Submodule.ext fun x => by simp [mem_fixS, hF]
  have keep : ∀ a : Module.End ℂ U, (∀ i, Commute (e i) a) → ∀ x ∈ F, a x ∈ F := fun a ha x hx =>
    (hF _).2 fun i => by rw [capp (ha i), (hF x).1 hx i]
  have hee : ∀ i x, e i (e i x) = e i x := fun i x => (hiso i _).1 ((he i).2.1 x)
  have keepE : ∀ i, ∀ a ∈ B (some i), ∀ x ∈ F, (e i * a) x ∈ F := fun i a ha x hx => (hF _).2 fun j => by
    by_cases h : j = i
    · subst h
      exact hee _ _
    · rw [capp (cij j i h _ (heB j) _ (mul_mem (heB i) ha)), (hF x).1 hx j]
  have keepR : ∀ j, ∀ x ∈ F, R j x ∈ F := fun j => keep _ fun i => hce i (aR i j)
  have keepP : ∀ j, ∀ x ∈ F, P j x ∈ F := fun j => keep _ fun i => hce i (aP i j)
  obtain ⟨⟨y, hy, hy0⟩, hFs⟩ := compress (fun i => alg (E1 i) (E2 i)) e (Set.range R) hee (fun i j => hce i (ae i j))
    (fun i j h a ha => cij i j h _ (heB i) _ (hAB j ha))
    (by rintro i _ ⟨j, rfl⟩; exact hce i (aR i j))
    (fun i j h a ha b hb => cij i j h _ (hAB i ha) _ (hAB j hb))
    (by rintro i a ha _ ⟨j, rfl⟩; exact cB _ _ (Option.some_ne_none i) _ (hAB i ha) _ (hRB j))
    (fun W h1 h2 => hsimp W (fun i a b x hx =>
      ⟨h1 i _ (Algebra.subset_adjoin ⟨a, b, Or.inl rfl⟩) x hx, h1 i _ (Algebra.subset_adjoin ⟨a, b, Or.inr rfl⟩) x hx⟩)
      fun j => h2 _ ⟨j, rfl⟩)
    (fun i => by
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne i)
      exact ⟨x, by rwa [(hiso i x).1 hx]⟩) Finset.univ
  rw [hFfix] at hy hFs
  have hΘ2 : ∀ i a b, Θ * E2 i a b = E1 i a b * Θ := fun i a b => by
    have h := (hloc i).AE a b
    calc Θ * E2 i a b = Θ * (E2 i a b * Θ) * Θ := by rw [mul_assoc, mul_assoc, hΘ, mul_one]
      _ = E1 i a b * Θ := by rw [← h, ← mul_assoc, hΘ, one_mul]
  obtain ⟨S, s, hs0, hS, htr⟩ := descend (F := F) hMF ((Submodule.ne_bot_iff _).2 ⟨y, hy, hy0⟩) B Θ cB hΘ
    (keep _ fun i => hce i (aΘ i))
    (fun o => adjoin_conj hΘ (by
      rcases o with _ | i
      · rintro _ ⟨j, rfl⟩
        obtain ⟨j', h⟩ := hRΘ j
        exact ⟨_, ⟨j', rfl⟩, h⟩
      · rintro _ (⟨a, b, rfl | rfl⟩ | rfl | rfl)
        · exact ⟨_, Or.inl ⟨a, b, Or.inr rfl⟩, (hloc i).AE a b⟩
        · exact ⟨_, Or.inl ⟨a, b, Or.inl rfl⟩, hΘ2 i a b⟩
        · exact ⟨_, Or.inr (Or.inl rfl), (hce i (aΘ i)).symm⟩
        · exact ⟨_, Or.inr (Or.inr rfl), (hcP i (aΘ i)).symm⟩))
    (fun W hW h => hFs W hW (by rintro _ ⟨j, rfl⟩; exact h none _ (hRB j) (keepR j))
      (fun i _ a ha => h (some i) (e i * a) (mul_mem (heB i) (hAB i ha)) (keepE i a (hAB i ha)))
      fun i hi => absurd (Finset.mem_univ i) hi)

  have horb : ∀ i x, ∀ a ∈ B (some i), a x ∈ orb (alg (E1 i) (E2 i)) x := by
    intro i x a ha
    have hA : ∀ c ∈ alg (E1 i) (E2 i), ∀ z ∈ orb (alg (E1 i) (E2 i)) x, c z ∈ orb (alg (E1 i) (E2 i)) x := by
      rintro c hc _ ⟨b, hb, rfl⟩
      exact mem_orb.2 ⟨c * b, mul_mem hc (show b ∈ alg (E1 i) (E2 i) from hb), rfl⟩
    have hσ := hLS n U (σ i) _ (hloc i).der (orb (alg (E1 i) (E2 i)) x) fun a b =>
      hA _ (add_mem (Algebra.subset_adjoin ⟨a, b, Or.inl rfl⟩) (Algebra.subset_adjoin ⟨a, b, Or.inr rfl⟩))
    refine adjoin_stab ?_ a ha x (mem_orb.2 ⟨1, one_mem _, rfl⟩)
    rintro c (hc | rfl | rfl)
    exacts [hA c (Algebra.subset_adjoin hc), (he i).2.2.2.2.2 _ hσ, (hP i).2.2.2.1 _ hσ]
  have hloc2 : ∀ i, trOn (S (some i)) (P i * Θ) ≠ 0 := by
    intro i
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS (some i)
    have := hOP n (lam i) (hlam i) (E i) (T i) (hT i) ν hν U (E1 i) (E2 i) (σ i) Θ (P i) (hloc i) (havg i) (S (some i))
      (Submodule.finiteDimensional_of_le h1) h2 (h1.trans (iInf_le _ i)) h4
      (fun a ha x hx hax => by
        rw [← (hiso i _).1 hax]
        exact h3 (e i * a) (mul_mem (heB i) (hAB i ha)) (keepE i a (hAB i ha)) x hx)
      (fun x hx z hz hx0 => by
        rcases h5 (S (some i) ⊓ orb (alg (E1 i) (E2 i)) x) inf_le_left (by
          rintro a ha haF _ ⟨hw, b, hb, rfl⟩
          exact ⟨h3 a ha haF _ hw, horb i x (a * b) (mul_mem ha (hAB i hb))⟩) with h | h
        · have : x ∈ S (some i) ⊓ orb (alg (E1 i) (E2 i)) x := ⟨hx, mem_orb.2 ⟨1, one_mem _, rfl⟩⟩
          rw [h] at this
          exact absurd this hx0
        · rw [← h] at hz
          exact hz.2)
    rcases this with h | h <;> rw [h] <;> simp
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS none
  refine ⟨S none, s * ∏ i, trOn (S (some i)) (P i * Θ), mul_ne_zero hs0 (Finset.prod_ne_zero_iff.2 fun i _ => hloc2 i),
    Submodule.finiteDimensional_of_le h1, h2, fun j => h3 _ (hRB j) (keepR j), h4, fun W hW h => h5 W hW fun a ha _ =>
      adjoin_stab (by rintro _ ⟨j, rfl⟩; exact h j) a ha, fun x => (hF _).2 fun i => ?_, fun j => ?_⟩
  · exact list_fix P (e i) (fun j => hce i (aP i j)) i (fun x => (hiso i _).1 ((hP i).1 x)) _ (by simp) x
  · have ha : ∀ o : Option ι, o.elim (R j) P ∈ B o := by
      rintro (_ | i)
      exacts [hRB j, hPB i]
    have := htr (fun o => o.elim (R j) P) ha (by
      rintro (_ | i)
      exacts [keepR j, keepP i])
    rw [prod_option _ fun o o' h => cB o o' h _ (ha o) _ (ha o'), Fintype.prod_option] at this
    refine this.trans ?_
    simp only [Option.elim]
    ring
