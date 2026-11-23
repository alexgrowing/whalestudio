import Formalism.LocalToGlobal.CharacterGerms.CoordinateChangeComp1IntertwinesAction

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}

variable (Y : FBChart C V O dd)

def exAt (a : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C := fun i => MvPowerSeries.subst a (e Y i)

theorem cc_exAt {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.constantCoeff (exAt Y a i) = 0 := by
  unfold exAt
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d = 0
  · subst hd
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, cc_e Y i]
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hd
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
      rw [map_finsuppProd]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
      show MvPowerSeries.constantCoeff (a s ^ d s) = 0
      rw [map_pow, ha s, zero_pow hs]
    rw [h0, smul_zero]

theorem l_add_at {u v : Fin dd → MvPowerSeries τ C} (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0)
    (hv : ∀ i, MvPowerSeries.constantCoeff (v i) = 0) (m : Fin dd) :
    MvPowerSeries.subst (addAt Y u v) (l Y m) = MvPowerSeries.subst u (l Y m) + MvPowerSeries.subst v (l Y m) := by
  have h := congrArg (MvPowerSeries.subst (P2 u v)) (l_add Y m)
  have hP := constantCoeff_pair_substitution hu hv
  rw [subst_add' hP, subst_subst (cc_F Y) hP,
    subst_subst (a := fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (fun _ => cc_X _) hP,
    subst_subst (a := fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) (fun _ => cc_X _) hP] at h
  have e0 : (fun s : Fin dd => MvPowerSeries.subst (P2 u v) (MvPowerSeries.X ((0 : Fin 2), s) : PS C 2 dd)) = u :=
    funext fun i => subst_X hP _
  have e1 : (fun s : Fin dd => MvPowerSeries.subst (P2 u v) (MvPowerSeries.X ((1 : Fin 2), s) : PS C 2 dd)) = v :=
    funext fun i => subst_X hP _
  rw [e0, e1] at h
  exact h

theorem l_exAt {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (m : Fin dd) :
    MvPowerSeries.subst (exAt Y a) (l Y m) = a m := by
  unfold exAt
  rw [← subst_subst (cc_e Y) ha, lgex, subst_X ha]

theorem e_lAt {P : Fin dd → MvPowerSeries τ C} (hP : ∀ i, MvPowerSeries.constantCoeff (P i) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun m => MvPowerSeries.subst P (l Y m)) (e Y i) = P i := by
  rw [← subst_subst (cc_l Y) hP, exlg, subst_X hP]

theorem ex_add {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    exAt Y (fun m => a m + b m) = addAt Y (exAt Y a) (exAt Y b) := by
  funext i
  have hP := cc_addAt Y (cc_exAt Y ha) (cc_exAt Y hb)
  rw [← e_lAt Y hP i]
  unfold exAt
  congr 1
  funext m
  show a m + b m = MvPowerSeries.subst (addAt Y (exAt Y a) (exAt Y b)) (l Y m)
  rw [l_add_at Y (cc_exAt Y ha) (cc_exAt Y hb), l_exAt Y ha, l_exAt Y hb]

theorem exAt_zero : exAt Y (fun _ : Fin dd => (0 : MvPowerSeries τ C)) = fun _ => 0 := by
  funext i
  ext e'
  simp only [exAt]
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => map_zero _)),
    finsum_eq_zero_of_forall_eq_zero]
  · simp
  · intro d
    by_cases hd : d = 0
    · subst hd
      simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, cc_e Y i]
    · obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hd
      have h0 : (d.prod fun s e => (0 : MvPowerSeries τ C) ^ e) = 0 :=
        Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs)
      rw [h0, map_zero, smul_zero]

theorem exAt_list : ∀ L : List (Fin dd → MvPowerSeries τ C),
    (∀ a ∈ L, ∀ i, MvPowerSeries.constantCoeff (a i) = 0) →
    exAt Y (fun m => (L.map fun a => a m).sum) = sumL Y (L.map (exAt Y))
  | [], _ => exAt_zero Y
  | a :: L, h => by
      have hL : ∀ m, MvPowerSeries.constantCoeff ((L.map fun a => a m).sum) = 0 := by
        intro m
        rw [map_list_sum, List.map_map]
        refine List.sum_eq_zero ?_
        intro x hx
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
        exact h b (List.mem_cons_of_mem _ hb) m
      show exAt Y (fun m => ((a :: L).map fun a => a m).sum) = addAt Y (exAt Y a) (sumL Y (L.map (exAt Y)))
      rw [← exAt_list L fun b hb => h b (List.mem_cons_of_mem _ hb), ← ex_add Y (h a List.mem_cons_self) hL]
      rfl

theorem sumL_subst [Finite τ] {A : τ → MvPowerSeries τ' C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0) :
    ∀ L : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ L, GoodPt V a) → ∀ i,
      MvPowerSeries.subst A (sumL Y L i) = sumL Y (L.map fun a j => MvPowerSeries.subst A (a j)) i
  | [], _, _ => subst_zero' hA
  | a :: L, h, i => by
      show MvPowerSeries.subst A (addAt Y a (sumL Y L) i) = addAt Y _ (sumL Y _) i
      rw [addAt_subst Y hA (h a List.mem_cons_self).1 (good_sumL Y L fun b hb => h b (List.mem_cons_of_mem _ hb)).1]
      congr 1
      funext j
      exact sumL_subst hA L (fun b hb => h b (List.mem_cons_of_mem _ hb)) j

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def zePart (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (s : Orb × Fin 2) (m : Fin dd) : MvPowerSeries (WVO I) C :=
  ∑ c : I s.1 s.2, (p s.1).u s.2 c m • (MvPowerSeries.X (⟨s.1, ⟨s.2, c⟩⟩ : WVO I) : MvPowerSeries (WVO I) C)

theorem cc_zePart (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (s : Orb × Fin 2) (m : Fin dd) :
    MvPowerSeries.constantCoeff (zePart Y p s m) = 0 := by
  unfold zePart
  simp

theorem toAllS_expPt (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (o : Orb) (g : Fin 2) (i : Fin dd) :
    toAllS o ((Y.raw (p o)).expPt g i) = VP.exAt Y (zePart Y p (o, g)) i := by
  unfold toAllS RawChart.expPt VP.exAt
  have h0 : ∀ m : Fin dd, MvPowerSeries.constantCoeff (∑ c : I o g, (Y.raw (p o)).u g c m •
      (MvPowerSeries.X (⟨g, c⟩ : WV (I o)) : MvPowerSeries (WV (I o)) C)) = 0 := by
    intro m
    rw [map_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  rw [VP.subst_subst h0 (fun _ => VP.cc_X _)]
  congr 1
  funext m
  rw [VP.subst_sum (fun _ => VP.cc_X _)]
  unfold zePart
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [VP.subst_smul (fun _ => VP.cc_X _), VP.subst_X (fun _ => VP.cc_X _)]
  rfl

theorem sumProj_holds (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) : SumProjSt Y p := by
  intro _ π hπ i
  have hgood : ∀ a ∈ projList π, VP.GoodPt V a := by
    intro a ha
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 ha
    exact ⟨hπ.cc s.1 s.2, hπ.int s.1 s.2⟩
  have hA := VP.cc_pull1Pt Y p
  have h1 : pull1 Y p (VP.sumL Y (projList π) i) =
      VP.sumL Y (((Finset.univ : Finset (Orb × Fin 2)).toList.map (zePart Y p)).map (VP.exAt Y)) i := by
    unfold pull1
    rw [VP.sumL_subst Y hA _ hgood]
    unfold projList
    rw [List.map_map, List.map_map]
    congr 2
    funext s j
    exact (hπ.pull s.1 s.2 j).trans (toAllS_expPt Y p s.1 s.2 j)
  rw [h1, ← VP.exAt_list Y _ (by
    intro a ha
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 ha
    exact cc_zePart Y p s)]
  unfold pull1
  rw [show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2) (pt C dd (0 : Fin 1) i) = expAll Y p i from
    VP.subst_X hA _]
  unfold expAll VP.exAt
  congr 1
  funext m
  rw [List.map_map, Finset.sum_map_toList, Fintype.sum_prod_type, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Fintype.sum_sigma]
  rfl

theorem biadd_holds (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) : BiaddSt Y p :=
  biadd_of_sum Y p (sumProj_holds Y p)

theorem value_equation_of_projectors (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V)
    (Ls : LetSys C dd) (n : ℕ) (hP : ProjPullSt Y p) (hT : ∀ o, RawChart.TCoordSt (H o).cartH)
    (h2 : CrossSt Y p) : ValEqPSt Y p H Ls n :=
  valuation_eq_pair_of_biadditive_cross Y p H Ls n hP hT (biadd_holds Y p) h2

end Formalism.L2.FormalSeriesBounds
