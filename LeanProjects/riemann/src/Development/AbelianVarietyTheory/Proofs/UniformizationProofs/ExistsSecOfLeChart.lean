import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistGen

open LBGerm TopologicalSpace

variable {X : Scheme.{0}} {M H : LB X}

theorem gm_tw_g (M H : LB X) (t : ℕ) (y : X) (p q : M.ι × H.ι) (hp : y ∈ M.U p.1 ⊓ H.U p.2)
    (hq : y ∈ M.U q.1 ⊓ H.U q.2) :
    (gm (𝟙 X) y ((tw M H t).U p ⊓ (tw M H t).U q) ((tw M H t).g p q)).val =
      (gm (𝟙 X) y (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1)).val *
        (gm (𝟙 X) y (H.U p.2 ⊓ H.U q.2) (H.g p.2 q.2)).val ^ t := by
  have hy : (𝟙 X : X ⟶ X) y ∈ M.U p.1 ⊓ H.U p.2 ⊓ (M.U q.1 ⊓ H.U q.2) := ⟨hp, hq⟩
  rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, tw_g]
  refine congrArg Units.val ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 X) y _ hy _) ?_))
  rw [zpow_natCast]
  exact (map_pow _ _ _).trans (congrArg (· ^ t) (gm_res (𝟙 X) y _ hy _))

theorem exists_mul_pow (a e : ℕ) (u : LB.Sec (tw M H a)) (s : LB.Sec H) :
    ∃ u' : LB.Sec (tw M H ((a + e : ℕ) : ℤ)), nonzeroLocus u ⊓ nonzeroLocus s ≤ nonzeroLocus u' := by
  let F : ∀ p : M.ι × H.ι, Γ(X, M.U p.1 ⊓ H.U p.2) := fun p =>
    (show Γ(X, M.U p.1 ⊓ H.U p.2) from u.f p) * resG X inf_le_right (s.f p.2) ^ e
  have hF : ∀ (y : X) (p : M.ι × H.ι), y ∈ M.U p.1 ⊓ H.U p.2 → gs (𝟙 X) y _ (F p) =
      gs (𝟙 X) y _ (u.f p) * gs (𝟙 X) y _ (s.f p.2) ^ e := fun y p hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy]
    rfl
  refine ⟨secOfGerm (M := tw M H ((a + e : ℕ) : ℤ)) F fun y p q hp hq => ?_, fun y hy => ?_⟩
  · refine (hF y p hp).trans (Eq.trans ?_ (congrArg₂ (· * ·) (gm_tw_g M H (a + e) y p q hp hq) (hF y q hq)).symm)
    rw [gs_compat u (𝟙 X) y (j := p) (j' := q) hp hq, gm_tw_g M H a y p q hp hq,
      gs_compat s (𝟙 X) y (j := p.2) (j' := q.2) hp.2 hq.2]
    ring
  · obtain ⟨p, hp⟩ := exists_chart_of_mem_nonzeroLocus hy.1
    refine (mem_nonzeroLocus_iff_isUnit (M := tw M H ((a + e : ℕ) : ℤ)) _ (k := p) hp).2 ?_
    refine (congrArg IsUnit (hF y p hp)).mpr ?_
    exact (((mem_nonzeroLocus_iff_isUnit u hp).1 hy.1).mul
      (((mem_nonzeroLocus_iff_isUnit s hp.2).1 hy.2).pow e))

theorem exists_sec_of_le_chart [CompactSpace X] [QuasiSeparatedSpace X] (hM : M.IsLB) (hH : H.IsLB) (n : ℕ)
    (σ : ∀ j, Γ(X, H.U j))
    (hσ : ∀ (y : X) j j', y ∈ H.U j → y ∈ H.U j' → gs (𝟙 X) y _ (σ j) =
      (gm (𝟙 X) y (H.U j ⊓ H.U j') (H.g j j')).val ^ n * gs (𝟙 X) y _ (σ j'))
    (V : X.Opens) (hV : ∀ (y : X) j, y ∈ H.U j → (y ∈ V ↔ IsUnit (gs (𝟙 X) y _ (σ j))))
    (k : M.ι) (hk : V ≤ M.U k) :
    ∃ (N : ℕ) (u : LB.Sec (tw M H ((n * N : ℕ) : ℤ))), V ≤ nonzeroLocus u := by
  obtain ⟨α, _, W, J, hWa, hW, hc⟩ : ∃ (α : Type) (_ : Fintype α) (W : α → X.Opens) (J : α → M.ι × H.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (J a).1 ⊓ H.U (J a).2) ∧ ∀ y : X, ∃ a, y ∈ W a :=
    exists_finite_affine_refinement (isLB_tw hM hH 0)
  have hW₂ : ∀ a, W a ≤ H.U (J a).2 := fun a => (hW a).trans inf_le_right
  have hb : ∀ (U : X.Opens) (j : H.ι) (hU : U ≤ H.U j) (y : X),
      y ∈ X.basicOpen (resG X hU (σ j)) → y ∈ V := fun U j hU y hy => by
    have hy₁ : y ∈ U := X.basicOpen_le _ hy
    have hs := (isUnit_gs_iff (𝟙 X) y _ hy₁ _).2 hy
    rwa [gs_res _ y _ hy₁, ← hV y j (hU hy₁)] at hs
  have step₁ : ∀ a, ∃ (e : ℕ) (v : Γ(X, W a)), ∀ y ∈ W a, y ∈ V →
      gs (𝟙 X) y _ v = gs (𝟙 X) y _ (σ (J a).2) ^ e *
        (gm (𝟙 X) y (M.U (J a).1 ⊓ M.U k) (M.g (J a).1 k)).val := fun a => by
    have le : X.basicOpen (resG X (hW₂ a) (σ (J a).2)) ≤ M.U (J a).1 ⊓ M.U k :=
      fun y hy => ⟨(hW a (X.basicOpen_le _ hy)).1, hk (hb _ _ _ y hy)⟩
    obtain ⟨e, v, hv⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X (W a) (hWa a).isCompact
      (hWa a).isQuasiSeparated (resG X (hW₂ a) (σ (J a).2)) (resG X le (M.g (J a).1 k).val)
    have hv' : resG X (X.basicOpen_le _) v =
        resG X (X.basicOpen_le _) (resG X (hW₂ a) (σ (J a).2)) ^ e * resG X le (M.g (J a).1 k).val := hv
    refine ⟨e, v, fun y hy hs => ?_⟩
    have hy' : y ∈ X.basicOpen (resG X (hW₂ a) (σ (J a).2)) := (isUnit_gs_iff (𝟙 X) y _ hy _).1 (by
      rw [gs_res _ y _ hy]; exact (hV y _ (hW₂ a hy)).1 hs)
    have e₁ := congrArg (gs (𝟙 X) y _) hv'
    rwa [gs_res _ y _ hy', gs_mul _ y _ hy', gs_pow _ y _ hy', gs_res _ y _ hy', gs_res _ y _ hy,
      gs_res _ y _ hy', gs_unit (𝟙 X) y _ (le hy')] at e₁
  choose e v hv using step₁
  obtain ⟨N₁, v', hv'⟩ : ∃ (N₁ : ℕ) (v' : ∀ a, Γ(X, W a)), ∀ a, ∀ y ∈ W a, y ∈ V →
      gs (𝟙 X) y _ (v' a) = gs (𝟙 X) y _ (σ (J a).2) ^ N₁ *
        (gm (𝟙 X) y (M.U (J a).1 ⊓ M.U k) (M.g (J a).1 k)).val :=
    ⟨Finset.univ.sup e, fun a => resG X (hW₂ a) (σ (J a).2) ^ (Finset.univ.sup e - e a) * v a, fun a y hy hs => by
      rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, hv a y hy hs, ← _root_.mul_assoc, ← pow_add,
        Nat.sub_add_cancel (Finset.le_sup (f := e) (Finset.mem_univ a))]⟩
  have step₂ : ∀ p : α × α, ∃ d : ℕ, ∀ y ∈ W p.1 ⊓ W p.2, gs (𝟙 X) y _ (σ (J p.1).2) ^ d *
      (gs (𝟙 X) y _ (v' p.1) - (gm (𝟙 X) y (M.U (J p.1).1 ⊓ M.U (J p.2).1) (M.g (J p.1).1 (J p.2).1)).val *
        (gm (𝟙 X) y (H.U (J p.1).2 ⊓ H.U (J p.2).2)
        (H.g (J p.1).2 (J p.2).2)).val ^ (n * N₁) * gs (𝟙 X) y _ (v' p.2)) = 0 := by
    rintro ⟨a, b⟩
    have hcpt : IsCompact ((W a ⊓ W b : X.Opens) : Set X) :=
      QuasiSeparatedSpace.inter_isCompact _ _ (W a).isOpen (hWa a).isCompact (W b).isOpen (hWa b).isCompact
    have le₁ : W a ⊓ W b ≤ M.U (J a).1 ⊓ M.U (J b).1 := fun y hy => ⟨(hW a hy.1).1, (hW b hy.2).1⟩
    have le : W a ⊓ W b ≤ H.U (J a).2 ⊓ H.U (J b).2 := fun y hy => ⟨(hW a hy.1).2, (hW b hy.2).2⟩
    have hx : ∀ y ∈ W a ⊓ W b, gs (𝟙 X) y (W a ⊓ W b) (resG X inf_le_left (v' a) -
        resG X le₁ (M.g (J a).1 (J b).1).val * resG X le (H.g (J a).2 (J b).2).val ^ (n * N₁) *
          resG X inf_le_right (v' b)) =
        gs (𝟙 X) y _ (v' a) - (gm (𝟙 X) y (M.U (J a).1 ⊓ M.U (J b).1) (M.g (J a).1 (J b).1)).val *
          (gm (𝟙 X) y (H.U (J a).2 ⊓ H.U (J b).2) (H.g (J a).2 (J b).2)).val ^ (n * N₁) *
            gs (𝟙 X) y _ (v' b) := fun y hy => by
      rw [gs_sub _ y _ hy, gs_mul _ y _ hy, gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy,
        gs_res _ y _ hy, gs_res _ y _ hy, gs_unit (𝟙 X) y _ (le hy), gs_unit (𝟙 X) y _ (le₁ hy)]
    obtain ⟨d, hd⟩ := exists_pow_mul_gs_eq_zero hcpt (resG X (inf_le_left.trans (hW₂ a)) (σ (J a).2)) _
      fun y hy => by
        have hy₁ : y ∈ W a ⊓ W b := X.basicOpen_le _ hy
        have hs := hb _ _ _ y hy
        refine (hx y hy₁).trans ?_
        rw [hv' a y hy₁.1 hs, hv' b y hy₁.2 hs, hσ y (J a).2 (J b).2 (hW₂ a hy₁.1) (hW₂ b hy₁.2),
          ← gm_cocycle hM (𝟙 X) y (hW a hy₁.1).1 (hW b hy₁.2).1 (hk hs), Units.val_mul]
        ring
    refine ⟨d, fun y hy => ?_⟩
    have := hd y hy
    rwa [hx y hy, gs_res _ y _ hy] at this
  choose d hd using step₂
  obtain ⟨c, hc'⟩ : ∃ c, ∀ p, d p ≤ c := ⟨Finset.univ.sup d, fun p => Finset.le_sup (Finset.mem_univ p)⟩
  have hz : ∀ a, ∀ y ∈ W a, gs (𝟙 X) y _ (resG X (hW₂ a) (σ (J a).2) ^ c * v' a) =
      gs (𝟙 X) y _ (σ (J a).2) ^ c * gs (𝟙 X) y _ (v' a) := fun a y hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy]
  obtain ⟨u, hu⟩ := exists_sec_of_refinement (isLB_tw hM hH ((n * (N₁ + c) : ℕ) : ℤ)) W J hW hc
    (fun a => resG X (hW₂ a) (σ (J a).2) ^ c * v' a) fun y a b ha hb => by
      obtain ⟨c', hc''⟩ := Nat.exists_eq_add_of_le (hc' (a, b))
      have e₁ := hd (a, b) y ⟨ha, hb⟩
      have e₂ := hσ y (J a).2 (J b).2 (hW₂ a ha) (hW₂ b hb)
      rw [hz a y ha, hz b y hb, gm_tw_g M H _ y (J a) (J b) (hW a ha) (hW b hb)]
      dsimp only at e₁
      rw [e₂] at e₁ ⊢
      rw [hc'']
      generalize gs (𝟙 X) y _ (σ (J b).2) = τ at e₁ ⊢
      generalize Units.val (gm (𝟙 X) y _ (H.g (J a).2 (J b).2)) = w at e₁ ⊢
      linear_combination (w ^ n * τ) ^ c' * e₁
  refine ⟨N₁ + c, u, fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := hc y
  have hs := (hV y _ (hW₂ a ha)).1 hy
  rw [mem_nonzeroLocus_iff_isUnit u (k := J a) (hW a ha), hu y (J a) a (hW a ha) ha, hz a y ha, hv' a y ha hy]
  exact (Units.isUnit _).mul ((hs.pow c).mul ((hs.pow N₁).mul (Units.isUnit _)))

theorem compact_quasiSeparated (hH : H.IsLB) {I : Type} [Finite I] (s : I → LB.Sec H)
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i))) :
    CompactSpace X ∧ QuasiSeparatedSpace X := by
  have mem : ∀ y : X, ∃ i, y ∈ nonzeroLocus (s i) := fun y =>
    Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hc]; trivial)
  refine ⟨⟨?_⟩, quasiSeparatedSpace_iff_forall_affineOpens.2 fun U V => ?_⟩
  · have : (Set.univ : Set X) = ⋃ i, (nonzeroLocus (s i) : Set X) :=
      (Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 (mem y)).symm
    rw [this]
    exact isCompact_iUnion fun i => (ha i).isCompact
  · have : (U.1 ∩ V.1 : Set X) = ⋃ i, ((nonzeroLocus (s i) ⊓ U.1 : X.Opens) : Set X) ∩
        ((nonzeroLocus (s i) ⊓ V.1 : X.Opens) : Set X) := by
      ext y
      refine ⟨fun hy => ?_, fun hy => ?_⟩
      · obtain ⟨i, hi⟩ := mem y
        exact Set.mem_iUnion.2 ⟨i, ⟨hi, hy.1⟩, ⟨hi, hy.2⟩⟩
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
        exact ⟨hi.1.2, hi.2.2⟩
    rw [this]
    exact isCompact_iUnion fun i => (ha i).isQuasiSeparated _ _ Set.inter_subset_left (Opens.isOpen _)
      (isAffineOpen_nonzeroLocus_inf hH (s i) U.2).isCompact Set.inter_subset_left (Opens.isOpen _)
      (isAffineOpen_nonzeroLocus_inf hH (s i) V.2).isCompact

theorem exists_nhds [CompactSpace X] [QuasiSeparatedSpace X] (hM : M.IsLB) (hH : H.IsLB) (s : LB.Sec H)
    (ha : IsAffineOpen (nonzeroLocus s)) (y : X) (hy : y ∈ nonzeroLocus s) :
    ∃ (V : X.Opens) (N : ℕ), y ∈ V ∧ ∀ e : ℕ, ∃ u : LB.Sec (tw M H ((N + e : ℕ) : ℤ)), V ≤ nonzeroLocus u := by
  obtain ⟨k, hk⟩ := exists_chart hM y
  have hl := nonzeroLocus_secToPow s (le_refl 1)
  rw [← hl] at ha hy
  obtain ⟨a, hle, hya⟩ := ha.exists_basicOpen_le (V := M.U k) ⟨y, hk⟩ hy
  obtain ⟨m, -, σ, hσ⟩ := exists_nonzeroLocus_eq_basicOpen hH (secToPow s 1) a
  obtain ⟨N, u, hu⟩ := exists_sec_of_le_chart hM hH (1 * m) (powSecFn σ) (fun z j j' hj hj' => by
      have hz : z ∈ H.U j ⊓ H.U j' := ⟨hj, hj'⟩
      have e := congrArg (gs (𝟙 X) z _) (powSecFn_compat σ j j')
      rwa [gs_res _ z _ hz, gs_mul _ z _ hz, gs_res _ z _ hz, gs_pow _ z _ hz, gs_unit _ z _ hz] at e)
    (X.basicOpen a) (fun z j hj => by
      rw [isUnit_gs_iff (𝟙 X) z _ hj, ← nonzeroLocus_inf_powSecFn, hσ]
      exact ⟨fun h => ⟨h, hj⟩, fun h => h.1⟩) k hle
  refine ⟨X.basicOpen a, 1 * m * N, hya, fun e => ?_⟩
  obtain ⟨u', hu'⟩ := exists_mul_pow _ e u s
  exact ⟨u', (le_inf hu ((X.basicOpen_le a).trans hl.le)).trans hu'⟩

theorem twist_generated : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ M : LB X, M.IsLB → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∃ (n' : ℕ) (u : Fin (n' + 1) → LB.Sec (tw M H t)), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  intro R _ X f H n s hH hs M hM
  obtain ⟨_, _⟩ := compact_quasiSeparated hH s hs.1 fun i => (hs.2 i).1
  have loc : ∀ y : X, ∃ (V : X.Opens) (N : ℕ), y ∈ V ∧
      ∀ e : ℕ, ∃ u : LB.Sec (tw M H ((N + e : ℕ) : ℤ)), V ≤ nonzeroLocus u := fun y => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
    exact exists_nhds hM hH (s i) (hs.2 i).1 y hi
  choose V N hy hV using loc
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y => (V y : Set X)) (fun y => (V y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩)
  refine ⟨(T.sup N : ℕ), fun t ht => ?_⟩
  have h : ∀ y : T, ∃ u : LB.Sec (tw M H t), V y ≤ nonzeroLocus u := fun y => by
    have h₁ : N y ≤ T.sup N := Finset.le_sup y.2
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, t = ((N y + e : ℕ) : ℤ) := ⟨(t - N y).toNat, by omega⟩
    exact hV y e
  choose u hu using h
  let c : Option T → LB.Sec (tw M H t) := fun o => o.elim DVR.SecOps.secZero u
  let e : Option T ≃ Fin (Fintype.card T + 1) := Fintype.equivFinOfCardEq Fintype.card_option
  refine ⟨_, fun i => c (e.symm i), top_unique fun x _ => ?_⟩
  obtain ⟨y, hyT, hx⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ x))
  refine Opens.mem_iSup.2 ⟨e (some ⟨y, hyT⟩), ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hu ⟨y, hyT⟩ hx

end GlobalTheory.TwistGen
