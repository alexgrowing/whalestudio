import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.TopRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitLogRepresentativeCompat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitOfBasicOpenTop
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

noncomputable section

namespace GlobalTheory.CompanionTheory.OmCls

open CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)
open GlobalTheory.CompanionTheory.CupRep GlobalTheory.CompanionTheory.RepLifts GlobalTheory.CompanionTheory.ConeLocal

section Abs
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

def vx {n : ℕ} (s : ComposableArrows C n) (w : ∀ T : C, Φ.A.obj T) (i : Fin (n + 1)) : Φ.A.obj (s.obj (Fin.last n)) :=
  (Φ.A.map (s.map (homOfLE (Fin.le_last i)))).hom (w (s.obj i))

theorem vx_res {p n : ℕ} (s : ComposableArrows C n) (w : ∀ T : C, Φ.A.obj T) (g : Fin (p + 1) → Fin (n + 1))
    (hg : Monotone g) (i : Fin (p + 1)) :
    (Φ.A.map (s.map (homOfLE (Fin.le_last (g (Fin.last p)))))).hom (vx (hg.functor ⋙ s) w i) = vx s w (g i) := by
  have e : (hg.functor ⋙ s).map (homOfLE (Fin.le_last i)) ≫ s.map (homOfLE (Fin.le_last (g (Fin.last p)))) =
      s.map (homOfLE (Fin.le_last (g i))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  unfold vx
  change (Φ.A.map ((hg.functor ⋙ s).map (homOfLE (Fin.le_last i))) ≫
    Φ.A.map (s.map (homOfLE (Fin.le_last (g (Fin.last p)))))).hom (w (s.obj (g i))) = _
  rw [← Φ.A.map_comp, e]
  rfl

theorem map_idem {n : ℕ} (s : ComposableArrows C n) (i : Fin (n + 1)) (h : i ⟶ i) (x : Φ.A.obj (s.obj i)) :
    (Φ.A.map (s.map h)).hom x = x := by
  rw [Subsingleton.elim h (𝟙 _), s.map_id, Φ.A.map_id]
  rfl

theorem vx_last {n : ℕ} (s : ComposableArrows C n) (w : ∀ T : C, Φ.A.obj T) :
    vx s w (Fin.last n) = w (s.obj (Fin.last n)) :=
  map_idem s _ _ _

theorem cech_d_h0_vertex_diff (w : ∀ T : C, Φ.A.obj T) (t : ComposableArrows C 1) :
    vl (CH.d (CH.modF Φ.A) 0 (h0 w)) t = vx t w (Fin.last 1) - vx t w 0 := by
  rw [cech_d_h0_eval, vx_last]
  rfl

theorem cupList_val : ∀ {a : ℕ} (u : Fin a → ∀ T : C, Φ.A.obj T) (s : ComposableArrows C a),
    vl (cupListC Φ.A fun k => CH.d (CH.modF Φ.A) 0 (h0 (u k))) s =
      ∏ k : Fin a, (vx s (u k) k.succ - vx s (u k) k.castSucc)
  | 0, _, _ => by simp; rfl
  | a + 1, u, s => by
    have ih := cupList_val (fun i : Fin a => u i.castSucc)
      ((CH.front_mono (rfl : a + 1 = a + 1)).functor ⋙ s)
    have h1 : (show Φ.A.obj (s.obj (Fin.last (a + 1))) from CH.term (CH.modF Φ.A) s
        (cupListC Φ.A fun k : Fin a => CH.d (CH.modF Φ.A) 0 (h0 (u k.castSucc)))
        (CH.front (rfl : a + 1 = a + 1)) (CH.front_mono _)) =
        ∏ k : Fin a, (vx s (u k.castSucc) k.castSucc.succ - vx s (u k.castSucc) k.castSucc.castSucc) := by
      change (Φ.A.map (s.map (homOfLE (Fin.le_last (CH.front (rfl : a + 1 = a + 1) (Fin.last a)))))).hom
        (vl (cupListC Φ.A fun k : Fin a => CH.d (CH.modF Φ.A) 0 (h0 (u k.castSucc)))
          ((CH.front_mono (rfl : a + 1 = a + 1)).functor ⋙ s)) = _
      rw [ih, map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [map_sub, vx_res, vx_res]
      rfl
    have h2 : (show Φ.A.obj (s.obj (Fin.last (a + 1))) from CH.term (CH.modF Φ.A) s
        (CH.d (CH.modF Φ.A) 0 (h0 (u (Fin.last a))))
        (CH.back (rfl : a + 1 = a + 1)) (CH.back_mono _)) =
        vx s (u (Fin.last a)) (Fin.last a).succ - vx s (u (Fin.last a)) (Fin.last a).castSucc := by
      change (Φ.A.map (s.map (homOfLE (Fin.le_last (CH.back (rfl : a + 1 = a + 1) (Fin.last 1)))))).hom
        (vl (CH.d (CH.modF Φ.A) 0 (h0 (u (Fin.last a))))
          ((CH.back_mono (rfl : a + 1 = a + 1)).functor ⋙ s)) = _
      rw [cech_d_h0_vertex_diff, map_sub, vx_res, vx_res]
      rfl
    rw [Fin.prod_univ_castSucc, ← h1, ← h2]
    rfl

def fm {a : ℕ} (u₀ : ∀ T : C, Φ.A.obj T) (u : Fin a → ∀ T : C, Φ.A.obj T) : CH.Cn (CH.modF Φ.A) a :=
  (CH.mulP Φ.A).cupC (add_zero a) (cupListC Φ.A fun k => CH.d (CH.modF Φ.A) 0 (h0 (u k))) (h0 u₀)

theorem cup_h0_eval {a : ℕ} (P : CH.Cn (CH.modF Φ.A) a) (w : ∀ T : C, Φ.A.obj T) (s : ComposableArrows C a) :
    vl ((CH.mulP Φ.A).cupC (add_zero a) P (h0 w)) s = vl P s * w (s.obj (Fin.last a)) := by
  have h1 : (show Φ.A.obj (s.obj (Fin.last a)) from CH.term (CH.modF Φ.A) s P
      (CH.front (add_zero a)) (CH.front_mono _)) = vl P s :=
    map_idem (Φ := Φ) s (Fin.last a) _ _
  have h2 : (show Φ.A.obj (s.obj (Fin.last a)) from CH.term (CH.modF Φ.A) s (h0 w)
      (CH.back (add_zero a)) (CH.back_mono _)) = w (s.obj (Fin.last a)) :=
    map_idem (Φ := Φ) s (Fin.last a) _ _
  rw [← h1, ← h2]
  rfl

theorem fm_val {a : ℕ} (u₀ : ∀ T : C, Φ.A.obj T) (u : Fin a → ∀ T : C, Φ.A.obj T) (s : ComposableArrows C a) :
    vl (fm u₀ u) s = (∏ k : Fin a, (vx s (u k) k.succ - vx s (u k) k.castSucc)) * u₀ (s.obj (Fin.last a)) := by
  unfold fm
  rw [cup_h0_eval, cupList_val]

end Abs

section Cls
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

def Nr (Fil : ℤ → IdF Φ.A) (w : ∀ T : C, Φ.A.obj T) : Prop :=
  ∀ (T T' : C) (f : T ⟶ T'), w T' - (Φ.A.map f).hom (w T) ∈ (Fil ((1 : ℕ) : ℤ)).S T'

theorem d_h0_mem_filtration_one {w : ∀ T : C, Φ.A.obj T} (hw : Nr Fil w) :
    CH.d (CH.modF Φ.A) 0 (h0 w) ∈ FC (Fil ((1 : ℕ) : ℤ)) 1 :=
  mem_FC.2 fun t => by
    rw [cech_d_h0_eval]
    exact hw _ _ _

theorem h0_mem_filtration_zero (hF : IsFil Φ Fil) (w : ∀ T : C, Φ.A.obj T) : h0 w ∈ FC (Fil ((0 : ℕ) : ℤ)) 0 :=
  mem_FC.2 fun t => by
    have e : (Fil ((0 : ℕ) : ℤ)).S (t.obj (Fin.last 0)) = ⊤ := hF.top _ (by simp) _
    rw [e]
    trivial

theorem fm_mem (hF : IsFil Φ Fil) {a : ℕ} (u₀ : ∀ T : C, Φ.A.obj T) {u : Fin a → ∀ T : C, Φ.A.obj T}
    (hu : ∀ k, Nr Fil (u k)) : fm u₀ u ∈ FC (Fil (a : ℤ)) a :=
  cup_mem hF (add_zero a) (r := a) (r' := 0) (cupList_mem hF _ fun k => d_h0_mem_filtration_one (hu k)) (h0_mem_filtration_zero hF u₀)

theorem d_fm_mem (hF : IsFil Φ Fil) {a : ℕ} {u₀ : ∀ T : C, Φ.A.obj T} {u : Fin a → ∀ T : C, Φ.A.obj T}
    (h₀ : Nr Fil u₀) (hu : ∀ k, Nr Fil (u k)) :
    CH.d (CH.modF Φ.A) a (fm u₀ u) ∈ FC (Fil ((a + 1 : ℕ) : ℤ)) (a + 1) := by
  unfold fm
  rw [CrystallineSemistableComparison.P.leibniz, d_cupList Φ.A _ fun k => CH.d_d _ 0 _]
  simp only [map_zero, LinearMap.zero_apply, zero_add]
  exact zsmul_mem (cup_mem hF _ (r := a) (r' := 1) (cupList_mem hF _ fun k => d_h0_mem_filtration_one (hu k)) (d_h0_mem_filtration_one h₀)) _

theorem cup_h0_normal_coboundary (hF : IsFil Φ Fil) {m : ℕ} {g : CH.Cn (CH.modF Φ.A) m} (hg : IsBd Fil m g)
    {y : ∀ T : C, Φ.A.obj T} (hy : Nr Fil y) :
    ∃ W ∈ FC (Fil ((m + 1 : ℕ) : ℤ)) m, IsBd Fil m ((CH.mulP Φ.A).cupC (add_zero m) g (h0 y) - W) := by
  cases m with
  | zero =>
    have hg0 : g = 0 := hg
    subst hg0
    refine ⟨0, zero_mem _, ?_⟩
    change _ = _
    simp
  | succ n =>
    obtain ⟨H, hH, rfl⟩ := hg
    refine ⟨-((-1 : ℤ) ^ n • (CH.mulP Φ.A).cupC (p := n) (q := 0 + 1) (by omega) H (CH.d (CH.modF Φ.A) 0 (h0 y))),
      neg_mem (zsmul_mem (cup_mem hF _ (r := n + 1) (r' := 1) hH (d_h0_mem_filtration_one hy)) _),
      (CH.mulP Φ.A).cupC (add_zero n) H (h0 y), cup_mem hF (add_zero n) (r := n + 1) (r' := 0) hH (h0_mem_filtration_zero hF y), ?_⟩
    rw [CrystallineSemistableComparison.P.leibniz, sub_neg_eq_add]

theorem fm_change (hF : IsFil Φ Fil) {a : ℕ} {u₀ u₀' : ∀ T : C, Φ.A.obj T} {u u' : Fin a → ∀ T : C, Φ.A.obj T}
    (h₀' : Nr Fil u₀') (hu : ∀ k, Nr Fil (u k))
    (hz₀ : ∀ T, u₀' T - u₀ T ∈ (Fil ((1 : ℕ) : ℤ)).S T) (hz : ∀ k T, u' k T - u k T ∈ (Fil ((1 : ℕ) : ℤ)).S T)
    {c : CH.H (sq (Fil (a : ℤ)) (Fil ((a : ℤ) + 1))) a}
    (h : CrystallineSemistableComparison.Pb.Rep (Fil (a : ℤ)) (Fil ((a : ℤ) + 1)) (fm u₀ u) c) :
    CrystallineSemistableComparison.Pb.Rep (Fil (a : ℤ)) (Fil ((a : ℤ) + 1)) (fm u₀' u') c := by
  set P := cupListC Φ.A fun k => CH.d (CH.modF Φ.A) 0 (h0 (u k)) with hP
  set P' := cupListC Φ.A fun k => CH.d (CH.modF Φ.A) 0 (h0 (u' k)) with hP'
  have hα : ∀ k, h0 (u' k) - h0 (u k) ∈ FC (Fil ((1 : ℕ) : ℤ)) 0 := fun k => mem_FC.2 fun t => hz k _
  have hbd : IsBd Fil a (P' - P) := by
    have := cupList_diff hF (fun k => CH.d (CH.modF Φ.A) 0 (h0 (u k))) (fun k => h0 (u' k) - h0 (u k))
      (fun k => d_h0_mem_filtration_one (hu k)) (fun k => CH.d_d _ 0 _) hα
    have e : (fun k => CH.d (CH.modF Φ.A) 0 (h0 (u k)) + CH.d (CH.modF Φ.A) 0 (h0 (u' k) - h0 (u k))) =
        fun k => CH.d (CH.modF Φ.A) 0 (h0 (u' k)) := by
      funext k
      rw [map_sub]
      abel
    rw [e] at this
    exact this
  obtain ⟨W, hW, hD⟩ := cup_h0_normal_coboundary hF hbd h₀'
  set D := (CH.mulP Φ.A).cupC (add_zero a) (P' - P) (h0 u₀') with hDdef
  set V := (CH.mulP Φ.A).cupC (add_zero a) P (h0 u₀' - h0 u₀) with hV
  have hVm : V ∈ FC (Fil ((a + 1 : ℕ) : ℤ)) a :=
    cup_mem hF (add_zero a) (r := a) (r' := 1)
      (cupList_mem hF _ fun k => d_h0_mem_filtration_one (hu k)) (mem_FC.2 fun t => hz₀ _)
  have e : fm u₀' u' = fm u₀ u + D + V := by
    change (CH.mulP Φ.A).cupC (add_zero a) P' (h0 u₀') = (CH.mulP Φ.A).cupC (add_zero a) P (h0 u₀) + D + V
    simp only [hDdef, hV, map_sub, LinearMap.sub_apply]
    abel
  have h1 : CrystallineSemistableComparison.Pb.Rep (Fil (a : ℤ)) (Fil ((a : ℤ) + 1)) (fm u₀ u + (D - W)) c :=
    rep_of_bd (z := fm u₀ u) (by rwa [add_sub_cancel_left]) h
  refine rep_congr h1 fun s => ?_
  have e2 : (fm u₀ u + (D - W)) - fm u₀' u' = -(W + V) := by
    rw [e]
    abel
  have h3 : -(W + V) ∈ FC (Fil ((a + 1 : ℕ) : ℤ)) a := neg_mem (add_mem hW hVm)
  have h4 := mem_FC.1 h3 s
  rw [← e2] at h4
  exact h4

theorem fm_exists (hF : IsFil Φ Fil) {a : ℕ} {u₀ : ∀ T : C, Φ.A.obj T} {u : Fin a → ∀ T : C, Φ.A.obj T}
    (h₀ : Nr Fil u₀) (hu : ∀ k, Nr Fil (u k)) :
    ∃ c : CH.H (sq (Fil (a : ℤ)) (Fil ((a : ℤ) + 1))) a, CrystallineSemistableComparison.Pb.Rep (Fil (a : ℤ)) (Fil ((a : ℤ) + 1)) (fm u₀ u) c :=
  rep_exists (fm u₀ u) (fun s => mem_FC.1 (fm_mem hF u₀ hu) s) (fun s => by
    have h := mem_FC.1 (d_fm_mem hF h₀ hu) s
    rw [Nat.cast_succ] at h
    exact h)

end Cls

section Conc
open CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2

theorem isFil_thFil {b : Base} (L : b.Fun) : IsFil (thP L) (thFil L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr T
    change T.pdPow r.toNat = ⊤
    rw [Int.toNat_of_nonpos hr]
    exact T.pdPow_zero
  · intro T
    change T.pdPow (1 : ℤ).toNat = T.J
    exact le_antisymm (GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_one_le T.δ) T.J_le_pdPow_one
  · intro r r' h T
    exact T.pdPow_anti (Int.toNat_le_toNat h)
  · intro r r' T x y hx hy
    have hx' : (show T.B from x) ∈ pdP T.δ r := by
      have : (show T.B from x) ∈ T.pdPow ((r : ℤ).toNat) := hx
      rw [Int.toNat_natCast] at this
      exact this
    have hy' : (show T.B from y) ∈ pdP T.δ r' := by
      have : (show T.B from y) ∈ T.pdPow ((r' : ℤ).toNat) := hy
      rw [Int.toNat_natCast] at this
      exact this
    have h := GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.δ r r' (Ideal.mul_mem_mul hx' hy')
    change _ ∈ T.pdPow (((r + r' : ℕ) : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact h
  · intro k T x hx
    change _ ∈ T.pdPow ((k : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP T.δ k hx

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem fil_one (T : Thick (smFun X q)) : (thFil (smFun X q) ((1 : ℕ) : ℤ)).S T = T.J :=
  (isFil_thFil (smFun X q)).one T

theorem lifts_nr (Λ : LiftsT q) (x : Γ(X, ⊤)) : Nr (Φ := thP (smFun X q)) (thFil (smFun X q)) fun T => Λ.v T x := by
  intro T T' f
  rw [fil_one]
  have h : Ideal.Quotient.mk T'.J (Λ.v T' x) = Ideal.Quotient.mk T'.J (f.φ (Λ.v T x)) := by
    rw [Λ.hv T' x]
    refine (GlobalTheory.CompanionTheory.KMVan.evT_nat f x).trans ?_
    change Ideal.quotientMap T'.J f.φ f.hle (ev T (inTop q T) x) = _
    rw [← Λ.hv T x]
    rfl
  exact Ideal.Quotient.eq.1 h

theorem lifts_sub (Λ Λ' : LiftsT q) (x : Γ(X, ⊤)) (T : Thick (smFun X q)) :
    Λ'.v T x - Λ.v T x ∈ (thFil (smFun X q) ((1 : ℕ) : ℤ)).S T := by
  rw [fil_one]
  exact Ideal.Quotient.eq.1 ((Λ'.hv T x).trans (Λ.hv T x).symm)

variable (q) in

def liftsTopBot : LiftsT q where
  v T g := Function.surjInv Ideal.Quotient.mk_surjective
    (ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (inTop q T) g)
  hv T g := Function.surjInv_eq _ _

theorem form_eq (Λ : LiftsT q) {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) :
    Λ.form g₀ g = fm (Φ := thP (smFun X q)) (fun T => Λ.v T g₀) fun k T => Λ.v T (g k) := by
  funext s
  refine Eq.trans ?_ (fm_val (Φ := thP (smFun X q)) (fun T => Λ.v T g₀) (fun k T => Λ.v T (g k)) s).symm
  exact mul_comm _ _

end Conc

open CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2 in

theorem main : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)),
    ∃ c : CrystallineSemistableComparison.HT.Hdg q a a, CrystallineSemistableComparison.Om.L2.IsFormT q g₀ g c := by
  intro K _ X q a g₀ g
  have hF := isFil_thFil (smFun X q)
  obtain ⟨c, hc⟩ := fm_exists (Φ := thP (smFun X q)) hF (u₀ := fun T => (liftsTopBot q).v T g₀)
    (u := fun k T => (liftsTopBot q).v T (g k)) (lifts_nr _ _) fun k => lifts_nr _ _
  refine ⟨c, fun Λ => ?_⟩
  rw [form_eq]
  exact fm_change hF (lifts_nr Λ g₀) (fun k => lifts_nr _ _) (lifts_sub _ _ _) (fun k => lifts_sub _ _ _) hc

end GlobalTheory.CompanionTheory.OmCls
