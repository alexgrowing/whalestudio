import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.LocalEqGlue

noncomputable section

open TopologicalSpace Opposite

variable {X Y Z : Scheme.{0}}

theorem resU_resU {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (x : Γ(X, U)ˣ) :
    res k (res h x) = res (k.trans h) x := by
  ext
  change (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE k).op).hom x.val = _
  rw [← X.presheaf.map_comp]
  rfl

theorem resU_pullU_resU (f : Y ⟶ X) {U V : X.Opens} (k : V ≤ U) {W : Y.Opens}
    (h : W ≤ f ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    res h (pullU f V (res k x)) = res (h.trans (f.preimage_mono k)) (pullU f U x) := by
  ext
  change (X.presheaf.map (homOfLE k).op ≫ f.appLE V W h).hom x.val = (f.appLE U W _).hom x.val
  rw [Scheme.Hom.map_appLE]

theorem resU_pullU_congr {m m' : Y ⟶ X} (e : m = m') (U : X.Opens) {W : Y.Opens}
    (h : W ≤ m ⁻¹ᵁ U) (h' : W ≤ m' ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU m U x) = res h' (pullU m' U x) := by
  subst e
  rfl

theorem resU_pullU_square {P : Scheme.{0}} {g : Z ⟶ Y} {f : Y ⟶ X} {g' : Z ⟶ P} {f' : P ⟶ X}
    (e : g ≫ f = g' ≫ f') (U : X.Opens) {W : Z.Opens} (h : W ≤ g ⁻¹ᵁ f ⁻¹ᵁ U)
    (h' : W ≤ g' ⁻¹ᵁ f' ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU g _ (pullU f U x)) = res h' (pullU g' _ (pullU f' U x)) := by
  exact resU_pullU_congr e U h h' x

theorem rs_rs {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE k).op).hom ((X.presheaf.map (homOfLE h).op).hom x) =
      (X.presheaf.map (homOfLE (k.trans h)).op).hom x := by
  change (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE k).op).hom x = _
  rw [← X.presheaf.map_comp]
  rfl

theorem rs_app (f : Y ⟶ X) (U : X.Opens) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (x : Γ(X, U)) :
    (Y.presheaf.map (homOfLE h).op).hom ((f.app U).hom x) = (f.appLE U W h).hom x := rfl

theorem appLE_rs (f : Y ⟶ X) {U V : X.Opens} (k : V ≤ U) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ V)
    (x : Γ(X, U)) :
    (f.appLE V W h).hom ((X.presheaf.map (homOfLE k).op).hom x) =
      (f.appLE U W (h.trans (f.preimage_mono k))).hom x := by
  change (X.presheaf.map (homOfLE k).op ≫ f.appLE V W h).hom x = _
  rw [Scheme.Hom.map_appLE]

theorem rs_appLE (f : Y ⟶ X) (U : X.Opens) {V W : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) (k : W ≤ V)
    (x : Γ(X, U)) :
    (Y.presheaf.map (homOfLE k).op).hom ((f.appLE U V h).hom x) =
      (f.appLE U W (k.trans h)).hom x := by
  change (f.appLE U V h ≫ Y.presheaf.map (homOfLE k).op).hom x = _
  rw [Scheme.Hom.appLE_map]

theorem val_res_pullU (f : Y ⟶ X) (U : X.Opens) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    ((res h (pullU f U x) : Γ(Y, W)ˣ) : Γ(Y, W)) = (f.appLE U W h).hom x := rfl

theorem val_res {U W : X.Opens} (h : W ≤ U) (x : Γ(X, U)ˣ) :
    ((res h x : Γ(X, W)ˣ) : Γ(X, W)) = (X.presheaf.map (homOfLE h).op).hom x := rfl

theorem inf_inf_le_inf_left (A B C D : X.Opens) : (A ⊓ B) ⊓ (C ⊓ D) ≤ A ⊓ C :=
  fun _ hx => ⟨hx.1.1, hx.2.1⟩

theorem inf_inf_le_inf_right (A B C D : X.Opens) : (A ⊓ B) ⊓ (C ⊓ D) ≤ B ⊓ D :=
  fun _ hx => ⟨hx.1.2, hx.2.2⟩

theorem inf_preimage_le (f : Y ⟶ X) (A B : X.Opens) : f ⁻¹ᵁ A ⊓ f ⁻¹ᵁ B ≤ f ⁻¹ᵁ (A ⊓ B) :=
  fun _ hx => hx

theorem pull_g_eq (L : LB X) (f : Y ⟶ X) (i i' : (L.pull f).ι) :
    (L.pull f).g i i' = res (le_inf ((inf_le_left.trans (LB.wchart_le L (fun _ => f) i PUnit.unit)))
      (inf_le_right.trans (LB.wchart_le L (fun _ => f) i' PUnit.unit)))
      (pullU f _ (L.g (i PUnit.unit) (i' PUnit.unit))) := by
  exact (Fintype.prod_unique (fun _ : PUnit => _)).trans (zpow_one _)

theorem cancel_nzd {R : Type} [CommRing R] {x y r : R} (hr : r ∈ nonZeroDivisors R)
    (h : x * r = y * r) : x = y :=
  (mul_cancel_right_mem_nonZeroDivisors hr).mp h

theorem exists_lb_of_localEq : ∀ (X Y : Scheme.{0}) (j : Y ⟶ X) (L : LB Y) (θ : L.Sec) (Ix : Type) (V : Ix → X.Opens) (a : ∀ k, Γ(X, V k)), (∀ k (W : X.Opens) (hW : W ≤ V k), (X.presheaf.map (homOfLE hW).op).hom (a k) ∈ nonZeroDivisors Γ(X, W)) → (∀ k (W : Y.Opens) (hW : W ≤ j ⁻¹ᵁ V k), (Y.presheaf.map (homOfLE hW).op).hom ((j.app (V k)).hom (a k)) ∈ nonZeroDivisors Γ(Y, W)) → (∀ k l, ∃ c : Γ(X, V k ⊓ V l)ˣ, (X.presheaf.map (homOfLE inf_le_left).op).hom (a k) = (c : Γ(X, V k ⊓ V l)) * (X.presheaf.map (homOfLE inf_le_right).op).hom (a l)) → (∀ k i, ∃ w : Γ(Y, j ⁻¹ᵁ V k ⊓ L.U i)ˣ, (Y.presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) = (w : Γ(Y, j ⁻¹ᵁ V k ⊓ L.U i)) * (Y.presheaf.map (homOfLE inf_le_left).op).hom ((j.app (V k)).hom (a k))) → ∃ (O : X.Opens) (N : LB O.toScheme), (∀ k, V k ≤ O) ∧ N.IsLB ∧ LBIso (N.pull (pullback.fst O.ι j)) (L.pull (pullback.snd O.ι j)) := by
  intro X Y j L θ Ix V a ha hb hc hw
  choose c hc using hc
  choose w hw using hw
  have c_self : ∀ k, c k k = 1 := by
    intro k
    apply Units.ext
    have h' : (c k k : Γ(X, V k ⊓ V k)) *
        (X.presheaf.map (homOfLE (inf_le_left : V k ⊓ V k ≤ V k)).op).hom (a k) =
        1 * (X.presheaf.map (homOfLE (inf_le_left : V k ⊓ V k ≤ V k)).op).hom (a k) := by
      rw [_root_.one_mul]; exact (hc k k).symm
    exact cancel_nzd (ha k (V k ⊓ V k) inf_le_left) h'
  have c_cocycle : ∀ k l m,
      res (inf_le_left : V k ⊓ V l ⊓ V m ≤ V k ⊓ V l) (c k l) *
        res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          V k ⊓ V l ⊓ V m ≤ V l ⊓ V m) (c l m) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          V k ⊓ V l ⊓ V m ≤ V k ⊓ V m) (c k m) := by
    intro k l m
    apply Units.ext
    have e1 := congrArg (X.presheaf.map (homOfLE
      (inf_le_left : V k ⊓ V l ⊓ V m ≤ V k ⊓ V l)).op).hom (hc k l)
    have e2 := congrArg (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          V k ⊓ V l ⊓ V m ≤ V l ⊓ V m)).op).hom (hc l m)
    have e3 := congrArg (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          V k ⊓ V l ⊓ V m ≤ V k ⊓ V m)).op).hom (hc k m)
    simp only [map_mul, rs_rs] at e1 e2 e3
    apply cancel_nzd (ha m (V k ⊓ V l ⊓ V m) inf_le_right)
    simp only [res, Units.coe_map, MonoidHom.coe_coe, Units.val_mul]
    rw [_root_.mul_assoc, ← e2, ← e1, e3]
  have Y1 : ∀ k l i i',
      res (inf_inf_le_inf_left (j ⁻¹ᵁ V k) (j ⁻¹ᵁ V l) (L.U i) (L.U i')) (w k i) =
        res (inf_le_right : (j ⁻¹ᵁ V k ⊓ j ⁻¹ᵁ V l) ⊓ (L.U i ⊓ L.U i') ≤ L.U i ⊓ L.U i')
          (L.g i i') *
        (res ((inf_le_left : (j ⁻¹ᵁ V k ⊓ j ⁻¹ᵁ V l) ⊓ (L.U i ⊓ L.U i') ≤ _).trans
          (inf_preimage_le j (V k) (V l))) (pullU j _ (c k l)))⁻¹ *
        res (inf_inf_le_inf_right (j ⁻¹ᵁ V k) (j ⁻¹ᵁ V l) (L.U i) (L.U i')) (w l i') := by
    intro k l i i'
    have hWl : (j ⁻¹ᵁ V k ⊓ j ⁻¹ᵁ V l) ⊓ (L.U i ⊓ L.U i') ≤ j ⁻¹ᵁ V l := fun _ hx => hx.1.2
    have hWkl : (j ⁻¹ᵁ V k ⊓ j ⁻¹ᵁ V l) ⊓ (L.U i ⊓ L.U i') ≤ j ⁻¹ᵁ (V k ⊓ V l) := fun _ hx => hx.1
    have hW1 : (j ⁻¹ᵁ V k ⊓ j ⁻¹ᵁ V l) ⊓ (L.U i ⊓ L.U i') ≤ j ⁻¹ᵁ V k ⊓ L.U i :=
      fun _ hx => ⟨hx.1.1, hx.2.1⟩
    have hW2 : (j ⁻¹ᵁ V k ⊓ j ⁻¹ᵁ V l) ⊓ (L.U i ⊓ L.U i') ≤ j ⁻¹ᵁ V l ⊓ L.U i' :=
      fun _ hx => ⟨hx.1.2, hx.2.2⟩
    have hW3 : (j ⁻¹ᵁ V k ⊓ j ⁻¹ᵁ V l) ⊓ (L.U i ⊓ L.U i') ≤ L.U i ⊓ L.U i' := fun _ hx => hx.2
    have f1 := congrArg (Y.presheaf.map (homOfLE hW1).op).hom (hw k i)
    have f2 := congrArg (Y.presheaf.map (homOfLE hW2).op).hom (hw l i')
    have f3 := congrArg (Y.presheaf.map (homOfLE hW3).op).hom (θ.compat i i')
    have f4 := congrArg (j.appLE (V k ⊓ V l) _ hWkl).hom (hc k l)
    simp only [map_mul, rs_rs, rs_app, appLE_rs, rs_appLE] at f1 f2 f3 f4
    have Y1e : (Y.presheaf.map (homOfLE hW1).op).hom (w k i : Γ(Y, j ⁻¹ᵁ V k ⊓ L.U i)) *
        (j.appLE (V k ⊓ V l) _ hWkl).hom (c k l : Γ(X, V k ⊓ V l)) =
        (Y.presheaf.map (homOfLE hW3).op).hom (L.g i i' : Γ(Y, L.U i ⊓ L.U i')) *
        (Y.presheaf.map (homOfLE hW2).op).hom (w l i' : Γ(Y, j ⁻¹ᵁ V l ⊓ L.U i')) := by
      apply cancel_nzd (hb l _ hWl)
      simp only [rs_app]
      rw [_root_.mul_assoc, ← f4, ← f1, f3, f2, _root_.mul_assoc]
    rw [mul_right_comm, eq_mul_inv_iff_mul_eq]
    exact Units.ext Y1e
  let O : X.Opens := ⨆ k, V k
  have hVO : ∀ k, V k ≤ O := fun k => le_iSup V k
  have hinf3 : ∀ A B C : X.Opens,
      O.ι ⁻¹ᵁ A ⊓ O.ι ⁻¹ᵁ B ⊓ O.ι ⁻¹ᵁ C ≤ O.ι ⁻¹ᵁ (A ⊓ B ⊓ C) := fun _ _ _ _ hx => hx
  let N : LB O.toScheme := LB.mk Ix (fun k => O.ι ⁻¹ᵁ V k)
    (fun k l => res (inf_preimage_le O.ι (V k) (V l))
      (pullU O.ι _ (c k l)))
  have hN : N.IsLB := by
    refine ⟨?_, ?_, ?_⟩
    · refine eq_top_iff.mpr fun x _ => ?_
      have hx : O.ι x ∈ O := by
        first
          | exact x.2
          | exact (Scheme.Opens.range_ι O).le ⟨x, rfl⟩
          | simp [Scheme.Opens.ι_apply]
      rw [TopologicalSpace.Opens.mem_iSup] at hx ⊢
      exact hx
    · intro k
      show res _ (res _ (pullU O.ι _ (c k k))) = 1
      rw [c_self, map_one, map_one, map_one]
    · intro k l m
      show res _ (res _ (pullU O.ι _ (c k l))) * res _ (res _ (pullU O.ι _ (c l m))) =
        res _ (res _ (pullU O.ι _ (c k m)))
      have := congrArg (fun u => res (hinf3 (V k) (V l) (V m)) (pullU O.ι _ u))
        (c_cocycle k l m)
      simp only [map_mul, resU_pullU_resU] at this
      simp only [resU_resU]
      exact this
  refine ⟨O, N, hVO, hN, ?_⟩
  have hsq : pullback.fst O.ι j ≫ O.ι = pullback.snd O.ι j ≫ j := pullback.condition
  have hpt : ∀ x, O.ι.base ((pullback.fst O.ι j).base x) = j.base ((pullback.snd O.ι j).base x) :=
    fun x => by
      have := congrArg (fun f : pullback O.ι j ⟶ X => f.base x) hsq
      simpa using this
  have hle : ∀ p : (PUnit → L.ι) × (PUnit → Ix),
      (L.pull (pullback.snd O.ι j)).U p.1 ⊓ (N.pull (pullback.fst O.ι j)).U p.2 ≤
        pullback.snd O.ι j ⁻¹ᵁ (j ⁻¹ᵁ V (p.2 PUnit.unit) ⊓ L.U (p.1 PUnit.unit)) := by
    intro p x hx
    have h1 := LB.wchart_le L (fun _ => pullback.snd O.ι j) p.1 PUnit.unit hx.1
    have h2 := LB.wchart_le N (fun _ => pullback.fst O.ι j) p.2 PUnit.unit hx.2
    refine ⟨?_, h1⟩
    show j.base ((pullback.snd O.ι j).base x) ∈ V (p.2 PUnit.unit)
    rw [← hpt]
    exact h2
  let w' : LB.Iso (N.pull (pullback.fst O.ι j)) (L.pull (pullback.snd O.ι j)) :=
    ⟨fun p => res (hle p) (pullU (pullback.snd O.ι j) _ (w (p.2 PUnit.unit) (p.1 PUnit.unit)))⟩
  refine ⟨w', fun p q => ?_⟩
  have hQ : (LB.div (L.pull (pullback.snd O.ι j)) (N.pull (pullback.fst O.ι j))).U p ⊓
      (LB.div (L.pull (pullback.snd O.ι j)) (N.pull (pullback.fst O.ι j))).U q ≤
      pullback.snd O.ι j ⁻¹ᵁ ((j ⁻¹ᵁ V (p.2 PUnit.unit) ⊓ j ⁻¹ᵁ V (q.2 PUnit.unit)) ⊓
        (L.U (p.1 PUnit.unit) ⊓ L.U (q.1 PUnit.unit))) := fun x hx =>
    ⟨⟨(hle p hx.1).1, (hle q hx.2).1⟩, ⟨(hle p hx.1).2, (hle q hx.2).2⟩⟩
  have hQc : (LB.div (L.pull (pullback.snd O.ι j)) (N.pull (pullback.fst O.ι j))).U p ⊓
      (LB.div (L.pull (pullback.snd O.ι j)) (N.pull (pullback.fst O.ι j))).U q ≤
      pullback.fst O.ι j ⁻¹ᵁ O.ι ⁻¹ᵁ (V (p.2 PUnit.unit) ⊓ V (q.2 PUnit.unit)) := fun x hx =>
    ⟨LB.wchart_le N (fun _ => pullback.fst O.ι j) p.2 PUnit.unit hx.1.2,
      LB.wchart_le N (fun _ => pullback.fst O.ι j) q.2 PUnit.unit hx.2.2⟩
  have key := congrArg (fun u => res hQ (pullU (pullback.snd O.ι j) _ u))
    (Y1 (p.2 PUnit.unit) (q.2 PUnit.unit) (p.1 PUnit.unit) (q.1 PUnit.unit))
  simp only [map_mul, map_inv, resU_pullU_resU] at key
  rw [resU_pullU_square hsq.symm _ _ hQc] at key
  have goal' : res (inf_le_left : ((L.pull (pullback.snd O.ι j)).U p.1 ⊓ (N.pull (pullback.fst O.ι j)).U p.2) ⊓
        ((L.pull (pullback.snd O.ι j)).U q.1 ⊓ (N.pull (pullback.fst O.ι j)).U q.2) ≤ _)
        (res (hle p) (pullU (pullback.snd O.ι j) _ (w (p.2 PUnit.unit) (p.1 PUnit.unit)))) =
      (res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          ((L.pull (pullback.snd O.ι j)).U p.1 ⊓ (N.pull (pullback.fst O.ι j)).U p.2) ⊓
          ((L.pull (pullback.snd O.ι j)).U q.1 ⊓ (N.pull (pullback.fst O.ι j)).U q.2) ≤ _)
          ((L.pull (pullback.snd O.ι j)).g p.1 q.1) *
        (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          ((L.pull (pullback.snd O.ι j)).U p.1 ⊓ (N.pull (pullback.fst O.ι j)).U p.2) ⊓
          ((L.pull (pullback.snd O.ι j)).U q.1 ⊓ (N.pull (pullback.fst O.ι j)).U q.2) ≤ _)
          ((N.pull (pullback.fst O.ι j)).g p.2 q.2))⁻¹) *
      res (inf_le_right : ((L.pull (pullback.snd O.ι j)).U p.1 ⊓ (N.pull (pullback.fst O.ι j)).U p.2) ⊓
        ((L.pull (pullback.snd O.ι j)).U q.1 ⊓ (N.pull (pullback.fst O.ι j)).U q.2) ≤ _)
        (res (hle q) (pullU (pullback.snd O.ι j) _ (w (q.2 PUnit.unit) (q.1 PUnit.unit)))) := by
    have eL : res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          ((L.pull (pullback.snd O.ι j)).U p.1 ⊓ (N.pull (pullback.fst O.ι j)).U p.2) ⊓
          ((L.pull (pullback.snd O.ι j)).U q.1 ⊓ (N.pull (pullback.fst O.ι j)).U q.2) ≤ _)
          ((L.pull (pullback.snd O.ι j)).g p.1 q.1) =
        res (hQ.trans ((pullback.snd O.ι j).preimage_mono inf_le_right))
          (pullU (pullback.snd O.ι j) _ (L.g (p.1 PUnit.unit) (q.1 PUnit.unit))) := by
      rw [pull_g_eq]
      exact resU_resU _ _ _
    have eN : res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          ((L.pull (pullback.snd O.ι j)).U p.1 ⊓ (N.pull (pullback.fst O.ι j)).U p.2) ⊓
          ((L.pull (pullback.snd O.ι j)).U q.1 ⊓ (N.pull (pullback.fst O.ι j)).U q.2) ≤ _)
          ((N.pull (pullback.fst O.ι j)).g p.2 q.2) =
        res hQc (pullU (pullback.fst O.ι j) _
          (pullU O.ι _ (c (p.2 PUnit.unit) (q.2 PUnit.unit)))) := by
      rw [pull_g_eq, show N.g (p.2 PUnit.unit) (q.2 PUnit.unit) =
        res (inf_preimage_le O.ι (V (p.2 PUnit.unit)) (V (q.2 PUnit.unit)))
          (pullU O.ι _ (c (p.2 PUnit.unit) (q.2 PUnit.unit))) from rfl]
      refine (resU_resU _ _ _).trans ?_
      exact resU_pullU_resU (pullback.fst O.ι j) (inf_preimage_le O.ι _ _) _ _
    rw [eL, eN, resU_resU, resU_resU]
    exact key
  exact goal'

end

end GlobalTheory.LocalEqGlue
