import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

noncomputable section

namespace GlobalTheory.CompanionTheory.NormLB

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LBGerm

variable {X Y : Scheme.{0}} {L : LB X} {W W' : X.Opens}

structure Frame (L : LB X) (W : X.Opens) where

  e : ∀ i, Γ(X, W ⊓ L.U i)ˣ

  rel : ∀ (x : X) (i j : L.ι), x ∈ W ⊓ L.U i → x ∈ W ⊓ L.U j →
    gm (𝟙 X) x _ (e i) = gm (𝟙 X) x (L.U i ⊓ L.U j) (L.g i j) * gm (𝟙 X) x _ (e j)

def Frame.res (e : Frame L W) (h : W' ≤ W) : Frame L W' where
  e i := Semi.res (inf_le_inf_right _ h) (e.e i)
  rel x i j hi hj := by
    rw [gm_res (𝟙 X) x _ hi, gm_res (𝟙 X) x _ hj]
    exact e.rel x i j ⟨h hi.1, hi.2⟩ ⟨h hj.1, hj.2⟩

theorem gs_appIso_inv (W : X.Opens) (A : W.toScheme.Opens) (z : W.toScheme) (hz : z ∈ A) (a : Γ(W.toScheme, A)) :
    gs W.ι z (W.ι ''ᵁ A) ((W.ι.appIso A).inv.hom a) = gs (𝟙 _) z A a := by
  have hz' : W.ι z ∈ W.ι ''ᵁ A := ⟨z, hz, rfl⟩
  have e := gs_pull (𝟙 _) W.ι z (W.ι ''ᵁ A) hz' ((W.ι.appIso A).inv.hom a)
  rw [Category.id_comp] at e
  rw [← e]
  have e2 : (W.ι.app (W.ι ''ᵁ A)).hom ((W.ι.appIso A).inv.hom a) =
      resG W.toScheme (W.ι.preimage_image_eq A).le a := by
    have := congrArg (fun f => f.hom a) (Scheme.Hom.appIso_inv_app W.ι A)
    exact this
  rw [e2]
  exact gs_res (𝟙 _) z _ (by simpa using hz) a

theorem gm_stalk {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)ˣ) :
    (gm r z U a).val = (r.stalkMap z).hom (gm (𝟙 X) (r z) U a).val := by
  rw [← gs_unit r z U h, ← gs_unit (𝟙 X) (r z) U h]
  exact gs_stalkMap r z U h a.val

def genUnit (W : X.Opens) (t : (L.pull W.ι).Gen) (i : L.ι) : Γ(X, W ⊓ L.U i)ˣ :=
  Semi.res (U := W.ι ''ᵁ (L.pull W.ι).U fun _ => i) (V := W ⊓ L.U i)
    (fun x hx => ⟨⟨x, hx.1⟩, mem_pull.2 hx.2, rfl⟩)
    (Units.map (W.ι.appIso ((L.pull W.ι).U fun _ => i)).inv.hom (t.s fun _ => i))

theorem gm_genUnit (W : X.Opens) (t : (L.pull W.ι).Gen) (i : L.ι) (z : W.toScheme) (hz : W.ι z ∈ L.U i) :
    gm W.ι z _ (genUnit W t i) = gm (𝟙 _) z _ (t.s fun _ => i) := by
  have hA : z ∈ (L.pull W.ι).U fun _ => i := mem_pull.2 hz
  have h1 : W.ι z ∈ W ⊓ L.U i := ⟨z.2, hz⟩
  apply Units.ext
  rw [← gs_unit W.ι z _ h1, ← gs_unit (𝟙 _) z _ hA]
  exact (gs_res W.ι z _ h1 _).trans (gs_appIso_inv W _ z hA _)

def Frame.ofGen (W : X.Opens) (t : (L.pull W.ι).Gen) (ht : t.IsGen) : Frame L W where
  e := genUnit W t
  rel x i j hi hj := by
    obtain ⟨z, rfl⟩ : ∃ z : W.toScheme, W.ι z = x := ⟨⟨x, hi.1⟩, rfl⟩
    have hiz : z ∈ (L.pull W.ι).U fun _ => i := mem_pull.2 hi.2
    have hjz : z ∈ (L.pull W.ι).U fun _ => j := mem_pull.2 hj.2
    have hm : z ∈ (L.pull W.ι).U (fun _ => i) ⊓ (L.pull W.ι).U fun _ => j := ⟨hiz, hjz⟩
    have e1 := congrArg (gm (𝟙 _) z _) (ht (fun _ => i) (fun _ => j))
    rw [map_mul, gm_res (𝟙 _) z _ hm, gm_res (𝟙 _) z _ hm, (chartPullPull L W.ι).g z _ _ hiz hjz,
      ← gm_genUnit W t i z hi.2, ← gm_genUnit W t j z hj.2] at e1
    have inj : Function.Injective (W.ι.stalkMap z).hom :=
      (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap z)).1
    have hij : W.ι z ∈ L.U i ⊓ L.U j := ⟨hi.2, hj.2⟩
    apply Units.ext
    apply inj
    rw [Units.val_mul, map_mul, ← gm_stalk W.ι z _ hi, ← gm_stalk W.ι z _ hij, ← gm_stalk W.ι z _ hj]
    exact congrArg Units.val e1

theorem exists_div (hL : L.IsLB) (e : Frame L W) (e' : Frame L W') (T : X.Opens) (hT : T ≤ W) (hT' : T ≤ W') :
    ∃ u : Γ(X, T)ˣ, ∀ (x : X) (i : L.ι), x ∈ T → (hi : x ∈ L.U i) →
      gm (𝟙 X) x T u = gm (𝟙 X) x _ (e'.e i) * (gm (𝟙 X) x _ (e.e i))⁻¹ := by
  have h1 : ∀ i, T ⊓ L.U i ≤ W ⊓ L.U i := fun i => inf_le_inf_right _ hT
  have h2 : ∀ i, T ⊓ L.U i ≤ W' ⊓ L.U i := fun i => inf_le_inf_right _ hT'
  obtain ⟨u, hu⟩ := glue_unit T (fun i => T ⊓ L.U i) (fun _ => inf_le_left)
    (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hL x
      exact Opens.mem_iSup.2 ⟨i, hx, hi⟩)
    (fun i => Semi.res (h2 i) (e'.e i) * (Semi.res (h1 i) (e.e i))⁻¹)
    (fun i j x hx => by
      have a := e.rel x i j (h1 i hx.1) (h1 j hx.2)
      have b := e'.rel x i j (h2 i hx.1) (h2 j hx.2)
      rw [map_mul, map_mul, map_inv, map_inv, gm_res _ x _ hx.1, gm_res _ x _ hx.1, gm_res _ x _ hx.2,
        gm_res _ x _ hx.2, a, b, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul])
  refine ⟨u, fun x i hx hi => ?_⟩
  have hm : x ∈ T ⊓ L.U i := ⟨hx, hi⟩
  have := congrArg (gm (𝟙 X) x _) (hu i)
  rwa [gm_res _ x _ hm, map_mul, map_inv, gm_res _ x _ hm, gm_res _ x _ hm] at this

def Frame.div (hL : L.IsLB) (e : Frame L W) (e' : Frame L W') (T : X.Opens) (hT : T ≤ W) (hT' : T ≤ W') : Γ(X, T)ˣ :=
  (exists_div hL e e' T hT hT').choose

theorem Frame.gm_div (hL : L.IsLB) (e : Frame L W) (e' : Frame L W') {T : X.Opens} (hT : T ≤ W) (hT' : T ≤ W')
    {x : X} (i : L.ι) (hx : x ∈ T) (hi : x ∈ L.U i) :
    gm (𝟙 X) x T (e.div hL e' T hT hT') = gm (𝟙 X) x _ (e'.e i) * (gm (𝟙 X) x _ (e.e i))⁻¹ :=
  (exists_div hL e e' T hT hT').choose_spec x i hx hi

theorem Frame.res_div (hL : L.IsLB) (e : Frame L W) (e' : Frame L W') {T T' : X.Opens} (hT : T ≤ W) (hT' : T ≤ W')
    (h : T' ≤ T) : Semi.res h (e.div hL e' T hT hT') = e.div hL e' T' (h.trans hT) (h.trans hT') :=
  unit_ext fun x hx => by
    obtain ⟨i, hi⟩ := exists_chart hL x
    rw [gm_res _ x _ hx, e.gm_div hL e' hT hT' i (h hx) hi, e.gm_div hL e' _ _ i hx hi]

theorem Frame.div_self (hL : L.IsLB) (e : Frame L W) {T : X.Opens} (hT : T ≤ W) (hT' : T ≤ W) :
    e.div hL e T hT hT' = 1 :=
  unit_ext fun x hx => by
    obtain ⟨i, hi⟩ := exists_chart hL x
    rw [e.gm_div hL e hT hT' i hx hi, mul_inv_cancel, map_one]

theorem Frame.div_mul_div (hL : L.IsLB) {W'' : X.Opens} (e : Frame L W) (e' : Frame L W') (e'' : Frame L W'')
    {T : X.Opens} (h : T ≤ W) (h' : T ≤ W') (h'' : T ≤ W'') :
    e.div hL e' T h h' * e'.div hL e'' T h' h'' = e.div hL e'' T h h'' :=
  unit_ext fun x hx => by
    obtain ⟨i, hi⟩ := exists_chart hL x
    rw [map_mul, e.gm_div hL e' h h' i hx hi, e'.gm_div hL e'' h' h'' i hx hi, e.gm_div hL e'' h h'' i hx hi]
    simp only [← div_eq_mul_inv]
    rw [mul_comm]
    exact div_mul_div_cancel _ _ _

theorem exists_fn (hL : L.IsLB) (e : Frame L W) {n : ℕ} (s : (lbPow L n).Sec) :
    ∃ a : Γ(X, W), ∀ (x : X) (i : L.ι), x ∈ W → (hi : x ∈ L.U i) →
      gs (𝟙 X) x W a * (gm (𝟙 X) x _ (e.e i)).val ^ n = gs (𝟙 X) x _ (powFn s fun _ => i) := by
  have hc : ∀ i, W ⊓ L.U i ≤ powChart L fun _ => i := fun i x hx => mem_powChart.2 hx.2
  let a : ∀ i, Γ(X, W ⊓ L.U i) := fun i => resG X (hc i) (powFn s fun _ => i) * (((e.e i)⁻¹ ^ n : Γ(X, W ⊓ L.U i)ˣ) : Γ(X, W ⊓ L.U i))
  have ga : ∀ (x : X) (i : L.ι) (hx : x ∈ W ⊓ L.U i), gs (𝟙 X) x _ (a i) =
      gs (𝟙 X) x _ (powFn s fun _ => i) * (((gm (𝟙 X) x _ (e.e i))⁻¹ ^ n : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) := by
    intro x i hx
    rw [gs_mul _ x _ hx, gs_res _ x _ hx, gs_unit _ x _ hx, map_pow, map_inv]
  have inv1 : ∀ (x : X) (u : (X.presheaf.stalk x)ˣ), (u.val) ^ n * ((u⁻¹ ^ n : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) = 1 := by
    intro x u
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow, Units.val_one]
  have hh : ∀ i j, resG X (inf_le_left : (W ⊓ L.U i) ⊓ (W ⊓ L.U j) ≤ W ⊓ L.U i) (a i) =
      resG X (inf_le_right : (W ⊓ L.U i) ⊓ (W ⊓ L.U j) ≤ W ⊓ L.U j) (a j) := fun i j => fn_ext fun x hx => by
    have h1 := inv1 x (gm (𝟙 X) x _ (L.g i j))
    rw [gs_res _ x _ hx, gs_res _ x _ hx, ga x i hx.1, ga x j hx.2,
      gs_powFn_compat s (𝟙 X) x (fun _ => i) (fun _ => j) (mem_powChart.2 hx.1.2) (mem_powChart.2 hx.2.2),
      e.rel x i j hx.1 hx.2, mul_inv, mul_pow, Units.val_mul]
    linear_combination (gs (𝟙 X) x _ (powFn s fun _ => j) *
      (((gm (𝟙 X) x _ (e.e j))⁻¹ ^ n : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x)) * h1
  obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' (fun i => W ⊓ L.U i) W (fun i => homOfLE inf_le_left)
    (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hL x
      exact Opens.mem_iSup.2 ⟨i, hx, hi⟩) a hh
  refine ⟨b, fun x i hxW hi => ?_⟩
  have hx : x ∈ W ⊓ L.U i := ⟨hxW, hi⟩
  have e1 : gs (𝟙 X) x _ (a i) = gs (𝟙 X) x W b := by
    rw [← hb i]
    exact gs_res _ x inf_le_left hx b
  have h1 := inv1 x (gm (𝟙 X) x _ (e.e i))
  rw [← e1, ga x i hx]
  linear_combination (gs (𝟙 X) x _ (powFn s fun _ => i)) * h1

def Frame.fn (hL : L.IsLB) (e : Frame L W) {n : ℕ} (s : (lbPow L n).Sec) : Γ(X, W) := (exists_fn hL e s).choose

theorem Frame.gs_fn (hL : L.IsLB) (e : Frame L W) {n : ℕ} (s : (lbPow L n).Sec) {x : X} (i : L.ι) (hx : x ∈ W)
    (hi : x ∈ L.U i) : gs (𝟙 X) x W (e.fn hL s) * (gm (𝟙 X) x _ (e.e i)).val ^ n =
      gs (𝟙 X) x _ (powFn s fun _ => i) :=
  (exists_fn hL e s).choose_spec x i hx hi

theorem Frame.res_fn (hL : L.IsLB) (e : Frame L W) (e' : Frame L W') {n : ℕ} (s : (lbPow L n).Sec) {T : X.Opens}
    (hT : T ≤ W) (hT' : T ≤ W') :
    resG X hT (e.fn hL s) = ((e.div hL e' T hT hT') ^ n).val * resG X hT' (e'.fn hL s) := fn_ext fun x hx => by
  obtain ⟨i, hi⟩ := exists_chart hL x
  have a := e.gs_fn hL s i (hT hx) hi
  have b := e'.gs_fn hL s i (hT' hx) hi
  rw [gs_res _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_unit _ x _ hx, map_pow, e.gm_div hL e' hT hT' i hx hi]
  have u : (((gm (𝟙 X) x _ (e'.e i) * (gm (𝟙 X) x _ (e.e i))⁻¹) ^ n : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) *
      (gm (𝟙 X) x _ (e.e i)).val ^ n = (gm (𝟙 X) x _ (e'.e i)).val ^ n := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, inv_mul_cancel_right, Units.val_pow_eq_pow_val]
  apply ((gm (𝟙 X) x _ (e.e i) ^ n).isUnit).mul_right_cancel
  rw [Units.val_pow_eq_pow_val]
  linear_combination a - b - gs (𝟙 X) x W' (e'.fn hL s) * u

theorem Frame.mem_basicOpen_fn (hL : L.IsLB) (e : Frame L W) {n : ℕ} (s : (lbPow L n).Sec) {x : X} (hx : x ∈ W) :
    x ∈ X.basicOpen (e.fn hL s) ↔ x ∈ nonzeroLocus s := by
  obtain ⟨i, hi⟩ := exists_chart hL x
  refine (isUnit_gs_iff (𝟙 X) x W hx _).symm.trans ?_
  rw [mem_nonzeroLocus_iff_powFn s (J := fun _ => i) (mem_powChart.2 hi),
    ← e.gs_fn hL s i hx hi, ← Units.val_pow_eq_pow_val, Units.isUnit_mul_units]

section Norm

variable (q : X ⟶ Y) (N : ∀ V : Y.Opens, Γ(X, q ⁻¹ᵁ V) →* Γ(Y, V))

def NormRes : Prop := ∀ (V W : Y.Opens) (h : W ≤ V) (a : Γ(X, q ⁻¹ᵁ V)),
  (Y.presheaf.map (homOfLE h).op).hom (N V a) =
    N W ((X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ V from fun _ hx => h hx)).op).hom a)

def normLB (hL : L.IsLB) : LB Y where
  ι := Σ V : Y.Opens, Frame L (q ⁻¹ᵁ V)
  U c := c.1
  g c c' := Units.map (N (c.1 ⊓ c'.1))
    (c.2.div hL c'.2 _ (q.preimage_mono inf_le_left) (q.preimage_mono inf_le_right))

variable {q N}

theorem normLB_res_g (hN : NormRes q N) (hL : L.IsLB) (c c' : (normLB q N hL).ι) {T : Y.Opens}
    (h : T ≤ c.1 ⊓ c'.1) :
    Semi.res h ((normLB q N hL).g c c') = Units.map (N T)
      (c.2.div hL c'.2 (q ⁻¹ᵁ T) (q.preimage_mono (h.trans inf_le_left)) (q.preimage_mono (h.trans inf_le_right))) :=
  Units.ext ((hN _ _ h _).trans (congrArg (N T) (congrArg Units.val (Frame.res_div hL c.2 c'.2 _ _ _))))

theorem isLB_normLB (hN : NormRes q N) (hL : L.IsLB) (hc : ∀ y : Y, ∃ c : (normLB q N hL).ι, y ∈ c.1) :
    (normLB q N hL).IsLB where
  cover := top_le_iff.1 fun y _ => Opens.mem_iSup.2 (hc y)
  g_self c := (normLB_res_g hN hL c c _).trans (by rw [Frame.div_self, map_one])
  cocycle c₁ c₂ c₃ := (congrArg₂ (· * ·) (normLB_res_g hN hL c₁ c₂ _) (normLB_res_g hN hL c₂ c₃ _)).trans
    (((map_mul _ _ _).symm.trans (congrArg _ (Frame.div_mul_div hL _ _ _ _ _ _))).trans
      (normLB_res_g hN hL c₁ c₃ _).symm)

theorem gs_norm_compat (hN : NormRes q N) (hL : L.IsLB) {n : ℕ} (s : (lbPow L n).Sec) (c c' : (normLB q N hL).ι)
    {y : Y} (hy : y ∈ c.1) (hy' : y ∈ c'.1) :
    gs (𝟙 Y) y c.1 (N c.1 (c.2.fn hL s)) = (gm (𝟙 Y) y (c.1 ⊓ c'.1) ((normLB q N hL).g c c')).val ^ n *
      gs (𝟙 Y) y c'.1 (N c'.1 (c'.2.fn hL s)) := by
  have hm : y ∈ c.1 ⊓ c'.1 := ⟨hy, hy'⟩
  have e := Frame.res_fn hL c.2 c'.2 s (T := q ⁻¹ᵁ (c.1 ⊓ c'.1)) (q.preimage_mono inf_le_left)
    (q.preimage_mono inf_le_right)
  have e1 := hN c.1 (c.1 ⊓ c'.1) inf_le_left (c.2.fn hL s)
  have e2 := hN c'.1 (c.1 ⊓ c'.1) inf_le_right (c'.2.fn hL s)
  let gu : Γ(Y, c.1 ⊓ c'.1)ˣ := (normLB q N hL).g c c'
  have e3 : resG Y (inf_le_left : c.1 ⊓ c'.1 ≤ c.1) (N c.1 (c.2.fn hL s)) =
      (gu ^ n).val * resG Y (inf_le_right : c.1 ⊓ c'.1 ≤ c'.1) (N c'.1 (c'.2.fn hL s)) := by
    refine e1.trans (Eq.trans (congrArg _ e) ?_)
    rw [map_mul]
    exact congrArg₂ (· * ·) (congrArg Units.val (map_pow (Units.map (N (c.1 ⊓ c'.1))) _ n)) e2.symm
  rw [← gs_res _ y (inf_le_left : c.1 ⊓ c'.1 ≤ c.1) hm, e3, gs_mul _ y _ hm, gs_res _ y inf_le_right hm,
    gs_unit _ y _ hm, map_pow, Units.val_pow_eq_pow_val]

def normSec (hN : NormRes q N) (hL : L.IsLB) {n : ℕ} (s : (lbPow L n).Sec) : (lbPow (normLB q N hL) n).Sec :=
  powSecOfGerm n
    (fun J => resG Y (show powChart (normLB q N hL) J ≤ (J PUnit.unit).1 from fun _ hy => mem_powChart.1 hy)
      (N (J PUnit.unit).1 ((J PUnit.unit).2.fn hL s)))
    fun y J J' hJ hJ' => by
      rw [gs_res _ y _ hJ, gs_res _ y _ hJ']
      exact gs_norm_compat hN hL s _ _ (mem_powChart.1 hJ) (mem_powChart.1 hJ')

theorem mem_nonzeroLocus_normSec (hN : NormRes q N)
    (hB : ∀ (V : Y.Opens) (a : Γ(X, q ⁻¹ᵁ V)) (y : Y), y ∈ V →
      (y ∈ Y.basicOpen (N V a) ↔ ∀ x : X, q x = y → x ∈ X.basicOpen a))
    (hL : L.IsLB) (hc : ∀ y : Y, ∃ c : (normLB q N hL).ι, y ∈ c.1) {n : ℕ} (s : (lbPow L n).Sec) (y : Y) :
    y ∈ nonzeroLocus (normSec hN hL s) ↔ ∀ x : X, q x = y → x ∈ nonzeroLocus s := by
  obtain ⟨c, hy⟩ := hc y
  have hJ : y ∈ powChart (normLB q N hL) fun _ => c := mem_powChart.2 hy
  rw [mem_nonzeroLocus_iff_powFn _ hJ]
  have e : gs (𝟙 Y) y _ (powFn (normSec hN hL s) fun _ => c) = gs (𝟙 Y) y c.1 (N c.1 (c.2.fn hL s)) :=
    gs_res _ y _ hJ _
  rw [e, isUnit_gs_iff (𝟙 Y) y c.1 hy, show (𝟙 Y) y = y from rfl, hB c.1 _ y hy]
  refine forall_congr' fun x => imp_congr_right fun hx => ?_
  exact c.2.mem_basicOpen_fn hL s (show q x ∈ c.1 from hx ▸ hy)

end Norm

theorem exists_chart_of_gen {q : X ⟶ Y} (hq : IsClosedMap q) {y : Y} {W : X.Opens} (hW : ∀ x : X, q x = y → x ∈ W)
    (e : Frame L W) : ∃ c : Σ V : Y.Opens, Frame L (q ⁻¹ᵁ V), y ∈ c.1 := by
  let V : Y.Opens := ⟨(q '' (W : Set X)ᶜ)ᶜ, (hq _ W.isOpen.isClosed_compl).isOpen_compl⟩
  have hle : q ⁻¹ᵁ V ≤ W := fun x hx => by_contra fun h => hx ⟨x, h, rfl⟩
  exact ⟨⟨V, e.res hle⟩, fun ⟨x, hx, h⟩ => hx (hW x h)⟩

end GlobalTheory.CompanionTheory.NormLB

section Main

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CompanionTheory.NormLB.exists_normLB : ∀ {X Y : Scheme.{0}} (q : X ⟶ Y), IsFinite q → ∀ (N : ∀ V : Y.Opens, Γ(X, q ⁻¹ᵁ V) →* Γ(Y, V)), (∀ (V W : Y.Opens) (h : W ≤ V) (a : Γ(X, q ⁻¹ᵁ V)), (Y.presheaf.map (homOfLE h).op).hom (N V a) = N W ((X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ V from fun _ hx => h hx)).op).hom a)) → (∀ (V : Y.Opens) (a : Γ(X, q ⁻¹ᵁ V)) (y : Y), y ∈ V → (y ∈ Y.basicOpen (N V a) ↔ ∀ x : X, q x = y → x ∈ X.basicOpen a)) → ∀ L : LB X, L.IsLB → (∀ y : Y, ∃ W : X.Opens, (∀ x : X, q x = y → x ∈ W) ∧ ∃ t : (L.pull W.ι).Gen, t.IsGen) → ∃ L' : LB Y, L'.IsLB ∧ ∀ (n : ℕ) (s : (lbPow L n).Sec), ∃ σ : (lbPow L' n).Sec, ∀ y : Y, y ∈ nonzeroLocus σ ↔ ∀ x : X, q x = y → x ∈ nonzeroLocus s := by
  intro X Y q hq N hN hB L hL hgen
  have hcl : IsClosedMap q := q.isClosedMap
  have hc : ∀ y : Y, ∃ c : (normLB q N hL).ι, y ∈ c.1 := fun y => by
    obtain ⟨W, hW, t, ht⟩ := hgen y
    exact exists_chart_of_gen hcl hW (Frame.ofGen W t ht)
  exact ⟨normLB q N hL, isLB_normLB hN hL hc, fun n s => ⟨normSec hN hL s, mem_nonzeroLocus_normSec hN hB hL hc s⟩⟩

end Main
