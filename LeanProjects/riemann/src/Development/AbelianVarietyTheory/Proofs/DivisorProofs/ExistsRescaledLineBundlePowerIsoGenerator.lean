import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section
namespace GlobalTheory.RigNorm
open Opposite TopologicalSpace

theorem glue_units {T : Scheme.{0}} {I : Type} (W : I → T.Opens) (hW : ∀ x : T, ∃ i, x ∈ W i)
    (u : ∀ i, Γ(T, W i)ˣ)
    (hu : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (u i) = res (inf_le_right : W i ⊓ W j ≤ W j) (u j)) :
    ∃ v : Γ(T, ⊤)ˣ, ∀ i, res (le_top : W i ≤ ⊤) v = u i := by
  have hc : (⊤ : T.Opens) ≤ iSup W := fun x _ => by
    obtain ⟨i, hi⟩ := hW x
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  have glue : ∀ sf : ∀ i, Γ(T, W i), (∀ i j, (T.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op).hom (sf i) = (T.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op).hom (sf j)) →
      ∃ s : Γ(T, ⊤), ∀ i, (T.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op).hom s = sf i := by
    intro sf hsf
    obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' T.sheaf W ⊤ (fun i => homOfLE le_top) hc sf hsf
    exact ⟨s, hs⟩
  obtain ⟨s, hs⟩ := glue (fun i => (u i).val) (fun i j => congrArg Units.val (hu i j))
  obtain ⟨s', hs'⟩ := glue (fun i => ((u i)⁻¹).val) (fun i j => by
    have := congrArg (fun x => (x⁻¹).val) (hu i j)
    simpa [res, map_inv] using this)
  have h1 : s * s' = 1 := by
    apply TopCat.Sheaf.eq_of_locally_eq' T.sheaf W ⊤ (fun i => homOfLE le_top) hc
    intro i
    have := hs i; have := hs' i
    change (T.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op).hom (s * s') = (T.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op).hom 1
    rw [map_mul, map_one, hs i, hs' i, Units.mul_inv]
  refine ⟨⟨s, s', h1, by rw [mul_comm, h1]⟩, fun i => Units.ext ?_⟩
  exact hs i

theorem val_res {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    (res h u).val = (X.presheaf.map (homOfLE h).op).hom u.val := rfl

theorem val_pullU {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (u : Γ(X, U)ˣ) :
    (pullU f U u).val = (f.app U).hom u.val := rfl

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (u : Γ(X, U)ˣ) :
    res h₁ (res h₂ u) = res (h₁.trans h₂) u := by
  apply Units.ext
  simp only [val_res]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem appLE_res {X Y : Scheme.{0}} (h : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (e : V ≤ h ⁻¹ᵁ U)
    (hU : U ≤ U') (x : Γ(Y, U')) :
    (h.appLE U V e).hom ((Y.presheaf.map (homOfLE hU).op).hom x) =
      (h.appLE U' V (e.trans fun _ hy => hU hy)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem res_appLE {X Y : Scheme.{0}} (h : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (e : V ≤ h ⁻¹ᵁ U)
    (hV : V' ≤ V) (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE hV).op).hom ((h.appLE U V e).hom x) = (h.appLE U V' (hV.trans e)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_app {X Y Z : Scheme.{0}} (h : X ⟶ Y) (k : Y ⟶ Z) {U : Z.Opens} {W : X.Opens}
    (e : W ≤ h ⁻¹ᵁ (k ⁻¹ᵁ U)) (x : Γ(Z, U)) :
    (h.appLE (k ⁻¹ᵁ U) W e).hom ((k.app U).hom x) = ((h ≫ k).appLE U W (e.trans fun _ hy => hy)).hom x := by
  rw [Scheme.Hom.comp_appLE]; rfl

theorem appLE_congr' {X Y : Scheme.{0}} {h h' : X ⟶ Y} (H : h = h') {U : Y.Opens} {V : X.Opens}
    (e : V ≤ h ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (h.appLE U V e).hom x = (h'.appLE U V (H ▸ e)).hom x := by
  subst H; rfl

theorem id_appLE' {X : Scheme.{0}} {U V : X.Opens} (e : V ≤ (𝟙 X) ⁻¹ᵁ U) (x : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U V e).hom x = (X.presheaf.map (homOfLE e).op).hom x := by
  rfl

theorem alg {R : Type*} [CommRing R] (Bp Bq Ap Aq ap aq cM cL : R) (k : ℕ) (hB : Bp = cM * Bq)
    (hA : Ap = cL * Aq) (ha : ap * cL ^ k = cM ^ k * aq) : Bp ^ k * (aq * Aq ^ k) = Bq ^ k * (ap * Ap ^ k) := by
  subst hB hA; linear_combination (-(Bq ^ k * Aq ^ k)) * ha

theorem mul_inv_mul_cancel_comm {G : Type*} [CommGroup G] (m l a l' : G) (h : l = l') : m * l⁻¹ * a * l' = m * a := by
  subst h; rw [mul_right_comm, inv_mul_cancel_right]

theorem map_map' {X : Scheme.{0}} {U V W : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom x) =
      (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem pre_mono {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} (h : U ≤ U') : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U' :=
  fun _ hx => h hx

theorem pre_inf {X Y : Scheme.{0}} (f : X ⟶ Y) (U U' : Y.Opens) : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ U' ≤ f ⁻¹ᵁ (U ⊓ U') :=
  fun _ hx => hx

theorem pull_inf_le {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (i j : L.ι) :
    LB.wchart L (fun _ : PUnit => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : PUnit => φ) (fun _ => j) ≤ φ ⁻¹ᵁ (L.U i ⊓ L.U j) :=
  fun _ hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩

theorem pow_inf_le {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (i j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => φ) i ⊓ LB.wchart L (fun _ : Fin 1 => φ) j ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0)) :=
  fun _ hy => ⟨Set.mem_iInter.1 hy.1 0, Set.mem_iInter.1 hy.2 0⟩

theorem pull_g_val {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (i j : PUnit → L.ι) :
    ((L.pull φ).g i j).val = (Y.presheaf.map (homOfLE (fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit,
      Set.mem_iInter.1 hy.2 PUnit.unit⟩ : (L.pull φ).U i ⊓ (L.pull φ).U j ≤
        φ ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)))).op).hom
      ((φ.app _).hom (L.g (i PUnit.unit) (j PUnit.unit)).val) :=
by
  show (∏ m : PUnit, (res (le_inf (inf_le_left.trans (LB.wchart_le L _ i m)) (inf_le_right.trans (LB.wchart_le L _ j m)))
    (pullU φ (L.U (i m) ⊓ L.U (j m)) (L.g (i m) (j m)))) ^ (1 : ℤ)).val = _
  rw [Fintype.prod_unique, zpow_one]
  rfl

theorem powPull_g_val {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (i j : Fin 1 → L.ι) :
    ((powPull L φ (k : ℤ)).g i j).val = ((Y.presheaf.map (homOfLE (fun y hy => ⟨Set.mem_iInter.1 hy.1 0,
      Set.mem_iInter.1 hy.2 0⟩ : (powPull L φ (k : ℤ)).U i ⊓ (powPull L φ (k : ℤ)).U j ≤
        φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0)))).op).hom ((φ.app _).hom (L.g (i 0) (j 0)).val)) ^ k :=
by
  show (∏ m : Fin 1, (res (le_inf (inf_le_left.trans (LB.wchart_le L _ i m)) (inf_le_right.trans (LB.wchart_le L _ j m)))
    (pullU φ (L.U (i m) ⊓ L.U (j m)) (L.g (i m) (j m)))) ^ (k : ℤ)).val = _
  rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
  rfl

theorem pull_rel {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (e : LB.Gen (L.pull φ)) (he : e.IsGen)
    (s : ∀ i : L.ι, Γ(Y, LB.wchart L (fun _ : PUnit => φ) (fun _ => i))ˣ) (hs : s = fun i => e.s (fun _ => i))
    (i j : L.ι) :
    (Y.presheaf.map (homOfLE (inf_le_left : LB.wchart L (fun _ : PUnit => φ) (fun _ => i) ⊓
      LB.wchart L (fun _ : PUnit => φ) (fun _ => j) ≤ LB.wchart L (fun _ : PUnit => φ) (fun _ => i))).op).hom (s i).val =
    (Y.presheaf.map (homOfLE (pull_inf_le L φ i j)).op).hom ((φ.app _).hom (L.g i j).val) *
    (Y.presheaf.map (homOfLE (inf_le_right : LB.wchart L (fun _ : PUnit => φ) (fun _ => i) ⊓
      LB.wchart L (fun _ : PUnit => φ) (fun _ => j) ≤ LB.wchart L (fun _ : PUnit => φ) (fun _ => j))).op).hom (s j).val := by
  subst hs
  exact (congrArg Units.val (he (fun _ => i) (fun _ => j))).trans
    (congrArg (· * _) (pull_g_val L φ (fun _ => i) (fun _ => j)))

theorem div_rel {X Y₁ Y₂ : Scheme.{0}} (L : LB Y₁) (M : LB Y₂) (f : X ⟶ Y₁) (g : X ⟶ Y₂) (k : ℕ)
    (α₀ : LB.Gen (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ)))) (hα : α₀.IsGen)
    (s : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      Γ(X, LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2)ˣ)
    (hs : s = fun p => α₀.s p) (p q : (Fin 1 → M.ι) × (Fin 1 → L.ι)) :
    (X.presheaf.map (homOfLE (inf_le_left : (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) ⊓
      (LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2) ≤
        LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2)).op).hom (s p).val *
    ((X.presheaf.map (homOfLE ((inf_le_inf inf_le_right inf_le_right).trans (pow_inf_le L f p.2 q.2) :
      (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) ⊓
      (LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2) ≤
        f ⁻¹ᵁ (L.U (p.2 0) ⊓ L.U (q.2 0)))).op).hom ((f.app _).hom (L.g (p.2 0) (q.2 0)).val)) ^ k =
    ((X.presheaf.map (homOfLE ((inf_le_inf inf_le_left inf_le_left).trans (pow_inf_le M g p.1 q.1) :
      (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) ⊓
      (LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2) ≤
        g ⁻¹ᵁ (M.U (p.1 0) ⊓ M.U (q.1 0)))).op).hom ((g.app _).hom (M.g (p.1 0) (q.1 0)).val)) ^ k *
    (X.presheaf.map (homOfLE (inf_le_right : (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) ⊓
      (LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2) ≤
        LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2)).op).hom (s q).val := by
  subst hs
  have hhL : (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U q ≤ (powPull L f (k : ℤ)).U p.2 ⊓ (powPull L f (k : ℤ)).U q.2 :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have hhM : (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U q ≤ (powPull M g (k : ℤ)).U p.1 ⊓ (powPull M g (k : ℤ)).U q.1 :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have h2 : res (inf_le_left : (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U q ≤ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p) (α₀.s p) *
        res hhL ((powPull L f (k : ℤ)).g p.2 q.2) =
      res hhM ((powPull M g (k : ℤ)).g p.1 q.1) *
        res (inf_le_right : (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U q ≤ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U q) (α₀.s q) := by
    rw [hα p q]
    exact mul_inv_mul_cancel_comm _ _ _ _ rfl
  have eL := ((congrArg (X.presheaf.map (homOfLE hhL).op).hom (powPull_g_val L f k p.2 q.2)).trans
    (map_pow _ _ _)).trans (congrArg (· ^ k) (map_map' _ _ _))
  have eM := ((congrArg (X.presheaf.map (homOfLE hhM).op).hom (powPull_g_val M g k p.1 q.1)).trans
    (map_pow _ _ _)).trans (congrArg (· ^ k) (map_map' _ _ _))
  have h3 := congrArg Units.val h2
  rw [Units.val_mul, Units.val_mul, val_res hhL, val_res hhM, eL, eM] at h3
  exact h3

theorem exists_rescaled_gen : ∀ {T X Z₀ Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (g : X ⟶ Z₂) (eL : Z₀ ⟶ Z₁) (eM : Z₀ ⟶ Z₂) (t : T ⟶ Z₀) (z : T ⟶ X) (π : X ⟶ T) (k : ℕ) (eA : LB.Gen (L.pull eL)) (eB : LB.Gen (M.pull eM)) (α₀ : LB.Gen (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ)))), L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → α₀.IsGen → z ≫ π = 𝟙 T → z ≫ f = t ≫ eL → z ≫ g = t ≫ eM → ∃ α : LB.Gen (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))), α.IsGen ∧ ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), (z.appLE ((LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (inf_le_left.trans inf_le_left)).hom (α.s p).val * ((t.appLE (LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0)) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k = ((t.appLE (LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k := by
  intro T X Z₀ Z₁ Z₂ L M f g eL eM t z π k eA eB α₀ hL hM hA hB hα hzπ hzf hzg
  obtain ⟨sA, hsA⟩ : ∃ s : ∀ i : L.ι, Γ(Z₀, LB.wchart L (fun _ : PUnit => eL) (fun _ => i))ˣ, s = fun i => eA.s (fun _ => i) := ⟨_, rfl⟩
  obtain ⟨sB, hsB⟩ : ∃ s : ∀ i : M.ι, Γ(Z₀, LB.wchart M (fun _ : PUnit => eM) (fun _ => i))ˣ, s = fun i => eB.s (fun _ => i) := ⟨_, rfl⟩
  obtain ⟨sα, hsα⟩ : ∃ s : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), Γ(X, (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2))ˣ, s = fun p => α₀.s p :=
    ⟨_, rfl⟩
  let Wo : (Fin 1 → M.ι) × (Fin 1 → L.ι) → T.Opens := fun p =>
    z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)
  have hDU : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p = (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) := fun _ => rfl
  let a : ∀ p, Γ(T, Wo p)ˣ := fun p =>
    Units.map (z.appLE (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) (Wo p) ((inf_le_left.trans inf_le_left).trans (pre_mono z (hDU p).le))).hom.toMonoidHom (sα p)
  let A : ∀ p, Γ(T, Wo p)ˣ := fun p =>
    Units.map (t.appLE (LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0)) (Wo p) (inf_le_left.trans inf_le_right)).hom.toMonoidHom (sA (p.2 0))
  let B : ∀ p, Γ(T, Wo p)ˣ := fun p =>
    Units.map (t.appLE (LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (Wo p) inf_le_right).hom.toMonoidHom (sB (p.1 0))
  let u : ∀ p, Γ(T, Wo p)ˣ := fun p => B p ^ k * (a p * A p ^ k)⁻¹
  have hcov : ∀ x : T, ∃ p, x ∈ Wo p := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show eL (t x) ∈ ⨆ i, L.U i by rw [hL.cover]; trivial)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (show eM (t x) ∈ ⨆ j, M.U j by rw [hM.cover]; trivial)
    have hf : f (z x) = eL (t x) := by rw [← Scheme.Hom.comp_apply, hzf, Scheme.Hom.comp_apply]
    have hg : g (z x) = eM (t x) := by rw [← Scheme.Hom.comp_apply, hzg, Scheme.Hom.comp_apply]
    refine ⟨(fun _ => j, fun _ => i), ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩⟩
    · exact Set.mem_iInter.2 fun _ => show g (z x) ∈ M.U j by rw [hg]; exact hj
    · exact Set.mem_iInter.2 fun _ => show f (z x) ∈ L.U i by rw [hf]; exact hi
    · exact Set.mem_iInter.2 fun _ => hi
    · exact Set.mem_iInter.2 fun _ => hj
  have hcomp : ∀ p q, res (inf_le_left : Wo p ⊓ Wo q ≤ Wo p) (u p) =
      res (inf_le_right : Wo p ⊓ Wo q ≤ Wo q) (u q) := by
    intro p q
    have eV : Wo p ⊓ Wo q ≤ z ⁻¹ᵁ ((LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) ⊓ (LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2)) := (inf_le_inf ((inf_le_left.trans inf_le_left).trans (pre_mono z (hDU p).le))
      ((inf_le_left.trans inf_le_left).trans (pre_mono z (hDU q).le))).trans (pre_inf z _ _)
    have eVA : Wo p ⊓ Wo q ≤ t ⁻¹ᵁ (LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ LB.wchart L (fun _ : PUnit => eL) (fun _ => q.2 0)) := (inf_le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_right)).trans (pre_inf t _ _)
    have eVB : Wo p ⊓ Wo q ≤ t ⁻¹ᵁ (LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0) ⊓ LB.wchart M (fun _ : PUnit => eM) (fun _ => q.1 0)) := (inf_le_inf inf_le_right inf_le_right).trans (pre_inf t _ _)
    have ra := congrArg (z.appLE _ _ eV).hom (div_rel L M f g k α₀ hα sα hsα p q)
    have rA := congrArg (t.appLE _ _ eVA).hom (pull_rel L eL eA hA sA hsA (p.2 0) (q.2 0))
    have rB := congrArg (t.appLE _ _ eVB).hom (pull_rel M eM eB hB sB hsB (p.1 0) (q.1 0))
    simp only [map_mul, map_pow, appLE_res, appLE_app, appLE_congr' hzf, appLE_congr' hzg] at ra rA rB
    simp only [u, map_mul, map_pow, map_inv]
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, val_res, a, A, B, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, res_appLE]
    exact alg _ _ _ _ _ _ _ _ k rB rA ra
  obtain ⟨v, hv⟩ := glue_units Wo hcov u hcomp
  refine ⟨⟨fun p => res (show (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ≤ π ⁻¹ᵁ ⊤ from fun _ _ => trivial) (pullU π ⊤ v) * α₀.s p⟩, ?_, ?_⟩
  · intro p q
    dsimp only
    simp only [map_mul, res_res, hα p q]
    exact mul_left_comm _ _ _
  · intro p
    have key : ((z ≫ π).appLE ⊤ (Wo p) (fun _ _ => trivial)).hom v.val = (u p).val := by
      have h1 := appLE_congr' hzπ (U := ⊤) (V := Wo p) (fun _ _ => trivial) v.val
      rw [id_appLE'] at h1
      exact h1.trans (congrArg Units.val (hv p))
    have hu := congrArg Units.val (inv_mul_cancel_right (B p ^ k) (a p * A p ^ k))
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hu
    dsimp only
    simp only [Units.val_mul, val_res, val_pullU, map_mul, appLE_res, appLE_app]
    rw [key, _root_.mul_assoc]
    subst hsA hsB hsα
    exact hu

end GlobalTheory.RigNorm
