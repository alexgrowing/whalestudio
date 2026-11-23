import Development.EtaleCohomology.TateTwists.ExistsEtaleKummerChernClassCochainOfDegreeValues

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.V2

def PrimLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def KumTEx : Prop := ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)

def SecGlue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, h⟩ := hP
  obtain ⟨T, hT, h'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨h V g hg.1, h' V g hg.2⟩⟩

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, h'⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (h' V g hg)⟩

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  simp only [Sec.res, op_comp, Functor.map_comp]; rfl

theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sec.res (𝟙 U) a = a := by
  simp [Sec.res]

theorem umap_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) = Units.map (k ≫ g).appTop.hom.toMonoidHom u := by
  ext; simp; rfl

theorem umap_id {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) : Units.map (Scheme.Hom.appTop (𝟙 U)).hom.toMonoidHom u = u := by
  ext; simp

theorem unit_res {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (h : IsUnit (q : Γ(U, ⊤))) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using h.map g.appTop.hom

theorem sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  have := ConcreteCategory.congr_hom ((E.map (SimplexCategory.subinterval j l h).op).naturality g.op) x
  simpa using this

theorem glMat_res {V U : Scheme.{0}} (g : V ⟶ U) (y : Sx (ofCat (glCat 1)) 1 U) :
    glMat (((ofCat (glCat 1)).obj (op (SimplexCategory.mk 1))).map g.op y) = Matrix.GeneralLinearGroup.map g.appTop.hom (glMat y) := rfl

theorem det_gmap {V U : Scheme.{0}} (g : V ⟶ U) (m : GL (Fin 1) Γ(U, ⊤)) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map g.appTop.hom m) = Units.map g.appTop.hom.toMonoidHom (Matrix.GeneralLinearGroup.det m) := by
  ext
  simp [Matrix.GeneralLinearGroup.map]

theorem lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = Units.map g.appTop.hom.toMonoidHom (lineUnit L x) := by
  unfold lineUnit Sx.res
  have := ConcreteCategory.congr_hom ((L.app (op (SimplexCategory.mk 1))).naturality g.op) x
  simp only [ConcreteCategory.comp_apply] at this
  rw [this, glMat_res, det_gmap]

noncomputable def fv (q : ℕ) (U : Scheme.{0}) (v w : (Γ(U, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 0) U :=
  kumT q U v + kumT q U w - kumT q U (v * w)

theorem kumT_pow (hK : KumTEx) (q : ℕ) [NeZero q] {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) :
    ∀ (a : ℕ) (v w : (Γ(U, ⊤))ˣ), (w : Γ(U, ⊤)) = ζ.1 ^ a * v → kumT q U w = kumT q U v + a • resGen 1 ζ := by
  intro a
  induction a with
  | zero => intro v w h; have : w = v := Units.ext (by simpa using h); subst this; simp
  | succ a ih =>
    intro v w h
    have hu : IsUnit (ζ.1 ^ (a + 1)) := by
      rw [show ζ.1 ^ (a + 1) = (w : Γ(U, ⊤)) * ((v⁻¹ : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) by rw [h, mul_assoc]; simp]
      exact (w * v⁻¹).isUnit
    have hz : IsUnit ζ.1 := (isUnit_pow_iff (Nat.succ_ne_zero a)).1 hu
    let m : (Γ(U, ⊤))ˣ := hz.unit ^ a * v
    have hm : kumT q U m = kumT q U v + a • resGen 1 ζ := ih v m (by simp [m])
    have hw : kumT q U w = kumT q U m + resGen 1 ζ := (hK q).2 U ζ m w (by rw [h]; simp [m, pow_succ']; ring)
    rw [hw, hm, succ_nsmul, add_assoc]

theorem res_fv (hK : KumTEx) (q : ℕ) [NeZero q] {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) (v w : (Γ(U, ⊤))ˣ) :
    Sec.res g (fv q U v w) = fv q V (Units.map g.appTop.hom.toMonoidHom v) (Units.map g.appTop.hom.toMonoidHom w) := by
  have e : ∀ a b c : Sec ((res _ (tw q 1)).X 0) U, Sec.res g (a + b - c) = Sec.res g a + Sec.res g b - Sec.res g c := by
    intro a b c; simp [Sec.res]
  unfold fv
  rw [e, (hK q).1 V U g v hq, (hK q).1 V U g w hq, (hK q).1 V U g (v * w) hq, map_mul]

theorem umap_root {q : ℕ} {W V : Scheme.{0}} (h : W ⟶ V) (ζ : Prim q Γ(V, ⊤)) (v v' : (Γ(V, ⊤))ˣ) (a : ℕ)
    (ha : h.appTop.hom ((v' * v⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) = h.appTop.hom ζ.1 ^ a) :
    ((Units.map h.appTop.hom.toMonoidHom v' : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) =
      (Prim.map h.appTop.hom ζ).1 ^ a * Units.map h.appTop.hom.toMonoidHom v := by
  have : (v' : Γ(V, ⊤)) = ((v' * v⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) * v := by simp
  show h.appTop.hom (v' : Γ(V, ⊤)) = h.appTop.hom ζ.1 ^ a * h.appTop.hom v
  rw [this, map_mul, ha]

theorem indepA (hP : PrimLoc) (hK : KumTEx) (hG : SecGlue) (q : ℕ) [NeZero q] {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤))
    (hq : IsUnit (q : Γ(V, ⊤))) (v v' w w' : (Γ(V, ⊤))ˣ) (hv : v ^ q = v' ^ q) (hw : w ^ q = w' ^ q) :
    fv q V v w = fv q V v' w' := by
  have hx : (((v' * v⁻¹ : (Γ(V, ⊤))ˣ)) : Γ(V, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, ← hv, inv_pow, mul_inv_cancel]; rfl
  have hy : (((w' * w⁻¹ : (Γ(V, ⊤))ˣ)) : Γ(V, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, ← hw, inv_pow, mul_inv_cancel]; rfl
  apply (hG _ _ V).1
  refine loc_mono (loc_and ((hP q V).2.2.1 ζ _ hx) ((hP q V).2.2.1 ζ _ hy)) ?_
  rintro W h ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rw [res_fv hK q h hq, res_fv hK q h hq]
  have h1 := umap_root h ζ v v' a ha
  have h2 := umap_root h ζ w w' b hb
  have h3 : ((Units.map h.appTop.hom.toMonoidHom v' * Units.map h.appTop.hom.toMonoidHom w' : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) =
      (Prim.map h.appTop.hom ζ).1 ^ (a + b) * ((Units.map h.appTop.hom.toMonoidHom v * Units.map h.appTop.hom.toMonoidHom w : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) := by
    rw [Units.val_mul, h1, h2, Units.val_mul, pow_add]; ring
  unfold fv
  rw [kumT_pow hK q _ a _ _ h1, kumT_pow hK q _ b _ _ h2, kumT_pow hK q _ (a + b) _ _ h3, add_nsmul]
  abel

theorem indepB (hP : PrimLoc) (hK : KumTEx) (hG : SecGlue) (q : ℕ) [NeZero q] {U : Scheme.{0}}
    (hq : IsUnit (q : Γ(U, ⊤))) (v v' w w' : (Γ(U, ⊤))ˣ) (hv : v ^ q = v' ^ q) (hw : w ^ q = w' ^ q) :
    fv q U v w = fv q U v' w' := by
  apply (hG _ _ U).1
  refine loc_mono ((hP q U).1 hq) ?_
  rintro V g ⟨ζ⟩
  rw [res_fv hK q g hq, res_fv hK q g hq]
  exact indepA hP hK hG q ζ (unit_res g hq) _ _ _ _ (by rw [← map_pow, ← map_pow, hv]) (by rw [← map_pow, ← map_pow, hw])

def Good (q : ℕ) (U : Scheme.{0}) (u1 u2 : (Γ(U, ⊤))ˣ) (a : Sec ((res _ (tw q 1)).X 0) U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom u1 →
    w ^ q = Units.map g.appTop.hom.toMonoidHom u2 → Sec.res g a = fv q V v w

theorem good_exists (hP : PrimLoc) (hK : KumTEx) (hG : SecGlue) (q : ℕ) [NeZero q] {U : Scheme.{0}}
    (hq : IsUnit (q : Γ(U, ⊤))) (u1 u2 : (Γ(U, ⊤))ˣ) : ∃ a, Good q U u1 u2 a := by
  obtain ⟨S, hS, hS'⟩ := loc_and ((hP q U).2.2.2 hq u1) ((hP q U).2.2.2 hq u2)
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec ((res _ (tw q 1)).X 0) V :=
    fun V g hg => fv q V (hS' V g hg).1.choose (hS' V g hg).2.choose
  obtain ⟨a, ha⟩ := (hG _ _ U).2 S hS s (by
    intro V W g k hg
    simp only [s]
    rw [res_fv hK q k (unit_res g hq)]
    apply indepB hP hK hG q (unit_res (k ≫ g) hq)
    · rw [← map_pow, (hS' V g hg).1.choose_spec, umap_comp, (hS' W (k ≫ g) (S.downward_closed hg k)).1.choose_spec]
    · rw [← map_pow, (hS' V g hg).2.choose_spec, umap_comp, (hS' W (k ≫ g) (S.downward_closed hg k)).2.choose_spec])
  refine ⟨a, fun V g v w hv hw => ?_⟩
  apply (hG _ _ V).1
  refine ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W k hk => ?_⟩
  show Sec.res k (Sec.res g a) = Sec.res k (fv q V v w)
  rw [res_comp, ha W (k ≫ g) hk, res_fv hK q k (unit_res g hq)]
  apply indepB hP hK hG q (unit_res (k ≫ g) hq)
  · rw [(hS' W (k ≫ g) hk).1.choose_spec, ← map_pow, hv, umap_comp]
  · rw [(hS' W (k ≫ g) hk).2.choose_spec, ← map_pow, hw, umap_comp]

theorem good_unique (hP : PrimLoc) (hG : SecGlue) (q : ℕ) [NeZero q] {U : Scheme.{0}}
    (hq : IsUnit (q : Γ(U, ⊤))) {u1 u2 : (Γ(U, ⊤))ˣ} {a b : Sec ((res _ (tw q 1)).X 0) U}
    (ha : Good q U u1 u2 a) (hb : Good q U u1 u2 b) : a = b := by
  apply (hG _ _ U).1
  refine loc_mono (loc_and ((hP q U).2.2.2 hq u1) ((hP q U).2.2.2 hq u2)) ?_
  rintro V g ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
  rw [ha V g v w hv hw, hb V g v w hv hw]

theorem good_res (q : ℕ) {V U : Scheme.{0}} (g : V ⟶ U) {u1 u2 : (Γ(U, ⊤))ˣ} {a : Sec ((res _ (tw q 1)).X 0) U}
    (ha : Good q U u1 u2 a) :
    Good q V (Units.map g.appTop.hom.toMonoidHom u1) (Units.map g.appTop.hom.toMonoidHom u2) (Sec.res g a) := by
  intro W k v w hv hw
  rw [res_comp]
  exact ha W (k ≫ g) v w (by rw [hv, umap_comp]) (by rw [hw, umap_comp])

end LateralTheory.EtaleFoundations.V2

open LateralTheory.EtaleFoundations.V2 in
theorem LateralTheory.EtaleFoundations.exists_natural_etale_kummer_degree_two_value_of_roots_kummer_gluing (hP : PrimLoc) (hK : KumTEx) (hG : SecGlue) : LateralTheory.EtaleFoundations.ExistsNaturalEtaleKummerChernClassDegreeTwoValue := by
  intro q _ E L hi
  have hq : ∀ (U : Scheme.{0}) (x : Sx E 2 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hi U ⟨x.sub 0 0 (by omega)⟩
  refine ⟨fun U x => pick (Good q U (lineUnit L (x.sub 0 1 (by omega))) (lineUnit L (x.sub 1 1 (by omega)))), ?_, ?_⟩
  · intro V U g x
    have e1 : lineUnit L ((x.res g).sub 0 1 (by omega)) = Units.map g.appTop.hom.toMonoidHom (lineUnit L (x.sub 0 1 (by omega))) := by
      rw [sub_res, lineUnit_res]
    have e2 : lineUnit L ((x.res g).sub 1 1 (by omega)) = Units.map g.appTop.hom.toMonoidHom (lineUnit L (x.sub 1 1 (by omega))) := by
      rw [sub_res, lineUnit_res]
    have h1 := good_res q g (pick_spec (good_exists hP hK hG q (hq U x) (lineUnit L (x.sub 0 1 (by omega))) (lineUnit L (x.sub 1 1 (by omega)))))
    rw [← e1, ← e2] at h1
    exact good_unique hP hG q (hq V (x.res g)) h1 (pick_spec (good_exists hP hK hG q (hq V (x.res g)) _ _))
  · intro U x v w hv hw
    have := pick_spec (good_exists hP hK hG q (hq U x) (lineUnit L (x.sub 0 1 (by omega))) (lineUnit L (x.sub 1 1 (by omega))))
      U (𝟙 U) v w (by rw [umap_id]; exact hv) (by rw [umap_id]; exact hw)
    rwa [res_id] at this
