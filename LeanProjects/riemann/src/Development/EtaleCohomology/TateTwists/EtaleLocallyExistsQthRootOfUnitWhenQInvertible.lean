import Development.EtaleCohomology.TateTwists.FirstChernSpecOfRepresentative

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.FirstChernUniqueness

lemma sec_sub {q : ℕ} {F : Shv (ZMod q)} (hF : IsZero F) (U : Scheme.{0}) (a b : Sec F U) : a = b := by
  have h1 : IsZero F.obj := (sheafToPresheaf _ _).map_isZero hF
  have h2 : IsZero (F.obj.obj (op U)) := h1.obj (op U)
  have := (ModuleCat.isZero_iff_subsingleton.mp h2)
  exact Subsingleton.elim _ _

lemma res_zero_neg (q : ℕ) (s : ℤ) (hs : s < 0) : IsZero ((res _ (tw q 1)).X s) := by
  unfold res
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)

lemma sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  exact (NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x)

def ev_basic : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

def sec_glue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

lemma loc_imp {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

def EtaleLocallyExistsQthRootOfUnitWhenQInvertible : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
  Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u

lemma glMat_res {V U : Scheme.{0}} (g : V ⟶ U) (y : Sx (ofCat (glCat 1)) 1 U) :
    (glMat (y.res g) : Matrix (Fin 1) (Fin 1) Γ(V, ⊤)) = g.appTop.hom.mapMatrix (glMat y : Matrix (Fin 1) (Fin 1) Γ(U, ⊤)) := by
  rfl

lemma lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = Units.map g.appTop.hom.toMonoidHom (lineUnit L x) := by
  unfold lineUnit
  have hn : (L.app (op (SimplexCategory.mk 1))).app (op V) (x.res g) =
      Sx.res g ((L.app (op (SimplexCategory.mk 1))).app (op U) x) := by
    unfold Sx.res; rw [NatTrans.naturality_apply]
  rw [hn]
  ext
  simp only [Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [glMat_res, RingHom.map_det]

lemma root_line (hr : EtaleLocallyExistsQthRootOfUnitWhenQInvertible) (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hi : Inv q E)
    (U : Scheme.{0}) (x : Sx E 1 U) : Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = lineUnit L (x.res g) := by
  refine loc_imp (hr q U (hi U ⟨x.sub 0 0 (by omega)⟩) (lineUnit L x)) fun V g hv => ?_
  obtain ⟨v, hv⟩ := hv
  exact ⟨v, by rw [lineUnit_res]; exact hv⟩

lemma loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hSP⟩ := hP
  obtain ⟨T, hT, hTQ⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hSP V g hg.1, hTQ V g hg.2⟩⟩

end LateralTheory.EtaleFoundations.FirstChernUniqueness
