import Development.EtaleCohomology.TateTwists.EtaleKummerClassSpecificationOfExistenceNaturali

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def ev_basic : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

def prim_loc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def sec_glue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

theorem res_neg_isZero (R : Type) [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) := by
  unfold res InjectiveResolution.cochainComplex
  exact HomologicalComplex.isZero_extend_X _ _ _ (by intro i h; change ((i : ℕ) : ℤ) = s at h; omega)

theorem units_map_comp {V U X : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (u : (Γ(X, ⊤))ˣ) :
    Units.map (g ≫ x).appTop.hom.toMonoidHom u =
      Units.map g.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom u) := by
  ext; simp; rfl

theorem isUnit_q_map {U X : Scheme.{0}} (x : U ⟶ X) (q : ℕ) (hq : IsUnit (q : Γ(X, ⊤))) :
    IsUnit (q : Γ(U, ⊤)) := by
  simpa using hq.map x.appTop.hom

theorem kum_unique (hev : ev_basic) (hpl : prim_loc) (hsg : sec_glue) (q : ℕ) [NeZero q] (X : Scheme.{0})
    (u : (Γ(X, ⊤))ˣ) (hq : IsUnit (q : Γ(X, ⊤)))
    (γ γ' : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1)
    (h1 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0)
    (h2 : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h1' : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ'.1 1 0 (by simp) U x = 0)
    (h2' : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ'.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) : γ = γ' := by
  apply Cocycle.ext
  apply (hev (ZMod q)).2.2.1
  intro p s h U x
  match p, s, h with
  | 0, s, h =>
    obtain rfl : s = 1 := by omega
    revert x
    show ∀ x : U ⟶ X, _
    intro x
    apply (hsg (ZMod q) _ U).1
    obtain ⟨S, hS, hroot⟩ := (hpl q U).2.2.2 (isUnit_q_map x q hq) (Units.map x.appTop.hom.toMonoidHom u)
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨v, hv⟩ := hroot V g hg
    have hv' : v ^ q = Units.map (g ≫ x).appTop.hom.toMonoidHom u := by rw [units_map_comp]; exact hv
    exact ((hev (ZMod q)).2.1 γ.1 0 1 h V U g x).trans ((h2 V (g ≫ x) v hv').trans
      ((h2' V (g ≫ x) v hv').symm.trans ((hev (ZMod q)).2.1 γ'.1 0 1 h V U g x).symm))
  | 1, s, h =>
    obtain rfl : s = 0 := by omega
    exact (h1 U x).trans (h1' U x).symm
  | p + 2, s, h =>
    have hz := res_neg_isZero (ZMod q) (tw q 1) s (by omega)
    have hv : γ.1.v (-((p + 2 : ℕ) : ℤ)) s h = γ'.1.v (-((p + 2 : ℕ) : ℤ)) s h := hz.eq_of_tgt _ _
    unfold ev
    rw [hv]

theorem kum_nat_of (he : kum_exists) (hev : ev_basic) (hpl : prim_loc) (hsg : sec_glue) : kum_nat := by
  intro q _ Y X f u hq
  obtain ⟨γ, hc, h1, h2⟩ := kum_spec_of_exists he q X u hq
  have hqY := isUnit_q_map f q hq
  obtain ⟨γ', hc', h1', h2'⟩ := kum_spec_of_exists he q Y (Units.map f.appTop.hom.toMonoidHom u) hqY
  rw [← hc, ← hc']
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (sch.map f))) γ (zero_add 1)) = _
  congr 1
  refine kum_unique hev hpl hsg q Y _ hqY _ γ' ?_ ?_ h1' h2'
  · intro U x
    exact ((hev (ZMod q)).2.2.2.1 (sch.map f) γ.1 1 0 (by simp) U x).trans (h1 U (x ≫ f))
  · intro U x v hv
    exact ((hev (ZMod q)).2.2.2.1 (sch.map f) γ.1 0 1 (by simp) U x).trans
      (h2 U (x ≫ f) v (by rw [hv, units_map_comp]))

end LateralTheory.EtaleFoundations
