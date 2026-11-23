import Development.EtaleCohomology.TateTwists.KumAddPf

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def uniq_prim_loc : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def sections_unique_of_local_agreement : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

def uniq_ev_basic : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

theorem sec_neg_eq (q : ℕ) [NeZero q] (s : ℤ) (hs : s < 0) (U : Scheme.{0})
    (a b : Sec ((res _ (tw q 1)).X s) U) : a = b := by
  have h0 : IsZero ((res _ (tw q 1)).X s) := by
    unfold res
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)
  have h1 : IsZero (((res _ (tw q 1)).X s).obj.obj (op U)) :=
    ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)).map_isZero h0)
  have : Subsingleton (((res _ (tw q 1)).X s).obj.obj (op U)) :=
    (ModuleCat.isZero_iff_subsingleton).mp h1
  exact Subsingleton.elim a b

theorem root_res (q : ℕ) (X U V : Scheme.{0}) (u : (Γ(X, ⊤))ˣ) (x : U ⟶ X) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ)
    (hv : v ^ q = Units.map g.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom u)) :
    v ^ q = Units.map (Sx.res (E := sch.obj X) (p := 0) g x : V ⟶ X).appTop.hom.toMonoidHom u := by
  have e : (Sx.res (E := sch.obj X) (p := 0) g x : V ⟶ X) = g ≫ x := rfl
  rw [hv, e]; ext; simp
  rfl

theorem kum_uniq_of (hl : uniq_prim_loc) (hg : sections_unique_of_local_agreement) (hb : uniq_ev_basic) : kum_uniq := by
  intro q _ X u hq γ γ' h h'
  have key : γ = γ' := by
    apply Subtype.ext
    apply (hb (ZMod q)).2.2.1
    intro p s hs U x
    rcases p with _ | _ | p
    · have hs' : s = 1 := by omega
      subst hs'
      have hqU : IsUnit ((q : ℕ) : Γ(U, ⊤)) := by
        have := hq.map x.appTop.hom
        simpa using this
      obtain ⟨S, hS, hP⟩ := (hl q U).2.2.2 hqU (Units.map x.appTop.hom.toMonoidHom u)
      apply (hg (ZMod q) _ U).1
      refine ⟨S, hS, fun V g hgS => ?_⟩
      obtain ⟨v, hv⟩ := hP V g hgS
      rw [(hb (ZMod q)).2.1, (hb (ZMod q)).2.1]
      have hv' := root_res q X U V u x g v hv
      rw [h.2 V _ v hv', h'.2 V _ v hv']
    · have hs' : s = 0 := by omega
      subst hs'
      rw [h.1 U x, h'.1 U x]
    · exact sec_neg_eq q s (by omega) U _ _
  rw [key]

end LateralTheory.EtaleFoundations
