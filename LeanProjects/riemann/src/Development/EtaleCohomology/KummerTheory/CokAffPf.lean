import Development.EtaleCohomology.KummerTheory.LocCokPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

theorem bcMap_comp' {X : Scheme.{0}} {R A B C : CommRingCat.{0}} (p : X ⟶ Spec R) (f : R ⟶ A) (g : R ⟶ B) (g' : R ⟶ C)
    (h : A ⟶ B) (h' : B ⟶ C) (e : f ≫ h = g) (e' : g ≫ h' = g') :
    bcMap p g g' h' e' ≫ bcMap p f g h e = bcMap p f g' (h ≫ h') (by rw [← Category.assoc, e, e']) := by
  apply pullback.hom_ext <;>
    simp only [bcMap, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, Category.comp_id, Spec.map_comp]

theorem bcMap_eq {X : Scheme.{0}} {R A B : CommRingCat.{0}} (p : X ⟶ Spec R) (f : R ⟶ A) (g : R ⟶ B)
    (h h' : A ⟶ B) (e : f ≫ h = g) (hh : h = h') : bcMap p f g h e = bcMap p f g h' (hh ▸ e) := by
  subst hh; rfl

theorem CokAff_of (hS : StrictHenselization) (hC : Cont) (hL : LhNat) : CokAff := by
  classical
  intro h2 h6 hb1 q _ X R p _ _ hq i r c M N n hiso B s b x
  obtain ⟨J, _, _, D, cc, hcc, u, hSH, hu⟩ := hS B b
  have hun : ∀ {j k : J} (f : j ⟶ k), u.app j ≫ D.map f = u.app k := by
    intro j k f
    have := u.naturality f
    simpa using this.symm
  let j0 : J := (IsFiltered.nonempty (C := J)).some
  let w : B ⟶ cc.pt := u.app j0 ≫ cc.ι.app j0
  have hw : ∀ j, u.app j ≫ cc.ι.app j = w := by
    intro j
    show _ = u.app j0 ≫ cc.ι.app j0
    rw [← cc.w (IsFiltered.leftToMax j j0), ← cc.w (IsFiltered.rightToMax j j0), ← Category.assoc,
      ← Category.assoc, hun, hun]
  let v : R ⟶ cc.pt := s ≫ w
  obtain ⟨y, hy⟩ := (hiso cc.pt v hSH).2 (pull _ (sch.map (bcMap p s v w rfl)) _ _ x)
  have hqc : IsUnit ((q : ℕ) : cc.pt) := by simpa using hq.map v.hom
  have hB := fun n' i' => (hb1 q D cc hcc n' i').1
  choose jj z hz using fun (a : Fin (M + 1)) (t : Fin (r a)) => hB _ _ (y a t) hqc
  obtain ⟨k0, hk0⟩ := IsFiltered.sup_objs_exists
    (Finset.univ.image (fun pr : (Σ a : Fin (M + 1), Fin (r a)) => jj pr.1 pr.2))
  have fk : ∀ a t, jj a t ⟶ k0 := fun a t => (hk0 (Finset.mem_image.2 ⟨⟨a, t⟩, Finset.mem_univ _, rfl⟩)).some
  let y0 : ∀ a : Fin (M + 1), Fin (r a) → Ht q (sch.obj (Spec (D.obj k0))) (n - ((a : ℕ) : ℤ)) 0 :=
    fun a t => pull _ (sch.map (Spec.map (D.map (fk a t)))) _ _ (z a t)
  have hy0 : ∀ a t, pull _ (sch.map (Spec.map (cc.ι.app k0))) _ _ (y0 a t) = y a t := by
    intro a t
    rw [← hz a t]
    simp only [y0]
    rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp, cc.w]
    rfl
  let g : Over.mk (Spec.map v) ⟶ Over.mk (Spec.map (s ≫ u.app k0)) :=
    Over.homMk (Spec.map (cc.ι.app k0)) (by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, Category.assoc, hw])
  have hrst : rst p g = bcMap p (s ≫ u.app k0) v (cc.ι.app k0) (by rw [Category.assoc, hw]) := rfl
  have h0 := hL h6 q p i r c M n g y0
  rw [hrst] at h0
  have hyy : (fun a t => pull _ (sch.map g.left) _ _ (y0 a t)) = y := by
    funext a t; exact hy0 a t
  rw [hyy] at h0
  let e := lh q p (Spec.map (s ≫ u.app k0)) i r c M n y0 -
    N • pull _ (sch.map (bcMap p s (s ≫ u.app k0) (u.app k0) rfl)) _ _ x
  have he : pull _ (sch.map (bcMap p (s ≫ u.app k0) v (cc.ι.app k0) (by rw [Category.assoc, hw]))) _ _ e = 0 := by
    simp only [e, map_sub, map_nsmul]
    erw [h0, hy, ← pull_comp, ← Functor.map_comp, bcMap_comp', bcMap_eq _ _ _ _ _ _ (hw k0)]
    exact sub_self _
  have hC2 := (hC h2 hb1 q p hq D cc hcc (fun j => s ≫ u.app j)
    (fun {j k} f => by simp only [Category.assoc, hun]) v (fun j => by simp only [v, Category.assoc, hw]) n i).2 k0 e he
  obtain ⟨k1, f1, hk1⟩ := hC2
  obtain ⟨het, 𝔮, h𝔮⟩ := hu k1
  refine ⟨D.obj k1, u.app k1, het, ⟨(by exact 𝔮 : Spec (D.obj k1)), ?_⟩, fun a t => pull _ (sch.map (Spec.map (D.map f1))) _ _ (y0 a t), ?_⟩
  · exact (PrimeSpectrum.ext h𝔮 : PrimeSpectrum.comap (u.app k1).hom 𝔮 = b)
  · let g' : Over.mk (Spec.map (s ≫ u.app k1)) ⟶ Over.mk (Spec.map (s ≫ u.app k0)) :=
      Over.homMk (Spec.map (D.map f1)) (by
        show Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp, Category.assoc, hun])
    have h1 := hL h6 q p i r c M n g' y0
    have hrst' : rst p g' = bcMap p (s ≫ u.app k0) (s ≫ u.app k1) (D.map f1) (by rw [Category.assoc, hun]) := rfl
    rw [hrst'] at h1
    beta_reduce at hk1
    simp only [e, map_sub, map_nsmul, sub_eq_zero] at hk1
    erw [h1] at hk1
    refine hk1.trans ?_
    erw [← pull_comp, ← Functor.map_comp, bcMap_comp', bcMap_eq _ _ _ _ _ _ (hun f1)]

end LateralTheory.KummerTheory.LHCut
