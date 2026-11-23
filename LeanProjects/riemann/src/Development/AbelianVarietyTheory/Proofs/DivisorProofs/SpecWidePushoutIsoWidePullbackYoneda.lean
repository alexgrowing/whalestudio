import Mathlib
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.SpecWidePullback

noncomputable def specHomEquiv (X : Scheme.{0}) (R : CommRingCat.{0}) :
    (R ⟶ Γ(X, ⊤)) ≃ (X ⟶ Spec R) where
  toFun φ := ΓSpec.adjunction.homEquiv X (op R) (show Scheme.Γ.rightOp.obj X ⟶ op R from φ.op)
  invFun y := ((ΓSpec.adjunction.homEquiv X (op R)).symm y).unop
  left_inv φ := congrArg Quiver.Hom.unop (Equiv.symm_apply_apply (ΓSpec.adjunction.homEquiv X (op R))
    (show Scheme.Γ.rightOp.obj X ⟶ op R from φ.op))
  right_inv y := Equiv.apply_symm_apply (ΓSpec.adjunction.homEquiv X (op R)) y

theorem specHomEquiv_comp (X : Scheme.{0}) {R R' : CommRingCat.{0}} (ψ : R' ⟶ R) (φ : R ⟶ Γ(X, ⊤)) :
    specHomEquiv X R' (ψ ≫ φ) = specHomEquiv X R φ ≫ Spec.map ψ := by
  exact ΓSpec.adjunction.homEquiv_naturality_right (show Scheme.Γ.rightOp.obj X ⟶ op R from φ.op) ψ.op

theorem specHomEquiv_symm_comp (X : Scheme.{0}) {R R' : CommRingCat.{0}} (y : X ⟶ Spec R) (ψ : R' ⟶ R) :
    (specHomEquiv X R').symm (y ≫ Spec.map ψ) = ψ ≫ (specHomEquiv X R).symm y := by
  rw [Equiv.symm_apply_eq, specHomEquiv_comp, Equiv.apply_symm_apply]

theorem existsUnique_lift {A B T : Type} [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) {k : ℕ}
    (ι : Fin (k + 1) → (B →+* T))
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)),
      (∀ j, (g j).comp a = (g 0).comp a) → ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j)
    (X : Scheme.{0}) (y : Fin (k + 1) → (X ⟶ Spec (CommRingCat.of B)))
    (hy : ∀ j, y j ≫ Spec.map (CommRingCat.ofHom a) = y 0 ≫ Spec.map (CommRingCat.ofHom a)) :
    ∃! m : X ⟶ Spec (CommRingCat.of T), ∀ j, m ≫ Spec.map (CommRingCat.ofHom (ι j)) = y j := by
  let g : Fin (k + 1) → (B →+* Γ(X, ⊤)) := fun j => ((specHomEquiv X _).symm (y j)).hom
  have hg : ∀ j, (g j).comp a = (g 0).comp a := fun j => by
    have := congrArg (fun z => ((specHomEquiv X (CommRingCat.of A)).symm z).hom) (hy j)
    simpa [g, specHomEquiv_symm_comp] using this
  obtain ⟨φ, hφ, huniq⟩ := hu Γ(X, ⊤) g hg
  refine ⟨specHomEquiv X _ (CommRingCat.ofHom φ), fun j => ?_, fun m hm => ?_⟩
  · rw [← specHomEquiv_comp, Equiv.apply_eq_iff_eq_symm_apply]
    exact CommRingCat.hom_ext (hφ j)
  · have h1 : ((specHomEquiv X _).symm m).hom = φ := huniq _ fun j => by
      have := congrArg (fun z => ((specHomEquiv X (CommRingCat.of B)).symm z).hom) (hm j)
      simpa [g, specHomEquiv_symm_comp] using this
    rw [← h1]
    simp

end GlobalTheory.SpecWidePullback

namespace GlobalTheory.SpecWidePullback

theorem yoneda_spec_isoWidePullback (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B)
    (k : ℕ) (ι : Fin (k + 1) → (B →+* T)) (hι : ∀ j, (ι j).comp a = (ι 0).comp a)
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)),
      (∀ j, (g j).comp a = (g 0).comp a) → ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j) :
    ∃ e : yoneda.obj (Spec (CommRingCat.of T)) ≅ widePullback (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))),
      ∀ j, e.hom ≫ WidePullback.π _ j = yoneda.map (Spec.map (CommRingCat.ofHom (ι j))) := by
  have hleg : ∀ j, Spec.map (CommRingCat.ofHom (ι j)) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom ((ι 0).comp a)) := fun j => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hι j]
  let c : Cone (WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
      (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
      (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a)))) :=
    WidePullbackShape.mkCone (yoneda.map (Spec.map (CommRingCat.ofHom ((ι 0).comp a))))
      (fun j => yoneda.map (Spec.map (CommRingCat.ofHom (ι j))))
      (fun j => by
        change yoneda.map (Spec.map (CommRingCat.ofHom (ι j))) ≫ yoneda.map (Spec.map (CommRingCat.ofHom a)) = _
        rw [← yoneda.map_comp, hleg j])
  have hc : IsLimit c := by
    apply evaluationJointlyReflectsLimits
    intro U
    have hw : ∀ (s : Cone (WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))) ⋙ (evaluation _ _).obj U)) (x : s.pt) j,
        s.π.app (some j) x ≫ Spec.map (CommRingCat.ofHom a) = s.π.app none x := fun s x j =>
      ConcreteCategory.congr_hom (s.w (WidePullbackShape.Hom.term j)) x
    have H := fun (s : Cone (WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))) ⋙ (evaluation _ _).obj U)) (x : s.pt) =>
      existsUnique_lift a ι hu (unop U) (fun j => s.π.app (some j) x)
        (fun j => (hw s x j).trans (hw s x 0).symm)
    refine IsLimit.mk (fun s => TypeCat.ofHom (fun x => (H s x).exists.choose)) (fun s j => ?_) (fun s m hm => ?_)
    · ext x
      rcases j with _ | j
      · change (H s x).exists.choose ≫ Spec.map (CommRingCat.ofHom ((ι 0).comp a)) = s.π.app none x
        rw [← hleg 0, ← Category.assoc, (H s x).exists.choose_spec 0, hw]
      · exact (H s x).exists.choose_spec j
    · ext x
      refine (H s x).unique (fun j => ?_) (H s x).exists.choose_spec
      have h := ConcreteCategory.congr_hom (hm (some j)) x
      rw [ConcreteCategory.comp_apply] at h
      exact h
  exact ⟨hc.conePointUniqueUpToIso (limit.isLimit _), fun j =>
    hc.conePointUniqueUpToIso_hom_comp (limit.isLimit _) (some j)⟩

end GlobalTheory.SpecWidePullback
