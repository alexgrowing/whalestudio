import Development.EtaleCohomology.TateTwists.EtaleCechConerveImageIsoCechNerveOfPreservesWide

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ConerveIsomorphism

variable {T : Type 1} [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ)
  {U V : T} (g : U ⟶ V)

noncomputable def phi (n : ℕ) :
    (Ψ.obj (widePushout U (fun _ : Fin (n+1) => V) (fun _ => g))).unop ⟶
      widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) :=
  WidePullback.lift (Ψ.map (WidePushout.head _)).unop (fun j => (Ψ.map (WidePushout.ι _ j)).unop)
    (fun j => by
      have h := WidePushout.arrow_ι (fun _ : Fin (n+1) => g) j
      rw [← unop_comp, ← Ψ.map_comp, h])

@[reassoc (attr := simp)]
lemma phi_π (n : ℕ) (j : Fin (n+1)) :
    phi Ψ g n ≫ WidePullback.π _ j = (Ψ.map (WidePushout.ι _ j)).unop := by
  unfold phi; erw [WidePullback.lift_π]

@[reassoc (attr := simp)]
lemma phi_base (n : ℕ) :
    phi Ψ g n ≫ WidePullback.base _ = (Ψ.map (WidePushout.head _)).unop := by
  unfold phi; erw [WidePullback.lift_base]

lemma aux (n : ℕ) (j : Fin (n+1)) :
    Ψ.map g ≫ (WidePullback.π (fun _ : Fin (n+1) => (Ψ.map g).unop) j).op =
      (WidePullback.base (fun _ : Fin (n+1) => (Ψ.map g).unop)).op := by
  rw [← WidePullback.π_arrow (fun _ : Fin (n+1) => (Ψ.map g).unop) j]
  rfl

noncomputable def cocone (n : ℕ) : Cocone (WidePushoutShape.wideSpan U (fun _ : Fin (n+1) => V) (fun _ => g) ⋙ Ψ) where
  pt := op (widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop))
  ι :=
    { app := fun j => match j with
        | none => (WidePullback.base _).op
        | some j => (WidePullback.π _ j).op
      naturality := by
        rintro X Y (_ | j)
        · rw [WidePushoutShape.hom_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
            Category.id_comp, Category.comp_id]
        · exact (aux Ψ g n j).trans (Category.comp_id _).symm }

lemma natural (a b : ℕ) (σ : Fin (a+1) → Fin (b+1)) :
    (Ψ.map (WidePushout.desc (WidePushout.head (fun _ : Fin (b+1) => g))
      (fun i => WidePushout.ι (fun _ : Fin (b+1) => g) (σ i))
      (fun i => WidePushout.arrow_ι (fun _ : Fin (b+1) => g) (σ i)))).unop ≫ phi Ψ g a =
    phi Ψ g b ≫ WidePullback.lift (WidePullback.base (fun _ : Fin (b+1) => (Ψ.map g).unop))
      (fun i => WidePullback.π (fun _ : Fin (b+1) => (Ψ.map g).unop) (σ i))
      (fun i => WidePullback.π_arrow (fun _ : Fin (b+1) => (Ψ.map g).unop) (σ i)) := by
  apply WidePullback.hom_ext
  · intro j
    rw [Category.assoc, Category.assoc, phi_π, WidePullback.lift_π, phi_π, ← unop_comp, ← Ψ.map_comp,
      WidePushout.ι_desc]
  · rw [Category.assoc, Category.assoc, phi_base, WidePullback.lift_base, phi_base, ← unop_comp,
      ← Ψ.map_comp, WidePushout.head_desc]

variable (hΨ : ∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ)

noncomputable def hc (n : ℕ) :
    IsColimit (Ψ.mapCocone (colimit.cocone (WidePushoutShape.wideSpan U (fun _ : Fin (n+1) => V) (fun _ => g)))) :=
  haveI := hΨ n
  isColimitOfPreserves Ψ (colimit.isColimit _)

noncomputable def psi (n : ℕ) :
    widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) ⟶
      (Ψ.obj (widePushout U (fun _ : Fin (n+1) => V) (fun _ => g))).unop :=
  ((hc Ψ g hΨ n).desc (cocone Ψ g n)).unop

lemma desc_phi (n : ℕ) : (hc Ψ g hΨ n).desc (cocone Ψ g n) ≫ (phi Ψ g n).op = 𝟙 _ := by
  apply (hc Ψ g hΨ n).hom_ext
  rintro (_ | j)
  · rw [Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun x => x ≫ (phi Ψ g n).op)
      ((hc Ψ g hΨ n).fac (cocone Ψ g n) none)).trans (Quiver.Hom.unop_inj (phi_base Ψ g n)))
  · rw [Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun x => x ≫ (phi Ψ g n).op)
      ((hc Ψ g hΨ n).fac (cocone Ψ g n) (some j))).trans (Quiver.Hom.unop_inj (phi_π Ψ g n j)))

noncomputable def levelIso (n : ℕ) :
    (Ψ.obj (widePushout U (fun _ : Fin (n+1) => V) (fun _ => g))).unop ≅
      widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) where
  hom := phi Ψ g n
  inv := psi Ψ g hΨ n
  hom_inv_id := congrArg Quiver.Hom.unop (desc_phi Ψ g hΨ n)
  inv_hom_id := by
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, phi_π, Category.id_comp]
      exact congrArg Quiver.Hom.unop ((hc Ψ g hΨ n).fac (cocone Ψ g n) (some j))
    · rw [Category.assoc, phi_base, Category.id_comp]
      exact congrArg Quiver.Hom.unop ((hc Ψ g hΨ n).fac (cocone Ψ g n) none)

end LateralTheory.EtaleFoundations.ConerveIsomorphism

open LateralTheory.EtaleFoundations.ConerveIsomorphism in
theorem LateralTheory.EtaleFoundations.etale_cech_conerve_image_iso_cech_nerve_of_preserves_wide_pushouts : LateralTheory.EtaleFoundations.EtaleCechConerveImageIsoCechNerveOfPreservesWidePushouts := by
  intro T _ _ Ψ hΨ U V g
  refine ⟨NatIso.ofComponents (fun n => levelIso Ψ g hΨ n.unop.len) ?_, ?_⟩
  · intro m n h
    exact natural Ψ g _ _ h.unop.toOrderHom
  · ext n : 1
    exact (phi_base Ψ g (unop n).len).symm
