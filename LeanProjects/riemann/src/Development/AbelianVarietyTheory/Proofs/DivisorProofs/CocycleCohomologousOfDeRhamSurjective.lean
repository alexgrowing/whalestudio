import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt.Lift

variable {R : Type} [CommRing R] {X : Over (Sp R)}

def trivEquiv (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (hT : T.J = ⊥) : T.B ≃+* T.B₀ :=
  RingEquiv.ofBijective T.π ⟨(injective_iff_map_eq_zero T.π).2 fun b hb ↦ by
      have h := (T.ker b).1 hb
      rw [hT] at h
      exact Ideal.mem_bot.1 h, T.surj⟩

theorem trivEquiv_symm_π (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (hT : T.J = ⊥) (b : T.B) :
    (trivEquiv T hT).symm (T.π b) = b :=
  (trivEquiv T hT).symm_apply_apply b

def trivPt (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (hT : T.J = ⊥) : Pt X T.B :=
  Over.homMk (spMap ((trivEquiv T hT).symm.toRingHom) ≫ T.x) (by
    have h : T.x ≫ X.hom = spMap (T.π.comp (algebraMap R T.B)) :=
      ((Category.comp_id _).symm.trans (Category.assoc _ _ _)).trans T.w
    change (spMap _ ≫ T.x) ≫ X.hom = spMap (algebraMap R T.B)
    rw [Category.assoc, h, ← Cris.spMap_comp]
    congr 1
    ext r
    exact trivEquiv_symm_π T hT _)

theorem spOver_trivPt {T T' : Thick (dp0 R) (X.hom ≫ 𝟙 _)} (hT : T.J = ⊥) (hT' : T'.J = ⊥) (φ : T ⟶ T') :
    spOver φ.φ ≫ trivPt T hT = trivPt T' hT' := by
  apply Over.OverMorphism.ext
  change spMap (φ.φ : T.B →+* T'.B) ≫ spMap ((trivEquiv T hT).symm.toRingHom) ≫ T.x =
    spMap ((trivEquiv T' hT').symm.toRingHom) ≫ T'.x
  rw [← φ.pt, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
  congr 2
  ext b
  obtain ⟨b, rfl⟩ := T.surj b
  change φ.φ ((trivEquiv T hT).symm (T.π b)) = (trivEquiv T' hT').symm (φ.φ₀ (T.π b))
  rw [φ.comm, trivEquiv_symm_π, trivEquiv_symm_π]

theorem trivPt_trivAt {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) : trivPt (trivAt x) rfl = x := by
  apply Over.OverMorphism.ext
  change spMap ((trivEquiv (trivAt x) rfl).symm.toRingHom) ≫ x.left = x.left
  have : (trivEquiv (trivAt x) rfl).symm.toRingHom = RingHom.id D :=
    RingHom.ext fun b ↦ trivEquiv_symm_π (trivAt x) rfl b
  rw [this, Cris.spMap_id, Category.id_comp]

def trivCoc (u : Fn1 X) (hu : IsCoc (whole X) u) :
    Z1 ((IsTriv (X.hom ≫ 𝟙 _)).ι ⋙ O (dp0 R) (X.hom ≫ 𝟙 _)) :=
  ⟨fun T T' φ ↦ u T.obj.B T'.obj.B φ.hom.φ (trivPt T.obj T.property), fun T T' T'' φ ψ ↦ by
    change u _ _ (ψ.hom.φ.comp φ.hom.φ) _ = ψ.hom.φ (u _ _ φ.hom.φ _) + u _ _ ψ.hom.φ _
    rw [hu _ _ _ φ.hom.φ ψ.hom.φ _ (sm_whole _), spOver_trivPt T.property T'.property φ.hom]⟩

end GlobalTheory.PtExt.Lift

open GlobalTheory.PtExt.Lift in

theorem GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective : ∀ (R : Type) [CommRing R] (X : Over (Sp R)),
    Function.Surjective (toH1O (X.hom ≫ 𝟙 _)) → ∀ u : Fn1 X, IsCoc (whole X) u →
      ∃ f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)), Cohom (whole X) u (fv f) := by
  intro R _ X hs u hu
  obtain ⟨c, hc⟩ := hs (H1.mk _ (trivCoc u hu))
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  have hc' : H1.mk _ ((CoefMap.restrict (O (dp0 R) (X.hom ≫ 𝟙 _)) (IsTriv (X.hom ≫ 𝟙 _)).ι).pullbackOneCocycle f) =
      H1.mk _ (trivCoc u hu) := hc
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 hc'
  refine ⟨f, fun D _ _ x ↦ -g ⟨trivAt x, rfl⟩, ?_⟩
  intro D _ _ D' _ _ φ x _
  have h := congrFun (congrFun (congrFun hg ⟨trivAt x, rfl⟩) ⟨trivAt (spOver φ ≫ x), rfl⟩) ⟨trivMap φ x⟩
  change @id D' (g ⟨trivAt (spOver φ ≫ x), rfl⟩) - φ (@id D (g ⟨trivAt x, rfl⟩)) = ev f (trivMap φ x) - u D D' φ (trivPt (trivAt x) rfl) at h
  rw [trivPt_trivAt] at h
  change u D D' φ x + -ev f (trivMap φ x) = -@id D' (g ⟨trivAt (spOver φ ≫ x), rfl⟩) - φ (-(@id D (g ⟨trivAt x, rfl⟩)))
  rw [map_neg]
  linear_combination h
