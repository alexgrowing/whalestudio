import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

section GtIso

variable {S : Scheme.{0}} {E : SplitExt S} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂]

theorem pullU_res₂ {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U) (u : Γ(Y, U)ˣ) :
    pullU f V (res h u) = res (f.preimage_mono h) (pullU f U u) := by
  apply Units.ext
  have := congrArg (fun φ => φ.hom u.val) (f.naturality (homOfLE h).op)
  simpa [pullU, res] using this

theorem gm_id_pull {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm (𝟙 Y) y (f ⁻¹ᵁ U) (pullU f U a) = gm f y U a := (gm_pull (𝟙 Y) f y U h a).trans (by rw [Category.id_comp])

theorem gm_rp₁ {X Z : Scheme.{0}} (a : Z ⟶ X) (z : Z) (U : X.Opens) (V : Z.Opens) (hle : V ≤ a ⁻¹ᵁ U) (hz : z ∈ V)
    (u : Γ(X, U)ˣ) : gm (𝟙 Z) z V (res hle (pullU a U u)) = gm a z U u := (gm_res (𝟙 Z) z hle hz _).trans (gm_id_pull a z U (hle hz) u)

theorem gm_rp₂ {X Y Z : Scheme.{0}} (b : Z ⟶ Y) (a : Y ⟶ X) (z : Z) (U : X.Opens) (V : Z.Opens)
    (hle : V ≤ b ⁻¹ᵁ (a ⁻¹ᵁ U)) (hz : z ∈ V) (u : Γ(X, U)ˣ) :
    gm (𝟙 Z) z V (res hle (pullU b (a ⁻¹ᵁ U) (pullU a U u))) = gm (b ≫ a) z U u := (gm_res (𝟙 Z) z hle hz _).trans
    ((gm_id_pull b z _ (hle hz) _).trans (gm_pull b a z U (hle hz) u))

theorem transL {B Y Z : Scheme.{0}} (a : Z ⟶ Y) (q : Y ⟶ B) (U U' : B.Opens) (g : Γ(B, U ⊓ U')ˣ)
    (u : Γ(Y, q ⁻¹ᵁ U)ˣ) (u' : Γ(Y, q ⁻¹ᵁ U')ˣ)
    (h : res (q.preimage_mono (inf_le_right : U ⊓ U' ≤ U')) u' =
      pullU q _ g * res (q.preimage_mono (inf_le_left : U ⊓ U' ≤ U)) u) :
    res (a.preimage_mono (q.preimage_mono (inf_le_right : U ⊓ U' ≤ U'))) (pullU a _ u') =
      pullU a _ (pullU q _ g) * res (a.preimage_mono (q.preimage_mono (inf_le_left : U ⊓ U' ≤ U))) (pullU a _ u) := by
  have := congrArg (pullU a _) h
  rw [map_mul, pullU_res₂, pullU_res₂] at this
  exact this

private theorem pullU_comp_lemma {X Y Z : Scheme.{0}} (b : Z ⟶ Y) (a : Y ⟶ X) (W : X.Opens) (u : Γ(X, W)ˣ) :
    pullU b (a ⁻¹ᵁ W) (pullU a W u) = pullU (b ≫ a) W u := by
  apply Units.ext
  first
    | (simp [pullU]; done)
    | (simp [pullU]; rfl)
    | rfl

private theorem res_pullU_eq_mul_of_eq_of_eq {T Y P : Scheme.{0}} (W : Y.Opens) (u : Γ(Y, W)ˣ) (c : Γ(T, ⊤)ˣ) (F : P ⟶ T)
    (A S A' S' : P ⟶ Y) (hA : A = A') (hS : S = S')
    (le : S ⁻¹ᵁ W ≤ A ⁻¹ᵁ W) (t : S ⁻¹ᵁ W ≤ F ⁻¹ᵁ ⊤)
    (h : res le (pullU A W u) = res t (pullU F ⊤ c) * pullU S W u)
    (le' : S' ⁻¹ᵁ W ≤ A' ⁻¹ᵁ W) (t' : S' ⁻¹ᵁ W ≤ F ⁻¹ᵁ ⊤) :
    res le' (pullU A' W u) = res t' (pullU F ⊤ c) * pullU S' W u := by
  subst hA hS
  exact h

theorem equivL {T Y Z P₁ P₂ : Scheme.{0}} (act₁ s₁ : P₁ ⟶ Y) (f₁ : P₁ ⟶ T) (b : P₂ ⟶ P₁) (a : Z ⟶ Y) (act₂ s₂ : P₂ ⟶ Z)
    (f₂ : P₂ ⟶ T) (W : Y.Opens) (u : Γ(Y, W)ˣ) (c : Γ(T, ⊤)ˣ) (le₁ : s₁ ⁻¹ᵁ W ≤ act₁ ⁻¹ᵁ W)
    (t₁ : s₁ ⁻¹ᵁ W ≤ f₁ ⁻¹ᵁ ⊤) (h : res le₁ (pullU act₁ W u) = res t₁ (pullU f₁ ⊤ c) * pullU s₁ W u)
    (ha : act₂ ≫ a = b ≫ act₁) (hs : s₂ ≫ a = b ≫ s₁) (hf : f₂ = b ≫ f₁)
    (le₂ : s₂ ⁻¹ᵁ (a ⁻¹ᵁ W) ≤ act₂ ⁻¹ᵁ (a ⁻¹ᵁ W)) (t₂ : s₂ ⁻¹ᵁ (a ⁻¹ᵁ W) ≤ f₂ ⁻¹ᵁ ⊤) :
    res le₂ (pullU act₂ _ (pullU a W u)) = res t₂ (pullU f₂ ⊤ c) * pullU s₂ _ (pullU a W u) := by
  subst hf
  have h' := congrArg (pullU b (s₁ ⁻¹ᵁ W)) h
  rw [map_mul, pullU_res₂, pullU_res₂] at h'
  have key := res_pullU_eq_mul_of_eq_of_eq W u c (b ≫ f₁) (b ≫ act₁) (b ≫ s₁) (act₂ ≫ a) (s₂ ≫ a) ha.symm hs.symm
    (b.preimage_mono le₁) (b.preimage_mono t₁)
    (by
      first
        | exact h'
        | (rw [pullU_comp_lemma, pullU_comp_lemma, pullU_comp_lemma] at h'; exact h')) le₂ t₂
  first
    | exact key
    | (rw [pullU_comp_lemma, pullU_comp_lemma]; exact key)

theorem normL {S Y Z : Scheme.{0}} (e₁ : S ⟶ Y) (e₂ : S ⟶ Z) (a : Z ⟶ Y) (he : e₂ ≫ a = e₁) (W : Y.Opens) (V : S.Opens)
    (u : Γ(Y, W)ˣ) (r : Γ(S, V)ˣ)
    (h : res (inf_le_left : e₁ ⁻¹ᵁ W ⊓ V ≤ e₁ ⁻¹ᵁ W) (pullU e₁ W u) * res inf_le_right r = 1) :
    res (inf_le_left : e₂ ⁻¹ᵁ (a ⁻¹ᵁ W) ⊓ V ≤ e₂ ⁻¹ᵁ (a ⁻¹ᵁ W)) (pullU e₂ _ (pullU a W u)) * res inf_le_right r = 1 := by
  subst he
  first
    | exact h
    | (rw [pullU_comp_lemma]; exact h)
    | (convert h using 4; exact pullU_comp_lemma e₂ a W u)

theorem liftNC_comp₀ {A B C X : Type} [CommRing A] [CommRing B] [CommRing C] [AddCommGroup X] (f : A →+* B)
    (ρ : B →+* C) (g : Multiplicative X →* B) :
    AddMonoidAlgebra.liftNCRingHom (ρ.comp f) (ρ.toMonoidHom.comp g) (fun _ _ => Commute.all _ _) =
      ρ.comp (AddMonoidAlgebra.liftNCRingHom f g (fun _ _ => Commute.all _ _)) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro a
    simp [AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]
  · intro x
    simp [AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]

theorem liftNC_comp {A B C X ι' : Type} [CommRing A] [CommRing B] [CommRing C] [AddCommGroup X] (f : A →+* B)
    (ρ : B →+* C) (b : Module.Basis ι' ℤ X) (v : ι' → Bˣ) (v' : ι' → Cˣ) (hv : ∀ k, (v' k).val = ρ (v k).val) :
    AddMonoidAlgebra.liftNCRingHom (ρ.comp f) ((Units.coeHom C).comp (AddMonoidHom.toMultiplicativeLeft
        (b.constr ℤ (fun k => Additive.ofMul (v' k))).toAddMonoidHom)) (fun _ _ => Commute.all _ _) =
      ρ.comp (AddMonoidAlgebra.liftNCRingHom f ((Units.coeHom B).comp (AddMonoidHom.toMultiplicativeLeft
        (b.constr ℤ (fun k => Additive.ofMul (v k))).toAddMonoidHom)) (fun _ _ => Commute.all _ _)) := by
  have hlin : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map ρ.toMonoidHom))).comp
      (b.constr ℤ (fun k => Additive.ofMul (v k))) = b.constr ℤ (fun k => Additive.ofMul (v' k)) := by
    refine b.ext fun k => ?_
    simp only [LinearMap.comp_apply, Module.Basis.constr_basis]
    apply congrArg Additive.ofMul
    exact Units.ext (by rw [hv k]; rfl)
  have key : ∀ y : X, ρ ((Additive.toMul (b.constr ℤ (fun k => Additive.ofMul (v k)) y) : Bˣ) : B) =
      ((Additive.toMul (b.constr ℤ (fun k => Additive.ofMul (v' k)) y) : Cˣ) : C) := by
    intro y
    have := congrArg (fun φ : X →ₗ[ℤ] Additive Cˣ => ((Additive.toMul (φ y) : Cˣ) : C)) hlin
    simpa using this
  rw [← liftNC_comp₀]
  congr 1
  ext x
  first
    | exact (key (Multiplicative.toAdd x)).symm
    | simpa using (key x).symm

set_option maxHeartbeats 800000 in
theorem isGt_of_iso (e : G₁ ≅ G₂) [IsMonHom e.hom] (h : E.IsGt G₁) : E.IsGt G₂ := by
  obtain ⟨d⟩ := h
  have := d.q_hom
  have := d.i_hom
  have : IsIso e.inv.left := ⟨⟨e.hom.left, by rw [← Over.comp_left, e.inv_hom_id, Over.id_left],
    by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]⟩⟩
  have := d.q_flat
  have := d.q_surjective
  have := d.q_affine
  have hact : (lift (fst (splitTorus S E.X) G₂ ≫ d.i ≫ e.hom) (snd _ _) ≫ μ[G₂]).left ≫ e.inv.left =
      (splitTorus S E.X ◁ e.inv).left ≫ (lift (fst (splitTorus S E.X) G₁ ≫ d.i) (snd _ _) ≫ μ[G₁]).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [← Hom.mul_def, ← Hom.mul_def, MonObj.mul_comp, MonObj.comp_mul]
    simp
  have hsnd : (snd (splitTorus S E.X) G₂).left ≫ e.inv.left =
      (splitTorus S E.X ◁ e.inv).left ≫ (snd (splitTorus S E.X) G₁).left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  have hfst : (fst (splitTorus S E.X) G₂).left =
      (splitTorus S E.X ◁ e.inv).left ≫ (fst (splitTorus S E.X) G₁).left := by
    rw [← Over.comp_left, whiskerLeft_fst]
  have he : eSec G₂ ≫ e.inv.left = eSec G₁ := congrArg (fun z => z.left) (IsMonHom.one_hom e.inv)
  have m₁ : ∀ (j : E.ChartIdx) (y : (splitTorus S E.X ⊗ G₂).left),
      y ∈ (snd (splitTorus S E.X) G₂).left ⁻¹ᵁ ((e.inv ≫ d.q).left ⁻¹ᵁ E.chart j) →
      (splitTorus S E.X ◁ e.inv).left y ∈ (snd (splitTorus S E.X) G₁).left ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart j) := by
    intro j y hy
    have e₁ := congrArg (fun g => g y) hsnd
    exact (congrArg (fun z => d.q.left z ∈ E.chart j) e₁).mp hy
  have le : ∀ j : E.ChartIdx, (snd (splitTorus S E.X) G₂).left ⁻¹ᵁ ((e.inv ≫ d.q).left ⁻¹ᵁ E.chart j) ≤
      (lift (fst (splitTorus S E.X) G₂ ≫ d.i ≫ e.hom) (snd _ _) ≫ μ[G₂]).left ⁻¹ᵁ
        ((e.inv ≫ d.q).left ⁻¹ᵁ E.chart j) := by
    intro j y hy
    have e₁ := congrArg (fun g => g y) hact
    exact (congrArg (fun z => d.q.left z ∈ E.chart j) e₁).mpr (d.act_le j (m₁ j y hy))
  refine ⟨{ q := e.inv ≫ d.q
            i := d.i ≫ e.hom
            q_hom := inferInstance
            i_hom := inferInstance
            q_flat := by rw [Over.comp_left]; infer_instance
            q_surjective := by rw [Over.comp_left]; infer_instance
            q_affine := by rw [Over.comp_left]; infer_instance
            isKernel := by
              refine IsPullback.of_iso d.isKernel (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
            u := fun j k => pullU e.inv.left _ (d.u j k)
            coord := fun j V hV hle => ?_
            trans := fun j j' k => transL e.inv.left d.q.left _ _ _ _ _ (d.trans j j' k)
            act_le := le
            equiv := fun j k => equivL _ _ _ _ e.inv.left _ _ _ (d.q.left ⁻¹ᵁ E.chart j) (d.u j k) _ (d.act_le j) _
              (d.equiv j k) hact hsnd hfst (le j) _
            unit_norm := fun j k => normL (eSec G₁) (eSec G₂) e.inv.left he (d.q.left ⁻¹ᵁ E.chart j) _ (d.u j k) _
              (d.unit_norm j k) }⟩
  · have hb : Function.Bijective (e.inv.left.app (d.q.left ⁻¹ᵁ V)).hom :=
      ConcreteCategory.bijective_of_isIso (e.inv.left.app (d.q.left ⁻¹ᵁ V))
    have hl := liftNC_comp (d.q.left.app V).hom (e.inv.left.app (d.q.left ⁻¹ᵁ V)).hom E.basis
      (fun k => res (Scheme.Hom.preimage_mono d.q.left hle) (d.u j k))
      (fun k => res (e.inv.left.preimage_mono (Scheme.Hom.preimage_mono d.q.left hle)) (pullU e.inv.left _ (d.u j k)))
      (fun k => congrArg Units.val (pullU_res₂ e.inv.left (Scheme.Hom.preimage_mono d.q.left hle) (d.u j k)).symm)
    have hb₂ := hb.comp (d.coord j V hV hle)
    rw [← RingHom.coe_comp, ← hl] at hb₂
    exact hb₂

end GtIso

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem splitsAt (hC : Out.CubePullSt) (hU : Out.UnramExtSt) (hB : Out.GtBaseChangeSt) (hS : Y.SplitFibres)
    (P : ValPt Y) : SplitsAt P := by
  have := P.complete
  let f₀ : Sp (ResidueField P.V) ⟶ Y.X := spMap (residue P.V) ≫ P.yt
  let x : Y.X := f₀ (closedPoint (ResidueField P.V))
  let φ₀ : Y.X.residueField x ⟶ CommRingCat.of (ResidueField P.V) :=
    Scheme.descResidueField (Scheme.stalkClosedPointTo f₀)
  have hf₀ : Spec.map φ₀ ≫ Y.X.fromSpecResidueField x = f₀ :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField _ _ f₀
  obtain ⟨k, _, _, hfin, hsep, S, hGt⟩ := hS x
  let Ω := AlgebraicClosure (ResidueField P.V)
  let _ : Algebra (Y.X.residueField x) (ResidueField P.V) := φ₀.hom.toAlgebra
  let σ : k →ₐ[Y.X.residueField x] Ω := IsAlgClosed.lift
  let bs := Module.finBasis (Y.X.residueField x) k
  let k' := IntermediateField.adjoin (ResidueField P.V) (Set.range fun i => σ (bs i))
  have sepσ : ∀ z : k, IsSeparable (ResidueField P.V) (σ z) := fun z =>
    ((Algebra.IsSeparable.isSeparable (Y.X.residueField x) z).map σ σ.injective).tower_top _
  have : FiniteDimensional (ResidueField P.V) k' :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨i, rfl⟩; exact (sepσ _).isIntegral)
  have : Algebra.IsSeparable (ResidueField P.V) k' :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable _ _).2 (by rintro _ ⟨i, rfl⟩; exact sepσ _)
  have hmem : ∀ z : k, σ z ∈ k' := fun z => by
    rw [← bs.sum_repr z, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply (Y.X.residueField x) (ResidueField P.V) Ω]
    exact mul_mem (k'.algebraMap_mem _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  obtain ⟨W, _, _, _, hc, _, h₁, h₂, -, h₄, e, he⟩ := hU P.V k'
  let Wx : UnramExt P.V := { W := W, fin := h₁, inj := h₂, unram := h₄, complete := hc }
  let g : k →+* ResidueField W := e.symm.toRingHom.comp (σ.toRingHom.codRestrict k'.toSubring hmem)
  have hg : g.comp (algebraMap (Y.X.residueField x) k) =
      (e.symm.toRingHom.comp (algebraMap (ResidueField P.V) k')).comp φ₀.hom := by
    ext z
    exact congrArg e.symm (Subtype.ext (σ.commutes z))
  have hr : (residue W).comp (algebraMap P.V W) =
      (e.symm.toRingHom.comp (algebraMap (ResidueField P.V) k')).comp (residue P.V) := by
    ext v
    exact e.injective ((he v).trans (e.apply_symm_apply _).symm)
  have key : spMap g ≫ Spec.map (CommRingCat.ofHom (algebraMap (Y.X.residueField x) k)) ≫ Y.X.fromSpecResidueField x =
      spMap (residue W) ≫ P.ξ Wx := by
    have a₁ : spMap g ≫ Spec.map (CommRingCat.ofHom (algebraMap (Y.X.residueField x) k)) =
        spMap (e.symm.toRingHom.comp (algebraMap (ResidueField P.V) k')) ≫ Spec.map φ₀ :=
      (spMap_comp _ _).symm.trans ((congrArg spMap hg).trans (spMap_comp _ _))
    have a₂ : spMap (residue W) ≫ spMap (algebraMap P.V W) =
        spMap (e.symm.toRingHom.comp (algebraMap (ResidueField P.V) k')) ≫ spMap (residue P.V) :=
      (spMap_comp _ _).symm.trans ((congrArg spMap hr).trans (spMap_comp _ _))
    rw [← Category.assoc, a₁, Category.assoc, hf₀]
    show _ = spMap (residue W) ≫ spMap (algebraMap P.V W) ≫ P.yt
    rw [← Category.assoc (spMap (residue W)), a₂, Category.assoc]
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull hC (P.ξ Wx) Y.t
  obtain ⟨S', -, -, -, -, hGt'⟩ := hB _ _ (spMap g) S _ hGt
  refine ⟨Wx, _, m, S', ?_⟩
  have : IsMonHom (pullCompIso (spMap g) (Spec.map (CommRingCat.ofHom (algebraMap (Y.X.residueField x) k)) ≫
      Y.X.fromSpecResidueField x) Y.t.G).symm.hom := by
    show IsMonHom (pullCompIso _ _ _).inv
    infer_instance
  have h₀ := isGt_of_iso (pullCompIso (spMap g) _ Y.t.G).symm hGt'
  rw [key] at h₀
  exact isGt_of_iso (pullCompIso (spMap (residue W)) (P.ξ Wx) Y.t.G) h₀

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
