import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CompPowTate
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix

namespace GlobalTheory.Et.Rel

variable {X Y : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]

section
variable (f : X ⟶ Y)

abbrev liftOver {T : Over X} {T' : Over Y} (u : T' ⟶ (Over.map f).obj T) : Over X := Over.mk (u.left ≫ T.hom)

def liftOverHom {T : Over X} {T' : Over Y} (u : T' ⟶ (Over.map f).obj T) : liftOver f u ⟶ T :=
  Over.homMk u.left rfl

def mapLiftOverHom {T : Over X} {T' : Over Y} (u : T' ⟶ (Over.map f).obj T) : (Over.map f).obj (liftOver f u) ⟶ T' :=
  Over.homMk (𝟙 _) (by
    have h : u.left ≫ ((Over.map f).obj T).hom = T'.hom := Over.w u
    simp only [Over.map_obj_hom, Over.mk_hom] at h ⊢
    rw [Category.id_comp, ← h, Category.assoc])

end

variable (E) (f : X ⟶ Y) (Q' : RActPre X Γ) (Q : RActPre Y Γ) (ξ : Γ →* GL ι E)
  (e : ∀ T : Over X, Q'.P.obj (op T) ≃ Q.P.obj (op ((Over.map f).obj T)))
  (he : ∀ {T₁ T₂ : Over X} (v : T₁ ⟶ T₂) (η : Q'.P.obj (op T₂)),
    e T₁ (Q'.P.map v.op η) = Q.P.map ((Over.map f).map v).op (e T₂ η))
  (hq : ∀ (T : Over X) (γ : Γ) (η : Q'.P.obj (op T)), e T ((Q'.act γ).app (op T) η) = (Q.act γ).app _ (e T η))

def resAssocFwd (T : Over X) : assocSet E Q ξ ((Over.map f).obj T) →ₗ[E] assocSet E Q' ξ T where
  toFun F := ⟨fun T'' u η => F.1 ((Over.map f).obj T'') ((Over.map f).map u) (e T'' η),
    ⟨fun T₃ T₂ v u η t => by
      have h1 := F.2.1 ((Over.map f).map v) ((Over.map f).map u) (e T₂ η) t
      rw [← Functor.map_comp, ← he] at h1
      exact h1,
     fun T₂ u η γ t => by
      have h1 := F.2.2 ((Over.map f).map u) (e T₂ η) γ t
      rw [← hq] at h1
      exact h1⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end GlobalTheory.Et.Rel

namespace GlobalTheory.Et.Rel

variable {X Y : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]
variable (E) (f : X ⟶ Y) (Q' : RActPre X Γ) (Q : RActPre Y Γ) (ξ : Γ →* GL ι E)
  (e : ∀ T : Over X, Q'.P.obj (op T) ≃ Q.P.obj (op ((Over.map f).obj T)))
  (he : ∀ {T₁ T₂ : Over X} (v : T₁ ⟶ T₂) (η : Q'.P.obj (op T₂)),
    e T₁ (Q'.P.map v.op η) = Q.P.map ((Over.map f).map v).op (e T₂ η))
  (hq : ∀ (T : Over X) (γ : Γ) (η : Q'.P.obj (op T)), e T ((Q'.act γ).app (op T) η) = (Q.act γ).app _ (e T η))

def resAssocBwd (T : Over X) : assocSet E Q' ξ T →ₗ[E] assocSet E Q ξ ((Over.map f).obj T) where
  toFun G := ⟨fun T' u η => G.1 (liftOver f u) (liftOverHom f u) ((e _).symm (Q.P.map (mapLiftOverHom f u).op η)),
    ⟨fun T₂ T₁ v u η t => by
      let w : liftOver f (v ≫ u) ⟶ liftOver f u := Over.homMk v.left (by simp)
      have h1 : w ≫ liftOverHom f u = liftOverHom f (v ≫ u) := by
        ext; simp [w, liftOverHom]
      have h2 : Q'.P.map w.op ((e _).symm (Q.P.map (mapLiftOverHom f u).op η)) =
          (e _).symm (Q.P.map (mapLiftOverHom f (v ≫ u)).op (Q.P.map v.op η)) := by
        apply (e _).injective
        rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← FunctorToTypes.map_comp_apply,
          ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp]
        congr 2
      have h3 := G.2.1 w (liftOverHom f u) ((e _).symm (Q.P.map (mapLiftOverHom f u).op η)) t
      rw [h1, h2] at h3
      exact h3,
     fun T₁ u η γ t => by
      have h2 : (e _).symm (Q.P.map (mapLiftOverHom f u).op ((Q.act γ).app (op T₁) η)) =
          (Q'.act γ).app _ ((e _).symm (Q.P.map (mapLiftOverHom f u).op η)) := by
        apply (e _).injective
        rw [hq, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact (NatTrans.naturality_apply (Q.act γ) (mapLiftOverHom f u).op η).symm
      change G.1 (liftOver f u) (liftOverHom f u) ((e _).symm (Q.P.map (mapLiftOverHom f u).op ((Q.act γ).app (op T₁) η))) t = _
      rw [h2]
      exact G.2.2 (liftOverHom f u) ((e _).symm (Q.P.map (mapLiftOverHom f u).op η)) γ t⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def resAssocEquiv (T : Over X) : assocSet E Q ξ ((Over.map f).obj T) ≃ₗ[E] assocSet E Q' ξ T :=
  { resAssocFwd E f Q' Q ξ e he hq T with
    invFun := resAssocBwd E f Q' Q ξ e he hq T
    left_inv := fun F => by
      apply Subtype.ext
      funext T' u η
      ext t : 1
      change F.1 ((Over.map f).obj (liftOver f u)) ((Over.map f).map (liftOverHom f u))
        (e _ ((e _).symm (Q.P.map (mapLiftOverHom f u).op η))) t = F.1 T' u η t
      rw [Equiv.apply_symm_apply]
      have h1 : (Over.map f).map (liftOverHom f u) = mapLiftOverHom f u ≫ u := by
        ext; simp [mapLiftOverHom, liftOverHom]
      have h3 := F.2.1 (mapLiftOverHom f u) u η t
      rw [h1, h3]
      rfl
    right_inv := fun G => by
      apply Subtype.ext
      funext T'' u η
      ext t : 1
      let d : liftOver f ((Over.map f).map u) ⟶ T'' := Over.homMk (𝟙 _) (by
        have h : u.left ≫ _ = T''.hom := Over.w u
        simp only [Over.mk_hom, Over.map_map_left, Category.id_comp]
        exact h.symm)
      have h1 : liftOverHom f ((Over.map f).map u) = d ≫ u := by
        ext; simp [d, liftOverHom]
      have h2 : (e _).symm (Q.P.map (mapLiftOverHom f ((Over.map f).map u)).op (e T'' η)) = Q'.P.map d.op η := by
        apply (e _).injective
        rw [Equiv.apply_symm_apply, he]
        congr 2
      change G.1 _ (liftOverHom f ((Over.map f).map u))
        ((e _).symm (Q.P.map (mapLiftOverHom f ((Over.map f).map u)).op (e T'' η))) t = G.1 T'' u η t
      rw [h1, h2, G.2.1 d u η t]
      rfl }

end GlobalTheory.Et.Rel

namespace GlobalTheory.Et.Rel

variable {X Y : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]
variable (E) (f : X ⟶ Y) (Q' : RActPre X Γ) (Q : RActPre Y Γ) (ξ : Γ →* GL ι E)
  (e : ∀ T : Over X, Q'.P.obj (op T) ≃ Q.P.obj (op ((Over.map f).obj T)))
  (he : ∀ {T₁ T₂ : Over X} (v : T₁ ⟶ T₂) (η : Q'.P.obj (op T₂)),
    e T₁ (Q'.P.map v.op η) = Q.P.map ((Over.map f).map v).op (e T₂ η))
  (hq : ∀ (T : Over X) (γ : Γ) (η : Q'.P.obj (op T)), e T ((Q'.act γ).app (op T) η) = (Q.act γ).app _ (e T η))

def resAssocPreIso : (Over.map f).op ⋙ assocPre E Q ξ ≅ assocPre E Q' ξ :=
  NatIso.ofComponents
    (fun T => LinearEquiv.toModuleIso
      { resAssocEquiv E f Q' Q ξ e he hq T.unop with
        map_smul' := fun r x => (resAssocEquiv E f Q' Q ξ e he hq T.unop).map_smul r.down x })
    (fun {T₁ T₂} w => by
      ext F : 2
      apply Subtype.ext
      funext T'' u η
      change F.1 ((Over.map f).obj T'') ((Over.map f).map u ≫ (Over.map f).map w.unop) (e T'' η) =
        F.1 ((Over.map f).obj T'') ((Over.map f).map (u ≫ w.unop)) (e T'' η)
      rw [Functor.map_comp])

def resAssocIso : (res E f).obj (assoc E Q ξ) ≅ assoc E Q' ξ :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (resAssocPreIso E f Q' Q ξ e he hq)

end GlobalTheory.Et.Rel

namespace GlobalTheory.UPel.HT

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}

def ObjMap.ptEquiv (m : ObjMap o' o f) (T : Over S') : (T ⟶ o'.A) ≃* ((Over.map f).obj T ⟶ o.A) :=
  MulEquiv.ofBijective (pushHom m.cart T) ⟨GlobalTheory.SiegelPull.push_injective m.cart T, GlobalTheory.SiegelPull.push_surjective m.cart T⟩

theorem ObjMap.ptEquiv_left (m : ObjMap o' o f) (T : Over S') (x : T ⟶ o'.A) :
    (m.ptEquiv T x).left = x.left ≫ m.φ := rfl

theorem ObjMap.ptEquiv_act (m : ObjMap o' o f) (T : Over S') (x : T ⟶ o'.A) (c : D.O) :
    m.ptEquiv T (x ≫ o'.act.act c) = m.ptEquiv T x ≫ o.act.act c :=
  Over.OverMorphism.ext (by
    rw [ObjMap.ptEquiv_left, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, Category.assoc, m.act,
      Category.assoc])

theorem ObjMap.exists_ptEquiv (m : ObjMap o' o f) (Z : Over S) (g : Z.left ⟶ S') (hg : g ≫ f = Z.hom) :
    ∃ σ : (Over.mk g ⟶ o'.A) ≃* (Z ⟶ o.A), (∀ x, (σ x).left = x.left ≫ m.φ) ∧
      ∀ (n : ℤ) (a c : Over.mk g ⟶ o'.A) (z : Γ(Z.left, ⊤)ˣ),
        (Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n a c z ↔
          Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n (σ a) (σ c) z) := by
  obtain ⟨Zl, Zr, Zh⟩ := Z
  change Zl ⟶ S' at g
  change g ≫ f = Zh at hg
  subst hg
  refine ⟨m.ptEquiv (Over.mk g), fun x => rfl, fun n a c z => ?_⟩
  exact GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ o.A o'.A f m.φ _ _ (pull_isLB o.isLB _) (pull_isLB o'.isLB _)
    m.cart (GlobalTheory.SiegelPull.diag_iso m.sq m.pol) (Over.mk g) n a c _ _ z rfl rfl

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}

theorem ObjMap.geom_clauses_iff (m : ObjMap o' o f) (ℓ : ℕ) [Fact ℓ.Prime] {T : Over S'}
    (ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T ⟶ o'.A)) (k : Type) [Field k] (x : Sp k ⟶ S') (x₀ : Sp k ⟶ S)
    (j : Over.mk x ⟶ T) (j₀ : Over.mk x₀ ⟶ (Over.map f).obj T) (hj : j₀.left = j.left)
    (σ : (Over.mk x ⟶ o'.A) ≃* (Over.mk x₀ ⟶ o.A)) (hσ : ∀ y, (σ y).left = y.left ≫ m.φ)
    (hW : ∀ (n : ℤ) (a c : Over.mk x ⟶ o'.A) (z : Γ(Sp k, ⊤)ˣ),
        (Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n a c z ↔
          Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n (σ a) (σ c) z))
    (χ : ℕ → AddChar ℤ_[ℓ] kˣ) :
    ((∀ m v, j ≫ ev m v = 1 ↔ ∃ w, v = (ℓ : ℤ_[ℓ]) ^ m • w) ∧
      (∀ m (q : Over.mk x ⟶ o'.A), q ^ (ℓ ^ m) = 1 ↔ ∃ v, j ≫ ev m v = q) ∧
      ∀ m v w, Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) ((ℓ ^ m : ℕ) : ℤ) (j ≫ ev m v) (j ≫ ev m w)
        (unitOn (χ m (2 * (v ⬝ᵥ (D.gramEF.map (Int.castRingHom ℤ_[ℓ]) *ᵥ w)))))) ↔
    ((∀ mm v, j₀ ≫ m.ptEquiv T (ev mm v) = 1 ↔ ∃ w, v = (ℓ : ℤ_[ℓ]) ^ mm • w) ∧
      (∀ mm (q : Over.mk x₀ ⟶ o.A), q ^ (ℓ ^ mm) = 1 ↔ ∃ v, j₀ ≫ m.ptEquiv T (ev mm v) = q) ∧
      ∀ mm v w, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) ((ℓ ^ mm : ℕ) : ℤ)
        (j₀ ≫ m.ptEquiv T (ev mm v)) (j₀ ≫ m.ptEquiv T (ev mm w))
        (unitOn (χ mm (2 * (v ⬝ᵥ (D.gramEF.map (Int.castRingHom ℤ_[ℓ]) *ᵥ w)))))) := by
  have key : ∀ y : T ⟶ o'.A, σ (j ≫ y) = j₀ ≫ m.ptEquiv T y := fun y => Over.OverMorphism.ext (by
    rw [hσ, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, hj, Category.assoc])
  refine and_congr (forall₂_congr fun mm v => ?_) (and_congr (forall_congr' fun mm => ?_) (forall₃_congr fun mm v w => ?_))
  · rw [← key, map_eq_one_iff _ σ.injective]
  · rw [σ.surjective.forall]
    refine forall_congr' fun q => ?_
    rw [← map_pow, map_eq_one_iff _ σ.injective]
    exact iff_congr Iff.rfl (exists_congr fun v => by rw [← key, σ.injective.eq_iff])
  · rw [← key, ← key]
    exact hW _ _ _ _

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}

theorem ObjMap.isTateL_iff (m : ObjMap o' o f) (ℓ : ℕ) [Fact ℓ.Prime] (T : Over S')
    (ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T ⟶ o'.A)) :
    o'.IsTateL ℓ T ev ↔ o.IsTateL ℓ ((Over.map f).obj T) (fun mm v => m.ptEquiv T (ev mm v)) := by
  unfold Obj.IsTateL
  refine and_congr (forall₃_congr fun mm v w => ?_) (and_congr (forall₃_congr fun mm c v => ?_)
    (and_congr (forall₂_congr fun mm v => ?_) (and_congr (forall₂_congr fun mm v => ?_) ?_)))
  · rw [← map_mul, (m.ptEquiv T).injective.eq_iff]
  · rw [← ObjMap.ptEquiv_act, (m.ptEquiv T).injective.eq_iff]
  · exact (map_eq_one_iff _ (m.ptEquiv T).injective).symm
  · rw [← map_pow, (m.ptEquiv T).injective.eq_iff]
  constructor
  · intro h k _ _ x₀ j₀
    have hx : (j₀.left ≫ T.hom) ≫ f = x₀ := by
      have h0 : j₀.left ≫ ((Over.map f).obj T).hom = x₀ := Over.w j₀
      simpa only [Over.map_obj_hom, Category.assoc] using h0
    obtain ⟨σ, hσ, hW⟩ := m.exists_ptEquiv (Over.mk x₀) (j₀.left ≫ T.hom) hx
    obtain ⟨χ, h1, h2, hc⟩ := h k (j₀.left ≫ T.hom) (Over.homMk j₀.left rfl)
    exact ⟨χ, h1, h2, (m.geom_clauses_iff ℓ ev k _ x₀ (Over.homMk j₀.left rfl) j₀ rfl σ hσ hW χ).1 hc⟩
  · intro h k _ _ x j
    have hw : j.left ≫ T.hom = x := Over.w j
    let j₀ : Over.mk (x ≫ f) ⟶ (Over.map f).obj T := Over.homMk j.left (by
      rw [Over.map_obj_hom, ← Category.assoc, hw]; rfl)
    obtain ⟨σ, hσ, hW⟩ := m.exists_ptEquiv (Over.mk (x ≫ f)) x rfl
    obtain ⟨χ, h1, h2, hc⟩ := h k (x ≫ f) j₀
    exact ⟨χ, h1, h2, (m.geom_clauses_iff ℓ ev k x (x ≫ f) j j₀ rfl σ hσ hW χ).2 hc⟩

def ObjMap.tateLEquiv (m : ObjMap o' o f) (ℓ : ℕ) [Fact ℓ.Prime] (T : Over S') :
    (o'.tateL ℓ).P.obj (op T) ≃ (o.tateL ℓ).P.obj (op ((Over.map f).obj T)) :=
  Equiv.subtypeEquiv (Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ => (m.ptEquiv T).toEquiv)
    (fun ev => m.isTateL_iff ℓ T ev)

end GlobalTheory.UPel.HT
