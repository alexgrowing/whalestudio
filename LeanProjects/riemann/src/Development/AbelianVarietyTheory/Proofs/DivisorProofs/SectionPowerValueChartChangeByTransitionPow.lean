import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecValLC

theorem valR_def' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) := by
  unfold valR; rw [dif_pos h]

theorem valR_mul' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f g : Γ(X, U)) :
    valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_def' x U h, map_mul]

theorem valR_map' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V ((X.presheaf.map (homOfLE e).op).hom f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h.trans (x.preimage_mono e)
  rw [valR_def' x V h, valR_def' x U hU]
  have := Scheme.Hom.map_appLE x h (homOfLE e).op
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    ((X.presheaf.map (homOfLE e).op ≫ x.appLE V ⊤ h).hom f) = _
  rw [this]

theorem valR_id_app {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ ((𝟙 X) ⁻¹ᵁ U)) (f : Γ(X, U)) :
    valR x ((𝟙 X) ⁻¹ᵁ U) ((Scheme.Hom.app (𝟙 X) U).hom f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h
  rw [valR_def' x _ h, valR_def' x U hU]
  congr 1

theorem valR_pow' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (n : ℕ) :
    valR x U (f ^ n) = valR x U f ^ n := by
  simp only [valR_def' x U h, map_pow]

theorem secM_valR_transition : ∀ (X : Scheme.{0}) (L : LB X) (k : ℕ) (σ : SecM (𝟙 X) L k) (F : Type) [Field F] (ξ : Sp F ⟶ X) (j j' : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j → ⊤ ≤ ξ ⁻¹ᵁ L.U j' → valR ξ _ (σ.f fun _ => j) = valR ξ (L.U j ⊓ L.U j') (L.g j j').val ^ k * valR ξ _ (σ.f fun _ => j') := by
  intro X L k σ F _ ξ j j' hj hj'
  set LC := LB.LinComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => (k:ℤ)) with hLC
  have hW : ∀ i : L.ι, L.U i ≤ LC.U (fun _ => i) :=
    fun i x hx => Set.mem_iInter.2 fun _ => hx
  have h1 : ⊤ ≤ ξ ⁻¹ᵁ (LC.U (fun _ => j) ⊓ LC.U (fun _ => j')) := by
    intro x hx
    exact ⟨hW j (hj hx), hW j' (hj' hx)⟩
  have h2 : ⊤ ≤ ξ ⁻¹ᵁ ((𝟙 X) ⁻¹ᵁ (L.U j ⊓ L.U j')) := fun x hx => ⟨hj hx, hj' hx⟩
  have hle : LC.U (fun _ => j) ⊓ LC.U (fun _ => j') ≤ (𝟙 X) ⁻¹ᵁ (L.U j ⊓ L.U j') :=
    le_inf (inf_le_left.trans (LB.wchart_le L _ _ 0)) (inf_le_right.trans (LB.wchart_le L _ _ 0))
  have hg : ((LC.g (fun _ => j) (fun _ => j') : Γ(X, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))ˣ) :
      Γ(X, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))) =
      (X.presheaf.map (homOfLE hle).op).hom ((Scheme.Hom.app (𝟙 X) (L.U j ⊓ L.U j')).hom
        (L.g j j' : Γ(X, L.U j ⊓ L.U j'))) ^ k := by
    show Units.val (∏ _i : Fin 1, (res _ (pullU (𝟙 X) _ (L.g j j'))) ^ (k:ℤ)) = _
    rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
    rfl
  have hc := σ.compat (fun _ => j) (fun _ => j')
  have := congrArg (valR ξ _) hc
  rw [valR_map' _ _ h1, valR_mul' _ _ h1, valR_map' _ _ h1] at this
  rw [this, hg, valR_pow' _ _ h1, valR_map' _ _ h1, valR_id_app _ _ h2]

end GlobalTheory.SecValLC
