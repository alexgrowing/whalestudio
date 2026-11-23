import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmProd
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugationByInvolution
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AntidiagonalConjugation
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SignActionTheta

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Topology

namespace UpperTheory.V.Loc.OrdinaryDeformation

section Group

variable {G R S T U : Type} [Group G] [CommRing R] [CommRing S] [CommRing T] [CommRing U] {m : ℕ}

theorem map_conjBy (f : R →+* S) (h : GL (Fin m) R) (r : G →* GG m R) :
    (GG.map f).comp (conjBy h r) = conjBy (Matrix.GeneralLinearGroup.map f h) ((GG.map f).comp r) :=
  _root_.UpperTheory.Reformulated.B.SignActionTheta.map_conjBy f h r

theorem conjBy_one (r : G →* GG m R) : conjBy 1 r = r := by
  refine MonoidHom.ext fun g => ?_
  simp [conjBy]

theorem conjBy_inv_conjBy (h : GL (Fin m) R) (r : G →* GG m R) : conjBy h⁻¹ (conjBy h r) = r := by
  refine MonoidHom.ext fun g => ?_
  change GG.ofGL h⁻¹ * (GG.ofGL h * r g * (GG.ofGL h)⁻¹) * (GG.ofGL h⁻¹)⁻¹ = r g
  rw [map_inv]
  group

theorem conjBy_right (h : GL (Fin m) R) (r : G →* GG m R) (g : G) : (conjBy h r g).right = (r g).right :=
  _root_.UpperTheory.Reformulated.B.ConjugationByInvolution.conjBy_right h r g

theorem conjBy_left (h : GL (Fin m) R) (r : G →* GG m R) (g : G) :
    (conjBy h r g).left = h * (r g).left * sgnAct m R (r g).right h⁻¹ :=
  _root_.UpperTheory.Reformulated.B.AntidiagonalConjugation.conjBy_left h r g

theorem gg_ext (f₁ : R →+* S) (f₂ : R →+* T) (hf : ∀ x y, f₁ x = f₁ y → f₂ x = f₂ y → x = y) {x y : GG m R}
    (h₁ : GG.map f₁ x = GG.map f₁ y) (h₂ : GG.map f₂ x = GG.map f₂ y) : x = y :=
  SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => hf _ _
    (congrFun (congrFun (congrArg GG.mat h₁) a) b) (congrFun (congrFun (congrArg GG.mat h₂) a) b)))
    (congrArg SemidirectProduct.right h₁ :)

theorem glue_GL (f₁ : R →+* S) (f₂ : R →+* T) (q₁ : S →+* U) (q₂ : T →+* U)
    (hf : ∀ x y, f₁ x = f₁ y → f₂ x = f₂ y → x = y)
    (hq : ∀ s t, q₁ s = q₂ t → ∃ x, f₁ x = s ∧ f₂ x = t) (n₁ : GL (Fin m) S) (n₂ : GL (Fin m) T)
    (h : Matrix.GeneralLinearGroup.map q₁ n₁ = Matrix.GeneralLinearGroup.map q₂ n₂) :
    ∃ n : GL (Fin m) R, Matrix.GeneralLinearGroup.map f₁ n = n₁ ∧ Matrix.GeneralLinearGroup.map f₂ n = n₂ := by
  have h' : Matrix.GeneralLinearGroup.map q₁ n₁⁻¹ = Matrix.GeneralLinearGroup.map q₂ n₂⁻¹ := by
    rw [map_inv, map_inv, h]
  choose X hX1 hX2 using fun a b => hq ((n₁ : Matrix (Fin m) (Fin m) S) a b) ((n₂ : Matrix (Fin m) (Fin m) T) a b)
    (congrArg (fun x : GL (Fin m) U => (x : Matrix (Fin m) (Fin m) U) a b) h)
  choose Y hY1 hY2 using fun a b => hq (((n₁⁻¹ : GL (Fin m) S) : Matrix (Fin m) (Fin m) S) a b)
    (((n₂⁻¹ : GL (Fin m) T) : Matrix (Fin m) (Fin m) T) a b)
    (congrArg (fun x : GL (Fin m) U => (x : Matrix (Fin m) (Fin m) U) a b) h')
  have x1 : (Matrix.of X).map f₁ = n₁ := Matrix.ext hX1
  have x2 : (Matrix.of X).map f₂ = n₂ := Matrix.ext hX2
  have y1 : (Matrix.of Y).map f₁ = (n₁⁻¹ : GL (Fin m) S) := Matrix.ext hY1
  have y2 : (Matrix.of Y).map f₂ = (n₂⁻¹ : GL (Fin m) T) := Matrix.ext hY2
  have hM : ∀ A B : Matrix (Fin m) (Fin m) R, A.map f₁ = B.map f₁ → A.map f₂ = B.map f₂ → A = B :=
    fun A B h1 h2 => Matrix.ext fun a b => hf _ _ (congrFun (congrFun h1 a) b) (congrFun (congrFun h2 a) b)
  refine ⟨⟨Matrix.of X, Matrix.of Y, hM _ _ ?_ ?_, hM _ _ ?_ ?_⟩, Units.ext x1, Units.ext x2⟩
  · rw [Matrix.map_mul, x1, y1, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.map_mul, x2, y2, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.map_mul, x1, y1, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.map_mul, x2, y2, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem glue_hom (f₁ : R →+* S) (f₂ : R →+* T) (q₁ : S →+* U) (q₂ : T →+* U)
    (hf : ∀ x y, f₁ x = f₁ y → f₂ x = f₂ y → x = y)
    (hq : ∀ s t, q₁ s = q₂ t → ∃ x, f₁ x = s ∧ f₂ x = t) (r₁ : G →* GG m S) (r₂ : G →* GG m T)
    (h : (GG.map q₁).comp r₁ = (GG.map q₂).comp r₂) :
    ∃ r : G →* GG m R, (GG.map f₁).comp r = r₁ ∧ (GG.map f₂).comp r = r₂ := by
  have hg : ∀ g, GG.map q₁ (r₁ g) = GG.map q₂ (r₂ g) := fun g => DFunLike.congr_fun h g
  choose n h1 h2 using fun g => glue_GL f₁ f₂ q₁ q₂ hf hq (r₁ g).left (r₂ g).left
    (congrArg SemidirectProduct.left (hg g))
  let x : G → GG m R := fun g => ⟨n g, (r₁ g).right⟩
  have e1 : ∀ g, GG.map f₁ (x g) = r₁ g := fun g => SemidirectProduct.ext (h1 g) rfl
  have e2 : ∀ g, GG.map f₂ (x g) = r₂ g := fun g =>
    SemidirectProduct.ext (h2 g) (congrArg SemidirectProduct.right (hg g) :)
  refine ⟨MonoidHom.mk' x fun g g' => gg_ext f₁ f₂ hf ?_ ?_, MonoidHom.ext e1, MonoidHom.ext e2⟩
  · rw [map_mul, e1, e1, e1, map_mul]
  · rw [map_mul, e2, e2, e2, map_mul]

theorem congOne_iff (f : R →+* S) (n : GL (Fin m) R) :
    CongOne (RingHom.ker f) n ↔ Matrix.GeneralLinearGroup.map f n = 1 := by
  have e : ∀ a b, f (((n : Matrix (Fin m) (Fin m) R) - 1) a b) =
      (Matrix.GeneralLinearGroup.map f n : Matrix (Fin m) (Fin m) S) a b - (1 : Matrix (Fin m) (Fin m) S) a b := by
    intro a b
    rw [Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
    congr 1
    split_ifs <;> simp
  refine ⟨fun h => Units.ext (Matrix.ext fun a b => sub_eq_zero.1 ((e a b).symm.trans (h a b))), fun h a b => ?_⟩
  rw [RingHom.mem_ker, e, h, Units.val_one, sub_self]

theorem map_sub_one (f : R →+* S) (n : GL (Fin m) R) (a b : Fin m) :
    ((Matrix.GeneralLinearGroup.map f n : Matrix (Fin m) (Fin m) S) - 1) a b =
      f (((n : Matrix (Fin m) (Fin m) R) - 1) a b) := by
  rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
  congr 1
  split_ifs <;> simp

theorem lift_lower (f : R →+* S) (hf : Function.Surjective f)
    (n' : GL (Fin 3) S) (hn : ∀ a b, 0 ≤ wt a b → ((n' : Matrix (Fin 3) (Fin 3) S) - 1) a b = 0) :
    ∃ n : GL (Fin 3) R, (∀ a b, 0 ≤ wt a b → ((n : Matrix (Fin 3) (Fin 3) R) - 1) a b = 0) ∧
      Matrix.GeneralLinearGroup.map f n = n' := by
  have hX : ∀ a b, ∃ x : R, (0 ≤ wt a b → x = 0) ∧ f x = ((n' : Matrix (Fin 3) (Fin 3) S) - 1) a b := by
    intro a b
    by_cases h : 0 ≤ wt a b
    · exact ⟨0, fun _ => rfl, by rw [map_zero, hn a b h]⟩
    · obtain ⟨x, hx⟩ := hf (((n' : Matrix (Fin 3) (Fin 3) S) - 1) a b)
      exact ⟨x, fun h' => absurd h' h, hx⟩
  choose X h0 hX using hX
  have hd : (Matrix.of X + 1).det = 1 := by
    have h00 := h0 0 0 (by decide)
    have h01 := h0 0 1 (by decide)
    have h02 := h0 0 2 (by decide)
    have h11 := h0 1 1 (by decide)
    have h12 := h0 1 2 (by decide)
    have h22 := h0 2 2 (by decide)
    simp [Matrix.det_fin_three, h00, h01, h02, h11, h12, h22]
  refine ⟨Matrix.GeneralLinearGroup.mk'' (Matrix.of X + 1) (by rw [hd]; exact isUnit_one), fun a b h => ?_, ?_⟩
  · change (Matrix.of X + 1 - 1) a b = 0
    rw [add_sub_cancel_right]
    exact h0 a b h
  · refine Units.ext (Matrix.ext fun a b => ?_)
    change f ((Matrix.of X + 1) a b) = _
    rw [Matrix.add_apply, map_add, Matrix.of_apply, hX, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

end Group

section Cont

variable {l : ℕ} [Fact l.Prime] {X : Type} [TopologicalSpace X]

theorem qcont_map {V W : Type} [AddCommGroup V] [Module ℚ_[l] V] [AddCommGroup W] [Module ℚ_[l] W]
    (f : V →ₗ[ℚ_[l]] W) {c : X → V} (h : QCont l c) : QCont l fun x => f (c x) := by
  letI : TopologicalSpace V := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  letI : TopologicalSpace W := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI : ContinuousAdd W := IsModuleTopology.toContinuousAdd ℚ_[l] W
  exact (IsModuleTopology.continuous_of_linearMap f).comp h

theorem qcont_pair {V W W' : Type} [AddCommGroup V] [Module ℚ_[l] V] [AddCommGroup W] [Module ℚ_[l] W]
    [AddCommGroup W'] [Module ℚ_[l] W'] (f : V →ₗ[ℚ_[l]] W) (f' : V →ₗ[ℚ_[l]] W')
    (hf : ∀ x y, f x = f y → f' x = f' y → x = y) {c : X → V} (h : QCont l fun x => f (c x))
    (h' : QCont l fun x => f' (c x)) : QCont l c := by
  obtain ⟨L, hL⟩ := (f.prod f').exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 fun x y e =>
    hf x y (congrArg Prod.fst e) (congrArg Prod.snd e))
  have h1 := qcont_map (L.comp (LinearMap.inl _ _ _)) h
  have h2 := qcont_map (L.comp (LinearMap.inr _ _ _)) h'
  letI : TopologicalSpace V := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  have h3 := Continuous.add (M := V) h1 h2
  have e : (fun x => (L.comp (LinearMap.inl _ _ _)) (f (c x)) + (L.comp (LinearMap.inr _ _ _)) (f' (c x))) = c := by
    funext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← map_add]
    simpa using LinearMap.congr_fun hL (c x)
  rw [← e]
  exact h3

theorem cont_col {G B : Type} [Group G] [TopologicalSpace G] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (r : G →* GL (Fin 3) B) (h : ∀ a b, Continuous fun g => (r g : Matrix (Fin 3) (Fin 3) B) a b) :
    ContAction (colRep r) := by
  unfold ReciprocityTheory.Gal.ContAction
  refine continuous_pi fun a => ?_
  change Continuous fun p : G × (Fin 3 → B) => ∑ b, (r p.1 : Matrix (Fin 3) (Fin 3) B) a b * p.2 b
  exact continuous_finset_sum _ fun b _ => ((h a b).comp continuous_fst).mul ((continuous_apply b).comp continuous_snd)

end Cont

section Cr

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O)

theorem eta_open : IsOpen (D.η.ker : Set (GQ l)) := by
  have e : D.η.ker = GK D.Kv := Subgroup.ext fun g => D.η_ker g
  haveI := D.Kv.2
  rw [e]
  exact IntermediateField.fixingSubgroup_isOpen D.Kv.1

theorem eta_lc : IsLocallyConstant D.η := by
  refine IsLocallyConstant.iff_isOpen_fiber_apply.2 fun x => ?_
  have e : D.η ⁻¹' {D.η x} = (fun g => x⁻¹ * g) ⁻¹' (D.η.ker : Set (GQ l)) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv,
      inv_mul_eq_one]
    exact eq_comm
  rw [e]
  exact (eta_open D).preimage (continuous_const.mul continuous_id)

theorem HL_emb : IsOpenEmbedding D.HL.subtype :=
  IsOpen.isOpenEmbedding_subtypeVal ((eta_open D).inter D.τ_open)

variable {D} {B B' C E : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B]
  [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [CommRing C] [Algebra ℚ_[l] C] [Module.Finite ℚ_[l] C]
  [CommRing E] {r₁ : GQ l →* GG 3 E}

theorem dcr_map (f : B →ₐ[ℚ_[l]] B') (hf : Function.Surjective f) {π : B →+* E} {π' : B' →+* E}
    (hπ : π'.comp (f : B →+* B') = π) {r : GQ l →* GG 3 B} (hr : D.InDcrAt π r₁ r) :
    D.InDcrAt π' r₁ ((GG.map (f : B →+* B')).comp r) := by
  have hc : ∀ a b, QCont l fun g => (((GG.map (f : B →+* B')).comp r) g).mat a b := fun a b =>
    qcont_map f.toLinearMap (hr.cont a b)
  refine ⟨hr.mult, ?_, hc, ?_⟩
  · rw [← hr.red, ← hπ]; rfl
  obtain ⟨ρ, hρ, hcr⟩ := hr.cr
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  letI : TopologicalSpace B' := moduleTopology ℚ_[l] B'
  haveI : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩
  haveI : IsTopologicalRing B' := IsModuleTopology.isTopologicalRing ℚ_[l] B'
  refine ⟨(Matrix.GeneralLinearGroup.map (f : B →+* B')).comp ρ, fun g => by rw [MonoidHom.comp_apply, hρ]; rfl, ?_⟩
  refine ((isCrys_isDR_sub_quot _ (HL_emb D) (colRep ρ) _ (cont_col _ fun a b => ?_) (cont_col _ fun a b => ?_)
    (f.toLinearMap.compLeft (Fin 3)) fun g x => ?_).2 (fun y => ?_)).1 hcr
  · simp only [hρ]
    exact Continuous.comp (hr.cont a b) continuous_subtype_val
  · simp only [MonoidHom.comp_apply, hρ]
    exact (Continuous.comp (hc a b) (continuous_subtype_val (p := fun g => g ∈ D.HL)) :)
  · funext a
    exact RingHom.map_mulVec (f : B →+* B') _ x a
  · choose x hx using fun a => hf (y a)
    exact ⟨x, funext hx⟩

theorem dcr_pair (f : C →ₐ[ℚ_[l]] B) (f' : C →ₐ[ℚ_[l]] B') (hf : ∀ x y, f x = f y → f' x = f' y → x = y)
    {π : B →+* E} {π' : B' →+* E} {r : GQ l →* GG 3 C} (hr : D.InDcrAt π r₁ ((GG.map (f : C →+* B)).comp r))
    (hr' : D.InDcrAt π' r₁ ((GG.map (f' : C →+* B')).comp r)) : D.InDcrAt (π.comp (f : C →+* B)) r₁ r := by
  have hc : ∀ a b, QCont l fun g => (r g).mat a b := fun a b =>
    qcont_pair f.toLinearMap f'.toLinearMap hf (hr.cont a b) (hr'.cont a b)
  have hm : HasMult D.η r := hr.mult
  refine ⟨hm, hr.red, hc, ?_⟩
  obtain ⟨ρ, hρ, hcr⟩ := hr.cr
  obtain ⟨ρ', hρ', hcr'⟩ := hr'.cr
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  letI : TopologicalSpace B' := moduleTopology ℚ_[l] B'
  haveI : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩
  haveI : IsTopologicalRing B' := IsModuleTopology.isTopologicalRing ℚ_[l] B'
  letI : TopologicalSpace C := moduleTopology ℚ_[l] C
  haveI : IsModuleTopology ℚ_[l] C := ⟨rfl⟩
  haveI : IsTopologicalRing C := IsModuleTopology.isTopologicalRing ℚ_[l] C
  have c1 : ContAction (resCoef ℚ_[l] (colRep ρ)) := cont_col ρ fun a b => by
    simp only [hρ]
    exact (Continuous.comp (hr.cont a b) (continuous_subtype_val (p := fun g => g ∈ D.HL)) :)
  have c2 : ContAction (resCoef ℚ_[l] (colRep ρ')) := cont_col ρ' fun a b => by
    simp only [hρ']
    exact (Continuous.comp (hr'.cont a b) (continuous_subtype_val (p := fun g => g ∈ D.HL)) :)
  have c3 : ContAction ((resCoef ℚ_[l] (colRep ρ)).prod (resCoef ℚ_[l] (colRep ρ'))) :=
    (Continuous.comp c1 (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (Continuous.comp c2 (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  have hp := (isCrys_isDR_prod _ (HL_emb D) _ _ c1 c2).1 hcr hcr'
  refine ⟨(glPart D.η r hm).comp (Subgroup.inclusion inf_le_left), fun g => rfl, ?_⟩
  refine ((isCrys_isDR_sub_quot _ (HL_emb D) _ _ (cont_col _ fun a b => ?_) c3
    ((f.toLinearMap.compLeft (Fin 3)).prod (f'.toLinearMap.compLeft (Fin 3))) fun g x => ?_).1
    (fun x y h => ?_)).1 hp
  · exact Continuous.comp (hc a b) continuous_subtype_val
  · refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
    · change _ = Matrix.mulVec (ρ g : Matrix (Fin 3) (Fin 3) B) _ a
      rw [hρ]
      exact RingHom.map_mulVec (f : C →+* B) _ x a
    · change _ = Matrix.mulVec (ρ' g : Matrix (Fin 3) (Fin 3) B') _ a
      rw [hρ']
      exact RingHom.map_mulVec (f' : C →+* B') _ x a
  · exact funext fun a => hf _ _ (congrFun (congrArg Prod.fst h) a) (congrFun (congrArg Prod.snd h) a)

theorem dcr_conj {π : B →+* E} {r : GQ l →* GG 3 B} (hr : D.InDcrAt π r₁ r) (n : GL (Fin 3) B)
    (hn : Matrix.GeneralLinearGroup.map π n = 1) : D.InDcrAt π r₁ (conjBy n r) := by
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  have hm : HasMult D.η (conjBy n r) := fun g => (conjBy_right n r g).trans (hr.mult g)
  have h0 : Continuous fun g => (r g).mat := continuous_matrix fun a b => hr.cont a b
  have hc : Continuous fun g => (conjBy n r g).mat := by
    have e : (fun g => (conjBy n r g).mat) = fun g => (n : Matrix (Fin 3) (Fin 3) B) * (r g).mat *
        ((sgnAct 3 B (D.η g) n⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) := by
      funext g
      rw [GG.mat, conjBy_left, hr.mult g]
      rfl
    rw [e]
    exact (continuous_const.mul h0).mul (IsLocallyConstant.comp (eta_lc D)
      fun s => ((sgnAct 3 B s n⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)).continuous
  refine ⟨hm, by rw [map_conjBy, hn, conjBy_one, hr.red], fun a b => hc.matrix_elem a b, ?_⟩
  obtain ⟨ρ, hρ, hcr⟩ := hr.cr
  have hv : ∀ g : D.HL, conjGL n ρ g = (conjBy n r g).left := fun g => by
    rw [conjBy_left, hr.mult g, show D.η g = 1 from g.2.1, sgnAct_one, ← hρ]
    rfl
  refine ⟨conjGL n ρ, hv, ?_⟩
  refine ((isCrys_isDR_sub_quot _ (HL_emb D) (colRep ρ) _ (cont_col _ fun a b => ?_) (cont_col _ fun a b => ?_)
    ((Matrix.toLin' (n : Matrix (Fin 3) (Fin 3) B)).restrictScalars ℚ_[l]) fun g x => ?_).2 (fun y => ?_)).1 hcr
  · simp only [hρ]
    exact Continuous.comp (hr.cont a b) continuous_subtype_val
  · simp only [hv]
    exact Continuous.comp (hc.matrix_elem a b) continuous_subtype_val
  · change Matrix.mulVec (n : Matrix (Fin 3) (Fin 3) B) (Matrix.mulVec (ρ g : Matrix (Fin 3) (Fin 3) B) x) =
      Matrix.mulVec ((n * ρ g * n⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)
        (Matrix.mulVec (n : Matrix (Fin 3) (Fin 3) B) x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
  · refine ⟨Matrix.mulVec ((n⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) y, ?_⟩
    change Matrix.mulVec (n : Matrix (Fin 3) (Fin 3) B) (Matrix.mulVec _ y) = y
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

variable [Algebra O E]

theorem dcr_of_dord {π : B →+* E} {r : GQ l →* GG 3 B} (hr : D.InDord π r) : D.InDcr π r := by
  obtain ⟨u, n, hu, hn, -, rfl⟩ := hr
  exact dcr_conj hu.toInDcrAt n ((congOne_iff π n).1 hn)

theorem dord_map (f : B →ₐ[ℚ_[l]] B') (hf : Function.Surjective f) {π : B →+* E} {π' : B' →+* E}
    (hπ : π'.comp (f : B →+* B') = π) {r : GQ l →* GG 3 B} (hr : D.InDord π r) :
    D.InDord π' ((GG.map (f : B →+* B')).comp r) := by
  obtain ⟨u, n, hu, hn, hn', rfl⟩ := hr
  refine ⟨(GG.map (f : B →+* B')).comp u, Matrix.GeneralLinearGroup.map (f : B →+* B') n,
    ⟨dcr_map f hf hπ hu.toInDcrAt, fun g a b h => ?_⟩, fun a b => ?_, fun a b h => ?_, map_conjBy _ n u⟩
  · change (f : B →+* B') ((u g).mat a b) = 0
    rw [hu.tri g a b h, map_zero]
  · rw [map_sub_one, RingHom.mem_ker, ← RingHom.comp_apply, hπ]
    exact hn a b
  · rw [map_sub_one, hn' a b h, map_zero]

end Cr

end UpperTheory.V.Loc.OrdinaryDeformation
