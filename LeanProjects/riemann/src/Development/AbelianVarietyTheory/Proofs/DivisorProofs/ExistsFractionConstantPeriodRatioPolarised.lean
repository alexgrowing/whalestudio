import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HalfRatio

variable {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
    {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}

theorem lamVal_change (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)) (hw : w.IsGen)
    {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z) {J₁ J₂ : (Z ⟶ B.left) → M.ι} {J₁' J₂' : (Z ⟶ B'.left) → M'.ι}
    (h₁ : Good M z J₁) (h₂ : Good M z J₂) (h₁' : Good M' z J₁') (h₂' : Good M' z J₂') :
    lamVal w p z J₁ J₁' =
      (∏ I, gm (p ≫ β₂ ≫ PrimCocycle.lamφ B I) z (M.U (J₁ (p ≫ β₂ ≫ PrimCocycle.lamφ B I)) ⊓ M.U (J₂ (p ≫ β₂ ≫ PrimCocycle.lamφ B I)))
          (M.g (J₁ (p ≫ β₂ ≫ PrimCocycle.lamφ B I)) (J₂ (p ≫ β₂ ≫ PrimCocycle.lamφ B I))) ^ PrimCocycle.lamε I) *
      (∏ I, gm (p ≫ PrimCocycle.lamφ B' I) z (M'.U (J₁' (p ≫ PrimCocycle.lamφ B' I)) ⊓ M'.U (J₂' (p ≫ PrimCocycle.lamφ B' I)))
          (M'.g (J₁' (p ≫ PrimCocycle.lamφ B' I)) (J₂' (p ≫ PrimCocycle.lamφ B' I))) ^ PrimCocycle.lamε I)⁻¹ *
      lamVal w p z J₂ J₂' := by
  have mQ : ∀ {J : (Z ⟶ B.left) → M.ι}, Good M z J → p z ∈ LB.wchart (abelian₂ B M) (fun _ : PUnit => β₂)
      (fun _ I => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) := fun hJ =>
    Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun I => hJ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)
  have mQ' : ∀ {J : (Z ⟶ B.left) → M.ι}, Good M z J → (p ≫ β₂) z ∈ (abelian₂ B M).U
      (fun I => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) := fun hJ =>
    Set.mem_iInter.2 fun I => hJ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)
  have mD : ∀ {J' : (Z ⟶ B'.left) → M'.ι}, Good M' z J' → p z ∈ (abelian₂ B' M').U
      (fun I => J' (p ≫ (psum B' (x2 B') I.down).left)) := fun hJ =>
    hJ.mem (fun I : ULift (Finset (Fin 2)) => (psum B' (x2 B') I.down).left) p
  have mi : p z ∈ (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U
      (fun _ I => J₁ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₁' (p ≫ (psum B' (x2 B') I.down).left)) :=
    TopologicalSpace.Opens.mem_inf.2 ⟨mQ h₁, mD h₁'⟩
  have mj : p z ∈ (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U
      (fun _ I => J₂ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₂' (p ≫ (psum B' (x2 B') I.down).left)) :=
    TopologicalSpace.Opens.mem_inf.2 ⟨mQ h₂, mD h₂'⟩
  have e := congrArg (gm p z _) (hw (fun _ I => J₁ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₁' (p ≫ (psum B' (x2 B') I.down).left))
    (fun _ I => J₂ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₂' (p ≫ (psum B' (x2 B') I.down).left)))
  rw [gm_res p z _ (TopologicalSpace.Opens.mem_inf.2 ⟨mi, mj⟩), map_mul, gm_res p z _ (TopologicalSpace.Opens.mem_inf.2 ⟨mi, mj⟩)] at e
  refine e.trans (congrArg (· * _) ?_)
  have gQ := gm_linComb (abelian₂ B M) (fun _ : PUnit => β₂) (fun _ => 1) p z _ _ (mQ h₁) (mQ h₂)
  have gQ' := gm_linComb M (fun I : ULift (Finset (Fin 2)) => (psum B (x2 B) I.down).left) (fun I => (-1) ^ (2 - I.down.card)) (p ≫ β₂) z _ _ (mQ' h₁) (mQ' h₂)
  have gD := gm_linComb M' (fun I : ULift (Finset (Fin 2)) => (psum B' (x2 B') I.down).left) (fun I => (-1) ^ (2 - I.down.card)) p z _ _ (mD h₁') (mD h₂')
  rw [Fintype.prod_unique, zpow_one] at gQ
  simp only [Category.assoc] at gQ'
  erw [map_mul, map_inv, gm_res p z _ (TopologicalSpace.Opens.mem_inf.2 ⟨mi, mj⟩), gm_res p z _ (TopologicalSpace.Opens.mem_inf.2 ⟨mi, mj⟩), gQ, gQ', gD]

end GlobalTheory.HalfRatio

namespace GlobalTheory.HalfRatio
theorem ag1 {G : Type*} [CommGroup G] (a b c d : G) : (a⁻¹*b*c*d⁻¹) * (a*b⁻¹*c⁻¹*d) = 1 := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, ofMul_one]; abel
theorem ag2 {G : Type*} [CommGroup G] (A₂ B₂ C₂ TA TDl TQl TQt : G) (h1 : TA * TDl = 1) (h2 : TQl * TQt = 1) : (TA*A₂)⁻¹ * (TQl * TDl⁻¹ * B₂) * (TQt * C₂) = A₂⁻¹ * B₂ * C₂ := by
  rw [eq_inv_of_mul_eq_one_right h1, eq_inv_of_mul_eq_one_right h2]
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, inv_inv]; abel
end GlobalTheory.HalfRatio

namespace GlobalTheory.HalfRatio

theorem exists_unitOn (K : Type) [Field K] (z : Sp K) (r : ((Sp K).presheaf.stalk z)ˣ) :
    ∃ k : Kˣ, gm (𝟙 (Sp K)) z ⊤ (unitOn k) = r := by
  obtain ⟨U, hz, f, hf⟩ := TopCat.Presheaf.germ_exist (Sp K).presheaf r.val
  have hs : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain rfl : U = ⊤ := top_unique fun x _ => (Subsingleton.elim z x) ▸ hz
  have h0 : (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom f ≠ 0 := fun h => by
    have : f = 0 := ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply f).symm.trans
      ((congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom h).trans (map_zero _))
    rw [this, map_zero] at hf
    exact r.ne_zero hf.symm
  refine ⟨Units.mk0 _ h0, Units.ext ((gm_val _ z ⊤ trivial _).trans (Eq.trans ?_ hf))⟩
  exact congrArg ((Sp K).presheaf.germ ⊤ z hz).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply f)

theorem prod_neg {S : Scheme.{0}} {B : Over S} [GrpObj B] {T : Over S} (x y : T ⟶ B) {Z : Scheme.{0}} (κ : Z ⟶ T.left)
    {U : Type} [CommGroup U] (h : (Z ⟶ B.left) → U) : ∏ k, h (κ ≫ lamPts x y k) ^ negε k =
      (h (κ ≫ (x * y).left))⁻¹ * h (κ ≫ x.left) * h (κ ≫ y.left) * (h (κ ≫ (1 : T ⟶ B).left))⁻¹ := by
  simp only [Fin.prod_univ_four]
  simp [lamPts, negε]
end GlobalTheory.HalfRatio

namespace GlobalTheory.HalfRatio
theorem prod_tau {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a b : D.X) {U : Type} [CommGroup U]
    (h : ((TK R).left ⟶ D.P.A.left) → U) :
    ∏ k : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit, h (𝟙 _ ≫ Sum.elim (Sum.elim (Sum.elim (fun _ => ptK (D.c (a + b))) fun _ => ptK (D.c a))
        fun _ => ptK (D.c b)) (fun _ => (toUnit (TK R)).left ≫ eSec D.P.A) k) ^
      (Sum.elim (Sum.elim (Sum.elim (fun _ => -1) fun _ => - -1) fun _ => - -1) (fun _ => -1) k : ℤ) =
      (h (ptK (D.c (a + b))))⁻¹ * h (ptK (D.c a)) * h (ptK (D.c b)) * (h ((toUnit (TK R)).left ≫ eSec D.P.A))⁻¹ := by
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Category.id_comp]
  simp
end GlobalTheory.HalfRatio

namespace GlobalTheory.HalfRatio
variable {R : Type} [CommRing R] [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R'] {Q : Data R} {ρ : R →+* R'}
  {D : DegPre R'} {e : D.X ≃+ Q.X} {β : D.P.A.left ⟶ Q.B.left} {β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left}

theorem prod_cancel (hpb : IsGrpPullback D.P.A Q.B (spMap ρ) β) (hsq : IsSquare β β₂)
    (hc : ∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) {κ : (TK R').left ⟶ (TK R).left}
    (hκ : κ ≫ jK R = jK R' ≫ spMap ρ) {a b : D.X} {x y : TK R' ⟶ D.P.A} (hx : x = toUnit (TK R') ≫ D.c a)
    (hy : y = toUnit (TK R') ≫ D.c b) {U : Type} [CommGroup U] (H : ((TK R').left ⟶ Q.B.left) → U) :
    (∏ I, H ((lift x y).left ≫ β₂ ≫ PrimCocycle.lamφ Q.B I) ^ PrimCocycle.lamε I) *
      ∏ k, H (κ ≫ lamPts (toUnit (TK R) ≫ Q.c (e a)) (toUnit (TK R) ≫ Q.c (e b)) k) ^ negε k = 1 := by
  have hT : ∀ χ, (toUnit (TK R') ≫ D.c χ).left ≫ β = κ ≫ (toUnit (TK R) ≫ Q.c (e χ)).left := fun χ => by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hc χ]
    show jK R' ≫ spMap ρ ≫ _ = κ ≫ jK R ≫ _
    rw [← Category.assoc, ← hκ, Category.assoc]
  have c0 : D.c 0 = 1 := mul_eq_left.1 ((D.c_add 0 0).symm.trans (by rw [add_zero]))
  have q0 : Q.c 0 = 1 := mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))
  have hxy : toUnit (TK R') ≫ D.c (a + b) = x * y := by
    rw [hx, hy, ← MonObj.comp_mul]; exact congrArg (toUnit (TK R') ≫ ·) (D.c_add a b)
  let T' : Over (Sp R) := Over.mk ((TK R').hom ≫ spMap ρ)
  let up : (TK R' ⟶ D.P.A) → (T' ⟶ Q.B) := fun u => Over.homMk (u.left ≫ β)
    ((Category.assoc _ _ _).trans ((congrArg (u.left ≫ ·) hpb.1.w).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap ρ) (Over.w u)))))
  have f₁ : ((lift x y).left ≫ β₂) ≫ (fst Q.B Q.B).left = (up x).left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift x y).left ≫ ·) hsq.1).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun q : TK R' ⟶ D.P.A => q.left ≫ β) (lift_fst x y))))
  have f₂ : ((lift x y).left ≫ β₂) ≫ (snd Q.B Q.B).left = (up y).left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift x y).left ≫ ·) hsq.2).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun q : TK R' ⟶ D.P.A => q.left ≫ β) (lift_snd x y))))
  have hP : ((lift x y).left ≫ β₂) ≫ (G2 Q.B).hom = T'.hom :=
    (congrArg (_ ≫ ·) (Over.w (fst Q.B Q.B)).symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Q.B.hom) f₁).trans (Over.w (up x))))
  have hl : (lift (up x) (up y)).left = (lift x y).left ≫ β₂ := by
    have : lift (up x) (up y) = (Over.homMk _ hP : T' ⟶ G2 Q.B) :=
      CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (Over.OverMorphism.ext f₁.symm))
        ((lift_snd _ _).trans (Over.OverMorphism.ext f₂.symm))
    exact congrArg (fun q : T' ⟶ G2 Q.B => q.left) this
  have ux : (up x).left = κ ≫ (toUnit (TK R) ≫ Q.c (e a)).left := hx ▸ hT a
  have uy : (up y).left = κ ≫ (toUnit (TK R) ≫ Q.c (e b)).left := hy ▸ hT b
  have uxy : (up x * up y).left = κ ≫ (toUnit (TK R) ≫ Q.c (e a) * toUnit (TK R) ≫ Q.c (e b)).left := by
    refine (hpb.2 _ x y (up x) (up y) rfl rfl).trans ?_
    rw [← hxy, hT, map_add, Q.c_add, MonObj.comp_mul]
  have u1 : (1 : T' ⟶ Q.B).left = κ ≫ (1 : TK R ⟶ Q.B).left := by
    have h : up 1 * up 1 = up 1 := Over.OverMorphism.ext ((hpb.2 _ 1 1 (up 1) (up 1) rfl rfl).trans
      (congrArg (fun q : TK R' ⟶ D.P.A => q.left ≫ β) (_root_.mul_one 1)))
    have h' := hT 0
    rw [map_zero, c0, q0, MonObj.comp_one, MonObj.comp_one] at h'
    rw [← mul_eq_left.1 h]; exact h'
  have h := PrimCocycle.prod_lam (up x) (up y) H
  have h₀ : (∏ I, H ((lift x y).left ≫ β₂ ≫ PrimCocycle.lamφ Q.B I) ^ PrimCocycle.lamε I) = _ :=
    Eq.trans (Finset.prod_congr rfl fun I _ => congrArg (fun q => H q ^ PrimCocycle.lamε I)
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ PrimCocycle.lamφ Q.B I) hl.symm))) h
  rw [h₀, prod_neg _ _ κ H, ← ux, ← uy, ← uxy, ← u1, _root_.mul_comm]
  exact ag1 _ _ _ _

theorem ratio_indep (w : letI := D.P.isAb.comm; LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂))
    (hpb : IsGrpPullback D.P.A Q.B (spMap ρ) β) (hsq : IsSquare β β₂) (hw : w.IsGen)
    (hc : ∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) {κ : (TK R').left ⟶ (TK R).left}
    (hκ : κ ≫ jK R = jK R' ≫ spMap ρ) {a b : D.X} {x y : TK R' ⟶ D.P.A} (hx : x = toUnit (TK R') ≫ D.c a)
    (hy : y = toUnit (TK R') ≫ D.c b) :
    letI := D.P.isAb.comm
    ∀ z J₁ J₁' J₂ J₂', Good Q.M.L z J₁ → Good D.P.L z J₁' → Good Q.M.L z J₂ → Good D.P.L z J₂' →
      (val (D.tau a b) (𝟙 _) z J₁')⁻¹ * lamVal w (lift x y).left z J₁ J₁' * val (Q.tau (e a) (e b)) κ z J₁ =
      (val (D.tau a b) (𝟙 _) z J₂')⁻¹ * lamVal w (lift x y).left z J₂ J₂' * val (Q.tau (e a) (e b)) κ z J₂ := by
  letI := D.P.isAb.comm
  have hxy : toUnit (TK R') ≫ D.c (a + b) = x * y := by
    rw [hx, hy, ← MonObj.comp_mul]; exact congrArg (toUnit (TK R') ≫ ·) (D.c_add a b)
  intro z J₁ J₁' J₂ J₂' h₁ h₁' h₂ h₂'
  rw [GlobalTheory.UU.val_change (DVR.tau_isGen D a b) (𝟙 _) h₁' h₂', lamVal_change w hw _ z h₁ h₂ h₁' h₂',
    GlobalTheory.UU.val_change (Q.tau_gen _ _) κ h₁ h₂]
  refine ag2 _ _ _ _ _ _ _ ?_ ?_
  · refine (congrArg₂ (· * ·) ?_ (PrimCocycle.prod_lam x y
      fun q => gm q z (D.P.L.U (J₁' q) ⊓ D.P.L.U (J₂' q)) (D.P.L.g (J₁' q) (J₂' q)))).trans (ag1 _ _ _ _)
    have e₁ : ptK (D.c (a + b)) = (x * y).left := congrArg (fun q : TK R' ⟶ D.P.A => q.left) hxy
    have e₂ : (toUnit (TK R')).left ≫ eSec D.P.A = (1 : TK R' ⟶ D.P.A).left := rfl
    have e₃ : ptK (D.c a) = x.left := hx ▸ rfl
    have e₄ : ptK (D.c b) = y.left := hy ▸ rfl
    have gen : ∀ (U : Type) [CommGroup U] (H : ((TK R').left ⟶ D.P.A.left) → U),
        (H (ptK (D.c (a + b))))⁻¹ * H (ptK (D.c a)) * H (ptK (D.c b)) * (H ((toUnit (TK R')).left ≫ eSec D.P.A))⁻¹ =
        (H (x * y).left)⁻¹ * H x.left * H y.left * (H (1 : TK R' ⟶ D.P.A).left)⁻¹ := fun U _ H =>
      congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg (fun q => (H q)⁻¹) e₁) (congrArg H e₃))
        (congrArg H e₄)) (congrArg (fun q => (H q)⁻¹) e₂)
    exact (prod_tau D a b fun q => gm q z (D.P.L.U (J₁' q) ⊓ D.P.L.U (J₂' q)) (D.P.L.g (J₁' q) (J₂' q))).trans
      (gen _ fun q => gm q z (D.P.L.U (J₁' q) ⊓ D.P.L.U (J₂' q)) (D.P.L.g (J₁' q) (J₂' q)))
  · exact prod_cancel hpb hsq hc hκ hx hy fun q => gm q z (Q.M.L.U (J₁ q) ⊓ Q.M.L.U (J₂ q)) (Q.M.L.g (J₁ q) (J₂ q))

theorem ratio_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (β : D.P.A.left ⟶ Q.B.left) (β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left) (w : letI := D.P.isAb.comm; LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂)), IsGrpPullback D.P.A Q.B (spMap ρ) β → IsSquare β β₂ → w.IsGen → (∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) → ∀ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ → ∀ a b, ∃ k : (FractionRing R')ˣ, ∀ z J J', Good Q.M.L z J → Good D.P.L z J' → val (D.tau a b) (𝟙 _) z J' * gm (𝟙 (TK R').left) z ⊤ (unitOn k) = (letI := D.P.isAb.comm; lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J') * val (Q.tau (e a) (e b)) κ z J := by
  intro R _ _ R' _ _ Q ρ D e β β₂ w hpb hsq hw hc κ hκ a b
  letI := D.P.isAb.comm
  have indep := ratio_indep w hpb hsq hw hc hκ (a := a) (b := b) rfl rfl
  have hs : Subsingleton (TK R').left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R')))
  let z₀ : (TK R').left := (⊥ : PrimeSpectrum (FractionRing R'))
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.UU.exists_good_pt Q.M.isLB z₀
  obtain ⟨J₀', hJ₀'⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z₀
  obtain ⟨k, hk⟩ := exists_unitOn (FractionRing R') z₀ ((val (D.tau a b) (𝟙 _) z₀ J₀')⁻¹ *
    lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z₀ J₀ J₀' * val (Q.tau (e a) (e b)) κ z₀ J₀)
  refine ⟨k, fun z J J' hJ hJ' => ?_⟩
  obtain rfl : z = z₀ := Subsingleton.elim _ _
  have hk' : gm (𝟙 (TK R').left) z₀ ⊤ (unitOn k) = _ := hk.trans (indep _ _ _ _ _ hJ₀ hJ₀' hJ hJ')
  rw [hk', _root_.mul_assoc, mul_inv_cancel_left]
end GlobalTheory.HalfRatio
