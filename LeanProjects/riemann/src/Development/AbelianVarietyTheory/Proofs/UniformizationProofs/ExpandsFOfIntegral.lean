import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMoveMap

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaSpecialise

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange

theorem gs_pullOver {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of R')}
    {f : R →+* R'} {p : Y' ⟶ Y} (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) {φ' : K → (Y' ⟶ X)}
    (hφ : ∀ k, φ' k = p ≫ φ k) (s : SecOver π (LB.LinComb L φ ε)) (r : Z ⟶ Y') (z : Z) (j : K → L.ι)
    (hj : ∀ k, φ' k (r z) ∈ L.U (j k)) :
    gs r z (LB.wchart L φ' j) (LB.Sec.f (pullOver L ε hp hφ s) j) = gs (r ≫ p) z (LB.wchart L φ j) (LB.Sec.f s j) :=
  gs_pullFn hp _ _ r z (mem_wchart.2 hj)

section Act

variable {S₀ : Scheme.{0}} {A : Over S₀} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S₀}
  {S : Type} [CommRing S]

theorem lpow_ext (hL : L.IsLB) {s s' : LB.Sec (LPow A L k T)}
    (h : ∀ y J, Good L y J → secVal s (𝟙 _) y J = secVal s' (𝟙 _) y J) : s = s' :=
  sec_ext' (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) hL h

theorem secVal_add' (π : (T ⊗ A).left ⟶ Spec (CommRingCat.of S)) (s t : SecOver π (LPow A L k T))
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    secVal (s + t : SecOver π _) r z J = secVal s r z J + secVal t r z J :=
  sval_add' (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) (π := π) hJ r s t

theorem secVal_smul' (π : (T ⊗ A).left ⟶ Spec (CommRingCat.of S)) (c : S) (s : SecOver π (LPow A L k T))
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    secVal (c • s : SecOver π _) r z J = constVal (r ≫ π) z c * secVal s r z J :=
  sval_smul' (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) (π := π) hJ r c s

theorem exists_actMap (hL : L.IsLB) (θ : ThetaGrp A L k T) (q : T.left ⟶ Spec (CommRingCat.of S))
    (π : (T ⊗ A).left ⟶ Spec (CommRingCat.of S)) (hπ : π = (fst T A).left ≫ q) :
    ∃ a : SecOver π (LPow A L k T) →ₗ[S] SecOver π (LPow A L k T), Function.Injective a ∧
      ∀ s s', IsActOf A L k θ s s' ↔ a s = s' := by
  choose a ha using fun s : SecOver π (LPow A L k T) => exists_actVal hL θ s
  have e : (𝟙 _ ≫ (translT A θ.pt).left) ≫ π = 𝟙 _ ≫ π := by
    rw [hπ, Category.assoc, ← Category.assoc (translT A θ.pt).left, ← Over.comp_left, translT, lift_fst]
  refine ⟨{ toFun := a
            map_add' := fun s t => lpow_ext hL fun y J hJ => ?_
            map_smul' := fun c s => lpow_ext hL fun y J hJ => ?_ }, fun s t h => lpow_ext hL fun y J hJ => ?_,
    fun s s' => ⟨fun H => lpow_ext hL fun y J hJ => (ha s _ _ y J hJ).trans (actVal_of_isActOf H _ _ y J hJ).symm,
      fun H => H ▸ (ha s).isActOf hL⟩⟩
  · refine (ha _ _ _ y J hJ).trans (Eq.trans ?_ (secVal_add' π _ _ _ y hJ).symm)
    rw [secVal_add' π _ _ _ y hJ, mul_add]
    exact (congrArg₂ (· + ·) (ha s _ _ y J hJ) (ha t _ _ y J hJ)).symm
  · refine (ha _ _ _ y J hJ).trans (Eq.trans ?_ (secVal_smul' π _ _ _ y hJ).symm)
    rw [secVal_smul' π _ _ _ y hJ, mul_left_comm, e]
    exact (congrArg _ (ha s _ _ y J hJ)).symm
  · have h : a s = a t := h
    have r : (translT A θ.pt⁻¹).left ≫ (translT A θ.pt).left = 𝟙 _ := by
      rw [← Over.comp_left, translT_mul, mul_inv_cancel, translT_one, Over.id_left]
    have e₁ := ha s _ (translT A θ.pt⁻¹).left y J hJ
    have e₂ := ha t _ (translT A θ.pt⁻¹).left y J hJ
    rw [r] at e₁ e₂
    rw [h] at e₁
    exact (Units.mul_right_inj _).1 (e₁.symm.trans e₂)

theorem exists_act_ratio (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {F : Type} [Field F]
    {t : Spec (CommRingCat.of F) ⟶ S₀} (θ θ' : ThetaGrp A L k (Over.mk t)) (h : θ.pt = θ'.pt)
    (π : (Over.mk t ⊗ A).left ⟶ Spec (CommRingCat.of F)) (hπ : π = (fst (Over.mk t) A).left) :
    ∃ c : F, c ≠ 0 ∧ ∀ s s₁ s₂ : SecOver π (LPow A L k (Over.mk t)), IsActOf A L k θ s s₁ →
      IsActOf A L k θ' s s₂ → s₂ = c • s₁ := by
  obtain ⟨u, hu⟩ := ThetaAct.exists_ratio hG hA hL θ θ' h
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 u.val
  refine ⟨c, ?_, fun s s₁ s₂ h₁ h₂ => lpow_ext hL fun y J hJ => ?_⟩
  · rintro rfl
    have : Nontrivial Γ((Over.mk t).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
    exact u.ne_zero (hc.symm.trans (map_zero _))
  · refine (actVal_of_isActOf h₂ _ _ y J hJ).trans (Eq.trans ?_ (secVal_smul' π _ _ _ y hJ).symm)
    rw [actVal_of_isActOf h₁ _ _ y J hJ, ← _root_.mul_assoc, h]
    refine congrArg (· * _) ((hu _ _ y J hJ).trans (congrArg (· * _) ?_))
    rw [hπ, ← hc]; rfl

end Act

section Side

variable {S₀ S₁ : Scheme.{0}} {G : Over S₀} [GrpObj G] {A : Over S₁} [GrpObj A]
  {f : S₁ ⟶ S₀} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S₁} {T₀ : Over S₀} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}

include hp hτ in

theorem exists_psi : ∃ ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left, IsPullback ψ (fst T A).left (fst T₀ G).left τ ∧
    ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ ∧ ψ = (psiO hp τ hτ).left := by
  refine ⟨(psiO hp τ hτ).left, ?_, psi_snd hp τ hτ, rfl⟩
  have h₀ : IsPullback (snd T₀ G).left (fst T₀ G).left G.hom T₀.hom := (IsPullback.of_hasPullback _ _).flip
  have h₁ : IsPullback (snd T A).left (fst T A).left A.hom T.hom := (IsPullback.of_hasPullback _ _).flip
  refine IsPullback.of_right ?_ (psi_fst hp τ hτ) h₀
  rw [psi_snd, hτ]
  exact h₁.paste_horiz hp.1

theorem exists_theta_side (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) (k : ℤ)
    (x : T ⟶ A) (θ₀ : ThetaGrp G L₀ k T₀) (hx : τ ≫ θ₀.pt.left = x.left ≫ φ)
    {ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left} (hψ : ψ = (psiO hp τ hτ).left) :
    ∃ θ : ThetaGrp A L₁ k T, θ.pt = x ∧ ∀ (s₀ s₀' : LB.Sec (LPow G L₀ k T₀)) (s s' : LB.Sec (LPow A L₁ k T)),
      PSec w (fun _ : Fin 1 => (snd T A).left) (fun _ => (snd T₀ G).left) (fun _ => k) ψ s s₀ →
      PSec w (fun _ : Fin 1 => (snd T A).left) (fun _ => (snd T₀ G).left) (fun _ => k) ψ s' s₀' →
      IsActOf G L₀ k θ₀ s₀ s₀' → IsActOf A L₁ k θ s s' := by
  obtain ⟨θ, rfl, hm⟩ := exists_theta_move hp τ hτ hL₀ hL₁ w hw k x θ₀ hx
  have hm : PMaps w ![(snd T A).left, (translPt A θ.pt).left] ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![k, -k]
      θ.φ θ₀.φ ψ := hψ ▸ hm
  have c₁ : (snd T A).left ≫ φ = ψ ≫ (snd T₀ G).left := hψ ▸ (psi_snd hp τ hτ).symm
  have c₂ : (translPt A θ.pt).left ≫ φ = ψ ≫ (translPt G θ₀.pt).left := hψ ▸ (psi_tr hp τ hτ _ _ hx).symm
  have c₃ : (translT A θ.pt).left ≫ ψ = ψ ≫ (translT G θ₀.pt).left := hψ ▸ psi_transl hp τ hτ _ _ hx
  refine ⟨θ, rfl, fun s₀ s₀' s s' m m' H => (ThetaAct.isActOf_iff hL₁ θ s s').2 fun y J hJ => ?_⟩
  choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
  have hJ₀ : Good L₀ y J₀ := hJ₀
  have c : ∀ _ : Fin 1, (snd T A).left ≫ φ = ψ ≫ (snd T₀ G).left := fun _ => c₁
  have a := actVal_of_isActOf H _ (𝟙 _ ≫ ψ) y J₀ hJ₀
  have b := ExpTrans.gen_val w _ _ _ _ (fun i => by
    fin_cases i
    · exact c₁
    · exact c₂) _ _ hm y hJ₀ hJ
  have d := ExpTrans.sec_val w _ _ _ _ c _ _ (𝟙 _) y (m' _ (𝟙 _) y) hJ₀ hJ
  have e := ExpTrans.sec_val w _ _ _ _ c _ _ (𝟙 _ ≫ (translT A θ.pt).left) y (m _ _ y) hJ₀ hJ
  have g : (𝟙 _ ≫ ψ) ≫ (translT G θ₀.pt).left =
      (𝟙 _ ≫ (translT A θ.pt).left) ≫ ψ := by
    rw [Category.assoc, Category.assoc, c₃]
  rw [g] at a
  rw [Fin.prod_univ_one] at d e
  rw [Fin.prod_univ_two] at b
  rw [Category.assoc _ _ (snd T A).left, translT_snd_left, Category.id_comp (translPt A θ.pt).left] at e
  rw [Category.id_comp (snd T A).left] at d
  have b' : thetaVal θ₀ (𝟙 _ ≫ ψ) y J₀ = ExpTrans.om w y J₀ J (snd T A).left ^ k *
      ExpTrans.om w y J₀ J (translPt A θ.pt).left ^ (-k) * thetaVal θ (𝟙 _) y J := by
    rw [Category.id_comp]; exact b
  have z := d.symm.trans (a.trans (congrArg₂ (· * ·) (congrArg Units.val b') e))
  refine (ExpTrans.om w y J₀ J (snd T A).left ^ k).mul_right_inj.1 (z.trans ?_)
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, zpow_neg, mul_right_comm _ _⁻¹,
    inv_mul_cancel_right]
  rfl

end Side

section Phi

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem eq_zero_of_phiVal {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (s : Fam D F k)
    (h : PhiVal p w s.s (0 : Fam D F k).s) : s = 0 := by
  have := D.P.isAb.comm
  have r : DegPre.trPt D F p.g.b⁻¹ ≫ DegPre.trPt D F p.g.b = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, tr_fst, Category.id_comp]
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (tr_pr D F _)).trans ?_)
      rw [MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, _root_.mul_assoc, ← MonObj.comp_mul, inv_mul_cancel,
        MonObj.comp_one, _root_.mul_one, Category.id_comp]
  refine fam_ext fun α j => sec_ext_val D.P.isLB (fun y J hJ => ?_) j
  have e := h α _ rfl _ (DegPre.trPt D F p.g.b⁻¹) y J hJ
  rw [r] at e
  have z : ∀ β (r : (DegPre.BF D F).left ⟶ (DegPre.BF D F).left), sval ((0 : Fam D F k).s β) r y J = 0 := fun β r =>
    sval_zero' (π := famBase D F) hJ r
  rw [z] at e ⊢
  exact (Units.mul_left_eq_zero _).1 e.symm

end Phi

section Expand

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem expandsF_of_integral {k : ℕ}
    {w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))}
    {u : LB.Iso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R)))}
    (hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ A.A.left) (z : Z) (j : U.LG.L.ι) (i : A.L.ι),
      (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) (f z) ∈ U.LG.L.U j → f z ∈ A.L.U i →
      gw u f z j i = isoVal w (f ≫ U.gen.inv.left) z j i)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hE : ∀ e, U.ExpandsAt e k σ f) (s : Fam D.toPre F k)
    (hs : ∀ α y J, Good D.toPre.P.L y J →
      sval (s.s α) (𝟙 _) y J = sval (f α) (𝟙 _ ≫ (DegPre.prB D.toPre F).left) y J)
    (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)))
    (ht : PSec u (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))
      ((snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) t σ) :
    U.ExpandsF F k w t s := by
  have h₂ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)
  have n₃ : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left]
  have h₃ : ((𝟙 _ ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left) ≫ U.gen.inv.left =
      𝟙 _ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
    rw [Category.id_comp, Category.id_comp, h₂, Category.assoc, n₃, Category.comp_id]
  have h₄ : (𝟙 _ ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      (𝟙 _ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R) := by
    rw [← h₃]; simp only [Category.assoc]
  have one : ∀ {Y : Scheme.{0}} (π : Y ⟶ Spec (CommRingCat.of F)) (y : Y), gs (𝟙 Y) y ⊤ (scal π (1 : F)) = 1 :=
    fun π y => by simp only [gs_eq _ y ⊤ trivial, scal, map_one]
  refine ⟨extendSec U F k (genericSec U k σ), (isoRelM_iff w _ k _ h₂ _ (Category.id_comp _) _ _).2
    fun y i₂ i₁ a₂ a₁ => ?_, 1, fun _ => 1, fun _ => σ, fun _ => f, fun _ => hE,
    (secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => ?_,
    fun α => (secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_⟩
  · have b₂ := (congrArg (fun q : _ ⟶ G.left => q y ∈ U.LG.L.U i₂) h₄).mpr a₂
    have b₁ := (congrArg (fun q : _ ⟶ A.A.left => q y ∈ A.L.U i₁) h₂).mpr a₁
    have e := ht _ (𝟙 _ ≫ (U.genF F).left) y (fun _ => i₂) (fun _ => i₁) (fun _ => b₂) (fun _ => b₁)
    rw [Fin.prod_univ_one, hu _ ((𝟙 _ ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left) y i₂ i₁ b₂ b₁, h₃, h₄] at e
    refine Eq.trans ?_ e
    rw [Category.id_comp (𝟙 _)]
    exact (gs_pullOver (isPullback_groupBase F).w (fun _ => rfl) (genericSec U k σ) (𝟙 _) y (fun _ => i₂)
      (fun _ => a₂)).trans (gs_pullOver (p := pullback.fst G.hom (jK R)) pullback.condition
        (fun _ => (Category.comp_id _).symm) σ _ y (fun _ => i₂) (fun _ => a₂))
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
      (congrArg (fun q => sval σ q y J) (Category.assoc _ _ _)))
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact hs α y J hJ

end Expand

end GlobalTheory.ThetaSpecialise
