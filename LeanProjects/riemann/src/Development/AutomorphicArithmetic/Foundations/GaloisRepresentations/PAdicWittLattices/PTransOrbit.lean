import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntIntCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem pol_step {S : Scheme.{0}} {A₁ A₂ A : Over S} [GrpObj A₁] [IsCommMonObj A₁] [GrpObj A₂] [IsCommMonObj A₂]
    [GrpObj A] [IsCommMonObj A] {P₁ : LB (G2 A₁).left} {P₂ : LB (G2 A₂).left} {P : LB (G2 A).left}
    (h₁ : P₁.IsLB) (h₂ : P₂.IsLB) (h : P.IsLB) (θ : A₁ ⟶ A₂) (ψ₁ : A₁ ⟶ A) (ψ₂ : A₂ ⟶ A) (e : θ ≫ ψ₂ = ψ₁)
    (i₁ : LBIso (Hecke.lbPow P₁ 1) (P.pull (Hecke.sq2 ψ₁))) (i₂ : LBIso (Hecke.lbPow P₂ 1) (P.pull (Hecke.sq2 ψ₂))) :
    LBIso (Hecke.lbPow P₁ 1) (P₂.pull (Hecke.sq2 θ)) := by
  have pw : ∀ {X : Scheme} (L : LB X), L.IsLB → (Hecke.lbPow L 1).IsLB := by
    intro X L hL
    unfold Hecke.lbPow
    exact LB.isLB_linComb hL _ _
  have c₁ := (GlobalTheory.CechPic.cls_eq_iff (pw P₁ h₁) (pull_isLB h (Hecke.sq2 ψ₁))).mpr i₁
  have c₂ := (GlobalTheory.CechPic.cls_eq_iff (pw P₂ h₂) (pull_isLB h (Hecke.sq2 ψ₂))).mpr i₂
  rw [Hecke.Comp.cls_lbPow' h₁ 1 (pw P₁ h₁), one_smul] at c₁
  rw [Hecke.Comp.cls_lbPow' h₂ 1 (pw P₂ h₂), one_smul] at c₂
  rw [GlobalTheory.CechPic.cls_pull h] at c₁ c₂
  apply (GlobalTheory.CechPic.cls_eq_iff (pw P₁ h₁) (pull_isLB h₂ (Hecke.sq2 θ))).mp
  rw [Hecke.Comp.cls_lbPow' h₁ 1 (pw P₁ h₁), one_smul, GlobalTheory.CechPic.cls_pull h₂, c₁, c₂, ← e,
    Hecke.Comp.grpSchemeSquareProductMap_comp, GlobalTheory.CechPic.pull_comp]

private theorem isMonHom_inv' {C : Type*} [Category C] [MonoidalCategory C] {A B : C} [MonObj A] [MonObj B]
    (f : A ⟶ B) [IsIso f] [IsMonHom f] : IsMonHom (inv f) := by
  have : IsMonHom (asIso f).inv := inferInstance
  simpa using this

theorem UpperTheory.Gal.G3.pTransOrbit :
    MultBasic → RelComp → TateDiff → TateTwist → KNCong → TransIso → TransOrbit := by
  intro hMB hRC hTD hTT hKN hTI p _ D G L R _ _ gb k _ _ s N' N o₁ o₂ o ψ₁ ψ₂ h₁ h₂
  have one_mem : (1 : G.GAf) ∈ L.KN 1 := (L.KN 1).one_mem
  have kn1 : ∀ {M : ℕ} {g : G.GAf}, g ∈ L.KN M → g ∈ L.KN 1 :=
    fun hg => UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hg
  haveI : IsIso ψ₁ := hTI p D G L R gb _ s _ _ o₁ o ψ₁ 1 one_mem h₁
  haveI : IsIso ψ₂ := hTI p D G L R gb _ s _ _ o₂ o ψ₂ 1 one_mem h₂
  unfold UpperTheory.Gal.Int.Geo.IsTrans at h₁ h₂
  haveI hm₁ : IsMonHom ψ₁ := h₁.1
  haveI hm₂ : IsMonHom ψ₂ := h₂.1
  haveI hmi₁ : IsMonHom (inv ψ₁) := isMonHom_inv' ψ₁
  haveI hmi₂ : IsMonHom (inv ψ₂) := isMonHom_inv' ψ₂
  have hNpos : 0 < (N' : ℕ) := by
    have := N'.2.1
    omega
  have hNcop : (N' : ℕ).Coprime p := N'.2.2
  have flip : ∀ {X Y : Over (Sp k)} (a : X ⟶ X) (b : Y ⟶ Y) (ψ : X ⟶ Y) [IsIso ψ],
      a ≫ ψ = ψ ≫ b → b ≫ inv ψ = inv ψ ≫ a := by
    intro X Y a b ψ _ h
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have rev : ∀ {k' : Type} [Field k'] {t : Sp k' ⟶ Sp k} (I : UpperTheory.Gal.Int.Geo.TIso o₂ t)
      (J : UpperTheory.Gal.Int.Geo.TIso o t),
      UpperTheory.Gal.G3.Rel L I J ψ₂ 1 → UpperTheory.Gal.G3.Rel L J I (inv ψ₂) 1 := by
    intro k' _ t I J hIJ n hn hc x y
    rw [IsIso.comp_inv_eq]
    refine (eq_comm.trans (hIJ n hn hc y x)).trans ?_
    simp only [map_one, Module.End.one_apply]
    constructor
    · rintro ⟨v, hv, e⟩
      exact ⟨-v, neg_mem hv, by rw [e, smul_neg, add_neg_cancel_right]⟩
    · rintro ⟨v, hv, e⟩
      exact ⟨-v, neg_mem hv, by rw [e, smul_neg, add_neg_cancel_right]⟩
  have key : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (t : Sp k' ⟶ Sp k) (β' : R →+* k'),
      t ≫ s = spMap β' →
      ∃ (I' : UpperTheory.Gal.Int.Geo.TIso o₁ t) (I'' : UpperTheory.Gal.Int.Geo.TIso o₂ t),
        UpperTheory.Gal.G3.Ind o₁ I' ∧ UpperTheory.Gal.G3.Ind o₂ I'' ∧
          ∃ w ∈ L.KN N, UpperTheory.Gal.G3.Rel L I' I'' (ψ₁ ≫ inv ψ₂) w := by
    intro k' _ _ t β' ht
    obtain ⟨I₁', I₁'', a₁, b₁, r₁⟩ := h₁.2.2.2.2 k' t β' ht
    obtain ⟨I₂', I₂'', a₂, b₂, r₂⟩ := h₂.2.2.2.2 k' t β' ht
    obtain ⟨w, hw, rr⟩ := hTD p D G L R gb _ s N o k' t I₁'' I₂'' b₁ b₂
    have s1 := (hRC p D G L R gb _ s _ _ _ o₁ o o k' t I₁' I₁'' I₂'' ψ₁ (𝟙 _) 1 w hm₁ inferInstance
      (UpperTheory.Gal.Int.Geo.integ_of_mem (kn1 hw))).2 r₁ rr
    have s2 := (hRC p D G L R gb _ s _ _ _ o₁ o o₂ k' t I₁' I₂'' I₂' (ψ₁ ≫ 𝟙 _) (inv ψ₂) (w * 1) 1
      inferInstance hmi₂ (UpperTheory.Gal.Int.Geo.integ_of_mem one_mem)).2 s1 (rev I₂' I₂'' r₂)
    refine ⟨I₁', I₂', a₁, a₂, w, hw, ?_⟩
    rw [Category.comp_id, _root_.mul_one, _root_.one_mul] at s2
    exact s2
  obtain ⟨I₀', I₀'', hI₀', hI₀'', w₀, hw₀, r₀⟩ :=
    key k (𝟙 (Sp k)) (Spec.preimage s).hom (by simp [spMap])
  obtain ⟨c₁, hc₁, ⟨i₁⟩, t₁, t₁', x1, x2, x3, x4⟩ := h₁.2.2.2.1
  have e₁ : c₁ = 1 := (hMB p).1 _ c₁ 1 hc₁ (Nat.coprime_one_left p) ⟨t₁, t₁', x1, x2, x3, x4⟩
    ((hMB p).2.2 D G L 1 one_mem)
  subst e₁
  obtain ⟨c₂, hc₂, ⟨i₂⟩, t₂, t₂', y1, y2, y3, y4⟩ := h₂.2.2.2.1
  have e₂ : c₂ = 1 := (hMB p).1 _ c₂ 1 hc₂ (Nat.coprime_one_left p) ⟨t₂, t₂', y1, y2, y3, y4⟩
    ((hMB p).2.2 D G L 1 one_mem)
  subst e₂
  refine ⟨w₀, hw₀, ψ₁ ≫ inv ψ₂, ?_, by simp⟩
  unfold UpperTheory.Gal.Int.Geo.IsTrans
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · intro c
    rw [← Category.assoc, h₁.2.1 c, Category.assoc, flip _ _ ψ₂ (h₂.2.1 c)]
    simp only [Category.assoc]
  · refine ⟨ψ₂ ≫ inv ψ₁, 1, inferInstance, ?_, by simp, by simp, Nat.coprime_one_left p⟩
    intro c
    rw [← Category.assoc, h₂.2.1 c, Category.assoc, flip _ _ ψ₁ (h₁.2.1 c)]
    simp only [Category.assoc]
  · exact ⟨1, Nat.coprime_one_left p,
      ⟨pol_step o₁.isLB o₂.isLB o.isLB (ψ₁ ≫ inv ψ₂) ψ₁ ψ₂ (by simp) i₁ i₂⟩,
      (hMB p).2.2 D G L w₀ (kn1 hw₀)⟩
  · intro k' _ _ t β' ht
    obtain ⟨I', I'', hI', hI'', w, hw, r⟩ := key k' t β' ht
    have A : ∀ x y : D.La, (∃ v ∈ LaHat D, (L.actG w₀) (inAf D x) = inAf D y + (N' : ℕ) • v) →
        ∃ v ∈ LaHat D, (L.actG w) (inAf D x) = inAf D y + (N' : ℕ) • v := by
      intro x y hxy
      have e0 := (r₀ N' hNpos hNcop x y).mpr hxy
      apply (r N' hNpos hNcop x y).mp
      rw [← hI₀' x, ← hI₀'' y] at e0
      rw [← hI' x, ← hI'' y]
      have hu : toUnit (Over.mk t) =
          Over.homMk (U := Over.mk t) (V := Over.mk (𝟙 (Sp k))) t (by simp) ≫ toUnit (Over.mk (𝟙 (Sp k))) :=
        toUnit_unique _ _
      rw [hu]
      simp only [Category.assoc] at e0 ⊢
      rw [e0]
    have cong : ∀ x : D.La, ∃ m ∈ LaHat D,
        (L.actG (w₀ * w⁻¹)) (inAf D x) = inAf D x + (N' : ℕ) • m := by
      intro x
      have hwi : w⁻¹ ∈ L.KN 1 := (L.KN 1).inv_mem (kn1 hw)
      obtain ⟨x', m, hm, hz⟩ := exists_inAf_add_nsmul_of_mem_laHat p D N' hNpos hNcop _
        (UpperTheory.Gal.Int.Geo.integ_of_mem hwi _ (GlobalTheory.HeckeApprox.inAf_mem D x))
      obtain ⟨y', m₁, hm₁, e₁⟩ := exists_inAf_add_nsmul_of_mem_laHat p D N' hNpos hNcop _
        (UpperTheory.Gal.Int.Geo.integ_of_mem (kn1 hw₀) _ (GlobalTheory.HeckeApprox.inAf_mem D x'))
      obtain ⟨m₂, hm₂, e₂⟩ := A x' y' ⟨m₁, hm₁, e₁⟩
      have hback : (L.actG w) ((L.actG w⁻¹) (inAf D x)) = inAf D x := by
        rw [← Module.End.mul_apply, ← map_mul, _root_.mul_inv_cancel, map_one, Module.End.one_apply]
      refine ⟨m₁ - m₂ + ((L.actG w₀) m - (L.actG w) m), ?_, ?_⟩
      · exact add_mem (sub_mem hm₁ hm₂) (sub_mem (UpperTheory.Gal.Int.Geo.integ_of_mem (kn1 hw₀) _ hm)
          (UpperTheory.Gal.Int.Geo.integ_of_mem (kn1 hw) _ hm))
      · rw [map_mul, Module.End.mul_apply, hz, map_add, map_nsmul, e₁]
        rw [hz, map_add, map_nsmul, e₂] at hback
        rw [← hback]
        simp only [smul_add, smul_sub]
        abel
    have hv : w₀ * w⁻¹ ∈ L.KN (N' : ℕ) :=
      hKN p D G L N' hNpos hNcop _ (mul_mem (kn1 hw₀) (inv_mem (kn1 hw))) cong
    obtain ⟨J, hJ, rJ⟩ := hTT p D G L R gb _ s N' o₂ k' t I'' hI'' _ hv
    refine ⟨I', J, hI', hJ, ?_⟩
    have := (hRC p D G L R gb _ s _ _ _ o₁ o₂ o₂ k' t I' I'' J (ψ₁ ≫ inv ψ₂) (𝟙 _) w (w₀ * w⁻¹)
      inferInstance inferInstance (UpperTheory.Gal.Int.Geo.integ_of_mem (kn1 hv))).2 r rJ
    rw [Category.comp_id, _root_.inv_mul_cancel_right] at this
    exact this
