import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegCompData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegOfValWOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnOfPsiOn
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PullDegTop

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem psi_val_on {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') {W : (Sp R).Opens}
    (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf φ) (x : D'.X) (z : (TK R').left)
    {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val (ψW.psi (h.xe x)) g z J = (om h.w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J' := by
  have v := PsiEvenPull.psi_pull h x (𝟙 _) z hJ hJ'
  have ag : val (ψW.psi (h.xe x)) g z J = val (h.psiW.psi (h.xe x)) (𝟙 _ ≫ h.g) z J :=
    ArcSpecialise.psiOn_agree ψW h.psiW _ _ _ (by rw [hg, Category.id_comp, h.g_comm]) hJ
  change _ = (om h.w z J J' (𝟙 _ ≫ D'.xK x))⁻¹ * _ at v
  rw [ag, v, Category.id_comp]

def reopen {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') {W : (Sp R).Opens}
    (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf φ) : IsPullDeg φ D D' :=
  { h with
    W := W
    psiW := ψW
    g := g
    g_comm := hg
    psi_pr := fun x => by
      obtain ⟨b, hb, hc⟩ := h.psi_pr x
      refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => (val_corr hJ hc (𝟙 _)).trans ?_⟩
      rw [val_pull hJ, val_pull hJ]
      exact ArcSpecialise.psiOn_agree h.psiW ψW _ _ _ (by
        rw [Category.id_comp, Category.id_comp, hg, h.g_comm]) hJ }

theorem exists_top {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D')
    (hU : ∀ y, PsiUnitOn D y Set.univ) : ∃ h' : IsPullDeg φ D D', h'.W = ⊤ ∧ proj h' = proj h ∧ h'.xe = h.xe := by
  obtain ⟨ψ⟩ := nonempty_psiOn_top D hU
  exact ⟨reopen h ψ ((jK R' ≫ specOf φ) ≫ (Sp R).topIso.inv) (by
    rw [Category.assoc, ← Scheme.topIso_hom, Iso.inv_hom_id, Category.comp_id]), rfl, rfl, rfl⟩

theorem psiUnitOn_univ {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D')
    (hU : ∀ y, PsiUnitOn D y Set.univ) (x : D'.X) : PsiUnitOn D' x Set.univ := by
  obtain ⟨h', hW, -, -⟩ := exists_top h hU
  obtain ⟨ψ, -⟩ := GlobalTheory.PullDegCancelTop.exists_psiOn_pull h'
  have := GlobalTheory.PsiUnitOfPsiOn.psiUnitOn_of_psiOn _ _ _ ψ x
  rw [hW] at this
  exact this

theorem act_iff {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') (f : D.P.A ⟶ D.P.A)
    (f' : D'.P.A ⟶ D'.P.A) :
    f' ≫ h.e.hom = h.e.hom ≫ (Over.pullback (specOf φ)).map f ↔ f'.left ≫ proj h = proj h ≫ f.left := by
  have a : ((Over.pullback (specOf φ)).map f).left ≫ pullback.fst D.P.A.hom (specOf φ) =
      pullback.fst D.P.A.hom (specOf φ) ≫ f.left := by
    simp [Over.pullback_map_left, pullback.lift_fst]
  constructor
  · intro H
    have := congrArg (fun q => q.left ≫ pullback.fst D.P.A.hom (specOf φ)) H
    simp only [Over.comp_left, Category.assoc] at this
    rw [a] at this
    exact this.trans (Category.assoc _ _ _).symm
  · intro H
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      rw [a]
      exact H.trans (Category.assoc _ _ _)
    · exact (Over.w (f' ≫ h.e.hom)).trans (Over.w (h.e.hom ≫ (Over.pullback (specOf φ)).map f)).symm

theorem exists_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''}
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p₀ : IsPullDeg i D D') (q : IsPullDeg j D' D'')
    (hU : ∀ y, PsiUnitOn D y Set.univ) :
    ∃ r : IsPullDeg (j.comp i) D D'', proj r = proj q ≫ proj p₀ ∧ ∀ x, r.xe x = p₀.xe (q.xe x) := by
  obtain ⟨p, hW, e₁, e₂⟩ := exists_top p₀ hU
  rw [← e₁, ← e₂]
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  obtain ⟨ψ, hv⟩ := GlobalTheory.PullDegCancelTop.exists_psiOn_pull p
  obtain ⟨g, hg⟩ : ∃ g : (TK R'').left ⟶ (specOf i ⁻¹ᵁ p.W).toScheme,
      g ≫ (specOf i ⁻¹ᵁ p.W).ι = jK R'' ≫ specOf j :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro y -
      rw [Scheme.Opens.range_ι, hW]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have hg' : (g ≫ (specOf i ∣_ p.W)) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg, Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, hr₁, hr₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW D D'' p.psiW (g ≫ (specOf i ∣_ p.W)) hg' gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := hv (q.xe x) _ g z J J' hJ hJ'
      have v₂ := psi_val_on q ψ g hg x z hJ' hJ''
      have hx : D''.xK x ≫ proj q = g ≫ (specOf i ⁻¹ᵁ p.W).ι ≫ (D'.c (q.xe x)).left := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = _
        rw [Category.assoc, q.c_pr, ← Category.assoc g, hg, Category.assoc]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      rw [v₂, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, hr₁, hr₂⟩

theorem exists_cancel {R₀ R₁ R₂ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁]
    [CommRing R₂] [IsDomain R₂] {α : R₀ →+* R₁} {β : R₁ →+* R₂} {θ : R₀ →+* R₂} (hθ : β.comp α = θ)
    {D₀ : DegPre R₀} {D₁ : DegPre R₁} {D : DegPre R₂}
    (h₀ : IsPullDeg α D₀ D₁) (h : IsPullDeg θ D₀ D) (hU : ∀ y, PsiUnitOn D₀ y Set.univ) :
    ∃ h' : IsPullDeg β D₁ D, proj h' ≫ proj h₀ = proj h ∧ ∀ x, h₀.xe (h'.xe x) = h.xe x := by
  subst hθ
  obtain ⟨h₁, hW₁, e₁', e₂'⟩ := exists_top h₀ hU
  rw [← e₁', ← e₂']
  have hW : specOf α ⁻¹ᵁ h₁.W = ⊤ := by rw [hW₁]; rfl
  have p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w
    ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁)
    (FieldPull.pmaps_rig h)
  let xe : D.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ψW, hv⟩ := GlobalTheory.PullDegCancelTop.exists_psiOn_pull h₁
  obtain ⟨g, hg⟩ : ∃ g : (TK R₂).left ⟶ (specOf α ⁻¹ᵁ h₁.W).toScheme,
      g ≫ (specOf α ⁻¹ᵁ h₁.W).ι = jK R₂ ≫ specOf β :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro y -
      rw [Scheme.Opens.range_ι, hW]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨hD, k₁, k₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW D₁ D ψW g hg gp w hw hr xe hc
    (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have v := PsiEvenPull.psi_pull h x (𝟙 _) z hJ₀ hJ
    have v₁ := hv (xe x) _ g z J₀ J₁ hJ₀ hJ₁
    have ag : val (h₁.psiW.psi (h.xe x)) (g ≫ (specOf α ∣_ h₁.W)) z J₀ =
        val (h.psiW.psi (h.xe x)) (𝟙 _ ≫ h.g) z J₀ :=
      ArcSpecialise.psiOn_agree h₁.psiW h.psiW _ _ _ (by
        rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg, Category.id_comp, h.g_comm, Category.assoc]
        exact congrArg (jK R₂ ≫ ·) sc) hJ₀
    have hx : D.xK x ≫ Φ = g ≫ (specOf α ⁻¹ᵁ h₁.W).ι ≫ (D₁.c (xe x)).left := by
      show (jK R₂ ≫ (D.c x).left) ≫ Φ = _
      rw [Category.assoc, hc, ← Category.assoc g, hg, Category.assoc]
    change _ = (om h.w z J₀ J (𝟙 _ ≫ D.xK x))⁻¹ * _ at v
    rw [hxe, ag, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD, by rw [k₁, e₁], fun x => by rw [k₂, hxe]⟩

theorem main : (∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (_ : IsPullDeg φ D D'), (∀ y, PsiUnitOn D y Set.univ) → ∀ x, PsiUnitOn D' x Set.univ) ∧ (∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') (f : D.P.A ⟶ D.P.A) (f' : D'.P.A ⟶ D'.P.A), f' ≫ h.e.hom = h.e.hom ≫ (Over.pullback (specOf φ)).map f ↔ f'.left ≫ h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = (h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ f.left) ∧ (∀ {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D''), (∀ y, PsiUnitOn D y Set.univ) → ∃ r : IsPullDeg (j.comp i) D D'', r.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (j.comp i)) = (q.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf j)) ≫ p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, r.xe x = p.xe (q.xe x)) ∧ (∀ {R₀ R₁ R₂ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁] [CommRing R₂] [IsDomain R₂] {α : R₀ →+* R₁} {β : R₁ →+* R₂} {θ : R₀ →+* R₂}, β.comp α = θ → ∀ {D₀ : DegPre R₀} {D₁ : DegPre R₁} {D : DegPre R₂} (h₀ : IsPullDeg α D₀ D₁) (h : IsPullDeg θ D₀ D), (∀ y, PsiUnitOn D₀ y Set.univ) → ∃ h' : IsPullDeg β D₁ D, (h'.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf β)) ≫ h₀.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf α) = h.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ) ∧ ∀ x, h₀.xe (h'.xe x) = h.xe x) :=
  ⟨fun h hU x => psiUnitOn_univ h hU x, fun h f f' => act_iff h f f', fun p q hU => exists_comp p q hU,
    fun e _ _ _ h₀ h hU => exists_cancel e h₀ h hU⟩

end GlobalTheory.PullDegTop
