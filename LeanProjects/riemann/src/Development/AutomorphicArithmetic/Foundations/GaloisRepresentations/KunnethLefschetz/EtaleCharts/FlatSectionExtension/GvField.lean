import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaLocal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SectionExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.PieceFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatNat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GvChart

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem uV_eq' {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} {y y' : V ⟶ Y}
    (e : y = y') (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c α).C k) : uV B α k y h = uV B α k y' h' := by
  subst e; rfl

private theorem secOf_eq' {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} {y y' : V ⟶ Y}
    (e : y = y') (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c α).C k) : secOf B α k y h = secOf B α k y' h' := by
  subst e; rfl

private theorem u_eq' {Y : Scheme.{0}} (D : E.LineData Y) {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y}
    (ea : a = a') (eb : b = b') (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : D.u a b h = D.u a' b' h' := by
  subst ea eb; rfl

private theorem rho_c {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W)
    (hw : j ≫ π = r ≫ i) : rhoP B j r hw ≫ cP B = eP B j ≫ r := by
  refine Sigma.hom_ext _ _ fun p => ?_
  simp only [rhoP, cP, eP, wI, Category.assoc, colimit.ι_desc_assoc, colimit.ι_desc, Cofan.mk_ι_app, Discrete.functor_obj_eq_as,
    rhoC, IsOpenImmersion.lift_fac]

private theorem core {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W)
    (hsq : IsPullback j r π i) (v : Fin d → Γ(TP B j, ⊤)) (hv : IsV B j v) {V : Scheme.{0}}
    (p p' : B.ι × Fin d) (a₁ : V ⟶ (oT B j p : Scheme.{0})) (b₁ : V ⟶ (oT B j p' : Scheme.{0}))
    (hab : (a₁ ≫ tI B j p) ≫ eP B j = (b₁ ≫ tI B j p') ≫ eP B j)
    (hh : ((a₁ ≫ tI B j p) ≫ tauP B j) ≫ D.f = ((b₁ ≫ tI B j p') ≫ tauP B j) ≫ D.f)
    (M : Matrix (Fin d) (Fin d) Γ(V, ⊤))
    (hG : GMat B ((a₁ ≫ tI B j p) ≫ rhoP B j r hsq.w) ((b₁ ≫ tI B j p') ≫ rhoP B j r hsq.w) M) :
    M.mulVec ((a₁ ≫ tI B j p).appTop.hom ∘ v) =
      (((D.u _ _ hh)⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) • ((b₁ ≫ tI B j p').appTop.hom ∘ v) := by
  obtain ⟨h₁, e1, e2, e3⟩ := UpperTheory.Gal.KunnethLefschetz.G.PX.pieceFacts B j r hsq.w v hv p a₁
  obtain ⟨h₂, f1, f2, f3⟩ := UpperTheory.Gal.KunnethLefschetz.G.PX.pieceFacts B j r hsq.w v hv p' b₁
  have hy : (b₁ ≫ tI B j p') ≫ eP B j ≫ j = (a₁ ≫ tI B j p) ≫ eP B j ≫ j := by
    rw [← Category.assoc, ← hab, Category.assoc]
  have h₂' : ⊤ ≤ ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ⁻¹ᵁ (B.c p'.1).C p'.2 := hy ▸ h₂
  have hL := UpperTheory.Gal.KunnethLefschetz.G.PX.gMatLoc B _ _ M p.1 p'.1 (a₁ ≫ rhoC B j r hsq.w p) (b₁ ≫ rhoC B j r hsq.w p') e3 f3 hG
  have hc : ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ≫ π = (((a₁ ≫ tI B j p) ≫ rhoP B j r hsq.w) ≫ cP B) ≫ i := by
    rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, Category.assoc, hsq.w,
      ← Category.assoc (rhoP B j r hsq.w), rho_c B j r hsq.w]
    simp only [Category.assoc]
  have key := UpperTheory.Gal.KunnethLefschetz.G.PX.gvChart B _ _ hc p.1 p'.1 p.2 p'.2 h₁ h₂' M hL
  rw [e1, f1, uV_eq' B p'.1 p'.2 hy h₂ h₂',
    u_eq' D e2 (f2.trans (secOf_eq' B p'.1 p'.2 hy h₂ h₂')) hh
      ((secOf_f B p.1 p.2 _ h₁).trans (secOf_f B p'.1 p'.2 _ h₂').symm)]
  exact key

private theorem core' {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W)
    (hsq : IsPullback j r π i) (v : Fin d → Γ(TP B j, ⊤)) (hv : IsV B j v) {V : Scheme.{0}}
    (p p' : B.ι × Fin d) (a₁ : V ⟶ (oT B j p : Scheme.{0})) (b₁ : V ⟶ (oT B j p' : Scheme.{0}))
    (a b : V ⟶ TP B j) (ea : a = a₁ ≫ tI B j p) (eb : b = b₁ ≫ tI B j p')
    (hab : a ≫ eP B j = b ≫ eP B j) (hh : (a ≫ tauP B j) ≫ D.f = (b ≫ tauP B j) ≫ D.f)
    (M : Matrix (Fin d) (Fin d) Γ(V, ⊤))
    (hG : GMat B (a ≫ rhoP B j r hsq.w) (b ≫ rhoP B j r hsq.w) M) :
    M.mulVec (a.appTop.hom ∘ v) = (((D.u _ _ hh)⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) • (b.appTop.hom ∘ v) := by
  subst ea eb
  exact core B j r hsq v hv p p' a₁ b₁ hab hh M hG

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gvField :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W) (hsq : IsPullback j r π i) (v : Fin d → Γ(TP B j, ⊤)), IsV B j v → ∀ {V : Scheme.{0}} (a b : V ⟶ TP B j), a ≫ eP B j = b ≫ eP B j → ∀ (hh : (a ≫ tauP B j) ≫ D.f = (b ≫ tauP B j) ≫ D.f) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), GMat B (a ≫ rhoP B j r hsq.w) (b ≫ rhoP B j r hsq.w) M → M.mulVec (a.appTop.hom ∘ v) = (((D.u _ _ hh)⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) • (b.appTop.hom ∘ v) := by
  intro K _ W Z Y q i π D d B T j r hsq v hv V a b hab hh M hG
  funext m
  refine UpperTheory.Gal.KunnethLefschetz.G.PX.sectionExt _ _ fun x => ?_
  obtain ⟨U₁, p, a₁, hx₁, ha⟩ := UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaLocal (fun p : B.ι × Fin d => (oT B j p : Scheme.{0})) a x
  obtain ⟨U₂, p', b₁, hx₂, hb⟩ := UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaLocal (fun p : B.ι × Fin d => (oT B j p : Scheme.{0})) b x
  let U : V.Opens := U₁ ⊓ U₂
  have hU₁ : U ≤ U₁ := inf_le_left
  have hU₂ : U ≤ U₂ := inf_le_right
  have ea : U.ι ≫ a = (V.homOfLE hU₁ ≫ a₁) ≫ tI B j p := by
    have : (V.homOfLE hU₁ ≫ a₁) ≫ tI B j p = V.homOfLE hU₁ ≫ (U₁.ι ≫ a) := by
      rw [ha]; simp [tI]
    rw [this, ← Category.assoc, Scheme.homOfLE_ι]
  have eb : U.ι ≫ b = (V.homOfLE hU₂ ≫ b₁) ≫ tI B j p' := by
    have : (V.homOfLE hU₂ ≫ b₁) ≫ tI B j p' = V.homOfLE hU₂ ≫ (U₂.ι ≫ b) := by
      rw [hb]; simp [tI]
    rw [this, ← Category.assoc, Scheme.homOfLE_ι]
  refine ⟨U, ⟨hx₁, hx₂⟩, ?_⟩
  have hG' : GMat B ((U.ι ≫ a) ≫ rhoP B j r hsq.w) ((U.ι ≫ b) ≫ rhoP B j r hsq.w) (M.map U.ι.appTop.hom) := by
    simpa only [Category.assoc] using UpperTheory.Gal.KunnethLefschetz.G.PX.gMatNat B U.ι _ _ M hG
  have hab' : (U.ι ≫ a) ≫ eP B j = (U.ι ≫ b) ≫ eP B j := by
    rw [Category.assoc, Category.assoc, hab]
  have hh' : ((U.ι ≫ a) ≫ tauP B j) ≫ D.f = ((U.ι ≫ b) ≫ tauP B j) ≫ D.f := by
    simp only [Category.assoc] at hh ⊢
    rw [hh]
  have res := core' B j r hsq v hv p p' _ _ (U.ι ≫ a) (U.ι ≫ b) ea eb hab' hh' _ hG'
  have hc : ∀ g : V ⟶ TP B j, (U.ι ≫ g).appTop.hom ∘ v = U.ι.appTop.hom ∘ (g.appTop.hom ∘ v) := by
    intro g
    funext l
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, Scheme.Hom.comp_appTop]
    rfl
  have hu : D.u ((U.ι ≫ a) ≫ tauP B j) ((U.ι ≫ b) ≫ tauP B j) hh' =
      Units.map U.ι.appTop.hom.toMonoidHom (D.u _ _ hh) := by
    rw [← D.nat]
    exact u_eq' D (Category.assoc _ _ _) (Category.assoc _ _ _) _ _
  rw [hc a, hc b, hu] at res
  have e := congrFun res m
  rw [RingHom.map_mulVec, e]
  simp [Pi.smul_apply, smul_eq_mul, map_mul]
