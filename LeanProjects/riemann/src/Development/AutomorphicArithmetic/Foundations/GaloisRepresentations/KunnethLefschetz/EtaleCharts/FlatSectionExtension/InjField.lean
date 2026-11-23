import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaLocal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.HomExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.CoverComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.PieceFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatNat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GvChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.RatioInj

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem injKey {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W)
    (hw : j ≫ π = r ≫ i) (v : Fin d → Γ(TP B j, ⊤)) (hv : IsV B j v) {V : Scheme.{0}} (p p' : B.ι × Fin d)
    (a₁ : V ⟶ (oT B j p : Scheme.{0})) (b₁ : V ⟶ (oT B j p' : Scheme.{0}))
    (M : Matrix (Fin d) (Fin d) Γ(V, ⊤))
    (hp : ((a₁ ≫ tI B j p) ≫ rhoP B j r hw) ≫ cP B = ((b₁ ≫ tI B j p') ≫ rhoP B j r hw) ≫ cP B)
    (hG : GMat B ((a₁ ≫ tI B j p) ≫ rhoP B j r hw) ((b₁ ≫ tI B j p') ≫ rhoP B j r hw) M)
    (u : (Γ(V, ⊤))ˣ)
    (hyp : M.mulVec ((a₁ ≫ tI B j p).appTop.hom ∘ v) = (u : Γ(V, ⊤)) • ((b₁ ≫ tI B j p').appTop.hom ∘ v))
    (m : Fin d) (hm : ⊤ ≤ ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ⁻¹ᵁ (B.c p'.1).C m) :
    (a₁ ≫ tI B j p) ≫ eP B j ≫ j = (b₁ ≫ tI B j p') ≫ eP B j ≫ j := by
  obtain ⟨h₁, e₁, -, r₁⟩ := pieceFacts B j r hw v hv p a₁
  obtain ⟨h₂, e₂, -, r₂⟩ := pieceFacts B j r hw v hv p' b₁
  have hL := gMatLoc B _ _ M p.1 p'.1 _ _ r₁ r₂ hG
  have hc := (coverComm B j r hw).1
  have hy : ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ≫ π = (((a₁ ≫ tI B j p) ≫ rhoP B j r hw) ≫ cP B) ≫ i := by
    rw [Category.assoc (a₁ ≫ tI B j p) (rhoP B j r hw) (cP B), hc]
    simp only [Category.assoc, hw]
  have hy' : ((b₁ ≫ tI B j p') ≫ eP B j ≫ j) ≫ π = (((a₁ ≫ tI B j p) ≫ rhoP B j r hw) ≫ cP B) ≫ i := by
    rw [hp, Category.assoc (b₁ ≫ tI B j p') (rhoP B j r hw) (cP B), hc]
    simp only [Category.assoc, hw]
  have hg := gvChart B _ _ hy p.1 p'.1 p.2 m h₁ hm M hL
  rw [e₁, e₂, hg] at hyp
  refine ratioInj B p'.1 m p'.2 _ _ _ hm h₂ ((D.u _ _ ((secOf_f B p.1 p.2 _ h₁).trans (secOf_f B p'.1 m _ hm).symm)) * u) hy hy' ?_
  rw [Units.val_mul, mul_smul, ← hyp, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.injField :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W) (hsq : IsPullback j r π i) (v : Fin d → Γ(TP B j, ⊤)), IsV B j v → ∀ {V : Scheme.{0}} (a b : V ⟶ TP B j) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), (a ≫ rhoP B j r hsq.w) ≫ cP B = (b ≫ rhoP B j r hsq.w) ≫ cP B → GMat B (a ≫ rhoP B j r hsq.w) (b ≫ rhoP B j r hsq.w) M → ∀ u : (Γ(V, ⊤))ˣ, M.mulVec (a.appTop.hom ∘ v) = (u : Γ(V, ⊤)) • (b.appTop.hom ∘ v) → a ≫ eP B j = b ≫ eP B j := by
  intro K _ W Z Y q i π D d B T j r hsq v hv V a b M hp hG u hyp
  have hc := (coverComm B j r hsq.w).1
  have hrr : a ≫ eP B j ≫ r = b ≫ eP B j ≫ r := by
    have h := hp
    simp only [Category.assoc] at h
    rwa [hc] at h
  have hππ : (a ≫ eP B j ≫ j) ≫ π = (b ≫ eP B j ≫ j) ≫ π := by
    simp only [Category.assoc, hsq.w]
    simp only [← Category.assoc] at hrr ⊢
    rw [hrr]
  refine hsq.hom_ext ?_ (by simpa only [Category.assoc] using hrr)
  refine homExt _ _ fun x => ?_
  obtain ⟨U₁, p, a₁, hx₁, ha⟩ := sigmaLocal (fun p : B.ι × Fin d => (oT B j p : Scheme.{0})) a x
  obtain ⟨U₂, p', b₁, hx₂, hb⟩ := sigmaLocal (fun p : B.ι × Fin d => (oT B j p : Scheme.{0})) b x

  have hbx : (b ≫ eP B j ≫ j) x ∈ (B.c p'.1).C p'.2 := by
    obtain ⟨h₂, -, -, -⟩ := pieceFacts B j r hsq.w v hv p' b₁
    have h3 : ((b₁ ≫ tI B j p') ≫ eP B j ≫ j) (⟨x, hx₂⟩ : U₂) ∈ (B.c p'.1).C p'.2 := h₂ (Set.mem_univ _)
    have h4 : b₁ ≫ tI B j p' = U₂.ι ≫ b := hb.symm
    rw [h4] at h3
    have h6 : ((U₂.ι ≫ b) ≫ eP B j ≫ j) (⟨x, hx₂⟩ : U₂) = (b ≫ eP B j ≫ j) x := by
      rw [Category.assoc, Scheme.Hom.comp_apply]
      rfl
    rwa [h6] at h3
  have hπx : π ((a ≫ eP B j ≫ j) x) ∈ B.V p'.1 := by
    have h5 : π ((a ≫ eP B j ≫ j) x) = π ((b ≫ eP B j ≫ j) x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hππ]
    rw [h5]
    exact (B.c p'.1).C_le p'.2 hbx
  obtain ⟨m, hmx⟩ := TopologicalSpace.Opens.mem_iSup.mp ((B.c p'.1).C_cover hπx)
  let U₃ : V.Opens := (a ≫ eP B j ≫ j) ⁻¹ᵁ (B.c p'.1).C m
  let U : V.Opens := U₁ ⊓ U₂ ⊓ U₃
  have hxU : x ∈ U := ⟨⟨hx₁, hx₂⟩, hmx⟩
  have l₁ : U ≤ U₁ := inf_le_left.trans inf_le_left
  have l₂ : U ≤ U₂ := inf_le_left.trans inf_le_right
  have l₃ : U ≤ U₃ := inf_le_right
  have ea : U.ι ≫ a = (V.homOfLE l₁ ≫ a₁) ≫ tI B j p := by
    have h : a₁ ≫ tI B j p = U₁.ι ≫ a := ha.symm
    rw [Category.assoc, h, Scheme.homOfLE_ι_assoc]
  have eb : U.ι ≫ b = (V.homOfLE l₂ ≫ b₁) ≫ tI B j p' := by
    have h : b₁ ≫ tI B j p' = U₂.ι ≫ b := hb.symm
    rw [Category.assoc, h, Scheme.homOfLE_ι_assoc]
  refine ⟨U, hxU, ?_⟩
  have hk := injKey B j r hsq.w v hv p p' (V.homOfLE l₁ ≫ a₁) (V.homOfLE l₂ ≫ b₁) (M.map U.ι.appTop.hom)
    (by rw [← ea, ← eb]; simp only [Category.assoc]; simp only [Category.assoc] at hp; rw [hp])
    (by
      rw [← ea, ← eb]
      have h := gMatNat B U.ι _ _ M hG
      simpa only [Category.assoc] using h)
    (Units.map (U.ι.appTop.hom : Γ(V, ⊤) →+* Γ((U : Scheme.{0}), ⊤)).toMonoidHom u)
    (by
      rw [← ea, ← eb]
      have hca : ∀ (c : V ⟶ TP B j), (U.ι ≫ c).appTop.hom ∘ v = U.ι.appTop.hom ∘ (c.appTop.hom ∘ v) := by
        intro c
        funext n
        rw [Scheme.Hom.comp_appTop]
        rfl
      rw [hca a, hca b]
      funext n
      have h2 := congrArg (U.ι.appTop.hom : Γ(V, ⊤) →+* Γ((U : Scheme.{0}), ⊤)) (congrFun hyp n)
      rw [RingHom.map_mulVec] at h2
      refine h2.trans ?_
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Function.comp_apply]
      rfl)
    m
    (by
      rw [← ea, Category.assoc U.ι a]
      intro z _
      exact l₃ z.2)
  rw [← ea, ← eb] at hk
  simpa only [Category.assoc] using hk
