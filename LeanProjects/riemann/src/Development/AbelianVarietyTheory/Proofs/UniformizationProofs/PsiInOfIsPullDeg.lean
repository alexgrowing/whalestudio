import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PsiInPull

theorem gs_injective {Y Z : Scheme.{0}} [IsReduced Y] (f : Z ⟶ Y) (z : Z)
    (hz : ∀ U : Y.Opens, U ≠ ⊥ → f z ∈ U) (U : Y.Opens) (hU : f z ∈ U) {a b : Γ(Y, U)}
    (h : gs f z U a = gs f z U b) : a = b := by
  rw [gs_eq f z U hU, gs_eq f z U hU, ← sub_eq_zero, ← map_sub, ← map_sub] at h
  by_contra hne
  have h1 : f z ∈ Y.basicOpen (a - b) := hz _ (by
    rw [Ne, basicOpen_eq_bot_iff]; exact sub_ne_zero.2 hne)
  have h2 : z ∈ Z.basicOpen ((f.app U).hom (a - b)) := by
    rw [← Scheme.preimage_basicOpen]; exact h1
  have h3 := (Z.mem_basicOpen _ z hU).1 h2
  rw [h] at h3
  exact not_isUnit_zero h3

theorem jK_mem {R : Type} [CommRing R] [IsDomain R] (z : Spec (CommRingCat.of (FractionRing R)))
    (U : (Spec (CommRingCat.of R)).Opens) (hU : U ≠ ⊥) : jK R z ∈ U := by
  obtain ⟨v, hv⟩ : ∃ v, v ∈ U := by
    by_contra hc
    exact hU (eq_bot_iff.2 fun v hv => hc ⟨v, hv⟩)
  have hs : jK R z ⤳ v := by
    refine (PrimeSpectrum.le_iff_specializes (jK R z) v).1 ?_
    intro a ha
    have ha' : algebraMap R (FractionRing R) a ∈ (PrimeSpectrum.asIdeal z) := ha
    have hb : PrimeSpectrum.asIdeal z = ⊥ := Ideal.eq_bot_of_prime _ (h := z.isPrime)
    rw [hb, Ideal.mem_bot, IsFractionRing.to_map_eq_zero_iff] at ha'
    rw [ha']; exact Ideal.zero_mem _
  exact hs.mem_open U.isOpen hv

theorem res_toOpen {R : Type} [CommRing R] {U V : (Spec (CommRingCat.of R)).Opens} (h : U ≤ V) (a : R) :
    ((Spec (CommRingCat.of R)).presheaf.map (homOfLE h).op).hom (DegPre.toOpen V a) = DegPre.toOpen U a := by
  simp only [DegPre.toOpen, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem app_toOpen {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (V : (Spec (CommRingCat.of R)).Opens) (a : R) :
    ((specOf φ).app V).hom (DegPre.toOpen V a) = DegPre.toOpen (specOf φ ⁻¹ᵁ V) (φ a) := by
  have nat := congrArg (fun g => g.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  have e := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    ((specOf φ).naturality (homOfLE (le_top : V ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  simp only [DegPre.toOpen, RingHom.comp_apply]
  rw [e, nat]
  rfl

theorem exists_of_locally {R : Type} [CommRing R] [IsDomain R] (J : Ideal R)
    (z : Spec (CommRingCat.of (FractionRing R))) (t : (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk z)
    (V : (Spec (CommRingCat.of R)).Opens) (hV : IsAffineOpen V) (hz : jK R z ∈ V)
    (H : ∀ v ∈ V, ∃ U : (Spec (CommRingCat.of R)).Opens, U ≤ V ∧ v ∈ U ∧
      ∃ s ∈ J.map (DegPre.toOpen U), gs (jK R) z U s = t) :
    ∃ r ∈ J.map (DegPre.toOpen V), gs (jK R) z V r = t := by
  let θ : Γ(Spec (CommRingCat.of R), V) →+* (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk z :=
    ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ (jK R ⁻¹ᵁ V) z hz).hom.comp ((jK R).app V).hom
  have hθ : ∀ a, gs (jK R) z V a = θ a := fun a => gs_eq _ _ _ hz a
  let Q : Ideal Γ(Spec (CommRingCat.of R), V) :=
    { carrier := {a | ∃ b ∈ J.map (DegPre.toOpen V), θ b = θ a * t}
      zero_mem' := ⟨0, Ideal.zero_mem _, by simp⟩
      add_mem' := by
        rintro a a' ⟨b, hb, e⟩ ⟨b', hb', e'⟩
        exact ⟨b + b', Ideal.add_mem _ hb hb', by rw [map_add, map_add, e, e', add_mul]⟩
      smul_mem' := by
        rintro c a ⟨b, hb, e⟩
        exact ⟨c * b, Ideal.mul_mem_left _ _ hb, by rw [smul_eq_mul, map_mul, map_mul, e, _root_.mul_assoc]⟩ }
  have key : ∀ v ∈ V, ∃ f ∈ Q, v ∈ (Spec (CommRingCat.of R)).basicOpen f := by
    intro v hv
    obtain ⟨U, hUV, hvU, s, hs, e⟩ := H v hv
    obtain ⟨f, hfU, hvf⟩ := hV.exists_basicOpen_le (V := U) ⟨v, hvU⟩ hv
    have hzf : jK R z ∈ (Spec (CommRingCat.of R)).basicOpen f :=
      jK_mem z _ (fun h0 => by rw [h0] at hvf; exact hvf)
    have := hV.isLocalization_basicOpen f
    have hs' : ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hfU).op).hom s ∈
        (J.map (DegPre.toOpen V)).map
          (algebraMap Γ(Spec (CommRingCat.of R), V) Γ(Spec (CommRingCat.of R), (Spec (CommRingCat.of R)).basicOpen f)) := by
      have h1 := Ideal.mem_map_of_mem ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hfU).op).hom hs
      rw [Ideal.map_map] at h1 ⊢
      convert h1 using 2
      ext a
      exact (res_toOpen ((Spec (CommRingCat.of R)).basicOpen_le f) a).trans (res_toOpen hfU a).symm
    obtain ⟨⟨⟨b, hb⟩, ⟨_, n, rfl⟩⟩, e2⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) _).1 hs'
    have e3 := congrArg (gs (jK R) z ((Spec (CommRingCat.of R)).basicOpen f)) e2
    rw [gs_mul _ _ _ hzf, gs_res _ _ hfU hzf, e] at e3
    have e4 : ∀ a, gs (jK R) z ((Spec (CommRingCat.of R)).basicOpen f)
        (algebraMap Γ(Spec (CommRingCat.of R), V) _ a) = θ a := fun a =>
      (gs_res _ _ ((Spec (CommRingCat.of R)).basicOpen_le f) hzf a).trans (hθ a)
    rw [e4, e4] at e3
    refine ⟨f ^ n * f, Ideal.mul_mem_right _ _ ⟨b, hb, e3.symm.trans (_root_.mul_comm _ _)⟩, ?_⟩
    rw [← pow_succ, Scheme.basicOpen_pow _ _ (Nat.succ_pos n)]
    exact hvf
  have hQ : Ideal.span (Q : Set Γ(Spec (CommRingCat.of R), V)) = ⊤ := by
    refine (hV.self_le_iSup_basicOpen_iff).1 fun v hv => ?_
    obtain ⟨f, hf, hvf⟩ := key v hv
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hvf⟩
  rw [Ideal.span_eq] at hQ
  obtain ⟨b, hb, e⟩ : (1 : Γ(Spec (CommRingCat.of R), V)) ∈ Q := hQ ▸ Submodule.mem_top
  exact ⟨b, hb, by rw [hθ, e, map_one, _root_.one_mul]⟩

theorem mem_wchart {Y B : Scheme.{0}} (M : LB B) (φ : Y ⟶ B) (y : Y) (j : M.ι) (h : φ y ∈ M.U j) :
    y ∈ LB.wchart M (fun _ : PUnit => φ) (fun _ => j) := Set.mem_iInter.2 fun _ => h

theorem psiOn_val {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}
    (ψ : PsiOn D W) (χ : D.X) (p : D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens)
    (hVp : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U p)
    (h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (fun _ => p))
    (r : Γ(Spec (CommRingCat.of R), V))
    (hr : ((jK R).app V).hom r = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s (fun _ => p)).val)
    {Z : Scheme.{0}} (g : Z ⟶ W.toScheme) (z : Z) (hz : W.ι (g z) ∈ V) :
    (gm g z (LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c χ).left) (fun _ => p))
      ((ψ.psi χ).s (fun _ => p))).val = gs (g ≫ W.ι) z V r := by
  have hc : (toUnit (TW W) ≫ D.c χ).left = W.ι ≫ (D.c χ).left := rfl
  have hle : W.ι ⁻¹ᵁ V ≤ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c χ).left) (fun _ => p) :=
    fun y hy => mem_wchart _ _ _ _ (hVp hy)
  obtain ⟨z₀⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have hW : jK R z₀ ∈ W := jK_mem z₀ W (fun h0 => by
    have : (g z).1 ∈ W := (g z).2
    exact (h0.le this : (g z).1 ∈ (⊥ : (Spec (CommRingCat.of R)).Opens)))
  have hV : jK R z₀ ∈ V := jK_mem z₀ V (fun h0 => by rw [h0] at hz; exact hz)
  let z₁ : (jK R ⁻¹ᵁ W).toScheme := ⟨z₀, hW⟩
  have hι : (jK R ∣_ W) ≫ W.ι = (jK R ⁻¹ᵁ W).ι ≫ jK R := morphismRestrict_ι _ _
  have hpt : W.ι ((jK R ∣_ W) z₁) = jK R z₀ := congrArg (fun q => q z₁) hι
  have hm : (jK R ∣_ W) z₁ ∈ W.ι ⁻¹ᵁ V := by
    show W.ι ((jK R ∣_ W) z₁) ∈ V
    rw [hpt]; exact hV
  have hdense : ∀ U : W.toScheme.Opens, U ≠ ⊥ → (jK R ∣_ W) z₁ ∈ U := by
    intro U hU
    have h1 : jK R z₀ ∈ W.ι ''ᵁ U := jK_mem z₀ _ (fun h0 => hU (by
      rw [← W.ι.preimage_image_eq U, h0]; rfl))
    rw [← hpt] at h1
    rw [← W.ι.preimage_image_eq U]; exact h1
  have n₂ : (jK R ⁻¹ᵁ W).ι z₁ ∈ jK R ⁻¹ᵁ V := hV
  have e₃ := (gm_pullGen D.P.L _ _ (ψ.psi χ) (jK R ∣_ W) (𝟙 _) z₁ (fun _ => p) (mem_wchart _ _ _ _ (hVp hm))).symm.trans
    ((gm_corr D.P.L (ψ.psi_eq χ) (𝟙 _) z₁ p (mem_wchart _ _ _ _ (hVp hm)) (mem_wchart _ _ _ _ (hVp hV))).trans
      (gm_pullGen D.P.L _ _ (D.psi χ) (jK R ⁻¹ᵁ W).ι (𝟙 _) z₁ (fun _ => p) (mem_wchart _ _ _ _ (hVp hV))))
  rw [Category.id_comp, Category.id_comp] at e₃
  have e : (W.toScheme.presheaf.map (homOfLE hle).op).hom ((ψ.psi χ).s (fun _ => p)).val = (W.ι.app V).hom r := by
    refine gs_injective (jK R ∣_ W) z₁ hdense (W.ι ⁻¹ᵁ V) hm ?_
    refine ((gs_res _ _ hle hm _).trans ((gs_unit _ _ _ (hle hm) _).trans (congrArg Units.val e₃))).trans ?_
    refine Eq.trans ?_ (gs_pull (jK R ∣_ W) W.ι z₁ V hm r).symm
    rw [hι]
    refine Eq.trans ?_ (gs_pull (jK R ⁻¹ᵁ W).ι (jK R) z₁ V n₂ r)
    rw [hr]
    exact ((gs_res _ _ h n₂ _).trans (gs_unit _ _ _ (h n₂) _)).symm
  exact (gs_unit g z _ (hle hz) _).symm.trans ((gs_res g z hle hz _).symm.trans
    ((congrArg (gs g z (W.ι ⁻¹ᵁ V)) e).trans (gs_pull g W.ι z V hz r)))

end PsiInPull

open PsiInPull in

theorem psiIn_of_isPullDeg (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R')
    (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (x : D'.X) (J : Ideal R) (J' : Ideal R')
    (hJ : J.map φ ≤ J') (H : D.PsiIn (hD.xe x) J) : D'.PsiIn x J' := by
  intro j' V' hV' hle' h'
  obtain ⟨q, rfl⟩ : ∃ q, j' = fun _ => q := ⟨j' PUnit.unit, rfl⟩
  have hss : Subsingleton (Spec (CommRingCat.of (FractionRing R'))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R')))
  by_cases hne : ∃ z, jK R' z ∈ V'
  swap
  · exact ⟨0, Ideal.zero_mem _, fn_ext fun z hz => (hne ⟨z, hz⟩).elim⟩
  obtain ⟨z, hz⟩ := hne
  obtain ⟨b, hb, hcorr⟩ := hD.psi_pr x
  set Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) with hΦ
  have hcp : (D'.c x).left ≫ Φ = specOf φ ≫ (D.c (hD.xe x)).left := hD.c_pr x
  have hxK : D'.xK x = jK R' ≫ (D'.c x).left := rfl
  have cW : hD.g ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left = D'.xK x ≫ Φ := by
    rw [hxK, Category.assoc, hcp, ← Category.assoc (jK R'), ← hD.g_comm, Category.assoc]; rfl
  obtain ⟨r', hr', e'⟩ := exists_of_locally J' z
    (gm (𝟙 _) z (LB.wchart D'.P.L (fun _ : PUnit => D'.xK x) (fun _ => q)) ((D'.psi x).s (fun _ => q))).val
    V' hV' hz (by
    intro v hv
    obtain ⟨p, hp⟩ := exists_chart D.P.isLB ((D.c (hD.xe x)).left (specOf φ v))
    obtain ⟨_, ⟨V, hV, rfl⟩, hvV, hVp⟩ := (Spec (CommRingCat.of R)).isBasis_affineOpens.exists_subset_of_mem_open
      (show specOf φ v ∈ ((D.c (hD.xe x)).left ⁻¹ᵁ D.P.L.U p : (Spec (CommRingCat.of R)).Opens) from hp)
      ((D.c (hD.xe x)).left ⁻¹ᵁ D.P.L.U p).isOpen
    have h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK (hD.xe x)) (fun _ => -1)).U (fun _ => p) :=
      fun y hy => mem_wchart _ _ _ _ (hVp hy)
    obtain ⟨r, hrJ, hr⟩ := H (fun _ => p) V hV hVp h
    have hzU : jK R' z ∈ V' ⊓ specOf φ ⁻¹ᵁ V := jK_mem z _ (fun h0 =>
      (h0.le (show v ∈ V' ⊓ specOf φ ⁻¹ᵁ V from ⟨hv, hvV⟩) : v ∈ (⊥ : (Spec (CommRingCat.of R')).Opens)))
    have hU : V' ⊓ specOf φ ⁻¹ᵁ V ≤ (D'.c x).left ⁻¹ᵁ ((D.P.L.pull Φ).U (fun _ => p) ⊓ D'.P.L.U q) := fun y hy =>
      ⟨mem_pull.2 ((congrArg (fun m => m y ∈ D.P.L.U p) hcp).mpr (hVp hy.2)), hle' hy.1⟩
    have m₁ : (𝟙 (TK R').left : (TK R').left ⟶ (TK R').left) z ∈
        D'.xK x ⁻¹ᵁ ((D.P.L.pull Φ).U (fun _ => p) ⊓ D'.P.L.U q) := hU hzU
    have mp : Φ (D'.xK x z) ∈ D.P.L.U p := mem_pull.1 m₁.1
    have mW : (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left (hD.g z) ∈ D.P.L.U p :=
      (congrArg (fun m => m z ∈ D.P.L.U p) cW).mpr mp
    have e₁ := congrArg (gm (𝟙 (TK R').left) z (D'.xK x ⁻¹ᵁ ((D.P.L.pull Φ).U (fun _ => p) ⊓ D'.P.L.U q)))
      (hb (fun _ => p) q)
    have e₁' := (gm_res _ z _ m₁ _).symm.trans (e₁.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ (D'.xK x) z
        ((D.P.L.pull Φ).U (fun _ => p) ⊓ D'.P.L.U q) m₁ _))) (gm_res _ z _ m₁ _))))
    have e₂ := (gm_corr D.P.L hcorr (𝟙 (TK R').left) z p (mem_wchart _ _ _ _ mp) (mem_wchart _ _ _ _ mW)).trans
      (gm_pullGen D.P.L _ _ _ hD.g (𝟙 (TK R').left) z _ (mem_wchart _ _ _ _ mW))
    have hgz : hD.W.ι (hD.g z) ∈ V := (congrArg (fun m => m z ∈ V) hD.g_comm).mpr hzU.2
    have e₃ := psiOn_val hD.psiW (hD.xe x) p V hVp h r hr hD.g z hgz
    have e₄ := e₂.symm.trans e₁'
    rw [Category.id_comp, zpow_neg_one, eq_inv_mul_iff_mul_eq] at e₄
    erw [Category.id_comp] at e₄
    refine ⟨V' ⊓ specOf φ ⁻¹ᵁ V, inf_le_left, ⟨hv, hvV⟩,
      ((Spec (CommRingCat.of R')).presheaf.map (homOfLE hU).op).hom
        (((D'.c x).left.app _).hom (hD.w.s (fun _ => p, q)).val) *
      ((Spec (CommRingCat.of R')).presheaf.map (homOfLE (inf_le_right : V' ⊓ specOf φ ⁻¹ᵁ V ≤ _)).op).hom
        (((specOf φ).app V).hom r), Ideal.mul_mem_left _ _ ?_, ?_⟩
    · have h1 := Ideal.mem_map_of_mem (((Spec (CommRingCat.of R')).presheaf.map
        (homOfLE (inf_le_right : V' ⊓ specOf φ ⁻¹ᵁ V ≤ _)).op).hom.comp ((specOf φ).app V).hom) hrJ
      rw [Ideal.map_map] at h1
      refine Ideal.map_mono (f := DegPre.toOpen (V' ⊓ specOf φ ⁻¹ᵁ V)) hJ ?_
      rw [Ideal.map_map]
      have e5 : (DegPre.toOpen (V' ⊓ specOf φ ⁻¹ᵁ V)).comp φ = (((Spec (CommRingCat.of R')).presheaf.map
          (homOfLE (inf_le_right : V' ⊓ specOf φ ⁻¹ᵁ V ≤ _)).op).hom.comp ((specOf φ).app V).hom).comp
          (DegPre.toOpen V) :=
        RingHom.ext fun a => ((congrArg _ (app_toOpen φ V a)).trans (res_toOpen inf_le_right _)).symm
      rw [e5]
      exact h1
    · refine Eq.trans ?_ (congrArg Units.val e₄)
      refine (gs_mul _ _ _ hzU _ _).trans (congrArg₂ (· * ·) ?_ ?_)
      · exact (gs_res _ _ hU hzU _).trans ((gs_pull (jK R') (D'.c x).left z _ m₁ _).trans (gs_unit (D'.xK x) z ((D.P.L.pull Φ).U (fun _ => p) ⊓ D'.P.L.U q) m₁ _))
      · refine (gs_res _ _ _ hzU _).trans ((gs_pull (jK R') (specOf φ) z V hzU.2 r).trans ?_)
        exact (congrArg (fun m => gs m z V r) hD.g_comm).symm.trans e₃.symm)
  refine ⟨r', hr', fn_ext fun y hy => ?_⟩
  obtain rfl : y = z := Subsingleton.elim (α := Spec (CommRingCat.of (FractionRing R'))) y z
  exact (gs_pull (𝟙 _) (jK R') y V' hz r').trans (e'.trans
    ((gs_res (𝟙 _) y h' hy _).trans (gs_unit _ _ _ (h' hy) _)).symm)

end GlobalTheory
