import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
noncomputable section

namespace GlobalTheory.HomFixMat.SpanPull

theorem appLE_appLE_apply {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (V : Y.Opens)
    (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e : W ≤ (f ≫ g) ⁻¹ᵁ U) (x : Γ(Z, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) = ((f ≫ g).appLE U W e).hom x :=
  congrArg (fun φ => φ.hom x) (Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂)

theorem appLE_apply_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (f.appLE U V hf).hom x = (g.appLE U V hg).hom x := by
  subst h; rfl

theorem id_appLE_self {X : Scheme.{0}} (U : X.Opens) (h : U ≤ (𝟙 X) ⁻¹ᵁ U) (x : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U U h).hom x = x := by
  show (X.presheaf.map (𝟙 (Opposite.op U))).hom ((Scheme.Hom.app (𝟙 X) U).hom x) = x
  simp
  rfl

theorem appLE_appLE_eq {X Y Z : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (hfg : f ≫ g = h)
    (U : Z.Opens) (V : Y.Opens) (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (eh : W ≤ h ⁻¹ᵁ U)
    (x : Γ(Z, U)) : (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) = (h.appLE U W eh).hom x := by
  subst hfg
  exact appLE_appLE_apply f g U V W e₁ e₂ eh x

end GlobalTheory.HomFixMat.SpanPull

namespace GlobalTheory.HomFixMat

open GlobalTheory.HomFixMat.SpanPull in

theorem exists_coeff_of_isBCBasis : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ) (mA : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))), IsBCBasis A L k bA → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) (φA' : A'.left ⟶ A.left), IsPullback φA' A'.hom A.hom t → ∀ (ψA : A'.left ⟶ (topS Rg ⊗ A).left), ψA ≫ (snd (topS Rg) A).left = φA' → ∀ s : LB.Sec (powPull L (ψA ≫ (snd (topS Rg) A).left) (k : ℤ)), ∃ c : Fin mA → Γ(Sp R, ⊤), ∀ q : Fin 1 → L.ι, s.f q = ∑ i, (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q) (fun _ _ => trivial)).hom (c i) * (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) q) (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q) (GlobalTheory.HomFixMat.wchart_comp_le L ψA (snd (topS Rg) A).left q)).hom ((bA i).f q) := by
  intro Rg _ A _ L k mA bA hB R _ t A' φA' hpb ψA hψ s
  let t' : Sp R ⟶ (topS Rg).left := t ≫ (Sp Rg).topIso.inv
  have hbt : (baseAt t').hom = t := by
    show (t ≫ (Sp Rg).topIso.inv) ≫ ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _) = t
    rw [Category.comp_id, ← Scheme.topIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have eH : ∀ _k : Fin 1, (homAt t' ▷ A).left ≫ (snd (topS Rg) A).left = (snd (baseAt t') A).left :=
    fun _ => by rw [← Over.comp_left, whiskerRight_snd]
  let b' : Fin mA → LB.Sec (LPow A L (k : ℤ) (baseAt t')) := fun i =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.pullSecLC L _ _ _ (homAt t' ▷ A).left eH (bA i)
  have hb' : ∀ i, IsPullSec A L (k : ℤ) (homAt t' ▷ A) (whiskerRight_snd (homAt t') A) (bA i) (b' i) :=
    fun i j => rfl
  have hspan := (hB R t' b' hb').2
  have hY : IsPullback (snd (baseAt t') A).left (fst (baseAt t') A).left A.hom t := by
    rw [← hbt]
    exact (IsPullback.of_hasPullback _ _).flip
  let e := IsPullback.isoIsPullback _ _ hY hpb
  have e1 : e.hom ≫ φA' = (snd (baseAt t') A).left := IsPullback.isoIsPullback_hom_fst _ _ hY hpb
  have e2 : e.inv ≫ (snd (baseAt t') A).left = φA' := IsPullback.isoIsPullback_inv_fst _ _ hY hpb
  have e3 : e.inv ≫ (fst (baseAt t') A).left = A'.hom := IsPullback.isoIsPullback_inv_snd _ _ hY hpb
  have hTop : IsPullback (snd (topS Rg) A).left (fst (topS Rg) A).left A.hom (topS Rg).hom :=
    (IsPullback.of_hasPullback _ _).flip
  have e4 : e.inv ≫ (homAt t' ▷ A).left = ψA := by
    have hs : (e.inv ≫ (homAt t' ▷ A).left) ≫ (snd (topS Rg) A).left = ψA ≫ (snd (topS Rg) A).left := by
      rw [Category.assoc, eH 0, e2, hψ]
    refine hTop.hom_ext hs ?_
    haveI : Mono (topS Rg).hom := by dsimp [topS]; infer_instance
    rw [← cancel_mono (topS Rg).hom]
    simp only [Category.assoc, ← hTop.w]
    simp only [← Category.assoc]
    rw [hs]
  have eS : ∀ _k : Fin 1, e.hom ≫ (ψA ≫ (snd (topS Rg) A).left) = (snd (baseAt t') A).left :=
    fun _ => by rw [hψ, e1]
  let s'' : LB.Sec (LPow A L (k : ℤ) (baseAt t')) := ReciprocityTheory.ChartRestriction.G.PullbackSections.pullSecLC L _ _ _ e.hom eS s
  have hmem : SecM.ofSec A s'' ∈ Submodule.span Γ((baseAt t').left, ⊤)
      (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t'))) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
  refine ⟨c, fun q => ?_⟩
  have hq : s''.f q = (∑ i, liftHom A ((LPow A L (k : ℤ) (baseAt t')).U q) (c i) * (b' i).f q :
      Γ((baseAt t' ⊗ A).left, LB.wchart L (fun _ : Fin 1 => (snd (baseAt t') A).left) q)) := by
    have h0 := congrArg (fun x : SecM A L (k : ℤ) (baseAt t') =>
      (x : ∀ j, Γ((baseAt t' ⊗ A).left, (LPow A L (k : ℤ) (baseAt t')).U j)) q) hc
    rw [Submodule.coe_sum] at h0
    refine Eq.trans h0.symm ?_
    erw [Finset.sum_apply]
    rfl
  have hle : LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q ≤
      e.inv ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => (snd (baseAt t') A).left) q :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.wchart_pull_le' L (fun _ : Fin 1 => (snd (baseAt t') A).left)
      (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) (fun _ => (k : ℤ)) e.inv (fun _ => by rw [e2, hψ]) q
  have h1 : (e.inv.appLE _ _ hle).hom (s''.f q) = s.f q := by
    refine (appLE_appLE_eq (f := e.inv) (g := e.hom) e.inv_hom_id
      (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q)
      (LB.wchart L (fun _ : Fin 1 => (snd (baseAt t') A).left) q)
      (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q) _ hle (fun _ h => h) (s.f q)).trans ?_
    exact id_appLE_self _ _ _
  have h2 : ∀ r : Γ((baseAt t').left, ⊤),
      (e.inv.appLE _ _ hle).hom (liftHom A ((LPow A L (k : ℤ) (baseAt t')).U q) r) =
        (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q)
          (fun _ _ => trivial)).hom r := fun r =>
    appLE_appLE_eq (f := e.inv) (g := (fst (baseAt t') A).left) e3 ⊤ _ _ (fun _ _ => trivial) hle _ r
  have h3 : ∀ i, (e.inv.appLE _ _ hle).hom ((b' i).f q) =
      (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) q)
        (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q)
        (GlobalTheory.HomFixMat.wchart_comp_le L ψA (snd (topS Rg) A).left q)).hom ((bA i).f q) := fun i =>
    appLE_appLE_eq (f := e.inv) (g := (homAt t' ▷ A).left) e4 _ _ _ _ hle _ ((bA i).f q)
  rw [← h1, hq]
  erw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  erw [map_mul, h2, h3]

end GlobalTheory.HomFixMat
