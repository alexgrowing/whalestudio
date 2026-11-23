import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFacOfClosedPoint

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section

namespace GlobalTheory.ZJ.TestNorm

open CubeGen

variable {p : ℕ} [Fact p.Prime] {X Y Z : Scheme.{0}}

abbrev z₀ (p : ℕ) [Fact p.Prime] : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)

def sn (p : ℕ) [Fact p.Prime] : (Sp (PadicAlgCl p)).presheaf.stalk (z₀ p) →* ℝ :=
  (normHom : PadicAlgCl p →*₀ ℝ).toMonoidHom.comp (ev (z₀ p)).toRingHom.toMonoidHom

def un (p : ℕ) [Fact p.Prime] : ((Sp (PadicAlgCl p)).presheaf.stalk (z₀ p))ˣ →* ℝ :=
  (sn p).comp (Units.coeHom _)

theorem sn_val (u : ((Sp (PadicAlgCl p)).presheaf.stalk (z₀ p))ˣ) : sn p u.val = un p u := rfl

theorem un_pos (u : ((Sp (PadicAlgCl p)).presheaf.stalk (z₀ p))ˣ) : 0 < un p u :=
  norm_pos_iff.2 (u.isUnit.map (ev (z₀ p))).ne_zero

theorem sn_gs (x : Sp (PadicAlgCl p) ⟶ X) {U : X.Opens} (h : x (z₀ p) ∈ U) (a : Γ(X, U)) :
    sn p (gs x (z₀ p) U a) = ‖valF x U a‖ := congrArg norm (ev_gs x _ h a)

theorem un_gm (x : Sp (PadicAlgCl p) ⟶ X) {U : X.Opens} (h : x (z₀ p) ∈ U) (a : Γ(X, U)ˣ) :
    un p (gm x (z₀ p) U a) = ‖valF x U a.val‖ := congrArg norm (ev_gm x _ h a)

theorem gs_comp (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ q) z U a = (r.stalkMap z).hom (gs q (r z) U a) := by
  rw [← gs_pull r q z U h, gs_stalkMap r z (q ⁻¹ᵁ U) h, gs_pull (𝟙 Y) q (r z) U h, Category.id_comp]

theorem gm_comp (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (r ≫ q) z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm q (r z) U a) := by
  refine Units.ext ?_
  rw [← gs_unit (r ≫ q) z U h, gs_comp r q z U h, gs_unit q (r z) U h]
  rfl

theorem mem_of_cPt (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) : ⊤ ≤ b ⁻¹ᵁ U :=
  fun y _ => (IsLocalRing.specializes_closedPoint y).mem_open (b ⁻¹ᵁ U).isOpen h

theorem gen_mem (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) : (gPt p ≫ b) (z₀ p) ∈ U :=
  mem_of_cPt b h (show gPt p (z₀ p) ∈ (⊤ : (Sp (OO p)).Opens) from trivial)

theorem isUnit_iff_norm (v : OO p) : IsUnit v ↔ ‖(v : PadicAlgCl p)‖ = 1 := by
  have le : ∀ u : OO p, ‖(u : PadicAlgCl p)‖ ≤ 1 := fun u =>
    (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 u.2
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h.exists_right_inv
    have e : ‖(v : PadicAlgCl p)‖ * ‖(u : PadicAlgCl p)‖ = 1 := by
      rw [← norm_mul]
      exact (congrArg (fun t : OO p => ‖(t : PadicAlgCl p)‖) hu).trans norm_one
    have := le u
    have := le v
    have := norm_nonneg (v : PadicAlgCl p)
    nlinarith
  · intro h
    have h0 : (v : PadicAlgCl p) ≠ 0 := norm_pos_iff.1 (by rw [h]; exact one_pos)
    refine IsUnit.of_mul_eq_one ⟨(v : PadicAlgCl p)⁻¹,
      (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).2 (by rw [norm_inv, h, inv_one])⟩ ?_
    exact Subtype.ext (mul_inv_cancel₀ h0)

theorem sn_integral (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) (a : Γ(X, U)) :
    sn p (gs (gPt p ≫ b) (z₀ p) U a) ≤ 1 ∧
      (sn p (gs (gPt p ≫ b) (z₀ p) U a) = 1 ↔ b (cPt p) ∈ X.basicOpen a) := by
  have h' := mem_of_cPt b h
  have hg := gen_mem b h
  let v : OO p := (Scheme.ΓSpecIso (CommRingCat.of (OO p))).hom.hom ((b.appLE U ⊤ h').hom a)
  have e : valF (gPt p ≫ b) U a = (v : PadicAlgCl p) := by
    rw [valF, dif_pos ((top_le_iff_mem _ U _).2 hg)]
    have e₁ := Scheme.Hom.appLE_comp_appLE (gPt p) b U ⊤ ⊤ h' le_top
    have e₂ := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (OO p).subtype)
    have e₃ : (gPt p).appLE ⊤ ⊤ le_top = (gPt p).appTop := (Scheme.Hom.app_eq_appLE _).symm
    rw [← e₁, e₃]
    exact congrArg (fun q => q.hom ((b.appLE U ⊤ h').hom a)) e₂
  rw [sn_gs _ hg, e]
  refine ⟨(mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 v.2, (isUnit_iff_norm v).symm.trans ?_⟩
  have e₄ : (Sp (OO p)).basicOpen ((b.appLE U ⊤ h').hom a) = PrimeSpectrum.basicOpen v :=
    basicOpen_eq_of_affine' _
  have e₅ := Scheme.basicOpen_appLE b ⊤ U h' a
  have e₆ : cPt p ∈ (Sp (OO p)).basicOpen ((b.appLE U ⊤ h').hom a) ↔ b (cPt p) ∈ X.basicOpen a := by
    erw [e₅]
    exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  rw [← e₆, e₄]
  exact (IsLocalRing.notMem_maximalIdeal).symm

theorem un_integral (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) (a : Γ(X, U)ˣ) :
    un p (gm (gPt p ≫ b) (z₀ p) U a) = 1 := by
  rw [← sn_val, ← gs_unit _ _ _ (gen_mem b h)]
  refine (sn_integral b h a.val).2.2 ?_
  rw [Scheme.basicOpen_of_isUnit _ a.isUnit]
  exact h

theorem un_eq_of_charts {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {K : Type} [Field K]
    [Algebra V K] [IsFractionRing V K] {H HK : Scheme.{0}} {f : H ⟶ Sp V} [Smooth f] [GeometricallyIntegral f]
    {j : HK ⟶ H} {fK : HK ⟶ Sp K} (hK : IsPullback j fK f (spMap (algebraMap V K))) (e : Sp V ⟶ H)
    (he : e ≫ f = 𝟙 _) {α : Type} (U : α → H.Opens) (g : ∀ a b, Γ(H, U a ⊓ U b)ˣ) (r : ∀ a, Γ(HK, j ⁻¹ᵁ U a)ˣ)
    (hU : ∀ x, ∃ a, x ∈ U a)
    (hr : ∀ a a' x, j x ∈ U a → j x ∈ U a' →
      gm (𝟙 HK) x _ (r a) = gm j x _ (g a a') * gm (𝟙 HK) x _ (r a')) :
    ∃ u : Γ(Sp K, ⊤)ˣ, ∀ (c : Sp (OO p) ⟶ H) (cK : Sp (PadicAlgCl p) ⟶ HK), cK ≫ j = gPt p ≫ c → ∀ a,
      c (cPt p) ∈ U a → un p (gm cK (z₀ p) _ (r a)) = un p (gm (cK ≫ fK) (z₀ p) ⊤ u) := by
  have hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  let eK : Sp K ⟶ HK := hK.lift (spMap (algebraMap V K) ≫ e) (𝟙 _) (by simp [he])
  have h₁ : eK ≫ j = spMap (algebraMap V K) ≫ e := hK.lift_fst _ _ _
  have h₂ : eK ≫ fK = 𝟙 _ := hK.lift_snd _ _ _
  obtain ⟨a₀, ha₀⟩ := hU (e (IsLocalRing.closedPoint V))
  have hA : ⊤ ≤ e ⁻¹ᵁ U a₀ := fun y _ => (IsLocalRing.specializes_closedPoint y).mem_open (e ⁻¹ᵁ U a₀).isOpen ha₀
  have hA'' : ⊤ ≤ eK ⁻¹ᵁ (j ⁻¹ᵁ U a₀) := fun y _ => by
    show (eK ≫ j) y ∈ U a₀
    rw [h₁]
    exact hA (show spMap (algebraMap V K) y ∈ (⊤ : (Sp V).Opens) from trivial)
  let u : Γ(Sp K, ⊤)ˣ := res hA'' (pullU eK _ (r a₀))
  let r' : ∀ a, Γ(HK, j ⁻¹ᵁ U a)ˣ := fun a => r a * res (le_top : j ⁻¹ᵁ U a ≤ fK ⁻¹ᵁ ⊤) (pullU fK ⊤ u⁻¹)
  have v : ∀ (Z : Scheme.{0}) (q : Z ⟶ HK) (z : Z) a, j (q z) ∈ U a →
      gm q z _ (r' a) = gm q z _ (r a) * (gm (q ≫ fK) z ⊤ u)⁻¹ := fun Z q z a h =>
    (map_mul _ _ _).trans (congrArg (_ * ·) (((gm_res q z _ h _).trans (gm_pull q fK z ⊤ trivial _)).trans
      (map_inv _ _)))
  obtain ⟨s, ⟨hs₁, -, hs₂⟩, -⟩ := DvrModel.existsUnique_isUnit_appLE_eq hK hs (U := U) (g := fun a b => (g a b).val)
    (W := fun a => j ⁻¹ᵁ U a) (fun _ => rfl) hU (fun a b => (g a b).isUnit) (r := fun a => (r' a).val)
    (fun a b => fn_ext fun x hx => by
      refine (gs_res (𝟙 HK) x _ hx _).trans (Eq.trans ?_ ((gs_mul (𝟙 HK) x _ hx _ _).trans
        (congrArg₂ (· * ·) (gs_appLE j _ _ _ (𝟙 HK) x hx _) (gs_res (𝟙 HK) x _ hx _))).symm)
      rw [Category.id_comp, gs_unit (𝟙 HK) x _ hx.1, gs_unit (𝟙 HK) x _ hx.2, gs_unit j x (U a ⊓ U b) hx,
        v _ (𝟙 HK) x a hx.1, v _ (𝟙 HK) x b hx.2, hr a b x hx.1 hx.2, _root_.mul_assoc, Units.val_mul])
    (fun a => (r' a).isUnit) he h₁ (A := ⊤) trivial hA (A' := ⊤) rfl hA'' (u := 1) isUnit_one (by
      rw [map_one]
      refine fn_ext fun y hy => ?_
      refine Eq.trans ?_ (gs_appLE eK _ _ _ (𝟙 _) y hy _).symm
      rw [Category.id_comp, gs_unit eK y _ (hA'' hy), v _ eK y a₀ (hA'' hy), h₂]
      have : gm (𝟙 (Sp K)) y ⊤ u = gm eK y _ (r a₀) := by
        refine ((gm_res _ y _ hy _).trans (gm_pull (𝟙 _) eK y _ (hA'' hy) _)).trans ?_
        rw [Category.id_comp]
      rw [this, mul_inv_cancel, gs_eq _ y ⊤ hy, map_one, map_one, Units.val_one])
  refine ⟨u, fun c cK hc a ha => ?_⟩
  have hm : j (cK (z₀ p)) ∈ U a := by
    show (cK ≫ j) _ ∈ U a
    rw [hc]
    exact gen_mem c ha
  have e₁ : un p (gm cK (z₀ p) _ (r' a)) = 1 := by
    rw [← un_integral c ha (hs₁ a).unit, ← hc]
    refine congrArg (un p) (Units.ext ?_)
    rw [← gs_unit cK _ _ hm, ← gs_unit (cK ≫ j) _ _ hm, ← hs₂ a]
    exact gs_appLE j _ _ _ cK _ hm _
  rw [v _ cK _ a hm, map_mul, map_inv] at e₁
  exact (mul_inv_eq_one₀ (un_pos _).ne').1 e₁

theorem un_eq_of_fine_charts {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {K : Type} [Field K]
    [Algebra V K] [IsFractionRing V K] {H HK : Scheme.{0}} {f : H ⟶ Sp V} [Smooth f] [GeometricallyIntegral f]
    {j : HK ⟶ H} {fK : HK ⟶ Sp K} (hK : IsPullback j fK f (spMap (algebraMap V K))) (e : Sp V ⟶ H)
    (he : e ≫ f = 𝟙 _) {α κ : Type} (U : α → H.Opens) (g : ∀ a b, Γ(H, U a ⊓ U b)ˣ) (W : α → κ → HK.Opens)
    (r : ∀ a b, Γ(HK, W a b)ˣ) (hU : ∀ x, ∃ a, x ∈ U a) (hW : ∀ a x, j x ∈ U a ↔ ∃ b, x ∈ W a b)
    (hr : ∀ a b a' b' x, x ∈ W a b → x ∈ W a' b' →
      gm (𝟙 HK) x _ (r a b) = gm j x _ (g a a') * gm (𝟙 HK) x _ (r a' b'))
    {c c' : Sp (OO p) ⟶ H} {cK cK' : Sp (PadicAlgCl p) ⟶ HK} (hc : cK ≫ j = gPt p ≫ c) (hc' : cK' ≫ j = gPt p ≫ c')
    (h : c ≫ f = c' ≫ f) {a a' : α} {b b' : κ} (ha : c (cPt p) ∈ U a) (ha' : c' (cPt p) ∈ U a')
    (hb : cK (z₀ p) ∈ W a b) (hb' : cK' (z₀ p) ∈ W a' b') :
    un p (gm cK (z₀ p) _ (r a b)) = un p (gm cK' (z₀ p) _ (r a' b')) := by
  have le : ∀ a b, W a b ≤ j ⁻¹ᵁ U a := fun a b x hx => (hW a x).2 ⟨b, hx⟩
  choose R hR using fun a => glue_unit (j ⁻¹ᵁ U a) (W a) (le a)
    (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ((hW a x).1 hx)) (r a) (fun b b' x hx => by
      rw [hr a b a b' x hx.1 hx.2, mul_eq_right.1 (hr a b a b x hx.1 hx.1).symm, _root_.one_mul])
  have v : ∀ (Z : Scheme.{0}) (q : Z ⟶ HK) (z : Z) a b, q z ∈ W a b → gm q z _ (r a b) = gm q z _ (R a) :=
    fun Z q z a b h => by rw [← hR a b, gm_res q z _ h]
  obtain ⟨u, hu⟩ := un_eq_of_charts (p := p) hK e he U g R hU fun a a' x hx hx' => by
    obtain ⟨b, hb⟩ := (hW a x).1 hx
    obtain ⟨b', hb'⟩ := (hW a' x).1 hx'
    rw [← v _ (𝟙 HK) x a b hb, ← v _ (𝟙 HK) x a' b' hb', hr a b a' b' x hb hb']
  have := DvrModel.isOpenImmersion_generic (IsPullback.of_id_snd (f := spMap (algebraMap V K)))
  rw [v _ _ _ _ _ hb, v _ _ _ _ _ hb', hu c cK hc a ha, hu c' cK' hc' a' ha']
  refine congrArg (fun q => un p (gm q (z₀ p) ⊤ u)) ?_
  rw [← cancel_mono (spMap (algebraMap V K)), Category.assoc, Category.assoc, ← hK.w, ← Category.assoc, hc,
    ← Category.assoc, hc', Category.assoc, Category.assoc, h]

theorem exists_norm_ext {L : LB X} (hL : L.IsLB) (x : Sp (PadicAlgCl p) ⟶ X) (S : L.ι → ℝ → Prop)
    (hS : ∀ j t, S j t → 0 < t ∧ x (z₀ p) ∈ L.U j)
    (hS' : ∀ j t j' t', S j t → S j' t' → un p (gm x (z₀ p) _ (L.g j j')) * t = t') :
    ∃ n : L.ι → ℝ, (∀ j, 0 < n j) ∧ (∀ j j', x (z₀ p) ∈ L.U j → x (z₀ p) ∈ L.U j' →
      un p (gm x (z₀ p) _ (L.g j j')) * n j = n j') ∧ ∀ j t, S j t → n j = t := by
  classical
  obtain ⟨i, t₀, h₀, hi, H⟩ : ∃ i t₀, 0 < t₀ ∧ x (z₀ p) ∈ L.U i ∧
      ∀ j t, S j t → un p (gm x (z₀ p) _ (L.g i j)) * t₀ = t := by
    by_cases h : ∃ j t, S j t
    · obtain ⟨i, t₀, h⟩ := h
      exact ⟨i, t₀, (hS _ _ h).1, (hS _ _ h).2, fun j t h' => hS' _ _ _ _ h h'⟩
    · obtain ⟨i, hi⟩ := exists_chart hL (x (z₀ p))
      exact ⟨i, 1, one_pos, hi, fun j t h' => absurd ⟨j, t, h'⟩ h⟩
  refine ⟨fun j => un p (gm x (z₀ p) _ (L.g i j)) * t₀, fun j => mul_pos (un_pos _) h₀, fun j j' hj hj' => ?_, H⟩
  rw [← _root_.mul_assoc, ← map_mul, _root_.mul_comm (gm x _ _ _), gm_cocycle hL x _ hi hj hj']

end GlobalTheory.ZJ.TestNorm
