import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.EmbPull

open ReciprocityTheory.ChartRestriction.G.Out VVRank TopologicalSpace

section General

variable {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem secCoord_of_germ {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} {I : Type}
    {σ : I → (LB.LinComb L φ ε).Sec} {σ' : I → (LB.LinComb L φ' ε).Sec} {R : Type} [CommRing R]
    {x : Sp R ⟶ Y} {x' : Sp R ⟶ Y'} (e : ∀ k, x ≫ φ k = x' ≫ φ' k)
    (hσ : ∀ i y j, x y ∈ LB.wchart L φ j → gs x' y (LB.wchart L φ' j) ((σ' i).f j) = gs x y (LB.wchart L φ j) ((σ i).f j))
    {w : I → R} (H : SecCoord _ σ x w) : SecCoord _ σ' x' w := by
  obtain ⟨τ, hτ, H⟩ := H
  have mem : ∀ y j, x' y ∈ LB.wchart L φ' j → x y ∈ LB.wchart L φ j := fun y j hy =>
    Set.mem_iInter.2 fun k => by
      have : (x' ≫ φ' k) y ∈ L.U (j k) := Set.mem_iInter.1 hy k
      rw [← e] at this
      exact this
  have le : ∀ j : PUnit → K → L.ι, ((LB.LinComb L φ' ε).pull x').U j ≤ ((LB.LinComb L φ ε).pull x).U j :=
    fun j y hy => mem_pull.2 (mem y _ (mem_pull.1 hy))
  refine SegreCoord.secCoord_mk (fun j => resG (Sp R) (le j) (τ.s j).val)
    (fun y j => gs (𝟙 _) y _ (τ.s fun _ => j).val) (fun j y hy => gs_res _ y (le j) hy _) (fun y j hy => ?_)
    (fun y j j' hy hy' => ?_) (fun y j i hy => ?_)
  · have hy₁ : y ∈ ((LB.LinComb L φ ε).pull x).U (fun _ => j) := mem_pull.2 (mem y j hy)
    exact (congrArg IsUnit (gs_unit (𝟙 _) y _ hy₁ _)).mpr (Units.isUnit _)
  · have hy₁ : y ∈ ((LB.LinComb L φ ε).pull x).U (fun _ => j) := mem_pull.2 (mem y j hy)
    have hy₂ : y ∈ ((LB.LinComb L φ ε).pull x).U (fun _ => j') := mem_pull.2 (mem y j' hy')
    have q := gen_trans (φ := fun _ : PUnit => x) (ε := fun _ => 1) hτ (𝟙 _) y hy₁ hy₂
    refine (gs_unit (𝟙 _) y _ hy₁ _).trans ((congrArg Units.val q).trans ((Units.val_mul _ _).trans
      (congrArg₂ (· * ·) (congrArg Units.val ?_) (gs_unit (𝟙 _) y _ hy₂ _).symm)))
    unfold trF
    rw [Fintype.prod_unique, zpow_one, Category.id_comp]
    refine (gm_linComb L φ ε x y j j' (mem y j hy) (mem y j' hy')).trans
      (Eq.trans ?_ (gm_linComb L φ' ε x' y j j' hy hy').symm)
    simp only [e]
  · have hy' : y ∈ ((LB.LinComb L φ ε).pull x).U (fun _ => j) := mem_pull.2 (mem y j hy)
    have := congrArg (gs (𝟙 _) y _) (H i (fun _ => j) (fun z hz => mem_pull.1 hz))
    refine (hσ i y j (mem y j hy)).trans ((SegreCoord.gs_appLE x y _ hy' _).symm.trans
      (this.trans ((gs_mul _ y _ hy' _ _).trans (congrArg (· * _) ?_))))
    exact (gs_res _ y _ hy' _).trans (SegreCoord.ev_eq y _).symm

theorem gs_pullTo {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} (s : (LB.LinComb L φ ε).Sec) (h : Y' ⟶ Y)
    (e : ∀ k, h ≫ φ k = φ' k) {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (j : K → L.ι) (hz : r z ∈ LB.wchart L φ' j) :
    gs r z (LB.wchart L φ' j) ((pullTo s h e).f j) = gs (r ≫ h) z (LB.wchart L φ j) (s.f j) :=
  (gs_res r z (wchart_le_of_eq h e j) hz _).trans (gs_pull r h z _ (wchart_le_of_eq h e j hz) _)

theorem mem_wchart_of_eq {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} (h : Y' ⟶ Y)
    (e : ∀ k, h ≫ φ k = φ' k) (z : Y') (j : K → L.ι) (hz : h z ∈ LB.wchart L φ j) : z ∈ LB.wchart L φ' j := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k

theorem secCoord_pullTo {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} {I : Type}
    (σ : I → (LB.LinComb L φ ε).Sec) (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) {R : Type} [CommRing R]
    (y : Sp R ⟶ Y') (w : I → R) :
    SecCoord _ (fun i => pullTo (σ i) h e) y w ↔ SecCoord _ σ (y ≫ h) w := by
  have e' : ∀ k, y ≫ φ' k = (y ≫ h) ≫ φ k := fun k => by rw [Category.assoc, e]
  exact ⟨secCoord_of_germ e' fun i z j hz => (gs_pullTo (σ i) h e y z j hz).symm,
    secCoord_of_germ (fun k => (e' k).symm) fun i z j hz =>
      gs_pullTo (σ i) h e y z j (mem_wchart_of_eq h e _ j hz)⟩

theorem exists_pow_extend [CompactSpace Y] [QuasiSeparatedSpace Y] (hL : L.IsLB) {φ : K → (Y ⟶ X)}
    {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) [IsOpenImmersion h] (e : ∀ k, h ≫ φ k = φ' k) (a : Γ(Y, ⊤))
    (ha : h.opensRange = Y.basicOpen a) (x : (LB.LinComb L φ' ε).Sec) :
    ∃ (n : ℕ) (u : (LB.LinComb L φ ε).Sec), ∀ j z, z ∈ LB.wchart L φ' j →
      gs (𝟙 _) z (LB.wchart L φ' j) ((pullTo u h e).f j) = gs h z ⊤ a ^ n * gs (𝟙 _) z (LB.wchart L φ' j) (x.f j) := by
  have hz : ∀ z, h z ∈ Y.basicOpen a := fun z => ha.le ⟨z, rfl⟩
  choose θ hθ using fun j => PushInv.exists_lift h (Y.basicOpen a ⊓ (LB.LinComb L φ ε).U j)
    (inf_le_left.trans ha.ge) (LB.wchart L φ' j) (fun z hz => mem_wchart_of_eq h e z j hz.2) (x.f j)
  have hθ' : θ ∈ secOn (LB.LinComb L φ ε) (Y.basicOpen a) := LBGerm.mem_secOn_of_germ θ fun g i j hg hi hj => by
    obtain ⟨z, rfl⟩ := ha.ge hg
    apply PushInv.stalk_inj h z
    have hi' := mem_wchart_of_eq h e z i hi
    have hj' := mem_wchart_of_eq h e z j hj
    rw [map_mul, ← gs_stalkMap _ z (Y.basicOpen a ⊓ (LB.LinComb L φ ε).U i) ⟨hg, hi⟩,
      ← gs_stalkMap _ z (Y.basicOpen a ⊓ (LB.LinComb L φ ε).U j) ⟨hg, hj⟩,
      ← PushInv.gm_comp _ (𝟙 _) z ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j) ⟨hi, hj⟩, Category.comp_id]
    have e₁ := hθ i _ (𝟙 _) z ⟨hg, hi⟩
    have e₂ := hθ j _ (𝟙 _) z ⟨hg, hj⟩
    rw [Category.id_comp] at e₁ e₂
    rw [e₁, e₂]
    refine (sec_trans x (𝟙 _) z hi' hj').trans (congrArg (fun q : (Y'.presheaf.stalk z)ˣ => q.val * _) ?_)
    refine Eq.trans ?_ (gm_linComb L φ ε h z i j hi hj).symm
    simp only [trF, e, Category.id_comp]
  obtain ⟨n, t, ht⟩ := AbLaw.SecOn.exists_pow_smul_eq_restrict (LB.isLB_linComb hL φ ε) (V := ⊤) isCompact_univ
    isQuasiSeparated_univ a le_top rfl ((AbLaw.SecOn.equivFamilies _ _).symm ⟨θ, hθ'⟩)
  refine ⟨n, AbLaw.SecOn.topEquiv _ t, fun j z hj => ?_⟩
  have hj' : h z ∈ (LB.LinComb L φ ε).U j := wchart_le_of_eq h e j hj
  have hm : h z ∈ Y.basicOpen a ⊓ (LB.LinComb L φ ε).U j := ⟨hz z, hj'⟩
  have q := congrArg (fun s => gs h z _ (GlobalTheory.LB.coord s j)) ht
  have e₁ := hθ j _ (𝟙 _) z hm
  rw [Category.id_comp] at e₁
  rw [gs_pullTo _ _ _ _ _ _ hj, Category.id_comp, ← e₁]
  refine (gs_res h z _ hj' _).trans ((gs_res h z _ hm _).symm.trans (q.symm.trans ((gs_mul h z _ hm _ _).trans
    (congrArg₂ (· * ·) ?_ rfl))))
  exact (gs_res h z _ hm _).trans ((LBGerm.gs_pow h z _ (hz z) _ _).trans (congrArg (· ^ n) (gs_res h z _ (hz z) _)))

theorem exists_pow_kill [CompactSpace Y] (hL : L.IsLB) {φ : K → (Y ⟶ X)}
    {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) [IsOpenImmersion h] (e : ∀ k, h ≫ φ k = φ' k) (a : Γ(Y, ⊤))
    (ha : h.opensRange = Y.basicOpen a) (u : (LB.LinComb L φ ε).Sec) (hu : ∀ j, (pullTo u h e).f j = 0) :
    ∃ n : ℕ, ∀ j, resG Y le_top (a ^ n) * u.f j = 0 := by
  obtain ⟨n, hn⟩ := AbLaw.SecOn.exists_pow_smul_eq_zero (LB.isLB_linComb hL φ ε) (V := ⊤) isCompact_univ a le_top rfl
    ((AbLaw.SecOn.topEquiv _).symm u) (GlobalTheory.LB.sec_ext fun j => fn_ext fun y hy => by
      obtain ⟨z, rfl⟩ := ha.ge hy.1
      have hj := mem_wchart_of_eq h e z j hy.2
      have q := (gs_pullTo u h e (𝟙 _) z j hj).symm.trans ((congrArg (gs _ z _) (hu j)).trans (LBGerm.gs_zero _ z _ hj))
      rw [Category.id_comp] at q
      replace q := (gs_stalkMap h z (LB.wchart L φ j) hy.2 _).symm.trans q
      have hy' : (𝟙 Y : Y ⟶ Y) (h z) ∈ ⊤ ⊓ (LB.LinComb L φ ε).U j := ⟨trivial, hy.2⟩
      refine (gs_res (𝟙 Y) (h z) (inf_le_inf_right _ le_top) hy _).trans ((gs_res (𝟙 Y) (h z) inf_le_right hy' (u.f j)).trans
        (Eq.trans ?_ (LBGerm.gs_zero (𝟙 Y) (h z) _ hy).symm))
      exact PushInv.stalk_inj h z (q.trans (map_zero _).symm))
  have := congrArg (AbLaw.SecOn.topEquiv _) hn
  rw [map_smul, LinearEquiv.apply_symm_apply, map_zero] at this
  exact ⟨n, fun j => congrArg (fun q => q.f j) this⟩

theorem exists_pow_mul_extend [IsAffine Y] (f : Γ(Y, ⊤)) (d : Γ((Y.basicOpen f).toScheme, ⊤)) :
    ∃ (m : ℕ) (d₀ : Γ(Y, ⊤)), (Y.basicOpen f).ι.appTop.hom d₀ = (Y.basicOpen f).ι.appTop.hom (f ^ m) * d := by
  have main : ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsOpenImmersion i], i.opensRange = Y.basicOpen f → ∀ d : Γ(Z, ⊤),
      ∃ (m : ℕ) (d₀ : Γ(Y, ⊤)), i.appTop.hom d₀ = i.appTop.hom (f ^ m) * d := fun Z i _ hi d => by
    obtain ⟨c, hc⟩ := PushInv.exists_lift i (Y.basicOpen f) hi.ge ⊤ le_top d
    obtain ⟨m, d₀, hd₀⟩ := exists_eq_pow_mul_of_isAffineOpen Y ⊤ (isAffineOpen_top _) f c
    have hd : resG Y (Y.basicOpen_le f) d₀ = resG Y (Y.basicOpen_le f) f ^ m * c := hd₀
    refine ⟨m, d₀, fn_ext fun z _ => ?_⟩
    have hz : (𝟙 Z ≫ i) z ∈ Y.basicOpen f := hi.le ⟨z, rfl⟩
    have q := congrArg (gs (𝟙 Z ≫ i) z (Y.basicOpen f)) hd
    rw [gs_res _ z _ hz, gs_mul _ z _ hz, LBGerm.gs_pow _ z _ hz, gs_res _ z _ hz, hc _ _ z hz,
      ← LBGerm.gs_pow _ z ⊤ trivial] at q
    have k : ∀ a, gs (𝟙 Z) z ⊤ (i.appTop.hom a) = gs (𝟙 Z ≫ i) z ⊤ a := fun a => gs_pull (𝟙 Z) i z ⊤ trivial a
    rw [gs_mul _ z ⊤ trivial, k, k, q]
  exact main _ _ (Scheme.Opens.opensRange_ι _) d

theorem map_sub_eq_zero {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [AddCommGroup M'] [Module R M]
    [Module R' M'] (σ : R →+* R') (φ : M →ₛₗ[σ] M') (s t : M) (b : M') (a c d₀ r : R) (d : R')
    (e₁ : σ r • φ t = σ c • b) (hd : φ s = d • b) (hd₀ : σ d₀ = σ a * d) : φ ((a * c) • s - (d₀ * r) • t) = 0 := by
  rw [map_sub, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_mul, map_mul, hd, hd₀, mul_smul, mul_smul,
    mul_smul, e₁, smul_comm d, sub_self]

end General

variable {S : Scheme.{0}} (P : PolAV S) {T T' : Over S}

theorem isPullback_whisker (A : Over S) (h : T' ⟶ T) :
    IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  refine IsPullback.of_right ?_ (by rw [← Over.comp_left, whiskerRight_fst, Over.comp_left])
    (IsPullback.of_hasPullback T.hom A.hom).flip
  have e : (h ▷ A).left ≫ pullback.snd T.hom A.hom = pullback.snd T'.hom A.hom :=
    congrArg CommaMorphism.left (whiskerRight_snd h A)
  rw [e, Over.w]
  exact (IsPullback.of_hasPullback T'.hom A.hom).flip

theorem qcqs [IsAffine T.left] : CompactSpace (T ⊗ P.A).left ∧ QuasiSeparatedSpace (T ⊗ P.A).left := by
  have := P.isAb.proper
  have : IsProper (fst T P.A).left := inferInstanceAs (IsProper (pullback.fst T.hom P.A.hom))
  exact ⟨QuasiCompact.compactSpace_of_compactSpace (fst T P.A).left,
    quasiSeparatedSpace_of_quasiSeparated (fst T P.A).left⟩

theorem isOpenImmersion_whisker (W : T.left.Opens) : IsOpenImmersion (overResι W ▷ P.A).left :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_whisker P.A (overResι W)).flip
    (inferInstanceAs (IsOpenImmersion W.ι))

theorem opensRange_whisker (f : Γ(T.left, ⊤)) :
    haveI := isOpenImmersion_whisker P (T.left.basicOpen f)
    (overResι (T.left.basicOpen f) ▷ P.A).left.opensRange =
      (T ⊗ P.A).left.basicOpen ((fst T P.A).left.appTop.hom f) := by
  have H := isPullback_whisker P.A (overResι (T.left.basicOpen f))
  refine Eq.trans ?_ (Scheme.preimage_basicOpen_top (fst T P.A).left f)
  refine le_antisymm ?_ fun y hy => ?_
  · rintro _ ⟨z, rfl⟩
    show ((overResι (T.left.basicOpen f) ▷ P.A).left ≫ (fst T P.A).left) z ∈ T.left.basicOpen f
    rw [H.w]
    exact ((fst _ P.A).left z).2
  · obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback H y ⟨_, hy⟩ rfl
    exact ⟨z, hz⟩

theorem exists_pow_extend_secM [IsAffine T.left] (a : ℤ) (f : Γ(T.left, ⊤))
    (x : SecM P.A P.L a (overRes (T.left.basicOpen f))) :
    ∃ (n : ℕ) (u : SecM P.A P.L a T), pullM P.A P.L a (overResι (T.left.basicOpen f)) u =
      (overResι (T.left.basicOpen f)).left.appTop.hom (f ^ n) • x := by
  obtain ⟨_, _⟩ := qcqs P (T := T)
  have := isOpenImmersion_whisker P (T.left.basicOpen f)
  obtain ⟨n, u, hu⟩ := exists_pow_extend P.isLB (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => a)
    (overResι (T.left.basicOpen f) ▷ P.A).left (fun _ => whisker_snd_left P.A _) _ (opensRange_whisker P f)
    (SecM.toSec P.A x)
  refine ⟨n, SecM.ofSec P.A u, Subtype.ext (funext fun j => fn_ext fun z hz => (hu j z hz).trans ?_)⟩
  refine Eq.trans (congrArg (· * _) ?_) (PushInv.gs_smul P.A P.L _ a _ x j z hz).symm
  refine Eq.trans ?_ (gs_pull _ (overResι (T.left.basicOpen f)).left z ⊤ trivial _).symm
  rw [LBGerm.gs_pow _ z ⊤ trivial, ← (isPullback_whisker P.A (overResι (T.left.basicOpen f))).w]
  exact congrArg (· ^ n) (gs_pull _ (fst T P.A).left z ⊤ trivial f)

theorem exists_pow_kill_secM [IsAffine T.left] (a : ℤ) (f : Γ(T.left, ⊤)) (u : SecM P.A P.L a T)
    (hu : pullM P.A P.L a (overResι (T.left.basicOpen f)) u = 0) : ∃ n : ℕ, f ^ n • u = 0 := by
  obtain ⟨_, _⟩ := qcqs P (T := T)
  have := isOpenImmersion_whisker P (T.left.basicOpen f)
  obtain ⟨n, hn⟩ := exists_pow_kill P.isLB (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => a)
    (overResι (T.left.basicOpen f) ▷ P.A).left (fun _ => whisker_snd_left P.A _) _ (opensRange_whisker P f)
    (SecM.toSec P.A u) (fun j => congrFun (congrArg Subtype.val hu) j)
  refine ⟨n, Subtype.ext (funext fun j => Eq.trans ?_ (hn j))⟩
  rw [← map_pow]
  rfl

theorem isGenSec_pullS (hS : SecBaseChangeAnySt) [IsAffine T.left] [IsAffine T'.left] (h : T' ⟶ T)
    {th : LB.Sec (LPow P.A P.L 1 T)} (H : IsGenSec P.A P.L 1 th) : IsGenSec P.A P.L 1 (pullS P.A 1 h th) := by
  intro s
  let I : Ideal Γ(T'.left, ⊤) := (Submodule.span Γ(T'.left, ⊤)
    {pullM P.A P.L 1 h (SecM.ofSec P.A th)}).comap (LinearMap.toSpanSingleton _ _ (SecM.ofSec P.A s))
  have key : ∀ p : T'.left, ∃ f ∈ I, p ∈ T'.left.basicOpen f := fun p => by
    obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom (h.left p))
    have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
    obtain ⟨f, hf, hp⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨h.left p, hV⟩ trivial
    let f' := h.left.appTop.hom f
    have hf' : h.left ⁻¹ᵁ T.left.basicOpen f = T'.left.basicOpen f' := Scheme.preimage_basicOpen_top _ _
    let W := T.left.basicOpen f
    let W' := T'.left.basicOpen f'
    let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk
      (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hf y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
    let k₀ : W'.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι (W'.ι ≫ h.left) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hf'.ge y.2)
    have hk₀ : k₀ ≫ W.ι = W'.ι ≫ h.left := IsOpenImmersion.lift_fac _ _ _
    let k : overRes W' ⟶ overRes W := Over.homMk k₀ (by
      change k₀ ≫ W.ι ≫ T.hom = W'.ι ≫ T'.hom
      rw [← Category.assoc, hk₀, Category.assoc, Over.w])
    have hk : k ≫ overResι W = overResι W' ≫ h := Over.OverMorphism.ext hk₀
    have hW' : IsAffineOpen W' := (isAffineOpen_top _).basicOpen f'
    have : IsAffine (overRes W').left := hW'
    obtain ⟨c, hc⟩ := exists_basis P 1 b hb (overRes W') (k ≫ l)
    obtain ⟨n, u, hu⟩ := exists_pow_extend_secM P 1 f (pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)))
    obtain ⟨r, hr⟩ := H (SecM.toSec P.A u)
    have hr' : u = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
    have e₁ := congrArg (pullM P.A P.L 1 k) hu
    rw [LinearMap.map_smulₛₗ, pullM_comp _ P.isLB, pullM_comp _ P.isLB, hk, ← pullM_comp _ P.isLB, hr',
      LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ] at e₁
    have e₂ : k.left.appTop.hom ((overResι W).left.appTop.hom (f ^ n)) = (overResι W').left.appTop.hom (f' ^ n) :=
      (congrArg (fun q => q.left.appTop.hom (f ^ n)) hk).trans
        (congrArg (overResι W').left.appTop.hom (map_pow h.left.appTop.hom f n))
    rw [e₂] at e₁
    obtain ⟨d, hd⟩ : ∃ d : Γ((overRes W').left, ⊤), pullM P.A P.L 1 (overResι W') (SecM.ofSec P.A s) =
        d • pullM P.A P.L 1 (k ≫ l) (SecM.ofSec P.A (b hq.default)) := by
      have := c.sum_repr (pullM P.A P.L 1 (overResι W') (SecM.ofSec P.A s))
      rw [Fintype.sum_unique, hc] at this
      exact ⟨_, this.symm⟩
    obtain ⟨m, d₀, hd₀⟩ : ∃ (m : ℕ) (d₀ : Γ(T'.left, ⊤)), (overResι W').left.appTop.hom d₀ =
        (overResι W').left.appTop.hom (f' ^ m) * d := exists_pow_mul_extend f' d
    obtain ⟨N, hN⟩ := exists_pow_kill_secM P 1 f' ((f' ^ m * f' ^ n) • SecM.ofSec P.A s -
      (d₀ * h.left.appTop.hom r) • pullM P.A P.L 1 h (SecM.ofSec P.A th))
        (map_sub_eq_zero _ _ _ _ _ _ _ _ _ d e₁ hd hd₀)
    refine ⟨f' ^ N * (f' ^ m * f' ^ n), Submodule.mem_span_singleton.2 ⟨f' ^ N * (d₀ * h.left.appTop.hom r), ?_⟩, ?_⟩
    · rw [smul_sub, sub_eq_zero, ← mul_smul, ← mul_smul] at hN
      exact hN.symm
    · have hp' : p ∈ T'.left.basicOpen f' := hf'.le hp
      rw [Scheme.mem_basicOpen_top] at hp' ⊢
      simp only [map_mul, map_pow]
      exact (hp'.pow _).mul ((hp'.pow _).mul (hp'.pow _))
  have hI : Ideal.span (I : Set Γ(T'.left, ⊤)) = ⊤ :=
    (isAffineOpen_top T'.left).self_le_iSup_basicOpen_iff.1 fun p _ => by
      obtain ⟨f, hf, hp⟩ := key p
      exact Opens.mem_iSup.2 ⟨⟨f, hf⟩, hp⟩
  rw [Ideal.span_eq, Ideal.eq_top_iff_one] at hI
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hI
  rw [LinearMap.toSpanSingleton_apply, one_smul] at hr
  exact ⟨r, fun j => (congrArg (fun q => q.1 j) hr).symm⟩

end GlobalTheory.EmbPull

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Out VVRank EmbPull in

theorem emb_baseChange : Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (T T' : Over S) (h : T' ⟶ T) σ, IsAffine T.left → IsAffine T'.left → t.Emb m T σ → ∃ σ', t.Emb m T' σ' ∧ ∀ (R : Type) [CommRing R] (y : Sp R ⟶ (T' ⊗ t.A).left) (w : Ix g (N' ^ 2) → R), SecCoord _ σ' y w ↔ SecCoord _ σ (y ≫ (h ▷ t.A).left) w := by
  intro hl o _ g N' J b S s t m T T' h σ _ _ ⟨th, s₁, α, U, hth, hα, hs₁, hU, hσ⟩
  have hL := t.isLB
  obtain ⟨α', hα', k₁⟩ := exists_twist_pull t.A (ψ := mulT t.A T m) (hm := lift_snd _ _) (b := 1)
    hL hα h (ψ' := mulT t.A T' m) (lift_snd _ _) (mulT_comm t.A h m)
  choose U' hU' k₃ using fun a => ThetaCoord.exists_symLift_act_pull hL h (hU a)
  refine ⟨fun a => pullS t.A _ h (σ a), ⟨_, _, α', U', isGenSec_pullS t.pol hl.secBaseChangeAny h hth, hα',
    k₁ _ _ hs₁, fun a => ?_, fun a => k₃ a _ _ (hσ a)⟩, fun R _ y w => secCoord_pullTo σ _ _ y w⟩
  have e : h ≫ (Over.homMk T.hom (by simp) : T ⟶ baseOver S) = Over.homMk T'.hom (by simp) :=
    Over.OverMorphism.ext (Over.w h)
  have := hU' a
  rwa [MonObj.comp_pow, ← Category.assoc, e] at this

end GlobalTheory
end
