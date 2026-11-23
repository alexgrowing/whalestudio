import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoPullbackOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
import Development.AutomorphicArithmetic.DivisorFrames.FrameExtendsFromPullback
import Development.AutomorphicArithmetic.DivisorFrames.QuotientFrameFromPermutation
import Development.AutomorphicArithmetic.DivisorFrames.ExistsSubbundleCokernelFrame
import Development.AutomorphicArithmetic.DivisorFrames.CokernelFrameCompatMono

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite GlobalTheory GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res pullback_map_app_pullbackSections)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.FlagLocal GlobalTheory.LineQuot

namespace UpperTheory.Grass

section Basic

variable {X Y : Scheme.{0}} {A A' F : X.Modules}

def img (u : A ⟶ F) : Sub F := Sub.ker (cokernel.π u)

theorem same_img (u : A ⟶ F) [Mono u] : Same (img u).incl u := same_of_range fun V => by
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    exact (cokernel_app_eq_zero_iff u V _).1 ((img u).incl_app_mem s)
  · rintro ⟨s, rfl⟩
    exact (img u).mem_sec_iff.1 ((cokernel_app_eq_zero_iff u V _).2 ⟨s, rfl⟩)

theorem sub_ext {N N' : Sub F} (h : Same N.incl N'.incl) : N = N' := by
  have key {N N' : Sub F} (h : Same N.incl N'.incl) (V : X.Opens) : N.sec V ≤ N'.sec V := by
    obtain ⟨e, he⟩ := h
    intro s hs
    exact (N'.exists_comp_incl_iff N.incl).1 ⟨e.hom, he⟩ V (N.mkSec s hs)
  obtain ⟨s, _, _⟩ := N
  obtain ⟨s', _, _⟩ := N'
  obtain rfl : s = s' := funext fun V => le_antisymm (key h V) (key h.symm V)
  rfl

theorem exists_cokerIso {u : A ⟶ F} {v : A' ⟶ F} (h : Same u v) :
    ∃ ψ : cokernel u ≅ cokernel v, cokernel.π u ≫ ψ.hom = cokernel.π v := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨cokernelEpiComp e.hom v, by simp⟩

theorem isVB_of_same {u : A ⟶ F} {v : A' ⟶ F} (h : Same u v) {m r : ℕ} (h₁ : IsVB A' m) (h₂ : IsVB (cokernel v) r) :
    IsVB A m ∧ IsVB (cokernel u) r :=
  have ⟨e, _⟩ := h
  have ⟨ψ, _⟩ := exists_cokerIso h
  ⟨h₁.of_iso e.symm, h₂.of_iso ψ.symm⟩

theorem mono_of_same {u : A ⟶ F} {v : A' ⟶ F} (h : Same u v) [Mono v] : Mono u := by
  obtain ⟨e, rfl⟩ := h
  infer_instance

end Basic

variable {B : Scheme.{0}} {E : B.Modules} {m r : ℕ} {Z Z' Z'' : Scheme.{0}}

theorem cmp_id (g : Z ⟶ B) (w : 𝟙 Z ≫ g = g) :
    (cmp (𝟙 Z) g w).hom.app E = (Scheme.Modules.pullbackId Z).hom.app ((Scheme.Modules.pullback g).obj E) := by
  rw [cmp_hom_app]
  have := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality g) E
  simp [Scheme.Modules.pullbackCongr] at this ⊢
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom] at this
  rw [this]
  exact (Category.comp_id _).symm

theorem cmp_app_sec (a : Z' ⟶ Z) (g : Z ⟶ B) {k : Z' ⟶ B} (w : a ≫ g = k) {U : B.Opens} {V : Z.Opens} {T : Z'.Opens}
    (h₁ : V ≤ g ⁻¹ᵁ U) (h₂ : T ≤ a ⁻¹ᵁ V) (h : T ≤ k ⁻¹ᵁ U) (s : Γ(E, U)) :
    ((cmp a g w).hom.app E).app T (pullbackSections a _ h₂ (pullbackSections g E h₁ s)) = pullbackSections k E h s := by
  subst w
  exact PullPull.pullbackComp_hom_app a g E h₁ h₂ h s

def tr (a : Z' ⟶ Z) {g : Z ⟶ B} {k : Z' ⟶ B} (w : a ≫ g = k) {A : Z.Modules} (u : A ⟶ (Scheme.Modules.pullback g).obj E) :
    (Scheme.Modules.pullback a).obj A ⟶ (Scheme.Modules.pullback k).obj E :=
  (Scheme.Modules.pullback a).map u ≫ (cmp a g w).hom.app E

theorem exists_cokerIso_tr (a : Z' ⟶ Z) {g : Z ⟶ B} {k : Z' ⟶ B} (w : a ≫ g = k) {A : Z.Modules}
    (u : A ⟶ (Scheme.Modules.pullback g).obj E) :
    ∃ ψ : (Scheme.Modules.pullback a).obj (cokernel u) ≅ cokernel (tr a w u),
      (Scheme.Modules.pullback a).map (cokernel.π u) ≫ ψ.hom = (cmp a g w).hom.app E ≫ cokernel.π (tr a w u) := by
  refine ⟨PreservesCokernel.iso (Scheme.Modules.pullback a) u ≪≫
    (cokernelCompIsIso ((Scheme.Modules.pullback a).map u) ((cmp a g w).hom.app E)).symm, ?_⟩
  have : (Scheme.Modules.pullback a).map (cokernel.π u) ≫ (PreservesCokernel.iso (Scheme.Modules.pullback a) u).hom =
      cokernel.π _ := by
    rw [← Iso.eq_comp_inv, PreservesCokernel.iso_inv, π_comp_cokernelComparison]
  rw [Iso.trans_hom, reassoc_of% this]
  simp [tr]

theorem tr_good (a : Z' ⟶ Z) {g : Z ⟶ B} {k : Z' ⟶ B} (w : a ≫ g = k) {A : Z.Modules}
    (u : A ⟶ (Scheme.Modules.pullback g).obj E) [Mono u] (h₁ : IsVB A m) (h₂ : IsVB (cokernel u) r) :
    Mono (tr a w u) ∧ IsVB (cokernel (tr a w u)) r := by
  have := (SubPull.isSubbundle_pullback _ _ a _ _ u m h₁ ⟨inferInstance, r, h₂⟩).mono
  obtain ⟨ψ, -⟩ := exists_cokerIso_tr a w u
  exact ⟨by unfold tr; infer_instance, (h₂.pullback a).of_iso ψ⟩

theorem Same.tr (a : Z' ⟶ Z) {g : Z ⟶ B} {k : Z' ⟶ B} (w : a ≫ g = k) {A A' : Z.Modules}
    {u : A ⟶ (Scheme.Modules.pullback g).obj E} {v : A' ⟶ (Scheme.Modules.pullback g).obj E} (h : Same u v) :
    Same (tr a w u) (tr a w v) := (h.pull a).comp _

theorem same_tr_id {g : Z ⟶ B} (w : 𝟙 Z ≫ g = g) {A : Z.Modules} (u : A ⟶ (Scheme.Modules.pullback g).obj E) :
    Same (tr (𝟙 Z) w u) u :=
  ⟨(Scheme.Modules.pullbackId Z).app A, by
    rw [tr, cmp_id]; exact ((Scheme.Modules.pullbackId Z).hom.naturality u).symm⟩

theorem same_tr_tr (b : Z'' ⟶ Z') (a : Z' ⟶ Z) {g : Z ⟶ B} {k : Z' ⟶ B} (w : a ≫ g = k) {l : Z'' ⟶ B} (w₂ : b ≫ k = l)
    {c : Z'' ⟶ Z} (w₁ : b ≫ a = c) (w₃ : c ≫ g = l) {A : Z.Modules} (u : A ⟶ (Scheme.Modules.pullback g).obj E) :
    Same (tr b w₂ (tr a w u)) (tr c w₃ u) :=
  ⟨(cmp b a w₁).app A, by
    simp only [tr, Iso.app_hom, Functor.map_comp, Category.assoc]
    rw [cmp_assoc b a g w w₂ w₁ w₃, cmp_naturality_assoc]⟩

variable (E m r) in

structure Pt (Z : Scheme.{0}) : Type where

  g : Z ⟶ B

  N : Sub ((Scheme.Modules.pullback g).obj E)
  vbN : IsVB N.toMod m
  vb : IsVB (cokernel N.incl) r

def Pt.ofMono (g : Z ⟶ B) {A : Z.Modules} (u : A ⟶ (Scheme.Modules.pullback g).obj E) [Mono u] (h₁ : IsVB A m)
    (h₂ : IsVB (cokernel u) r) : Pt E m r Z :=
  ⟨g, img u, (isVB_of_same (same_img u) h₁ h₂).1, (isVB_of_same (same_img u) h₁ h₂).2⟩

def R (a : Z' ⟶ Z) (x : Pt E m r Z) (y : Pt E m r Z') : Prop :=
  ∃ w : a ≫ x.g = y.g, Same (tr a w x.N.incl) y.N.incl

def Pt.map (a : Z' ⟶ Z) (x : Pt E m r Z) : Pt E m r Z' :=
  haveI := (tr_good a rfl x.N.incl x.vbN x.vb).1
  Pt.ofMono (a ≫ x.g) (tr a rfl x.N.incl) (x.vbN.pullback a) (tr_good a rfl x.N.incl x.vbN x.vb).2

theorem R_map (a : Z' ⟶ Z) (x : Pt E m r Z) : R a x (x.map a) :=
  haveI := (tr_good a rfl x.N.incl x.vbN x.vb).1
  ⟨rfl, (same_img _).symm⟩

theorem R.unique {a : Z' ⟶ Z} {x : Pt E m r Z} {y y' : Pt E m r Z'} (h : R a x y) (h' : R a x y') : y = y' := by
  obtain ⟨g, N, _, _⟩ := y
  obtain ⟨g', N', _, _⟩ := y'
  obtain ⟨w, h⟩ := h
  obtain ⟨w', h'⟩ := h'
  obtain rfl : g = g' := w.symm.trans w'
  obtain rfl : N = N' := sub_ext (h.symm.trans h')
  rfl

theorem map_eq_iff {a : Z' ⟶ Z} {x : Pt E m r Z} {y : Pt E m r Z'} : x.map a = y ↔ R a x y :=
  ⟨fun h => h ▸ R_map a x, (R_map a x).unique⟩

theorem R_id (x : Pt E m r Z) : R (𝟙 Z) x x := ⟨Category.id_comp _, same_tr_id _ _⟩

theorem R.comp {a : Z' ⟶ Z} {b : Z'' ⟶ Z'} {x : Pt E m r Z} {y : Pt E m r Z'} {z : Pt E m r Z''} (h : R a x y)
    (h' : R b y z) : R (b ≫ a) x z := by
  obtain ⟨w, h⟩ := h
  obtain ⟨w', h'⟩ := h'
  have w₃ : (b ≫ a) ≫ x.g = z.g := by rw [Category.assoc, w, w']
  exact ⟨w₃, ((same_tr_tr b a w w' rfl w₃ _).symm.trans (Same.tr b w' h)).trans h'⟩

variable (E m r) in

def fct : Scheme.{0}ᵒᵖ ⥤ Type where
  obj Z := Pt E m r Z.unop
  map a := TypeCat.ofHom (Pt.map a.unop)
  map_id Z := by
    ext x
    exact map_eq_iff.2 (R_id x)
  map_comp a b := by
    ext x
    exact map_eq_iff.2 ((R_map _ x).comp (R_map _ _))

theorem fct_map (a : Z' ⟶ Z) (x : Pt E m r Z) : (fct E m r).map a.op x = x.map a := rfl

theorem tr_rfl (a : Z' ⟶ Z) {g : Z ⟶ B} {A : Z.Modules} (u : A ⟶ (Scheme.Modules.pullback g).obj E) :
    tr a rfl u = (Scheme.Modules.pullback a).map u ≫ (Scheme.Modules.pullbackComp a g).hom.app E :=
  congrArg (_ ≫ ·) (Category.comp_id _)

theorem tr_inv_comp (a : Z' ⟶ Z) {g : Z ⟶ B} {k : Z' ⟶ B} (w : a ≫ g = k) {A : Z'.Modules}
    (u : A ⟶ (Scheme.Modules.pullback k).obj E) (p : Z'' ⟶ Z') {c : Z'' ⟶ Z} (w₁ : p ≫ a = c) {l : Z'' ⟶ B}
    (w₃ : c ≫ g = l) (w₂ : p ≫ k = l) :
    tr p w₁ (u ≫ (cmp a g w).inv.app E) ≫ (cmp c g w₃).hom.app E = tr p w₂ u := by
  simp only [tr, Functor.map_comp, Category.assoc]
  rw [← cmp_assoc p a g w w₂ w₁ w₃, ← Functor.map_comp_assoc _ ((cmp a g w).inv.app E), Iso.inv_hom_id_app]
  simp

theorem isSheaf_fct : Presieve.IsSheaf Scheme.zariskiTopology (fct E m r) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y S hS
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hS
  rw [Presieve.isSheafFor_arrows_iff]
  intro (x : ∀ j, Pt E m r (𝒰.X j)) hx
  replace hx : ∀ i j (Z : Scheme.{0}) (a : Z ⟶ 𝒰.X i) (a' : Z ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = a' ≫ 𝒰.f j → Pt.map a (x i) = Pt.map a' (x j) := hx
  let b : Y ⟶ B := 𝒰.glueMorphisms (fun j => (x j).g) fun i j =>
    congrArg Pt.g (hx i j _ _ _ pullback.condition)
  have hb : ∀ j, 𝒰.f j ≫ b = (x j).g := fun j => 𝒰.ι_glueMorphisms _ _ j
  clear_value b
  have hc : ∀ y : Y, ∃ i z, 𝒰.f i z = y := fun y => 𝒰.exists_eq y
  let v (j) : (x j).N.toMod ⟶ (Scheme.Modules.pullback (𝒰.f j)).obj ((Scheme.Modules.pullback b).obj E) :=
    (x j).N.incl ≫ (cmp (𝒰.f j) b (hb j)).inv.app E
  have hmono (j) : Mono (v j) := inferInstanceAs (Mono (_ ≫ _))
  have hv : Compat 𝒰.f v := by
    intro i j S p q w
    obtain ⟨w₂, h₂⟩ := map_eq_iff.1 (hx i j S p q w)
    obtain ⟨w₂', h₂'⟩ := R_map q (x j)
    have w₃ : (q ≫ 𝒰.f j) ≫ b = (Pt.map q (x j)).g := by rw [Category.assoc, hb, w₂']
    rw [← same_comp_iff ((cmp (q ≫ 𝒰.f j) b w₃).hom.app E)]
    have e₁ := tr_inv_comp (𝒰.f i) (hb i) (x i).N.incl p w w₃ w₂
    have e₂ := tr_inv_comp (𝒰.f j) (hb j) (x j).N.incl q rfl w₃ w₂'
    rw [← e₁] at h₂
    rw [← e₂, tr_rfl] at h₂'
    exact h₂.trans h₂'.symm
  have hs (j) : Same (tr (𝒰.f j) (hb j) (glueSub 𝒰.f v).incl) (x j).N.incl := by
    simpa [v, tr] using (same_glueSub 𝒰.f v hv j).comp ((cmp (𝒰.f j) b (hb j)).hom.app E)
  let y : Pt E m r Y := ⟨b, glueSub 𝒰.f v,
    isVB_of_openImmersions 𝒰.f hc fun j => (isVB_of_same (hs j) (x j).vbN (x j).vb).1,
    isVB_of_openImmersions 𝒰.f hc fun j =>
      have ⟨ψ, _⟩ := exists_cokerIso_tr (𝒰.f j) (hb j) (glueSub 𝒰.f v).incl
      (isVB_of_same (hs j) (x j).vbN (x j).vb).2.of_iso ψ.symm⟩
  refine ⟨y, fun j => map_eq_iff.2 ⟨hb j, hs j⟩, fun (y' : Pt E m r Y) hy' => ?_⟩
  replace hy' : ∀ j, R (𝒰.f j) y' (x j) := fun j => map_eq_iff.1 (hy' j)
  obtain ⟨b', N', _, _⟩ := y'
  obtain rfl : b' = b := 𝒰.hom_ext _ _ fun j => (hy' j).1.trans (hb j).symm
  obtain rfl : N' = glueSub 𝒰.f v := sub_ext (same_of_cover 𝒰.f hc fun j =>
    (same_comp_iff ((cmp (𝒰.f j) b' (hb j)).hom.app E)).1 ((hy' j).2.trans (hs j).symm))
  rfl

def qs (y : Pt E m r Z) {U : B.Opens} (s : Γ(E, U)) {V : Z.Opens} (h : V ≤ y.g ⁻¹ᵁ U) : Γ(cokernel y.N.incl, V) :=
  (cokernel.π y.N.incl).app V (pullbackSections y.g E h s)

theorem resM_qs (y : Pt E m r Z) {U : B.Opens} (s : Γ(E, U)) {V V' : Z.Opens} (h : V ≤ y.g ⁻¹ᵁ U) (h' : V' ≤ V) :
    resM _ h' (qs y s h) = qs y s (h'.trans h) := by
  rw [qs, ← app_resM]
  exact congrArg _ (res_pullbackSections _ _ _ _ _)

theorem R.exists_iso {a : Z' ⟶ Z} {x : Pt E m r Z} {y : Pt E m r Z'} (H : R a x y) :
    ∃ ψ : (Scheme.Modules.pullback a).obj (cokernel x.N.incl) ≅ cokernel y.N.incl,
      ∀ (U : B.Opens) (s : Γ(E, U)) (V : Z.Opens) (h : V ≤ x.g ⁻¹ᵁ U) (V' : Z'.Opens) (h' : V' ≤ a ⁻¹ᵁ V)
        (h'' : V' ≤ y.g ⁻¹ᵁ U), ψ.hom.app V' (pullbackSections a _ h' (qs x s h)) = qs y s h'' := by
  obtain ⟨w, H⟩ := H
  obtain ⟨ψ, hψ⟩ := exists_cokerIso_tr a w x.N.incl
  obtain ⟨χ, hχ⟩ := exists_cokerIso H
  refine ⟨ψ ≪≫ χ, fun U s V h V' h' h'' => ?_⟩
  rw [qs, qs, ← pullback_map_app_pullbackSections, QCoh.app_app, Iso.trans_hom, reassoc_of% hψ, hχ,
    ← cmp_app_sec a x.g w h h' h'', QCoh.app_app]
  rfl

variable (E m r) in

structure Chart : Type where

  U : B.Opens

  e : Fin m ⊕ Fin r → Γ(E, U)
  he : IsFrame e

variable (c : Chart E m r)

def FrAt (y : Pt E m r Z) (z : Z) : Prop :=
  ∃ (V : Z.Opens) (h : V ≤ y.g ⁻¹ᵁ c.U), z ∈ V ∧ IsFrame fun k => qs y (c.e (.inr k)) h

def locus (y : Pt E m r Z) : Z.Opens :=
  ⟨{z | FrAt c y z}, isOpen_iff_forall_mem_open.2 fun _ ⟨V, h, hz, hf⟩ => ⟨V, fun _ hz' => ⟨V, h, hz', hf⟩, V.2, hz⟩⟩

theorem R.frAt_iff {a : Z' ⟶ Z} {x : Pt E m r Z} {y : Pt E m r Z'} (H : R a x y) (z : Z') :
    FrAt c y z ↔ FrAt c x (a z) := by
  obtain ⟨ψ, hψ⟩ := H.exists_iso
  have w : y.g ⁻¹ᵁ c.U = a ⁻¹ᵁ x.g ⁻¹ᵁ c.U := by rw [← H.1, Scheme.Hom.comp_preimage]
  have := x.vb.isQuasicoherent
  constructor
  · rintro ⟨V, h, hz, hf⟩
    obtain ⟨W, hW, hzW, hf'⟩ := UpperTheory.frame_extends_from_pullback Z Z' a _ r _ (fun k => qs x (c.e (.inr k)) le_rfl) V (h.trans w.le) z
      x.vb hz (by
        convert hf.map_iso ψ.inv using 2 with k
        rw [← hψ _ _ _ le_rfl _ (h.trans w.le), QCoh.app_app, Iso.hom_inv_id]
        rfl)
    exact ⟨W, hW, hzW, by simpa only [resM_qs] using hf'⟩
  · rintro ⟨V, h, hz, hf⟩
    refine ⟨a ⁻¹ᵁ V, (a.preimage_mono h).trans w.ge, hz, ?_⟩
    convert (hf.pullback a).map_iso ψ.hom using 2 with k
    rw [hψ]

def Gr (y : Pt E m r Z) (h : ⊤ ≤ y.g ⁻¹ᵁ c.U) (α : Fin m → Fin r → Γ(Z, ⊤)) : Prop :=
  IsFrame (fun k => qs y (c.e (.inr k)) h) ∧ ∀ i, qs y (c.e (.inl i)) h = ∑ k, α i k • qs y (c.e (.inr k)) h

theorem forall_frAt_iff (y : Pt E m r Z) : (∀ z, FrAt c y z) ↔ ∃ h α, Gr c y h α := by
  refine ⟨fun H => ?_, fun ⟨h, _, hf, _⟩ z => ⟨⊤, h, trivial, hf⟩⟩
  have h : ⊤ ≤ y.g ⁻¹ᵁ c.U := fun z _ => have ⟨_, h, hz, _⟩ := H z; h hz
  have hf : IsFrame fun k => qs y (c.e (.inr k)) h := isFrame_of_forall_exists fun V _ z hz => by
    obtain ⟨V', h', hz', hf⟩ := H z
    refine ⟨V ⊓ V', inf_le_left, ⟨hz, hz'⟩, ?_⟩
    simpa only [resM_qs] using hf (V ⊓ V') inf_le_right
  refine ⟨h, fun i k => (hf.basis le_rfl).repr (qs y (c.e (.inl i)) h) k, hf, fun i => ?_⟩
  simpa only [IsFrame.basis_apply, resM_self] using ((hf.basis le_rfl).sum_repr (qs y (c.e (.inl i)) h)).symm

theorem Gr.matrix_eq {y : Pt E m r Z} {h h' : ⊤ ≤ y.g ⁻¹ᵁ c.U} {α β : Fin m → Fin r → Γ(Z, ⊤)} (H : Gr c y h α)
    (H' : Gr c y h' β) : α = β := by
  funext i
  apply (H.1 ⊤ le_rfl).1
  simpa only [Fintype.linearCombination_apply, resM_self] using (H.2 i).symm.trans (H'.2 i)

theorem R.gr {a : Z' ⟶ Z} {x : Pt E m r Z} {y : Pt E m r Z'} (H : R a x y) {h : ⊤ ≤ x.g ⁻¹ᵁ c.U}
    {α : Fin m → Fin r → Γ(Z, ⊤)} (G : Gr c x h α) : ∃ h', Gr c y h' fun i k => a.appTop (α i k) := by
  obtain ⟨ψ, hψ⟩ := H.exists_iso
  have w : y.g ⁻¹ᵁ c.U = a ⁻¹ᵁ x.g ⁻¹ᵁ c.U := by rw [← H.1, Scheme.Hom.comp_preimage]
  have := x.vb.isQuasicoherent
  have h' : ⊤ ≤ y.g ⁻¹ᵁ c.U := (a.preimage_mono h).trans w.ge
  refine ⟨h', ?_, fun i => ?_⟩
  · rw [← funext fun k => hψ _ (c.e (.inr k)) ⊤ h ⊤ le_rfl h']
    exact (G.1.pullback a).map_iso ψ.hom
  · have e : a.appLE ⊤ ⊤ le_rfl = a.appTop := (a.app_eq_appLE (U := ⊤)).symm
    rw [← hψ _ _ ⊤ h ⊤ le_rfl, G.2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [QCoh.pullbackSections_smul, Scheme.Modules.Hom.app_smul, hψ _ _ _ _ _ _ h', e]

theorem isFrame_pull [E.IsQuasicoherent] (g : Z ⟶ B) {V : Z.Opens} (h : V ≤ g ⁻¹ᵁ c.U) :
    IsFrame fun i => pullbackSections g E h (c.e i) := by
  convert (c.he.pullback g).res h using 2 with i
  exact (res_pullbackSections _ _ _ _ _).symm

theorem Gr.eq [E.IsQuasicoherent] {y y' : Pt E m r Z} (w : y.g = y'.g) {h : ⊤ ≤ y.g ⁻¹ᵁ c.U} {h' : ⊤ ≤ y'.g ⁻¹ᵁ c.U}
    {α : Fin m → Fin r → Γ(Z, ⊤)} (H : Gr c y h α) (H' : Gr c y' h' α) : y = y' := by
  obtain ⟨g, N, _, _⟩ := y
  obtain ⟨g', N', _, _⟩ := y'
  obtain rfl : g = g' := w
  obtain rfl : N = N' := sub_ext (UpperTheory.cokernel_frame_compat_mono Z _ _ _ N.incl N'.incl m r _ α inferInstance inferInstance
    (isFrame_pull c g h) H.1 H.2 H'.1 H'.2)
  rfl

theorem exists_gr (hE : IsVB E (m + r)) (g : Z ⟶ B) (h : ⊤ ≤ g ⁻¹ᵁ c.U) (α : Fin m → Fin r → Γ(Z, ⊤)) :
    ∃ (x : Pt E m r Z) (_ : x.g = g) (h' : ⊤ ≤ x.g ⁻¹ᵁ c.U), Gr c x h' α := by
  have := hE.isQuasicoherent
  obtain ⟨N, h₁, h₂⟩ := UpperTheory.exists_subbundle_cokernel_frame Z _ m r _ α (isFrame_pull c g h)
  have hQ : IsVB (cokernel N.incl) r := by simpa using h₁.isVB
  exact ⟨⟨g, N, isVB_X₁_of_shortExact Z (.mk N.incl (cokernel.π _) (cokernel.condition _)) m r
    { exact := ShortComplex.exact_cokernel _ } (hE.pullback g) hQ, hQ⟩, rfl, h, h₁, h₂⟩

theorem exists_frAt (hE : IsVB E (m + r)) (y : Pt E m r Z) (z : Z) : ∃ c : Chart E m r, FrAt c y z := by
  have := hE.isQuasicoherent
  obtain ⟨U, e, hz, he⟩ := hE (y.g z)
  let c : Chart E m r := ⟨U, _, he.comp_equiv finSumFinEquiv⟩
  obtain ⟨σ, W, hW, hzW, hf⟩ := UpperTheory.quotient_frame_from_permutation Z _ _ (cokernel.π y.N.incl) m r _ _ z inferInstance
    (isFrame_pull c y.g le_rfl) y.vb hz
  refine ⟨⟨U, _, c.he.comp_equiv σ⟩, W, hW, hzW, ?_⟩
  convert hf using 2 with k
  exact (resM_qs y _ le_rfl hW).symm

theorem isRepresentable (hE : IsVB E (m + r)) : (fct E m r).IsRepresentable := by
  have := hE.isQuasicoherent
  choose x hx h hG using fun c : Chart E m r =>
    exists_gr c hE (𝔸(Fin m × Fin r; c.U.toScheme) ↘ c.U.toScheme ≫ c.U.ι)
      (by rw [Scheme.Hom.comp_preimage]; simp) fun i k => AffineSpace.coord _ (i, k)
  refine GeneratorFunctor.isRepresentable_of_charts _ isSheaf_fct (fun c : Chart E m r => 𝔸(Fin m × Fin r; c.U.toScheme)) x
    (fun c _ y => locus c y) (fun c Z y Z' a => ?_) (fun c Z g g' e => ?_) fun Z y z => exists_frAt hE y z
  · change _ ↔ ∃ g, Pt.map g (x c) = Pt.map a y
    have h₁ : Set.range a ⊆ (locus c y : Set Z) ↔ ∀ z, FrAt c (Pt.map a y) z := by
      simp only [Set.range_subset_iff, (R_map a y).frAt_iff c]
      rfl
    rw [h₁, forall_frAt_iff]
    generalize Pt.map a y = y'
    constructor
    · rintro ⟨h', α, H⟩
      let l := IsOpenImmersion.lift c.U.ι y'.g (by
        rw [Scheme.Opens.range_ι]; rintro _ ⟨z, rfl⟩; exact h' trivial)
      have hl : l ≫ c.U.ι = y'.g := IsOpenImmersion.lift_fac _ _ _
      refine ⟨AffineSpace.homOfVector l fun p => α p.1 p.2, ?_⟩
      obtain ⟨h'', H'⟩ := (R_map (AffineSpace.homOfVector l fun p : Fin m × Fin r => α p.1 p.2) (x c)).gr c (hG c)
      simp only [AffineSpace.homOfVector_appTop_coord] at H'
      refine Gr.eq c ?_ H' H
      change _ ≫ (x c).g = _
      rw [hx, AffineSpace.homOfVector_over_assoc, hl]
    · rintro ⟨g, rfl⟩
      obtain ⟨h'', H'⟩ := (R_map g (x c)).gr c (hG c)
      exact ⟨h'', _, H'⟩
  · change Pt.map g (x c) = Pt.map g' (x c) at e
    obtain ⟨_, H⟩ := (map_eq_iff.1 e).gr c (hG c)
    obtain ⟨_, H'⟩ := (R_map g' (x c)).gr c (hG c)
    have w : g ≫ (x c).g = g' ≫ (x c).g := congrArg Pt.g e
    rw [hx] at w
    refine AffineSpace.hom_ext ?_ fun p => congrFun (congrFun (H.matrix_eq c H') p.1) p.2
    rw [← cancel_mono c.U.ι, Category.assoc, Category.assoc, w]

theorem exists_grass : ∀ (B : Scheme.{0}) (E : B.Modules) (m r : ℕ), GlobalTheory.VB.IsVB E (m + r) →
      ∃ (G : Scheme.{0}) (γ : G ⟶ B) (P : G.Modules) (j : P ⟶ (Scheme.Modules.pullback γ).obj E),
        GlobalTheory.VB.IsVB P m ∧ Mono j ∧ GlobalTheory.VB.IsVB (Limits.cokernel j) r ∧
        ∀ (T : Scheme.{0}) (g : T ⟶ B) (P' : T.Modules) (j' : P' ⟶ (Scheme.Modules.pullback g).obj E),
          Mono j' → GlobalTheory.VB.IsVB (Limits.cokernel j') r →
          ∃! g' : T ⟶ G, ∃ w : g' ≫ γ = g, ∃ φ : (Scheme.Modules.pullback g').obj P ≅ P',
            φ.hom ≫ j' = (Scheme.Modules.pullback g').map j ≫ (Scheme.Modules.pullbackComp g' γ).hom.app E ≫
              (Scheme.Modules.pullbackCongr w).hom.app E := by
  intro B E m r hE
  have := isRepresentable hE
  let ρ := (fct E m r).representableBy
  let x : Pt E m r _ := ρ.homEquiv (𝟙 _)
  refine ⟨_, x.g, _, x.N.incl, x.vbN, inferInstance, x.vb, fun T g P' j' _ hQ => ?_⟩
  have hP : IsVB P' m := isVB_X₁_of_shortExact T (.mk j' (cokernel.π _) (cokernel.condition _)) m r
    { exact := ShortComplex.exact_cokernel _ } (hE.pullback g) hQ
  have key (g' : T ⟶ _) : ρ.homEquiv g' = Pt.ofMono g j' hP hQ ↔ ∃ w : g' ≫ x.g = g, Same (tr g' w x.N.incl) j' := by
    rw [ρ.homEquiv_eq]
    exact map_eq_iff.trans (exists_congr fun w => ⟨fun h => h.trans (same_img j'), fun h => h.trans (same_img j').symm⟩)
  exact ⟨ρ.homEquiv.symm (Pt.ofMono g j' hP hQ), (key _).1 (ρ.homEquiv.apply_symm_apply _),
    fun g' hg' => ρ.homEquiv.eq_symm_apply.2 ((key g').2 hg')⟩

end UpperTheory.Grass
