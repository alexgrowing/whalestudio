import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res
  pullback_map_app_pullbackSections)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)

namespace GlobalTheory.FlagLocal

variable {X Y S : Scheme.{0}} {A A' A'' E E' : X.Modules}

def Same (u : A ⟶ E) (v : A' ⟶ E) : Prop := ∃ e : A ≅ A', e.hom ≫ v = u

theorem Same.refl (u : A ⟶ E) : Same u u := ⟨Iso.refl _, Category.id_comp _⟩

theorem Same.symm {u : A ⟶ E} {v : A' ⟶ E} (h : Same u v) : Same v u :=
  have ⟨e, he⟩ := h
  ⟨e.symm, by rw [← he]; simp⟩

theorem Same.trans {u : A ⟶ E} {v : A' ⟶ E} {w : A'' ⟶ E} (h : Same u v) (h' : Same v w) : Same u w :=
  have ⟨e, he⟩ := h
  have ⟨e', he'⟩ := h'
  ⟨e ≪≫ e', by rw [← he, ← he']; simp⟩

theorem Same.comp {u : A ⟶ E} {v : A' ⟶ E} (h : Same u v) (φ : E ⟶ E') : Same (u ≫ φ) (v ≫ φ) :=
  have ⟨e, he⟩ := h
  ⟨e, by rw [← he, Category.assoc]⟩

theorem same_comp_iff {u : A ⟶ E} {v : A' ⟶ E} (φ : E ⟶ E') [Mono φ] : Same (u ≫ φ) (v ≫ φ) ↔ Same u v :=
  ⟨fun ⟨e, he⟩ => ⟨e, by rw [← cancel_mono φ, Category.assoc, he]⟩, fun h => h.comp φ⟩

theorem Same.pull {u : A ⟶ E} {v : A' ⟶ E} (h : Same u v) (f : Y ⟶ X) :
    Same ((Scheme.Modules.pullback f).map u) ((Scheme.Modules.pullback f).map v) :=
  have ⟨e, he⟩ := h
  ⟨(Scheme.Modules.pullback f).mapIso e, by rw [← he]; simp⟩

theorem same_of_le_le {u : A ⟶ E} {v : A' ⟶ E} [Mono u] [Mono v] (f : A ⟶ A') (g : A' ⟶ A)
    (hf : f ≫ v = u) (hg : g ≫ u = v) : Same u v :=
  ⟨⟨f, g, by rw [← cancel_mono u, Category.assoc, hg, hf, Category.id_comp],
    by rw [← cancel_mono v, Category.assoc, hf, hg, Category.id_comp]⟩, hf⟩

theorem cokernel_app_eq_zero_iff (v : A ⟶ E) [Mono v] (V : X.Opens) (t : Γ(E, V)) :
    (cokernel.π v).app V t = 0 ↔ ∃ m, v.app V m = t :=
  QCoh.exact_app_of_exact_of_mono (ShortComplex.exact_cokernel v) V t

theorem exists_fac_of_sections (u : A ⟶ E) (v : A' ⟶ E) [Mono v]
    (h : ∀ (V : X.Opens) (s : Γ(A, V)), ∃ m, v.app V m = u.app V s) : ∃ f : A ⟶ A', f ≫ v = u := by
  have : u ≫ cokernel.π v = 0 := by
    refine Scheme.Modules.hom_ext _ _ fun V => ?_
    ext s
    exact (cokernel_app_eq_zero_iff v V _).2 (h V s)
  exact ⟨Abelian.monoLift v u this, Abelian.monoLift_comp _ _ _⟩

theorem same_of_range {u : A ⟶ E} {v : A' ⟶ E} [Mono u] [Mono v]
    (h : ∀ V : X.Opens, Set.range (u.app V) = Set.range (v.app V)) : Same u v := by
  obtain ⟨f, hf⟩ := exists_fac_of_sections u v fun V s => (h V).le ⟨s, rfl⟩
  obtain ⟨g, hg⟩ := exists_fac_of_sections v u fun V s => (h V).ge ⟨s, rfl⟩
  exact same_of_le_le f g hf hg

theorem bijective_pullbackSections (a : Y ⟶ X) [IsOpenImmersion a] (E : X.Modules) {V : X.Opens}
    (hV : V ≤ a.opensRange) {W : Y.Opens} (hW : W = a ⁻¹ᵁ V) :
    Function.Bijective (pullbackSections a E hW.le) := by
  subst hW
  have e := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction a)
    (Scheme.Modules.pullbackPushforwardAdjunction a) E
  have h1 : Function.Bijective (E.presheaf.map (homOfLE (a.image_preimage_le V)).op) :=
    QCoh.res_bijective_of_eq E _ (by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact inf_eq_right.2 hV)
  have h2 := ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictFunctorIsoPullback a).hom.app E).app (a ⁻¹ᵁ V))
  convert h2.comp h1 using 1
  funext s
  exact (resM_self _ _).trans congr(($e).app V s).symm

theorem mem_range_of_pullback (a : Y ⟶ X) [IsOpenImmersion a] (v : A ⟶ E) {V : X.Opens}
    (hV : V ≤ a.opensRange) {W : Y.Opens} (hW : W = a ⁻¹ᵁ V) (t : Γ(E, V))
    (h : ∃ m, ((Scheme.Modules.pullback a).map v).app W m = pullbackSections a E hW.le t) :
    ∃ m, v.app V m = t := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨m, rfl⟩ := (bijective_pullbackSections a A hV hW).2 m
  rw [pullback_map_app_pullbackSections] at hm
  exact ⟨m, (bijective_pullbackSections a E hV hW).1 hm⟩

theorem mono_pullback_of_isOpenImmersion (a : Y ⟶ X) [IsOpenImmersion a] (v : A ⟶ E) [Mono v] :
    Mono ((Scheme.Modules.pullback a).map v) := by
  refine QCoh.mono_of_locally_app_injective _ fun W _ hx => ⟨W, hx, le_rfl, fun s t h => ?_⟩
  have hW := (a.preimage_image_eq W).symm
  have hV := a.image_le_opensRange W
  obtain ⟨s, rfl⟩ := (bijective_pullbackSections a A hV hW).2 s
  obtain ⟨t, rfl⟩ := (bijective_pullbackSections a A hV hW).2 t
  rw [pullback_map_app_pullbackSections, pullback_map_app_pullbackSections] at h
  rw [QCoh.injective_app_of_mono v _ ((bijective_pullbackSections a E hV hW).1 h)]

section Cover

variable {J : Type*} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]

theorem exists_fac_of_cover (hc : ∀ x : X, ∃ i y, a i y = x) (u : A ⟶ E) (v : A' ⟶ E) [Mono v]
    (h : ∀ i, ∃ f, f ≫ (Scheme.Modules.pullback (a i)).map v = (Scheme.Modules.pullback (a i)).map u) :
    ∃ f : A ⟶ A', f ≫ v = u := by
  refine exists_fac_of_sections u v fun V s => (cokernel_app_eq_zero_iff v V _).1 ?_
  refine (Sub.ker (cokernel.π v)).mem_of_local (V := V) (s := u.app V s) fun x hx => ?_
  obtain ⟨i, y, rfl⟩ := hc x
  obtain ⟨f, hf⟩ := h i
  refine ⟨V ⊓ (a i).opensRange, inf_le_left, ⟨hx, y, rfl⟩, (cokernel_app_eq_zero_iff v _ _).2 ?_⟩
  refine mem_range_of_pullback (a i) v inf_le_right rfl _
    ⟨f.app _ (pullbackSections (a i) A le_rfl (resM A inf_le_left s)), ?_⟩
  rw [QCoh.app_app, hf, pullback_map_app_pullbackSections, app_resM]

theorem same_of_cover (hc : ∀ x : X, ∃ i y, a i y = x) {u : A ⟶ E} {v : A' ⟶ E} [Mono u] [Mono v]
    (h : ∀ i, Same ((Scheme.Modules.pullback (a i)).map u) ((Scheme.Modules.pullback (a i)).map v)) :
    Same u v := by
  obtain ⟨f, hf⟩ := exists_fac_of_cover a hc u v fun i => have ⟨e, he⟩ := h i; ⟨e.hom, he⟩
  obtain ⟨g, hg⟩ := exists_fac_of_cover a hc v u fun i => have ⟨e, he⟩ := (h i).symm; ⟨e.hom, he⟩
  exact same_of_le_le f g hf hg

theorem isVB_of_openImmersions (hc : ∀ x : X, ∃ i y, a i y = x) {r : ℕ}
    (h : ∀ i, IsVB ((Scheme.Modules.pullback (a i)).obj A) r) : IsVB A r := fun x => by
  obtain ⟨i, y, rfl⟩ := hc x
  obtain ⟨W, e, hy, he⟩ :=
    (h i).of_iso ((Scheme.Modules.restrictFunctorIsoPullback (a i)).app A).symm y
  exact ⟨a i ''ᵁ W, e, ⟨y, hy, rfl⟩, (isFrame_restrict_iff (a i) e).1 he⟩

variable {G : ∀ i, (T i).Modules} (v : ∀ i, G i ⟶ (Scheme.Modules.pullback (a i)).obj E)

def glueSub : Sub E :=
  Sub.iInf fun i => Sub.ker ((Scheme.Modules.pullbackPushforwardAdjunction (a i)).unit.app E ≫
    (Scheme.Modules.pushforward (a i)).map (cokernel.π (v i)))

omit [∀ i, IsOpenImmersion (a i)] in
theorem mem_glueSub_iff [∀ i, Mono (v i)] {V : X.Opens} {s : Γ(E, V)} :
    s ∈ (glueSub a v).sec V ↔ ∀ i, ∃ m, (v i).app _ m = pullbackSections (a i) E le_rfl s := by
  refine (Submodule.mem_iInf _).trans (forall_congr' fun i => ?_)
  rw [← cokernel_app_eq_zero_iff]
  have : pullbackSections (a i) E le_rfl s =
      ((Scheme.Modules.pullbackPushforwardAdjunction (a i)).unit.app E).app V s := resM_self _ _
  rw [this]
  exact Iff.rfl

def Compat : Prop := ∀ i j (S : Scheme.{0}) (b : S ⟶ T i) (c : S ⟶ T j) (w : b ≫ a i = c ≫ a j),
  Same ((Scheme.Modules.pullback b).map (v i) ≫ (Scheme.Modules.pullbackComp b (a i)).hom.app E ≫
      (Scheme.Modules.pullbackCongr w).hom.app E)
    ((Scheme.Modules.pullback c).map (v j) ≫ (Scheme.Modules.pullbackComp c (a j)).hom.app E)

theorem mem_glueSub_of_le [∀ i, Mono (v i)] (hv : Compat a v) (i : J) {V : X.Opens}
    (hV : V ≤ (a i).opensRange) {s : Γ(E, V)} {W : (T i).Opens} (hW : W = a i ⁻¹ᵁ V)
    (hs : ∃ m, (v i).app W m = pullbackSections (a i) E hW.le s) : s ∈ (glueSub a v).sec V := by
  subst hW
  obtain ⟨m, hm⟩ := hs
  refine (mem_glueSub_iff a v).2 fun j => ?_
  let b := pullback.fst (a i) (a j)
  let c := pullback.snd (a i) (a j)
  have w : b ≫ a i = c ≫ a j := pullback.condition
  obtain ⟨e, he⟩ := hv i j _ b c w
  have hr : a j ⁻¹ᵁ V ≤ c.opensRange := by
    intro y hy
    obtain ⟨z, hz⟩ := hV hy
    obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback z y hz
    exact ⟨p, hp⟩
  have hle : c ⁻¹ᵁ a j ⁻¹ᵁ V ≤ b ⁻¹ᵁ a i ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]
  have key : e.hom ≫ (Scheme.Modules.pullback c).map (v j) = (Scheme.Modules.pullback b).map (v i) ≫
      (Scheme.Modules.pullbackComp b (a i) ≪≫ Scheme.Modules.pullbackCongr w ≪≫
        (Scheme.Modules.pullbackComp c (a j)).symm).hom.app E := by
    rw [← cancel_mono ((Scheme.Modules.pullbackComp c (a j)).hom.app E), Category.assoc, he]
    simp
  refine mem_range_of_pullback c (v j) hr rfl _ ⟨e.hom.app _ (pullbackSections b _ hle m), ?_⟩
  rw [← Vert.DivPull.pullbackSquare_app w E le_rfl hle le_rfl le_rfl, ← hm,
    ← pullback_map_app_pullbackSections, QCoh.app_app, key]
  first | exact (QCoh.app_app _ _ _ _).symm | rfl

theorem same_glueSub [∀ i, Mono (v i)] (hv : Compat a v) (i : J) :
    Same ((Scheme.Modules.pullback (a i)).map (glueSub a v).incl) (v i) := by
  have := mono_pullback_of_isOpenImmersion (a i) (glueSub a v).incl
  refine same_of_range fun W => ?_
  have hW := ((a i).preimage_image_eq W).symm
  have hV := (a i).image_le_opensRange W
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨s, rfl⟩ := (bijective_pullbackSections (a i) _ hV hW).2 s
    obtain ⟨m, hm⟩ := (mem_glueSub_iff a v).1 ((glueSub a v).incl_app_mem s) i
    refine ⟨resM _ hW.le m, ?_⟩
    rw [app_resM, hm, pullback_map_app_pullbackSections]
    exact res_pullbackSections _ _ _ _ _
  · rintro ⟨m, rfl⟩
    obtain ⟨s, hs⟩ := (bijective_pullbackSections (a i) _ hV hW).2 ((v i).app W m)
    refine ⟨pullbackSections (a i) _ hW.le ((glueSub a v).mkSec s
      (mem_glueSub_of_le a v hv i hV hW ⟨m, hs.symm⟩)), ?_⟩
    rw [pullback_map_app_pullbackSections, Sub.incl_app_mkSec, hs]

theorem exists_flag_of_cover (hc : ∀ x : X, ∃ i y, a i y = x) {n : ℕ}
    (fl : ∀ i, Vert.Flag ((Scheme.Modules.pullback (a i)).obj E) n)
    (h : ∀ k, Compat a fun i => (fl i).ι k) :
    ∃ fl₀ : Vert.Flag E n, ∀ i k, Same ((Scheme.Modules.pullback (a i)).map (fl₀.ι k)) ((fl i).ι k) := by
  let N : Fin (n + 1) → Sub E := fun k => glueSub a fun i => (fl i).ι k
  have hN := fun k i => same_glueSub a (fun i => (fl i).ι k) (h k) i
  have hstep : ∀ (k : Fin n) V s, (N k.castSucc).incl.app V s ∈ (N k.succ).sec V := fun k V s =>
    (mem_glueSub_iff a _).2 fun i => by
      obtain ⟨m, hm⟩ := (mem_glueSub_iff a _).1 ((N k.castSucc).incl_app_mem s) i
      exact ⟨((fl i).step k).app _ m, by rw [QCoh.app_app, (fl i).step_ι, hm]⟩
  refine ⟨{ F := fun k => (N k).toMod
            ι := fun k => (N k).incl
            isSubbundle := fun k => ⟨inferInstance, n - k, isVB_of_openImmersions a hc fun i => ?_⟩
            isVB := fun k => isVB_of_openImmersions a hc fun i => ?_
            step := fun k => (N k.succ).lift _ (hstep k)
            step_ι := fun k => (N k.succ).lift_incl _ (hstep k)
            isIso_last := ?_ }, fun i k => hN k i⟩
  · obtain ⟨e, he⟩ := hN k i
    exact ((fl i).isVB_cokernel k).of_iso ((cokernelEpiComp e.hom _).symm ≪≫ cokernelIsoOfEq he ≪≫
      (PreservesCokernel.iso (Scheme.Modules.pullback (a i)) (N k).incl).symm)
  · obtain ⟨e, -⟩ := hN k i
    exact ((fl i).isVB k).of_iso e.symm
  · refine Twist.isIso_of_bijective _ fun V => ⟨(N _).incl_app_injective V, fun s => ?_⟩
    exact (N _).mem_sec_iff.1 ((mem_glueSub_iff a _).2 fun i =>
      (ConcreteCategory.bijective_of_isIso (((fl i).ι (Fin.last n)).app _)).2 _)

end Cover

end GlobalTheory.FlagLocal
