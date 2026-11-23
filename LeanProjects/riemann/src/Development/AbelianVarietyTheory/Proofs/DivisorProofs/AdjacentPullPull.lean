import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagCh2FlagPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsArithVarEffCartier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubbundleKernelOfLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImagePrincipalOfEffCartier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointNotMemSupportCokernelOfNeZero

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Vert

namespace GlobalTheory.FlagChain

section Sub

variable {C C' : Type*} [Category C] [Category C'] {A B A' E E' : C}

def Le (f : A ⟶ E) (g : B ⟶ E) : Prop := ∃ u : A ⟶ B, u ≫ g = f

def Same (f : A ⟶ E) (g : B ⟶ E) : Prop := ∃ e : A ≅ B, e.hom ≫ g = f

variable {f : A ⟶ E} {g : B ⟶ E} {f' : A' ⟶ E}

theorem Le.trans (h : Le f g) (h' : Le g f') : Le f f' := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨v, rfl⟩ := h'
  exact ⟨u ≫ v, Category.assoc ..⟩

theorem Le.map (h : Le f g) (F : C ⥤ C') : Le (F.map f) (F.map g) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨F.map u, (F.map_comp ..).symm⟩

theorem Same.refl (f : A ⟶ E) : Same f f := ⟨Iso.refl _, Category.id_comp _⟩

theorem Same.symm (h : Same f g) : Same g f := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨e.symm, e.inv_hom_id_assoc _⟩

theorem Same.trans (h : Same f g) (h' : Same g f') : Same f f' := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨v, rfl⟩ := h'
  exact ⟨u ≪≫ v, Category.assoc ..⟩

theorem Same.le (h : Same f g) : Le f g := h.elim fun e he => ⟨e.hom, he⟩

theorem Same.map (h : Same f g) (F : C ⥤ C') : Same (F.map f) (F.map g) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨F.mapIso u, (F.map_comp ..).symm⟩

theorem Same.comp (h : Same f g) (t : E ⟶ E') : Same (f ≫ t) (g ≫ t) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨u, (Category.assoc ..).symm⟩

theorem same_natIso {F G : C ⥤ C'} (e : F ≅ G) (f : A ⟶ E) :
    Same (F.map f ≫ (e.app E).hom) (G.map f) :=
  ⟨e.app A, (e.hom.naturality f).symm⟩

end Sub

section Bundles

variable {X Y Z : Scheme.{0}} {A B E E' H : X.Modules} {r : ℕ}

theorem isSubbundle_comp {u : A ⟶ B} {g : B ⟶ E} (hu : IsSubbundle u) (hg : IsSubbundle g) :
    IsSubbundle (u ≫ g) := by
  have := hu.mono
  have := hg.mono
  obtain ⟨s, hs⟩ := hu.isVB_cokernel
  obtain ⟨t, ht⟩ := hg.isVB_cokernel
  exact ⟨inferInstance, _, (VBExt.isVB_and_cls_det_of_shortExact X _ _ _
    (Vert.shortExact_cokernel_comp u g) hs ht).1⟩

theorem isVB_cokernel [Nonempty X] {g : B ⟶ E} {b : ℕ} (hg : IsSubbundle g) (hB : IsVB B b)
    (hE : IsVB E r) : ∃ s, r = b + s ∧ IsVB (cokernel g) s := by
  obtain ⟨_, s, hs⟩ := hg
  exact ⟨s, hE.rank_unique (VBExt.isVB_and_cls_det_of_shortExact X (.mk g (cokernel.π _)
    (cokernel.condition _)) b s { exact := ShortComplex.exact_cokernel _ } hB hs).1, hs⟩

theorem isVB_cokernel_one [Nonempty X] {u : A ⟶ B} {g : B ⟶ E} {a : ℕ} (hu : IsSubbundle (u ≫ g))
    (hg : IsSubbundle g) (hA : IsVB A a) (hB : IsVB B (a + 1)) (hE : IsVB E r) :
    IsVB (cokernel u) 1 := by
  have := hg.mono
  obtain ⟨s, e, hs⟩ := isVB_cokernel hu hA hE
  obtain ⟨t, e', ht⟩ := isVB_cokernel hg hB hE
  obtain rfl : s = 1 + t := by omega
  exact VB.isVB_X₁_of_shortExact X _ 1 _ (Vert.shortExact_cokernel_comp u g) hs ht

abbrev Joined (fl fl' : Flag E r) : Prop := Relation.ReflTransGen Flag.Adjacent fl fl'

theorem Joined.pull {fl fl' : Flag E r} (h : Joined fl fl') (ρ : Y ⟶ X) :
    Joined (fl.pull ρ) (fl'.pull ρ) :=
  h.lift (fun a : Flag E r => a.pull ρ) fun _ _ ⟨j, hj⟩ =>
    ⟨j, fun i hi => Same.map (hj i hi) (Scheme.Modules.pullback ρ)⟩

theorem Joined.ofIso {fl fl' : Flag E r} (h : Joined fl fl') (e : E ≅ E') :
    Joined (fl.ofIso e) (fl'.ofIso e) :=
  h.lift (fun a : Flag E r => a.ofIso e) fun _ _ ⟨j, hj⟩ =>
    ⟨j, fun i hi => Same.comp (hj i hi) e.hom⟩

theorem adjacent_pull_pull (fl : Flag E r) (ρ : Y ⟶ X) (τ : Z ⟶ Y) :
    (((fl.pull ρ).pull τ).ofIso ((Scheme.Modules.pullbackComp τ ρ).app E)).Adjacent
      (fl.pull (τ ≫ ρ)) :=
  ⟨0, fun i _ => same_natIso (Scheme.Modules.pullbackComp τ ρ) (fl.ι i)⟩

theorem Joined.pull_comp {fl fl' : Flag E r} {ρ : Y ⟶ X} {τ : Z ⟶ Y}
    (h : Joined ((fl.pull ρ).pull τ) ((fl'.pull ρ).pull τ)) :
    Joined (fl.pull (τ ≫ ρ)) (fl'.pull (τ ≫ ρ)) :=
  ((h.ofIso _).tail (adjacent_pull_pull fl' ρ τ)).head (adjacent_pull_pull fl ρ τ).symm

theorem exists_update (fl : Flag E r) (j : Fin (r + 1)) {κ : H ⟶ E} (hs : IsSubbundle κ)
    (hv : IsVB H j) (hl : j ≠ Fin.last r)
    (h₁ : ∀ i : Fin r, i.succ = j → Le (fl.ι i.castSucc) κ)
    (h₂ : ∀ i : Fin r, i.castSucc = j → Le κ (fl.ι i.succ)) :
    ∃ fl' : Flag E r, Same (fl'.ι j) κ ∧ ∀ i, i ≠ j → Same (fl'.ι i) (fl.ι i) := by
  let G : Fin (r + 1) → Σ A : X.Modules, (A ⟶ E) :=
    Function.update (fun i => ⟨fl.F i, fl.ι i⟩) j ⟨H, κ⟩
  have e₁ : G j = ⟨H, κ⟩ := Function.update_self ..
  have e₂ (i) (hi : i ≠ j) : G i = ⟨fl.F i, fl.ι i⟩ := Function.update_of_ne hi ..
  have hsub (i) : IsSubbundle (G i).2 := by
    by_cases hi : i = j
    · rw [hi, e₁]; exact hs
    · rw [e₂ i hi]; exact fl.isSubbundle i
  have hvb (i) : IsVB (G i).1 i := by
    by_cases hi : i = j
    · rw [hi, e₁]; exact hv
    · rw [e₂ i hi]; exact fl.isVB i
  have hstep (i : Fin r) : Le (G i.castSucc).2 (G i.succ).2 := by
    by_cases hi : i.castSucc = j
    · rw [e₂ i.succ (hi ▸ i.castSucc_lt_succ.ne'), hi, e₁]; exact h₂ i hi
    by_cases hi' : i.succ = j
    · rw [e₂ _ hi, hi', e₁]; exact h₁ i hi'
    · rw [e₂ _ hi, e₂ _ hi']; exact ⟨fl.step i, fl.step_ι i⟩
  choose step step_ι using hstep
  have hiso : IsIso (G (Fin.last r)).2 := by
    rw [e₂ _ hl.symm]; exact fl.isIso_last
  refine ⟨⟨fun i => (G i).1, fun i => (G i).2, hsub, hvb, step, step_ι, hiso⟩, ?_, fun i hi => ?_⟩
  · change Same (G j).2 κ
    rw [e₁]; exact .refl _
  · change Same (G i).2 _
    rw [e₂ i hi]; exact .refl _

end Bundles

section Covers

variable {k : Type} [CommRing k] {D : ℕ} {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  [IsIntegral Z] {p : X ⟶ Sp k} {A E L H : X.Modules} {r : ℕ}

def IsCov (p : X ⟶ Sp k) (D : ℕ) (ρ : Y ⟶ X) : Prop :=
  IsArithVar (ρ ≫ p) D ∧ ρ (genericPoint Y) = genericPoint X ∧ ρ.residueDegree (genericPoint Y) ≠ 0

theorem IsCov.id (h : IsArithVar p D) : IsCov p D (𝟙 X) :=
  ⟨(Category.id_comp p).symm ▸ h, rfl, (Scheme.Hom.residueDegree_id _).trans_ne one_ne_zero⟩

theorem IsCov.comp {ρ : Y ⟶ X} {τ : Z ⟶ Y} (h : IsCov p D ρ) (h' : IsCov (ρ ≫ p) D τ) :
    IsCov p D (τ ≫ ρ) := by
  refine ⟨(Category.assoc τ ρ p).symm ▸ h'.1, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply, h'.2.1, h.2.1]
  · rw [CurveDegreesCompare.residueDegree_comp, h'.2.1]
    exact mul_ne_zero h.2.2 h'.2.2

theorem exists_cov_kernel (hX : IsArithVar p D) (φ : E ⟶ L) {n : ℕ} (hE : IsVB E (n + 1))
    (hL : IsVB L 1) (hφ : φ ≠ 0) : ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y), IsCov p D ρ ∧
      IsSubbundle (kernel.ι ((Scheme.Modules.pullback ρ).map φ)) ∧
      IsVB (kernel ((Scheme.Modules.pullback ρ).map φ)) n := by
  have := hE.isFiniteQC
  have := hL.isFiniteQC
  obtain ⟨Y, ρ, _, h₁, h₂, h₃, h₄⟩ := BlowArith.exists_isArithVar_effCartier k X p D hX (QCoh.annihilatorSheaf (cokernel φ))
    fun h => VB.genericPoint_notMem_support_cokernel_of_ne_zero X E L φ hL hφ ((QCoh.coe_support_annihilatorSheaf _).le h)
  exact ⟨Y, ρ, inferInstance, ⟨h₁, h₂, h₃⟩, VB.isSubbundle_kernel_of_locally_principal Y _ _ _ n (hE.pullback ρ) (hL.pullback ρ)
    (VB.exists_image_principal_of_effCartier X Y ρ E L φ _ hE hL h₄)⟩

theorem exists_common (hX : IsArithVar p D) (fl : Flag E r) {n : ℕ} (hn : n + 1 < r) {κ : H ⟶ E}
    (hs : IsSubbundle κ) (hv : IsVB H (n + 1)) (hle : Le κ (fl.ι ⟨n + 2, by omega⟩)) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y), IsCov p D ρ ∧
      ∃ (K : Y.Modules) (μ : K ⟶ (Scheme.Modules.pullback ρ).obj E), IsSubbundle μ ∧ IsVB K n ∧
        Le μ ((fl.pull ρ).ι ⟨n + 1, by omega⟩) ∧ Le μ ((Scheme.Modules.pullback ρ).map κ) := by
  obtain ⟨u, rfl⟩ := hle
  have := hs.mono
  have : Mono u := mono_of_mono u (fl.ι _)
  have hL := isVB_cokernel_one hs (fl.isSubbundle _) hv (fl.isVB _) fl.isVB_self
  let s : fl.F ⟨n + 1, by omega⟩ ⟶ fl.F ⟨n + 2, by omega⟩ := fl.step ⟨n + 1, hn⟩
  have hs' : s ≫ fl.ι _ = fl.ι _ := fl.step_ι ⟨n + 1, hn⟩
  by_cases hφ : s ≫ cokernel.π u = 0
  · have h₀ : Le (fl.ι ⟨n, by omega⟩) (fl.ι ⟨n + 1, by omega⟩) :=
      ⟨fl.step ⟨n, by omega⟩, fl.step_ι ⟨n, by omega⟩⟩
    have h₁ : Le (fl.ι ⟨n + 1, by omega⟩) (u ≫ fl.ι _) :=
      ⟨Abelian.monoLift u s hφ, by rw [Abelian.monoLift_comp_assoc, hs']⟩
    exact ⟨X, 𝟙 X, inferInstance, .id hX, _, (fl.pull _).ι ⟨n, by omega⟩, (fl.pull _).isSubbundle _,
      (fl.pull _).isVB _, h₀.map _, (h₀.trans h₁).map _⟩
  obtain ⟨Y, ρ, _, hρ, h₁, h₂⟩ := exists_cov_kernel hX _ (fl.isVB ⟨n + 1, by omega⟩) hL hφ
  refine ⟨Y, ρ, inferInstance, hρ, _, kernel.ι _ ≫ (fl.pull ρ).ι ⟨n + 1, by omega⟩,
    isSubbundle_comp h₁ ((fl.pull ρ).isSubbundle _), h₂, ⟨_, rfl⟩, ?_⟩
  have : Mono ((Scheme.Modules.pullback ρ).map u) :=
    (SubPull.isSubbundle_pullback X Y ρ _ _ u _ hv ⟨inferInstance, 1, hL⟩).mono
  have h₃ : (kernel.ι ((Scheme.Modules.pullback ρ).map (s ≫ cokernel.π u)) ≫
      (Scheme.Modules.pullback ρ).map s) ≫ cokernel.π ((Scheme.Modules.pullback ρ).map u) = 0 := by
    rw [← cancel_mono (cokernelComparison u (Scheme.Modules.pullback ρ)), Category.assoc,
      π_comp_cokernelComparison, Category.assoc, ← Functor.map_comp, kernel.condition, zero_comp]
  refine ⟨Abelian.monoLift _ _ h₃, ?_⟩
  refine (congrArg (_ ≫ ·) (Functor.map_comp _ u _)).trans
    ((Abelian.monoLift_comp_assoc _ _ h₃ _).trans ((Category.assoc ..).trans ?_))
  rw [← Functor.map_comp, hs']
  rfl

def Moves (p : X ⟶ Sp k) (D : ℕ) (fl : Flag E r) (n : Fin (r + 1)) (κ : H ⟶ E) : Prop :=
  ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y), IsCov p D ρ ∧
    ∃ g : Flag ((Scheme.Modules.pullback ρ).obj E) r, Joined (fl.pull ρ) g ∧
      Same (g.ι n) ((Scheme.Modules.pullback ρ).map κ) ∧
      ∀ i, n < i → Same (g.ι i) ((fl.pull ρ).ι i)

theorem Moves.of_pull {fl : Flag E r} {n : Fin (r + 1)} {κ : H ⟶ E} {ρ : Y ⟶ X} (hρ : IsCov p D ρ)
    (h : Moves (ρ ≫ p) D (fl.pull ρ) n ((Scheme.Modules.pullback ρ).map κ)) : Moves p D fl n κ := by
  obtain ⟨Z, τ, _, hτ, g, h₁, h₂, h₃⟩ := h
  exact ⟨Z, τ ≫ ρ, inferInstance, hρ.comp hτ, g.ofIso ((Scheme.Modules.pullbackComp τ ρ).app E),
    (h₁.ofIso _).head (adjacent_pull_pull fl ρ τ).symm,
    (h₂.comp _).trans (same_natIso (Scheme.Modules.pullbackComp τ ρ) κ), fun i hi =>
      ((h₃ i hi).comp _).trans (same_natIso (Scheme.Modules.pullbackComp τ ρ) (fl.ι i))⟩

theorem moves (n : ℕ) : ∀ {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {E H : X.Modules},
    IsArithVar p D → ∀ (fl : Flag E r) (hn : n < r) (κ : H ⟶ E), IsSubbundle κ → IsVB H n →
      Le κ (fl.ι ⟨n + 1, by omega⟩) → Moves p D fl ⟨n, by omega⟩ κ := by
  induction n with
  | zero =>
    intro X _ p E H hX fl hn κ _ hv _
    have h₀ := isVB_zero_iff.1 ((fl.pull (𝟙 X)).isVB ⟨0, by omega⟩)
    exact ⟨X, 𝟙 X, inferInstance, .id hX, _, .refl,
      ⟨h₀.iso (isVB_zero_iff.1 (hv.pullback _)), h₀.eq_of_src _ _⟩, fun _ _ => .refl _⟩
  | succ n ih =>
    intro X _ p E H hX fl hn κ hs hv hle
    obtain ⟨Y, ρ, _, hρ, K, μ, h₁, h₂, h₃, h₄⟩ := exists_common hX fl hn hs hv hle
    refine .of_pull hρ ?_
    obtain ⟨Z, τ, _, hτ, g, k₁, k₂, k₃⟩ := ih hρ.1 (fl.pull ρ) (by omega) μ h₁ h₂ h₃
    obtain ⟨g', l₁, l₂⟩ := exists_update g ⟨n + 1, by omega⟩
      (SubPull.isSubbundle_pullback _ _ τ _ _ _ _ (hv.pullback ρ)
        (SubPull.isSubbundle_pullback _ _ ρ _ _ κ _ hv hs)) ((hv.pullback ρ).pullback τ)
      (fun e => hn.ne (congrArg Fin.val e))
      (fun i hi => by
        obtain rfl : i = ⟨n, Nat.lt_of_succ_lt hn⟩ := Fin.ext (Nat.succ_injective (congrArg Fin.val hi))
        exact k₂.le.trans (h₄.map _))
      (fun i hi => by
        obtain rfl : i = ⟨n + 1, hn⟩ := Fin.ext (congrArg Fin.val hi :)
        exact ((hle.map _).map _).trans
          (k₃ ⟨n + 2, by omega⟩ (Fin.mk_lt_mk.2 (by omega))).symm.le)
    exact ⟨Z, τ, inferInstance, hτ, g', k₁.tail ⟨_, fun i hi => (l₂ i hi).symm⟩, l₁, fun i hi =>
      (l₂ i hi.ne').trans (k₃ i (lt_trans (Fin.mk_lt_mk.2 n.lt_succ_self) hi))⟩

theorem joined_of_same (n : ℕ) : ∀ {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {E : X.Modules},
    IsArithVar p D → n ≤ r → ∀ fl fl' : Flag E r,
      (∀ i : Fin (r + 1), n ≤ i → Same (fl.ι i) (fl'.ι i)) →
      ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y), IsCov p D ρ ∧
        Joined (fl.pull ρ) (fl'.pull ρ) := by
  induction n with
  | zero =>
    intro X _ p E hX _ fl fl' h
    exact ⟨X, 𝟙 X, inferInstance, .id hX,
      Joined.pull (.single ⟨0, fun i _ => h i (Nat.zero_le _)⟩) _⟩
  | succ n ih =>
    intro X _ p E hX hn fl fl' h
    obtain ⟨Y, ρ, _, hρ, g, h₁, h₂, h₃⟩ := moves n hX fl hn (fl'.ι ⟨n, by omega⟩)
      (fl'.isSubbundle _) (fl'.isVB _)
      (Le.trans ⟨fl'.step ⟨n, hn⟩, fl'.step_ι ⟨n, hn⟩⟩ (h ⟨n + 1, by omega⟩ le_rfl).symm.le)
    obtain ⟨Z, τ, _, hτ, k₁⟩ := ih hρ.1 (by omega) g (fl'.pull ρ) fun i hi => by
      rcases hi.eq_or_lt with e | e
      · obtain rfl : i = ⟨n, Nat.lt_succ_of_lt hn⟩ := Fin.ext e.symm
        exact h₂
      · exact (h₃ i e).trans ((h i e).map _)
    exact ⟨Z, τ ≫ ρ, inferInstance, hρ.comp hτ, Joined.pull_comp ((h₁.pull τ).trans k₁)⟩

theorem exists_cov_joined (hX : IsArithVar p D) (fl fl' : Flag E r) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y), IsCov p D ρ ∧
      Joined (fl.pull ρ) (fl'.pull ρ) :=
  joined_of_same r hX le_rfl fl fl' fun i hi => by
    obtain rfl : i = Fin.last r := Fin.last_le_iff.1 hi
    exact ⟨asIso (fl.ι _) ≪≫ (asIso (fl'.ι _)).symm, by simp⟩

end Covers

theorem exists_seq {α : Type*} {R : α → α → Prop} {a b : α} (h : Relation.ReflTransGen R a b) :
    ∃ (m : ℕ) (g : Fin (m + 1) → α), g 0 = a ∧ g (Fin.last m) = b ∧
      ∀ j : Fin m, R (g j.castSucc) (g j.succ) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun _ => b, rfl, rfl, finZeroElim⟩
  | @head a c hac _ ih =>
    obtain ⟨m, g, rfl, h₂, h₃⟩ := ih
    exact ⟨m + 1, Fin.cons a g, rfl, h₂, Fin.cases hac h₃⟩

theorem exists_chain : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], (∀ (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsIntegral Y], IsArithVar q 1 → Nonempty (RegCover q)) → IsArithVar p 1 → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl fl' : Vert.Flag E r), ∃ (C : RegCover p) (m : ℕ) (g : Fin (m + 1) → Vert.Flag ((Scheme.Modules.pullback C.ρ).obj E) r), (∀ a : ℝ, VMetric.IsFlagCh2 H fl a ↔ VMetric.IsFlagCh2 (H.pull C.ρ rfl) (g 0) (C.deg * a)) ∧ (∀ a : ℝ, VMetric.IsFlagCh2 H fl' a ↔ VMetric.IsFlagCh2 (H.pull C.ρ rfl) (g (Fin.last m)) (C.deg * a)) ∧ ∀ j : Fin m, (g j.castSucc).Adjacent (g j.succ) := by
  intro hA k _ X p _ hR hX E r h H fl fl'
  obtain ⟨Y, ρ, _, hρ, hj⟩ := exists_cov_joined hX fl fl'
  obtain ⟨C'⟩ := hR Y (ρ ≫ p) hρ.1
  have hC : IsCov p 1 (C'.ρ ≫ ρ) := hρ.comp ⟨C'.reg.toIsArithVar, C'.generic, C'.finite⟩
  obtain ⟨m, g, h₀, h₁, h₂⟩ := exists_seq (hj.pull C'.ρ).pull_comp
  refine ⟨⟨C'.Y, C'.ρ ≫ ρ, (Category.assoc C'.ρ ρ p).symm ▸ C'.reg, hC.2.1, hC.2.2⟩, m, g,
    fun a => ?_, fun a => ?_, h₂⟩
  · rw [h₀]
    exact FlagPull.isFlagCh2_flag_pull hA k X p _ _ hX hC.1 _ rfl hC.2.1 hC.2.2 E r h H fl a
  · rw [h₁]
    exact FlagPull.isFlagCh2_flag_pull hA k X p _ _ hX hC.1 _ rfl hC.2.1 hC.2.2 E r h H fl' a

end GlobalTheory.FlagChain
