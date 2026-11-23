import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionEqMulOfVanishingModElement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveAlgebraisationFormalEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LocalEmb

open MvPolynomial GlobalTheory.Unif.PolyStep GlobalTheory.Unif.FormalEmb GlobalTheory.MorAlg

theorem small_step {V A A₀ A' σ : Type} [CommRing V] [CommRing A] [CommRing A₀] [CommRing A'] (q : V →+* A)
    (g₀ : A →+* A₀) (g' : A →+* A') (a : V) (hq : Function.Surjective q) (hg₀ : Function.Surjective g₀)
    (hg' : Function.Surjective g') (hn : IsNilpotent (RingHom.ker g₀)) (hk : RingHom.ker g' = Ideal.span {q a})
    (ha₀ : q a ∈ RingHom.ker g₀) (ha : ∀ x, q a * x = 0 ↔ x ∈ RingHom.ker g₀) {X X₀ X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of A)} {f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)} {f' : X' ⟶ Spec (CommRingCat.of A')}
    {j₀ : X₀ ⟶ X} {β : X' ⟶ X} (hf : Flat f) (P₀ : IsPullback j₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)))
    (P' : IsPullback β f' f (Spec.map (CommRingCat.ofHom g'))) {H : LB X} {H₀ : LB X₀} {H' : LB X'}
    {s : σ → LB.Sec H} {s₀ : σ → LB.Sec H₀} {s' : σ → LB.Sec H'} (hH : H.IsLB) (hH₀ : H₀.IsLB) (hH' : H'.IsLB)
    (h₀ : IsPull j₀ s s₀) (h' : IsPull β s s') {t : ℕ}
    (ht : ∀ τ : LB.Sec (pw H₀ t), ∃ F : MvPolynomial σ A₀, F.IsHomogeneous t ∧
      ∀ k : H₀.ι, τ.f k = eval₂Hom (cst f₀ (H₀.U k)) (fun j => (s₀ j).f k) F)
    {F : MvPolynomial σ V} (hF : F.IsHomogeneous t)
    (hF0 : F ∈ vanIdeal (β ≫ f ≫ Spec.map (CommRingCat.ofHom q)) s') :
    ∃ G : MvPolynomial σ V, G.IsHomogeneous t ∧ F - C a * G ∈ vanIdeal (f ≫ Spec.map (CommRingCat.ofHom q)) s := by
  obtain ⟨w, hw, hr⟩ := h₀
  obtain ⟨v, -, hs⟩ := h'
  rw [mem_vanIdeal] at hF0
  have c₂ : j₀ ≫ f ≫ Spec.map (CommRingCat.ofHom q) = f₀ ≫ Spec.map (CommRingCat.ofHom (g₀.comp q)) := by
    rw [← Category.assoc, P₀.w, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨τ₀, hτ⟩ := GlobalTheory.SectionKernel.exists_sec_of_vanishing _ _ _ g₀ g' (q a) hg₀ hg' hn hk ha₀ ha _ _ _ _ _ _
    j₀ β hf P₀ P' (pw H t) (pw H₀ t) (pwIso w t) (isLB_pw hH _) (isLB_pw hH₀ _)
    ((isGen_iff _).2 (pgen_pwIso ((isGen_iff _).1 hw) t))
    (formSec (f ≫ Spec.map (CommRingCat.ofHom q)) s hF) (fun k =>
      fn_ext fun z hz => by
        obtain ⟨i, hi⟩ := exists_chart hH' z
        have h := Rel.form (w := v) hs (f ≫ Spec.map (CommRingCat.ofHom q)) hF z k i hz hi
        rw [hF0 i, ← gsHom_apply (𝟙 _) z _ hi, map_zero, mul_zero] at h
        refine (gs_pull (𝟙 _) β z _ hz _).trans ?_
        rw [Category.id_comp, ← gsHom_apply (𝟙 _) z _ hz, map_zero]
        exact h)
  obtain ⟨G₀, hG₀, hτ₀⟩ := ht τ₀
  obtain ⟨G, hG, rfl⟩ := exists_lift (g₀.comp q) (hg₀.comp hq) hG₀
  refine ⟨G, hG, (mem_vanIdeal _ _ _).2 fun k => ?_⟩
  have h := hτ (formSec (f ≫ Spec.map (CommRingCat.ofHom q)) s hG)
    (fun z k k' hk hk' => by
      have h := Rel.form (w := w) hr (f ≫ Spec.map (CommRingCat.ofHom q)) hG z k k' hk hk'
      rw [c₂, Unif.PolyStep.cst_comp f₀, ← MvPolynomial.eval₂Hom_map_hom] at h
      exact h.trans (congrArg₂ (· * ·) (congrArg Units.val (gw_pwIso w t (𝟙 _) z k k').symm)
        (congrArg (gs (𝟙 _) z _) (hτ₀ k').symm))) k
  rw [map_sub, map_mul, MvPolynomial.eval₂Hom_C, sub_eq_zero]
  exact h.trans (congrArg (· * _) (RingHom.congr_fun (Unif.PolyStep.cst_comp f _ _) _).symm)

theorem mem_vanIdeal_of_isIso {V σ : Type} [CommRing V] {X X' : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of V))
    {β : X' ⟶ X} [IsIso β] {H : LB X} {H' : LB X'} {s : σ → LB.Sec H} {s' : σ → LB.Sec H'} (hH' : H'.IsLB)
    (h' : IsPull β s s') {t : ℕ} {F : MvPolynomial σ V} (hF : F.IsHomogeneous t)
    (hF0 : F ∈ vanIdeal (β ≫ p) s') : F ∈ vanIdeal p s := by
  obtain ⟨v, -, hs⟩ := h'
  rw [mem_vanIdeal] at hF0 ⊢
  refine fun k => fn_ext fun x hx => ?_
  obtain ⟨z, rfl⟩ := β.surjective x
  obtain ⟨i, hi⟩ := exists_chart hH' z
  have h := Rel.form (w := v) hs p hF z k i hx hi
  rw [hF0 i, ← gsHom_apply (𝟙 _) z _ hi, map_zero, mul_zero] at h
  have e := gs_stalkMap β (𝟙 X) z _ hx (eval₂Hom (AbLaw.cst p (H.U k)) (fun j => (s j).f k) F)
  rw [Category.comp_id, h] at e
  rw [← gsHom_apply (𝟙 _) (β z) _ hx 0, map_zero]
  exact (ConcreteCategory.bijective_of_isIso (β.stalkMap z)).1 (e.trans (map_zero _).symm)

abbrev fac {V : Type} [CommRing V] {J J' : Ideal V} (h : J ≤ J') :
    Spec (CommRingCat.of (V ⧸ J')) ⟶ Spec (CommRingCat.of (V ⧸ J)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))

abbrev quo {V : Type} [CommRing V] (J : Ideal V) : Spec (CommRingCat.of (V ⧸ J)) ⟶ Spec (CommRingCat.of V) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))

theorem fac_fac {V : Type} [CommRing V] {J J' J'' : Ideal V} (h : J ≤ J') (h' : J' ≤ J'') :
    fac h' ≫ fac h = fac (h.trans h') := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp]

theorem fac_quo {V : Type} [CommRing V] {J J' : Ideal V} (h : J ≤ J') : fac h ≫ quo J = quo J' := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]

theorem mk_mem_ker {V : Type} [CommRing V] {J J' : Ideal V} (h : J ≤ J') (x : V) :
    Ideal.Quotient.mk J x ∈ RingHom.ker (Ideal.Quotient.factor h) ↔ x ∈ J' := by
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]

theorem nilpotent_ker_factor {V : Type} [CommRing V] {J J' : Ideal V} (h : J ≤ J') {N : ℕ} (hN : J' ^ N ≤ J) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor h)) := by
  refine ⟨N, le_bot_iff.1 ?_⟩
  have h₁ : RingHom.ker (Ideal.Quotient.factor h) ≤ J'.map (Ideal.Quotient.mk J) := fun x hx => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.mem_map_of_mem _ ((mk_mem_ker h x).1 hx)
  refine (Ideal.pow_right_mono h₁ N).trans ?_
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact hN

theorem correction {V σ : Type} [CommRing V] [IsNoetherianRing V] {M J₁ : Ideal V} (hM : M.IsMaximal)
    (hJ₁ : J₁ ≤ M) (N : ℕ) {X₀ X₁ : Scheme.{0}} (f₀ : X₀ ⟶ Spec (CommRingCat.of (V ⧸ M)))
    (f₁ : X₁ ⟶ Spec (CommRingCat.of (V ⧸ J₁))) {H₀ : LB X₀} {H₁ : LB X₁} {s₀ : σ → LB.Sec H₀} {s₁ : σ → LB.Sec H₁}
    (hH₀ : H₀.IsLB) (hH₁ : H₁.IsLB) {t : ℕ}
    (ht : ∀ τ : LB.Sec (pw H₀ t), ∃ F : MvPolynomial σ (V ⧸ M), F.IsHomogeneous t ∧
      ∀ k : H₀.ι, τ.f k = eval₂Hom (cst f₀ (H₀.U k)) (fun j => (s₀ j).f k) F)
    {F : MvPolynomial σ V} (hF : F.IsHomogeneous t) (hF0 : F ∈ vanIdeal (f₁ ≫ quo J₁) s₁) (J : Ideal V) :
    ∀ (h₁ : J ≤ J₁), M ^ N ≤ J → M * J₁ ≤ J → ∀ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of (V ⧸ J)))
      (j₀ : X₀ ⟶ X) (β : X₁ ⟶ X), Flat f → IsPullback j₀ f₀ f (fac (h₁.trans hJ₁)) → IsPullback β f₁ f (fac h₁) →
      ∀ (H : LB X) (s : σ → LB.Sec H), H.IsLB → IsPull j₀ s s₀ → IsPull β s s₁ →
      ∃ G ∈ J₁ • homogeneousSubmodule σ V t, F - G ∈ vanIdeal (f ≫ quo J) s := by
  induction J using IsNoetherian.induction with
  | hgt J ih => ?_
  intro h₁ hN hm X f j₀ β hf P₀ P₁ H s hH h₀ h'
  have c₁ : β ≫ f ≫ quo J = f₁ ≫ quo J₁ := by rw [← Category.assoc, P₁.w, Category.assoc, fac_quo]
  by_cases hle : J₁ ≤ J
  · have : IsIso (fac h₁) := ⟨fac hle, by rw [fac_fac]; simp [fac], by rw [fac_fac]; simp [fac]⟩
    have : IsIso β := P₁.isIso_fst_of_isIso
    refine ⟨0, zero_mem _, ?_⟩
    rw [sub_zero]
    exact mem_vanIdeal_of_isIso _ hH₁ h' hF (c₁ ▸ hF0)
  obtain ⟨a, ha₁, ha⟩ := SetLike.not_le_iff_exists.1 hle
  have haJ : a ∈ J ⊔ Ideal.span {a} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  have l₁ : J ≤ J ⊔ Ideal.span {a} := le_sup_left
  have l₂ : J ⊔ Ideal.span {a} ≤ J₁ := sup_le h₁ ((Ideal.span_singleton_le_iff_mem _).2 ha₁)
  have P := IsPullback.of_hasPullback f (fac l₁)
  have hL := LB.isLB_pull hH (pullback.fst f (fac l₁))
  obtain ⟨s', hs'⟩ := exists_isPull (pullback.fst f (fac l₁)) hH s
  have key : ∀ {J' : Ideal V} (l : J ⊔ Ideal.span {a} ≤ J') {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of (V ⧸ J')))
      (b : Y ⟶ X), IsPullback b g f (fac (l₁.trans l)) → ∀ {K : LB Y} (u : σ → LB.Sec K), K.IsLB → IsPull b s u →
      ∃ b' : Y ⟶ pullback f (fac l₁), IsPullback b' g (pullback.snd f (fac l₁)) (fac l) ∧ IsPull b' s' u := by
    intro J' l Y g b Q K u hK hu
    have e : b ≫ f = (g ≫ fac l) ≫ fac l₁ := by rw [Q.w, Category.assoc, fac_fac]
    refine ⟨pullback.lift b (g ≫ fac l) e, IsPullback.of_right ?_ (pullback.lift_snd _ _ _) P,
      IsPull.cancel hH hL hK hs' ?_⟩
    · rwa [pullback.lift_fst, fac_fac]
    · rwa [pullback.lift_fst]
  obtain ⟨j₀', P₀', h₀'⟩ := key (l₂.trans hJ₁) f₀ j₀ P₀ s₀ hH₀ h₀
  obtain ⟨β', P₁', h₁'⟩ := key l₂ f₁ β P₁ s₁ hH₁ h'
  obtain ⟨G', hG', hFG'⟩ := ih (J ⊔ Ideal.span {a}) (lt_of_le_of_ne l₁ fun e => ha (e ▸ haJ)) l₂ (hN.trans l₁)
    (hm.trans l₁) _ (pullback.snd f (fac l₁)) j₀' β' inferInstance P₀' P₁' _ s' hL h₀' h₁'
  have hFG : (F - G').IsHomogeneous t := hF.sub (Submodule.smul_le_right hG')
  obtain ⟨G, hG, h⟩ := small_step (Ideal.Quotient.mk J) (Ideal.Quotient.factor (h₁.trans hJ₁))
    (Ideal.Quotient.factor l₁) a Ideal.Quotient.mk_surjective (Ideal.Quotient.factor_surjective _)
    (Ideal.Quotient.factor_surjective _) (nilpotent_ker_factor _ hN)
    (by
      apply le_antisymm
      · intro x hx
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨c, y, hy, rfl⟩ := Ideal.mem_span_singleton_sup.1 (sup_comm J _ ▸ (mk_mem_ker _ x).1 hx)
        rw [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.2 hy, add_zero]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      · rwa [Ideal.span_singleton_le_iff_mem, mk_mem_ker])
    ((mk_mem_ker _ a).2 (hJ₁ ha₁))
    (fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [mk_mem_ker, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      refine ⟨fun h => by_contra fun hx => ha ?_, fun h => hm (mul_comm a x ▸ Ideal.mul_mem_mul h ha₁)⟩
      obtain ⟨y, m, hm', e⟩ := hM.exists_inv hx
      have : a = y * (a * x) + m * a := by linear_combination (-a) * e
      rw [this]
      exact add_mem (Ideal.mul_mem_left J _ h) (hm (Ideal.mul_mem_mul hm' ha₁)))
    hf P₀ P hH hH₀ hL h₀ hs' ht hFG (by rwa [← Category.assoc, P.w, Category.assoc, fac_quo])
  refine ⟨G' + C a * G, add_mem hG' ?_, by rwa [← sub_sub]⟩
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem_smul ha₁ hG

theorem exists_limit {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]
    [IsPrecomplete I M] (K : ℕ → Submodule R M) (hK : ∀ e, K (e + 1) ≤ K e) (ha : ∀ e, I ^ (e + 1) • ⊤ ≤ K e)
    (hs : ∀ e, ∀ x ∈ K e, ∃ y ∈ (I ^ (e + 1) • ⊤ : Submodule R M), x - y ∈ K (e + 1)) (e : ℕ) (x : M)
    (hx : x ∈ K e) : ∃ x' : M, (∀ e', x' ∈ K e') ∧ x - x' ∈ (I ^ (e + 1) • ⊤ : Submodule R M) := by
  have hanti : Antitone K := antitone_nat_of_succ_le hK
  have mono : ∀ {m n : ℕ}, m ≤ n → (I ^ n • ⊤ : Submodule R M) ≤ I ^ m • ⊤ := fun h =>
    Submodule.smul_mono_left (Ideal.pow_le_pow_right h)
  choose y hy' hy using hs
  let s : (n : ℕ) → K (e + n) := fun n =>
    Nat.rec (motive := fun n => K (e + n)) ⟨x, hx⟩ (fun n z => ⟨z.1 - y (e + n) z.1 z.2, hy _ _ _⟩) n
  have hsn : ∀ n, (s (n + 1) : M) = s n - y (e + n) (s n).1 (s n).2 := fun n => rfl
  have hd : ∀ m n, m ≤ n → (s m : M) - s n ∈ (I ^ (e + m + 1) • ⊤ : Submodule R M) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hsn, ← sub_add]
      exact add_mem ih (mono (by omega) (hy' _ _ _))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := M) inferInstance (f := fun n => (s n : M))
    (fun {m n} hmn => SModEq.sub_mem.2 (mono (by omega) (hd m n hmn)))
  have hl : ∀ m, (s m : M) - L ∈ (I ^ (e + m + 1) • ⊤ : Submodule R M) := fun m => by
    have := add_mem (hd m (e + m + 1) (by omega)) (SModEq.sub_mem.1 (hL (e + m + 1)))
    rwa [sub_add_sub_cancel] at this
  refine ⟨L, fun m => hanti (show m ≤ e + m by omega) ?_, hl 0⟩
  have := sub_mem (s m).2 (ha _ (hl m))
  rwa [sub_sub_cancel] at this

theorem exists_form_limit {R σ : Type} [CommRing R] [Finite σ] (I : Ideal R) [IsAdicComplete I R]
    (K : ℕ → Ideal (MvPolynomial σ R)) (t : ℕ) (h₁ : ∀ e F, F.IsHomogeneous t → F ∈ K (e + 1) → F ∈ K e)
    (h₂ : ∀ e, ∀ a ∈ I ^ (e + 1), C a ∈ K e)
    (h₃ : ∀ e F, F.IsHomogeneous t → F ∈ K e → ∃ G ∈ I ^ (e + 1) • homogeneousSubmodule σ R t, F - G ∈ K (e + 1))
    (e : ℕ) (F : MvPolynomial σ R) (hF : F.IsHomogeneous t) (h : F ∈ K e) :
    ∃ F₁ : MvPolynomial σ R, F₁.IsHomogeneous t ∧ (∀ e', F₁ ∈ K e') ∧
      map (Ideal.Quotient.mk (I ^ (e + 1))) F₁ = map (Ideal.Quotient.mk (I ^ (e + 1))) F := by
  haveI : Module.Finite R (homogeneousSubmodule σ R t) := Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
  haveI := GlobalTheory.isPrecomplete_of_finite I (homogeneousSubmodule σ R t)
  obtain ⟨x', hx', hy⟩ := exists_limit I
    (fun e => ((K e).restrictScalars R).comap (homogeneousSubmodule σ R t).subtype)
    (fun e x hx => h₁ e x.1 x.2 hx)
    (fun e => Submodule.smul_le.2 fun a ha x _ => by
      show a • x.1 ∈ K e
      rw [smul_eq_C_mul]
      exact Ideal.mul_mem_right _ _ (h₂ e a ha))
    (fun e x hx => by
      obtain ⟨G, hG, h⟩ := h₃ e x.1 x.2 hx
      exact ⟨⟨G, Submodule.smul_le_right hG⟩, (Submodule.mem_smul_top_iff _ _ _).2 hG, h⟩) e ⟨F, hF⟩ h
  refine ⟨x'.1, x'.2, hx', ?_⟩
  rw [eq_comm, ← sub_eq_zero, ← map_sub]
  have hy' : F - x'.1 ∈ I ^ (e + 1) • homogeneousSubmodule σ R t := (Submodule.mem_smul_top_iff _ _ _).1 hy
  refine Submodule.smul_induction_on (p := fun G => map (Ideal.Quotient.mk (I ^ (e + 1))) G = 0) hy'
    (fun a ha G _ => ?_) (fun x y hx hy => ?_)
  · rw [smul_eq_C_mul, map_mul, map_C, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero, zero_mul]
  · rw [map_add, hx, hy, add_zero]

theorem exists_projective_of_formal_embedding : ∀ (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e)) → (∀ e, Flat (Y e).hom) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e, (∀ j, (∀ z (k : (H (e + 1)).ι) (k' : (H e).ι), (β e) z ∈ (H (e + 1)).U k → z ∈ (H e).U k' → gs (β e) z _ ((s (e + 1) j).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k')))) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ (B : Over (Spec (CommRingCat.of V))) (H' : LB B.left) (s' : Fin (n + 1) → LB.Sec H') (b : ∀ e, (Y e).left ⟶ B.left) (w : ∀ e, LB.Iso (H e) (H'.pull (b e))), H'.IsLB ∧ VeryAmpleBy B.hom H' s' ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (w e).IsGen ∧ (∀ j, (∀ z (k : (H').ι) (k' : (H e).ι), (b e) z ∈ (H').U k → z ∈ (H e).U k' → gs (b e) z _ ((s' j).f k) = (Geo.Tor.gw (w e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k')))) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) V), F.IsHomogeneous t → (∀ e, (∀ k : (H e).ι, MvPolynomial.eval₂Hom (cst ((Y (e)).hom ≫ thick V (IsLocalRing.maximalIdeal V) (e)) ((H e).U k)) (fun j => (s e j).f k) (F) = 0)) → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (B.hom) ((H').U k)) (fun j => (s' j).f k) (F) = 0) := by
  intro V _ _ _ _ Y β hβ hflat H v hH n s hs hva
  have hp : ∀ e, (IsLocalRing.maximalIdeal V ^ (0 + 1)) ^ e ≤ IsLocalRing.maximalIdeal V ^ e := fun e => by
    rw [zero_add, pow_one]
  have hVA : ∀ e, VeryAmpleBy (Y e).hom (H e) (s e) := by
    rintro (_ | e)
    · exact hva
    · obtain ⟨j₀, hj, w, hw, hr⟩ := tower _ Y β hβ H v hH s hs e
      exact GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _)
        (nilpotent_ker_factor _ (hp _)) _ _ _ _ j₀ hj _ _ w n _ _ (hH _).1 (hH _).1 ((isGen_iff _).2 hw) hr hva
  have c₁ : ∀ e, β e ≫ (Y (e + 1)).hom ≫ thick V (IsLocalRing.maximalIdeal V) (e + 1) =
      (Y e).hom ≫ thick V (IsLocalRing.maximalIdeal V) e := fun e => by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  let K : ℕ → Ideal (MvPolynomial (Fin (n + 1)) V) := fun e =>
    vanIdeal ((Y e).hom ≫ thick V (IsLocalRing.maximalIdeal V) e) (s e)
  let S : Set (MvPolynomial (Fin (n + 1)) V) := {F | (∃ t, F.IsHomogeneous t) ∧ ∀ e, F ∈ K e}
  have hS : ∀ e, Ideal.span S ≤ K e := fun e => Ideal.span_le.2 fun F hF => hF.2 e
  obtain ⟨B, f, H', s', hH', hva', hB⟩ := GlobalTheory.ProjQuot.exists_veryAmpleBy_of_ideal V n (Ideal.span S)
    (component_mem_span S fun F hF => hF.1)
  have hB' : ∀ t (F : MvPolynomial (Fin (n + 1)) V), F.IsHomogeneous t → (∀ e, F ∈ K e) → ∀ k : H'.ι,
      MvPolynomial.eval₂Hom (cst f (H'.U k)) (fun j => (s' j).f k) F = 0 := fun t F hF h =>
    (hB t F hF).2 fun i => ⟨0, by rw [pow_zero, _root_.one_mul]; exact Ideal.subset_span ⟨⟨t, hF⟩, h⟩⟩
  choose b w hb hw hr using fun e => GlobalTheory.exists_hom_of_veryAmpleBy V B f H' n s' hH' hva' _
    ((Y e).hom ≫ thick V (IsLocalRing.maximalIdeal V) e) (H e) (s e) (hH e).1 (hVA e).1 (fun t F hF h =>
      (mem_vanIdeal _ _ _).1 (mem_vanIdeal_of_sat _ _ (hVA e).1 fun i =>
        ((hB t F hF).1 h i).imp fun _ hm => hS e hm))
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.AbLaw.serre_h1Zero_and_sections_polynomial.2 _ _ (Y 0).hom (H 0) n (s 0) (hH 0).1 hva
  have hM : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]
    infer_instance
  refine ⟨Over.mk f, H', s', b, w, hH', hva', fun e => ?_, fun e => ?_, fun e => ⟨hw e, hr e⟩,
    fun t F hF h => hB' t F hF fun e => (mem_vanIdeal _ _ _).2 (h e)⟩
  · refine GlobalTheory.ProjBaseChange.isPullback_of_equations_lift V B f H' n s' hH' hva' _ _ Ideal.Quotient.mk_surjective
      _ (Y e).hom (H e) (s e) (b e) (w e) (hH e).1 (hVA e) (hb e) (hw e) (hr e) t₀ fun t ht F hF h => ?_
    obtain ⟨F₁, hF₁, hK, hG⟩ := exists_form_limit (IsLocalRing.maximalIdeal V) K t
      (fun e F hF h => by
        have := mem_vanIdeal_pull (hH (e + 1)).1 (hs e) _ hF h
        rwa [c₁] at this)
      (fun e a ha => (mem_vanIdeal _ _ _).2 fun k => by
        rw [MvPolynomial.eval₂Hom_C, GlobalTheory.Unif.PolyStep.cst_comp, RingHom.comp_apply,
          Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero])
      (fun e F hF h => by
        obtain ⟨j₀, hj, u, hu, hr⟩ := tower _ Y β hβ H v hH s hs e
        exact correction hM (Ideal.pow_le_pow_right (by omega)) (e + 1 + 1) (Y 0).hom (Y e).hom (hH 0).1 (hH e).1
          (ht₀ t ht) hF h _ _ (hp _) (by rw [← pow_add, zero_add, add_comm]) _ _ j₀ (β e) (hflat _) hj (hβ e) _ _
          (hH _).1 ⟨u, (isGen_iff _).2 hu, hr⟩ ⟨v e, (hH e).2, hs e⟩) e F hF ((mem_vanIdeal _ _ _).2 h)
    exact ⟨F₁, hF₁, hB' t F₁ hF₁ hK, hG⟩
  · have hv := (isGen_iff _).1 (hH e).2
    have hw' := (isGen_iff _).1 (hw (e + 1))
    obtain ⟨w'', T⟩ := exists_comp (hH (e + 1)).1 (w (e + 1)) (v e) hw' hv hH' (hH e).1
    exact GlobalTheory.MapUniq.hom_eq_of_pull_sections V B f H' n s' hH' hva' _ (H e) (s e) _ _ w'' (w e) (hH e).1
      (by rw [Category.assoc, hb, hb, c₁]) ((isGen_iff _).2 (T.pgen_comp (hH (e + 1)).1 hw' hv)) (hw e)
      (fun j => Rel.comp T (hH (e + 1)).1 (hr (e + 1) j) (hs e j)) (hr e)

end GlobalTheory.LocalEmb
