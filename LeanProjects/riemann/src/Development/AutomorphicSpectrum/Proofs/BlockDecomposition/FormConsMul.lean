import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

section Abs
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
  {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R}

def pairU (P : CH.Pairing F₁ F₂ F₃) (W : ObjectProperty C) :
    CH.Pairing (W.ι ⋙ F₁) (W.ι ⋙ F₂) (W.ι ⋙ F₃) :=
  ⟨fun T => P.μ T.obj, fun φ => P.nat φ.hom⟩

theorem cupU_eq {K : Type} [CommRing K] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K))
    (U : ObjectProperty (Thick (smFun Z q))) {a a' c i j n : ℕ} (ha : a + a' = c) (h : i + j = n) :
    cupU q U ha h = (pairU (grOk (smFun Z q) ha).pair U).cupC h := rfl

def incl (F : C ⥤ ModuleCat.{0} R) (W : ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q) :
    Cx.Hom (RC F W hQ) (CH.cx (W.ι ⋙ F)) (RingHom.id R) :=
  ⟨fun n => Submodule.subtype _, fun _ _ => rfl⟩

theorem cup_mem_rel (P : CH.Pairing F₁ F₂ F₃) (W : ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q)
    {p n m : ℕ} (h : p + n = m) (b : CH.Cn (W.ι ⋙ F₁) p) (x : (RC F₂ W hQ).X n) :
    (pairU P W).cupC h b x.1 ∈ relS (W.ι ⋙ F₃) (fun T => Q T.obj) m := by
  intro s hs
  have hx : x.1 ((CH.back_mono h).functor ⋙ s) = 0 :=
    x.2 _ (cosieve_res hQ W (s.map (homOfLE (Fin.zero_le _))) hs)
  change (pairU P W).μ _ _ (CH.term (W.ι ⋙ F₂) s x.1 (CH.back h) (CH.back_mono h)) = 0
  unfold CH.term
  rw [hx, map_zero, map_zero]

def relCup (P : CH.Pairing F₁ F₂ F₃) (W : ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q)
    {p n m : ℕ} (h : p + n = m) (b : CH.Cn (W.ι ⋙ F₁) p) : (RC F₂ W hQ).X n →ₗ[R] (RC F₃ W hQ).X m :=
  (((pairU P W).cupC h b).comp (Submodule.subtype _)).codRestrict _ fun x => cup_mem_rel P W hQ h b x

theorem relCup_val (P : CH.Pairing F₁ F₂ F₃) (W : ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q)
    {p n m : ℕ} (h : p + n = m) (b : CH.Cn (W.ι ⋙ F₁) p) (x : (RC F₂ W hQ).X n) :
    (relCup P W hQ h b x).1 = (pairU P W).cupC h b x.1 := rfl

theorem res_cup (P : CH.Pairing F₁ F₂ F₃) {W V : ObjectProperty C} (k : V ≤ W) {p n m : ℕ} (h : p + n = m)
    (b : CH.Cn (W.ι ⋙ F₁) p) (x : CH.Cn (W.ι ⋙ F₂) n) :
    (resU F₃ k).pullC m ((pairU P W).cupC h b x) =
      (pairU P V).cupC h ((resU F₁ k).pullC p b) ((resU F₂ k).pullC n x) := rfl

theorem res_cup_top (P : CH.Pairing F₁ F₂ F₃) (V : ObjectProperty C) {p n m : ℕ} (h : p + n = m)
    (b : CH.Cn F₁ p) (x : CH.Cn F₂ n) :
    (CH.Mor.restrict F₃ V.ι).pullC m (P.cupC h b x) =
      (pairU P V).cupC h ((CH.Mor.restrict F₁ V.ι).pullC p b) ((CH.Mor.restrict F₂ V.ι).pullC n x) := rfl

end Abs

section Cone
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
  {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} {ι : Type} [DecidableEq ι]

theorem capU_le (U : ι → ObjectProperty C) (S : Finset ι) {α : ι} (hα : α ∈ S) : capU U S ≤ U α :=
  fun _ h => h.2 α hα

def rhoS (P : CH.Pairing F₁ F₂ F₃) (U : ι → ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q)
    (r : CH.Cn F₁ 2) (S : Finset ι) (n : ℕ) :
    ((covSy F₂ U hQ).K S).X n →ₗ[R] ((covSy F₃ U hQ).K S).X (n + 2) :=
  relCup P (capU U S) hQ (by omega : 2 + n = n + 2) ((CH.Mor.restrict F₁ (capU U S).ι).pullC 2 r)

def etaS (P : CH.Pairing F₁ F₂ F₃) (U : ι → ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q)
    (β : ∀ α, CH.Cn ((U α).ι ⋙ F₁) 1) (α : ι) (S : Finset ι) (hS : α ∈ S) (n : ℕ) :
    ((covSy F₂ U hQ).K S).X n →ₗ[R] ((covSy F₃ U hQ).K S).X (n + 1) :=
  relCup P (capU U S) hQ (by omega : 1 + n = n + 1) ((resU F₁ (capU_le U S hS)).pullC 1 (β α))

theorem cone_apply (hCK : ConeKill) (hCD : CovDesc) (P : CH.Pairing F₁ F₂ F₃) (U : ι → ObjectProperty C)
    (hU : ∀ α, Cosieve (U α)) {Q : ObjectProperty C} (hQ : Cosieve Q) (a : ℕ)
    (h1 : (covSy F₂ U hQ).One a) (h2 : (covSy F₃ U hQ).One (a + 1))
    (r : CH.Cn F₁ 2) (hr : CH.d F₁ 2 r = 0) (β : ∀ α, CH.Cn ((U α).ι ⋙ F₁) 1)
    (hβ : ∀ α, CH.d _ 1 (β α) = (CH.Mor.restrict F₁ (U α).ι).pullC 2 r)
    (lam : ∀ (α : ι) (S : Finset ι), α ∈ S →
      (((covSy F₂ U hQ).K S).H a →ₗ[R] ((covSy F₃ U hQ).K S).H (a + 1)))
    (lam_nat : ∀ α {S T : Finset ι} (h : S ⊆ T) hS x, lam α T (h hS) (((covSy F₂ U hQ).res h).mapH a x) =
      ((covSy F₃ U hQ).res h).mapH _ (lam α S hS x))
    (lam_diff : ∀ α α' S hS hS' x hx hz,
      ((covSy F₃ U hQ).K S).cls (etaS P U hQ β α S hS a x - etaS P U hQ β α' S hS' a x) hz =
        lam α S hS (((covSy F₂ U hQ).K S).cls x hx) - lam α' S hS' (((covSy F₂ U hQ).K S).cls x hx))
    (n : ℕ) (x : ((covSy F₂ U hQ).K ∅).X n) (hx : ((covSy F₂ U hQ).K ∅).d n x = 0) :
    rhoS P U hQ r ∅ n x ∈ ((covSy F₃ U hQ).K ∅).B (n + 2) := by
  refine hCK R ι (covSy F₂ U hQ) (covSy F₃ U hQ) a (hCD R ι C F₂ U Q hQ hU) (hCD R ι C F₃ U Q hQ hU) h1 h2
    (rhoS P U hQ r) (etaS P U hQ β) ?_ ?_ ?_ ?_ lam lam_nat lam_diff n x hx
  · intro S n x
    refine Subtype.ext ?_
    change CH.d _ (n + 2) ((pairU P (capU U S)).cupC _ _ x.1) = (pairU P (capU U S)).cupC _ _ (CH.d _ n x.1)
    rw [CrystallineSemistableComparison.P.leibniz, CH.Mor.d_pullC, hr]
    simp
  · intro S T h n x
    rfl
  · intro α S T h hS n x
    rfl
  · intro α S hS n x
    refine Subtype.ext ?_
    change CH.d _ (n + 1) ((pairU P (capU U S)).cupC _ _ x.1) + (pairU P (capU U S)).cupC _ _ (CH.d _ n x.1) =
      (pairU P (capU U S)).cupC _ _ x.1
    rw [CrystallineSemistableComparison.P.leibniz, CH.Mor.d_pullC, hβ]
    simp
    rfl

end Cone

section Top
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem relNull_top (hT : TopRes) (F : C ⥤ ModuleCat.{0} R) {Q : ObjectProperty C} (hQ : Cosieve Q)
    (Wt Wp : ObjectProperty C) (hWt : ∀ T, Wt T) (h : Wp ≤ Wt) {n : ℕ}
    (hb : Function.Bijective ((RC.res F hQ h).mapH (n + 2))) (y : CH.Cn F (n + 2)) (hy : CH.d F (n + 2) y = 0)
    (hyr : y ∈ relS F Q (n + 2)) (x : (RC F Wp hQ).X (n + 2)) (hx : x.1 = (CH.Mor.restrict F Wp.ι).pullC (n + 2) y)
    (hB : x ∈ (RC F Wp hQ).B (n + 2)) : RelNull F Q (n + 2) y := by
  obtain ⟨hb2, hm2⟩ := hT R C F Wt Q hWt (n + 2)
  obtain ⟨hb1, hm1⟩ := hT R C F Wt Q hWt (n + 1)
  let y' : (RC F Wt hQ).X (n + 2) := ⟨(CH.Mor.restrict F Wt.ι).pullC (n + 2) y, (hm2 y).2 hyr⟩
  have hy' : (RC F Wt hQ).d (n + 2) y' = 0 := by
    refine Subtype.ext ?_
    change CH.d _ (n + 2) ((CH.Mor.restrict F Wt.ι).pullC (n + 2) y) = 0
    rw [CH.Mor.d_pullC, hy, map_zero]
  have hxy : (RC.res F hQ h).f (n + 2) y' = x := Subtype.ext hx.symm
  have hdx : (RC F Wp hQ).d (n + 2) x = 0 := by
    rw [← hxy, (RC.res F hQ h).comm, hy', map_zero]
  have h0 : (RC.res F hQ h).mapH (n + 2) ((RC F Wt hQ).cls y' hy') = 0 := by
    have e : (RC.res F hQ h).mapH (n + 2) ((RC F Wt hQ).cls y' hy') = (RC F Wp hQ).cls x hdx := by
      refine congrArg Submodule.Quotient.mk (Subtype.ext hxy)
    rw [e]
    exact (Submodule.Quotient.mk_eq_zero _).2 hB
  have h1 : (RC F Wt hQ).cls y' hy' = 0 := hb.1 (h0.trans (map_zero _).symm)
  have h2 : (⟨y', hy'⟩ : (RC F Wt hQ).Z (n + 2)) ∈ ((RC F Wt hQ).B (n + 2)).submoduleOf ((RC F Wt hQ).Z (n + 2)) :=
    (Submodule.Quotient.mk_eq_zero _).1 h1
  have h3 : y' ∈ (RC F Wt hQ).B (n + 2) := h2
  obtain ⟨b', hb'⟩ := h3
  obtain ⟨b, hbb⟩ := hb1.2 b'.1
  refine ⟨b, (hm1 b).1 (hbb ▸ b'.2), hb2.1 ?_⟩
  rw [← CH.Mor.d_pullC, hbb]
  exact congrArg Subtype.val hb'

end Top

section Forms
variable {K A B : Type} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

theorem lin_ext (hFL : FormLaws) {a : ℕ} {M : Type*} [AddCommGroup M] [Module K M] (g g' : Om K A a →ₗ[K] M)
    (h : ∀ g₀ (v : Fin a → A), g (form K g₀ v) = g' (form K g₀ v)) : g = g' :=
  LinearMap.ext_on (hFL K A A a).1 (by rintro _ ⟨g₀, v, rfl⟩; exact h g₀ v)

theorem form_cons_mul {a : ℕ} (g₀ u f : A) (v : Fin a → A) :
    form K g₀ (Fin.cons (u * f) v : Fin (a + 1) → A) =
      u • form K g₀ (Fin.cons f v : Fin (a + 1) → A) + f • form K g₀ (Fin.cons u v : Fin (a + 1) → A) := by
  have e : ∀ x : A, (fun k => KaehlerDifferential.D K A ((Fin.cons x v : Fin (a + 1) → A) k)) =
      (Fin.cons (KaehlerDifferential.D K A x) (fun k => KaehlerDifferential.D K A (v k)) : Fin (a + 1) → Ω[A⁄K]) := by
    intro x
    funext k
    refine Fin.cases ?_ (fun k => ?_) k <;> simp
  unfold form
  rw [e, e, e, Derivation.leibniz]
  have h1 := (exteriorPower.ιMulti A (a + 1) (M := Ω[A⁄K])).toMultilinearMap.cons_add
    (fun k => KaehlerDifferential.D K A (v k)) (u • KaehlerDifferential.D K A f) (f • KaehlerDifferential.D K A u)
  have h2 := (exteriorPower.ιMulti A (a + 1) (M := Ω[A⁄K])).toMultilinearMap.cons_smul
    (fun k => KaehlerDifferential.D K A (v k)) u (KaehlerDifferential.D K A f)
  have h3 := (exteriorPower.ιMulti A (a + 1) (M := Ω[A⁄K])).toMultilinearMap.cons_smul
    (fun k => KaehlerDifferential.D K A (v k)) f (KaehlerDifferential.D K A u)
  simp only [AlternatingMap.coe_multilinearMap] at h1 h2 h3
  rw [h1, h2, h3, smul_add, smul_comm g₀ u, smul_comm g₀ f]

theorem wedge_mul (hFL : FormLaws) {a : ℕ} (u f : A) (wuf wf wu : Om K A a →ₗ[A] Om K A (a + 1))
    (huf : ∀ g₀ (g : Fin a → A), wuf (form K g₀ g) = form K g₀ (Fin.cons (u * f) g))
    (hf : ∀ g₀ (g : Fin a → A), wf (form K g₀ g) = form K g₀ (Fin.cons f g))
    (hu : ∀ g₀ (g : Fin a → A), wu (form K g₀ g) = form K g₀ (Fin.cons u g)) (ω : Om K A a) :
    wuf ω = u • wf ω + f • wu ω := by
  have := lin_ext (K := K) hFL (wuf.restrictScalars K) (u • wf.restrictScalars K + f • wu.restrictScalars K) (by
    intro g₀ v
    simp [huf, hf, hu, form_cons_mul])
  exact LinearMap.congr_fun this ω

theorem relOm_map (hFL : FormLaws) {a : ℕ} (φ : A →ₐ[K] B) (f : A) (ω : Om K A a)
    (hω : ω ∈ relOm K (Ideal.span {f}) a) : omMap φ a ω ∈ relOm K (Ideal.span {φ f}) a := by
  obtain ⟨-, hφ⟩ := hFL K A B a
  obtain ⟨h1, h2, -⟩ := hφ φ
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g₀, g, hg, rfl⟩ := hx
    rw [h1]
    refine Submodule.subset_span ⟨_, _, ?_, rfl⟩
    have hm : ∀ {x : A}, x ∈ Ideal.span {f} → φ x ∈ Ideal.span {φ f} := fun {x} hx => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    exact hg.imp hm fun ⟨k, hk⟩ => ⟨k, hm hk⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [h2]; exact Submodule.smul_mem _ _ hx

theorem wedge_map (hFL : FormLaws) {a : ℕ} (φ : A →ₐ[K] B) (f : A) (w : Om K A a →ₗ[A] Om K A (a + 1))
    (w' : Om K B a →ₗ[B] Om K B (a + 1))
    (hw : ∀ g₀ (g : Fin a → A), w (form K g₀ g) = form K g₀ (Fin.cons f g))
    (hw' : ∀ g₀ (g : Fin a → B), w' (form K g₀ g) = form K g₀ (Fin.cons (φ f) g)) (ω : Om K A a) :
    omMap φ (a + 1) (w ω) = w' (omMap φ a ω) := by
  have := lin_ext (K := K) hFL ((omMap φ (a + 1)).comp (w.restrictScalars K))
    ((w'.restrictScalars K).comp (omMap φ a)) (by
      intro g₀ v
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hw]
      rw [(hFL K A B a).2 φ |>.1, (hFL K A B (a + 1)).2 φ |>.1, hw']
      congr 1
      funext k
      refine Fin.cases ?_ (fun k => ?_) k <;> simp)
  exact LinearMap.congr_fun this ω

theorem eta_diff (hFL : FormLaws) {a : ℕ} (u : Aˣ) (f f' : A) (huf : f = u * f')
    (hnz : ∀ ω : Om K A (a + 1), f • ω = 0 → ω = 0) (w w' wu : Om K A a →ₗ[A] Om K A (a + 1))
    (hw : ∀ g₀ (g : Fin a → A), w (form K g₀ g) = form K g₀ (Fin.cons f g))
    (hw' : ∀ g₀ (g : Fin a → A), w' (form K g₀ g) = form K g₀ (Fin.cons f' g))
    (hwu : ∀ g₀ (g : Fin a → A), wu (form K g₀ g) = form K g₀ (Fin.cons (u : A) g)) (ω : Om K A a)
    (η η' : Om K A (a + 1)) (hη : f • η = w ω) (hη' : f' • η' = w' ω) :
    η - η' = (↑u⁻¹ : A) • wu ω := by
  subst huf
  have e := wedge_mul hFL (u : A) f' w w' wu hw hw' hwu ω
  have : ((u : A) * f') • (η - η' - (↑u⁻¹ : A) • wu ω) = 0 := by
    have e2 : ((u : A) * f') • ((↑u⁻¹ : A) • wu ω) = f' • wu ω := by
      rw [smul_smul, mul_comm (u : A), mul_assoc, Units.mul_inv, mul_one]
    rw [smul_sub, smul_sub, hη, e, e2, ← hη', smul_smul]
    abel
  exact sub_eq_zero.1 (hnz _ this)

end Forms

section abelian₂
variable {K : Type} [CommRing K]

theorem lin_out {Hr X O : Type*} [AddCommGroup Hr] [Module K Hr] [AddCommGroup X] [Module K X] [AddCommGroup O] [Module K O]
    (i : Hr →ₗ[K] X) (e : O →ₗ[K] X) (N : Submodule K O) (he : Function.Bijective e)
    (hr : ∀ ω, e ω ∈ LinearMap.range i ↔ ω ∈ N) : ∃ g : Hr →ₗ[K] N, ∀ y, e (g y) = i y := by
  let E := LinearEquiv.ofBijective e he
  refine ⟨((E.symm : X →ₗ[K] O).comp i).codRestrict N fun y => (hr _).1 ?_, fun y => ?_⟩
  · refine ⟨y, ?_⟩
    exact (E.apply_symm_apply (i y)).symm
  · exact E.apply_symm_apply (i y)

theorem lin_in {Hr X O : Type*} [AddCommGroup Hr] [Module K Hr] [AddCommGroup X] [Module K X] [AddCommGroup O] [Module K O]
    (i : Hr →ₗ[K] X) (e : O →ₗ[K] X) (N : Submodule K O) (hi : Function.Injective i)
    (hr : ∀ ω, e ω ∈ LinearMap.range i ↔ ω ∈ N) : ∃ g : N →ₗ[K] Hr, ∀ ω, i (g ω) = e ω := by
  let E := LinearEquiv.ofInjective i hi
  refine ⟨(E.symm : LinearMap.range i →ₗ[K] Hr).comp ((e.domRestrict N).codRestrict _ fun ω => (hr ω).2 ω.2), fun ω => ?_⟩
  have := E.apply_symm_apply ((e.domRestrict N).codRestrict _ (fun ω => (hr ω).2 ω.2) ω)
  exact congrArg Subtype.val this

variable {A : Type} [CommRing A] [Algebra K A]

theorem lam_one (hDW : DWedge) (hDL : DLog) {a : ℕ} {H₂ X₂ H₃ X₃ : Type*} [AddCommGroup H₂] [Module K H₂]
    [AddCommGroup X₂] [Module K X₂] [AddCommGroup H₃] [Module K H₃] [AddCommGroup X₃] [Module K X₃] (hFL : FormLaws)
    (i₂ : H₂ →ₗ[K] X₂) (i₃ : H₃ →ₗ[K] X₃) (e₂ : Om K A a →ₗ[K] X₂) (e₃ : Om K A (a + 1) →ₗ[K] X₃)
    (he₂ : Function.Bijective e₂) (hi₃ : Function.Injective i₃) (I : Ideal A)
    (hr₂ : ∀ ω, e₂ ω ∈ LinearMap.range i₂ ↔ ω ∈ relOm K I a)
    (hr₃ : ∀ ω, e₃ ω ∈ LinearMap.range i₃ ↔ ω ∈ relOm K I (a + 1)) (f : A) (hI : I = Ideal.span {f})
    (hnz : ∀ ω : Om K A (a + 1), f • ω = 0 → ω = 0) (c : ℤ) :
    ∃ l : H₂ →ₗ[K] H₃, ∀ (y : H₂) (ω : Om K A a) (η : Om K A (a + 1)) (w : Om K A a →ₗ[A] Om K A (a + 1)),
      (∀ g₀ (g : Fin a → A), w (form K g₀ g) = form K g₀ (Fin.cons f g)) → i₂ y = e₂ ω → f • η = w ω →
      i₃ (l y) = e₃ (c • η) := by
  subst hI
  obtain ⟨w₀, hw₀⟩ := hDW K A a f
  have hex := hDL K A a f hnz w₀ hw₀
  have uniq : ∀ η η' : Om K A (a + 1), f • η = f • η' → η = η' := fun η η' h =>
    sub_eq_zero.1 (hnz _ (by rw [smul_sub, h, sub_self]))
  let N := (relOm K (Ideal.span {f}) a).restrictScalars K
  let N' := (relOm K (Ideal.span {f}) (a + 1)).restrictScalars K
  have hch : ∀ ω : N, ∃ η : N', f • (η : Om K A (a + 1)) = w₀ ω.1 := fun ω => by
    obtain ⟨η, ⟨h1, h2⟩, -⟩ := hex ω.1 ω.2
    exact ⟨⟨η, h1⟩, h2⟩
  choose T hT using hch
  let TL : N →ₗ[K] N' :=
    { toFun := T
      map_add' := fun x y => Subtype.ext (uniq _ _ (by
        change f • ((T (x + y) : N') : Om K A (a + 1)) = f • (((T x : N') : Om K A (a + 1)) + (T y : N'))
        rw [smul_add, hT, hT, hT]
        exact map_add w₀ _ _))
      map_smul' := fun r x => Subtype.ext (uniq _ _ (by
        change f • ((T (r • x) : N') : Om K A (a + 1)) = f • (r • ((T x : N') : Om K A (a + 1)))
        rw [smul_comm f r, hT, hT]
        exact LinearMap.map_smul_of_tower w₀ r x.1)) }
  obtain ⟨g, hg⟩ := lin_out i₂ e₂ N he₂ hr₂
  obtain ⟨g', hg'⟩ := lin_in i₃ e₃ N' hi₃ hr₃
  refine ⟨g' ∘ₗ (c • TL) ∘ₗ g, fun y ω η w hw hy hη => ?_⟩
  have hww : w = w₀ := by
    have := lin_ext (K := K) hFL (w.restrictScalars K) (w₀.restrictScalars K) (fun g₀ v => by
      simp [hw, hw₀])
    exact LinearMap.ext fun x => LinearMap.congr_fun this x
  subst hww
  have hgy : (g y : Om K A a) = ω := he₂.1 ((hg y).trans hy)
  have hTy : ((T (g y) : N') : Om K A (a + 1)) = η := uniq _ _ (by rw [hT, hη, hgy])
  change i₃ (g' (c • T (g y))) = _
  rw [hg']
  congr 1
  rw [← hTy]
  rfl

end abelian₂

end GlobalTheory.CompanionTheory.RelKill
