import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeLiftRatioMemIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConeLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PderivComp1PtZeroEqZero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Onto CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.ConeUnit
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.OntoFirstChernCocycle

variable {K : Type} [CommRing K] {Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of K)}

abbrev Pt (T : Thick (smFun Y q)) : Scheme.{0} := Spec (CommRingCat.of (T.B ⧸ T.J))

abbrev gam (T : Thick (smFun Y q)) : Γ(Pt T, ⊤) →+* T.B ⧸ T.J := (Scheme.ΓSpecIso (CommRingCat.of (T.B ⧸ T.J))).hom.hom

abbrev qm {T T' : Thick (smFun Y q)} (φ : T ⟶ T') : Pt T' ⟶ Pt T :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle))

theorem lift_unit (T : Thick (smFun Y q)) (v : (Γ(Pt T, ⊤))ˣ) :
    ∃ w : T.Bˣ, Ideal.Quotient.mk T.J (w : T.B) = gam T (v : Γ(Pt T, ⊤)) :=
  GlobalTheory.CompanionTheory.ConeLiftEx.exists_unit_lift T.J (fun x hx => GlobalTheory.CompanionTheory.SiteNil.thick_J_isNilpotent _ x hx)
    (Units.map (gam T).toMonoidHom v)

theorem range_sub {T : Thick (smFun Y q)} {V : Y.Opens} (h : InU V T) : Set.range (pt T) ⊆ Set.range V.ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  exact h (show x ∈ (⊤ : Scheme.Opens _) from trivial)

def lf (T : Thick (smFun Y q)) {V : Y.Opens} (h : InU V T) : Pt T ⟶ (V : Scheme.{0}) :=
  IsOpenImmersion.lift V.ι (pt T) (range_sub h)

theorem lf_fac (T : Thick (smFun Y q)) {V : Y.Opens} (h : InU V T) : lf T h ≫ V.ι = pt T :=
  IsOpenImmersion.lift_fac _ _ _

theorem lf_nat {T T' : Thick (smFun Y q)} (φ : T ⟶ T') {V : Y.Opens} (h : InU V T) (h' : InU V T') :
    qm φ ≫ lf T h = lf T' h' := by
  rw [← cancel_mono V.ι, Category.assoc, lf_fac, lf_fac]
  exact pt_of_hom φ

theorem lf_le (T : Thick (smFun Y q)) {V V' : Y.Opens} (k : V ≤ V') (h : InU V T) (h' : InU V' T) :
    lf T h ≫ Y.homOfLE k = lf T h' := by
  rw [← cancel_mono V'.ι, Category.assoc, lf_fac, Scheme.homOfLE_ι, lf_fac]

theorem ev_eq (T : Thick (smFun Y q)) {V : Y.Opens} (h : InU V T) (g : Γ(Y, V)) :
    ev T h g = gam T ((lf T h).appTop.hom (V.topIso.inv.hom g)) := by
  have e : (pt T).appLE V ⊤ h = V.topIso.inv ≫ (lf T h).appTop := by
    have e1 : V.topIso.inv = V.ι.appLE V ⊤ V.ι_preimage_self.ge := by
      rw [Scheme.Opens.ι_appLE]
      rfl
    have e2 : (lf T h).appTop = (lf T h).appLE ⊤ ⊤ le_top := by
      simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rw [e1, e2, Scheme.Hom.appLE_comp_appLE]
    simp only [lf_fac]
  exact congrArg (fun k => gam T (k.hom g)) e

theorem compat (D : E.LineData Y) {T T' : Thick (smFun Y q)} (φ : T ⟶ T') (p e : Pt T ⟶ D.Y) (p' e' : Pt T' ⟶ D.Y)
    (hpe : p ≫ D.f = e ≫ D.f) (hpe' : p' ≫ D.f = e' ≫ D.f) (hqp : (qm φ ≫ p) ≫ D.f = p' ≫ D.f) (hee : qm φ ≫ e = e')
    (w : T'.Bˣ) (t : T.Bˣ) (t' : T'.Bˣ)
    (hw : Ideal.Quotient.mk T'.J (w : T'.B) = gam T' (D.u (qm φ ≫ p) p' hqp : Γ(Pt T', ⊤)))
    (ht : Ideal.Quotient.mk T.J (t : T.B) = gam T (D.u p e hpe : Γ(Pt T, ⊤)))
    (ht' : Ideal.Quotient.mk T'.J (t' : T'.B) = gam T' (D.u p' e' hpe' : Γ(Pt T', ⊤))) :
    ((w * (t' * (Units.map φ.φ.toMonoidHom t)⁻¹) : T'.Bˣ) : T'.B) - 1 ∈ T'.J := by
  have h1 : (qm φ ≫ p) ≫ D.f = (qm φ ≫ e) ≫ D.f := by rw [Category.assoc, Category.assoc, hpe]
  have nat := D.nat (qm φ) p e hpe
  have A : Ideal.Quotient.mk T'.J ((Units.map φ.φ.toMonoidHom t : T'.Bˣ) : T'.B) =
      gam T' (D.u (qm φ ≫ p) (qm φ ≫ e) h1 : Γ(Pt T', ⊤)) := by
    change Ideal.quotientMap T'.J φ.φ φ.hle (Ideal.Quotient.mk T.J t) = _
    rw [ht, nat, ← gamma_nat]
    rfl
  have coc := D.coc (qm φ ≫ p) p' e' hqp hpe'
  have uc : D.u (qm φ ≫ p) e' (hqp.trans hpe') = D.u (qm φ ≫ p) (qm φ ≫ e) h1 := by
    subst hee
    rfl
  have B : Ideal.Quotient.mk T'.J (w : T'.B) * Ideal.Quotient.mk T'.J (t' : T'.B) =
      Ideal.Quotient.mk T'.J ((Units.map φ.φ.toMonoidHom t : T'.Bˣ) : T'.B) := by
    rw [A, hw, ht', ← map_mul, ← Units.val_mul, coc, uc]
  rw [← Ideal.Quotient.eq, map_one, Units.val_mul, Units.val_mul, map_mul, map_mul, ← mul_assoc, B, ← map_mul, Units.mul_inv, map_one]

theorem tau_ev (D : E.LineData Y) {T : Thick (smFun Y q)} {V : Y.Opens} (h : InU V T) (p : Pt T ⟶ D.Y)
    (a a' : (V : Scheme.{0}) ⟶ D.Y) (haa : a ≫ D.f = a' ≫ D.f) (hp : p ≫ D.f = (lf T h ≫ a) ≫ D.f)
    (hp' : p ≫ D.f = (lf T h ≫ a') ≫ D.f) (t t' : T.Bˣ)
    (ht : Ideal.Quotient.mk T.J (t : T.B) = gam T (D.u p (lf T h ≫ a) hp : Γ(Pt T, ⊤)))
    (ht' : Ideal.Quotient.mk T.J (t' : T.B) = gam T (D.u p (lf T h ≫ a') hp' : Γ(Pt T, ⊤)))
    (u : Γ(Y, V)) (hu : V.topIso.inv.hom u = (D.u a a' haa : Γ((V : Scheme.{0}), ⊤))) :
    Ideal.Quotient.mk T.J (t : T.B) * ev T h u = Ideal.Quotient.mk T.J (t' : T.B) := by
  have h2 : (lf T h ≫ a) ≫ D.f = (lf T h ≫ a') ≫ D.f := by rw [Category.assoc, Category.assoc, haa]
  have coc := D.coc p (lf T h ≫ a) (lf T h ≫ a') hp h2
  have nat := D.nat (lf T h) a a' haa
  rw [ev_eq, hu, ht, ht', ← congrArg Units.val coc, Units.val_mul, map_mul, nat]
  rfl

section Fam

variable {Cc : Type 1} [Category.{0} Cc] (g : Cc ⥤ Thick (smFun Y q))

abbrev HH : Cc ⥤ CommAlgCat.{0} K := g ⋙ thA (smFun Y q)

abbrev a1 : IdF (HH g) := (thFil (smFun Y q) ((1 : ℕ) : ℤ)).res g

abbrev a2 : IdF (HH g) := (thFil (smFun Y q) (((1 : ℕ) : ℤ) + 1)).res g

theorem hab1 (T : Cc) (x y : (HH g).obj T) (hx : x ∈ (a1 g).S T) (hy : y ∈ (a1 g).S T) : x * y ∈ (a2 g).S T :=
  (grOk (smFun Y q) (show 1 + 0 = 1 from rfl)).ab (g.obj T) hx hy

theorem J_le (T : Cc) {x : (g.obj T).B} (hx : x ∈ (g.obj T).J) : x ∈ (a1 g).S T := Thick.J_le_pdPow_one _ hx

variable {g} {D : E.LineData Y}

abbrev wΛ (Λ : CLiftK g D) {c c' : Cc} (φ : c ⟶ c') : ((HH g).obj c')ˣ := Λ.w φ

theorem hq (Λ : CLiftK g D) {c c' : Cc} (φ : c ⟶ c') : (qm (g.map φ) ≫ Λ.p c) ≫ D.f = Λ.p c' ≫ D.f := by
  rw [Category.assoc, Λ.hp, Λ.hp]
  exact pt_of_hom (g.map φ)

theorem W_mem (Λ : CLiftK g D) (e : ∀ c, Pt (g.obj c) ⟶ D.Y) (he : ∀ c, Λ.p c ≫ D.f = e c ≫ D.f)
    (hn : ∀ {c c' : Cc} (φ : c ⟶ c'), qm (g.map φ) ≫ e c = e c') (t : ∀ c, ((HH g).obj c)ˣ)
    (ht : ∀ c, Ideal.Quotient.mk (g.obj c).J (show (g.obj c).B from (t c : (HH g).obj c)) =
      gam (g.obj c) (D.u _ _ (he c) : Γ(Pt (g.obj c), ⊤))) {c c' : Cc} (φ : c ⟶ c') :
    ((tw (fun φ => wΛ Λ φ) t φ : ((HH g).obj c')ˣ) : (HH g).obj c') - 1 ∈ (a1 g).S c' :=
  J_le g c' (compat D (g.map φ) (Λ.p c) (e c) (Λ.p c') (e c') (he c) (he c') (hq Λ φ) (hn φ) (Λ.w φ) (t c) (t c')
    (Λ.hw φ (hq Λ φ)) (ht c) (ht c'))

theorem twisted_log_cocycle_d (Λ : CLiftK g D) (f : CH.Cn (sq (a1 g) (a2 g)) 2)
    (hval : ∀ s, (show sqM (a1 g) (a2 g) _ from f s).1 =
      Ideal.Quotient.mk _ ((Λ.r s : (g.obj (s.obj (Fin.last 2))).B) - 1)) (t : ∀ c, ((HH g).obj c)ˣ)
    (hW : ∀ {c c' : Cc} (φ : c ⟶ c'), ((tw (fun φ => wΛ Λ φ) t φ : ((HH g).obj c')ˣ) : (HH g).obj c') - 1 ∈ (a1 g).S c') :
    CH.d (sq (a1 g) (a2 g)) 1 (dl (a1 g) (a2 g) (fun φ => tw (fun φ => wΛ Λ φ) t φ) hW) = f := by
  funext s
  have hr : ((rU (fun φ => tw (fun φ => wΛ Λ φ) t φ) s : ((HH g).obj (s.obj (Fin.last 2)))ˣ) : (HH g).obj (s.obj (Fin.last 2))) - 1 ∈
      (a1 g).S (s.obj (Fin.last 2)) := by
    rw [rU_tw]
    exact J_le g _ (r_sub_mem Λ (s.map' 0 1) (s.map' 1 2) (s.map' 0 2) (s.map'_comp 0 1 2))
  rw [d_dl (a1 g) (a2 g) (hab1 g) _ hW s hr]
  refine Subtype.ext ((?_ : _ = _).trans (hval s).symm)
  change Ideal.Quotient.mk _ _ = _
  rw [rU_tw]
  rfl

end Fam

theorem tw_id {G : Type} [CommGroup G] (w a b m n : G) :
    w * (a * m⁻¹) = w * (b * n⁻¹) * ((a * b⁻¹) * (m * n⁻¹)⁻¹) := by
  simp only [mul_inv, inv_inv]
  have : w * (b * n⁻¹) * (a * b⁻¹ * (m⁻¹ * n)) = w * (a * m⁻¹) * (b * b⁻¹) * (n * n⁻¹) := by
    simp only [mul_assoc, mul_left_comm, mul_comm]
  rw [this]
  simp

theorem form_one {V : Y.Opens} (Λ : Lifts q V) (g₀ u : Sec q V) (s : ComposableArrows (inU q V).FullSubcategory 1) :
    Λ.form g₀ ![u] s = Λ.v _ g₀ * (Λ.v _ u - (s.map' 0 1).hom.φ (Λ.v _ u)) := by
  unfold Lifts.form
  rw [Fin.prod_univ_one]
  have e : (s.map (homOfLE (Fin.le_last (Fin.succ (0 : Fin 1))))).hom.φ (Λ.v _ u) = Λ.v _ u := by
    have : s.map (homOfLE (Fin.le_last (Fin.succ (0 : Fin 1)))) = 𝟙 _ := s.map_id _
    rw [this]
    rfl
  simp only [Matrix.cons_val_fin_one]
  rw [e]
  rfl

theorem exists_lift {Cc : Type 1} [Category.{0} Cc] (g : Cc ⥤ Thick (smFun Y q)) (D : E.LineData Y)
    (h : ∀ c, ∃ p : Pt (g.obj c) ⟶ D.Y, p ≫ D.f = pt (g.obj c)) : Nonempty (CLiftK g D) := by
  choose p hp using h
  have hq' : ∀ {c c' : Cc} (φ : c ⟶ c'), (qm (g.map φ) ≫ p c) ≫ D.f = p c' ≫ D.f := by
    intro c c' φ
    rw [Category.assoc, hp, hp]
    exact pt_of_hom (g.map φ)
  have hw : ∀ {c c' : Cc} (φ : c ⟶ c'), ∃ w : (g.obj c').Bˣ,
      Ideal.Quotient.mk (g.obj c').J (w : (g.obj c').B) = gam (g.obj c') (D.u _ _ (hq' φ) : Γ(Pt (g.obj c'), ⊤)) :=
    fun φ => lift_unit _ _
  choose w hw using @hw
  exact ⟨{ p := p, hp := hp, w := fun φ => w φ, hw := fun φ _ => hw φ }⟩

def PU (q : Y ⟶ Spec (CommRingCat.of K)) {ι : Type} (U : ι → Y.Opens) : ObjectProperty (Thick (smFun Y q)) :=
  fun T => ∃ α, inU q (U α) T

theorem jU (q : Y ⟶ Spec (CommRingCat.of K)) {ι : Type} (U : ι → Y.Opens) (α : ι) : inU q (U α) ≤ PU q U :=
  fun _ h => ⟨α, h⟩

theorem cls_congr {R : Type} [CommRing R] (Kx : Cx.{1} R) {n : ℕ} {x y : Kx.X n} (h : x = y) (hx : Kx.d n x = 0) (hy : Kx.d n y = 0) :
    Kx.cls x hx = Kx.cls y hy := by
  subst h
  rfl

theorem u_right (D : E.LineData Y) {V : Scheme.{0}} {a b b' : V ⟶ D.Y} (hb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a ≫ D.f = b' ≫ D.f) : D.u a b h = D.u a b' h' := by
  subst hb
  rfl

section Data

variable {D : E.LineData Y} {ι : Type} {U : ι → Y.Opens}

def Lα (Λ : CLiftK (PU q U).ι D) (α : ι) : CLiftK (inU q (U α)).ι D := Λ.precomp (ObjectProperty.ιOfLE (jU q U α))

def eA (σ : ∀ α, (U α : Scheme.{0}) ⟶ D.Y) (α : ι) (c : (inU q (U α)).FullSubcategory) : Pt c.obj ⟶ D.Y :=
  lf c.obj c.property ≫ σ α

theorem he_A (Λ : CLiftK (PU q U).ι D) (σ : ∀ α, (U α : Scheme.{0}) ⟶ D.Y) (hσ : ∀ α, σ α ≫ D.f = (U α).ι) (α : ι)
    (c : (inU q (U α)).FullSubcategory) : (Lα Λ α).p c ≫ D.f = eA σ α c ≫ D.f := by
  rw [(Lα Λ α).hp, eA, Category.assoc, hσ, lf_fac]
  rfl

theorem hn_A (σ : ∀ α, (U α : Scheme.{0}) ⟶ D.Y) (α : ι) {c c' : (inU q (U α)).FullSubcategory} (φ : c ⟶ c') :
    qm ((inU q (U α)).ι.map φ) ≫ eA σ α c = eA σ α c' := by
  rw [eA, eA, ← Category.assoc]
  exact congrArg (· ≫ σ α) (lf_nat φ.hom c.property c'.property)

end Data

theorem tau_ev' (D : E.LineData Y) {T : Thick (smFun Y q)} {V V₁ V₂ : Y.Opens} (h : InU V T) (p : Pt T ⟶ D.Y)
    (σ₁ : (V₁ : Scheme.{0}) ⟶ D.Y) (σ₂ : (V₂ : Scheme.{0}) ⟶ D.Y) (k₁ : V ≤ V₁) (k₂ : V ≤ V₂) (h₁ : InU V₁ T) (h₂ : InU V₂ T)
    (haa : (Y.homOfLE k₁ ≫ σ₁) ≫ D.f = (Y.homOfLE k₂ ≫ σ₂) ≫ D.f) (hp₁ : p ≫ D.f = (lf T h₁ ≫ σ₁) ≫ D.f)
    (hp₂ : p ≫ D.f = (lf T h₂ ≫ σ₂) ≫ D.f) (t t' : T.Bˣ)
    (ht : Ideal.Quotient.mk T.J (t : T.B) = gam T (Units.val (D.u p (lf T h₁ ≫ σ₁) hp₁)))
    (ht' : Ideal.Quotient.mk T.J (t' : T.B) = gam T (Units.val (D.u p (lf T h₂ ≫ σ₂) hp₂)))
    (u : Γ(Y, V)) (hu : V.topIso.inv.hom u = Units.val (D.u _ _ haa)) :
    Ideal.Quotient.mk T.J (t : T.B) * ev T h u = Ideal.Quotient.mk T.J (t' : T.B) := by
  have hb : lf T h₁ ≫ σ₁ = lf T h ≫ Y.homOfLE k₁ ≫ σ₁ := by rw [← Category.assoc, lf_le T k₁ h h₁]
  have hb' : lf T h₂ ≫ σ₂ = lf T h ≫ Y.homOfLE k₂ ≫ σ₂ := by rw [← Category.assoc, lf_le T k₂ h h₂]
  have hp := hp₁
  have hp' := hp₂
  rw [hb] at hp
  rw [hb'] at hp'
  exact tau_ev D h p _ _ haa hp hp' t t' (ht.trans (congrArg (fun v => gam T (Units.val v)) (u_right D hb _ _)))
    (ht'.trans (congrArg (fun v => gam T (Units.val v)) (u_right D hb' _ _))) u hu

theorem mk3 {B : Type} [CommRing B] (J : Ideal B) (x y z : B) (e : B ⧸ J)
    (h : Ideal.Quotient.mk J x * Ideal.Quotient.mk J y * e = 1) (hz : Ideal.Quotient.mk J z = e) :
    Ideal.Quotient.mk J (x * y * z) = Ideal.Quotient.mk J 1 := by
  rw [map_mul, map_mul, hz, h, map_one]

theorem mk2 {B : Type} [CommRing B] (J : Ideal B) (x y g : B) (e : B ⧸ J) (hg : Ideal.Quotient.mk J g = -e)
    (h : -e + Ideal.Quotient.mk J x * Ideal.Quotient.mk J y = 0) : Ideal.Quotient.mk J (g + x * y) = 0 := by
  rw [map_add, map_mul, hg, h]

theorem tau_alg {A : Type} [CommRing A] {a bi b e ei : A} (h1 : a * e = b) (h2 : b * bi = 1) (h3 : e * ei = 1) :
    a * bi * e = 1 ∧ -ei + a * bi = 0 := by
  refine ⟨by linear_combination bi * h1 + h2, ?_⟩
  linear_combination ei * (bi * h1 + h2) - a * bi * h3

theorem main : CrystallineSemistableComparison.Onto.FirstChernCoboundary := by
  intro K _ Y q D ι U σ hσ r hr hc
  have hsec : ∀ c : (PU q U).FullSubcategory, ∃ V ∈ 𝒱D D, InU V ((PU q U).ι.obj c) := by
    rintro ⟨T, α, h⟩
    exact ⟨U α, ⟨σ α, hσ α⟩, h⟩
  obtain ⟨Λ⟩ : Nonempty (CLiftK (PU q U).ι D) := by
    refine exists_lift _ D ?_
    rintro ⟨T, α, h⟩
    exact ⟨lf T h ≫ σ α, by rw [Category.assoc, hσ, lf_fac]; rfl⟩
  obtain ⟨f, hf, hcl, hval⟩ := hc (PU q U).FullSubcategory (PU q U).ι hsec Λ
  have hy : CH.d ((PU q U).ι ⋙ G q 1) 2 ((CH.Mor.restrict (G q 1) (PU q U).ι).pullC 2 r) = 0 := by
    rw [CH.Mor.d_pullC, hr, map_zero]
  obtain ⟨bb, hbb⟩ := cls_eq_d (F := (PU q U).ι ⋙ G q 1) hy hf hcl
  have ex : ∀ (α : ι) (c : (inU q (U α)).FullSubcategory), ∃ t : ((HH (inU q (U α)).ι).obj c)ˣ,
      Ideal.Quotient.mk c.obj.J (show c.obj.B from (t : (HH (inU q (U α)).ι).obj c)) =
        gam ((inU q (U α)).ι.obj c) (Units.val (D.u _ _ (he_A Λ σ hσ α c))) := fun α c => lift_unit c.obj _
  choose t ht using ex
  have hW : ∀ (α : ι) {c c' : (inU q (U α)).FullSubcategory} (φ : c ⟶ c'),
      ((tw (fun φ => wΛ (Lα Λ α) φ) (t α) φ : ((HH (inU q (U α)).ι).obj c')ˣ) : (HH (inU q (U α)).ι).obj c') - 1 ∈
        (a1 (inU q (U α)).ι).S c' :=
    fun α _ _ φ => W_mem (Lα Λ α) (eA σ α) (he_A Λ σ hσ α) (hn_A σ α) (t α) (ht α) φ
  obtain ⟨dA, hdA⟩ : ∃ dA : ∀ α, CH.Cn ((inU q (U α)).ι ⋙ G q 1) 1, ∀ α, dA α =
      dl (a1 (inU q (U α)).ι) (a2 (inU q (U α)).ι) (fun φ => tw (fun φ => wΛ (Lα Λ α) φ) (t α) φ) (hW α) := ⟨_, fun α => rfl⟩
  have dW : ∀ α : ι, CH.d ((inU q (U α)).ι ⋙ G q 1) 1 (dA α) = (resU (G q 1) (jU q U α)).pullC 2 f := by
    intro α
    rw [hdA]
    exact twisted_log_cocycle_d (Lα Λ α) ((resU (G q 1) (jU q U α)).pullC 2 f) (fun s => hval (s ⋙ ObjectProperty.ιOfLE (jU q U α))) (t α) (hW α)
  have hβ : ∀ α : ι, CH.d ((inU q (U α)).ι ⋙ G q 1) 1 ((resU (G q 1) (jU q U α)).pullC 1 bb + dA α) =
        (CH.Mor.restrict (G q 1) (inU q (U α)).ι).pullC 2 r := by
    intro α
    rw [map_add, CH.Mor.d_pullC, hbb, map_sub, dW, sub_add_cancel]
    rfl
  refine ⟨-1, fun α => (resU (G q 1) (jU q U α)).pullC 1 bb + dA α, hβ, ?_⟩
  intro α α' V h h' k k' u hu
  let W₁ : ∀ {c c' : (inU q V).FullSubcategory}, (c ⟶ c') → ((HH (inU q V).ι).obj c')ˣ :=
    fun φ => tw (fun φ => wΛ (Lα Λ α) φ) (t α) ((ObjectProperty.ιOfLE k).map φ)
  let W₂ : ∀ {c c' : (inU q V).FullSubcategory}, (c ⟶ c') → ((HH (inU q V).ι).obj c')ˣ :=
    fun φ => tw (fun φ => wΛ (Lα Λ α') φ) (t α') ((ObjectProperty.ιOfLE k').map φ)
  have hW₁ : ∀ {c c' : (inU q V).FullSubcategory} (φ : c ⟶ c'), ((W₁ φ : ((HH (inU q V).ι).obj c')ˣ) : (HH (inU q V).ι).obj c') - 1 ∈
      (a1 (inU q V).ι).S c' := fun φ => hW α ((ObjectProperty.ιOfLE k).map φ)
  have hW₂ : ∀ {c c' : (inU q V).FullSubcategory} (φ : c ⟶ c'), ((W₂ φ : ((HH (inU q V).ι).obj c')ˣ) : (HH (inU q V).ι).obj c') - 1 ∈
      (a1 (inU q V).ι).S c' := fun φ => hW α' ((ObjectProperty.ιOfLE k').map φ)
  let d₁ : CH.Cn ((inU q V).ι ⋙ G q 1) 1 := dl (a1 (inU q V).ι) (a2 (inU q V).ι) (fun φ => W₁ φ) hW₁
  let d₂ : CH.Cn ((inU q V).ι ⋙ G q 1) 1 := dl (a1 (inU q V).ι) (a2 (inU q V).ι) (fun φ => W₂ φ) hW₂
  have e₁ : (resU (G q 1) k).pullC 1 ((resU (G q 1) (jU q U α)).pullC 1 bb + dA α) =
      (resU (G q 1) (le_trans k (jU q U α))).pullC 1 bb + d₁ := by
    rw [map_add, hdA]
    rfl
  have e₂ : (resU (G q 1) k').pullC 1 ((resU (G q 1) (jU q U α')).pullC 1 bb + dA α') =
      (resU (G q 1) (le_trans k (jU q U α))).pullC 1 bb + d₂ := by
    rw [map_add, hdA]
    rfl
  have hz : CH.d ((inU q V).ι ⋙ G q 1) 1 ((resU (G q 1) k).pullC 1 ((resU (G q 1) (jU q U α)).pullC 1 bb + dA α) -
      (resU (G q 1) k').pullC 1 ((resU (G q 1) (jU q U α')).pullC 1 bb + dA α')) = 0 := by
    rw [map_sub, CH.Mor.d_pullC, CH.Mor.d_pullC, hβ, hβ, sub_eq_zero]
    rfl
  have e₃ : (resU (G q 1) k).pullC 1 ((resU (G q 1) (jU q U α)).pullC 1 bb + dA α) -
      (resU (G q 1) k').pullC 1 ((resU (G q 1) (jU q U α')).pullC 1 bb + dA α') = d₁ - d₂ := by
    rw [e₁, e₂, add_sub_add_left_eq_sub]
  have hx := e₃ ▸ hz
  refine ⟨hz, fun Λ' => ?_⟩
  have key : ∀ c : (inU q V).FullSubcategory,
      Ideal.Quotient.mk c.obj.J (show c.obj.B from Units.val (t α ((ObjectProperty.ιOfLE k).obj c))) *
        ev c.obj c.property (u : Sec q V) =
      Ideal.Quotient.mk c.obj.J (show c.obj.B from Units.val (t α' ((ObjectProperty.ιOfLE k').obj c))) := by
    intro c
    exact tau_ev' D c.property ((Lα Λ α).p ((ObjectProperty.ιOfLE k).obj c)) (σ α) (σ α') h h'
      ((ObjectProperty.ιOfLE k).obj c).property ((ObjectProperty.ιOfLE k').obj c).property (by simp [hσ])
      (he_A Λ σ hσ α ((ObjectProperty.ιOfLE k).obj c)) (he_A Λ σ hσ α' ((ObjectProperty.ιOfLE k').obj c))
      (t α ((ObjectProperty.ιOfLE k).obj c)) (t α' ((ObjectProperty.ιOfLE k').obj c))
      (ht α ((ObjectProperty.ιOfLE k).obj c)) (ht α' ((ObjectProperty.ιOfLE k').obj c)) (u : Sec q V) hu
  let t₁ : ∀ c : (inU q V).FullSubcategory, ((HH (inU q V).ι).obj c)ˣ := fun c => t α ((ObjectProperty.ιOfLE k).obj c)
  let t₂ : ∀ c : (inU q V).FullSubcategory, ((HH (inU q V).ι).obj c)ˣ := fun c => t α' ((ObjectProperty.ιOfLE k').obj c)
  let τ : ∀ c : (inU q V).FullSubcategory, ((HH (inU q V).ι).obj c)ˣ := fun c => t₁ c * (t₂ c)⁻¹
  let ũ : ∀ c : (inU q V).FullSubcategory, (HH (inU q V).ι).obj c := fun c => Λ'.v c (u : Sec q V)
  let gg : ∀ c : (inU q V).FullSubcategory, (HH (inU q V).ι).obj c := fun c => Λ'.v c (((-1 : ℤˣ) : ℤ) • (↑u⁻¹ : Sec q V))
  have hτ : ∀ {c c' : (inU q V).FullSubcategory} (φ : c ⟶ c'), W₁ φ = W₂ φ * (τ c' * (mu φ (τ c))⁻¹) := by
    intro c c' φ
    have e : mu φ (τ c) = mu φ (t₁ c) * (mu φ (t₂ c))⁻¹ := (map_mul _ _ _).trans (congrArg _ (map_inv _ _))
    rw [e]
    exact tw_id _ _ _ _ _
  have alg : ∀ c : (inU q V).FullSubcategory, _ := fun c => tau_alg (key c)
    (show Ideal.Quotient.mk c.obj.J (show c.obj.B from Units.val (t α' ((ObjectProperty.ιOfLE k').obj c))) *
      Ideal.Quotient.mk c.obj.J (show c.obj.B from Units.val (t α' ((ObjectProperty.ιOfLE k').obj c))⁻¹) = 1 by
      rw [← map_mul]
      exact (congrArg _ (Units.mul_inv (t α' ((ObjectProperty.ιOfLE k').obj c)))).trans (map_one _))
    (show ev c.obj c.property (u : Sec q V) * ev c.obj c.property (↑u⁻¹ : Sec q V) = 1 by
      rw [← map_mul, Units.mul_inv, map_one])
  have h1 : ∀ c, (τ c : (HH (inU q V).ι).obj c) * ũ c - 1 ∈ (a1 (inU q V).ι).S c := by
    intro c
    refine J_le _ c (Ideal.Quotient.eq.1 ?_)
    exact mk3 c.obj.J (Units.val (t₁ c)) (Units.val (t₂ c)⁻¹) (ũ c) _ (alg c).1 (Λ'.hv c _)
  have h2 : ∀ c, gg c + (τ c : (HH (inU q V).ι).obj c) ∈ (a1 (inU q V).ι).S c := by
    intro c
    refine J_le _ c (Ideal.Quotient.eq_zero_iff_mem.1 ?_)
    have e : (((-1 : ℤˣ) : ℤ) • (↑u⁻¹ : Sec q V)) = -(↑u⁻¹ : Sec q V) := by simp
    refine mk2 c.obj.J (Units.val (t₁ c)) (Units.val (t₂ c)⁻¹) (gg c) _ ?_ (alg c).2
    refine (Λ'.hv c _).trans ?_
    rw [e, map_neg]
  have rep := form_rep (a1 (inU q V).ι) (a2 (inU q V).ι) (hab1 _) (fun φ => W₁ φ) (fun φ => W₂ φ) hW₁ hW₂ τ hτ ũ gg h1 h2 hx
  have ez : Λ'.form (((-1 : ℤˣ) : ℤ) • (↑u⁻¹ : Sec q V)) ![(u : Sec q V)] = _ := funext (form_one Λ' _ _)
  rw [ez, cls_congr _ e₃ hz hx]
  exact rep

end GlobalTheory.CompanionTheory.OntoFirstChernCocycle
