import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LogarithmicDerivatives.CrystallineFirstChernExistsUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Zar2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.HT.constant_weight_sum_bound

open CH Pb GlobalTheory.CompanionTheory

section Gen
variable {R : Type} [CommRing R] {C D : Type 1} [Category.{0} C] [Category.{0} D] {F : D ⥤ ModuleCat.{0} R}

def incG (S : SubF F) (G : C ⥤ D) : CH.Mor (G ⋙ S.fn) (G ⋙ F) (RingHom.id R) where
  G := 𝟭 C
  τ T := (S.S (G.obj T)).subtype
  nat _ _ := rfl

theorem sub_d (S : SubF F) (G : C ⥤ D) (n : ℕ) (z : Cn (G ⋙ S.fn) n) (w : Cn (G ⋙ S.fn) (n + 1))
    (h : d _ n ((incG S G).pullC n z) = (incG S G).pullC (n + 1) w) : d _ n z = w := by
  rw [(incG S G).d_pullC] at h
  funext s
  exact Subtype.ext (congrFun h s)

def sub (F : D ⥤ ModuleCat.{0} R) {P Q : ObjectProperty D} (h : Q ≤ P) : CH.Mor (P.ι ⋙ F) (Q.ι ⋙ F) (RingHom.id R) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem res_all (F : D ⥤ ModuleCat.{0} R) (P : ObjectProperty D) (hP : ∀ T, P T) (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict F P.ι).pull j) := by
  refine CrystallineChernClass.mapH_bijective _ (fun n => ⟨fun f g e => ?_, fun g => ?_⟩) j
  · funext t
    exact congrFun e (P.lift t fun i => hP _)
  · exact ⟨fun t => g (P.lift t fun i => hP _), rfl⟩

theorem bij_three (F : D ⥤ ModuleCat.{0} R) {P Q S : ObjectProperty D} (h : Q ≤ P) (h1 : S ≤ Q) (h2 : S ≤ P) (j : ℕ)
    (s1 : Function.Bijective ((sub F h1).pull j)) (s2 : Function.Bijective ((sub F h2).pull j)) (hP : ∀ T, P T) :
    Function.Bijective ((CH.Mor.restrict F Q.ι).pull j) := by
  have s3 : Function.Bijective ((sub F h).pull j) := by
    have e : (sub F h1).pull j ∘ (sub F h).pull j = (sub F h2).pull j := funext fun x => by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
    refine (Function.Bijective.of_comp_iff' s1 _).1 ?_
    rw [e]
    exact s2
  have e : (sub F h).pull j ∘ (CH.Mor.restrict F P.ι).pull j = (CH.Mor.restrict F Q.ι).pull j := funext fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  rw [← e]
  exact s3.comp (res_all F _ hP j)

end Gen

section Th
variable {b : Base} {L : b.Fun} {Λ : Type} [CommRing Λ] (c : Λ →+* b.R)

theorem span_zero (Q : ObjectProperty (Thick L)) (T : Q.FullSubcategory) : (IdF.span (sP Q).A (0 : b.R)).S T = ⊥ := by
  change Ideal.span {algebraMap b.R ((sP Q).A.obj T) 0} = ⊥
  rw [map_zero, Ideal.span_singleton_eq_bot]

def toJ (Q : ObjectProperty (Thick L)) :
    CH.Mor (Q.ι ⋙ (B.pdS L c 1).fn) (sq (stdI Q (some 1) 0) (stdI Q none 0)) c where
  G := 𝟭 _
  τ T := { toFun := fun x => sqMk _ _ (show T.obj.B from (show (B.pdS L c 1).S T.obj from x).1)
              (Ideal.mem_sup_left (show (B.pdS L c 1).S T.obj from x).2)
           map_add' := fun _ _ => rfl
           map_smul' := fun _ _ => rfl }
  nat _ _ := rfl

theorem toJ_τ (Q : ObjectProperty (Thick L)) (T : Q.FullSubcategory) : Function.Bijective ((toJ c Q).τ T) := by
  refine ⟨fun x y e => ?_, fun y => ?_⟩
  · have h := Ideal.Quotient.eq.1 (congrArg Subtype.val e)
    change _ ∈ (⊥ : Ideal _) ⊔ (IdF.span (sP Q).A (0 : b.R)).S T at h
    rw [span_zero, sup_bot_eq, Ideal.mem_bot, sub_eq_zero] at h
    exact Subtype.ext h
  · obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
    have hy' := hy
    change _ ∈ (sFil Q 1).S T ⊔ (IdF.span (sP Q).A (0 : b.R)).S T at hy'
    rw [span_zero, sup_bot_eq] at hy'
    exact ⟨⟨y, hy'⟩, rfl⟩

theorem toJ_bij (Q : ObjectProperty (Thick L)) (n : ℕ) : Function.Bijective ((toJ c Q).pull n) := by
  refine CrystallineChernClass.mapH_bijective _ (fun n => ⟨fun f g e => ?_, fun g => ?_⟩) n
  · funext s
    have := congrFun e s
    exact (toJ_τ c Q (s.obj (Fin.last n))).1 this
  · choose f hf using fun s : ComposableArrows Q.FullSubcategory n => (toJ_τ c Q (s.obj (Fin.last n))).2 (g s)
    exact ⟨f, funext hf⟩

theorem sub_bij {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) (j : ℕ)
    (hb : Function.Bijective (((incl h).sq (incl_std h (some 1) 0) (incl_std h none 0)).pull j)) :
    Function.Bijective ((sub (B.pdS L c 1).fn h).pull j) := by
  have e : (toJ c Q).pull j ∘ (sub (B.pdS L c 1).fn h).pull j =
      ((incl h).sq (incl_std h (some 1) 0) (incl_std h none 0)).pull j ∘ (toJ c P).pull j := funext fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  refine (Function.Bijective.of_comp_iff' (toJ_bij c Q j) _).1 ?_
  rw [e]
  exact hb.comp (toJ_bij c P j)

end Th

theorem res_bij {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (hp : p ≠ 0) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤)
    {Λ : Type} [CommRing Λ] (c : Λ →+* R) (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict (B.pdS (nlFun γ p X q κ) c 1).fn (CrystallineChernClass.Lifts D).ι).pull j) := by
  have hU : Used (⊤ : ObjectProperty (Thick (nlFun γ p X q κ))) := Or.inr ⟨hp, Or.inl rfl⟩
  have h1 : St ⊤ (𝒱D D) ≤ CrystallineChernClass.Lifts (γ := γ) (p := p) (q := q) (κ := κ) D := CrystallineChernClass.st_le_lifts D
  have h1' : CrystallineChernClass.Lifts (γ := γ) (p := p) (q := q) (κ := κ) D ≤ St ⊤ {sSup (𝒱D D)} := fun T _ =>
    ⟨trivial, _, rfl, by rw [hD]; exact CrystallineChernClass.inU_top T⟩
  have b1 := (zar2 ⊤ hU (𝒱D D) (CrystallineChernClass.Lifts D) h1 h1' (fun T T' φ h _ => CrystallineChernClass.lifts_map D φ h) j).2.1 (some 1) none 0 0
  have h2 : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (𝒱D D) ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, CrystallineChernClass.inU_top T⟩
  have b2 := (zar ⊤ hU (𝒱D D) {⊤} h2 (by rintro W rfl; rw [hD]) j).2.1 (some 1) none 0 0
  have h3 : CrystallineChernClass.Lifts (γ := γ) (p := p) (q := q) (κ := κ) D ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, CrystallineChernClass.inU_top T⟩
  have hall : ∀ T, St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {⊤} T := fun T => ⟨trivial, ⊤, rfl, CrystallineChernClass.inU_top T⟩
  exact bij_three _ h3 h1 h2 j (sub_bij (b := nlBase R I γ p) c h1 j b1) (sub_bij (b := nlBase R I γ p) c h2 j b2) hall

theorem dlog_mem {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) (N : ℕ) {v : A} (hv : v - 1 ∈ J) :
    B.dlog δ N v ∈ pdP δ 1 :=
  Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _
    (Ideal.subset_span ⟨[(k + 1, v - 1)], by simpa using hv, by simp, by simp⟩)

section Core
variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
  {κ : O →+* b.R ⧸ b.I} {D : E.LineData X} {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (N : ℕ)

section
variable {C : Type 1} [Category.{0} C] {G : C ⥤ Thick ((B.schFn q).cr b ht κ)}

theorem r_mem (Lf : B.CLift G D) (s : ComposableArrows C 2) : (Lf.r s).val - 1 ∈ (G.obj (s.obj (Fin.last 2))).J := by
  have hfg : s.map' 0 2 = s.map' 0 1 ≫ s.map' 1 2 := s.map'_comp 0 1 2
  have := CocCls.red_Rf Lf (s.map' 0 1) (s.map' 1 2)
  rw [← hfg] at this
  exact CocCls.sub_one_mem this

def cocJ (Lf : B.CLift G D) : Cn (G ⋙ (B.pdS _ c 1).fn) 2 :=
  fun s => ⟨Lf.coc c N s, mem_pdS.2 (dlog_mem _ N (r_mem Lf s))⟩

variable (hN : ∀ T k, N ≤ k → ∀ x ∈ (G.obj T).J, (k.factorial : (G.obj T).B) * (G.obj T).δ.dpow (k + 1) x = 0)
include hN

theorem cocJ_closed (Lf : B.CLift G D) : d _ 2 (cocJ c N Lf) = 0 :=
  sub_d _ G 2 _ _ ((CocCls.closed Lf c N hN).trans (map_zero _).symm)

theorem cocJ_cls (Lf Lf' : B.CLift G D) (hz hz') : (cx _).cls (cocJ c N Lf) hz = (cx _).cls (cocJ c N Lf') hz' := by
  obtain ⟨v, hv⟩ := CocCls.exists_v Lf Lf'
  let y : Cn (G ⋙ (B.pdS _ c 1).fn) 1 := fun s => ⟨CocCls.yc Lf Lf' v c N s,
    mem_pdS.2 (dlog_mem _ N (CocCls.sub_one_mem (CocCls.red_Ef hv (s.map' 0 1))))⟩
  exact ((CrystallineSemistableComparison.P.cls_surj _ 2).2.2.1 _ _ hz hz').2 ⟨y, sub_d _ G 1 y _ (CocCls.d_yc hv c N hN)⟩

end

variable (D) in

def IsFirstChernClassDividedPower (x : H (B.pdS ((B.schFn q).cr b ht κ) c 1).fn 2) : Prop :=
  ∀ (C : Type 1) [Category.{0} C] (G : C ⥤ Thick ((B.schFn q).cr b ht κ)) (Lf : B.CLift G D),
    ∃ (z : Cn (G ⋙ (B.pdS _ c 1).fn) 2) (hz : d _ 2 z = 0),
      (∀ s, (show (B.pdS _ c 1).S _ from z s).1 = Lf.coc c N s) ∧
      (cx _).cls z hz = (Mor.restrict (B.pdS _ c 1).fn G).pull 2 x

theorem exu_core (D : E.LineData X) (Q : ObjectProperty (Thick ((B.schFn q).cr b ht κ)))
    (hQ : ∀ T, Q T ↔ ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = B.thPt T)
    (hbij : Function.Bijective ((CH.Mor.restrict (B.pdS ((B.schFn q).cr b ht κ) c 1).fn Q.ι).pull 2))
    (hN : ∀ (T : Thick ((B.schFn q).cr b ht κ)) (k : ℕ), N ≤ k → (k.factorial : T.B) = 0) :
    ∃! x, IsFirstChernClassDividedPower (q := q) (b := b) (ht := ht) (κ := κ) D c N x := by
  obtain ⟨Λ₀⟩ := clift_ex Q.ι D (fun T => (hQ _).1 T.property)
  have hz₀ := cocJ_closed c N (G := Q.ι) (fun T k hk x _ => by
    change ((k.factorial : ℕ) : (T.obj).B) * _ = 0
    rw [hN _ k hk, zero_mul]) Λ₀
  obtain ⟨x, hx⟩ := hbij.2 ((CH.cx _).cls _ hz₀)
  refine ⟨x, ?_, ?_⟩
  · intro C _ G Λ₁
    have hG : ∀ T, Q (G.obj T) := fun T => (hQ _).2 ⟨Λ₁.p T, Λ₁.hp T⟩
    have hN' : ∀ T k, N ≤ k → ∀ x ∈ (G.obj T).J, (k.factorial : (G.obj T).B) * (G.obj T).δ.dpow (k + 1) x = 0 :=
      fun T k hk x _ => by rw [hN _ k hk, zero_mul]
    let Λ' : B.CLift G D := CrystallineChernClass.precomp Λ₀ (Q.lift G hG)
    refine ⟨cocJ c N Λ₁, cocJ_closed c N hN' Λ₁, fun _ => rfl, ?_⟩
    rw [cocJ_cls c N hN' Λ₁ Λ' _ (cocJ_closed c N hN' Λ')]
    have e1 : (CH.Mor.restrict (B.pdS ((B.schFn q).cr b ht κ) c 1).fn G).pull 2 x =
        (CH.Mor.restrict (Q.ι ⋙ (B.pdS ((B.schFn q).cr b ht κ) c 1).fn) (Q.lift G hG)).pull 2
          ((CH.Mor.restrict (B.pdS ((B.schFn q).cr b ht κ) c 1).fn Q.ι).pull 2 x) := by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
    rw [e1, hx]
    rfl
  · intro y hy
    apply hbij.1
    obtain ⟨z, h1, h2, h3⟩ := hy _ Q.ι Λ₀
    obtain rfl : z = cocJ c N Λ₀ := funext fun s => Subtype.ext (h2 s)
    rw [hx, ← h3]

end Core

theorem exu {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤) {Λ : Type} [CommRing Λ]
    (c : Λ →+* R) (N : ℕ) (hN : (N.factorial : R) = 0) :
    ∃! x, IsFirstChernClassDividedPower (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) D c N x := by
  have hf : ∀ (T : Thick ((B.schFn q).cr (nlBase R I γ p) rfl κ)) (k : ℕ), N ≤ k → (k.factorial : T.B) = 0 := fun T k hk => by
    obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial hk
    have h0 : (k.factorial : R) = 0 := by rw [hm, Nat.cast_mul, hN, zero_mul]
    have := congrArg T.i h0
    rwa [map_natCast, map_zero] at this
  have hb := res_bij (γ := γ) (q := q) (κ := κ) hp D hD c 2
  let Q : ObjectProperty (Thick ((B.schFn q).cr (nlBase R I γ p) rfl κ)) := CrystallineChernClass.Lifts (γ := γ) (p := p) (q := q) (κ := κ) D
  have hQ : ∀ T, Q T ↔ ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = B.thPt T := fun T => Iff.rfl
  have hb' : Function.Bijective ((CH.Mor.restrict (B.pdS ((B.schFn q).cr (nlBase R I γ p) rfl κ) c 1).fn Q.ι).pull 2) := hb
  exact exu_core (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) c N D Q hQ hb' hf

open B in
theorem isFirstChernJ_base_change {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b b' : Base}
    {ht : b.t = 1} {ht' : b'.t = 1} {κ : O →+* b.R ⧸ b.I} {κ' : O →+* b'.R ⧸ b'.I}
    (σ : b.R →+* b'.R) (hp : b.p = b'.p) (hI : IsDPMorphism b.γ b'.γ σ) (τ : b.R ⧸ b.I →+* b'.R ⧸ b'.I)
    (hτ : τ.comp κ = κ') (hs)
    {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (c' : Λ →+* b'.R) (hc : ∀ a, σ (c a) = c' (RingHom.id Λ a))
    (D : E.LineData X) {N N' : ℕ} (hN : N ≤ N') (hf : ∀ k, N ≤ k → (k.factorial : b'.R) = 0)
    (y : CH.H (pdS ((schFn q).cr b ht κ) c 1).fn 2)
    (hy : IsFirstChernClassDividedPower (q := q) (b := b) (ht := ht) (κ := κ) D c N' y) :
    IsFirstChernClassDividedPower (q := q) (b := b') (ht := ht') (κ := κ') D c' N
      ((pdOm (crMor (F := schFn q) (F' := schFn q) (b := b) (b' := b') (ht := ht) (ht' := ht') σ hp hI
        (basePt (schFn q) τ hτ) hs) (RingHom.id Λ) hc 1).pull 2 y) := by
  intro C _ G Lf
  let mm := pdOm (c := c) (c' := c') (crMor (F := schFn q) (F' := schFn q) (b := b) (b' := b') (ht := ht) (ht' := ht') σ hp hI
        (basePt (schFn q) τ hτ) hs) (RingHom.id Λ) hc 1
  let G' : C ⥤ Thick ((schFn q).cr b ht κ) := G ⋙ mm.G
  let Lf' : CLift G' D := { p := Lf.p, hp := Lf.hp, w := Lf.w, hw := Lf.hw }
  obtain ⟨z, hz', hv, hcl⟩ := hy C G' Lf'
  let m4 : CH.Mor (G' ⋙ (pdS _ c 1).fn) (G ⋙ (pdS _ c' 1).fn) (RingHom.id _) :=
    { G := 𝟭 C, τ := fun T => mm.τ (G.obj T), nat := fun φ x => mm.nat (G.map φ) x }
  have hz : CH.d _ 2 (m4.pullC 2 z) = 0 := by rw [m4.d_pullC, hz', map_zero]
  refine ⟨m4.pullC 2 z, hz, fun s => (hv s).trans ?_, ?_⟩
  · refine FirstChernClassFactorial.dlog_eq_of_factorial (G.obj (s.obj (Fin.last 2))).δ hN (fun j hj => ?_) _
    have := congrArg (G.obj (s.obj (Fin.last 2))).i (hf j hj)
    rw [map_natCast, map_zero] at this
    exact this
  · have h1 : (CH.Mor.restrict (pdS _ c' 1).fn G).pull 2 (mm.pull 2 y) =
        m4.pull 2 ((CH.Mor.restrict (pdS _ c 1).fn G').pull 2 y) := by
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rfl
    refine Eq.trans ?_ h1.symm
    rw [← hcl]
    rfl

end CrystallineSemistableComparison.HT.constant_weight_sum_bound
