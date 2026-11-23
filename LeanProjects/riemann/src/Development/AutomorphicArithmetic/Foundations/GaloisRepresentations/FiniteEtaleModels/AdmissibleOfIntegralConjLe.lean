import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BaseOnto

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)

namespace UpperTheory.Gal.FiniteEtaleModels

theorem powMap_congr {X Y : Scheme.{0}} {A : Over X} {B : Over Y} {f f' : X ⟶ Y} {φ φ' : A.left ⟶ B.left} (h : f = f') (h' : φ = φ')
    (u : φ ≫ B.hom = A.hom ≫ f) (u' : φ' ≫ B.hom = A.hom ≫ f') (k : ℕ) : GlobalTheory.KS.powMap f φ u k = GlobalTheory.KS.powMap f' φ' u' k := by
  subst h h'; rfl

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {E : Type} [Field E] [NumberField E] {gb : GBase D.toG E}
  {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 𝔫 : Ideal (𝓞 D.F)} {S : Site gb w q r 𝔴 𝔫}

theorem Down.pw_ov (hP : PowCart) {N₁ N₂ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₁ 𝔟₁} {X₂ : Ext S N₂ 𝔟₂} (d : Down X₁ X₂) (k : ℕ) :
    d.pw k ≫ (GlobalTheory.KS.pow X₂.Y.univ.A k).hom ≫ X₂.Y.s = (GlobalTheory.KS.pow X₁.Y.univ.A k).hom ≫ X₁.Y.s := by
  have h := (hP _ _ _ X₁.Y.univ.A X₂.Y.univ.A X₂.Y.univ.A d.t (𝟙 _) d.Φ (𝟙 _) d.w (by simp) k).2.1
  rw [Down.pw, ← Category.assoc, h, Category.assoc, d.ov]

theorem exists_wit (hP : PowCart) {k : ℕ} (T : KS L gb k) (h : G.GAf) (M₁ M₂ : Lv p) (a b) :
    ∃ W : Wit T h M₁ M₂, ∀ {N₁ N₂ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₁ 𝔟₁} {X₂ : Ext S N₂ 𝔟₂} {c₁ c₂ : ℕ} {a₁ a₂ : 𝓞 D.F}
      (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (d : Down X₁ X₂), d.Extends W C₁ C₂ →
      X₁.site.pi T C₁ ≫ d.pw k = T.X.tr (T.lev M₁) (T.lev M₂) h a b ≫ X₂.site.pi T C₂ := by
  obtain ⟨π, o, ψ, φ, hw, hov, htr, he⟩ := T.tr_eq M₁ M₂ h a b
  refine ⟨⟨π, o, ψ, φ, hov, htr⟩, fun {_ _ _ _ X₁ X₂ _ _ _ _} C₁ C₂ d hd => ?_⟩
  have e1 := (hP _ _ _ (T.M M₁).univ.A X₁.Y.univ.A X₂.Y.univ.A C₁.j d.t C₁.m.φ d.Φ C₁.m.cart.1.w d.w k).2.2
    (by rw [Category.assoc, d.w, ← Category.assoc, C₁.m.cart.1.w, Category.assoc])
  have e2 := (hP _ _ _ (T.M M₁).univ.A (T.M M₂).univ.A X₂.Y.univ.A π C₂.j (ψ.left ≫ φ.φ) C₂.m.φ hw C₂.m.cart.1.w k).2.2
    (by rw [Category.assoc, C₂.m.cart.1.w, ← Category.assoc, hw, Category.assoc])
  have e3 : C₁.pw k ≫ d.pw k = GlobalTheory.KS.powMap π (ψ.left ≫ φ.φ) hw k ≫ C₂.pw k :=
    e1.trans ((powMap_congr hd.1 (hd.2.trans (Category.assoc _ _ _).symm) _ _ k).trans e2.symm)
  show ((T.e M₁).hom ≫ C₁.pw k) ≫ d.pw k = _ ≫ (T.e M₂).hom ≫ C₂.pw k
  rw [Category.assoc, e3, ← Category.assoc, ← he, Category.assoc]

def Ext.ps {N₁ : ℕ} {𝔟 : Ideal (𝓞 D.F)} (X : Ext S N₁ 𝔟) (k : ℕ) : (GlobalTheory.KS.pow X.Y.univ.A k).left ⟶ Spec (CommRingCat.of (Ow w)) :=
  (GlobalTheory.KS.pow X.Y.univ.A k).hom ≫ X.Y.s

def Ok {N₁ N₂ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₁ 𝔟₁} {X₂ : Ext S N₂ 𝔟₂} {k : ℕ} (T : KS L gb k) (h : G.GAf) {M₁ M₂ : Lv p}
    (π₁ : T.X.Z (T.lev M₁) ⟶ (GlobalTheory.KS.pow X₁.Y.univ.A k).left) (π₂ : T.X.Z (T.lev M₂) ⟶ (GlobalTheory.KS.pow X₂.Y.univ.A k).left)
    (t : (GlobalTheory.KS.pow X₁.Y.univ.A k).left ⟶ (GlobalTheory.KS.pow X₂.Y.univ.A k).left) : Prop :=
  t ≫ X₂.ps k = X₁.ps k ∧ ∀ a b, π₁ ≫ t = T.X.tr (T.lev M₁) (T.lev M₂) h a b ≫ π₂

theorem ok_of (hP : PowCart) {N₁ N₂ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₁ 𝔟₁} {X₂ : Ext S N₂ 𝔟₂} {k : ℕ} (T : KS L gb k) (h : G.GAf)
    {M₁ M₂ : Lv p} {c₁ c₂ : ℕ} {a₁ a₂ : 𝓞 D.F} (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂)
    (Q : Down X₁ X₂ → Prop) (ad : T.X.admitted (T.lev M₁) (T.lev M₂) h)
    (H : ∀ W : Wit T h M₁ M₂, ∃ d : Down X₁ X₂, d.Extends W C₁ C₂ ∧ Q d) :
    ∃ d : Down X₁ X₂, Ok T h (X₁.site.pi T C₁) (X₂.site.pi T C₂) (d.pw k) ∧ Q d := by
  obtain ⟨W, hW⟩ := exists_wit (S := S) hP T h M₁ M₂ ad.1 ad.2
  obtain ⟨d, hd, hq⟩ := H W
  exact ⟨d, ⟨d.pw_ov hP k, fun _ _ => hW C₁ C₂ d hd⟩, hq⟩

theorem Ok.comp {N₁ N₂ N₃ : ℕ} {𝔟₁ 𝔟₂ 𝔟₃ : Ideal (𝓞 D.F)} {X₁ : Ext S N₁ 𝔟₁} {X₂ : Ext S N₂ 𝔟₂} {X₃ : Ext S N₃ 𝔟₃} {k : ℕ} {T : KS L gb k}
    {h h' : G.GAf} {M₁ M₂ M₃ : Lv p} {π₁ : T.X.Z (T.lev M₁) ⟶ (GlobalTheory.KS.pow X₁.Y.univ.A k).left}
    {π₂ : T.X.Z (T.lev M₂) ⟶ (GlobalTheory.KS.pow X₂.Y.univ.A k).left} {π₃ : T.X.Z (T.lev M₃) ⟶ (GlobalTheory.KS.pow X₃.Y.univ.A k).left} {t t'}
    (H : Ok T h π₁ π₂ t) (H' : Ok T h' π₂ π₃ t') (ad : T.X.admitted (T.lev M₁) (T.lev M₂) h) (ad' : T.X.admitted (T.lev M₂) (T.lev M₃) h') :
    Ok T (h' * h) π₁ π₃ (t ≫ t') := by
  refine ⟨by rw [Category.assoc, H'.1, H.1], fun a b => ?_⟩
  rw [← Category.assoc, H.2 ad.1 ad.2, Category.assoc, H'.2 ad'.1 ad'.2, ← Category.assoc, T.X.tr_mul]

theorem admissible_of_integral_conj_le {k : ℕ} (T : KS L gb k) {h : G.GAf} {M₁ M₂ : Lv p} (hi : Integ L h) (ha : ∀ u ∈ L.KN M₁.1, h * u * h⁻¹ ∈ L.KN M₂.1) :
    T.X.admitted (T.lev M₁) (T.lev M₂) h :=
  ⟨(T.Δ_eq _).2 hi, fun u hu => by rw [T.K_eq] at hu ⊢; exact ha u hu⟩

theorem cls_of (hNum : NumEx) (hCls : ClsEx) {N₁ : ℕ} {𝔟 : Ideal (𝓞 D.F)} (X : Ext S N₁ 𝔟) {k : ℕ} (T : KS L gb k) (M : Lv p) (c : ℕ) (a : 𝓞 D.F)
    (hn : X.site.Num M.1 c a) : Nonempty (X.site.Cl (T.M M).univ c a) :=
  (hCls q (datAt S.atq S.sp) (Ow w) E S.b gb _ S.mat M.1 _ c a _ hn.1 (lt_of_lt_of_le (by norm_num) M.2.1) X.lev.1 X.lev.2.1 hn.2 X.Y _ _
    (T.M M).univ).1

theorem lev_le {N₀ κ : ℕ} {𝔞 𝔞' : Ideal (𝓞 D.F)} {K₀ K₁ : Subgroup G.GAf} (hK₀ : IsLev L (Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞) K₀)
    (hK₁ : IsLev L (Ideal.span {((N₀ * κ : ℕ) : 𝓞 D.F)} * 𝔞') K₁) (hle : 𝔞' ≤ 𝔞) : K₁ ≤ K₀ := fun u hu => by
  obtain ⟨u1, u2⟩ := (hK₁ u).1 hu
  refine (hK₀ u).2 ⟨u1, fun v hv => AddSubgroup.closure_mono ?_ (u2 v hv)⟩
  rintro z ⟨x, hx, y⟩
  refine ⟨x, Ideal.mul_mono ?_ hle hx, y⟩
  rw [Ideal.span_singleton_le_span_singleton, Nat.cast_mul]
  exact dvd_mul_right _ _

theorem forget_of (hSc : Sc D G) (hNum : NumEx) (hCls : ClsEx) (hInv : PiInv) (hP : PowCart) (hQ : QuotOf) (hF : StepF) (hD : DegGen) (hE : FEtExt)
    {k : ℕ} (T : KS L gb k) {N₀ κ : ℕ} {𝔞 𝔞' : Ideal (𝓞 D.F)} (X₁ : Ext S (N₀ * κ) 𝔞') (X₀ : Ext S N₀ 𝔞) (hle : 𝔞' ≤ 𝔞) {K₀ K₁ : Subgroup G.GAf}
    (hK₀ : IsLev L (Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞) K₀) (hK₁ : IsLev L (Ideal.span {((N₀ * κ : ℕ) : 𝓞 D.F)} * 𝔞') K₁) {M N : Lv p}
    (hd : N.1 ∣ M.1) {c₁ c₀ : ℕ} {a₁ a₀ : 𝓞 D.F} (n₁ : X₁.site.Num M.1 c₁ a₁) (n₀ : X₀.site.Num N.1 c₀ a₀)
    (C₁ : X₁.site.Cl (T.M M).univ c₁ a₁) (C₀ : X₀.site.Cl (T.M N).univ c₀ a₀) :
    ∃ s, Ok T 1 (X₁.site.pi T C₁) (X₀.site.pi T C₀) s ∧ IsQuot T.X (Ow w) K₀ (T.lev M) (X₀.ps k) (X₁.site.pi T C₁ ≫ s) ∧
      IsQuot T.X (Ow w) K₁ (T.lev M) (s ≫ X₀.ps k) (X₁.site.pi T C₁) ∧ FEt s (K₁.relIndex K₀) := by
  have ad : T.X.admitted (T.lev M) (T.lev N) 1 := admissible_of_integral_conj_le T (integ_of_mem (one_mem _)) fun u hu => by simpa using KN_anti hd hu
  obtain ⟨d, ok, fd, ed, pd⟩ := ok_of hP T 1 C₁ C₀ _ ad (hF p D G L hSc E gb w q r 𝔴 _ S k T N₀ κ 𝔞' 𝔞 X₁ X₀ hle M N c₁ c₀ a₁ a₀ n₁ n₀ hd C₁ C₀)
  obtain ⟨t, ht⟩ := hd
  have n₀' : X₀.site.Num M.1 (c₀ * t) (t * a₀) := by
    rw [ht]; exact (hNum p D E gb w q r 𝔴 _ X₀.site N.1 (lt_of_lt_of_le (by norm_num) N.2.1)).2 c₀ a₀ t n₀
  obtain ⟨C₀'⟩ := cls_of hNum hCls X₀ T M _ _ n₀'
  have pb := (hP _ _ _ X₁.Y.univ.A X₀.Y.univ.A X₀.Y.univ.A d.t (𝟙 _) d.Φ (𝟙 _) d.w (by simp) k).1 pd
  have fs : IsFinite (d.pw k) := MorphismProperty.of_isPullback pb.flip fd
  have ets : Etale (d.pw k) := MorphismProperty.of_isPullback pb.flip ed
  have e0 : X₁.site.pi T C₁ ≫ d.pw k = X₀.site.pi T C₀' :=
    (ok.2 ad.1 ad.2).trans (hInv p D G L E gb w q r 𝔴 _ X₀.site k T K₀ hK₀ M N t c₀ a₀ ht n₀ C₀' C₀ 1 (one_mem _) _ _)
  have q0 : IsQuot T.X (Ow w) K₀ (T.lev M) (X₀.ps k) (X₁.site.pi T C₁ ≫ d.pw k) :=
    e0.symm ▸ hQ p D G L hSc E gb w q r 𝔴 _ X₀.site k T K₀ hK₀ M _ _ n₀' C₀'
  have q1 : IsQuot T.X (Ow w) K₁ (T.lev M) (d.pw k ≫ X₀.ps k) (X₁.site.pi T C₁) := by
    rw [ok.1]
    exact hQ p D G L hSc E gb w q r 𝔴 _ X₁.site k T K₁ hK₁ M _ _ n₁ C₁
  have fl : Flat (X₀.ps k) := by
    obtain ⟨n, hn⟩ := X₀.dim k
    haveI : Smooth (X₀.ps k) := hn.smooth
    infer_instance
  exact ⟨d.pw k, ok, q0, q1, hE (Ow w) E _ _ _ _ _ fl fs ets (hD E _ T.X (Ow w) K₀ K₁ _ _ _ _ _ _ (lev_le hK₀ hK₁ hle) q0 q1)⟩

theorem transl_of (hSc : Sc D G) (hNum : NumEx) (hCls : ClsEx) (hP : PowCart) (hExt : ExtEx) (hA : StepA) (hB : StepB)
    {k : ℕ} (T : KS L gb k) {N₀ κ : ℕ} {𝔞 𝔞' : Ideal (𝓞 D.F)} (X₁ : Ext S (N₀ * κ) 𝔞') (X₀ : Ext S N₀ 𝔞) (hle : 𝔞' ≤ 𝔞) {M N N₁ : Lv p}
    {c₁ c₀ : ℕ} {a₁ a₀ : 𝓞 D.F} (n₁ : X₁.site.Num M.1 c₁ a₁) (n₀ : X₀.site.Num N.1 c₀ a₀)
    (C₁ : X₁.site.Cl (T.M M).univ c₁ a₁) (C₀ : X₀.site.Cl (T.M N).univ c₀ a₀) {h₁ h₂ : G.GAf} (i₁ : Integ L h₁) (i₂ : Integ L h₂)
    (hκ : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h₂ v' = κ • v) (hN₁ : ((N₁.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞')
    (ad₂ : ∀ u ∈ L.KN M.1, h₂ * u * h₂⁻¹ ∈ L.KN N₁.1) (ad₁ : ∀ u ∈ L.KN N₁.1, h₁ * u * h₁⁻¹ ∈ L.KN N.1)
    (hcase : h₁ = 1 ∨ ∃ (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal ∧ uId D q r ≤ 𝔴' ∧ 𝔞' ≤ 𝔞 * 𝔴' ∧ i ≤ D.n ∧
      Ideal.absNorm 𝔴' ^ i ∣ N₁.1 ∧ IsTjElt L q r 𝔴' i h₁) :
    ∃ t, Ok T (h₁ * h₂) (X₁.site.pi T C₁) (X₀.site.pi T C₀) t := by
  rcases hcase with h1 | ⟨𝔴', i, m', u', le', hi, dv, tj⟩
  · rw [h1] at ad₁
    rw [h1, _root_.one_mul]
    obtain ⟨d, ok, -⟩ := ok_of hP T h₂ C₁ C₀ (fun _ => True) (admissible_of_integral_conj_le T i₂ fun u hu => by simpa using ad₁ _ (ad₂ u hu)) fun W =>
      (hA p D G L hSc E gb w q r 𝔴 _ S k T N₀ κ 𝔞' 𝔞 X₁ X₀ hle _ i₂ hκ M N c₁ c₀ a₁ a₀ n₁ n₀ C₁ C₀ W).imp fun _ h => ⟨h, trivial⟩
    exact ⟨_, ok⟩
  · obtain ⟨X₂⟩ := hExt p D G hSc E gb w q r 𝔴 _ S N₀ 𝔞' ⟨X₀.lev.1, X₀.lev.2.1, X₀.lev.2.2.1, X₁.lev.2.2.2.1, X₁.lev.2.2.2.2⟩
    obtain ⟨c₂, a₂, n₂⟩ := (hNum p D E gb w q r 𝔴 _ X₂.site N₁.1 (lt_of_lt_of_le (by norm_num) N₁.2.1)).1 hN₁
    obtain ⟨C₂⟩ := cls_of hNum hCls X₂ T N₁ c₂ a₂ n₂
    obtain ⟨d₂, ok₂, -⟩ := ok_of hP T h₂ C₁ C₂ (fun _ => True) (admissible_of_integral_conj_le T i₂ ad₂) fun W =>
      (hA p D G L hSc E gb w q r 𝔴 _ S k T N₀ κ 𝔞' 𝔞' X₁ X₂ le_rfl _ i₂ hκ M N₁ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W).imp fun _ h => ⟨h, trivial⟩
    obtain ⟨d₁, ok₁, -⟩ := ok_of hP T h₁ C₂ C₀ (fun _ => True) (admissible_of_integral_conj_le T i₁ ad₁) fun W =>
      (hB p D G L hSc E gb w q r 𝔴 _ S k T N₀ 𝔞' 𝔞 X₂ X₀ 𝔴' i m' u' le' hi h₁ i₁ tj N₁ N c₂ c₀ a₂ a₀ n₂ n₀ dv C₂ C₀ W).imp fun _ h => ⟨h, trivial⟩
    exact ⟨_, ok₂.comp ok₁ (admissible_of_integral_conj_le T i₂ ad₂) (admissible_of_integral_conj_le T i₁ ad₁)⟩

end

theorem ksGood_of (hSite : SiteEx) (hNum : NumEx) (hCls : ClsEx) (hCov : KSCover) (hInv : PiInv) (hP : PowCart) (hExt : ExtEx)
    (hQ : QuotOf) (hA : StepA) (hB : StepB) (hF : StepF) (hD : DegGen) (hE : FEtExt) (hL : LiesAbs) : KSGood := by
  intro p _ D G L hSc E _ _ e gb hstd k T N J A _ g θ w 𝔴 hpl ⟨q, r, N₀, 𝔞, K₀, hat, hlev, hK₀, hNK, hNm, hdeck, hall⟩
  haveI : Fact q.Prime := ⟨hat.prime⟩
  obtain ⟨S⟩ := hSite p D G hSc E e gb hstd w q r 𝔴 _ hpl hat ⟨N₀, 𝔞, hlev.1, hlev.2.1, hlev.2.2.1, hlev.2.2.2.1, hlev.2.2.2.2, rfl⟩
  have pos : ∀ M : Lv p, 0 < M.1 := fun M => lt_of_lt_of_le (by norm_num) M.2.1
  obtain ⟨X₀⟩ := hExt p D G hSc E gb w q r 𝔴 _ S N₀ 𝔞 hlev
  obtain ⟨c₀, a₀, n₀⟩ := (hNum p D E gb w q r 𝔴 _ X₀.site N.1 (pos N)).1 hNm
  obtain ⟨C₀⟩ := cls_of hNum hCls X₀ T N c₀ a₀ n₀
  obtain ⟨Cv⟩ := hCov p D G L E gb w q r 𝔴 _ X₀.site k T K₀ hK₀ N c₀ a₀ n₀ C₀ hNK J A g θ hdeck
  refine ⟨Cv.toCover, fun j => ?_⟩
  obtain ⟨κ, 𝔞', K₁, h₁, h₂, N₁, hlev', hK₁, hle, -, hMm, hdec, hh, i₁, i₂, hκ, hN₁, ad₂, ad₁, hcase⟩ := hall j
  obtain ⟨X₁⟩ := hExt p D G hSc E gb w q r 𝔴 _ S (N₀ * κ) 𝔞' hlev'
  obtain ⟨c₁, a₁, n₁⟩ := (hNum p D E gb w q r 𝔴 _ X₁.site (g j).M.1 (pos _)).1 hMm
  obtain ⟨C₁⟩ := cls_of hNum hCls X₁ T (g j).M c₁ a₁ n₁
  obtain ⟨s, ok, q0, q1, fe⟩ := forget_of hSc hNum hCls hInv hP hQ hF hD hE T X₁ X₀ hle hK₀ hK₁ (g j).dvd n₁ n₀ C₁ C₀
  refine hL p D G L E gb k T N J A g θ (Ow w) Cv.toCover j K₀ K₁ _ (X₁.site.pi T C₁) s _ (lev_le hK₀ hK₁ hle) hNK q0 q1
    (fun a b => (ok.2 a b).symm) fe hdec fun x hx => ?_
  have x1 : x ∈ L.KN 1 := (g j).le_one hx
  have κx : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG (h₂ * x) v' = κ • v := fun v hv => by
    obtain ⟨v', hv', e'⟩ := hκ v hv
    refine ⟨L.actG x⁻¹ v', integ_of_mem (inv_mem x1) v' hv', ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right, e']
  obtain ⟨t, okt⟩ := transl_of hSc hNum hCls hP hExt hA hB T X₁ X₀ hle n₁ n₀ C₁ C₀ i₁ (i₂.mul (integ_of_mem x1)) κx hN₁ (ad₂ x hx) ad₁ hcase
  rw [← _root_.mul_assoc, ← hh] at okt
  exact ⟨t, okt.1.trans ok.1.symm, okt.2⟩

end UpperTheory.Gal.FiniteEtaleModels
