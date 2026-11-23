import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionPowerCalculusGeometricFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsFieldExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisedThetaTranslateConstantRigidifiedPullba

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.TabMap
open GlobalTheory.FrameGen GlobalTheory.ConstFam GlobalTheory.FrameMove GlobalTheory.OneBasis.Calc

theorem gs_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ q) z U a = (r.stalkMap z).hom (gs q (r z) U a) := by
  rw [← gs_pull r q z U h a, gs_eq r z _ h, gs_eq q (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r _ z h _).symm

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left} {T : Over S} {T' : Over S'} {h : T'.left ⟶ T.left}

theorem exists_ptHom (gp : IsGrpPullback A' A f φ) (hh : h ≫ T.hom = T'.hom ≫ f) :
    ∃ β : (T ⟶ A) →* (T' ⟶ A'), ∀ x, (β x).left ≫ φ = h ≫ x.left := by
  let u : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk h (by simpa using hh)
  let b : (T ⟶ A) → (T' ⟶ A') := fun x =>
    Over.homMk (gp.1.lift (h ≫ x.left) T'.hom (by rw [Category.assoc, Over.w, hh])) (gp.1.lift_snd _ _ _)
  have hb : ∀ x, (b x).left ≫ φ = h ≫ x.left := fun x => gp.1.lift_fst _ _ _
  have key : ∀ x y : T' ⟶ A', x.left ≫ φ = y.left ≫ φ → x = y := fun x y hxy => by
    ext1
    exact gp.1.hom_ext hxy ((Over.w x).trans (Over.w y).symm)
  refine ⟨MonoidHom.mk' b (fun x y => key _ _ ?_), hb⟩
  have hu : ∀ z : T ⟶ A, (u ≫ z).left = (b z).left ≫ φ := fun z => by
    rw [hb]
    rfl
  rw [← gp.2 T' (b x) (b y) (u ≫ x) (u ≫ y) (hu x) (hu y), hb, ← MonObj.comp_mul]
  rfl

omit [GrpObj A] in

theorem sval_all {L : LB A.left} {k : ℤ} {s : LB.Sec (LPow A L k T)} {q : T.left ⟶ (T ⊗ A).left} {p : T.left ⟶ A.left}
    {e : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => p) (fun _ => k))} {c : Γ(T.left, ⊤)}
    (H : ∀ z J, Good L z J → sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s q z J =
      gs (𝟙 _) z ⊤ c * (val e (𝟙 _) z J).val) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (r ≫ q) z J = gs r z ⊤ c * (val e r z J).val := by
  have hJ' : Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => by
    have := hJ (r ≫ ψ)
    simpa using this
  have H1 := H (r z) (fun ψ => J (r ≫ ψ)) hJ'
  rw [sval_of s q (r z) _ (fun _ => J (r ≫ q ≫ (snd T A).left)) (fun _ => rfl),
    val_of e (𝟙 _) (r z) _ (fun _ => J (r ≫ p)) (fun _ => by simp)] at H1
  have hm := hJ.mem (fun _ : Fin 1 => (snd T A).left) (r ≫ q)
  have hm' := hJ.mem (fun _ : Fin 1 => p) r
  rw [sval_of s (r ≫ q) z J (fun _ => J (r ≫ q ≫ (snd T A).left)) (fun _ => by simp),
    val_of e r z J (fun _ => J (r ≫ p)) (fun _ => rfl)]
  simp only [Category.assoc] at hm
  refine (gs_comp r q z _ hm _).trans ?_
  erw [H1]
  rw [map_mul]
  congr 1
  · have := gs_comp r (𝟙 _) z ⊤ trivial c
    simpa using this.symm
  · erw [← gs_unit r z _ hm', ← gs_unit (𝟙 _) (r z) _ (by simpa using hm')]
    have := gs_comp r (𝟙 _) z (L.wchart (fun _ => p) fun _ => J (r ≫ p)) hm' (e.s fun _ => J (r ≫ p)).val
    rw [Category.comp_id] at this
    exact this.symm
end

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {P : PolAV S} {P' : PolAV S'} {φ : P'.A.left ⟶ P.A.left}
  {w : LB.Iso P'.L (P.L.pull φ)} {T : Over S} {T' : Over S'} {h : T'.left ⟶ T.left}

theorem cmb_move (hφ : φ ≫ P.A.hom = P'.A.hom ≫ f) (hh : h ≫ T.hom = T'.hom ≫ f) {k n : ℕ}
    {b : Fin n → LB.Sec (LPow P.A P.L (k : ℤ) T)} {c : Fin n → Γ(T.left, ⊤)} {t : LB.Sec (LPow P.A P.L (k : ℤ) T)}
    {b' : Fin n → LB.Sec (LPow P'.A P'.L (k : ℤ) T')} {t' : LB.Sec (LPow P'.A P'.L (k : ℤ) T')}
    (H : ∀ j, t.f j = ∑ i, liftFun P.A _ (c i) * (b i).f j) (hb : ∀ i, Thru w k h (b i) (b' i)) (ht : Thru w k h t t') :
    ∀ j, t'.f j = ∑ i, liftFun P'.A _ (h.appTop.hom (c i)) * (b' i).f j := by
  have hl : Lin P.A P.L k (𝟙 T) b c t := by
    intro z J hJ
    have e := (cmb_iff P.isLB b c t).1 H _ (𝟙 _) z J hJ
    have hw : ((𝟙 T) ▷ P.A).left = 𝟙 _ := by simp
    rw [hw]
    refine e.trans (Finset.sum_congr rfl fun i _ => ?_)
    congr 1
    rw [Category.id_comp, gs_eq (fst T P.A).left z ⊤ trivial]
    rfl
  exact cmb_of_lin hφ P.isLB P'.isLB hh (h := 𝟙 T) (p := h) (by simp) hl hb ht

theorem frame_move {ρ ρ'} (R : RigPull P'.A P.A f φ w ρ' ρ) {x : T ⟶ P.A} {x' : T' ⟶ P'.A}
    (hx : x'.left ≫ φ = h ≫ x.left) {n : ℕ} {e} (H : IsTorsFrame P ρ n x e) :
    ∃ e', IsTorsFrame P' ρ' n x' e' ∧ ∀ (k : ℕ) (s : LB.Sec (LPow P.A P.L (k : ℤ) T))
      (s' : LB.Sec (LPow P'.A P'.L (k : ℤ) T')) (c : Γ(T.left, ⊤)), Thru w k h s s' →
      (∀ z J, Good P.L z J → sval (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => (k : ℤ)) s
        (ptSecT P.A x).left z J = gs (𝟙 _) z ⊤ c * (val (powFrame P.A P.L x e k) (𝟙 _) z J).val) →
      ∀ z J, Good P'.L z J → sval (φ := fun _ : Fin 1 => (snd T' P'.A).left) (ε := fun _ => (k : ℤ)) s'
        (ptSecT P'.A x').left z J = gs h z ⊤ c * (val (powFrame P'.A P'.L x' e' k) (𝟙 _) z J).val := by
  obtain ⟨gp, hw, -, hpm⟩ := R
  obtain ⟨e', he', hv⟩ := exists_gen_through (φ' := fun _ : Fin 1 => x'.left) (φ := fun _ : Fin 1 => x.left) (h := h)
    (ε := fun _ => 1) hw P.isLB P'.isLB (fun _ => hx) e H.2.1
  have ht : ∀ (z : T'.left) J J', Good P.L z J → Good P'.L z J' →
      val e h z J = wVal w z J J' x'.left * val e' (𝟙 _) z J' := by
    intro z J J' hJ hJ'
    have := hv _ (𝟙 _) z J J' hJ hJ'
    simpa using this
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S')).left) (z : Z) J J', Good P.L z J → Good P'.L z J' →
      rval ρ (r ≫ f) z J = wVal w z J J' (r ≫ eSec P'.A) * rval ρ' r z J' := by
    intro Z r z J J' hJ hJ'
    have := pmaps_val (fun _ => PolBaseChange.eSec_comm gp) hpm r hJ hJ'
    simpa using this
  refine ⟨e', isTorsFrame_move gp hw hr hx H he' ht, ?_⟩
  intro k s s' c hs hval z J' hJ'
  obtain ⟨J, hJ⟩ := exists_good' P.isLB z
  have pf : ∀ {S₀ : Scheme.{0}} {A₀ U : Over S₀} (y : U ⟶ A₀), (ptSecT A₀ y).left ≫ (fst U A₀).left = 𝟙 _ :=
    fun y => by rw [← Over.comp_left, ptSecT, lift_fst]; rfl
  have ps : ∀ {S₀ : Scheme.{0}} {A₀ U : Over S₀} (y : U ⟶ A₀), (ptSecT A₀ y).left ≫ (snd U A₀).left = y.left :=
    fun y => by rw [← Over.comp_left, ptSecT, lift_snd]
  have c1 : (h ≫ (ptSecT P.A x).left) ≫ (fst T P.A).left = (ptSecT P'.A x').left ≫ (fst T' P'.A).left ≫ h := by
    rw [Category.assoc, pf, ← Category.assoc, pf, Category.comp_id, Category.id_comp]
  have c2 : (h ≫ (ptSecT P.A x).left) ≫ (snd T P.A).left = (ptSecT P'.A x').left ≫ (snd T' P'.A).left ≫ φ := by
    rw [Category.assoc, ps, ← Category.assoc, ps, hx]
  have h1 := hs _ (ptSecT P'.A x').left (h ≫ (ptSecT P.A x).left) c1 c2 z J J' hJ hJ'
  have h2 := sval_all hval h z hJ
  rw [ps] at h1
  rw [h1, val_powFrame, ht z J J' hJ hJ'] at h2
  rw [val_powFrame]
  simp only [zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val] at h2 ⊢
  apply ((wVal w z J J' x'.left).isUnit.pow k).mul_left_cancel
  rw [h2]
  ring
end

theorem tab_map : LL → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing R'] [IsDomain R'] (gam : FractionRing R →+* FractionRing R') (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing R'))) (ψ : A'.A.left ⟶ A.A.left) (ω : LB.Iso A'.L (A.L.pull ψ)) ρ ρ', RigPull A'.A A.A (spMap gam) ψ ω ρ' ρ → ∀ (F F' : Type) [Field F] [Field F'] [IsAlgClosed F] [IsAlgClosed F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F'] (σ : F →+* F'), (∀ x, σ (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R') F' (gam x)) → ∀ (m r : ℕ) (th : SecA A F 1) (th' : SecA A' F' 1) (τ : Fin r → SecA A F (m ^ 2)) (τ' : Fin r → SecA A' F' (m ^ 2)), Thru ω 1 (T' := TFK (R := R') F') (T := TFK (R := R) F) (spMap σ) th th' → (∀ i, Thru ω (m ^ 2) (T' := TFK (R := R') F') (T := TFK (R := R) F) (spMap σ) (τ i) (τ' i)) → Tab.Map σ (tab ρ m th τ) (tab ρ' m th' τ') := by
  intro hLL R R' _ _ _ _ _ gam A A' ψ ω ρ ρ' hR F F' _ _ _ _ _ _ σ hσ m r th th' τ τ' hth hτ
  have gp := hR.1
  have hw := hR.2.1
  have hφ : ψ ≫ A.A.hom = A'.A.hom ≫ spMap gam := gp.1.w
  have hh : spMap σ ≫ (TFK (R := R) F).hom = (TFK (R := R') F').hom ≫ spMap gam := by
    show spMap σ ≫ spMap (algebraMap (FractionRing R) F) = spMap (algebraMap (FractionRing R') F') ≫ spMap gam
    rw [← spMap_comp, ← spMap_comp]
    congr 1
    exact RingHom.ext hσ
  obtain ⟨β, hβ⟩ := exists_ptHom (T := TFK (R := R) F) (T' := TFK (R := R') F') (h := spMap σ) gp hh
  have thru : ∀ (k : ℕ) (s : SecA A F k), ∃ s' : SecA A' F' k,
      Thru ω k (T' := TFK (R := R') F') (T := TFK (R := R) F) (spMap σ) s s' :=
    fun k s => (existsUnique_thru hφ hw A.isLB A'.isLB hh s).exists
  refine ⟨β, ?_, ?_, ?_, ?_⟩
  · intro k y₁ hk hy₁
    obtain ⟨y, rfl⟩ : ∃ y : TFK (R := R') F' ⟶ A'.A, y = y₁ := ⟨y₁, rfl⟩
    have hy : y ^ k = 1 := hy₁
    have hk0 : (k : F) ≠ 0 := by
      rw [← map_natCast (algebraMap (FractionRing R) F), ← map_natCast (algebraMap R (FractionRing R))]
      intro h0
      rw [map_eq_zero_iff _ (algebraMap (FractionRing R) F).injective,
        map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h0
      exact (Nat.cast_ne_zero.2 (by omega : k ≠ 0)) h0
    have hz : (y.left ≫ ψ) ≫ A.A.hom = spMap σ ≫ (TFK (R := R) F).hom := by
      rw [Category.assoc, hφ, ← Category.assoc, Over.w, hh]
    let zt : Over.mk (spMap σ ≫ (TFK (R := R) F).hom) ⟶ A.A := Over.homMk (y.left ≫ ψ) hz
    have hzy : y.left ≫ ψ = 𝟙 (TFK (R := R') F').left ≫ zt.left := by simp [zt]
    have hzk : zt ^ k = 1 := by
      have e1 := pow_comm gp hzy k
      have e0 := pow_comm gp hzy 0
      rw [hy] at e1
      simp only [pow_zero] at e0
      ext1
      have := e1.symm.trans e0
      erw [Category.id_comp, Category.id_comp] at this
      exact this
    obtain ⟨x, hxk, hxz⟩ := (GlobalTheory.torsion_points_field_extension hLL.1 _ A F F' σ (TFK (R := R) F).hom).2 k zt hk0 hzk
    refine ⟨x, hxk, ?_⟩
    apply Over.OverMorphism.ext
    apply gp.1.hom_ext
    · refine (hβ x).trans ?_
      have := congrArg CommaMorphism.left hxz
      simpa [zt] using this
    · exact (Over.w (β x)).trans (Over.w y).symm
  · rintro x a ⟨hx, t, c, hc, hcmb⟩
    obtain ⟨t', ht'⟩ := thru _ t
    refine ⟨(map_pow β x _).symm.trans ((congrArg β hx).trans (map_one β)), t', σ c,
      ThMove.thC_move R R' gam A A' ψ ω ρ ρ' hR F F' σ hσ m th th' x (β x) t t' c (hβ x) hth ht' hc, ?_⟩
    intro j
    rw [cmb_move hφ hh hcmb hτ ht' j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (spMap σ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i)) =
      (Scheme.ΓSpecIso (CommRingCat.of F')).inv.hom (σ (a i)) from appTop_fnR σ (a i)]
    rfl
  · rintro k x c ⟨hx, t, hc⟩
    obtain ⟨t', ht'⟩ := thru _ t
    exact ⟨(map_pow β x _).symm.trans ((congrArg β hx).trans (map_one β)), t',
      ThMove.thC_move R R' gam A A' ψ ω ρ ρ' hR F F' σ hσ k th th' x (β x) t t' c (hβ x) hth ht' hc⟩
  · rintro k x l ⟨e, he, hv⟩
    obtain ⟨e', he', hmv⟩ := frame_move hR (hβ x) he
    refine ⟨e', he', fun j z J' hJ' => ?_⟩
    have := hmv (m ^ 2) (τ j) (τ' j) (fnR (l j)) (hτ j) (hv j) z J' hJ'
    erw [gs_spMap] at this
    exact this

end GlobalTheory.OneBasis.TabMap
end
