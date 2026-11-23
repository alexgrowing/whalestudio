import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCrystallineLiftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineCocycleClosed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueChernClassNilpotentBase
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernClassReductionCompatible
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.ReductionFirstChern

open GlobalTheory.CompanionTheory.CocCls

section Ring

variable {S S' : Type} [CommRing S] [CommRing S'] {J : Ideal S} {J' : Ideal S'}

theorem dpow_mem_pdP (δ : DividedPowers J) {x : S} (hx : x ∈ J) {k r : ℕ} (h : r ≤ k) : δ.dpow k x ∈ pdP δ r :=
  Ideal.subset_span ⟨[(k, x)], by simpa using hx, by simpa using h, by simp⟩

theorem dlog_trunc (δ : DividedPowers J) {s N : ℕ} (hs : pdP δ s = ⊥) (h : s ≤ N) {v : S} (hv : v - 1 ∈ J) :
    B.dlog δ N v = B.dlog δ s v := by
  unfold B.dlog
  refine (Finset.sum_subset (Finset.range_mono h) fun k _ hk => ?_).symm
  have h1 : δ.dpow (k + 1) (v - 1) ∈ pdP δ s := dpow_mem_pdP δ hv (by
    have : s ≤ k := by simpa using hk
    omega)
  rw [hs, Ideal.mem_bot] at h1
  rw [h1, mul_zero]

theorem dlog_red {δ : DividedPowers J} {δ' : DividedPowers J'} {f : S →+* S'} (hf : IsDPMorphism δ δ' f) {s N : ℕ}
    (hs : pdP δ s = ⊥) (hN : ∀ k, N ≤ k → (k.factorial : S') = 0) {v : S} (hv : v - 1 ∈ J) :
    f (B.dlog δ s v) = B.dlog δ' N (f v) := by
  rw [← dlog_trunc δ hs (le_max_left s N) hv, dlog_map hf _ hv]
  exact GlobalTheory.CompanionTheory.FirstChernClassFactorial.dlog_eq_of_factorial δ' (le_max_right s N) hN _

theorem factorial_quot {l : ℕ} (hl : l ≠ 0) (n k : ℕ) (hk : l * n ≤ k) :
    (k.factorial : S ⧸ Ideal.span {(l : S) ^ n}) = 0 := by
  obtain ⟨a, ha⟩ := (GlobalTheory.CompanionTheory.FirstChernClassFactorial.pow_dvd_factorial_mul l (Nat.pos_of_ne_zero hl) n).trans (Nat.factorial_dvd_factorial hk)
  rw [ha, ← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : S) ^ n})), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_mul, Nat.cast_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end Ring

section Lift

variable {O A R : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R]
  {I : Ideal A} {γ : DividedPowers I} {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ}
  (d : RedIn δ κ γ l n) {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {s : ℕ} {𝒱 : Set X.Opens}
  {C : Type 1} [Category.{0} C] (g : C ⥤ (TS γ q l s 𝒱).FullSubcategory) {D : E.LineData X}

def redLift (Lf : B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ (TS γ q l s 𝒱).ι) D) :
    B.CLift (q := q) (b := nlBase R J δ l) (ht := rfl) (κ := κ) (g ⋙ redG q s d 𝒱) D where
  p T := Spec.map (CommRingCat.ofHom (qBar (g.obj T).obj l n)) ≫ Lf.p T
  hp T := by
    rw [Category.assoc, Lf.hp]
    rfl
  w {T T'} φ := Units.map (Ideal.Quotient.mk (lnT (g.obj T').obj l n)).toMonoidHom (Lf.w φ)
  hw {T T'} φ h := by
    have e : B.thSp (q := q) (b := nlBase R J δ l) (ht := rfl) (κ := κ) ((g ⋙ redG q s d 𝒱).map φ) ≫ Spec.map (CommRingCat.ofHom (qBar (g.obj T).obj l n)) ≫ Lf.p T =
        Spec.map (CommRingCat.ofHom (qBar (g.obj T').obj l n)) ≫ (B.thSp (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) ((g ⋙ (TS γ q l s 𝒱).ι).map φ) ≫ Lf.p T) := by
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      unfold B.thSp
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))
    have h0 := hh Lf φ
    have h2 : (Spec.map (CommRingCat.ofHom (qBar (g.obj T').obj l n)) ≫ (B.thSp (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) ((g ⋙ (TS γ q l s 𝒱).ι).map φ) ≫ Lf.p T)) ≫ D.f =
        (Spec.map (CommRingCat.ofHom (qBar (g.obj T').obj l n)) ≫ Lf.p T') ≫ D.f := by
      rw [Category.assoc, h0, Category.assoc]
    have h3 := uq_map D (qBar (g.obj T').obj l n) _ _ h0 h2
    have h4 := uq_congr D e rfl h h2
    have h5 := Lf.hw φ h0
    change _ = (uq D _ _ h).val
    rw [h4, h3]
    change _ = qBar (g.obj T').obj l n (uq D _ _ h0).val
    refine Eq.trans ?_ (congrArg (qBar (g.obj T').obj l n) h5)
    rfl

theorem r_red (Lf : B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ (TS γ q l s 𝒱).ι) D)
    (σ : ComposableArrows C 2) :
    (B.CLift.r (redLift d g Lf) σ).val = Ideal.Quotient.mk (lnT (g.obj (σ.obj (Fin.last 2))).obj l n) (B.CLift.r Lf σ).val := by
  have h2 : B.CLift.r (redLift d g Lf) σ =
      Units.map (Ideal.Quotient.mk (lnT (g.obj (σ.obj (Fin.last 2))).obj l n)).toMonoidHom (B.CLift.r Lf σ) := by
    unfold B.CLift.r
    rw [map_mul, map_mul, map_inv]
    rfl
  rw [h2]
  rfl

theorem r_sub (Lf : B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ (TS γ q l s 𝒱).ι) D)
    (σ : ComposableArrows C 2) : (B.CLift.r Lf σ).val - 1 ∈ (g.obj (σ.obj (Fin.last 2))).obj.J := by
  have hfg : σ.map' 0 2 = σ.map' 0 1 ≫ σ.map' 1 2 := σ.map'_comp 0 1 2
  have h0 : B.CLift.r Lf σ = Rf Lf (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 1 ≫ σ.map' 1 2) := by
    rw [← hfg]
    rfl
  have h1 : red (σ.obj (Fin.last 2)) (g ⋙ (TS γ q l s 𝒱).ι) (B.CLift.r Lf σ) = 1 := by
    rw [h0]
    exact red_Rf Lf _ _
  exact sub_one_mem h1

theorem coc_red {Λ : Type} [CommRing Λ] (c : Λ →+* R)
    (Lf : B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ (TS γ q l s 𝒱).ι) D)
    (σ : ComposableArrows C 2) :
    B.CLift.coc (redLift d g Lf) c (l * n) σ =
      Ideal.Quotient.mk (lnT (g.obj (σ.obj (Fin.last 2))).obj l n) (B.CLift.coc Lf (RingHom.id A) s σ) := by
  have e1 := dlog_red (redδ_dp (g.obj (σ.obj (Fin.last 2))).obj (g.obj (σ.obj (Fin.last 2))).property.1 n) (s := s) (N := l * n)
    (g.obj (σ.obj (Fin.last 2))).property.1.1 (fun k hk => factorial_quot d.hl n k hk) (r_sub g Lf σ)
  exact (congrArg _ (r_red d g Lf σ)).trans e1.symm

end Lift

section Top

variable {b : Base} {L : b.Fun}

theorem idF_ext {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} {a a' : IdF A}
    (h : a.S = a'.S) : a = a' := by
  cases a
  cases a'
  cases h
  rfl

theorem stdI_top (Q : ObjectProperty (Thick L)) : stdI Q (some 0) 0 = IdF.top _ :=
  idF_ext (funext fun T => top_unique (le_trans (le_of_eq T.obj.pdPow_zero.symm) le_sup_left))

theorem bij_top {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) {a e : IdF (sP Q).A} {a' e' : IdF (sP Q').A}
    (ha : a = IdF.top _) (ha' : a' = IdF.top _) (h1 : (incl h).Le a a') (h2 : (incl h).Le e e') (j : ℕ)
    (H : Function.Bijective (((incl h).sq h1 h2).pull j)) :
    Function.Bijective (((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) h2).pull j) := by
  subst ha ha'
  exact H

end Top

theorem coefficientReduction_firstChernClass_tateTwist : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (c : Λ →+* R) (lam : Λ →+* A) (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))
    (D : E.LineData X), sSup (𝒱D D) = ⊤ → ∀ (x : CH.H (B.OM (nlFun δ l X q κ) c) 2) (z : HO (TS γ q l s {⊤}) 2),
    B.IsFirstChernClassOfLineBundle (q := q) (b := nlBase R J δ l) (ht := rfl) (κ := κ) D c (l * n) x → IsFirstChernThickening (TS γ q l s {⊤}) D s z →
    redM (TS γ q l s {⊤}) none ((l : A) ^ n) 2 z = (redMor q s d {⊤} c lam hc none).pull 2 x := by
  intro O A R Λ _ _ _ _ _ I γ J δ κ l n d X q s c lam hc D hD x z hx hz
  let Q := TS γ q l s {⊤}
  let Q' := TS γ q l s (𝒱D D)
  have h : Q' ≤ Q := fun T hT => ⟨hT.1, ⊤, rfl, GlobalTheory.CompanionTheory.CrystallineChernClass.inU_top T⟩
  let g : Q'.FullSubcategory ⥤ Q.FullSubcategory := ObjectProperty.ιOfLE h
  have hU : Used (TF l s : ObjectProperty (Thick (nlFun γ 0 X q (κA O I)))) := Or.inl ⟨rfl, l, s, rfl⟩
  have hinj := bij_top h (stdI_top Q) (stdI_top Q') _ (incl_std h none ((l : A) ^ n)) 2
    ((GlobalTheory.T.cech_refinement_cohomology_bijective (TF l s) hU (𝒱D D) {⊤} h (by rintro W rfl; rw [hD]) 2).2.1 (some 0) none 0 ((l : A) ^ n))
  obtain ⟨Lf⟩ := GlobalTheory.T.exists_crystalline_lift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ Q.ι) D (fun T =>
    GlobalTheory.CompanionTheory.CrystallineChernClass.st_le_lifts (γ := γ) (p := 0) (q := q) (κ := κA O I) D T.obj ⟨trivial, T.property.2⟩)
  obtain ⟨hz1, hcl1⟩ := hz Q'.FullSubcategory g (fun T => T.property.2) Lf
  let Lr := redLift d g Lf
  obtain ⟨hz2, hcl2⟩ := hx Q'.FullSubcategory (g ⋙ redG q s d {⊤}) Lr
  apply hinj.1
  let P := (incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h none ((l : A) ^ n))
  let M₁ := (toSq (IdF.top _) (stdI Q none ((l : A) ^ n)) fun _ => rfl).comp P
  let M₂ := (redMor q s d {⊤} c lam hc none).comp (σ'' := lam) P
  let m₁ : CH.Mor (g ⋙ CH.modF (sP Q).A) (sq (IdF.top (sP Q').A) (stdI Q' none ((l : A) ^ n))) (RingHom.id A) :=
    { G := 𝟭 _, τ := fun T => M₁.τ T, nat := fun φ x => M₁.nat φ x }
  let m₂ : CH.Mor ((g ⋙ redG q s d {⊤}) ⋙ B.OM (nlFun δ l X q κ) c) (sq (IdF.top (sP Q').A) (stdI Q' none ((l : A) ^ n))) lam :=
    { G := 𝟭 _, τ := fun T => M₂.τ T, nat := fun φ x => M₂.nat φ x }
  have hL : P.pull 2 (redM Q none ((l : A) ^ n) 2 z) = m₁.pull 2 ((CH.Mor.restrict (CH.modF (sP Q).A) g).pull 2 z) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rfl
  have hR : P.pull 2 ((redMor q s d {⊤} c lam hc none).pull 2 x) =
      m₂.pull 2 ((CH.Mor.restrict (B.OM (nlFun δ l X q κ) c) (g ⋙ redG q s d {⊤})).pull 2 x) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  have hE : m₁.pullC 2 (Lf.coc (RingHom.id A) s) = m₂.pullC 2 (Lr.coc c (l * n)) := by
    funext σ
    have e := coc_red d g c Lf σ
    have t : ∀ (T : Q'.FullSubcategory) (b : (g.obj T).obj.B), m₁.τ T b = m₂.τ T (Ideal.Quotient.mk (lnT (g.obj T).obj l n) b) :=
      fun _ _ => rfl
    exact (t _ _).trans (congrArg (m₂.τ _) e.symm)
  have hb1 : CH.d _ 2 (m₁.pullC 2 (Lf.coc (RingHom.id A) s)) = 0 :=
    (m₁.d_pullC 2 _).trans ((congrArg _ hz1).trans (map_zero _))
  have hb2 : CH.d _ 2 (m₂.pullC 2 (Lr.coc c (l * n))) = 0 :=
    (m₂.d_pullC 2 _).trans ((congrArg _ hz2).trans (map_zero _))
  have a1 := CrystallineSemistableComparison.P.mapH_cls m₁.hom 2 _ hz1 hb1
  have a2 := CrystallineSemistableComparison.P.mapH_cls m₂.hom 2 _ hz2 hb2
  have key : ∀ (w w' : CH.Cn (sq (IdF.top (sP Q').A) (stdI Q' none ((l : A) ^ n))) 2) (k : CH.d _ 2 w = 0) (k' : CH.d _ 2 w' = 0),
      w = w' → (CH.cx _).cls w k = (CH.cx _).cls w' k' := by
    rintro _ _ _ _ rfl
    rfl
  exact hL.trans ((congrArg (m₁.pull 2) hcl1.symm).trans (a1.trans ((key _ _ hb1 hb2 hE).trans
    (a2.symm.trans ((congrArg (m₂.pull 2) hcl2).trans hR.symm)))))

end GlobalTheory.CompanionTheory.ReductionFirstChern
