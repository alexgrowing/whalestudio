import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormLocalOfFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChart
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.FibGr

structure Pts {b : Base} (L : b.Fun) {Y : Scheme.{0}} (qY : Y ⟶ Spec (CommRingCat.of b.R)) where
  pt : ∀ T : Thick L, Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ Y
  nat : ∀ {T T' : Thick L} (φ : T ⟶ T'),
    pt T' = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T
  str : ∀ T : Thick L, pt T ≫ qY = Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk T.J).comp T.i))

section Fib

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (hI : I = ⊥)

def bar : R ⧸ I ≃+* R := (Ideal.quotEquivOfEq hI).trans (RingEquiv.quotientBot R)

def gk (κ : O →+* R ⧸ I) : O →+* R := (bar hI).toRingHom.comp κ

theorem mk_bar (x : R ⧸ I) : Ideal.Quotient.mk I (bar hI x) = x := by
  subst hI
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem mk_gk (κ : O →+* R ⧸ I) (a : O) : Ideal.Quotient.mk I (gk hI κ a) = κ a := mk_bar hI (κ a)

variable {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I)

abbrev XF : Scheme.{0} := pullback q (Spec.map (CommRingCat.ofHom (gk hI κ)))

abbrev jF : XF hI q κ ⟶ X := pullback.fst _ _

abbrev qF : XF hI q κ ⟶ Spec (CommRingCat.of R) := pullback.snd _ _

variable {q κ} {γ : DividedPowers I} {p : ℕ}

theorem pt_comp (T : Thick (nlFun γ p X q κ)) :
    pt T ≫ q = Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk T.J).comp T.i)) ≫
      Spec.map (CommRingCat.ofHom (gk hI κ)) := by
  have h := (show PtOver X q κ (T.B ⧸ T.J) from T.y).2
  refine h.trans ?_
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (RingHom.ext fun a => ?_)
  have hw := T.w (gk hI κ a)
  rw [mk_gk] at hw
  exact hw

theorem pt_nat {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') :
    pt T' = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T := by
  have := φ.pt
  unfold pt
  rw [← this]
  rfl

variable (γ p q κ) in

def fib : Pts (nlFun γ p X q κ) (qF hI q κ) where
  pt T := pullback.lift (pt T) (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk T.J).comp T.i))) (pt_comp hI T)
  nat {T T'} φ := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
      exact pt_nat φ
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      refine congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (RingHom.ext fun a => ?_)
      exact congrArg (Ideal.Quotient.mk T'.J) (φ.comm a).symm
  str T := pullback.lift_snd _ _ _

theorem fib_fst (T : Thick (nlFun γ p X q κ)) : (fib hI q κ γ p).pt T ≫ jF hI q κ = pt T := pullback.lift_fst _ _ _

end Fib

end GlobalTheory.CompanionTheory.FibGr
end

noncomputable section
namespace GlobalTheory.CompanionTheory.FibGr
open GlobalTheory.CompanionTheory.GrForm (wz wz_mem rep_add rep_neg sum_wz_sub rep_congr a_eq form_eq form_sub_mem)
open GlobalTheory.CompanionTheory.GrCech (mulMor mulT_congr mulMor_add mulMor_mul mulMor_smul res_res pull_mk)

variable {b : Base} {L : b.Fun} {Y : Scheme.{0}} {qY : Y ⟶ Spec (CommRingCat.of b.R)} (𝔭 : Pts L qY)

def InY (W : Y.Opens) (T : Thick L) : Prop := ⊤ ≤ 𝔭.pt T ⁻¹ᵁ W

def ev {W : Y.Opens} (T : Thick L) (h : InY 𝔭 W T) : Γ(Y, W) →+* T.B ⧸ T.J := GlobalTheory.Cris.evalAt (𝔭.pt T) W h

theorem ev_nat {W : Y.Opens} {T T' : Thick L} (φ : T ⟶ T') (h : InY 𝔭 W T) (h' : InY 𝔭 W T') (f : Γ(Y, W)) :
    ev 𝔭 T' h' f = Ideal.quotientMap T'.J φ.φ φ.hle (ev 𝔭 T h f) := by
  have key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ Y) (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ 𝔭.pt T)
      (hh : ⊤ ≤ y ⁻¹ᵁ W), GlobalTheory.Cris.evalAt y W hh f = Ideal.quotientMap T'.J φ.φ φ.hle (ev 𝔭 T h f) := by
    intro y hy hh
    subst hy
    exact evalAt_map (B := CommRingCat.of (T.B ⧸ T.J)) (B' := CommRingCat.of (T'.B ⧸ T'.J)) _ (𝔭.pt T) h hh f
  exact key _ (𝔭.nat φ) h'

theorem ev_res {W W' : Y.Opens} (hW : W' ≤ W) (T : Thick L) (h : InY 𝔭 W T) (h' : InY 𝔭 W' T) (f : Γ(Y, W)) :
    ev 𝔭 T h' (rs hW f) = ev 𝔭 T h f := evalAt_res (𝔭.pt T) hW h h' f

theorem ev_str {W : Y.Opens} (T : Thick L) (h : InY 𝔭 W T) (a : b.R) :
    ev 𝔭 T h (strV qY W a) = Ideal.Quotient.mk T.J (T.i a) :=
  evalAt_base qY (RingHom.id b.R) ((Ideal.Quotient.mk T.J).comp T.i) (𝔭.pt T) (by rw [RingHom.comp_id]; exact 𝔭.str T) h a

open Classical in

def lft (W : Y.Opens) (T : Thick L) (f : Γ(Y, W)) : T.B :=
  if h : InY 𝔭 W T then Function.surjInv Ideal.Quotient.mk_surjective (ev 𝔭 T h f) else 0

theorem lft_spec {W : Y.Opens} (T : Thick L) (h : InY 𝔭 W T) (f : Γ(Y, W)) :
    Ideal.Quotient.mk T.J (lft 𝔭 W T f) = ev 𝔭 T h f := by
  rw [lft, dif_pos h]
  exact Function.surjInv_eq _ _

def IsLift (W : Y.Opens) {d : ℕ} (t : Fin d → Γ(Y, W)) (u : Fin d → ∀ T : Thick L, T.B) : Prop :=
  ∀ i (T : Thick L) (h : InY 𝔭 W T), Ideal.Quotient.mk T.J (u i T) = ev 𝔭 T h (t i)

variable (L) in

abbrev GF (r : ℕ) : Thick L ⥤ ModuleCat.{0} b.R := sq (thFil L r) (thFil L ((r : ℤ) + 1))

def Rp {W : Y.Opens} (P : ObjectProperty (Thick L)) {d r : ℕ} (u : Fin d → ∀ T : Thick L, T.B)
    (x : Idx r d → Γ(Y, W)) (c : HU (GF L r) P r) : Prop :=
  CrystallineSemistableComparison.Pb.Rep (sFil P r) (sFil P ((r : ℤ) + 1)) (fun s => ∑ I : Idx r d,
    wz (Φ := sP P) (fun i T => u i T.obj) I.1 s *
      (show (sP P).A.obj (s.obj (Fin.last r)) from lft 𝔭 W (s.obj (Fin.last r)).obj (x I))) c

theorem lift_sub_mem {W : Y.Opens} {P : ObjectProperty (Thick L)} (hP : ∀ T, P T → InY 𝔭 W T) (f : Γ(Y, W))
    (v : ∀ T : Thick L, T.B) (hv : ∀ (T : Thick L) (h : InY 𝔭 W T), Ideal.Quotient.mk T.J (v T) = ev 𝔭 T h f)
    {T T' : P.FullSubcategory} (φ : T ⟶ T') :
    (show (sP P).A.obj T' from v T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from v T.obj) ∈ (sP P).J.S T' := by
  have h := hP _ T.property
  have h' := hP _ T'.property
  change v T'.obj - φ.hom.φ (v T.obj) ∈ T'.obj.J
  rw [← Ideal.Quotient.eq, hv _ h', ev_nat 𝔭 φ.hom h h' f, ← hv _ h]
  rfl

theorem exists_rp (W : Y.Opens) {d : ℕ} (t : Fin d → Γ(Y, W)) (u : Fin d → ∀ T : Thick L, T.B) (hu : IsLift 𝔭 W t u)
    (P : ObjectProperty (Thick L)) (hP : ∀ T, P T → InY 𝔭 W T) (r : ℕ) (x : Idx r d → Γ(Y, W)) :
    ∃ c, Rp 𝔭 (W := W) P u x c := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have hu' : ∀ i {T T' : P.FullSubcategory} (φ : T ⟶ T'),
      (show (sP P).A.obj T' from u i T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from u i T.obj) ∈ (sP P).J.S T' :=
    fun i _ _ φ => lift_sub_mem 𝔭 hP (t i) (u i) (hu i) φ
  have hy : ∀ (I : Idx r d) {T T' : P.FullSubcategory} (φ : T ⟶ T'),
      (show (sP P).A.obj T' from lft 𝔭 W T'.obj (x I)) -
        ((sP P).A.map φ).hom (show (sP P).A.obj T from lft 𝔭 W T.obj (x I)) ∈ (sP P).J.S T' :=
    fun I _ _ φ => lift_sub_mem 𝔭 hP (x I) (fun T => lft 𝔭 W T (x I)) (fun T h => lft_spec 𝔭 T h (x I)) φ
  choose f hf hz using fun I : Idx r d =>
    GlobalTheory.CompanionTheory.GrForm.stCocycle hF (fun i (T : P.FullSubcategory) => (show (sP P).A.obj T from u i T.obj)) hu'
      (fun T : P.FullSubcategory => (show (sP P).A.obj T from lft 𝔭 W T.obj (x I))) (hy I) I.1
  have hd : CH.d (sq (sFil P r) (sFil P ((r : ℤ) + 1))) r (∑ I, f I) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun I _ => hf I
  refine ⟨(CH.cx (sq (sFil P r) (sFil P ((r : ℤ) + 1)))).cls (∑ I, f I) hd, ∑ I, f I, hd, rfl, ?_⟩
  intro s
  have e : (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from (∑ I, f I) s) =
      ∑ I, (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from f I s) := Finset.sum_apply _ _ _
  rw [e, AddSubmonoidClass.coe_finset_sum, map_sum]
  exact Finset.sum_congr rfl fun I _ => hz I s

theorem lft_add_sub {W : Y.Opens} (T : Thick L) (h : InY 𝔭 W T) (f g : Γ(Y, W)) :
    lft 𝔭 W T (f + g) - (lft 𝔭 W T f + lft 𝔭 W T g) ∈ T.J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, lft_spec 𝔭 T h, lft_spec 𝔭 T h, lft_spec 𝔭 T h, map_add, sub_self]

theorem lft_neg_sub {W : Y.Opens} (T : Thick L) (h : InY 𝔭 W T) (f : Γ(Y, W)) :
    lft 𝔭 W T (-f) - (-lft 𝔭 W T f) ∈ T.J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_neg, lft_spec 𝔭 T h, lft_spec 𝔭 T h, map_neg, sub_self]

theorem lift_cocycle {W : Y.Opens} {d : ℕ} {t : Fin d → Γ(Y, W)} {u : Fin d → ∀ T : Thick L, T.B}
    (hu : IsLift 𝔭 W t u) (P : ObjectProperty (Thick L)) (hP : ∀ T, P T → InY 𝔭 W T) (i : Fin d)
    {T T' : P.FullSubcategory} (φ : T ⟶ T') :
    (show (sP P).A.obj T' from u i T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from u i T.obj) ∈ (sP P).J.S T' := by
  change u i T'.obj - φ.hom.φ (u i T.obj) ∈ T'.obj.J
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hu i _ (hP _ T'.property), ev_nat 𝔭 φ.hom (hP _ T.property) (hP _ T'.property),
    ← hu i _ (hP _ T.property)]
  exact sub_eq_zero.2 rfl

theorem rp_add (W : Y.Opens) {d : ℕ} (t : Fin d → Γ(Y, W)) (u : Fin d → ∀ T : Thick L, T.B) (hu : IsLift 𝔭 W t u)
    (P : ObjectProperty (Thick L)) (hP : ∀ T, P T → InY 𝔭 W T) (r : ℕ) (x x' : Idx r d → Γ(Y, W))
    (c c' : HU (GF L r) P r) (hc : Rp 𝔭 (W := W) P u x c) (hc' : Rp 𝔭 (W := W) P u x' c') :
    Rp 𝔭 (W := W) P u (x + x') (c + c') ∧ Rp 𝔭 (W := W) P u (-x) (-c) := by
  have hF : IsFil (sP P) (sFil P) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have hcoc := fun i {T T' : P.FullSubcategory} (φ : T ⟶ T') => lift_cocycle 𝔭 hu P hP i φ
  constructor
  · refine rep_add (fun s => ?_) hc hc'
    have := sum_wz_sub hF (fun i T => u i T.obj) hcoc (fun I : Idx r d => I.1) s
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft 𝔭 W (s.obj (Fin.last r)).obj ((x + x') I)))
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft 𝔭 W (s.obj (Fin.last r)).obj (x I)) +
        (show (sP P).A.obj (s.obj (Fin.last r)) from lft 𝔭 W (s.obj (Fin.last r)).obj (x' I)))
      (fun I => lft_add_sub 𝔭 _ (hP _ (s.obj (Fin.last r)).property) _ _)
    simpa only [mul_add, Finset.sum_add_distrib] using this
  · refine rep_neg (fun s => ?_) hc
    have := sum_wz_sub hF (fun i T => u i T.obj) hcoc (fun I : Idx r d => I.1) s
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft 𝔭 W (s.obj (Fin.last r)).obj ((-x) I)))
      (fun I => -(show (sP P).A.obj (s.obj (Fin.last r)) from lft 𝔭 W (s.obj (Fin.last r)).obj (x I)))
      (fun I => lft_neg_sub 𝔭 _ (hP _ (s.obj (Fin.last r)).property) _)
    simpa only [mul_neg, Finset.sum_neg_distrib] using this

theorem lift_cocycle_mem {W : Y.Opens} {d : ℕ} {t : Fin d → Γ(Y, W)} {u : Fin d → ∀ T : Thick L, T.B}
    (hu : IsLift 𝔭 W t u) {Q : ObjectProperty (Thick L)} (hQ : ∀ T, Q T → InY 𝔭 W T) (i : Fin d)
    {T T' : Q.FullSubcategory} (φ : T ⟶ T') :
    (show (sP Q).A.obj T' from u i T'.obj) - ((sP Q).A.map φ).hom (show (sP Q).A.obj T from u i T.obj) ∈ (sP Q).J.S T' := by
  have h := hQ _ T.property
  have h' := hQ _ T'.property
  change u i T'.obj - φ.hom.φ (u i T.obj) ∈ T'.obj.J
  refine Ideal.Quotient.eq.1 ?_
  rw [hu i T'.obj h', ev_nat 𝔭 φ.hom h h' (t i), ← hu i T.obj h]
  rfl

theorem lft_res_sub_mem {W W' : Y.Opens} (hW : W' ≤ W) (T : Thick L) (h : InY 𝔭 W T) (h' : InY 𝔭 W' T) (f : Γ(Y, W)) :
    lft 𝔭 W T f - lft 𝔭 W' T (rs hW f) ∈ T.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [lft_spec 𝔭 T h f, lft_spec 𝔭 T h' (rs hW f), ev_res 𝔭 hW T h h' f]

theorem rp_res (W W' : Y.Opens) (hW : W' ≤ W) {d : ℕ} (t : Fin d → Γ(Y, W)) (u : Fin d → ∀ T : Thick L, T.B) (hu : IsLift 𝔭 W t u)
    (P P' : ObjectProperty (Thick L)) (hPP : P' ≤ P) (hP : ∀ T, P T → InY 𝔭 W T) (hP' : ∀ T, P' T → InY 𝔭 W' T)
    (r : ℕ) (x : Idx r d → Γ(Y, W)) (c : HU (GF L r) P r) (hc : Rp 𝔭 (W := W) P u x c) :
    Rp 𝔭 (W := W') P' u (fun I => rs hW (x I)) ((resU (GF L r) hPP).pull r c) := by
  obtain ⟨f, hf, rfl, hz⟩ := hc
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P'
  have hP'W : ∀ T, P' T → InY 𝔭 W T := fun T h => hP T (hPP T h)
  refine ⟨(resU (GF L r) hPP).pullC r f, ?_, rfl, ?_⟩
  · have := (resU (GF L r) hPP).d_pullC r f
    refine this.trans ?_
    have hf' : CH.d (P.ι ⋙ GF L r) r f = 0 := hf
    rw [hf', map_zero]
  · intro s
    refine (hz (s ⋙ ObjectProperty.ιOfLE hPP)).trans ?_
    refine Ideal.Quotient.eq.2 ?_
    have hdiff : ∀ I : Idx r d,
        wz (Φ := sP P') (fun i T => u i T.obj) I.1 s *
          ((show (sP P').A.obj (s.obj (Fin.last r)) from lft 𝔭 W (s.obj (Fin.last r)).obj (x I)) -
            (show (sP P').A.obj (s.obj (Fin.last r)) from lft 𝔭 W' (s.obj (Fin.last r)).obj (rs hW (x I)))) ∈
          (sFil P' ((r : ℤ) + 1)).S (s.obj (Fin.last r)) := by
      intro I
      have hw := wz_mem hF (fun i T => u i T.obj)
        (fun i {T T'} φ => lift_cocycle_mem 𝔭 hu hP'W i φ) I.1 s
      have hδ : (show (sP P').A.obj (s.obj (Fin.last r)) from lft 𝔭 W (s.obj (Fin.last r)).obj (x I)) -
          (show (sP P').A.obj (s.obj (Fin.last r)) from lft 𝔭 W' (s.obj (Fin.last r)).obj (rs hW (x I))) ∈
          (sFil P' ((1 : ℕ) : ℤ)).S (s.obj (Fin.last r)) := by
        have e : (sFil P' ((1 : ℕ) : ℤ)).S (s.obj (Fin.last r)) = (sP P').J.S (s.obj (Fin.last r)) := hF.one _
        rw [e]
        exact lft_res_sub_mem 𝔭 hW _ (hP'W _ (s.obj (Fin.last r)).property) (hP' _ (s.obj (Fin.last r)).property) (x I)
      have := hF.mul r 1 _ hw hδ
      simpa using this
    have hsum := Ideal.sum_mem _ (t := Finset.univ) (fun I _ => hdiff I)
    simp only [mul_sub, Finset.sum_sub_distrib] at hsum
    exact hsum

end GlobalTheory.CompanionTheory.FibGr
end
