import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationCriticalComparisonMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCohomologyOfFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormRestrictionCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormCoboundaryRelation
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.LocGrStep

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

theorem rep_sum {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ} {ι : Type} (S : Finset ι)
    (z : ι → ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))) (c : ι → CH.H (sq a b) j)
    (h : ∀ i ∈ S, Rep a b (z i) (c i)) : Rep a b (fun s => ∑ i ∈ S, z i s) (∑ i ∈ S, c i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using rep_zero (a := a) (b := b) (z := fun s => 0) (fun s => Ideal.zero_mem _)
  | insert i S hi ih =>
    have h1 := rep_add (h i (Finset.mem_insert_self i S)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
    rw [Finset.sum_insert hi]
    simpa only [Finset.sum_insert hi] using h1

theorem crit_shift (Q : Poly Φ) {Fil : ℤ → IdF Φ.A} {r : ℤ} (h : Q.Crit Fil (r + 1)) :
    Q.Crit (fun r => Fil (r + 1)) r := by
  intro T b
  refine (h T b).trans (forall_congr' fun k => ?_)
  have e : r + 1 - (k : ℤ) = r - k + 1 := by ring
  rw [e]

variable {d : ℕ}

abbrev Fl (Fil : ℤ → IdF Φ.A) (E : Frame Φ (d + 1)) : ℤ → IdF (Cut.Φ1 E).A := fun r => (Fil r).res (Cut.U E)

def rho (Q : Poly Φ) (Fil : ℤ → IdF Φ.A) {E : Frame Φ (d + 1)} (σ : ∀ T : C, E.D ⟶ T) (r : ℤ) (n : ℕ) :
    CH.H (gr (Fl Fil E) r) n →ₗ[R] CH.H (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r) n :=
  (CH.Mor.restrict (gr (Fl Fil E) r) (Cut.Pσ Q σ)).pull n

theorem rho_bij (Q : Poly Φ) (Fil : ℤ → IdF Φ.A) {E : Frame Φ (d + 1)} (σ : ∀ T : C, E.D ⟶ T) (r : ℤ) (n : ℕ) :
    Function.Bijective (rho Q Fil σ r n) :=
  CrystallineSemistableComparison.P.adj _ (Cut.Pσ Q σ) (Cut.U E) (Cut.adjPσ Q σ) n

def alpha (Q : Poly Φ) (Fil : ℤ → IdF Φ.A) {E : Frame Φ (d + 1)} (σ : ∀ T : C, E.D ⟶ T) (r : ℤ) :
    gr Fil r ⟶ Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r :=
  Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r)

example (Fil : ℤ → IdF Φ.A) (E : Frame Φ (d + 1)) (r : ℤ) : gr (Fl Fil E) r = Cut.U E ⋙ gr Fil r := rfl

universe w in
theorem cls_congr {K : Cx.{w} R} {n : ℕ} {x y : K.X n} (h : x = y) (hx : K.d n x = 0)
    (hy : K.d n y = 0) : K.cls x hx = K.cls y hy := by
  subst h; rfl

theorem pull_form (Q : Poly Φ) {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T)
    (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ) (hr : r = j + q) (I : Fin j → Fin d) (x : Φ.A.obj E.D)
    (hx : x ∈ (Fil q).S E.D) (a : CH.H (gr (Fl Fil E) r) j) (b : CH.H (gr Fil r) j)
    (ha : Rep (Fl Fil E r) (Fl Fil E (r + 1)) ((Cut.E1 E).form Cut.can I x) a)
    (hb : Rep (Fil r) (Fil (r + 1)) (E.form σ (Fin.succ ∘ I) x) b) :
    (CH.Mor.ofNatTrans (alpha Q Fil σ r)).pull j b = rho Q Fil σ r j a := by
  obtain ⟨f, hf, rfl, hv⟩ := ha
  obtain ⟨g, hg, rfl, hv'⟩ := hb
  have key := GlobalTheory.CompanionTheory.GrPull.gr_pull Q hF E σ hc j q r hr I x hx f g hv hv'
  exact (CrystallineSemistableComparison.P.mapH_cls _ j _ hg (CrystallineSemistableComparison.CechClassBoundaries.cyc _ _ hg)).trans
    ((cls_congr key.symm _ _).trans (CrystallineSemistableComparison.P.mapH_cls _ j _ hf (CrystallineSemistableComparison.CechClassBoundaries.cyc _ _ hf)).symm)

theorem coef {M : Type} [AddCommMonoid M] (u v : M) (n : ℕ) :
    (Finsupp.single 0 v : ℕ →₀ M) n = (Finsupp.single 0 u + Finsupp.single 1 v : ℕ →₀ M) (n + 1) := by
  cases n <;> simp [Finsupp.single_apply]

theorem val_ev (Q : Poly Φ) (T : C) (u f : Φ.A.obj T) :
    (Q.X T + (Φ.A.map (Q.j T)).hom u) * (Φ.A.map (Q.j T)).hom f =
      GlobalTheory.CompanionTheory.PolySes.ev Q T (Finsupp.single 0 (u * f) + Finsupp.single 1 f) := by
  rw [map_add, GlobalTheory.CompanionTheory.PolySes.ev_single, GlobalTheory.CompanionTheory.PolySes.ev_single, Φ.dp_zero (Q.X_mem T), Φ.dp_one (Q.X_mem T), map_mul]
  ring

theorem lift_form (Q : Poly Φ) {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T)
    {r : ℤ} (k q : ℕ) (hr : r = k + 1 + q) (I : Fin k → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D)
    (β : Cut.P0 Q ⋙ Cut.U E ⋙ gr Fil r ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ gr Fil (r - 1))
    (hform : ∀ (X : Pt E) (c c' : ℕ →₀ Φ.A.obj X.T) (z : sqM (Fil r) (Fil (r + 1)) (Q.P X.T))
      (z' : sqM (Fil (r - 1)) (Fil (r - 1 + 1)) (Q.P X.T)), (∀ k, c' k = c (k + 1)) →
      z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
      z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
      (β.app X).hom z = z')
    (g : CH.Cn (gr Fil (r - 1)) k)
    (hg : ∀ s, (show sqM _ _ _ from g s).1 = Ideal.Quotient.mk _ (E.form σ (Fin.succ ∘ I) x s)) :
    ∃ y : CH.Cn (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r) k,
      (∀ s, (show sqM _ _ _ from y s).1 = Ideal.Quotient.mk _
        ((Q.X (s.obj (Fin.last k)) + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.zero_le (Fin.last k)))))) *
          (Φ.A.map (Q.j _)).hom (E.form σ (Fin.succ ∘ I) x s))) ∧
      (CH.Mor.ofNatTrans (Functor.whiskerLeft (Pt.Sσ σ) β)).pullC k y =
        (CH.Mor.ofNatTrans (alpha Q Fil σ (r - 1))).pullC k g := by
  have hm : ∀ s : ComposableArrows C k, (Q.X (s.obj (Fin.last k)) + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.zero_le (Fin.last k)))))) *
      (Φ.A.map (Q.j _)).hom (E.form σ (Fin.succ ∘ I) x s) ∈ (Fil r).S (Q.P (s.obj (Fin.last k))) := by
    intro s
    have h1 := GlobalTheory.CompanionTheory.GrDelta.Bv_mem Q E σ hF s 0
    have h2 := (Fil _).map_mem (Q.j _) (GlobalTheory.CompanionTheory.FormMem.form_mem hF E σ k q (Fin.succ ∘ I) x hx s)
    have h3 := hF.mul 1 (k + q) _ h1 h2
    have e : ((1 + (k + q) : ℕ) : ℤ) = r := by rw [hr]; push_cast; ring
    rw [e] at h3
    exact h3
  refine ⟨fun s => sqMk (Fil r) (Fil (r + 1)) _ (hm s), fun s => rfl, funext fun s => ?_⟩
  refine hform ((Pt.Sσ σ).obj (s.obj (Fin.last k)))
    (Finsupp.single 0 (E.a σ 0 (s.map (homOfLE (Fin.zero_le (Fin.last k)))) * E.form σ (Fin.succ ∘ I) x s) +
      Finsupp.single 1 (E.form σ (Fin.succ ∘ I) x s))
    (Finsupp.single 0 (E.form σ (Fin.succ ∘ I) x s)) _ _ (fun n => coef _ _ n)
    (congrArg (Ideal.Quotient.mk _) (val_ev Q _ _ _)) ?_
  refine (GlobalTheory.CompanionTheory.PolySes.sqMap_val (Fil (r - 1)) (Fil (r - 1 + 1)) (Q.j (s.obj (Fin.last k))) (g s) _ (hg s)).trans ?_
  exact congrArg (Ideal.Quotient.mk _) (GlobalTheory.CompanionTheory.PolySes.ev_single_zero Q _).symm

theorem delta_form (Q : Poly Φ) {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T)
    (hc : E.GrConst Fil) {r : ℤ} (k q : ℕ) (hr : r = k + 1 + q) (I : Fin k → Fin d) (x : Φ.A.obj E.D)
    (hx : x ∈ (Fil q).S E.D)
    (β : Cut.P0 Q ⋙ Cut.U E ⋙ gr Fil r ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ gr Fil (r - 1))
    (hform : ∀ (X : Pt E) (c c' : ℕ →₀ Φ.A.obj X.T) (z : sqM (Fil r) (Fil (r + 1)) (Q.P X.T))
      (z' : sqM (Fil (r - 1)) (Fil (r - 1 + 1)) (Q.P X.T)), (∀ k, c' k = c (k + 1)) →
      z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
      z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
      (β.app X).hom z = z')
    (δ : ∀ n, (CH.cx (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil (r - 1))).H n →ₗ[R] (CH.cx (gr Fil r)).H (n + 1))
    (hδ : ∀ (n : ℕ) (y : (CH.cx (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r)).X n) (x : (CH.cx (gr Fil r)).X (n + 1))
      (hz : (CH.cx (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil (r - 1))).d n
        ((CH.Mor.ofNatTrans (Functor.whiskerLeft (Pt.Sσ σ) β)).hom.f n y) = 0)
      (hx : (CH.cx (gr Fil r)).d (n + 1) x = 0),
      (CH.Mor.ofNatTrans (alpha Q Fil σ r)).hom.f (n + 1) x = (CH.cx (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r)).d n y →
      δ n ((CH.cx (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil (r - 1))).cls
        ((CH.Mor.ofNatTrans (Functor.whiskerLeft (Pt.Sσ σ) β)).hom.f n y) hz) = (CH.cx (gr Fil r)).cls x hx)
    (a : CH.H (gr (Fl Fil E) (r - 1)) k) (w : CH.H (gr Fil r) (k + 1))
    (ha : Rep (Fl Fil E (r - 1)) (Fl Fil E (r - 1 + 1)) ((Cut.E1 E).form Cut.can I x) a)
    (hw : Rep (Fil r) (Fil (r + 1)) (E.form σ (Fin.cons 0 (Fin.succ ∘ I)) x) w) :
    δ k (rho Q Fil σ (r - 1) k a) = -w := by
  obtain ⟨f, hf, rfl, hv⟩ := ha
  obtain ⟨wc, hwc, rfl, hwv⟩ := hw
  have hr' : r - 1 = k + q := by rw [hr]; ring
  obtain ⟨c, g, hg, -, hgv⟩ := GlobalTheory.CompanionTheory.CocProd.rep_form hF E σ hc k q (r - 1) hr' (Fin.succ ∘ I) x hx
  have key := GlobalTheory.CompanionTheory.GrPull.gr_pull Q hF E σ hc k q (r - 1) hr' I x hx f g hv hgv
  obtain ⟨y, hy, hβ⟩ := lift_form Q hF E σ k q hr I x hx β hform g hgv
  have hd := GlobalTheory.CompanionTheory.GrDelta.gr_delta Q hF E σ hc k q r hr I x hx y wc hy hwv
  have hz : (CH.cx (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil (r - 1))).d k
      ((CH.Mor.ofNatTrans (Functor.whiskerLeft (Pt.Sσ σ) β)).hom.f k y) = 0 := by
    have e : (CH.Mor.ofNatTrans (Functor.whiskerLeft (Pt.Sσ σ) β)).hom.f k y =
        (CH.Mor.restrict (gr (Fl Fil E) (r - 1)) (Cut.Pσ Q σ)).hom.f k f := hβ.trans key.symm
    rw [e]
    exact CrystallineSemistableComparison.CechClassBoundaries.cyc _ _ hf
  have e1 : rho Q Fil σ (r - 1) k ((CH.cx _).cls f hf) = (CH.cx (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil (r - 1))).cls
      ((CH.Mor.ofNatTrans (Functor.whiskerLeft (Pt.Sσ σ) β)).hom.f k y) hz :=
    (CrystallineSemistableComparison.P.mapH_cls _ k _ hf (CrystallineSemistableComparison.CechClassBoundaries.cyc _ _ hf)).trans (cls_congr (key.trans hβ.symm) _ _)
  rw [e1]
  exact hδ k y (-wc) hz (by rw [map_neg, hwc, neg_zero]) (by rw [map_neg]; exact hd.symm)

structure Pack (Fil : ℤ → IdF Φ.A) (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T) (r : ℤ)
    (π : ∀ n, CH.H (gr Fil r) n →ₗ[R] CH.H (gr (Fl Fil E) r) n)
    (ε : ∀ n, CH.H (gr (Fl Fil E) (r - 1)) n →ₗ[R] CH.H (gr Fil r) (n + 1))
    (θ : ∀ n, CH.H (gr (Fl Fil E) r) n →ₗ[R] CH.H (gr (Fl Fil E) (r - 1)) n) : Prop where
  inj0 : Function.Injective (π 0)
  ex1 : ∀ n, Function.Exact (ε n) (π (n + 1))
  ex2 : ∀ n, Function.Exact (θ n) (ε n)
  ex3 : ∀ n b, θ n (π n b) = 0
  pull : ∀ (j q : ℕ), r = j + q → ∀ (I : Fin j → Fin d) (x : Φ.A.obj E.D), x ∈ (Fil q).S E.D →
    ∀ (a : CH.H (gr (Fl Fil E) r) j) (b : CH.H (gr Fil r) j),
      Rep (Fl Fil E r) (Fl Fil E (r + 1)) ((Cut.E1 E).form Cut.can I x) a →
      Rep (Fil r) (Fil (r + 1)) (E.form σ (Fin.succ ∘ I) x) b → π j b = a
  delta : ∀ (k q : ℕ), r = k + 1 + q → ∀ (I : Fin k → Fin d) (x : Φ.A.obj E.D), x ∈ (Fil q).S E.D →
    ∀ (a : CH.H (gr (Fl Fil E) (r - 1)) k) (w : CH.H (gr Fil r) (k + 1)),
      Rep (Fl Fil E (r - 1)) (Fl Fil E (r - 1 + 1)) ((Cut.E1 E).form Cut.can I x) a →
      Rep (Fil r) (Fil (r + 1)) (E.form σ (Fin.cons 0 (Fin.succ ∘ I)) x) w → ε k a = -w

theorem pack (Q : Poly Φ) {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T)
    (hc : E.GrConst Fil) (r : ℤ) (hQ : ∀ r' ≤ r + 1, Q.Crit Fil r') : ∃ π ε θ, Pack Fil E σ r π ε θ := by
  have c1 := hQ r (by omega)
  have c0 := hQ (r - 1) (by omega)
  have c2 := hQ (r + 1) le_rfl
  have c1' : Q.Crit Fil (r - 1 + 1) := by simpa using c1
  obtain ⟨β, hi, he, hs, hf⟩ := GlobalTheory.CompanionTheory.PolySes.ses Q E Fil (fun r => Fil (r + 1)) r
    (fun r' T => hF.anti (by omega) T) c1 c0 (crit_shift Q c2) (crit_shift Q c1')
  let βσ : Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r ⟶ Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil (r - 1) :=
    Functor.whiskerLeft (Pt.Sσ σ) β
  obtain ⟨s1, s2, s3⟩ := CrystallineSemistableComparison.P.ses_cochains (alpha Q Fil σ r) βσ (fun T => hi _) (fun T => he _) (fun T => hs _)
  obtain ⟨δ, hδ, h0, e1, e2, e3⟩ := CrystallineSemistableComparison.P.les _ _ s1 s2 s3
  let e := fun (r : ℤ) (n : ℕ) => LinearEquiv.ofBijective (rho Q Fil σ r n) (rho_bij Q Fil σ r n)
  let fH := fun n => (CH.Mor.ofNatTrans (alpha Q Fil σ r)).hom.mapH n
  let gH := fun n => (CH.Mor.ofNatTrans βσ).hom.mapH n
  refine ⟨fun n => (e r n).symm.toLinearMap ∘ₗ fH n, fun n => δ n ∘ₗ (e (r - 1) n).toLinearMap,
    fun n => (e (r - 1) n).symm.toLinearMap ∘ₗ gH n ∘ₗ (e r n).toLinearMap, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun a b h => h0 ((e r 0).symm.injective h)
  · intro n b
    constructor
    · intro h
      have h' : fH (n + 1) b = 0 := (e r (n + 1)).symm.map_eq_zero_iff.1 h
      obtain ⟨m, rfl⟩ := (e3 n b).1 h'
      refine ⟨(e (r - 1) n).symm m, ?_⟩
      change δ n (e (r - 1) n ((e (r - 1) n).symm m)) = _
      rw [LinearEquiv.apply_symm_apply]
    · rintro ⟨a, rfl⟩
      change (e r (n + 1)).symm (fH (n + 1) (δ n (e (r - 1) n a))) = 0
      rw [(e3 n _).2 ⟨_, rfl⟩, map_zero]
  · intro n a
    constructor
    · intro h
      obtain ⟨m, hm⟩ := (e2 n _).1 h
      refine ⟨(e r n).symm m, ?_⟩
      change (e (r - 1) n).symm (gH n (e r n ((e r n).symm m))) = a
      rw [LinearEquiv.apply_symm_apply]
      exact (LinearEquiv.symm_apply_eq _).2 hm
    · rintro ⟨b, rfl⟩
      change δ n (e (r - 1) n ((e (r - 1) n).symm (gH n (e r n b)))) = 0
      rw [LinearEquiv.apply_symm_apply]
      exact (e2 n _).2 ⟨_, rfl⟩
  · intro n b
    change (e (r - 1) n).symm (gH n (e r n ((e r n).symm (fH n b)))) = 0
    rw [LinearEquiv.apply_symm_apply, (e1 n _).2 ⟨b, rfl⟩, map_zero]
  · intro j q hr I x hx a b ha hb
    change (e r j).symm (fH j b) = a
    exact (LinearEquiv.symm_apply_eq _).2 (pull_form Q hF E σ hc j q r hr I x hx a b ha hb)
  · intro k q hr I x hx a w ha hw
    exact delta_form Q hF E σ hc k q hr I x hx β hf δ hδ a w ha hw

theorem ex_rep {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T)
    (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ) (hr : r = j + q) {ι : Type} [Fintype ι]
    (J : ι → Fin j → Fin d) (x : ι → Φ.A.obj E.D) (hx : ∀ i, x i ∈ (Fil q).S E.D) :
    ∃ c, Rep (Fil r) (Fil (r + 1)) (fun s => ∑ i, E.form σ (J i) (x i) s) c := by
  choose c hc' using fun i => GlobalTheory.CompanionTheory.CocProd.rep_form hF E σ hc j q r hr (J i) (x i) (hx i)
  exact ⟨_, rep_sum Finset.univ _ c fun i _ => hc' i⟩

section Sums

variable {Fil : ℤ → IdF Φ.A} {E : Frame Φ (d + 1)} {σ : ∀ T : C, E.D ⟶ T} {r : ℤ}
  {π : ∀ n, CH.H (gr Fil r) n →ₗ[R] CH.H (gr (Fl Fil E) r) n}
  {ε : ∀ n, CH.H (gr (Fl Fil E) (r - 1)) n →ₗ[R] CH.H (gr Fil r) (n + 1)}
  {θ : ∀ n, CH.H (gr (Fl Fil E) r) n →ₗ[R] CH.H (gr (Fl Fil E) (r - 1)) n}

theorem sum_pull (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (P : Pack Fil E σ r π ε θ) {j q : ℕ} (hr : r = j + q)
    (x : Idx j d → Φ.A.obj E.D) (hx : ∀ I, x I ∈ (Fil q).S E.D) (a : CH.H (gr (Fl Fil E) r) j) (b : CH.H (gr Fil r) j)
    (ha : Rep (Fl Fil E r) (Fl Fil E (r + 1)) (fun s => ∑ I : Idx j d, (Cut.E1 E).form Cut.can I.1 (x I) s) a)
    (hb : Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j d, E.form σ (Fin.succ ∘ I.1) (x I) s) b) : π j b = a := by
  have hF1 := Cut.isFil_1 (E := E) hF
  have hc1 := Cut.grConst_1 hc
  choose a' ha' using fun I : Idx j d => GlobalTheory.CompanionTheory.CocProd.rep_form hF1 (Cut.E1 E) Cut.can hc1 j q r hr I.1 (x I) (hx I)
  choose b' hb' using fun I : Idx j d => GlobalTheory.CompanionTheory.CocProd.rep_form hF E σ hc j q r hr (Fin.succ ∘ I.1) (x I) (hx I)
  have e1 : a = ∑ I, a' I := rep_unique ha (rep_sum Finset.univ _ a' fun I _ => ha' I)
  have e2 : b = ∑ I, b' I := rep_unique hb (rep_sum Finset.univ _ b' fun I _ => hb' I)
  rw [e1, e2, map_sum]
  exact Finset.sum_congr rfl fun I _ => P.pull j q hr I.1 (x I) (hx I) _ _ (ha' I) (hb' I)

theorem sum_delta (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (P : Pack Fil E σ r π ε θ) {k q : ℕ} (hr : r = k + 1 + q)
    (x : Idx k d → Φ.A.obj E.D) (hx : ∀ I, x I ∈ (Fil q).S E.D) (a : CH.H (gr (Fl Fil E) (r - 1)) k)
    (w : CH.H (gr Fil r) (k + 1))
    (ha : Rep (Fl Fil E (r - 1)) (Fl Fil E (r - 1 + 1)) (fun s => ∑ I : Idx k d, (Cut.E1 E).form Cut.can I.1 (x I) s) a)
    (hw : Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx k d, E.form σ (Fin.cons 0 (Fin.succ ∘ I.1)) (x I) s) w) :
    ε k a = -w := by
  have hF1 := Cut.isFil_1 (E := E) hF
  have hc1 := Cut.grConst_1 hc
  have hr' : r - 1 = k + q := by rw [hr]; ring
  have hr'' : r = ((k + 1 : ℕ) : ℤ) + q := by rw [hr]; push_cast; ring
  choose a' ha' using fun I : Idx k d =>
    GlobalTheory.CompanionTheory.CocProd.rep_form hF1 (Cut.E1 E) Cut.can hc1 k q (r - 1) hr' I.1 (x I) (hx I)
  choose w' hw' using fun I : Idx k d =>
    GlobalTheory.CompanionTheory.CocProd.rep_form hF E σ hc (k + 1) q r hr'' (Fin.cons 0 (Fin.succ ∘ I.1)) (x I) (hx I)
  have e1 : a = ∑ I, a' I := rep_unique ha (rep_sum Finset.univ _ a' fun I _ => ha' I)
  have e2 : w = ∑ I, w' I := rep_unique hw (rep_sum Finset.univ _ w' fun I _ => hw' I)
  rw [e1, e2, map_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun I _ => P.delta k q hr I.1 (x I) (hx I) _ _ (ha' I) (hw' I)

end Sums

section Index

variable {j k : ℕ}

def ia (I : Idx j d) : Idx j (d + 1) := ⟨Fin.succ ∘ I.1, (Fin.strictMono_succ).comp I.2⟩

def ib (I : Idx k d) : Idx (k + 1) (d + 1) := ⟨Fin.cons 0 (Fin.succ ∘ I.1), by
  intro a b hab
  induction a using Fin.cases with
  | zero =>
    induction b using Fin.cases with
    | zero => exact absurd hab (lt_irrefl _)
    | succ b => simpa using Fin.succ_pos _
  | succ a =>
    induction b using Fin.cases with
    | zero => exact absurd hab (Fin.not_lt_zero _)
    | succ b => simpa using I.2 (Fin.succ_lt_succ_iff.1 hab)⟩

theorem index_zero_extend_bijective : Function.Bijective (ia : Idx 0 d → Idx 0 (d + 1)) :=
  ⟨fun _ _ _ => Subtype.ext (funext fun i => i.elim0),
    fun J => ⟨⟨Fin.elim0, fun a => a.elim0⟩, Subtype.ext (funext fun i => i.elim0)⟩⟩

theorem split_bij : Function.Bijective (Sum.elim (ia (j := k + 1) (d := d)) (ib (k := k))) := by
  constructor
  · rintro (I | I) (I' | I') h
    · have h' : ia I = ia I' := h
      exact congrArg Sum.inl (Subtype.ext (funext fun i => Fin.succ_injective _ (congrFun (congrArg Subtype.val h') i)))
    · have h' : ia I = ib I' := h
      exact absurd (congrFun (congrArg Subtype.val h') 0) (by simp [ia, ib])
    · have h' : ib I = ia I' := h
      exact absurd (congrFun (congrArg Subtype.val h') 0) (by
        simp only [ia, ib, Function.comp, Fin.cons_zero]
        exact (Fin.succ_ne_zero _).symm)
    · have h' : ib I = ib I' := h
      refine congrArg Sum.inr (Subtype.ext (funext fun i => Fin.succ_injective _ ?_))
      simpa [ib] using congrFun (congrArg Subtype.val h') i.succ
  · intro J
    by_cases h : J.1 0 = 0
    · have hn : ∀ i : Fin k, J.1 i.succ ≠ 0 := fun i e => by
        have := J.2 (Fin.succ_pos i)
        rw [h, e] at this
        exact lt_irrefl _ this
      refine ⟨Sum.inr ⟨fun i => (J.1 i.succ).pred (hn i), fun a b hab => ?_⟩, ?_⟩
      · exact Fin.pred_lt_pred_iff.2 (J.2 (Fin.succ_lt_succ_iff.2 hab))
      · refine Subtype.ext (funext fun i => ?_)
        induction i using Fin.cases with
        | zero => simpa [ib] using h.symm
        | succ i => simp [ib]
    · have hn : ∀ i : Fin (k + 1), J.1 i ≠ 0 := fun i e => by
        have h1 := J.2.monotone (Fin.zero_le i)
        rw [e] at h1
        exact h (Fin.le_zero_iff.1 h1)
      refine ⟨Sum.inl ⟨fun i => (J.1 i).pred (hn i), fun a b hab => ?_⟩, ?_⟩
      · exact Fin.pred_lt_pred_iff.2 (J.2 hab)
      · exact Subtype.ext (funext fun i => by simp [ia])

theorem sum_split {M : Type*} [AddCommMonoid M] (f : Idx (k + 1) (d + 1) → M) :
    ∑ J, f J = ∑ I : Idx (k + 1) d, f (ia I) + ∑ I : Idx k d, f (ib I) :=
  (Fintype.sum_bijective _ split_bij _ _ fun _ => rfl).symm.trans (Fintype.sum_sum_type _)

theorem sum_zero {M : Type*} [AddCommMonoid M] (f : Idx 0 (d + 1) → M) : ∑ J, f J = ∑ I : Idx 0 d, f (ia I) :=
  (Fintype.sum_bijective _ index_zero_extend_bijective _ _ fun _ => rfl).symm

end Index

def LG {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Fil : ℤ → IdF Φ.A) {d : ℕ} (E : Frame Φ d)
    (σ : ∀ T : C, E.D ⟶ T) (r : ℤ) (j : ℕ) : Prop :=
  (r < j → Subsingleton (CH.H (gr Fil r) j)) ∧
    ∀ q : ℕ, r = j + q →
      (∀ c : CH.H (gr Fil r) j, ∃ x : Idx j d → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) ∧
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j d, E.form σ I.1 (x I) s) c) ∧
      ∀ x : Idx j d → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) →
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j d, E.form σ I.1 (x I) s) 0 → ∀ I, x I ∈ (Fil ((q : ℤ) + 1)).S E.D

section Step

variable {Fil : ℤ → IdF Φ.A} {E : Frame Φ (d + 1)} {σ : ∀ T : C, E.D ⟶ T} {r : ℤ}
  {π : ∀ n, CH.H (gr Fil r) n →ₗ[R] CH.H (gr (Fl Fil E) r) n}
  {ε : ∀ n, CH.H (gr (Fl Fil E) (r - 1)) n →ₗ[R] CH.H (gr Fil r) (n + 1)}
  {θ : ∀ n, CH.H (gr (Fl Fil E) r) n →ₗ[R] CH.H (gr (Fl Fil E) (r - 1)) n}

theorem van_step (hF : IsFil Φ Fil) (P : Pack Fil E σ r π ε θ)
    (h0 : ∀ j, LG (Fl Fil E) (Cut.E1 E) Cut.can r j) (h1 : ∀ j, LG (Fl Fil E) (Cut.E1 E) Cut.can (r - 1) j)
    (j : ℕ) (hr : r < j) : Subsingleton (CH.H (gr Fil r) j) := by
  cases j with
  | zero => exact GlobalTheory.CompanionTheory.LocGr.H_zero_subsingleton hF (by simpa using hr)
  | succ k =>
    have key : ∀ c : CH.H (gr Fil r) (k + 1), c = 0 := by
      intro c
      have s0 := (h0 (k + 1)).1 hr
      obtain ⟨m, rfl⟩ := (P.ex1 k c).1 (Subsingleton.elim _ _)
      have s1 := (h1 k).1 (by push_cast at hr; omega)
      rw [Subsingleton.elim m 0, map_zero]
    exact ⟨fun a b => by rw [key a, key b]⟩

theorem exA (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (P : Pack Fil E σ r π ε θ)
    (h0 : ∀ j, LG (Fl Fil E) (Cut.E1 E) Cut.can r j) {j q : ℕ} (hr : r = j + q) (c : CH.H (gr Fil r) j) :
    ∃ (x : Idx j d → Φ.A.obj E.D) (b : CH.H (gr Fil r) j), (∀ I, x I ∈ (Fil q).S E.D) ∧
      Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j d, E.form σ (Fin.succ ∘ I.1) (x I) s) b ∧ π j (c - b) = 0 := by
  obtain ⟨x, hx, hrep⟩ := ((h0 j).2 q hr).1 (π j c)
  obtain ⟨b, hb⟩ := ex_rep hF E σ hc j q r hr (fun I : Idx j d => Fin.succ ∘ I.1) x hx
  exact ⟨x, b, hx, hb, by rw [map_sub, sum_pull hF hc P hr x hx _ _ hrep hb, sub_self]⟩

theorem unA (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (P : Pack Fil E σ r π ε θ)
    (h0 : ∀ j, LG (Fl Fil E) (Cut.E1 E) Cut.can r j) {j q : ℕ} (hr : r = j + q)
    (x : Idx j d → Φ.A.obj E.D) (hx : ∀ I, x I ∈ (Fil q).S E.D) (b : CH.H (gr Fil r) j)
    (hb : Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j d, E.form σ (Fin.succ ∘ I.1) (x I) s) b)
    (hπ : π j b = 0) : (∀ I, x I ∈ (Fil ((q : ℤ) + 1)).S E.D) ∧ b = 0 := by
  obtain ⟨a, ha⟩ := ex_rep (Cut.isFil_1 (E := E) hF) (Cut.E1 E) Cut.can (Cut.grConst_1 hc) j q r hr
    (fun I : Idx j d => I.1) x hx
  have e := sum_pull hF hc P hr x hx a b ha hb
  rw [hπ] at e
  rw [← e] at ha
  have hx' := ((h0 j).2 q hr).2 x hx ha
  refine ⟨hx', rep_unique hb (rep_zero fun s => ?_)⟩
  refine Ideal.sum_mem _ fun I _ => ?_
  have h := GlobalTheory.CompanionTheory.FormMem.form_mem hF E σ j (q + 1) (Fin.succ ∘ I.1) (x I) (by push_cast; exact hx' I) s
  have e' : (((j + (q + 1) : ℕ)) : ℤ) = r + 1 := by rw [hr]; push_cast; ring
  rwa [e'] at h

theorem ex_step (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (P : Pack Fil E σ r π ε θ)
    (h0 : ∀ j, LG (Fl Fil E) (Cut.E1 E) Cut.can r j) (h1 : ∀ j, LG (Fl Fil E) (Cut.E1 E) Cut.can (r - 1) j)
    {k q : ℕ} (hr : r = k + 1 + q) (c : CH.H (gr Fil r) (k + 1)) :
    ∃ (xa : Idx (k + 1) d → Φ.A.obj E.D) (xb : Idx k d → Φ.A.obj E.D),
      (∀ I, xa I ∈ (Fil q).S E.D) ∧ (∀ I, xb I ∈ (Fil q).S E.D) ∧
      Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx (k + 1) d, E.form σ (Fin.succ ∘ I.1) (xa I) s +
        ∑ I : Idx k d, E.form σ (Fin.cons 0 (Fin.succ ∘ I.1)) (xb I) s) c := by
  have hr'' : r = ((k + 1 : ℕ) : ℤ) + q := by rw [hr]; push_cast; ring
  have hr' : r - 1 = k + q := by rw [hr]; ring
  obtain ⟨xa, b, hxa, hb, hz⟩ := exA hF hc P h0 hr'' c
  obtain ⟨m, hm⟩ := (P.ex1 k _).1 hz
  obtain ⟨xb, hxb, hrep⟩ := ((h1 k).2 q hr').1 (-m)
  obtain ⟨w, hw⟩ := ex_rep hF E σ hc (k + 1) q r hr'' (fun I : Idx k d => Fin.cons 0 (Fin.succ ∘ I.1)) xb hxb
  have e := sum_delta hF hc P hr xb hxb _ w hrep hw
  rw [map_neg, hm, neg_inj] at e
  have e' : c = b + w := by rw [← e]; abel
  exact ⟨xa, xb, hxa, hxb, e' ▸ rep_add hb hw⟩

theorem un_step (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (P : Pack Fil E σ r π ε θ)
    (h0 : ∀ j, LG (Fl Fil E) (Cut.E1 E) Cut.can r j) (h1 : ∀ j, LG (Fl Fil E) (Cut.E1 E) Cut.can (r - 1) j)
    {k q : ℕ} (hr : r = k + 1 + q) (xa : Idx (k + 1) d → Φ.A.obj E.D) (xb : Idx k d → Φ.A.obj E.D)
    (hxa : ∀ I, xa I ∈ (Fil q).S E.D) (hxb : ∀ I, xb I ∈ (Fil q).S E.D)
    (h : Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx (k + 1) d, E.form σ (Fin.succ ∘ I.1) (xa I) s +
      ∑ I : Idx k d, E.form σ (Fin.cons 0 (Fin.succ ∘ I.1)) (xb I) s) 0) :
    (∀ I, xa I ∈ (Fil ((q : ℤ) + 1)).S E.D) ∧ (∀ I, xb I ∈ (Fil ((q : ℤ) + 1)).S E.D) := by
  have hr'' : r = ((k + 1 : ℕ) : ℤ) + q := by rw [hr]; push_cast; ring
  have hr' : r - 1 = k + q := by rw [hr]; ring
  have hr3 : r = (k : ℤ) + ((q + 1 : ℕ) : ℤ) := by rw [hr]; push_cast; ring
  obtain ⟨b, hb⟩ := ex_rep hF E σ hc (k + 1) q r hr'' (fun I : Idx (k + 1) d => Fin.succ ∘ I.1) xa hxa
  obtain ⟨w, hw⟩ := ex_rep hF E σ hc (k + 1) q r hr'' (fun I : Idx k d => Fin.cons 0 (Fin.succ ∘ I.1)) xb hxb
  have hs : b + w = 0 := rep_unique (rep_add hb hw) h
  obtain ⟨a, ha⟩ := ex_rep (Cut.isFil_1 (E := E) hF) (Cut.E1 E) Cut.can (Cut.grConst_1 hc) k q (r - 1) hr'
    (fun I : Idx k d => I.1) xb hxb
  have e := sum_delta hF hc P hr xb hxb a w ha hw
  have eb : b = ε k a := by rw [e]; exact eq_neg_of_add_eq_zero_left hs
  have hπ : π (k + 1) b = 0 := (P.ex1 k b).2 ⟨a, eb.symm⟩
  obtain ⟨hxa', hb0⟩ := unA hF hc P h0 hr'' xa hxa b hb hπ
  refine ⟨hxa', ?_⟩
  have ea : ε k a = 0 := by rw [← eb, hb0]
  obtain ⟨a₂, rfl⟩ := (P.ex2 k a).1 ea
  obtain ⟨xc, hxc, hrep⟩ := ((h0 k).2 (q + 1) hr3).1 a₂
  obtain ⟨b₂, hb₂⟩ := ex_rep hF E σ hc k (q + 1) r hr3 (fun I : Idx k d => Fin.succ ∘ I.1) xc hxc
  have e2 := sum_pull hF hc P hr3 xc hxc _ _ hrep hb₂
  rw [← e2, P.ex3] at ha
  exact ((h1 k).2 q hr').2 xb hxb ha

end Step

theorem rep_eq {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : CH.H (sq a b) j}
    (h : Rep a b z c) (e : ∀ s, z s = z' s) : Rep a b z' c :=
  (funext e : z = z') ▸ h

theorem step (Q : Poly Φ) {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T)
    (hc : E.GrConst Fil) (r : ℤ) (hQ : ∀ r' ≤ r + 1, Q.Crit Fil r')
    (h0 : ∀ j, LG (Fl Fil E) (Cut.E1 E) Cut.can r j) (h1 : ∀ j, LG (Fl Fil E) (Cut.E1 E) Cut.can (r - 1) j) (j : ℕ) :
    LG Fil E σ r j := by
  obtain ⟨π, ε, θ, P⟩ := pack Q hF E σ hc r hQ
  refine ⟨van_step hF P h0 h1 j, fun q hq => ?_⟩
  cases j with
  | zero =>
    refine ⟨fun c => ?_, fun x hx h I => ?_⟩
    · obtain ⟨x, b, hx, hb, hz⟩ := exA hF hc P h0 hq c
      have e : c = b := sub_eq_zero.1 (P.inj0 (hz.trans (map_zero _).symm))
      let e0 : Idx 0 d ≃ Idx 0 (d + 1) := Equiv.ofBijective _ index_zero_extend_bijective
      refine ⟨fun J => x (e0.symm J), fun I => hx _, ?_⟩
      rw [e]
      refine rep_eq hb fun s => ?_
      rw [sum_zero]
      refine Finset.sum_congr rfl fun I _ => ?_
      have e1 : e0.symm (ia I) = I := e0.symm_apply_apply I
      change _ = E.form σ (Fin.succ ∘ I.1) (x (e0.symm (ia I))) s
      rw [e1]
    · obtain ⟨I, rfl⟩ := index_zero_extend_bijective.2 I
      exact (unA hF hc P h0 hq (fun I => x (ia I)) (fun I => hx _) 0
        (rep_eq h fun s => sum_zero _) (map_zero _)).1 I
  | succ k =>
    have hr : r = k + 1 + q := by rw [hq]; push_cast; ring
    refine ⟨fun c => ?_, fun x hx h J => ?_⟩
    · obtain ⟨xa, xb, hxa, hxb, hrep⟩ := ex_step hF hc P h0 h1 hr c
      let e0 : Idx (k + 1) d ⊕ Idx k d ≃ Idx (k + 1) (d + 1) := Equiv.ofBijective _ split_bij
      refine ⟨fun J => Sum.elim xa xb (e0.symm J), fun J => ?_, rep_eq hrep fun s => ?_⟩
      · change Sum.elim xa xb (e0.symm J) ∈ _
        rcases e0.symm J with I | I
        · exact hxa I
        · exact hxb I
      · rw [sum_split]
        refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun I _ => ?_) (Finset.sum_congr rfl fun I _ => ?_)
        · have e1 : e0.symm (ia I) = Sum.inl I := e0.symm_apply_apply (Sum.inl I)
          change _ = E.form σ (Fin.succ ∘ I.1) (Sum.elim xa xb (e0.symm (ia I))) s
          rw [e1]
          rfl
        · have e1 : e0.symm (ib I) = Sum.inr I := e0.symm_apply_apply (Sum.inr I)
          change _ = E.form σ (Fin.cons 0 (Fin.succ ∘ I.1)) (Sum.elim xa xb (e0.symm (ib I))) s
          rw [e1]
          rfl
    · obtain ⟨ha, hb⟩ := un_step hF hc P h0 h1 hr (fun I => x (ia I)) (fun I => x (ib I)) (fun I => hx _) (fun I => hx _)
        (rep_eq h fun s => sum_split _)
      obtain ⟨I | I, rfl⟩ := split_bij.2 J
      · exact ha I
      · exact hb I

theorem main (d : ℕ) : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ)
    {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (r : ℤ)
    (hQ : ∀ r' ≤ r + 1, Q.Crit Fil r') (j : ℕ), LG Fil E σ r j := by
  induction d with
  | zero =>
    intro R _ C _ Φ Q Fil hF E σ hc r hQ j
    exact GlobalTheory.CompanionTheory.LocGr.gr_zero hF E σ r j
  | succ d ih =>
    intro R _ C _ Φ Q Fil hF E σ hc r hQ j
    have hh : ∀ r' ≤ r, ∀ j, LG (Fl Fil E) (Cut.E1 E) Cut.can r' j := fun r' hr' j =>
      ih (Cut.Q1 Q) (Cut.isFil_1 hF) (Cut.E1 E) Cut.can (Cut.grConst_1 hc) r'
        (fun r'' h => Cut.criterion_truncation Q (hQ r'' (by omega))) j
    exact step Q hF E σ hc r hQ (hh r le_rfl) (hh (r - 1) (by omega)) j

theorem loc_gr : KH.LocGr := by
  intro R _ C _ Φ Q Fil hF d E σ hc r hQ j
  exact main d Q hF E σ hc r hQ j

end GlobalTheory.CompanionTheory.LocGrStep
