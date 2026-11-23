import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsUnivChartOfIsLieBasis
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalEvSecondPointOfXZero

noncomputable section

namespace GlobalTheory.ChartJet

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Points

variable {k : Type} [CommRing k] {d : ℕ}

variable (k d) in

def Q (n : ℕ) : AddSubgroup (Pt k n d) where
  carrier := {p | ∀ i, constantCoeff (p i) = 0}
  add_mem' := fun ha hb i => by rw [Pi.add_apply, map_add, ha i, hb i, add_zero]
  zero_mem' := fun _ => map_zero _
  neg_mem' := fun ha i => by rw [Pi.neg_apply, map_neg, ha i, neg_zero]

variable {n l : ℕ}

def gen (j : Fin n) : Q k d n := ⟨pt k d j, cc_pt j⟩

theorem czQ (b : Fin n → Q k d l) : CZ (fun j => (b j).1) := fun j i => (b j).2 i

def sb (b : Fin n → Q k d l) : PS k n d →+* PS k l d := evHom (czQ b)

theorem sb_apply (b : Fin n → Q k d l) (f : PS k n d) : sb b f = ev (fun j => (b j).1) f := evHom_apply (czQ b) f

def sq (b : Fin n → Q k d l) : Q k d n →+ Q k d l where
  toFun p := ⟨fun i => sb b (p.1 i), fun i =>
    (congrArg constantCoeff (sb_apply b _)).trans (constantCoeff_ev (czQ b) (p.2 i))⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)

@[simp] theorem sq_gen (b : Fin n → Q k d l) (j : Fin n) : sq b (gen j) = b j := by
  apply Subtype.ext
  funext i
  show sb b (pt k d j i) = (b j).1 i
  rw [sb_apply, pt_apply, ev_X (czQ b)]

def ac (A : Q k d 1) (u : Q k d n) : Q k d n := sq ![u] A

theorem ac_val (A : Q k d 1) (u : Q k d n) : (ac A u).1 = comp1 A.1 u.1 := by
  funext i
  show sb ![u] (A.1 i) = ev ![u.1] (A.1 i)
  rw [sb_apply]
  congr 1
  funext j
  fin_cases j
  rfl

def op (F : Q k d 2) (u v : Q k d n) : Q k d n := sq ![u, v] F

theorem op_val (F : Q k d 2) (u v : Q k d n) : (op F u v).1 = addOf F.1 u.1 v.1 := by
  funext i
  show sb ![u, v] (F.1 i) = ev ![u.1, v.1] (F.1 i)
  rw [sb_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

end Points

variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]

def pj (m : ℕ) (f : MvPowerSeries σ R) : JetR R σ m := Ideal.Quotient.mk _ (truncTotal (m + 1) f)

theorem pj_eq_mk {m : ℕ} {f : MvPowerSeries σ R} {q : MvPolynomial σ R} :
    pj m f = Ideal.Quotient.mk _ q ↔ ∀ e : σ →₀ ℕ, e.degree < m + 1 → coeff e f = q.coeff e := by
  unfold pj
  rw [Ideal.Quotient.eq]
  change _ ∈ MvPolynomial.idealOfVars σ R ^ (m + 1) ↔ _
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  refine forall_congr' fun e => imp_congr_right fun he => ?_
  rw [MvPolynomial.coeff_sub, MvPowerSeries.coeff_truncTotal _ he, sub_eq_zero]

theorem pj_coe (m : ℕ) (q : MvPolynomial σ R) : pj m (q : MvPowerSeries σ R) = Ideal.Quotient.mk _ q := by
  rw [pj_eq_mk]
  intro e _
  rw [MvPolynomial.coeff_coe]

theorem pj_X (m : ℕ) (s : σ) : pj m (X s : MvPowerSeries σ R) = zR m s := by
  rw [← MvPolynomial.coe_X, pj_coe]

theorem pj_trunc (m : ℕ) (f : MvPowerSeries σ R) : jetTruncR R σ m (pj (m + 1) f) = pj m f := by
  symm
  show pj m f = Ideal.Quotient.mk _ (truncTotal (m + 1 + 1) f)
  rw [pj_eq_mk]
  intro e he
  rw [MvPowerSeries.coeff_truncTotal _ (by omega)]

theorem aug_pj (m : ℕ) (f : MvPowerSeries σ R) : jetAug R σ m (pj m f) = constantCoeff f := by
  show (MvPolynomial.aeval fun _ => (0 : R)) (truncTotal (m + 1) f) = constantCoeff f
  simp [MvPowerSeries.constantCoeff_truncTotal_eq_ite]

theorem pj_ext {f g : MvPowerSeries σ R} (h : ∀ m, pj m f = pj m g) : f = g := by
  ext e
  have h1 := h e.degree
  have h2 : pj e.degree g = Ideal.Quotient.mk _ (truncTotal (e.degree + 1) g) := rfl
  rw [h2, pj_eq_mk] at h1
  rw [h1 e (Nat.lt_succ_self _), MvPowerSeries.coeff_truncTotal _ (Nat.lt_succ_self _)]

private theorem coeff_add_degree_eq_coeff_degree_of_stable (q : ℕ → MvPolynomial σ R)
    (hq : ∀ m, ∀ e : σ →₀ ℕ, e.degree < m + 1 → (q (m + 1)).coeff e = (q m).coeff e)
    (e : σ →₀ ℕ) : ∀ j, (q (e.degree + j)).coeff e = (q e.degree).coeff e := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih => rw [← ih, ← Nat.add_assoc, hq _ e (by omega)]

theorem exists_pj (z : ∀ m, JetR R σ m) (hz : ∀ m, jetTruncR R σ m (z (m + 1)) = z m) :
    ∃ f : MvPowerSeries σ R, ∀ m, pj m f = z m := by
  choose q hq using fun m => Ideal.Quotient.mk_surjective (z m)
  have hc : ∀ m, ∀ e : σ →₀ ℕ, e.degree < m + 1 → (q (m + 1)).coeff e = (q m).coeff e := by
    intro m e he
    have h := hz m
    rw [← hq (m + 1), ← hq m] at h
    have h' : (Ideal.Quotient.mk _ (q (m + 1)) : JetR R σ m) = Ideal.Quotient.mk _ (q m) := h
    rw [Ideal.Quotient.eq] at h'
    have := (MvPolynomial.mem_pow_idealOfVars_iff' _ _).1 h' e he
    rwa [MvPolynomial.coeff_sub, sub_eq_zero] at this
  refine ⟨(show MvPowerSeries σ R from fun e => (q e.degree).coeff e), fun m => ?_⟩
  rw [← hq m, pj_eq_mk]
  intro e he
  show (q e.degree).coeff e = (q m).coeff e
  obtain ⟨j, rfl⟩ : ∃ j, m = e.degree + j := ⟨m - e.degree, by omega⟩
  exact (coeff_add_degree_eq_coeff_degree_of_stable q hc e j).symm

def jS {κ : Type} (m : ℕ) (a : κ → MvPowerSeries τ R) (ha : ∀ s, constantCoeff (a s) = 0) : JetR R κ m →ₐ[R] JetR R τ m :=
  jetLift R (RingHom.ker (jetAug R τ m)) (ker_jetAug_pow τ m) (fun s => pj m (a s)) fun s => (aug_pj m _).trans (ha s)

theorem jS_zR {κ : Type} (m : ℕ) (a : κ → MvPowerSeries τ R) (ha) (s : κ) : jS m a ha (zR m s) = pj m (a s) := by
  show (MvPolynomial.aeval fun s => pj m (a s)) (MvPolynomial.X s) = pj m (a s)
  rw [MvPolynomial.aeval_X]

private theorem pj_add {κ : Type} [Finite κ] (m : ℕ) (g h : MvPowerSeries κ R) :
    pj m (g + h) = pj m g + pj m h := by
  simp only [pj, map_add]

private theorem pj_mul' {κ : Type} [Finite κ] (m : ℕ) (g h : MvPowerSeries κ R) :
    pj m (g * h) = pj m g * pj m h := by
  show pj m (g * h) = Ideal.Quotient.mk _ (truncTotal (m + 1) g) * Ideal.Quotient.mk _ (truncTotal (m + 1) h)
  rw [← map_mul, pj_eq_mk]
  intro x hx
  rw [MvPowerSeries.coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ hx]

private theorem pj_aeval (m : ℕ) (a : σ → MvPowerSeries τ R) (q : MvPolynomial σ R) :
    pj m (MvPolynomial.aeval a q) = MvPolynomial.aeval (fun s => pj m (a s)) q := by
  induction q using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]
    show pj m _ = Ideal.Quotient.mk _ (MvPolynomial.C r)
    rw [pj_eq_mk]
    intro e _
    classical
    rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, MvPolynomial.coeff_C]
    by_cases h : e = 0
    · subst h
      simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  | add p q hp hq => rw [map_add, map_add, pj_add, hp, hq]
  | mul_X p s hp => rw [map_mul, map_mul, pj_mul', hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X]

theorem jS_pj (m : ℕ) (a : σ → MvPowerSeries τ R) (ha) (f : MvPowerSeries σ R) : jS m a ha (pj m f) = pj m (subst a f) := by
  have ha' : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have h1 : pj m (subst a f) = pj m (subst a (truncTotal (m + 1) f : MvPowerSeries σ R)) := by
    show Ideal.Quotient.mk _ (truncTotal (m + 1) (subst a f)) =
      Ideal.Quotient.mk _ (truncTotal (m + 1) (subst a (truncTotal (m + 1) f : MvPowerSeries σ R)))
    rw [MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_sum ha' ha, ← MvPowerSeries.truncTotal_eq_sum]
  rw [h1, MvPowerSeries.subst_coe, pj_aeval]
  rfl

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) {n l : ℕ}

def jP (m : ℕ) (p : Q R d n) : JetR R (Fin d) m →ₐ[R] JetR R (Fin n × Fin d) m := jS m p.1 p.2

theorem jP_zR (m : ℕ) (p : Q R d n) (j : Fin d) : jP m p (zR m j) = pj m (p.1 j) := jS_zR m p.1 p.2 j

private theorem jet_spMap_square_comm {A B C : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [CommRing C] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  apply Over.OverMorphism.ext
  simp only [spMap, Over.comp_left, Over.homMk_left, ← Spec.map_comp]
  rfl

private theorem jetR_algHom_ext_of_eq_on_zR {κ A : Type} [CommRing A] [Algebra R A] {m : ℕ} (f g : JetR R κ m →ₐ[R] A)
    (h : ∀ j, f (zR m j) = g (zR m j)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h

def ptJ (m : ℕ) (p : Q R d n) : sp (R₀ := R) (JetR R (Fin n × Fin d) m) ⟶ G := spMap (jP m p) ≫ x m

def jQ (m : ℕ) (b : Fin n → Q R d l) : JetR R (Fin n × Fin d) m →ₐ[R] JetR R (Fin l × Fin d) m :=
  jS m (fun s => (b s.1).1 s.2) fun s => (b s.1).2 s.2

theorem ptJ_sq (m : ℕ) (b : Fin n → Q R d l) (p : Q R d n) : spMap (jQ m b) ≫ ptJ x m p = ptJ x m (sq b p) := by
  have e : (jQ m b).comp (jP m p) = jP m (sq b p) := by
    apply jetR_algHom_ext_of_eq_on_zR
    intro j
    show jQ m b (jP m p (zR m j)) = jP m (sq b p) (zR m j)
    rw [jP_zR, jP_zR]
    unfold jQ
    rw [jS_pj]
    show pj m (subst _ (p.1 j)) = pj m (sb b (p.1 j))
    rw [sb_apply]
    rfl
  unfold ptJ
  rw [← Category.assoc, ← jet_spMap_square_comm, e]

variable {x} (hx : IsUnivChart G d x)
include hx

theorem aug_jS (m : ℕ) (p : Q R d n) : (jetAug R _ m).comp (jP m p) = jetAug R (Fin d) m := by
  apply jetR_algHom_ext_of_eq_on_zR
  intro j
  show jetAug R _ m (jP m p (zR m j)) = jetAug R (Fin d) m (zR m j)
  rw [jP_zR, aug_pj, p.2 j]
  show (0 : R) = (MvPolynomial.aeval fun _ => (0 : R)) (MvPolynomial.X j)
  rw [MvPolynomial.aeval_X]

private theorem spMap_jetAug_comp_x_eq_one (m : ℕ) : spMap (jetAug R (Fin d) m) ≫ x m = 1 := by
  have e : (jetAug R (Fin d) 0).comp (jetZeroR R (Fin d) m) = jetAug R (Fin d) m := by
    apply jetR_algHom_ext_of_eq_on_zR
    intro j
    rfl
  rw [← e, jet_spMap_square_comm, Category.assoc, hx.2.1 m, MonObj.comp_one]

theorem ptJ_aug (m : ℕ) (p : Q R d n) : spMap (jetAug R _ m) ≫ ptJ x m p = 1 := by
  unfold ptJ
  rw [← Category.assoc, ← jet_spMap_square_comm, aug_jS hx]
  exact spMap_jetAug_comp_x_eq_one hx m

theorem ptJ_trunc (m : ℕ) (p : Q R d n) : spMap (jetTruncR R _ m) ≫ ptJ x (m + 1) p = ptJ x m p := by
  have e : (jetTruncR R (Fin n × Fin d) m).comp (jP (m + 1) p) = (jP m p).comp (jetTruncR R (Fin d) m) := by
    apply jetR_algHom_ext_of_eq_on_zR
    intro j
    show jetTruncR R _ m (jP (m + 1) p (zR (m + 1) j)) = jP m p (jetTruncR R (Fin d) m (zR (m + 1) j))
    rw [jP_zR, pj_trunc]
    show pj m (p.1 j) = jP m p (zR m j)
    rw [jP_zR]
  unfold ptJ
  rw [← Category.assoc, ← jet_spMap_square_comm, e, jet_spMap_square_comm, Category.assoc, hx.1 m]

theorem ptJ_inj {p q : Q R d n} (h : ∀ m, ptJ x m p = ptJ x m q) : p = q := by
  apply Subtype.ext
  funext j
  apply pj_ext
  intro m
  have hu := hx.2.2 (JetR R (Fin n × Fin d) m) (jetAug R _ m) m (ker_jetAug_pow _ m) (ptJ x m q) (ptJ_aug hx m q)
  have e : jP m p = jP m q := hu.unique ⟨aug_jS hx m p, (h m).symm⟩ ⟨aug_jS hx m q, rfl⟩
  rw [← jP_zR m p j, ← jP_zR m q j, e]

private theorem jetAug_comp_jetTruncR_eq_jetAug_succ (κ : Type) (m : ℕ) :
    (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1) := by
  apply jetR_algHom_ext_of_eq_on_zR
  intro j
  rfl

theorem exists_ptJ (y : ∀ m, sp (R₀ := R) (JetR R (Fin n × Fin d) m) ⟶ G) (h₀ : ∀ m, spMap (jetAug R _ m) ≫ y m = 1)
    (h₁ : ∀ m, spMap (jetTruncR R _ m) ≫ y (m + 1) = y m) : ∃ p : Q R d n, ∀ m, ptJ x m p = y m := by
  choose ψ hψ hu using fun m =>
    hx.2.2 (JetR R (Fin n × Fin d) m) (jetAug R _ m) m (ker_jetAug_pow _ m) (y m) (h₀ m)
  have hc : ∀ m, (jetTruncR R (Fin n × Fin d) m).comp (ψ (m + 1)) = (ψ m).comp (jetTruncR R (Fin d) m) := by
    intro m
    have hk : RingHom.ker (jetAug R (Fin n × Fin d) m) ^ (m + 1 + 1) = ⊥ :=
      le_bot_iff.mp ((Ideal.pow_le_pow_right (by omega)).trans (ker_jetAug_pow _ m).le)
    refine (hx.2.2 (JetR R (Fin n × Fin d) m) (jetAug R _ m) (m + 1) hk (y m) (h₀ m)).unique
      ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · rw [← AlgHom.comp_assoc, jetAug_comp_jetTruncR_eq_jetAug_succ hx, (hψ (m + 1)).1]
    · rw [jet_spMap_square_comm, Category.assoc, ← (hψ (m + 1)).2, h₁]
    · rw [← AlgHom.comp_assoc, (hψ m).1, jetAug_comp_jetTruncR_eq_jetAug_succ hx]
    · rw [jet_spMap_square_comm, Category.assoc, hx.1 m, (hψ m).2]
  have hz : ∀ j m, jetTruncR R (Fin n × Fin d) m (ψ (m + 1) (zR (m + 1) j)) = ψ m (zR m j) := by
    intro j m
    exact congrArg (fun φ => φ (zR (m + 1) j)) (hc m)
  choose P hP using fun j => exists_pj (fun m => ψ m (zR m j)) (hz j)
  have hP0 : ∀ j, constantCoeff (P j) = 0 := by
    intro j
    rw [← aug_pj 0, hP j 0]
    show ((jetAug R _ 0).comp (ψ 0)) (zR 0 j) = 0
    rw [(hψ 0).1]
    show (MvPolynomial.aeval fun _ => (0 : R)) (MvPolynomial.X j) = 0
    rw [MvPolynomial.aeval_X]
  refine ⟨⟨P, hP0⟩, fun m => ?_⟩
  have e : jP m ⟨P, hP0⟩ = ψ m := by
    apply jetR_algHom_ext_of_eq_on_zR
    intro j
    rw [jP_zR]
    exact hP j m
  unfold ptJ
  rw [e, (hψ m).2]

theorem ptJ_zero (m : ℕ) : ptJ x m (0 : Q R d n) = 1 := by
  have e : jP m (0 : Q R d n) = (Algebra.ofId R _).comp (jetAug R (Fin d) m) := by
    apply jetR_algHom_ext_of_eq_on_zR
    intro j
    rw [jP_zR]
    show pj m 0 = algebraMap R _ ((MvPolynomial.aeval fun _ => (0 : R)) (MvPolynomial.X j))
    rw [MvPolynomial.aeval_X, map_zero]
    simp [pj]
  unfold ptJ
  rw [e, jet_spMap_square_comm, Category.assoc, spMap_jetAug_comp_x_eq_one hx m, MonObj.comp_one]

theorem exists_series [IsCommMonObj G] {O : Type} [CommRing O] (a : Geo.Tor.OAct O G) :
    ∃ (F : FGLaw R d) (A : OAct O F),
      (∀ m, ptJ x m (⟨F.F, F.const⟩ : Q R d 2) = ptJ x m (gen 0) * ptJ x m (gen 1)) ∧
      ∀ c m, ptJ x m (⟨A.act c, A.const c⟩ : Q R d 1) = ptJ x m (gen 0) ≫ a.act c := by
  obtain ⟨F0, hF0⟩ : ∃ F0 : Q R d 2, ∀ m, ptJ x m F0 = ptJ x m (gen 0) * ptJ x m (gen 1) :=
    exists_ptJ hx (fun m => ptJ x m (gen 0) * ptJ x m (gen 1))
      (fun m => by rw [MonObj.comp_mul, ptJ_aug hx, ptJ_aug hx, _root_.one_mul])
      (fun m => by rw [MonObj.comp_mul, ptJ_trunc hx, ptJ_trunc hx])
  have hA : ∀ c : O, ∃ A0 : Q R d 1, ∀ m, ptJ x m A0 = ptJ x m (gen 0) ≫ a.act c := by
    intro c
    have := a.hom c
    exact exists_ptJ hx (fun m => ptJ x m (gen 0) ≫ a.act c)
      (fun m => by rw [← Category.assoc, ptJ_aug hx, MonObj.one_comp])
      (fun m => by rw [← Category.assoc, ptJ_trunc hx])
  choose A0 hA0 using hA
  have hop : ∀ {l : ℕ} (u v : Q R d l) (m : ℕ), ptJ x m (op F0 u v) = ptJ x m u * ptJ x m v := by
    intro l u v m
    show ptJ x m (sq ![u, v] F0) = _
    rw [← ptJ_sq x m ![u, v] F0, hF0, MonObj.comp_mul, ptJ_sq, ptJ_sq, sq_gen, sq_gen]
    rfl
  have hac : ∀ {l : ℕ} (u : Q R d l) (c : O) (m : ℕ), ptJ x m (ac (A0 c) u) = ptJ x m u ≫ a.act c := by
    intro l u c m
    show ptJ x m (sq ![u] (A0 c)) = _
    rw [← ptJ_sq x m ![u] (A0 c), hA0, ← Category.assoc, ptJ_sq, sq_gen]
    rfl
  refine ⟨⟨F0.1, F0.2, ?unit, ?comm, ?assoc⟩,
    ⟨fun c => (A0 c).1, fun c => (A0 c).2, ?hom, ?add, ?mul, ?one⟩, fun m => hF0 m, fun c m => hA0 c m⟩
  case unit =>
    intro i
    have E : op F0 (0 : Q R d 1) (gen 0) = (gen 0 : Q R d 1) :=
      ptJ_inj hx fun m => by rw [hop, ptJ_zero hx, _root_.one_mul]
    have h := congrFun (op_val F0 (0 : Q R d 1) (gen 0)) i
    rw [E] at h
    exact h.symm.trans (pt_apply _ _)
  case comm =>
    intro i
    have E : op F0 (gen 1 : Q R d 2) (gen 0) = F0 :=
      ptJ_inj hx fun m => by rw [hop, hF0, _root_.mul_comm]
    have h := congrFun (op_val F0 (gen 1 : Q R d 2) (gen 0)) i
    rw [E] at h
    exact h.symm
  case assoc =>
    intro i
    have E : op F0 (op F0 (gen 0 : Q R d 3) (gen 1)) (gen 2) = op F0 (gen 0) (op F0 (gen 1) (gen 2)) :=
      ptJ_inj hx fun m => by simp only [hop, _root_.mul_assoc]
    have h := congrArg (fun r : Q R d 3 => r.1 i) E
    simp only [op_val] at h
    exact h
  case hom =>
    intro c
    have := a.hom c
    have E : ac (A0 c) (op F0 (gen 0 : Q R d 2) (gen 1)) = op F0 (ac (A0 c) (gen 0)) (ac (A0 c) (gen 1)) :=
      ptJ_inj hx fun m => by simp only [hac, hop, MonObj.mul_comp]
    have h := congrArg Subtype.val E
    simp only [ac_val, op_val] at h
    exact h
  case add =>
    intro c₁ c₂
    have E : A0 (c₁ + c₂) = op F0 (A0 c₁) (A0 c₂) :=
      ptJ_inj hx fun m => by rw [hA0, hop, hA0, hA0, a.add, MonObj.comp_mul]
    have h := congrArg Subtype.val E
    rw [op_val] at h
    exact h
  case mul =>
    intro c₁ c₂
    have E : A0 (c₁ * c₂) = ac (A0 c₁) (A0 c₂) :=
      ptJ_inj hx fun m => by rw [hA0, hac, hA0, Category.assoc, ← a.mul c₂ c₁, _root_.mul_comm c₂ c₁]
    have h := congrArg Subtype.val E
    rw [ac_val] at h
    exact h
  case one =>
    have E : A0 1 = (gen 0 : Q R d 1) :=
      ptJ_inj hx fun m => by rw [hA0, a.one, Category.comp_id]
    exact congrArg Subtype.val E

private theorem prod_ofFn_eq_one_of_forall_eq_one {M : Type*} [Monoid M] (n : ℕ) :
    ∀ g : Fin n → M, (∀ j, g j = 1) → (List.ofFn g).prod = 1 := by
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro g h
    rw [List.ofFn_succ, List.prod_cons, h 0, _root_.one_mul]
    exact ih _ fun j => h _

private theorem prod_ofFn_eq_apply_of_forall_ne_eq_one {M : Type*} [Monoid M] (n : ℕ) :
    ∀ (f : Fin n → M) (i : Fin n), (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i := by
  induction n with
  | zero => intro f i; exact i.elim0
  | succ n ih =>
    intro f i h
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero =>
      rw [prod_ofFn_eq_one_of_forall_eq_one hx n _ fun j => h _ (Fin.succ_ne_zero j), _root_.mul_one]
    | succ i =>
      rw [h 0 (Fin.succ_ne_zero i).symm, _root_.one_mul]
      exact ih (fun j => f j.succ) i fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

theorem comb_single {v : Fin d → (Geo.Tor.epsR R ⟶ G)} (hv : ∀ j, v j = spMap (dualLift (Pi.single j 1)) ≫ x 1) (i : Fin d) :
    Geo.Tor.IsLieComb (Pi.single i 1) v (v i) := by
  have h1 : Geo.Tor.epsScaleR (1 : R) = RingHom.id (DualNumber R) :=
    RingHom.ext fun z => TrivSqZeroExt.ext (by simp [Geo.Tor.epsScaleR]) (by simp [Geo.Tor.epsScaleR])
  have h0 : Geo.Tor.epsScaleR (0 : R) =
      (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
    RingHom.ext fun z => TrivSqZeroExt.ext (by simp [Geo.Tor.epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])
      (by simp [Geo.Tor.epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])
  refine ⟨fun j => if j = i then v j else 1, fun j => ?_, ?_⟩
  · by_cases hj : j = i
    · subst hj
      simp only [if_true, Pi.single_eq_same, h1]
      show _ = Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ _
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    · show (if j = i then v j else 1).left = _
      have ht0 : Geo.Tor.IsTangent (v j) := by
        rw [hv j]
        exact (basis_of_chart hx).1 j
      have ht : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ (v j).left = η[G].left := ht0
      rw [if_neg hj, Pi.single_eq_of_ne hj, h0]
      show _ = Spec.map (CommRingCat.ofHom ((algebraMap R (DualNumber R)).comp
        (TrivSqZeroExt.fstHom R R R).toRingHom)) ≫ (v j).left
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ht]
      rfl
  · rw [prod_ofFn_eq_apply_of_forall_ne_eq_one hx d _ i fun j hj => if_neg hj]
    show v i = if i = i then v i else 1
    rw [if_pos rfl]

end GlobalTheory.ChartJet
