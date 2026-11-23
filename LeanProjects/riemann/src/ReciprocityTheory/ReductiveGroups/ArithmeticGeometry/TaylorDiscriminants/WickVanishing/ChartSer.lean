import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CanonB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Chart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.Canon
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]

def pj (m : ℕ) (f : MvPowerSeries σ R) : JetR R σ m := Ideal.Quotient.mk _ (truncTotal (m + 1) f)

theorem pj_eq_mk {m : ℕ} {f : MvPowerSeries σ R} {q : MvPolynomial σ R} :
    pj m f = Ideal.Quotient.mk _ q ↔ ∀ e : σ →₀ ℕ, e.degree < m + 1 → coeff e f = q.coeff e := by
  rw [pj, Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff']
  exact forall₂_congr fun e he => by rw [MvPolynomial.coeff_sub, coeff_truncTotal _ he, sub_eq_zero]

theorem pj_coe (m : ℕ) (q : MvPolynomial σ R) : pj m (q : MvPowerSeries σ R) = Ideal.Quotient.mk _ q :=
  pj_eq_mk.2 fun _ _ => MvPolynomial.coeff_coe _ _

theorem pj_X (m : ℕ) (s : σ) : pj m (X s : MvPowerSeries σ R) = zR m s := by rw [← MvPolynomial.coe_X, pj_coe]

theorem pj_trunc (m : ℕ) (f : MvPowerSeries σ R) : jetTruncR R σ m (pj (m + 1) f) = pj m f :=
  (pj_eq_mk.2 fun _ he => (coeff_truncTotal _ (Nat.lt_succ_of_lt he)).symm).symm

theorem aug_pj (m : ℕ) (f : MvPowerSeries σ R) : jetAug R σ m (pj m f) = constantCoeff f := by
  show MvPolynomial.aeval (fun _ : σ => (0 : R)) (truncTotal (m + 1) f) = _
  rw [MvPolynomial.aeval_zero', MvPolynomial.constantCoeff_eq, coeff_truncTotal _ (by simp)]; rfl

theorem pj_ext {f g : MvPowerSeries σ R} (h : ∀ m, pj m f = pj m g) : f = g := by
  ext e
  exact (pj_eq_mk.1 (h e.degree) e (Nat.lt_succ_self _)).trans (coeff_truncTotal _ (Nat.lt_succ_self _))

theorem exists_pj (z : ∀ m, JetR R σ m) (hz : ∀ m, jetTruncR R σ m (z (m + 1)) = z m) :
    ∃ f : MvPowerSeries σ R, ∀ m, pj m f = z m := by
  choose q hq using fun m => Ideal.Quotient.mk_surjective (z m)
  have step : ∀ m (e : σ →₀ ℕ), e.degree < m + 1 → (q (m + 1)).coeff e = (q m).coeff e := fun m e he => by
    have : Ideal.Quotient.mk _ (q (m + 1)) = Ideal.Quotient.mk _ (q m) := ((congrArg (jetTruncR R σ m) (hq _)).trans (hz m)).trans
      (hq m).symm
    rw [Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff'] at this
    exact sub_eq_zero.1 ((MvPolynomial.coeff_sub _ _ _ _).symm.trans (this e he))
  refine ⟨fun e => (q e.degree).coeff e, fun m => (pj_eq_mk.2 fun e he => ?_).trans (hq m)⟩
  show (q e.degree).coeff e = _
  induction m, Nat.le_of_lt_succ he using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [step k e (Nat.lt_succ_of_le hk), ih (Nat.lt_succ_of_le hk)]

def jS {κ : Type} (m : ℕ) (a : κ → MvPowerSeries τ R) (ha : ∀ s, constantCoeff (a s) = 0) : JetR R κ m →ₐ[R] JetR R τ m :=
  jetLift R (RingHom.ker (jetAug R τ m)) (ker_jetAug_pow τ m) (fun s => pj m (a s)) fun s => (aug_pj m _).trans (ha s)

theorem jS_zR {κ : Type} (m : ℕ) (a : κ → MvPowerSeries τ R) (ha) (s : κ) : jS m a ha (zR m s) = pj m (a s) :=
  jetLift_zR _ _ _ _ s

theorem jS_pj (m : ℕ) (a : σ → MvPowerSeries τ R) (ha) (f : MvPowerSeries σ R) : jS m a ha (pj m f) = pj m (subst a f) := by
  have e : ∀ p : MvPolynomial σ R, MvPolynomial.aeval (fun s => ((truncTotal (m + 1) (a s) : MvPolynomial τ R) :
      MvPowerSeries τ R)) p = ((MvPolynomial.aeval (fun s => truncTotal (m + 1) (a s)) p : MvPolynomial τ R) :
        MvPowerSeries τ R) := fun p => by
    induction p using MvPolynomial.induction_on with
    | C r => simp [MvPowerSeries.algebraMap_apply]
    | add p q hp hq => simp [hp, hq]
    | mul_X p s hp => simp [hp]
  rw [pj.eq_def m (subst a f), truncTotal_subst ha, subst_coe, e]
  refine Eq.trans ?_ (pj_coe m _).symm
  have h : (jS m a ha).comp (Ideal.Quotient.mkₐ R _) =
      (Ideal.Quotient.mkₐ R _).comp (MvPolynomial.aeval fun s => truncTotal (m + 1) (a s)) :=
    MvPolynomial.algHom_ext fun s => (jS_zR m a ha s).trans (by rw [AlgHom.comp_apply, MvPolynomial.aeval_X]; rfl)
  exact AlgHom.congr_fun h _

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) {n l : ℕ}

def jP (m : ℕ) (p : Q R d n) : JetR R (Fin d) m →ₐ[R] JetR R (Fin n × Fin d) m := jS m p.1 p.2

theorem jP_zR (m : ℕ) (p : Q R d n) (j : Fin d) : jP m p (zR m j) = pj m (p.1 j) := jS_zR m p.1 p.2 j

def ptJ (m : ℕ) (p : Q R d n) : sp (R₀ := R) (JetR R (Fin n × Fin d) m) ⟶ G := spMap (jP m p) ≫ x m

def jQ (m : ℕ) (b : Fin n → Q R d l) : JetR R (Fin n × Fin d) m →ₐ[R] JetR R (Fin l × Fin d) m :=
  jS m (fun s => (b s.1).1 s.2) fun s => (b s.1).2 s.2

theorem ptJ_sq (m : ℕ) (b : Fin n → Q R d l) (p : Q R d n) : spMap (jQ m b) ≫ ptJ x m p = ptJ x m (sq b p) := by
  rw [ptJ, ptJ, ← Category.assoc, spMap_comp]
  refine congrArg (fun g => spMap g ≫ x m) (jet_ext fun j => ?_)
  rw [AlgHom.comp_apply, jP_zR, jP_zR, jQ, jS_pj]
  exact congrArg _ (sb_apply b _).symm

variable {x} (hx : IsUnivChart G d x)
include hx

theorem aug_jS (m : ℕ) (p : Q R d n) : (jetAug R _ m).comp (jP m p) = jetAug R (Fin d) m :=
  jet_ext fun j => by rw [AlgHom.comp_apply, jP_zR, aug_pj, jetAug_zR]; exact p.2 j

theorem ptJ_aug (m : ℕ) (p : Q R d n) : spMap (jetAug R _ m) ≫ ptJ x m p = 1 := by
  rw [ptJ, ← Category.assoc, spMap_comp, aug_jS hx, spMap_jetAug_alt hx]

theorem ptJ_trunc (m : ℕ) (p : Q R d n) : spMap (jetTruncR R _ m) ≫ ptJ x (m + 1) p = ptJ x m p := by
  rw [ptJ, ptJ, ← hx.1 m, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp]
  refine congrArg (fun g => spMap g ≫ x (m + 1)) (jet_ext fun j => ?_)
  rw [AlgHom.comp_apply, AlgHom.comp_apply, jP_zR, pj_trunc]
  exact (jP_zR m p j).symm

theorem ptJ_inj {p q : Q R d n} (h : ∀ m, ptJ x m p = ptJ x m q) : p = q :=
  Subtype.ext (funext fun j => pj_ext fun m => by
    have := (hx.2.2 _ (jetAug R _ m) m (ker_jetAug_pow _ m) _ (ptJ_aug hx m p)).unique ⟨aug_jS hx m p, rfl⟩
      ⟨aug_jS hx m q, h m⟩
    rw [← jP_zR, this, jP_zR])

theorem exists_ptJ (y : ∀ m, sp (R₀ := R) (JetR R (Fin n × Fin d) m) ⟶ G) (h₀ : ∀ m, spMap (jetAug R _ m) ≫ y m = 1)
    (h₁ : ∀ m, spMap (jetTruncR R _ m) ≫ y (m + 1) = y m) : ∃ p : Q R d n, ∀ m, ptJ x m p = y m := by
  choose ψ hψ hu using fun m => hx.2.2 _ (jetAug R _ m) m (ker_jetAug_pow _ m) _ (h₀ m)
  have at' : ∀ κ m, (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1) := fun κ m =>
    jet_ext fun j => (jetAug_zR m j).trans (jetAug_zR (m + 1) j).symm
  have cmp : ∀ m, (jetTruncR R _ m).comp (ψ (m + 1)) = (ψ m).comp (jetTruncR R _ m) := fun m =>
    (hx.2.2 _ (jetAug R _ m) (m + 1) (le_bot_iff.1 ((Ideal.pow_le_pow_right (Nat.le_succ _)).trans (ker_jetAug_pow _ m).le))
      _ (h₀ m)).unique
      ⟨by rw [← AlgHom.comp_assoc, at', (hψ _).1], by rw [← spMap_comp, Category.assoc, ← (hψ _).2, h₁]⟩
      ⟨by rw [← AlgHom.comp_assoc, (hψ _).1, at'], by rw [← spMap_comp, Category.assoc, hx.1, ← (hψ _).2]⟩
  choose f hf using fun j => exists_pj (fun m => ψ m (zR m j)) fun m => AlgHom.congr_fun (cmp m) (zR (m + 1) j)
  refine ⟨⟨f, fun j => ?_⟩, fun m => ?_⟩
  · rw [← aug_pj 0, hf]; exact (AlgHom.congr_fun (hψ 0).1 _).trans (jetAug_zR 0 j)
  · rw [(hψ m).2, ptJ]
    exact congrArg (fun g => spMap g ≫ x m) (jet_ext fun j => (jP_zR _ _ j).trans (hf j m))

theorem ptJ_zero (m : ℕ) : ptJ x m (0 : Q R d n) = 1 := by
  have e : jP m (0 : Q R d n) = (Algebra.ofId R _).comp (jetAug R (Fin d) m) := jet_ext fun j => by
    rw [jP_zR, AlgHom.comp_apply, jetAug_zR, map_zero]
    exact (congrArg _ (map_zero (truncTotal (m + 1)))).trans (map_zero _)
  rw [ptJ, e, ← spMap_comp, Category.assoc, spMap_jetAug_alt hx, comp_one']

theorem exists_series [IsCommMonObj G] {O : Type} [CommRing O] (a : Geo.Tor.OAct O G) :
    ∃ (F : FGLaw R d) (A : OAct O F),
      (∀ m, ptJ x m (⟨F.F, F.const⟩ : Q R d 2) = ptJ x m (gen 0) * ptJ x m (gen 1)) ∧
      ∀ c m, ptJ x m (⟨A.act c, A.const c⟩ : Q R d 1) = ptJ x m (gen 0) ≫ a.act c := by
  obtain ⟨F, hF⟩ := exists_ptJ hx (fun m => ptJ x m (gen 0 : Q R d 2) * ptJ x m (gen 1))
    (fun m => by rw [MonObj.comp_mul, ptJ_aug hx, ptJ_aug hx, _root_.mul_one])
    (fun m => by rw [MonObj.comp_mul, ptJ_trunc hx, ptJ_trunc hx])
  choose A hA using fun c => exists_ptJ hx (fun m => ptJ x m (gen 0 : Q R d 1) ≫ a.act c)
    (fun m => by have := a.hom c; rw [← Category.assoc, ptJ_aug hx, MonObj.one_comp])
    (fun m => by rw [← Category.assoc, ptJ_trunc hx])
  have vF : ∀ {n} m (u v : Q R d n), ptJ x m (op F u v) = ptJ x m u * ptJ x m v := fun m u v => by
    rw [op, ← ptJ_sq, hF, MonObj.comp_mul, ptJ_sq, ptJ_sq, sq_gen, sq_gen]; rfl
  have vA : ∀ c {n} m (u : Q R d n), ptJ x m (ac (A c) u) = ptJ x m u ≫ a.act c := fun c n m u => by
    rw [ac, ← ptJ_sq, hA, ← Category.assoc, ptJ_sq, sq_gen]; rfl
  have val := fun {n} {p q : Q R d n} (h : ∀ m, ptJ x m p = ptJ x m q) => congrArg Subtype.val (ptJ_inj hx h)
  refine ⟨⟨F.1, F.2, fun i => ?_, fun i => ?_, fun i => ?_⟩, ⟨fun c => (A c).1, fun c => (A c).2, fun c => ?_, fun c c' => ?_,
    fun c c' => ?_, ?_⟩, hF, hA⟩
  · have := val (p := op F 0 (gen 0 : Q R d 1)) (q := gen 0) fun m => by rw [vF, ptJ_zero hx, _root_.one_mul]
    rw [op_val] at this; exact congrFun this i
  · have := val (p := op F (gen 1) (gen 0 : Q R d 2)) (q := F) fun m => by rw [vF, hF, mul_comm]
    rw [op_val] at this; exact congrFun this i
  · have := val (p := op F (op F (gen 0) (gen 1)) (gen 2 : Q R d 3)) (q := op F (gen 0) (op F (gen 1) (gen 2))) fun m => by
      simp only [vF, _root_.mul_assoc]
    simp only [op_val] at this; exact congrFun this i
  · have := val (p := ac (A c) (op F (gen 0) (gen 1 : Q R d 2))) (q := op F (ac (A c) (gen 0)) (ac (A c) (gen 1))) fun m => by
      have := a.hom c
      simp only [vF, vA, MonObj.mul_comp]
    simp only [op_val, ac_val] at this; exact this
  · have := val (p := A (c + c')) (q := op F (A c) (A c')) fun m => by rw [vF, hA, hA, hA, a.add, MonObj.comp_mul]
    rw [op_val] at this; exact this
  · have := val (p := A (c * c')) (q := ac (A c) (A c')) fun m => by rw [vA, hA, hA, mul_comm, a.mul, Category.assoc]
    rw [ac_val] at this; exact this
  · exact val (p := A 1) (q := gen 0) fun m => by rw [hA, a.one, Category.comp_id]

theorem comb_single {v : Fin d → (Geo.Tor.epsR R ⟶ G)} (hv : ∀ j, v j = spMap (dualLift (Pi.single j 1)) ≫ x 1) (i : Fin d) :
    Geo.Tor.IsLieComb (Pi.single i 1) v (v i) := by
  have ht : ∀ j, IsTan (v j) := fun j => hv j ▸ isTan_dualLift hx _
  obtain ⟨h, e⟩ := prodPts_tan hx (Pi.single i 1) v ht
  refine (isLieComb_iff _ _ _).2 (tan_ext hx (ht i) h ?_)
  rw [e, Finset.sum_congr rfl fun j _ => congrArg _ (tcoord_eq hx _ (ht j) _ (hv j)), sum_single, tcoord_eq hx _ (ht i) _ (hv i)]

end ReciprocityTheory.ChartRestriction.G.Chart
