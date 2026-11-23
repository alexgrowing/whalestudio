import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AddPCvOfAddMod
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvalPowerSeriesEqOneOfTwoAxesStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvPFirstOrderOfEqOne

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.DegenDir

theorem telescope {Gp R : Type} [CommGroup Gp] [CommRing R] (θ : Gp → Gp → Gp → Rˣ) (x y : Gp) (f : ℕ → Rˣ) (w : Rˣ)
    (t : R) (ht : t ^ 2 = 0) (B : ℕ → R) (β : R)
    (h : ∀ i, (θ (x ^ i) x y * f i * w).val = (1 + t * (B (i + 1) - B i - β)) * (f (i + 1)).val) (k : ℕ) :
    (cubN θ k 1 x y * f 0 * w ^ k).val = (1 + t * (B k - B 0 - k * β)) * (f k).val := by
  induction k with
  | zero => simp [cubN]
  | succ k ih =>
    have hk := h k
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul, Units.val_mul, pow_succ w, Nat.cast_succ] at ih hk ⊢
    linear_combination ((θ (x ^ k) x y).val * w.val) * ih + (1 + t * (B k - B 0 - k * β)) * hk +
      ((B k - B 0 - k * β) * (B (k + 1) - B k - β) * (f (k + 1)).val) * ht

theorem telescope_eq_one {Gp R : Type} [CommGroup Gp] [CommRing R] (θ : Gp → Gp → Gp → Rˣ) (x y : Gp) (f : ℕ → Rˣ)
    (w : Rˣ) (t : R) (ht : t ^ 2 = 0) (B : ℕ → R) (β : R)
    (h : ∀ i, (θ (x ^ i) x y * f i * w).val = (1 + t * (B (i + 1) - B i - β)) * (f (i + 1)).val) (p : ℕ)
    (hp : (p : R) = 0) (hf : f p = f 0) (hB : B p = B 0) : cubN θ p 1 x y * w ^ p = 1 := by
  have e := telescope θ x y f w t ht B β h p
  rw [hp, hf, hB, sub_self, zero_mul, sub_zero, mul_zero, add_zero, _root_.one_mul, Units.val_inj,
    mul_right_comm] at e
  exact mul_eq_right.1 e

section Eval

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ}

theorem pair_mem {I : Ideal A} {a b : Fin d → A} (ha : ∀ j, a j ∈ I) (hb : ∀ j, b j ∈ I) (q : Fin 2 × Fin d) :
    ![a, b] q.1 q.2 ∈ I := by
  obtain ⟨i, j⟩ := q
  fin_cases i
  exacts [ha j, hb j]

theorem formalAdd_mem {F : Fin d → PS R 2 d} (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0) {I : Ideal A}
    (hI : ∀ x ∈ I, IsNilpotent x) {a b : Fin d → A} (ha : ∀ j, a j ∈ I) (hb : ∀ j, b j ∈ I) (j : Fin d) :
    addP F a b j ∈ I := by
  have := evBasic_nEval_sub_coeff_mem (F j) (fun q : Fin 2 × Fin d => ![a, b] q.1 q.2)
    (fun q => hI _ (pair_mem ha hb q))
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF, map_zero, sub_zero] at this
  exact (Ideal.span_le.2 (by rintro _ ⟨q, rfl⟩; exact pair_mem ha hb q) : Ideal.span _ ≤ I) this

def mult (F : Fin d → PS R 2 d) (a : Fin d → A) (i : ℕ) : Fin d → A :=
  Nat.rec 0 (fun _ v => addP F v a) i

theorem mult_succ (F : Fin d → PS R 2 d) (a : Fin d → A) (i : ℕ) : mult F a (i + 1) = addP F (mult F a i) a := rfl

theorem mult_mem {F : Fin d → PS R 2 d} (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0) {I : Ideal A}
    (hI : ∀ x ∈ I, IsNilpotent x) {a : Fin d → A} (ha : ∀ j, a j ∈ I) (i : ℕ) : ∀ j, mult F a i j ∈ I := by
  induction i with
  | zero => exact fun _ => I.zero_mem
  | succ i ih => exact formalAdd_mem hF hI ih ha

theorem cv_nil {ga : Fin d → PowerSeries R} (h : ∀ j, PowerSeries.constantCoeff (ga j) = 0) {a : A}
    (ha : IsNilpotent a) (j : Fin d) : IsNilpotent (cv ga a j) :=
  ChartCompare.isNilpotent_nEval (σ := Unit) _ (h j) _ fun _ => ha

theorem cv_sq_zero {ga : Fin d → PowerSeries R} (h : ∀ j, PowerSeries.constantCoeff (ga j) = 0) {e : A}
    (he : e ^ 2 = 0) : cv ga e = fun j => PowerSeries.coeff 1 (ga j) • e := by
  funext j
  have hn : IsNilpotent e := ⟨2, he⟩
  have h0 := evBasic_nEval_sub_coeff_mem (ga j : MvPowerSeries Unit R) (fun _ => (0 : A)) fun _ => IsNilpotent.zero
  have h0' : nEval (σ := Unit) (ga j) (fun _ => (0 : A)) = 0 := by
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      show MvPowerSeries.constantCoeff (ga j) = 0 from h j, map_zero, sub_zero] at h0
    exact (Ideal.span_le.2 (by rintro _ ⟨q, rfl⟩; simp) : Ideal.span _ ≤ (⊥ : Ideal A)) h0
  have h1 := ChartCompare.nEval_sub_mem (σ := Unit) (ga j) (fun _ => e) (fun _ => 0) (fun _ => hn)
    (fun _ => IsNilpotent.zero) (Ideal.span {e}) (Ideal.span {e}) (fun _ => Ideal.subset_span rfl)
    (fun _ => Ideal.zero_mem _) (fun _ => by simp)
  rw [Ideal.span_singleton_mul_span_singleton, ← pow_two, he, Ideal.span_singleton_eq_bot.2 rfl, Ideal.mem_bot,
    h0', sub_zero, sub_eq_zero, Fintype.sum_unique, sub_zero] at h1
  exact h1

theorem evalPoints_eval_one {a b : Fin d → A} (h : ∀ q : Fin 2 × Fin d, IsNilpotent (![a, b] q.1 q.2)) (v : Fin d → PS R 2 d)
    (hv : ∀ j, MvPowerSeries.constantCoeff (v j) = 0) (f : PS R 1 d) :
    evP ![a, b] (ev (n := 2) ![v] f) = evP ![fun j => evP ![a, b] (v j)] f := by
  unfold evP ev
  rw [ChartCompare.nEval_subst _ (by rintro ⟨i, j⟩; fin_cases i; exact hv j) _ _ h]
  congr 1
  funext ⟨i, j⟩
  fin_cases i
  rfl

theorem evalPoints_coboundary {F : Fin d → PS R 2 d} (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0) {a b : Fin d → A}
    (h : ∀ q : Fin 2 × Fin d, IsNilpotent (![a, b] q.1 q.2)) (f : PS R 1 d) :
    evP ![a, b] (ev (n := 2) ![addOf F (pt R d 0) (pt R d 1)] f - ev (n := 2) ![pt R d 0] f -
      ev (n := 2) ![pt R d 1] f) = evP ![addP F a b] f - evP ![a] f - evP ![b] f := by
  have hX : (fun q : Fin 2 × Fin d => (![pt R d 0, pt R d 1] : Fin 2 → Fin d → PS R 2 d) q.1 q.2) =
      MvPowerSeries.X := by
    funext ⟨i, j⟩
    fin_cases i <;> rfl
  have hA : addOf F (pt R d 0) (pt R d 1) = F := by
    funext j
    unfold addOf ev
    rw [hX, MvPowerSeries.subst_self]
    rfl
  have hp : ∀ i : Fin 2, (fun j => evP ![a, b] (pt R d i j)) = ![a, b] i := fun i =>
    funext fun j => ChartCompare.nEval_X _ h (i, j)
  have hs : ∀ f g : PS R 2 d, evP ![a, b] (f - g) = evP ![a, b] f - evP ![a, b] g := nEval_sub h
  rw [hs, hs, hA, evalPoints_eval_one h _ hF, evalPoints_eval_one h _ (fun j => by simp [pt]),
    evalPoints_eval_one h _ (fun j => by simp [pt]), hp, hp]
  rfl

end Eval

section Main

variable {S : Scheme.{0}} {Ω : Type} [Field Ω] {s : Sp Ω ⟶ S} {G : Over S} [GrpObj G] {d : ℕ}
  {F : Fin d → PS Ω 2 d} {P : PtFam s G d}

theorem pt_mult (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0) (hL : IsPtLaw s G F P) {A : Type} [CommRing A]
    [Algebra Ω A] {a : Fin d → A} (ha : ∀ j, IsNilpotent (a j)) (i : ℕ) : P A (mult F a i) = P A a ^ i := by
  induction i with
  | zero => exact (hL.2.1 A).trans (pow_zero _).symm
  | succ i ih =>
    rw [mult_succ, hL.2.2 A _ _ (mult_mem (I := nilradical A) hF (fun _ h => h) ha i) ha, ih, pow_succ]

theorem cubWeil_one [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {p : ℕ} [CharP Ω p] {ph1 ph2 : PS Ω 3 d}
    (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0)
    (h₁ : ev (n := 2) ![0, pt Ω d 0, pt Ω d 1] ph1 = 1) (h₂ : ev (n := 2) ![pt Ω d 0, 0, pt Ω d 1] ph1 = 1)
    (h₃ : ev (n := 2) ![0, pt Ω d 0, pt Ω d 1] ph2 = 1) (hL : IsPtLaw s G F P) (hU : IsPtUniv s G P)
    (hC : IsPtCube s G c F ph1 ph2 P) {u : Fin d → Ω} {f : PS Ω 1 d}
    (hf : c2 ph2 u = ev (n := 2) ![addOf F (pt Ω d 0) (pt Ω d 1)] f - ev (n := 2) ![pt Ω d 0] f -
      ev (n := 2) ![pt Ω d 1] f)
    {A : Type} [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω) (hπ : IsNilpotent (RingHom.ker π)) {e : A} (he : e ^ 2 = 0)
    {b : Fin d → A} (hb : ∀ j, IsNilpotent (b j)) (hx : P A (fun j => u j • e) ^ p = 1) (hy : P A b ^ p = 1) :
    CubWeil c p (P A fun j => u j • e) (P A b) 1 := by
  refine ⟨hx, hy, fun z J hJ => ?_⟩
  obtain ⟨w, hw⟩ := hC A _ hπ z J hJ
  set a : Fin d → A := fun j => u j • e with hadef
  have hker : ∀ x : A, IsNilpotent x → x ∈ RingHom.ker π := fun x hx => (hx.map π).eq_zero
  have hen : ∀ x ∈ Ideal.span {e}, IsNilpotent x := fun x hx => by
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    exact ⟨2, by rw [mul_pow, he, mul_zero]⟩
  have hae : ∀ j, a j ∈ Ideal.span {e} := fun j => by
    simp only [hadef, Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have ha : ∀ j, IsNilpotent (a j) := fun j => hen _ (hae j)
  have hn : ∀ {v : Fin d → A}, (∀ j, IsNilpotent (v j)) → ∀ i j, IsNilpotent (mult F v i j) := fun hv i =>
    mult_mem (I := nilradical A) hF (fun _ h => h) hv i
  have h0 : ∀ {v : Fin d → A}, (∀ j, IsNilpotent (v j)) → P A v ^ p = 1 → mult F v p = mult F v 0 := fun hv h =>
    (hU A π hπ).1 _ (hn hv p) ((pt_mult hF hL hv p).trans h)
  let ρ : A →+* (overAt s A).left.presheaf.stalk z :=
    (((overAt s A).left.presheaf.germ ⊤ z trivial).hom).comp (toΓ A)
  have hρ : ∀ r : A, gs (𝟙 (overAt s A).left) z ⊤ (toΓ A r) = ρ r := fun r => gs_eq _ z ⊤ trivial _
  have hp : ((p : ℕ) : (overAt s A).left.presheaf.stalk z) = 0 := by
    rw [← map_natCast (ρ.comp (algebraMap Ω A)), CharP.cast_eq_zero, map_zero]
  have e₁ := telescope_eq_one (cubV c z J) (P A a) (P A b) (fun i => w (mult F a i) b) (w a b) 0 (by simp) 0 0
    (fun i => by
      have := (hw (mult F a i) a b (fun j => hker _ (hn ha i j)) (fun j => hker _ (ha j))
        (fun j => hker _ (hb j))).1
      rw [pt_mult hF hL ha, T.evalPowerSeries_eq_one_of_two_axes Ω d ph1 h₁ h₂ A e he _ _ _ (mult_mem hF hen hae i) hae hb, hρ, map_one] at this
      rw [zero_mul, add_zero]
      exact this) p hp (by rw [h0 ha hx]) rfl
  have e₂ := telescope_eq_one (cubV c z J) (P A b) (P A a) (fun i => w a (mult F b i)) (w a b) (ρ e)
    (by rw [← map_pow, he, map_zero]) (fun i => ρ (evP ![mult F b i] f)) (ρ (evP ![b] f))
    (fun i => by
      have := (hw a (mult F b i) b (fun j => hker _ (ha j)) (fun j => hker _ (hn hb i j))
        (fun j => hker _ (hb j))).2
      rw [pt_mult hF hL hb, evalPoints_first_order_of_eq_one Ω d ph2 h₃ A e he u _ _ (hn hb i) hb, hρ, hf,
        evalPoints_coboundary hF (pair_mem (I := nilradical A) (hn hb i) hb), map_add, map_one, map_mul, map_sub,
        map_sub] at this
      exact this) p hp (by rw [h0 hb hy]) (by rw [h0 hb hy])
  rw [map_one, _root_.one_mul]
  exact mul_right_cancel (e₁.trans e₂.symm)

end Main

theorem not_nonDeg_of_degenerate : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (d : ℕ) (F : Fin d → PS Ω 2 d) (ph1 ph2 : PS Ω 3 d) (P : PtFam s G d), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → ev (n := 2) ![0, pt Ω d 0, pt Ω d 1] ph1 = 1 → ev (n := 2) ![pt Ω d 0, 0, pt Ω d 1] ph1 = 1 → ev (n := 2) ![0, pt Ω d 0, pt Ω d 1] ph2 = 1 → IsPtLaw s G F P → IsPtUniv s G P → IsPtCube s G c F ph1 ph2 P → Degenerate p F ph2 → ¬ NonDeg p s G c := by
  intro Ω _ p _ _ S s G _ _ L c d F ph1 ph2 P hF h₁ h₂ h₃ hL hU hC ⟨ga, hc, ⟨i, hi⟩, hadd, f, hf⟩ hN
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hα : IsAlpha p s G fun A _ _ a => P A (cv ga a) := by
    refine ⟨fun A B _ _ _ _ φ a ha => ?_, fun A _ _ a a' ha ha' => ?_⟩
    · beta_reduce
      rw [← hL.1 A B φ _ (cv_nil hc ⟨p, ha⟩)]
      congr 1
      funext j
      exact (evBasic_map_nEval φ (ga j : MvPowerSeries Unit Ω) _ fun _ => ⟨p, ha⟩).symm
    · beta_reduce
      rw [← formalAdd_cv_of_addMod Ω p d F ga hc hadd A a a' ha ha', hL.2.2 A _ _ (cv_nil hc ⟨p, ha⟩) (cv_nil hc ⟨p, ha'⟩)]
  have h := hN _ hα fun A _ _ π hπ e he z hz hzp => by
    obtain ⟨b, hb, rfl⟩ := (hU A π hπ).2 z hz
    have hx := hα.pow_eq_one (by omega) (pow_eq_zero_of_le hp he)
    beta_reduce at hx ⊢
    rw [cv_sq_zero hc he] at hx ⊢
    exact cubWeil_one hF h₁ h₂ h₃ hL hU hC hf π hπ he hb hx hzp
  have he : (DualNumber.eps : DualNumber Ω) ^ 2 = 0 := by rw [pow_two, DualNumber.eps_mul_eps]
  have hk : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom Ω Ω Ω)) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']
  have h0 := (hU (DualNumber Ω) _ hk).1 _ (cv_nil hc ⟨2, he⟩) h
  rw [cv_sq_zero hc he] at h0
  exact hi (by simpa using congrArg TrivSqZeroExt.snd (congrFun h0 i))

end GlobalTheory.AlphaPair.DegenDir
end
