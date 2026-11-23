import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableSetBox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleAbsDetUnitaryAdelicEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharLeftRightMatrixMulAdeleTensor

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SigL

section Abstract2

theorem mod_sub {A N : Type} [Ring A] [AddCommGroup N] [Module A N] (e : A) (x : N) : x - e • x = (1 - e) • x := by
  rw [sub_smul, one_smul]

theorem rh_of_idem {A R : Type} [Ring A] [Ring R] (f : A →+* R) {e y : A} (he : f e = 0) (h : e * y = y) : f y = 0 := by
  rw [← h, map_mul, he, zero_mul]

theorem rh_sum_right {A R ι : Type} [Ring A] [Ring R] (f : A →+* R) (s : Finset ι) (p q : ι → A) (h : ∀ k, f (q k) = 0) :
    f (∑ k ∈ s, p k * q k) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun k _ => by rw [map_mul, h k, mul_zero]

theorem rh_sum_left {A R ι : Type} [Ring A] [Ring R] (f : A →+* R) (s : Finset ι) (p q : ι → A) (h : ∀ k, f (p k) = 0) :
    f (∑ k ∈ s, p k * q k) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun k _ => by rw [map_mul, h k, zero_mul]

theorem rh_add_zero {A R : Type} [Ring A] [Ring R] (f : A →+* R) (p q : A) (h : f q = 0) : f (p + q) = f p := by
  rw [map_add, h, add_zero]

variable {A B : Type} [MeasurableSpace A] [MeasurableSpace B]

theorem abs_prod_map (p : Measure A) (q : Measure B) [SFinite p] [SFinite q] {f : A → A} {g : B → B} (hf : Measurable f)
    (hg : Measurable g) (k : ℝ≥0) (h1 : p.map f = p) (h2 : q.map g = k • q) :
    (p.prod q).map (Prod.map f g) = k • p.prod q := by
  rw [← Measure.map_prod_map p q hf hg, h1, h2]
  exact Measure.prod_smul_right (μ := p) (ν := q) (k : ℝ≥0∞)

theorem abs_shear [Add B] (p : Measure A) (q : Measure B) [SFinite p] [SFinite q] (s : A → B)
    (hg : Measurable fun z : A × B => z.2 + s z.1) (hq : ∀ c, q.map (· + c) = q) :
    (p.prod q).map (fun z => (z.1, z.2 + s z.1)) = p.prod q :=
  ((MeasurePreserving.id p).skew_product (g := fun x y => y + s x) hg (.of_forall fun x => hq (s x))).map_eq

theorem map_aut {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsAddHaarMeasure]
    (φ : G ≃ₜ+ G) : ν.map φ = (addEquivAddHaarChar φ)⁻¹ • ν := by
  have h := addEquivAddHaarChar_smul_map ν φ
  have hne : addEquivAddHaarChar φ ≠ 0 := (addEquivAddHaarChar_pos φ).ne'
  conv_rhs => rw [← h]
  rw [smul_smul, inv_mul_cancel₀ hne, one_smul]

end Abstract2

variable {D : D7} {a b c r t : ℕ}

theorem map_lr (g : GL (Fin a) (AE D)) (k : GL (Fin b) (AE D)) (ν : Measure (Mx D a b)) (hν : ν.IsAddHaarMeasure) :
    ν.map (fun U => mm (mm g.1 U) k.1) =
      ((absA D (Matrix.GeneralLinearGroup.det g)) ^ b * (absA D (Matrix.GeneralLinearGroup.det k)) ^ a)⁻¹ • ν := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := top_mx (D := D) a b
  haveI := topRing D
  have hc : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE g k) =
      absA D (Matrix.GeneralLinearGroup.det g) ^ b * absA D (Matrix.GeneralLinearGroup.det k) ^ a :=
    GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) a b g k
  have h := map_aut ν (GlobalTheory.ModuLR.lrCE g k)
  rw [hc] at h
  exact h

theorem map_left_unitary (V : HSp D) (h : GA D V) (ν : Measure (Mx D V.rank b)) (hν : ν.IsAddHaarMeasure) :
    ν.map (fun U => mm (mt V h) U) = ν := by
  have h1 := map_lr (matHom V h) (1 : GL (Fin b) (AE D)) ν hν
  have h2 : absA D (Matrix.GeneralLinearGroup.det (matHom V h)) = 1 := GlobalTheory.UnitaryDetAbs.absE_det_matHom D V h
  rw [h2, map_one, map_one, one_pow, one_pow, mul_one, inv_one, one_smul] at h1
  have e : (fun U : Mx D V.rank b => mm (mt V h) U) =
      fun U => mm (mm (matHom V h).1 U) (1 : GL (Fin b) (AE D)).1 := funext fun U => by
    rw [Units.val_one]
    simp only [mm, Matrix.mul_one]
    rfl
  rw [e]
  exact h1

theorem map_right_gl (g : GL (Fin b) (AE D)) (ν : Measure (Mx D a b)) (hν : ν.IsAddHaarMeasure) :
    ν.map (fun U => mm U g.1) = ((absA D (Matrix.GeneralLinearGroup.det g))⁻¹ ^ a : ℝ≥0) • ν := by
  have h1 := map_lr (1 : GL (Fin a) (AE D)) g ν hν
  rw [map_one, map_one, one_pow, one_mul, ← inv_pow] at h1
  have e : (fun U : Mx D a b => mm U g.1) = fun U => mm (mm (1 : GL (Fin a) (AE D)).1 U) g.1 := funext fun U => by
    rw [Units.val_one]
    simp only [mm, Matrix.one_mul]
  rw [e]
  exact h1

end GlobalTheory.CompanionTheory.SigL

namespace GlobalTheory.CompanionTheory.SigL

section Abstract3

theorem mat_left {R : Type} [Ring R] {a b : ℕ} (M : Matrix (Fin a) (Fin a) R) (x : Matrix (Fin a) (Fin b) R) :
    M * x = x + (M - 1) * x := by
  rw [Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]

theorem mat_right {R : Type} [Ring R] {a b : ℕ} (M : Matrix (Fin b) (Fin b) R) (x : Matrix (Fin a) (Fin b) R) :
    x * M = x + x * (M - 1) := by
  rw [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]

theorem mat_left_apply {R : Type} [Ring R] {a b : ℕ} (M : Matrix (Fin a) (Fin a) R) (x : Matrix (Fin a) (Fin b) R)
    (i : Fin a) (j : Fin b) : (M * x) i j = x i j + ∑ k, (M - 1) i k * x k j := by
  rw [mat_left, Matrix.add_apply, Matrix.mul_apply]

theorem mat_right_apply {R : Type} [Ring R] {a b : ℕ} (M : Matrix (Fin b) (Fin b) R) (x : Matrix (Fin a) (Fin b) R)
    (i : Fin a) (j : Fin b) : (x * M) i j = x i j + ∑ k, x i k * (M - 1) k j := by
  rw [mat_right, Matrix.add_apply, Matrix.mul_apply]

theorem mat_shear_apply {R : Type} [Ring R] {a r t : ℕ} (p : Matrix (Fin a) (Fin t) R) (x : Matrix (Fin a) (Fin r) R)
    (y : Matrix (Fin r) (Fin t) R) (i : Fin a) (j : Fin t) : (p + x * y) i j = p i j + ∑ k, x i k * y k j := by
  rw [Matrix.add_apply, Matrix.mul_apply]

end Abstract3

variable {D : D7} {a b c r t : ℕ}

theorem intOff_congr {S : Finset (Pl D)} {x y : Mx D a b}
    (h : ∀ v ∉ S, ∀ i j, cv D v (x i j) = cv D v (y i j)) : IntOff S x ↔ IntOff S y :=
  ⟨fun hx v hv i j => by rw [← h v hv i j]; exact hx v hv i j,
    fun hy v hv i j => by rw [h v hv i j]; exact hy v hv i j⟩

theorem cv_of_idem {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) {v : Pl D} (hv : v ∉ S) {x : Mx D a b}
    (h : e • x = x) (i : Fin a) (j : Fin b) : cv D v (x i j) = 0 := by
  have h0 : cv D v e = 0 := by
    have := hS.2 v
    rwa [if_neg hv] at this
  exact rh_of_idem _ h0 (congrFun (congrFun h i) j)

theorem cv_left {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) {v : Pl D} (hv : v ∉ S) {M : Mx D a a}
    (hM : e • (M - 1) = M - 1) (x : Mx D a b) (i : Fin a) (j : Fin b) : cv D v ((mm M x) i j) = cv D v (x i j) := by
  have e1 : (mm M x) i j = x i j + ∑ k, (M - 1) i k * x k j := mat_left_apply M x i j
  rw [e1]
  exact rh_add_zero _ _ _ (rh_sum_left _ _ _ _ fun k => cv_of_idem hS hv hM i k)

theorem cv_right {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) {v : Pl D} (hv : v ∉ S) {M : Mx D b b}
    (hM : e • (M - 1) = M - 1) (x : Mx D a b) (i : Fin a) (j : Fin b) : cv D v ((mm x M) i j) = cv D v (x i j) := by
  have e1 : (mm x M) i j = x i j + ∑ k, x i k * (M - 1) k j := mat_right_apply M x i j
  rw [e1]
  exact rh_add_zero _ _ _ (rh_sum_right _ _ _ _ fun k => cv_of_idem hS hv hM k j)

theorem cv_shear {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) {v : Pl D} (hv : v ∉ S) {y : Mx D r t}
    (hy : e • y = y) (p : Mx D a t) (x : Mx D a r) (i : Fin a) (j : Fin t) :
    cv D v ((p + mm x y) i j) = cv D v (p i j) := by
  have e1 : (p + mm x y) i j = p i j + ∑ k, x i k * y k j := mat_shear_apply p x y i j
  rw [e1]
  exact rh_add_zero _ _ _ (rh_sum_right _ _ _ _ fun k => cv_of_idem hS hv hy k j)

theorem ip_smul (V : HSp D) {e : AE D} (he : e * e = e) (hc : cA D e = e) (x : Mx D V.rank a) :
    ip V (e • x) (e • x) = e • ip V x x := by
  unfold ip
  rw [adj_smul, hc]
  simp only [mm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]

theorem sig_finite (S : Finset (Pl D)) {e : AE D} (hS : IsIdem S e) (he : e * e = e)
    [T2Space (XS D a r t e)] [BorelSpace (XS D a r t e)]
    (P : Measure (Mx D a r × Mx D a t)) [IsFiniteMeasureOnCompacts P] :
    IsFiniteMeasureOnCompacts (sig S he P) := by
  obtain ⟨T₁, hT₁, h₁⟩ := exists_box S hS a r
  obtain ⟨T₂, hT₂, h₂⟩ := exists_box S hS a t
  obtain ⟨q1, -, -, w1, -⟩ := top_mx (D := D) a r
  obtain ⟨q2, -, -, w2, -⟩ := top_mx (D := D) a t
  obtain ⟨g1, g2⟩ := top_pair (D := D) a r t
  have oX : OpensMeasurableSpace (XS D a r t e) := BorelSpace.opensMeasurable
  have oM : OpensMeasurableSpace (Mx D a r × Mx D a t) := g1.opensMeasurable
  have c1 : ContinuousAdd (Mx D a r) := q1.toContinuousAdd
  have c2 : ContinuousAdd (Mx D a t) := q2.toContinuousAdd
  have c3 : ContinuousAdd (Mx D a r × Mx D a t) := Prod.continuousAdd
  have t3 : T2Space (Mx D a r × Mx D a t) := Prod.t2Space
  refine abs_finite (toX he) (measurable_toX he) Subtype.val continuous_subtype_val (measurableSet_box S) P
    (T₁ ×ˢ T₂) (hT₁.prod hT₂) (fun z hz => ?_)
  have e1 : z - ((toX he z).1 : Mx D a r × Mx D a t) = ((1 - e) • z.1, (1 - e) • z.2) :=
    Prod.ext (mod_sub e z.1) (mod_sub e z.2)
  rw [e1]
  exact ⟨h₁ _ hz.1, h₂ _ hz.2⟩

theorem continuous_ip (V : HSp D) :
    Continuous fun x : Mx D V.rank a => ip V x x := by
  haveI := topRing D
  have hc : Continuous (cA D) := GlobalTheory.FockCompare.ThetaCont.continuous_conj
  have h1 : Continuous (adj : Mx D V.rank a → Mx D a V.rank) := (continuous_id.matrix_map hc).matrix_transpose
  exact h1.matrix_mul (continuous_const.matrix_mul continuous_id)

theorem sig_supp (S : Finset (Pl D)) {e : AE D} (he : e * e = e) (hc : cA D e = e) (V : HSp D)
    [BorelSpace (XS D V.rank r t e)] (b₀ : HermE D r) (fib : Measure (Mx D V.rank r))
    (μt : Measure (Mx D V.rank t)) [SFinite fib] [SFinite μt] (hs : fib {x | ip V x x ≠ rat b₀.1} = 0) :
    sig S he (fib.prod μt) {z | ip V z.1.1 z.1.1 = e • rat b₀.1}ᶜ = 0 := by
  obtain ⟨-, -, -, w1, -⟩ := top_mx (D := D) r r
  have hcl : IsClosed {z : XS D V.rank r t e | ip V z.1.1 z.1.1 = e • rat b₀.1} :=
    isClosed_eq ((continuous_ip V).comp (continuous_fst.comp continuous_subtype_val)) continuous_const
  have oX : OpensMeasurableSpace (XS D V.rank r t e) := BorelSpace.opensMeasurable
  have hm := measurable_toX (a := V.rank) (r := r) (t := t) he
  have hAc := hcl.measurableSet.compl
  unfold sig
  rw [Measure.map_apply hm hAc, Measure.restrict_apply (hm hAc)]
  have h0 : (fib.prod μt) ({x | ip V x x ≠ rat b₀.1} ×ˢ Set.univ) = 0 := by
    rw [Measure.prod_prod, hs, zero_mul]
  refine measure_mono_null ?_ h0
  rintro z ⟨hz, -⟩
  refine ⟨fun h => hz ?_, trivial⟩
  change ip V (e • z.1) (e • z.1) = e • rat b₀.1
  rw [ip_smul V he hc, h]

theorem sig_map (S : Finset (Pl D)) {e : AE D} (he : e * e = e) [BorelSpace (XS D a r t e)]
    (P : Measure (Mx D a r × Mx D a t)) (T : Mx D a r × Mx D a t → Mx D a r × Mx D a t) (hT : Measurable T)
    (k : ℝ≥0) (Θ : XS D a r t e ≃ₜ XS D a r t e)
    (hBT : ∀ z, (IntOff S (T z).1 ∧ IntOff S (T z).2) ↔ (IntOff S z.1 ∧ IntOff S z.2))
    (hΘ : ∀ z, Θ (toX he z) = toX he (T z)) (hP : P.map T = k • P) :
    (sig S he P).map Θ = k • sig S he P := by
  have oX : OpensMeasurableSpace (XS D a r t e) := BorelSpace.opensMeasurable
  exact abs_map (toX he) (measurable_toX he) (measurableSet_box S) P T hT k Θ Θ.continuous.measurable
    (Set.ext hBT) hΘ hP

theorem sig_integral (S : Finset (Pl D)) {e : AE D} (he : e * e = e) [BorelSpace (XS D a r t e)]
    (P : Measure (Mx D a r × Mx D a t)) (Ξ : Mx D a r × Mx D a t → ℂ) (hc : Continuous Ξ)
    (h : ∀ z, (IntOff S z.1 ∧ IntOff S z.2 → Ξ z = Ξ (e • z.1, e • z.2)) ∧ (¬ (IntOff S z.1 ∧ IntOff S z.2) → Ξ z = 0)) :
    (Integrable Ξ P → Integrable (fun z : XS D a r t e => Ξ z.1) (sig S he P)) ∧
    ∫ z, Ξ z ∂P = ∫ z, Ξ z.1 ∂(sig S he P) := by
  have oX : OpensMeasurableSpace (XS D a r t e) := BorelSpace.opensMeasurable
  have hf : Continuous fun z : XS D a r t e => Ξ z.1 := hc.comp continuous_subtype_val
  exact abs_integral (toX he) (measurable_toX he) (measurableSet_box S) P (fun z => Ξ z.1)
    hf.aestronglyMeasurable Ξ (fun z hz => (h z).1 hz) (fun z hz => (h z).2 hz)

end GlobalTheory.CompanionTheory.SigL

namespace GlobalTheory.CompanionTheory.SigL

variable {D : D7} {a b c r t : ℕ}

theorem measurable_left (M : Mx D a a) : Measurable fun x : Mx D a b => mm M x := by
  haveI := topRing D
  obtain ⟨-, -, -, -, h5⟩ := top_mx (D := D) a b
  exact (continuous_const.matrix_mul continuous_id).measurable

theorem measurable_right (M : Mx D b b) : Measurable fun x : Mx D a b => mm x M := by
  haveI := topRing D
  obtain ⟨-, -, -, -, h5⟩ := top_mx (D := D) a b
  exact (continuous_id.matrix_mul continuous_const).measurable

theorem sig_U (S : Finset (Pl D)) {e : AE D} (hS : IsIdem S e) (he : e * e = e) (V : HSp D)
    [BorelSpace (XS D V.rank r t e)] (fib : Measure (Mx D V.rank r)) (μt : Measure (Mx D V.rank t)) [SFinite fib] [SFinite μt]
    (hμ : μt.IsAddHaarMeasure) (h : GA D V) (hf : fib.map (fun x => mm (mt V h) x) = fib)
    (hh : e • (mt V h - 1) = mt V h - 1) (Θ : XS D V.rank r t e ≃ₜ XS D V.rank r t e)
    (hΘ : ∀ z, (Θ z).1 = (mm (mt V h) z.1.1, mm (mt V h) z.1.2)) :
    (sig S he (fib.prod μt)).map Θ = sig S he (fib.prod μt) := by
  have m1 := measurable_left (D := D) (b := r) (mt V h)
  have m2 := measurable_left (D := D) (b := t) (mt V h)
  have hP := abs_prod_map fib μt m1 m2 1 hf (by rw [map_left_unitary V h μt hμ, one_smul])
  have key := sig_map S he (fib.prod μt) (Prod.map (fun x => mm (mt V h) x) fun x => mm (mt V h) x)
    ((m1.comp measurable_fst).prodMk (m2.comp measurable_snd)) 1 Θ
    (fun z => and_congr (intOff_congr fun v hv i j => cv_left hS hv hh z.1 i j)
      (intOff_congr fun v hv i j => cv_left hS hv hh z.2 i j))
    (fun z => Subtype.ext ((hΘ _).trans (Prod.ext (Matrix.mul_smul _ _ _) (Matrix.mul_smul _ _ _)))) hP
  rwa [one_smul] at key

theorem sig_S (S : Finset (Pl D)) {e : AE D} (hS : IsIdem S e) (he : e * e = e)
    [BorelSpace (XS D a r t e)] (fib : Measure (Mx D a r)) (μt : Measure (Mx D a t)) [SFinite fib] [SFinite μt]
    (hμ : μt.IsAddHaarMeasure) (y : Mx D r t) (hy : e • y = y) (Θ : XS D a r t e ≃ₜ XS D a r t e)
    (hΘ : ∀ z, (Θ z).1 = (z.1.1, z.1.2 + mm z.1.1 y)) :
    (sig S he (fib.prod μt)).map Θ = sig S he (fib.prod μt) := by
  haveI := topRing D
  obtain ⟨q2, -, -, -, b2⟩ := top_mx (D := D) a t
  obtain ⟨g1, g2⟩ := top_pair (D := D) a r t
  have oM : OpensMeasurableSpace (Mx D a r × Mx D a t) := g1.opensMeasurable
  have c2 : ContinuousAdd (Mx D a t) := q2.toContinuousAdd
  have hc : Continuous fun z : Mx D a r × Mx D a t => z.2 + mm z.1 y :=
    continuous_snd.add (continuous_fst.matrix_mul continuous_const)
  have hq : ∀ u : Mx D a t, μt.map (· + u) = μt := fun u => map_add_right_eq_self μt u
  have hP := abs_shear fib μt (fun x => mm x y) hc.measurable hq
  have key := sig_map S he (fib.prod μt) (fun z => (z.1, z.2 + mm z.1 y))
    (measurable_fst.prodMk hc.measurable) 1 Θ
    (fun z => and_congr Iff.rfl (intOff_congr fun v hv i j => cv_shear hS hv hy z.2 z.1 i j))
    (fun z => Subtype.ext ((hΘ _).trans (Prod.ext rfl ?_))) (by rw [hP, one_smul])
  · rwa [one_smul] at key
  · change e • z.2 + mm (e • z.1) y = e • (z.2 + mm z.1 y)
    rw [smul_add]
    exact congrArg (e • z.2 + ·) (Matrix.smul_mul _ _ _)

theorem sig_G (S : Finset (Pl D)) {e : AE D} (hS : IsIdem S e) (he : e * e = e)
    [BorelSpace (XS D a r t e)] (fib : Measure (Mx D a r)) (μt : Measure (Mx D a t)) [SFinite fib] [SFinite μt]
    (hμ : μt.IsAddHaarMeasure) (g : GL (Fin t) (AE D)) (hg : e • (g.1 - 1) = g.1 - 1)
    (Θ : XS D a r t e ≃ₜ XS D a r t e) (hΘ : ∀ z, (Θ z).1 = (z.1.1, mm z.1.2 g.1)) :
    (sig S he (fib.prod μt)).map Θ = ((absA D (Matrix.GeneralLinearGroup.det g))⁻¹ ^ a : ℝ≥0) • sig S he (fib.prod μt) := by
  have m2 := measurable_right (D := D) (a := a) g.1
  have hP := abs_prod_map fib μt measurable_id m2 ((absA D (Matrix.GeneralLinearGroup.det g))⁻¹ ^ a)
    Measure.map_id (map_right_gl g μt hμ)
  exact sig_map S he (fib.prod μt) (Prod.map id fun x => mm x g.1)
    (measurable_fst.prodMk (m2.comp measurable_snd)) _ Θ
    (fun z => and_congr Iff.rfl (intOff_congr fun v hv i j => cv_right hS hv hg z.2 i j))
    (fun z => Subtype.ext ((hΘ _).trans (Prod.ext rfl (Matrix.smul_mul _ _ _)))) hP

theorem main : IdemEx → TopX → SigLaw := by
  intro hI hT D r t V b₀ S e hS he fib μt hfin hs hinv hμ
  obtain ⟨x1, x2, x3, x4, x5, x6, -, -, -⟩ := hT D V.rank r t e
  have hc : cA D e = e := (((hI D S).2 e hS)).2
  obtain ⟨q1, l1, s1, w1, b1⟩ := top_mx (D := D) V.rank r
  obtain ⟨q2, l2, s2, w2, b2⟩ := top_mx (D := D) V.rank t
  have f1 : SFinite fib := by
    have : IsLocallyFiniteMeasure fib := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
    infer_instance
  have f2 : SFinite μt := by
    infer_instance
  refine ⟨sig_finite S hS he _, sig_supp S he hc V b₀ fib μt hs, fun Ξ h1 h2 => sig_integral S he _ Ξ h1 h2,
    fun h hh Θ hΘ => sig_U S hS he V fib μt hμ h (hinv h) hh Θ hΘ,
    fun y hy Θ hΘ => sig_S S hS he fib μt hμ y hy Θ hΘ,
    fun g hg Θ hΘ => sig_G S hS he fib μt hμ g hg Θ hΘ⟩

end GlobalTheory.CompanionTheory.SigL

end
