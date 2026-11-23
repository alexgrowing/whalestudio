import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.ZSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.HkApply
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.BandOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.DatBasics
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CompBound
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CompShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CompCap
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CompHecke
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep PositivityTheory.Rg.Fx UpperTheory.V.Cm GroundTheory.Automorphic

namespace UpperTheory.ConvolutionTheory.BW

private theorem exists_alg {M : Type} [AddCommGroup M] [Module ℂ M] (V : Submodule ℂ M) (s : Set (Module.End ℂ M))
    (hp : ∀ x ∈ s, ∀ v ∈ V, x v ∈ V) (hc : ∀ x ∈ s, ∀ y ∈ s, ∀ v ∈ V, x (y v) = y (x v)) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra ℂ A) (_ : Module A V) (_ : IsScalarTower ℂ A V),
      (∀ x ∈ s, ∃ a : A, ∀ v : V, ((a • v : V) : M) = x v) ∧ ∀ a b : A, (∀ v : V, a • v = b • v) → a = b := by
  let s' : Set (Module.End ℂ V) := {y | ∃ x, ∃ h : x ∈ s, y = x.restrict (hp x h)}
  have hs : ∀ a ∈ s', ∀ b ∈ s', a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact LinearMap.ext fun v => Subtype.ext (hc x hx y hy v v.2)
  letI : CommRing (Algebra.adjoin ℂ s') :=
    { (inferInstance : Ring (Algebra.adjoin ℂ s')) with
      mul_comm := (Algebra.isMulCommutative_adjoin ℂ hs).is_comm.comm }
  refine ⟨Algebra.adjoin ℂ s', inferInstance, Subalgebra.algebra _, inferInstance, ⟨fun _ _ _ => rfl⟩, fun x hx => ?_,
    fun a b h => Subtype.ext (LinearMap.ext h)⟩
  exact ⟨⟨_, Algebra.subset_adjoin ⟨x, hx, rfl⟩⟩, fun v => rfl⟩

private theorem coef_zero (n : ℕ) (a : ℕ → ℂ) (h : ∀ u : ℂ, ∑ k ∈ Finset.range (n + 1), u ^ (n - k) * a k = 0)
    {k : ℕ} (hk : k ≤ n) : a k = 0 := by
  have hp : (∑ k ∈ Finset.range (n + 1), Polynomial.monomial (n - k) (a k)) = 0 :=
    Polynomial.funext fun u => by
      rw [Polynomial.eval_finset_sum, Polynomial.eval_zero, ← h u]
      exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.eval_monomial, mul_comm]
  have := congrArg (fun p => Polynomial.coeff p (n - k)) hp
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single k] at this
  · simpa using this
  · intro b hb hne
    rw [if_neg]
    have := Finset.mem_range.1 hb
    omega
  · intro h'
    exact absurd (Finset.mem_range.2 (by omega)) h'

private theorem prod_add_esymm {A : Type} [CommRing A] [Algebra ℂ A] (n : ℕ) (u : ℂ) (X : Fin n → A) :
    ∏ i, (algebraMap ℂ A u + X i) =
      ∑ k ∈ Finset.range (n + 1), u ^ (n - k) • MvPolynomial.aeval X (MvPolynomial.esymm (Fin n) ℂ k) := by
  have h := congrArg (Polynomial.eval (algebraMap ℂ A u))
    (Multiset.prod_X_add_C_eq_sum_esymm (Finset.univ.val.map X))
  rw [Multiset.map_map, ← Finset.prod_eq_multiset_prod, Polynomial.eval_prod, Polynomial.eval_finset_sum] at h
  simp only [Function.comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Multiset.card_map,
    Finset.card_val, Finset.card_univ, Fintype.card_fin, Polynomial.eval_mul, Polynomial.eval_pow] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, Algebra.smul_def, map_pow, mul_comm]

private theorem ofFn_rel {M A : Type} [AddCommGroup M] [Module ℂ M] {V : Submodule ℂ M} [CommRing A] [Module A V] :
    ∀ (n : ℕ) (f : Fin n → A) (g : Fin n → Module.End ℂ M), (∀ i (v : V), ((f i • v : V) : M) = g i v) →
      ∀ v : V, (((∏ i, f i) • v : V) : M) = (List.ofFn g).prod v
  | 0, f, g, _, v => by simp
  | n + 1, f, g, h, v => by
    rw [Fin.prod_univ_succ, List.ofFn_succ, List.prod_cons, mul_smul, h, Module.End.mul_apply,
      ofFn_rel n _ _ fun i => h i.succ]

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} {S : Set (Pl E)}

theorem commute_uC_finRep (u : UC E n) (k : GL (Fin n) (Af E)) : Commute (uC E n u) (finRep E n k) := by
  have hu : u ∈ Algebra.adjoin ℂ {x : UC E n | ∃ τ i j, x = genC τ i j} := by rw [adjoin_genC]; trivial
  refine Algebra.adjoin_induction (p := fun x _ => Commute (uC E n x) (finRep E n k)) ?_
    (fun r => by rw [AlgHom.commutes]; exact Algebra.commutes r _)
    (fun _ _ _ _ hx hy => by rw [map_add]; exact hx.add_left hy)
    (fun _ _ _ _ hx hy => by rw [map_mul]; exact hx.mul_left hy) hu
  rintro _ ⟨τ, i, j, rfl⟩
  have h : ∀ i j x, Commute (lieS E n i j x) (finRep E n k) := fun i j x => lie_rt_fin _ k
  rw [uC_genC]
  exact ((h i j _).sub_left ((h i j _).smul_left _)).smul_left _

theorem commute_center_rt_infGL {u : UC E n} (hu : u ∈ Subalgebra.center ℂ (UC E n)) (y : GL (Fin n) (Cinf E)) :
    Commute (uC E n u) (rt E n (infGL E n y)) := by
  rw [center_UC] at hu
  refine Algebra.adjoin_induction (p := fun x _ => Commute (uC E n x) (rt E n (infGL E n y))) ?_
    (fun r => by rw [AlgHom.commutes]; exact Algebra.commutes r _)
    (fun _ _ _ _ hx hy => by rw [map_add]; exact hx.add_left hy)
    (fun _ _ _ _ hx hy => by rw [map_mul]; exact hx.mul_left hy) hu
  rintro _ ⟨τ, u, rfl⟩
  rw [uC_capC]
  exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E n τ u _

private theorem sph_of {x : Module.End ℂ (Sm E n)} (h : ∀ k, Commute x (finRep E n k)) {φ : Sm E n} (hφ : Sph S φ) :
    Sph S (x φ) := fun w hw k hk => by
  have h1 : finRep E n (locGL E n w k) φ = φ := hφ w hw k hk
  have := LinearMap.congr_fun (h (locGL E n w k)).eq φ
  rw [Module.End.mul_apply, Module.End.mul_apply, h1] at this
  exact this.symm

def bsp (S : Set (Pl E)) (n : ℕ) {C : ℝ} (hC : 0 ≤ C) : Submodule ℂ (Sm E n) where
  carrier := {φ | Band C φ ∧ Sph S φ}
  zero_mem' := ⟨(bandOps E n C hC).1, fun _ _ _ _ => map_zero _⟩
  add_mem' {φ ψ} hφ hψ := ⟨((bandOps E n C hC).2 φ hφ.1).1 ψ hψ.1, fun w hw k hk => by
    rw [map_add, hφ.2 w hw k hk, hψ.2 w hw k hk]⟩
  smul_mem' c φ hφ := ⟨((bandOps E n C hC).2 φ hφ.1).2.1 c, fun w hw k hk => by rw [map_smul, hφ.2 w hw k hk]⟩

def cmp (d : Dat S n) {C : ℝ} (hC : 0 ≤ C) : bsp S n hC →ₗ[ℂ] ((Fin d.len → ℝ) → ℂ) where
  toFun φ := d.comp φ.1.1
  map_add' φ ψ := funext fun t => by
    simpa using (compBound E S n d).2 φ.1 ψ.1 1 φ.2.1.toUmg ψ.2.1.toUmg t
  map_smul' c φ := funext fun t => by
    have h0 : Umg (0 : Sm E n) := (bandOps E n C hC).1.toUmg
    have h1 := (compBound E S n d).2 0 0 1 h0 h0 t
    have h2 := (compBound E S n d).2 φ.1 0 c φ.2.1.toUmg h0 t
    rw [one_smul, add_zero, one_mul, left_eq_add] at h1
    rw [add_zero, h1, add_zero] at h2
    exact h2

def Dat.lamR (d : Dat S n) (p : (E →+* ℂ) × Fin n) : ℂ := d.lam p.1 p.2 + (d.rho (d.idx p.2) : ℂ)

def Dat.hEP (d : Dat S n) (k : Pl E × Fin n) : EP (Fin d.len) :=
  ∑ a ∈ Finset.piAntidiag Finset.univ ((k.2 : ℕ) + 1),
    AddMonoidAlgebra.single (-fun l => a l * Real.log (Formalism.UG.qV E k.1))
      (MvPolynomial.C (∏ l, ((d.sat l k.1).map fun x : ℂˣ => (x : ℂ)).esymm (a l) * qc k.1 ^ (-(d.rho l : ℂ) * a l)))

private def ops (d : Dat S n) : Set (Module.End ℂ (Sm E n)) :=
  {x | (∃ u ∈ Subalgebra.center ℂ (UC E n), x = uC E n u) ∨ (∃ j, x = d.J j) ∨ (∃ v, x = rt E n (d.tr v)) ∨
    ∃ w ∉ S, ∃ j, x = hk n w j}

private theorem ops_mem (d : Dat S n) {C : ℝ} (hC : 0 ≤ C) : ∀ x ∈ ops d, ∀ v ∈ bsp S n hC, x v ∈ bsp S n hC := by
  obtain ⟨-, -, -, -, -, -, hinf, -, -, hJ⟩ := (datBasics E).2 S n d
  rintro x hx φ ⟨hb, hs⟩
  obtain ⟨-, -, b1, b2, b3⟩ := (bandOps E n C hC).2 φ hb
  rcases hx with ⟨u, -, rfl⟩ | ⟨j, rfl⟩ | ⟨v, rfl⟩ | ⟨w, hw, j, rfl⟩
  · exact ⟨b1 u, sph_of (commute_uC_finRep u) hs⟩
  · obtain ⟨u, hu⟩ := hJ j
    rw [hu]
    exact ⟨b1 u, sph_of (commute_uC_finRep u) hs⟩
  · refine ⟨b2 _, sph_of (fun k => ?_) hs⟩
    obtain ⟨y, hy⟩ := hinf v
    rw [hy]
    exact (show Commute (infGL E n y) (finGL E n k) from infGL_comm y k).map (rt E n)
  · exact ⟨b3 w j, ((hkOps E n w j).2.2.2 S φ hw hs).1⟩

private theorem ops_comm (d : Dat S n) {C : ℝ} (hC : 0 ≤ C) :
    ∀ x ∈ ops d, ∀ y ∈ ops d, ∀ v ∈ bsp S n hC, x (y v) = y (x v) := by
  obtain ⟨-, -, -, -, -, hadd, hinf, hJJ, hJt, hJ⟩ := (datBasics E).2 S n d
  have zu : ∀ u ∈ Subalgebra.center ℂ (UC E n), ∀ u', Commute (uC E n u) (uC E n u') := fun u hu u' =>
    (show Commute u u' from (Subalgebra.mem_center_iff.1 hu u').symm).map (uC E n)
  have zJ : ∀ u ∈ Subalgebra.center ℂ (UC E n), ∀ j, Commute (uC E n u) (d.J j) := fun u hu j => by
    obtain ⟨u', h⟩ := hJ j
    rw [h]; exact zu u hu u'
  have zt : ∀ u ∈ Subalgebra.center ℂ (UC E n), ∀ v, Commute (uC E n u) (rt E n (d.tr v)) := fun u hu v => by
    obtain ⟨y, h⟩ := hinf v
    rw [h]; exact commute_center_rt_infGL hu y
  have Jh : ∀ j w i, Commute (d.J j) (hk n w i) := fun j w i => by
    obtain ⟨u', h⟩ := hJ j
    rw [h]; exact (hkOps E n w i).2.1 u'
  have th : ∀ v w i, Commute (rt E n (d.tr v)) (hk n w i) := fun v w i => by
    obtain ⟨y, h⟩ := hinf v
    rw [h]; exact (hkOps E n w i).2.2.1 y
  have tt : ∀ v v', Commute (rt E n (d.tr v)) (rt E n (d.tr v')) := fun v v' =>
    (show Commute (d.tr v) (d.tr v') by rw [Commute, SemiconjBy, ← hadd, ← hadd, add_comm]).map (rt E n)
  have ap : ∀ {x y : Module.End ℂ (Sm E n)}, Commute x y → ∀ φ, x (y φ) = y (x φ) := fun h φ =>
    LinearMap.congr_fun h.eq φ
  rintro x hx y hy φ ⟨-, hs⟩
  rcases hx with ⟨u, hu, rfl⟩ | ⟨j, rfl⟩ | ⟨v, rfl⟩ | ⟨w, hw, j, rfl⟩ <;>
    rcases hy with ⟨u', hu', rfl⟩ | ⟨j', rfl⟩ | ⟨v', rfl⟩ | ⟨w', hw', j', rfl⟩
  exacts [ap (zu u hu u') φ, ap (zJ u hu j') φ, ap (zt u hu v') φ, ap ((hkOps E n w' j').2.1 u) φ,
    ap (zJ u' hu' j).symm φ, ap (hJJ j j') φ, ap (hJt j v') φ, ap (Jh j w' j') φ,
    ap (zt u' hu' v).symm φ, ap (hJt j' v).symm φ, ap (tt v v') φ, ap (th v w' j') φ,
    ap ((hkOps E n w j).2.1 u').symm φ, ap (Jh j' w j).symm φ, ap (th v' w j).symm φ,
    ((hkOps E n w j).2.2.2 S φ hw hs).2.2.2 w' hw' j']

theorem exists_sys (d : Dat S n) {C : ℝ} (hC : 0 ≤ C) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra ℂ A) (_ : Module A (bsp S n hC)) (_ : IsScalarTower ℂ A (bsp S n hC))
      (Z : (E →+* ℂ) × Fin n → A) (H : Pl E × Fin n → A) (I : Fin d.len → A) (t : Multiplicative (Fin d.len → ℝ) →* A),
      (∀ (P : MvPolynomial ((E →+* ℂ) × Fin n) ℂ) (v : bsp S n hC),
        ((MvPolynomial.aeval Z P • v : bsp S n hC) : Sm E n) = zop P v) ∧
      (∀ k : Pl E × Fin n, k.1 ∉ S → ∀ v : bsp S n hC, ((H k • v : bsp S n hC) : Sm E n) = hk n k.1 (k.2 + 1) v) ∧
      AbsSys Z H I t (cmp d hC) d.idx d.lamR d.hEP {k | k.1 ∉ S} C := by
  classical
  obtain ⟨hsurj, -, -, -, h0, hadd, -, -, -, hJ⟩ := (datBasics E).2 S n d
  obtain ⟨A, _, _, _, _, hex, hf⟩ := exists_alg (bsp S n hC) (ops d) (ops_mem d hC) (ops_comm d hC)
  choose z hz using fun (τ : E →+* ℂ) (i : ℕ) => hex _ (Or.inl ⟨zC E n τ i, zC_mem τ i, rfl⟩)
  choose I hI using fun j => hex _ (Or.inr (Or.inl ⟨j, rfl⟩))
  choose T hT using fun v => hex _ (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩)))
  choose H' hH' using fun (w : Pl E) (hw : w ∉ S) (j : ℕ) => hex _ (Or.inr (Or.inr (Or.inr ⟨w, hw, j, rfl⟩)))
  let t : Multiplicative (Fin d.len → ℝ) →* A :=
    { toFun := fun v => T v.toAdd
      map_one' := hf _ _ fun v => Subtype.ext (by rw [hT, toAdd_one, h0, map_one, one_smul]; rfl)
      map_mul' := fun a b => hf _ _ fun v => Subtype.ext (by
        rw [mul_smul, hT, hT, hT, toAdd_mul, hadd, map_mul]; rfl) }
  have hc : ∀ v : bsp S n hC, cmp d hC v = d.comp (v : Sm E n).1 := fun _ => rfl
  have hZ : ∀ (P : MvPolynomial ((E →+* ℂ) × Fin n) ℂ) (v : bsp S n hC),
      ((MvPolynomial.aeval (fun p : (E →+* ℂ) × Fin n => z p.1 (p.2 + 1)) P • v : bsp S n hC) : Sm E n) = zop P v := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      intro v
      rw [MvPolynomial.aeval_C, algebraMap_smul, zop, MvPolynomial.algHom_C, Subalgebra.coe_algebraMap, AlgHom.commutes]
      rfl
    | add p q hp hq =>
      intro v
      rw [map_add, add_smul, Submodule.coe_add, hp, hq]
      simp only [zop, map_add, Subalgebra.coe_add, LinearMap.add_apply]
    | mul_X p q hp =>
      intro v
      rw [map_mul, mul_smul, hp, MvPolynomial.aeval_X, hz]
      simp only [zop, evZ, map_mul, Subalgebra.coe_mul, MvPolynomial.aeval_X, Module.End.mul_apply]
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, fun p => z p.1 (p.2 + 1),
    fun k => if h : k.1 ∉ S then H' k.1 h (k.2 + 1) else 0, I, t, hZ, fun k hk v => by beta_reduce; rw [dif_pos hk, hH'],
    hsurj, fun v φ x => ?_, fun j φ x => ?_, fun p φ => ?_, fun k hk φ => ?_, fun φ β R => ?_⟩
  · rw [hc, hc]
    exact (congrArg (fun ψ : Sm E n => d.comp ψ.1 x) (hT v φ)).trans ((compShift E S n d φ x φ.2.1.toUmg).1 v)
  · rw [hc, hc, hI]
    exact (compShift E S n d φ x φ.2.1.toUmg).2 j
  · obtain ⟨τ, i⟩ := p
    let X : Fin n → A := fun i => algebraMap ℂ A (d.lamR (τ, i)) + I (d.idx i)
    have key : ∀ u : ℂ, ∑ k ∈ Finset.range (n + 1), u ^ (n - k) • cmp d hC (z τ k • φ) =
        ∑ k ∈ Finset.range (n + 1), u ^ (n - k) •
          cmp d hC (MvPolynomial.aeval X (MvPolynomial.esymm (Fin n) ℂ k) • φ) := fun u => by
      have e1 : (((∑ k ∈ Finset.range (n + 1), u ^ (n - k) • z τ k) • φ : bsp S n hC) : Sm E n) = cap τ u φ := by
        rw [← uC_capC, ((zSpec E) n τ).2 u, map_sum, Finset.sum_smul, Submodule.coe_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_assoc, Submodule.coe_smul, hz, map_smul, LinearMap.smul_apply]
      have e2 := ofFn_rel n (fun i => algebraMap ℂ A u + X i) (fun i : Fin n =>
        algebraMap ℂ (Module.End ℂ (Sm E n)) (u + d.lam τ i + (d.rho (d.idx i) : ℂ)) + d.J (d.idx i))
        (fun i v => by
          simp only [X, Dat.lamR, add_smul, algebraMap_smul, Submodule.coe_add, Submodule.coe_smul, hI,
            LinearMap.add_apply, Module.algebraMap_end_apply, add_assoc]) φ
      have e3 := compCap E S n d φ τ u φ.2.1.toUmg
      rw [← e1, ← e2, ← hc, ← hc, prod_add_esymm] at e3
      simpa only [Finset.sum_smul, smul_assoc, map_sum, map_smul] using e3
    have e : MvPolynomial.aeval (fun q : (E →+* ℂ) × Fin n => algebraMap ℂ A (d.lamR q) + I (d.idx q.2)) (blockE (τ, i)) =
        MvPolynomial.aeval X (MvPolynomial.esymm (Fin n) ℂ (i + 1)) := by
      rw [blockE, MvPolynomial.aeval_rename]; rfl
    rw [e]
    funext x
    refine sub_eq_zero.1 (coef_zero n (fun k => cmp d hC (z τ k • φ) x -
      cmp d hC (MvPolynomial.aeval X (MvPolynomial.esymm (Fin n) ℂ k) • φ) x) (fun u => ?_) (k := i + 1) i.2)
    have := congrFun (key u) x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [mul_sub, Finset.sum_sub_distrib, this, sub_self]
  · have hk' : k.1 ∉ S := hk
    funext x
    rw [dif_pos hk', hc, hH', compHecke E S n d φ k.1 (k.2 + 1) x φ.2.1.toUmg φ.2.2 hk' k.2.2, Dat.hEP, map_sum,
      Finset.sum_smul, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    have e : ∀ (v : Fin d.len → ℝ) (c : ℂ), lift I t (AddMonoidAlgebra.single v (MvPolynomial.C c)) =
        algebraMap ℂ A c * T v := fun v c => by
      simp [lift, AddMonoidAlgebra.liftNCRingHom, t]
    rw [e, mul_smul, algebraMap_smul, map_smul, Pi.smul_apply, smul_eq_mul, hc, hT,
      (compShift E S n d φ x φ.2.1.toUmg).1, sub_eq_add_neg]
  · obtain ⟨u, hu⟩ : ∃ u, ∀ v : bsp S n hC, (((β.prod fun j e => I j ^ e) • v : bsp S n hC) : Sm E n) = uC E n u v := by
      have hm : ∀ a b : A, (∃ u, ∀ v : bsp S n hC, ((a • v : bsp S n hC) : Sm E n) = uC E n u v) →
          (∃ u, ∀ v : bsp S n hC, ((b • v : bsp S n hC) : Sm E n) = uC E n u v) →
          ∃ u, ∀ v : bsp S n hC, (((a * b) • v : bsp S n hC) : Sm E n) = uC E n u v := by
        rintro a b ⟨u, hu⟩ ⟨u', hu'⟩
        exact ⟨u * u', fun v => by rw [mul_smul, hu, hu', map_mul]; rfl⟩
      have h1 : ∃ u, ∀ v : bsp S n hC, (((1 : A) • v : bsp S n hC) : Sm E n) = uC E n u v :=
        ⟨1, fun v => by rw [one_smul, map_one]; rfl⟩
      refine Finset.prod_induction _
        (fun a : A => ∃ u, ∀ v : bsp S n hC, ((a • v : bsp S n hC) : Sm E n) = uC E n u v) hm h1 fun j _ => ?_
      beta_reduce
      generalize β j = e
      induction e with
      | zero => rw [pow_zero]; exact h1
      | succ e ih =>
        rw [pow_succ]
        obtain ⟨u, hu⟩ := hJ j
        exact hm _ _ ih ⟨u, fun v => by rw [hI, hu]⟩
    obtain ⟨N, hN⟩ := φ.2.1.band
    obtain ⟨B, hB⟩ := hN u
    obtain ⟨C', R', hb⟩ := (compBound E S n d).1 N
    refine ⟨|C' * B| * Real.exp (|R'| * R), fun α x hx => ?_⟩
    have e : (α.prod fun p e => z p.1 (p.2 + 1) ^ e) =
        MvPolynomial.aeval (fun p : (E →+* ℂ) × Fin n => z p.1 (p.2 + 1)) (MvPolynomial.monomial α (1 : ℂ)) := by
      rw [MvPolynomial.aeval_monomial, map_one, one_mul]
    rw [e, mul_comm (MvPolynomial.aeval _ _), mul_smul, hc]
    refine (hb _ (B * C ^ α.degree) (Subtype.prop (_ : bsp S n hC)).1.toUmg (fun g => ?_) x).trans ?_
    · rw [hu, hZ]; exact hB α g
    · have h1 : Real.exp (R' * ‖x‖) ≤ Real.exp (|R'| * R) := Real.exp_le_exp.2
        (mul_le_mul (le_abs_self _) hx (norm_nonneg _) (abs_nonneg _))
      have h2 : 0 ≤ C ^ α.degree := pow_nonneg hC _
      calc C' * (B * C ^ α.degree) * Real.exp (R' * ‖x‖) = C' * B * Real.exp (R' * ‖x‖) * C ^ α.degree := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul (le_abs_self _) h1 (Real.exp_pos _).le (abs_nonneg _)) h2

end UpperTheory.ConvolutionTheory.BW
