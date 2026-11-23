import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSumRowCol
import Formalism.LocalToGlobal.IndefiniteReal.DatumLemmas

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

noncomputable section
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatUnip

def lo {ρ c : ℕ} (h : c = 2 * ρ) (i : Fin ρ) : Fin c := ⟨i.val, by omega⟩

def hi {ρ c : ℕ} (h : c = 2 * ρ) (i : Fin ρ) : Fin c := ⟨2 * ρ - 1 - i.val, by omega⟩

theorem lo_hi_bij {ρ c : ℕ} (h : c = 2 * ρ) : Function.Bijective (Sum.elim (lo h) (hi h)) := by
  constructor
  · rintro (a | a) (b | b) e <;> simp only [lo, hi, Fin.ext_iff, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq] at e ⊢ <;> omega
  · intro l
    by_cases hl : l.val < ρ
    · exact ⟨.inl ⟨l, hl⟩, rfl⟩
    · exact ⟨.inr ⟨2 * ρ - 1 - l, by omega⟩, Fin.ext (by simp only [hi, Sum.elim_inr]; omega)⟩

theorem sum_lo_hi {M : Type} [AddCommMonoid M] {ρ c : ℕ} (h : c = 2 * ρ) (f : Fin c → M) :
    ∑ l, f l = ∑ i, f (lo h i) + ∑ i, f (hi h i) := by
  rw [← (lo_hi_bij h).sum_comp f, Fintype.sum_sum_type]; rfl

theorem frame_mul {k : Type} [Field k] {m ρ c : ℕ} {n : Type} [Fintype n] [DecidableEq n] (h : c = 2 * ρ) (ξ s t : k)
    (hξ : ξ ≠ 0) (M : Matrix (Fin m) (Fin m) k) (E E' : Matrix (Fin m) (Fin ρ) k) (β : Matrix (Fin m) (n ⊕ Fin c) k)
    (u : Matrix (Fin c) (Fin c) k) (hu : ∀ l l', l' < l → u l l' = 0)
    (hb : ∀ l l' : Fin c, l.val < ρ → ρ ≤ l'.val → u l l' = 0)
    (h0 : ∀ r a, (M * β) r (.inl a) = β r (.inl a))
    (hlo : ∀ i r, β r (.inr (lo h i)) = s * ξ ^ (ρ - i.val) * E r i)
    (hhi : ∀ i r, β r (.inr (hi h i)) = t * (-1 / ξ) ^ (ρ - 1 - i.val) * E' r i)
    (hE : M * E = E * Matrix.of fun i j => u (lo h i) (lo h j) * ξ ^ (j.val - i.val))
    (hE' : M * E' = E' * Matrix.of fun i j => u (hi h i) (hi h j) * (-ξ) ^ (i.val - j.val)) :
    M * β = β * (fromBlocks 1 0 0 u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) := by
  ext r x
  rcases x with a | l
  · rw [h0, Matrix.mul_apply, Fintype.sum_sum_type]; simp [Matrix.one_apply]
  have e : (β * (fromBlocks 1 0 0 u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r (.inr l) = ∑ l', β r (.inr l') * u l' l := by
    rw [Matrix.mul_apply, Fintype.sum_sum_type]; simp
  rw [e, sum_lo_hi h]
  obtain ⟨j | j, rfl⟩ := (lo_hi_bij h).2 l
  · simp only [Sum.elim_inl]
    have e1 : (M * β) r (.inr (lo h j)) = s * ξ ^ (ρ - j.val) * (M * E) r j := by
      simp only [Matrix.mul_apply, hlo, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, hE, Finset.sum_eq_zero (s := Finset.univ) (f := fun i => β r (.inr (hi h i)) * u (hi h i) (lo h j))
      fun i _ => by rw [hu _ _ (by simp only [lo, hi, Fin.lt_def]; omega), mul_zero], add_zero, Matrix.mul_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hlo, Matrix.of_apply]
    by_cases hij : i.val ≤ j.val
    · rw [show ρ - i.val = (ρ - j.val) + (j.val - i.val) by omega, pow_add]; ring
    · rw [hu _ _ (by simp only [lo, Fin.lt_def]; omega)]; ring
  · simp only [Sum.elim_inr]
    have e1 : (M * β) r (.inr (hi h j)) = t * (-1 / ξ) ^ (ρ - 1 - j.val) * (M * E') r j := by
      simp only [Matrix.mul_apply, hhi, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, hE', Finset.sum_eq_zero (s := Finset.univ) (f := fun i => β r (.inr (lo h i)) * u (lo h i) (hi h j))
      fun i _ => by rw [hb _ _ (by simp only [lo]; omega) (by simp only [hi]; omega), mul_zero], zero_add, Matrix.mul_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hhi, Matrix.of_apply]
    by_cases hij : j.val ≤ i.val
    · have e2 : (-1 / ξ) ^ (i.val - j.val) * (-ξ) ^ (i.val - j.val) = 1 := by
        rw [← mul_pow, show -1 / ξ * -ξ = 1 by field_simp, one_pow]
      rw [show ρ - 1 - j.val = (ρ - 1 - i.val) + (i.val - j.val) by omega, pow_add]
      linear_combination (t * (-1 / ξ) ^ (ρ - 1 - i.val) * E' r i * u (hi h i) (hi h j)) * e2
    · rw [hu _ _ (by simp only [hi, Fin.lt_def]; omega)]; ring

theorem simpleSum_split {k : Type} [Field k] {ρ c : ℕ} (n : Type) [Fintype n] [DecidableEq n] (h : c = 2 * ρ)
    (u : GL (Fin c) k) (hb : ∀ l l' : Fin c, l.val < ρ → ρ ≤ l'.val → u.val l l' = 0) :
    GlobalTheory.RootEx.simpleSum (GlobalTheory.RootEx.embA n u) =
      (∑ i : Fin ρ, ∑ j : Fin ρ, if j.val = i.val + 1 then u.val (lo h i) (lo h j) else 0) +
        ∑ i : Fin ρ, ∑ j : Fin ρ, if j.val = i.val + 1 then u.val (hi h j) (hi h i) else 0 := by
  change (∑ i : Fin c, ∑ j : Fin c, if j.val = i.val + 1 then u.val i j else 0) = _
  rw [sum_lo_hi h]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_lo_hi h, Finset.sum_eq_zero (s := Finset.univ)
      (f := fun j => if (hi h j).val = (lo h i).val + 1 then u.val (lo h i) (hi h j) else 0)
      fun j _ => by rw [hb _ _ (by simp only [lo]; omega) (by simp only [hi]; omega), ite_self], add_zero]
    rfl
  · rw [Finset.sum_comm (f := fun i j : Fin ρ => if j.val = i.val + 1 then u.val (hi h j) (hi h i) else 0)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_lo_hi h, Finset.sum_eq_zero (s := Finset.univ)
      (f := fun j => if (lo h j).val = (hi h i).val + 1 then u.val (hi h i) (lo h j) else 0)
      fun j _ => if_neg (by simp only [lo, hi]; omega), zero_add]
    exact Finset.sum_congr rfl fun j _ => if_congr (by simp only [hi]; omega) rfl rfl

theorem det_of_inN {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
    {g : GL (n ⊕ Fin c) F} (hg : InN p g) : Matrix.GeneralLinearGroup.det g = 1 := by
  apply Units.ext
  change g.val.det = 1
  rw [(GlobalTheory.RootEx.Model.inN_tri hg).det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : g.val.toSquareBlock (lev p) a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    rw [hg i j (by rw [hi, hj]), Matrix.one_apply, Matrix.one_apply]
    simp [Subtype.ext_iff]
  rw [this, det_one]

variable {D : D7}

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem jacT_levi (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (y : Mx D S.rank ρ)
    (a : GL (Fin ρ) (AE D)) (f : WO S T₀ → ℂ) : jacT ψ d S y (d.levi a) f = f := by
  have e : ∃ η, HMul.hMul (mt T (d.levi a)⁻¹) (d.incAdj S y : Mx D T.rank S.rank) = d.incY S η := by
    rw [← map_inv, d.incAdj_apply, d.incY_apply, ← Matrix.mul_assoc, d.levi_jY, Matrix.mul_assoc]
    exact ⟨_, rfl⟩
  obtain ⟨η, e⟩ := e
  rw [jacT, cenT, ptT, e, d.incAdj_apply, d.symplOH_incY_incY, d.incY_apply, ← Matrix.mul_assoc, d.p0_jY, Matrix.zero_mul,
    heisO_zero, AddChar.map_zero_eq_one, one_smul]

theorem grpAt_of_suppAt {e : AE D} (he : IsSplitIdem D e) {S : HSp D} {g : GA D S} (hg : SuppAt e S g) :
    g ∈ GlobalTheory.FinPl.grpAt S (fun _ => True) := by
  obtain ⟨-, -, v, ε, ⟨α, rfl, -⟩, hε⟩ := he
  rw [GlobalTheory.FinPl.grpAt, GlobalTheory.FinPl.congGrp, MonoidHom.mem_ker]
  ext i j
  change Ideal.Quotient.mk _ (mt S g i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) _) i j
  rw [← Matrix.map_one (Ideal.Quotient.mk (GlobalTheory.FinPl.idAt D fun _ => True)) (map_zero _) (map_one _), Matrix.map_apply,
    Ideal.Quotient.eq]
  refine ⟨?_, Ideal.mem_iInf.2 fun w => (w.2 trivial).elim⟩
  change infPart D ((mt S g - 1) i j) = 0
  rw [← hg i j, map_mul, hε]
  have : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := TensorProduct.zero_tmul _ _
  rw [this, zero_mul]

theorem exists_lift {k : Type} [Field k] {ρ : ℕ} (f : k →+ AE D) (α : Matrix (Fin ρ) (Fin ρ) k)
    (h0 : ∀ i j, j < i → α i j = 0) (h1 : ∀ i, α i i = 1) :
    ∃ a ∈ UX D ρ, (∀ i j, a.val i j = (1 : Mx D ρ ρ) i j + f ((α - 1) i j)) ∧
      upSum a.val = f (∑ i : Fin ρ, ∑ j : Fin ρ, if j.val = i.val + 1 then α i j else 0) := by
  let U : Mx D ρ ρ := Matrix.of fun i j => (1 : Mx D ρ ρ) i j + f ((α - 1) i j)
  have u0 : ∀ i j, j < i → U i j = 0 := fun i j h => by
    simp [U, h0 i j h, Matrix.one_apply_ne h.ne']
  have u1 : ∀ i, U i i = 1 := fun i => by simp [U, h1]
  have hU : IsUnit U := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_upperTriangular (fun i j h => u0 i j h)]
    simp [u1]
  refine ⟨hU.unit, fun i j => ⟨u0 i j, u1 i⟩, fun _ _ => rfl, ?_⟩
  simp only [upSum, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · have : i ≠ j := fun e => by rw [e] at h; omega
    simp [U, Matrix.one_apply_ne this]
  · simp

theorem map_inv_one {A B : Type} [CommRing A] [CommRing B] {ρ : ℕ} (φ : A →+* B) (a : GL (Fin ρ) A)
    (h : a.val.map φ = 1) : (a⁻¹).val.map φ = 1 := by
  have := congrArg (fun x => x.map φ) a.mul_inv
  simp only [Matrix.map_mul, h, Matrix.one_mul] at this
  rw [this, Matrix.map_one _ (map_zero _) (map_one _)]

theorem smul_inv_one {A : Type} [CommRing A] {ρ : ℕ} (η : A) (a : GL (Fin ρ) A)
    (h : η • a.val = η • 1) : η • (a⁻¹).val = η • 1 := by
  have := congrArg (· * (a⁻¹).val) h
  simp only [Matrix.smul_mul, Matrix.one_mul, Units.mul_inv] at this
  exact this.symm

theorem smul_div_one {A : Type} [CommRing A] {ρ : ℕ} (η : A) (a b : GL (Fin ρ) A)
    (ha : η • a.val = η • 1) (hb : η • b.val = η • 1) : η • (a * b⁻¹).val = η • 1 := by
  rw [Units.val_mul, ← Matrix.smul_mul, ha, Matrix.smul_mul, Matrix.one_mul, smul_inv_one _ _ hb]

theorem smul_three {A : Type} [CommRing A] {ρ m : ℕ} (η : A) (x y : Matrix (Fin m) (Fin ρ) A) (x' y' : Matrix (Fin ρ) (Fin m) A)
    (z : Matrix (Fin m) (Fin m) A) (a b : Matrix (Fin ρ) (Fin ρ) A) (ha : η • a = η • 1) (hb : η • b = η • 1)
    (h : x * x' + z + y * y' = 1) : η • (x * a * x' + z + y * b * y') = η • 1 := by
  have e (x : Matrix (Fin m) (Fin ρ) A) (x' : Matrix (Fin ρ) (Fin m) A) (a : Matrix (Fin ρ) (Fin ρ) A)
      (ha : η • a = η • 1) : η • (x * a * x') = η • (x * x') := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ha, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [← h, smul_add, smul_add, smul_add, smul_add, e x x' a ha, e y y' b hb]

theorem suppAt_levi {e : AE D} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : GL (Fin ρ) (AE D))
    (h : (1 - (e + cA D e)) • a.val = (1 - (e + cA D e)) • 1) : SuppAt e S (d.levi a) := by
  have hc : cA D (1 - (e + cA D e)) = 1 - (e + cA D e) := by
    rw [map_sub, map_add, map_one, GlobalTheory.DualPairCheck.cA_cA, add_comm]
  generalize hη : 1 - (e + cA D e) = η at h hc
  have h2 : η • adj (a⁻¹).val = η • 1 := by
    rw [← hc, ← adj_smul, smul_inv_one η a h, adj_smul, adj_one]
  have h3 : η • mt S (d.levi a) = η • 1 := by
    rw [d.mt_levi]
    exact smul_three η _ _ _ _ _ _ _ h h2 d.sum_eq_one
  intro i j
  have h4 := congrFun (congrFun h3 i) j
  simp only [Matrix.smul_apply, smul_eq_mul, ← hη] at h4
  rw [Matrix.sub_apply]
  linear_combination (-1 : AE D) * h4

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem π_c_ι (x : k) : p.π (cA D (p.ι x)) = 0 := by
  have h1 : p.π p.e = 1 := by rw [← GlobalTheory.LocChar.ι_one, p.π_ι]
  have h2 := congrArg p.π p.split.2.1
  rw [map_mul, h1, one_mul, map_zero] at h2
  rw [← GlobalTheory.LocChar.e_mul_ι, map_mul, map_mul, h2, zero_mul]

theorem eta_ι (x : k) : (1 - (p.e + cA D p.e)) * p.ι x = 0 := by
  have h1 := GlobalTheory.LocChar.e_mul_ι p x
  have h2 := p.split.2.1
  linear_combination (cA D p.e - 1) * h1 - p.ι x * h2

theorem eta_c_ι (x : k) : (1 - (p.e + cA D p.e)) * cA D (p.ι x) = 0 := by
  have := congrArg (cA D) (eta_ι p x)
  rwa [map_mul, map_zero, map_sub, map_add, map_one, GlobalTheory.DualPairCheck.cA_cA, add_comm] at this

theorem psiE_ι {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (h : p.IsChar ψ ψk) (x : k) :
    psiE ψ (p.ι (p.xi * x)) = ψk x := by
  rw [h x, GlobalTheory.LocChar.ι_mul, Place.xi, Place.pr, p.ι_π, mul_comm p.e, mul_assoc, GlobalTheory.LocChar.e_mul_ι]

theorem one_map (φ : AE D →+* k) {ρ : ℕ} (i j : Fin ρ) : φ ((1 : Mx D ρ ρ) i j) = (1 : Matrix (Fin ρ) (Fin ρ) k) i j := by
  rw [← Matrix.map_one φ (map_zero _) (map_one _), Matrix.map_apply]

theorem map_div_one {A B : Type} [CommRing A] [CommRing B] {ρ : ℕ} (φ : A →+* B) (a b : GL (Fin ρ) A)
    (α : Matrix (Fin ρ) (Fin ρ) B) (ha : a.val.map φ = α) (hb : b.val.map φ = 1) : (a * b⁻¹).val.map φ = α := by
  rw [Units.val_mul, Matrix.map_mul, ha, map_inv_one _ _ hb, Matrix.mul_one]

theorem map_mul_of_eq {A B : Type} [CommRing A] [CommRing B] {m l r : ℕ} (φ : A →+* B) {M : Matrix (Fin m) (Fin m) A}
    {x : Matrix (Fin m) (Fin l) A} {y : Matrix (Fin m) (Fin r) A} {a : Matrix (Fin r) (Fin l) A} (h : M * x = y * a) :
    M.map φ * x.map φ = y.map φ * a.map φ := by
  rw [← Matrix.map_mul, h, Matrix.map_mul]

theorem psiE_cA (ψ : AddChar (AF D.host.F) ℂ) (x : AE D) : psiE ψ (cA D x) = psiE ψ x := by
  rw [psiE, psiE, Formalism.IndefR.Datum.Brg.trace_cA]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem psiFlag_div (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    {a b : GL (Fin ρ) (AE D)} (ha : a ∈ UX D ρ) (hb : b ∈ UX D ρ) {x y : k} (fa : psiFlag ψ d (d.levi a) = ψk x)
    (fb : psiFlag ψ d (d.levi b) = ψk (-y)) : psiFlag ψ d (d.levi (a * b⁻¹)) = ψk (x + y) := by
  have m := psiFlag_mul d ψ (d.levi_mem_NFlag (mul_mem ha (inv_mem hb) : a * b⁻¹ ∈ UX D ρ)) (d.levi_mem_NFlag hb)
  have hab : d.levi (a * b⁻¹) * d.levi b = d.levi a :=
    (d.levi.map_mul _ _).symm.trans (congrArg d.levi (inv_mul_cancel_right a b))
  rw [hab, fa, fb] at m
  refine mul_right_cancel₀ (Circle.coe_ne_zero _) (m.symm.trans ?_)
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel_right]

theorem levi_comp {ρ c : ℕ} (J : JacLev D ρ)
    (s hh : k) {n : Type} [Fintype n] [DecidableEq n] (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c))
    (hJ : p.IsJacFrame J s hh G₀ FW) (u : GL (Fin c) k) (h0 : ∀ l l', l' < l → u.val l l' = 0)
    (hb : ∀ l l' : Fin c, l.val < ρ → ρ ≤ l'.val → u.val l l' = 0) (a : GL (Fin ρ) (AE D))
    (h1 : a.val.map p.π = Matrix.of fun i j => u.val (lo hJ.1 i) (lo hJ.1 j) * p.xi ^ (j.val - i.val))
    (h2 : (a⁻¹).val.map (p.π.comp (cA D)) =
      (Matrix.of fun i j => u.val (hi hJ.1 i) (hi hJ.1 j) * (-p.xi) ^ (i.val - j.val))ᵀ) :
    (mt J.W (J.d.levi a)).map p.π = FW.β * (GlobalTheory.RootEx.embA n u).val * FW.γ := by
  have q1 := map_mul_of_eq p.π (J.d.levi_jX a)
  have q2 := map_mul_of_eq p.π (J.d.levi_jY a)
  have q3 := map_mul_of_eq p.π ((J.d.wittDecomp_levi_inclAnisotropic a).trans (Matrix.mul_one _).symm)
  have e2 : (adj (a⁻¹).val).map p.π = ((a⁻¹).val.map (p.π.comp (cA D)))ᵀ := rfl
  have e0 : J.d.j0.map p.π = J.d.i₀.map p.pr := rfl
  rw [h1] at q1
  rw [e2, h2, Matrix.transpose_transpose] at q2
  rw [e0, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at q3
  generalize (mt J.W (J.d.levi a)).map p.π = M at q1 q2 q3 ⊢
  obtain ⟨h, hI, hlo, hhi⟩ := hJ
  have key := frame_mul h p.xi s (s * (hh / p.xi)) (GlobalTheory.LocChar.xi_ne p) M
    (J.d.jX.map p.π) (J.d.jY.map p.π) FW.β u.val h0 hb ?_ (fun i r => hlo i _ rfl r)
    (fun i r => hhi i _ (by simp only [hi]; omega) r) q1 q2
  · rw [← Matrix.mul_one M, ← FW.βγ, ← Matrix.mul_assoc, key]; rfl
  · intro r x
    have e1 : M * (J.d.i₀.map p.pr * G₀.β) = J.d.i₀.map p.pr * G₀.β := by rw [← Matrix.mul_assoc, q3]
    rw [hI, ← e1, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun y _ => by rw [hI]

theorem exists_levi {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (hψ : p.IsChar ψ ψk) {ρ c : ℕ} (J : JacLev D ρ)
    (s hh : k) {n : Type} [Fintype n] [DecidableEq n] (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c))
    (hJ : p.IsJacFrame J s hh G₀ FW) (u : GL (Fin c) k) (h0 : ∀ l l', l' < l → u.val l l' = 0) (h1 : ∀ l, u.val l l = 1)
    (hb : ∀ l l' : Fin c, l.val < ρ → ρ ≤ l'.val → u.val l l' = 0) :
    ∃ a ∈ UX D ρ, p.IsLoc FW (J.d.levi a) (GlobalTheory.RootEx.embA n u) ∧
      psiFlag ψ J.d (J.d.levi a) = ψk (GlobalTheory.RootEx.simpleSum (GlobalTheory.RootEx.embA n u)) := by
  have h := hJ.1
  obtain ⟨α, hα⟩ : ∃ α : Matrix (Fin ρ) (Fin ρ) k,
    α = Matrix.of fun i j => u.val (lo h i) (lo h j) * p.xi ^ (j.val - i.val) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : Matrix (Fin ρ) (Fin ρ) k,
    δ = Matrix.of fun i j => u.val (hi h i) (hi h j) * (-p.xi) ^ (i.val - j.val) := ⟨_, rfl⟩
  obtain ⟨a, ha, ea, sa⟩ := exists_lift p.ι α
    (fun i j hij => by rw [hα, Matrix.of_apply, h0 _ _ (by simp only [lo, Fin.lt_def] at hij ⊢; omega), zero_mul])
    (fun i => by simp [hα, h1])
  obtain ⟨b, hb', eb, sb⟩ := exists_lift ((cA D).toAddMonoidHom.comp p.ι) δᵀ
    (fun i j hij => by
      rw [hδ, Matrix.transpose_apply, Matrix.of_apply, h0 _ _ (by simp only [hi, Fin.lt_def] at hij ⊢; omega), zero_mul])
    (fun i => by simp [hδ, h1])
  have eb' : ∀ i j, b.val i j = (1 : Mx D ρ ρ) i j + cA D (p.ι ((δᵀ - 1) i j)) := eb
  have a1 : a.val.map p.π = α := by
    ext i j; rw [Matrix.map_apply, ea, map_add, one_map, p.π_ι, Matrix.sub_apply, add_sub_cancel]
  have a2 : a.val.map (p.π.comp (cA D)) = 1 := by
    ext i j; rw [Matrix.map_apply, ea, map_add, one_map, RingHom.comp_apply, π_c_ι, add_zero]
  have b1 : b.val.map p.π = 1 := by
    ext i j; rw [Matrix.map_apply, eb', map_add, one_map, π_c_ι, add_zero]
  have b2 : b.val.map (p.π.comp (cA D)) = δᵀ := by
    ext i j
    rw [Matrix.map_apply, eb', map_add, one_map, RingHom.comp_apply, GlobalTheory.DualPairCheck.cA_cA, p.π_ι, Matrix.sub_apply,
      add_sub_cancel]
  have hm : a * b⁻¹ ∈ UX D ρ := mul_mem ha (inv_mem hb')
  refine ⟨a * b⁻¹, hm, ⟨suppAt_levi _ _ ?_, ?_⟩, ?_⟩
  · have a3 : (1 - (p.e + cA D p.e)) • a.val = (1 - (p.e + cA D p.e)) • 1 := by
      ext i j; rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, ea, mul_add, eta_ι, add_zero]
    have b3 : (1 - (p.e + cA D p.e)) • b.val = (1 - (p.e + cA D p.e)) • 1 := by
      ext i j; rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, eb', mul_add, eta_c_ι, add_zero]
    exact smul_div_one _ a b a3 b3
  · refine levi_comp p J s hh G₀ FW hJ u h0 hb _ ?_ ?_
    · rw [← hα]; exact map_div_one _ a b α a1 b1
    · rw [← hδ, _root_.mul_inv_rev, inv_inv]; exact map_div_one _ b a _ b2 a2
  · rw [simpleSum_split n h u hb]
    have fa : psiFlag ψ J.d (J.d.levi a) =
        ψk (∑ i : Fin ρ, ∑ j : Fin ρ, if j.val = i.val + 1 then u.val (lo h i) (lo h j) else 0) := by
      rw [psiFlag, blockX_levi, sa]
      refine (congrArg (fun x => psiE ψ (p.ι x)) ?_).trans (psiE_ι p hψ _)
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hij
      · rw [hα, Matrix.of_apply, show j.val - i.val = 1 by omega]; ring
      · rw [mul_zero]
    have fb : psiFlag ψ J.d (J.d.levi b) =
        ψk (-∑ i : Fin ρ, ∑ j : Fin ρ, if j.val = i.val + 1 then u.val (hi h j) (hi h i) else 0) := by
      have e3 : ∀ x, psiE ψ (((cA D).toAddMonoidHom.comp p.ι) x) = psiE ψ (p.ι x) := fun x => psiE_cA ψ (p.ι x)
      rw [psiFlag, blockX_levi, sb, e3]
      refine (congrArg (fun x => psiE ψ (p.ι x)) ?_).trans (psiE_ι p hψ _)
      simp only [← Finset.sum_neg_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hij
      · rw [hδ, Matrix.transpose_apply, Matrix.of_apply, show j.val - i.val = 1 by omega]; ring
      · rw [neg_zero, mul_zero]
    exact psiFlag_div ψ ψk J.d ha hb' fa fb

end GlobalTheory.FlatUnip

namespace GlobalTheory.FlatUnip

theorem flatBF_unip : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ u : GL (Fin c) k, GlobalTheory.RootEx.embA n u ∈ GlobalTheory.RootEx.N k n c (ρ + 1) → (∀ l l' : Fin c, l.val < ρ → ρ ≤ l'.val → u.val l l' = 0) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((GlobalTheory.RootEx.embA n u)⁻¹).val * t)) → flatBF st (Tm Φ') = (ψk (-GlobalTheory.RootEx.simpleSum (GlobalTheory.RootEx.embA n u)) : ℂ) • flatBF st (Tm Φ) := by
  intro D _ hLaws hOm k _ _ _ _ _ _ p ν _ ψ ψk hχ ρ B J st s _ n n' _ _ _ _ c FA F₀ FV G₀ FW _ _ hJac Tm hTm u hN hb Φ Φ' hΦ
  obtain ⟨-, -, -, -, hcomp⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ st.weil.std
  obtain ⟨μS, hμS⟩ := hcomp st.χV
  obtain ⟨μT, hμT⟩ := hcomp st.χW
  have hI := GlobalTheory.RootEx.Model.mem_N_iff.1 hN
  obtain ⟨a, ha, hloc, hpsi⟩ := exists_levi p hχ J s _ G₀ FW hJac u
    (fun l l' h => (hI (.inr l) (.inr l') (by simp only [lev, Sum.elim_inr]; omega)).trans
      (Matrix.one_apply_ne fun e => h.ne' (Sum.inr.inj e)))
    (fun l => (hI (.inr l) (.inr l) le_rfl).trans (Matrix.one_apply_eq _)) hb
  have hone : p.IsLoc FV (1 : GA D B.V) 1 := by
    refine ⟨fun i j => ?_, ?_⟩
    · rw [mt_one, sub_self, Matrix.zero_apply, mul_zero]
    · rw [mt_one, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one, Matrix.mul_one, FV.βγ]
  have h1 : st.om (1, J.d.levi a) (Tm Φ) = Tm Φ' := by
    refine hOm k p ψ B.V J.W st.χV st.χW st.om st.weil μS μT hμS hμT _ _ FV FW Tm hTm 1 1 _ _ hone hloc Φ Φ' ?_
    funext t
    rw [hΦ]
    simp [GlobalTheory.SplitWeil.om, det_of_inN hI, nabs]
  have h2 := ((hLaws ψ fun _ => True).1 ρ B J st).equiv (Tm Φ) (hTm.theta Φ) _ (J.d.levi_mem_NFlag ha)
    (grpAt_of_suppAt p.split hloc.1) 1 (one_mem _)
  rw [map_one, mul_one, h1, hpsi, GlobalTheory.MixPer.opA, jacT_levi] at h2
  rw [h2, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  change _ • st.om₀ 1 _ = _
  rw [map_one]; rfl

end GlobalTheory.FlatUnip

end
