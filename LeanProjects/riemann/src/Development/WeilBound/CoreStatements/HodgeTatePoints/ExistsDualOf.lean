import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsDerAt0
import Development.WeilBound.CoreStatements.HodgeTatePoints.FormMemLin
import ReciprocityTheory.DualLattices.PrimeHopfOrderOfAddEquiv
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelatedPairsOrbitalTermEq

open NumberField ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.GR GlobalTheory.CompanionTheory.Ar.Num.FamEx
open PositivityTheory.Xgn.TestGroupPoint
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Sgp

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def cz : (Fin n → 𝓞 E) →+ (Ix E n → ℤ) where
  toFun x m := (RingOfIntegers.basis E).repr (x m.1) m.2
  map_zero' := by ext m; simp
  map_add' x y := by ext m; simp

theorem cz_apply (x : Fin n → 𝓞 E) (m : Ix E n) : cz x m = (RingOfIntegers.basis E).repr (x m.1) m.2 := rfl

def co (p : ℕ) : (Fin n → 𝓞 E) →+ (Ix E n → ZMod p) where
  toFun x m := ((cz x m : ℤ) : ZMod p)
  map_zero' := by ext m; simp
  map_add' x y := by ext m; simp

theorem co_apply (p : ℕ) (x : Fin n → 𝓞 E) (m : Ix E n) : co p x m = ((cz x m : ℤ) : ZMod p) := rfl

theorem sum_cz (x : Fin n → 𝓞 E) : ∑ m, cz x m • dl m = x := by
  funext j
  rw [Finset.sum_apply, Fintype.sum_prod_type]
  simp only [dl, cz_apply, Pi.smul_apply, Pi.single_apply]
  simp only [smul_ite, smul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact (RingOfIntegers.basis E).sum_repr (x j)

theorem hom_eq {A : Type} [AddCommGroup A] (f : (Fin n → 𝓞 E) →+ A) (x : Fin n → 𝓞 E) :
    f x = ∑ m, cz x m • f (dl m) := by
  conv_lhs => rw [← sum_cz x]
  rw [map_sum]
  simp only [map_zsmul]

theorem cz_surj : Function.Surjective (cz (E := E) (n := n)) := fun z =>
  ⟨fun i => (RingOfIntegers.basis E).equivFun.symm fun j => z (i, j), by
    funext m
    rw [cz_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]⟩

theorem co_surj (p : ℕ) : Function.Surjective (co (E := E) (n := n) p) := by
  intro y
  obtain ⟨x, hx⟩ := cz_surj (E := E) (n := n) (fun m => ((y m).cast : ℤ))
  refine ⟨x, ?_⟩
  funext m
  rw [co_apply, hx]
  exact ZMod.intCast_zmod_cast (y m)

def mkH (p : ℕ) : (Fin n → 𝓞 E) →+ TestPt.NAdd E n p where
  toFun := mkN p
  map_zero' := by ext i; simp [mkN]
  map_add' x y := by ext i; simp [mkN]

theorem mkN_surj (p : ℕ) : Function.Surjective (mkN (E := E) (n := n) p) := fun z => by
  choose u hu using fun i => Ideal.Quotient.mk_surjective (z i)
  exact ⟨u, funext hu⟩

private theorem natCast_dvd_iff_dvd_basis_repr (p : ℕ) (y : 𝓞 E) :
    (p : 𝓞 E) ∣ y ↔ ∀ k, (p : ℤ) ∣ (RingOfIntegers.basis E).repr y k := by
  constructor
  · rintro ⟨z, rfl⟩ k
    have : (p : 𝓞 E) * z = (p : ℤ) • z := by simp [zsmul_eq_mul]
    rw [this, map_zsmul]
    simp
  · intro h
    choose c hc using h
    refine ⟨∑ k, c k • RingOfIntegers.basis E k, ?_⟩
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr y]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hc k]
    simp [zsmul_eq_mul, mul_assoc]

theorem ker_co (p : ℕ) : (co (E := E) (n := n) p).ker = (mkH p).ker := by
  ext x
  simp only [AddMonoidHom.mem_ker, funext_iff, co_apply, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd, cz_apply]
  show _ ↔ ∀ i, mkN p x i = 0
  simp only [mkN, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, natCast_dvd_iff_dvd_basis_repr]
  constructor
  · intro h i k; exact h (i, k)
  · intro h m; exact h m.1 m.2

theorem exists_phiN (E : Type) [Field E] [NumberField E] (n p : ℕ) :
    ∃ φ : (Ix E n → ZMod p) ≃+ TestPt.NAdd E n p, ∀ x, φ (co p x) = mkN p x := by
  let e1 := QuotientAddGroup.quotientKerEquivOfSurjective _ (co_surj (E := E) (n := n) p)
  let e2 := QuotientAddGroup.quotientAddEquivOfEq (ker_co (E := E) (n := n) p)
  let e3 := QuotientAddGroup.quotientKerEquivOfSurjective (mkH (E := E) (n := n) p) (mkN_surj p)
  refine ⟨e1.symm.trans (e2.trans e3), fun x => ?_⟩
  have h1 : e1.symm (co p x) = (x : (Fin n → 𝓞 E) ⧸ (co (E := E) (n := n) p).ker) := by
    rw [AddEquiv.symm_apply_eq]; rfl
  simp only [AddEquiv.trans_apply, h1]
  rfl

variable {R : Type} [CommRing R]

theorem val_sub (p : ℕ) [NeZero p] (z : ℤ) :
    ((((z : ZMod p).val : ℕ) : R)) - (z : R) ∈ Ideal.span {(p : R)} := by
  rw [Ideal.mem_span_singleton]
  have h := ZMod.val_intCast (n := p) z
  have h2 : (((z : ZMod p).val : ℕ) : R) - (z : R) = ((-((p : ℤ) * (z / p)) : ℤ) : R) := by
    have h3 : (((z : ZMod p).val : ℕ) : R) = ((((z : ZMod p).val : ℕ) : ℤ) : R) := by push_cast; rfl
    rw [h3, h, Int.emod_def]
    push_cast
    ring
  rw [h2]
  push_cast
  exact ⟨-((z / p : ℤ) : R), by ring⟩

theorem sum_co_sub (p : ℕ) [NeZero p] (l : Ix E n → R) (x : Fin n → 𝓞 E) :
    ∑ m, l m * ((co p x m).val : R) - ∑ m, l m * (cz x m : R) ∈ Ideal.span {(p : R)} := by
  rw [← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun m _ => ?_
  rw [← mul_sub]
  exact Ideal.mul_mem_left _ _ (val_sub p _)

def Pm (n : ℕ) (σ : 𝓞 E →+* R) : Matrix (Fin n) (Ix E n) R :=
  fun i m => if m.1 = i then σ (RingOfIntegers.basis E m.2) else 0

def Jm (n : ℕ) (s : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → R) : Matrix (Ix E n) (Fin n) R :=
  fun m i => if m.1 = i then s m.2 else 0

def IsDualOf (σ : 𝓞 E →+* R) (s : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → R) : Prop :=
  ∑ k, s k * σ (RingOfIntegers.basis E k) = 1 ∧
    ∀ a l, σ a * s l = ∑ k, (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E k) l : ℤ) : R) * s k

theorem exists_dualOf {C : Type} [Field C] [Algebra R C] (hi : Function.Injective (algebraMap R C)) (σ : E →+* C)
    (h1 : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap R C).range) (h2 : ∀ k, σ (HT.dualInt E k) ∈ (algebraMap R C).range) :
    ∃ (σ' : 𝓞 E →+* R) (s : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → R),
      (∀ a, algebraMap R C (σ' a) = σ (a : E)) ∧ (∀ k, algebraMap R C (s k) = σ (HT.dualInt E k)) ∧ IsDualOf σ' s := by
  have hsurj : Function.Surjective (algebraMap R C).rangeRestrict := RingHom.rangeRestrict_surjective _
  have hinj : Function.Injective (algebraMap R C).rangeRestrict := fun x y hxy => hi (congrArg Subtype.val hxy)
  let e := RingEquiv.ofBijective (algebraMap R C).rangeRestrict ⟨hinj, hsurj⟩
  let σ0 : 𝓞 E →+* (algebraMap R C).range := (σ.comp (algebraMap (𝓞 E) E)).codRestrict _ (fun a => h1 a)
  let σ' : 𝓞 E →+* R := e.symm.toRingHom.comp σ0
  have hσ' : ∀ a, algebraMap R C (σ' a) = σ (a : E) := by
    intro a
    have h3 : e (σ' a) = σ0 a := by simp [σ']
    have h4 := congrArg Subtype.val h3
    exact h4
  choose s hs using h2
  refine ⟨σ', s, hσ', hs, ?_⟩
  unfold IsDualOf
  refine ⟨?_, ?_⟩
  · apply hi
    rw [map_sum, map_one]
    simp only [map_mul, hs, hσ']
    rw [← map_one σ, ← GlobalTheory.CompanionTheory.Ar.HT.ProjEig.sum_dualInt_mul, map_sum]
    simp [map_mul]
  · intro a l
    apply hi
    simp only [map_mul, map_sum, hs, hσ', map_intCast]
    rw [← map_mul, GlobalTheory.CompanionTheory.Ar.HT.ProjEig.mul_dualInt_eq, map_sum]
    simp [map_mul, map_intCast]

variable {σ : 𝓞 E →+* R} {s : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → R}

theorem Pm_mul_Jm (h : IsDualOf σ s) : Pm n σ * Jm n s = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]
  simp only [Pm, Jm, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp only [if_true]
    split_ifs with hij
    · rw [← h.1]; simp [mul_comm]
    · simp
  · intro b _ hb; simp [hb]
  · simp

theorem Pm_cz (k : Fin n) (x : Fin n → 𝓞 E) : ∑ m, Pm n σ k m * (cz x m : R) = σ (x k) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single k]
  · simp only [Pm, if_true, cz_apply]
    conv_rhs => rw [← (RingOfIntegers.basis E).sum_repr (x k)]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k' _ => ?_)
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  · intro b _ hb; simp [Pm, hb]
  · simp

theorem Pm_cong {p : ℕ} [NeZero p] {F : Type} [Field F] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F)
    (φ : (Ix E n → ZMod p) ≃+ TestPt.NAdd E n p) (hφ : ∀ x, φ (co p x) = mkN p x) (χ : F → R)
    (hχ : ∀ a, χ (pq (Ideal.Quotient.mk _ a)) - σ a ∈ Ideal.span {(p : R)}) (k : Fin n) (x : Ix E n → ZMod p) :
    (∑ j, Pm n σ k j * ((x j).val : R)) - χ (((TestPt.fromNAdd pq).comp φ.toAddMonoidHom) x k) ∈
      Ideal.span {(p : R)} := by
  obtain ⟨x, rfl⟩ := co_surj p x
  have h1 := sum_co_sub p (Pm n σ k) x
  rw [Pm_cz] at h1
  have h2 : ((TestPt.fromNAdd pq).comp φ.toAddMonoidHom) (co p x) k = pq (Ideal.Quotient.mk _ (x k)) := by
    change TestPt.fromNAdd pq (φ (co p x)) k = _
    rw [hφ]; rfl
  rw [h2]
  convert Ideal.sub_mem _ h1 (hχ (x k)) using 1
  ring

def Ma (R : Type) [CommRing R] (n : ℕ) (a : 𝓞 E) : Matrix (Ix E n) (Ix E n) R :=
  fun m m' => (cz (a • dl m') m : R)

theorem Jm_mul_Pm (h : IsDualOf σ s) : Jm n s * Pm n σ = ∑ k, s k • Ma R n (RingOfIntegers.basis E k) := by
  ext m m'
  rw [Matrix.mul_apply, Matrix.sum_apply]
  simp only [Matrix.smul_apply, Ma, Jm, Pm, cz_apply, dl, smul_eq_mul, Pi.smul_apply, Pi.single_apply]
  by_cases hm : m.1 = m'.1
  · rw [Finset.sum_eq_single m.1 (by intro b _ hb; simp [Ne.symm hb]) (by simp)]
    simp only [if_true, hm, mul_ite, mul_zero]
    rw [mul_comm (s m.2), h.2 (RingOfIntegers.basis E m'.2) m.2]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [mul_comm (RingOfIntegers.basis E m'.2)]
    ring
  · have hm' : m'.1 ≠ m.1 := Ne.symm hm
    simp [hm, hm']

theorem vecMul_Ma (l : Ix E n → R) (a : 𝓞 E) (x : Fin n → 𝓞 E) :
    ∑ m, (l ᵥ* Ma R n a) m * (cz x m : R) = ∑ m, l m * (cz (a • x) m : R) := by
  have key : ∀ m', (cz (a • x) m' : R) = ∑ m, (cz x m : R) * (cz (a • dl m) m' : R) := by
    intro m'
    have := hom_eq ((cz (E := E) (n := n)).comp (DistribMulAction.toAddMonoidHom (Fin n → 𝓞 E) a)) x
    simp only [AddMonoidHom.comp_apply, DistribMulAction.toAddMonoidHom_apply] at this
    rw [this]
    simp [Finset.sum_apply]
  simp only [key, Matrix.vecMul, dotProduct, Ma, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun m' _ => ?_))
  ring

variable {C : Type} [Field C] [Algebra R C]

theorem alg_mem_pInt {p : ℕ} {r : R} (h : r ∈ Ideal.span {(p : R)}) : algebraMap R C r ∈ pInt (C := C) R p := by
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 h
  exact Submodule.mem_span_singleton.2 ⟨t, by simp [Algebra.smul_def]⟩

theorem afLat_stable {p : ℕ} [NeZero p] (h : IsDualOf σ s)
    (φ : (Ix E n → ZMod p) ≃+ TestPt.NAdd E n p) (hφ : ∀ x, φ (co p x) = mkN p x)
    (M : Submodule R (TestPt.NAdd E n p → C))
    (hact : ∀ (a : 𝓞 E), ∀ f ∈ M, (fun x : TestPt.NAdd E n p => f fun i => Ideal.Quotient.mk _ a * x i) ∈ M)
    (MM : Submodule R ((Ix E n → ZMod p) → C)) (hMM : ∀ g, g ∈ MM ↔ ∃ f ∈ M, (fun x => f (φ x)) = g) :
    ∀ l ∈ afLat p MM, l ᵥ* (Jm n s * Pm n σ) ∈ afLat p MM := by
  have hMa : ∀ a : 𝓞 E, ∀ l ∈ afLat p MM, l ᵥ* Ma R n a ∈ afLat p MM := by
    intro a l hl
    obtain ⟨g, hg, hgl⟩ := hl
    obtain ⟨f, hf, rfl⟩ := (hMM g).1 hg
    refine ⟨fun x => f (fun i => Ideal.Quotient.mk _ a * φ x i), (hMM _).2 ⟨_, hact a f hf, rfl⟩, ?_⟩
    intro x
    obtain ⟨y, rfl⟩ := co_surj (E := E) (n := n) p x
    have hy : (fun i => Ideal.Quotient.mk (Ideal.span {(p : 𝓞 E)}) a * φ (co p y) i) = φ (co p (a • y)) := by
      rw [hφ, hφ]
      funext i
      simp [mkN]
    show f (fun i => Ideal.Quotient.mk (Ideal.span {(p : 𝓞 E)}) a * φ (co p y) i) - _ ∈ _
    rw [hy]
    have h1 := hgl (co p (a • y))
    have h2 := alg_mem_pInt (C := C) (sum_co_sub p (l ᵥ* Ma R n a) y)
    have h3 := alg_mem_pInt (C := C) (sum_co_sub p l (a • y))
    rw [vecMul_Ma] at h2
    rw [map_sub] at h2 h3
    convert Submodule.sub_mem _ (Submodule.add_mem _ h1 h3) h2 using 1
    ring
  intro l hl
  rw [Jm_mul_Pm h]
  have hsum : l ᵥ* (∑ k, s k • Ma R n (RingOfIntegers.basis E k)) =
      ∑ k, s k • (l ᵥ* Ma R n (RingOfIntegers.basis E k)) := by
    funext m
    simp only [Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun m' _ => ?_))
    ring
  rw [hsum]
  exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (hMa _ l hl))

end PositivityTheory.HtPt.Sgp
