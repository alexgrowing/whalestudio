import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSerrePoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u

namespace LaurentLoc

variable (S : Type u) [CommRing S] (N : ℕ)

def expHom : (Fin (N + 1) →₀ ℕ) →+ (Fin (N + 1) → ℤ) where
  toFun := expToInt N
  map_zero' := by funext j; simp [expToInt]
  map_add' e f := by funext j; simp [expToInt]

theorem expToInt_injective : Function.Injective (expToInt N) := fun e f h =>
  Finsupp.ext fun j => by
    have := congrFun h j
    simpa [expToInt] using this

abbrev LRing : Type u := AddMonoidAlgebra S (Fin (N + 1) → ℤ)

def toL : Poly S N →+* LRing S N := AddMonoidAlgebra.mapDomainRingHom S (expHom N)

theorem coeff_toL (p : Poly S N) : (toL S N p).coeff = polyToLaurent S N p := rfl

theorem toL_injective : Function.Injective (toL S N) := fun p q h => by
  have h' : polyToLaurent S N p = polyToLaurent S N q := by rw [← coeff_toL, ← coeff_toL, h]
  exact AddMonoidAlgebra.coeff_injective (Finsupp.mapDomain_injective (expToInt_injective N) h')

variable {S N}

theorem toL_monomial (f : Fin (N + 1) →₀ ℕ) (r : S) :
    toL S N (monomial f r) = AddMonoidAlgebra.single (expToInt N f) r :=
  AddMonoidAlgebra.mapDomain_single

theorem single_neg_mul (b : Fin (N + 1) → ℤ) (x : LRing S N) :
    AddMonoidAlgebra.single (-b) (1 : S) * (AddMonoidAlgebra.single b 1 * x) = x := by
  rw [← mul_assoc, AddMonoidAlgebra.single_mul_single, neg_add_cancel, mul_one]
  exact one_mul x

theorem mem_monos_iff {I : Finset (Fin (N + 1))} {s : Poly S N} :
    s ∈ monos I → ∃ f : Fin (N + 1) →₀ ℕ, (∀ j ∉ I, f j = 0) ∧ s = monomial f 1 := by
  intro hs
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨Finsupp.single i 1, fun j hj => ?_, rfl⟩
    rw [Finsupp.single_apply, if_neg]
    rintro rfl; exact hj hi
  | one => exact ⟨0, fun _ _ => rfl, rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨g, hg, rfl⟩ := hy
    refine ⟨f + g, fun j hj => by simp [hf j hj, hg j hj], ?_⟩
    rw [monomial_mul, one_mul]

theorem monomial_mem_monos {I : Finset (Fin (N + 1))} (f : Fin (N + 1) →₀ ℕ) (hf : ∀ j ∉ I, f j = 0) :
    (monomial f 1 : Poly S N) ∈ monos I := by
  rw [monomial_eq, C_1, one_mul]
  refine Submonoid.prod_mem _ fun i hi => Submonoid.pow_mem _ (X_mem_monos ?_) _
  by_contra h
  exact (Finsupp.mem_support_iff.mp hi) (hf i h)

theorem isUnit_toL {I : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos I) : IsUnit (toL S N s) := by
  obtain ⟨f, -, rfl⟩ := mem_monos_iff hs
  rw [toL_monomial]
  refine isUnit_iff_exists_inv.mpr ⟨AddMonoidAlgebra.single (-expToInt N f) 1, ?_⟩
  rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one]
  rfl

abbrev algP : Algebra (Poly S N) (LRing S N) := (toL S N).toAlgebra

attribute [local instance] algP

theorem smul_def' (p : Poly S N) (x : LRing S N) : p • x = toL S N p * x := rfl

instance : IsScalarTower S (Poly S N) (LRing S N) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap S (LRing S N) r = toL S N (monomial 0 r)
    rw [toL_monomial]
    have : expToInt N 0 = 0 := funext fun j => by simp [expToInt]
    rw [this]
    rfl

theorem isUnit_end (I : Finset (Fin (N + 1))) (s : monos (S := S) I) :
    IsUnit (algebraMap (Poly S N) (Module.End (Poly S N) (LRing S N)) s) := by
  rw [Module.End.isUnit_iff]
  have hu := (isUnit_toL s.2).unit.mulLeft_bijective
  exact hu

def iotaP (I : Finset (Fin (N + 1))) : LocMod S N (Poly S N) I →ₗ[Poly S N] LRing S N :=
  LocalizedModule.lift (monos I) (Algebra.linearMap (Poly S N) (LRing S N)) (isUnit_end I)

theorem localizationToLaurent_mk_eq_iff (I : Finset (Fin (N + 1))) (p : Poly S N) (s : monos (S := S) I) (y : LRing S N) :
    iotaP I (LocalizedModule.mk p s) = y ↔ toL S N p = toL S N s * y := by
  change (↑((isUnit_end (S := S) I s).unit⁻¹) : Module.End (Poly S N) (LRing S N))
      (Algebra.linearMap (Poly S N) (LRing S N) p) = y ↔ _
  rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]
  rfl

theorem toL_mul_iotaP (I : Finset (Fin (N + 1))) (p : Poly S N) (s : monos (S := S) I) :
    toL S N p = toL S N s * iotaP I (LocalizedModule.mk p s) :=
  (localizationToLaurent_mk_eq_iff I p s _).mp rfl

theorem localizationToLaurent_injective (I : Finset (Fin (N + 1))) : Function.Injective (iotaP (S := S) (N := N) I) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  induction z using LocalizedModule.induction_on with
  | h p s =>
    rw [localizationToLaurent_mk_eq_iff, mul_zero, ← map_zero (toL S N)] at hz
    rw [toL_injective S N hz]
    exact LocalizedModule.zero_mk s

end LaurentLoc

namespace LaurentLoc

variable {S : Type u} [CommRing S] {N : ℕ}

attribute [local instance] algP

def iota (I : StdCell N) : LocMod S N (Poly S N) I.1 →ₗ[S] Laurent S N :=
  (AddMonoidAlgebra.coeffLinearEquiv S).toLinearMap ∘ₗ (iotaP (S := S) (N := N) I.1).restrictScalars S

theorem iota_apply (I : StdCell N) (z : LocMod S N (Poly S N) I.1) : iota I z = (iotaP I.1 z).coeff := rfl

theorem sum_expToInt (d : Fin (N + 1) →₀ ℕ) :
    ∑ j, expToInt N d j = Finsupp.weight (fun _ : Fin (N + 1) => (1 : ℤ)) d := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [expToInt]

theorem sum_expToInt' (d : Fin (N + 1) →₀ ℕ) :
    ∑ j, expToInt N d j = ((Finsupp.weight (1 : Fin (N + 1) → ℕ) d : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [expToInt]

theorem image_exps (c : ℤ) :
    expToInt N '' {d | Finsupp.weight (fun _ : Fin (N + 1) => (1 : ℤ)) d = c} = laurentExps N c ∅ := by
  ext a
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨(sum_expToInt d).trans hd, fun j _ => by simp [expToInt]⟩
  · rintro ⟨hs, hnn⟩
    have ha : expToInt N (Finsupp.equivFunOnFinite.symm fun j => (a j).toNat) = a := by
      funext j; simp [expToInt, Int.toNat_of_nonneg (hnn j (Finset.notMem_empty j))]
    refine ⟨Finsupp.equivFunOnFinite.symm fun j => (a j).toNat, ?_, ha⟩
    change _ = c
    rw [← sum_expToInt, ha, hs]

theorem map_piece (c : ℤ) : ((polyGraded S N).piece c).map (polyToLaurent S N) =
    Finsupp.supported S S (laurentExps N c ∅) := by
  change (weightedHomogeneousSubmodule S (fun _ => (1 : ℤ)) c).map _ = _
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported, AddMonoidAlgebra.supported_eq_map,
    ← Submodule.map_comp]
  have : (polyToLaurent S N).comp (AddMonoidAlgebra.coeffLinearEquiv S).symm.toLinearMap =
      Finsupp.lmapDomain S S (expToInt N) := LinearMap.ext fun _ => rfl
  rw [this, Finsupp.lmapDomain_supported, image_exps]

theorem localizationToLaurent_mk_monomial (I : Finset (Fin (N + 1))) (p : Poly S N) (s : monos (S := S) I)
    (f : Fin (N + 1) →₀ ℕ) (hf : (s : Poly S N) = monomial f 1) :
    iotaP I (LocalizedModule.mk p s) = AddMonoidAlgebra.single (-expToInt N f) 1 * toL S N p := by
  rw [localizationToLaurent_mk_eq_iff, hf, toL_monomial, ← mul_assoc, AddMonoidAlgebra.single_mul_single,
    add_neg_cancel, mul_one]
  exact (one_mul _).symm

theorem iota_mk (I : StdCell N) (p : Poly S N) :
    iota I (locMk (Poly S N) I.1 p) = polyToLaurent S N p := by
  rw [iota_apply, ← coeff_toL]
  congr 1
  change iotaP I.1 (LocalizedModule.mk p 1) = _
  rw [localizationToLaurent_mk_eq_iff]
  change _ = toL S N 1 * _
  rw [map_one, one_mul]

theorem iota_res (I J : StdCell N) (h : I.1 ⊆ J.1) (z : LocMod S N (Poly S N) I.1) :
    iota J (locResS I J h z) = iota I z := by
  rw [iota_apply, iota_apply]
  congr 1
  induction z using LocalizedModule.induction_on with
  | h p s =>
    change iotaP J.1 (locRes h (LocalizedModule.mk p s)) = _
    rw [locRes_mk, localizationToLaurent_mk_eq_iff]
    exact toL_mul_iotaP I.1 p s

theorem iota_injective (I : StdCell N) : Function.Injective (iota (S := S) I) :=
  (AddMonoidAlgebra.coeffLinearEquiv S).injective.comp (localizationToLaurent_injective I.1)

end LaurentLoc

namespace LaurentLoc

variable {S : Type u} [CommRing S] {N : ℕ}

attribute [local instance] algP

theorem iota_gen_mem (c : ℤ) (I : StdCell N) (m : Poly S N) (s : monos (S := S) I.1) (a : ℤ) (e : ℕ)
    (hm : m ∈ (polyGraded S N).piece a) (hs : (s : Poly S N).IsHomogeneous e) (hc : a - e = c) :
    iota I (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I.1) (Poly S N)) ∈
      laurentDeg S N c I := by
  obtain ⟨f, hfI, hf⟩ := mem_monos_iff s.2
  change ((iotaP I.1 (LocalizedModule.mk m s)).coeff.support : Set _) ⊆ laurentExps N c I.1
  rw [localizationToLaurent_mk_monomial I.1 m s f hf]
  intro y hy
  rw [Finset.mem_coe, Finsupp.mem_support_iff, AddMonoidAlgebra.coeff_single_mul_apply, one_mul,
    neg_neg, coeff_toL] at hy
  have hy2 : expToInt N f + y ∈ (Finsupp.mapDomain (expToInt N) (AddMonoidAlgebra.coeff m)).support :=
    Finsupp.mem_support_iff.mpr hy
  obtain ⟨d, hd, hdy⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hy2)
  have : Nontrivial S := nontrivial_of_ne _ _ hy
  have hwd : Finsupp.weight (fun _ : Fin (N + 1) => (1 : ℤ)) d = a :=
    hm (Finsupp.mem_support_iff.mp hd)
  have hwf : Finsupp.weight (1 : Fin (N + 1) → ℕ) f = e := by
    refine hs ?_
    rw [hf, coeff_monomial, if_pos rfl]
    exact one_ne_zero
  have hy' : y = expToInt N d - expToInt N f := by rw [hdy]; abel
  refine ⟨?_, fun j hj => ?_⟩
  · have h1 := sum_expToInt d
    have h2 : ∑ j, expToInt N f j = (e : ℤ) := by rw [sum_expToInt', ← hwf]
    rw [hy']
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib, h1, h2, hwd, hc]
  · rw [hy']
    simp [expToInt, hfI j hj]

theorem single_mem_map (c : ℤ) (I : StdCell N) (x : Fin (N + 1) → ℤ) (hx : x ∈ laurentExps N c I.1) :
    Finsupp.single x (1 : S) ∈ (degLoc (polyGraded S N) c I).map (iota I) := by
  obtain ⟨hsum, hnn⟩ := hx
  set dp : Fin (N + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => (x j).toNat
  set dm : Fin (N + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => (-x j).toNat
  have hdm : ∀ j ∉ I.1, dm j = 0 := fun j hj => by
    simp [dm, Int.toNat_eq_zero, hnn j hj]
  have hx' : -expToInt N dm + expToInt N dp = x := by
    funext j
    have h1 : ((dp j : ℕ) : ℤ) = ((x j).toNat : ℤ) := by simp [dp]
    have h2 : ((dm j : ℕ) : ℤ) = ((-x j).toNat : ℤ) := by simp [dm]
    have := Int.toNat_sub_toNat_neg (x j)
    simp only [Pi.add_apply, Pi.neg_apply, expToInt]
    omega
  let s : monos (S := S) I.1 := ⟨monomial dm 1, monomial_mem_monos dm hdm⟩
  refine ⟨LocalizedModule.mk (monomial dp 1) s, Submodule.subset_span
    ⟨monomial dp 1, s, Finsupp.weight (fun _ : Fin (N + 1) => (1 : ℤ)) dp, dm.degree, ?_, ?_, ?_, rfl⟩, ?_⟩
  · exact isWeightedHomogeneous_monomial _ _ _ rfl
  · exact isHomogeneous_monomial _ rfl
  · have h2 : ((dm.degree : ℕ) : ℤ) = ∑ j, expToInt N dm j := by
      rw [sum_expToInt', Finsupp.degree_eq_weight_one]; rfl
    rw [← sum_expToInt, h2, ← Finset.sum_sub_distrib, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← congrFun hx' j]
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  · change (iotaP I.1 (LocalizedModule.mk (monomial dp 1) s)).coeff = _
    rw [localizationToLaurent_mk_monomial I.1 _ s dm rfl, toL_monomial, AddMonoidAlgebra.single_mul_single, mul_one, hx']
    rfl

theorem iota_deg (c : ℤ) (I : StdCell N) :
    (degLoc (polyGraded S N) c I).map (iota I) = laurentDeg S N c I := by
  apply le_antisymm
  · rw [degLoc, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨z, ⟨m, s, a, e, hm, hs, hc, rfl⟩, rfl⟩
    exact iota_gen_mem c I m s a e hm hs hc
  · rw [laurentDeg, Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact single_mem_map c I x hx

end LaurentLoc

theorem SerrePoly.Laurent.proof : SerrePoly.Laurent.Statement.{u} := by
  intro S _ N
  refine ⟨fun p q h => LaurentLoc.toL_injective S N (AddMonoidAlgebra.coeff_injective h),
    LaurentLoc.map_piece, LaurentLoc.iota, LaurentLoc.iota_injective, LaurentLoc.iota_res,
    LaurentLoc.iota_mk, LaurentLoc.iota_deg⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
