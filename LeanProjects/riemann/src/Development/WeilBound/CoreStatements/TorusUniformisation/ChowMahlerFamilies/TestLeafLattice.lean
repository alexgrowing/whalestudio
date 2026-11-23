import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FromNAdd
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SymplecticPeriodMatrixIntegrality
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedAugmentationTheorem
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsAddEquiv
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TestLeafLattice

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

section Abstract

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def Leaf (p : ℕ) (cp : R) {N : Type} [AddCommGroup N] (M : Submodule R (N → C)) : Prop :=
  ∀ f : N → R, (∀ x y, f (x + y) - f x - f y ∈ Ideal.span {(p : R)}) →
    ∃ g ∈ M, ∀ x, g x - algebraMap R C (cp * f x) ∈ pInt (C := C) R p

theorem mem_pInt {p : ℕ} {r : R} (hr : r ∈ Ideal.span {(p : R)}) : algebraMap R C r ∈ pInt (C := C) R p := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
  refine Submodule.mem_span_singleton.2 ⟨a, ?_⟩
  rw [Algebra.smul_def, map_mul, map_natCast]

theorem leaf_of_afLat (p : ℕ) [Fact p.Prime] (cp : R) {I : Type} [Fintype I] [DecidableEq I]
    (M : Submodule R ((I → ZMod p) → C)) (h : ∀ l : I → R, cp • l ∈ afLat p M) : Leaf p cp M := by
  intro f hf
  obtain ⟨g, hg, hgl⟩ := h fun i => f (Pi.single i 1)
  refine ⟨g, hg, fun x => ?_⟩
  let fb : (I → ZMod p) →+ R ⧸ Ideal.span {(p : R)} := AddMonoidHom.mk' (fun x => Ideal.Quotient.mk _ (f x))
    fun x y => by
      rw [← map_add, Ideal.Quotient.eq, ← sub_sub]
      exact hf x y
  have hx : x = ∑ i, (x i).val • Pi.single i (1 : ZMod p) := by
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j (fun i _ hi => by rw [Pi.smul_apply, Pi.single_eq_of_ne hi.symm, smul_zero])
      (fun hj => absurd (Finset.mem_univ j) hj), Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, _root_.mul_one,
      ZMod.natCast_zmod_val]
  have h1 : (∑ i, f (Pi.single i 1) * ((x i).val : R)) - f x ∈ Ideal.span {(p : R)} := by
    rw [← Ideal.Quotient.eq]
    have h2 : fb x = ∑ i, (x i).val • fb (Pi.single i 1) := by
      conv_lhs => rw [hx]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_nsmul _ _ _
    have h3 : fb x = Ideal.Quotient.mk _ (f x) := rfl
    rw [← h3, h2, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, map_mul, map_natCast, nsmul_eq_mul]
    rfl
  have h4 := Submodule.add_mem _ (hgl x) (mem_pInt (C := C) (Ideal.mul_mem_left _ cp h1))
  convert h4 using 1
  simp only [Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, ← Finset.mul_sum, mul_sub, map_sub]
  ring

theorem Leaf.retract {p : ℕ} {cp : R} {N N' : Type} [AddCommGroup N] [AddCommGroup N']
    {M : Submodule R (N → C)} {M' : Submodule R (N' → C)} (j : N →+ N') (r : N' →+ N) (hr : ∀ x, r (j x) = x)
    (hj : ∀ g ∈ M', (fun x => g (j x)) ∈ M) (h : Leaf p cp M') : Leaf p cp M := by
  intro f hf
  obtain ⟨g, hg, h1⟩ := h (fun x => f (r x)) fun x y => by
    rw [map_add]; exact hf _ _
  refine ⟨_, hj g hg, fun x => ?_⟩
  have := h1 (j x)
  rwa [hr] at this

theorem htd_afLat {p : ℕ} [Fact p.Prime] {g : ℕ} {v : Valuation C NNReal} [Algebra ℤ_[p] R]
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} (hS : HodgeTateSetting p v R O σ cp)
    (H : HodgeTateDatum p g v R O σ cp) (l : Ix g → R) : cp • l ∈ afLat p H.AA.carrier := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hvcp : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    have h := hS.cp_val
    rw [h0, zero_pow (by omega)] at h
    exact hS.p_ne h.symm
  have hcp : cp ≠ 0 := by rintro rfl; exact hvcp (by simp)
  have hEalt : (H.E.map (algebraMap ℤ_[p] R))ᵀ = -(H.E.map (algebraMap ℤ_[p] R)) := by
    ext i j
    have h := congrFun (congrFun H.E_alternating.1 j) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
    simp [Matrix.transpose_apply, Matrix.map_apply, h]
  have hEu : IsUnit (H.E.map (algebraMap ℤ_[p] R)).det := by
    have : (H.E.map (algebraMap ℤ_[p] R)).det = algebraMap ℤ_[p] R H.E.det :=
      (RingHom.map_det _ _).symm
    rw [this]; exact H.isUnit_det_E.map _
  obtain ⟨-, -, -, hcpmem⟩ :=
    gp_mat_lattice C v R hS.integers g H.Ht H.Bt _ cp hcp hEalt hEu H.form_eq_alt
  exact (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact PolAF.rows_mem_afLat H k)) (hcpmem l)

end Abstract

section Geom

open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj G'] {p : ℕ}
  {N N' : Type} [AddCommGroup N] [AddCommGroup N']
  {pt : N → (Chart.sp (R₀ := R) R ⟶ G)} {pt' : N' → (Chart.sp (R₀ := R) R ⟶ G')}

theorem exists_hom (h : IsTorsPts G p pt) (h' : IsTorsPts G' p pt') (j : G ⟶ G') [IsMonHom j] :
    ∃ jN : N →+ N', ∀ x, pt' (jN x) = pt x ≫ j := by
  have hx : ∀ x, (pt x ≫ j) ^ p = 1 := fun x => by
    rw [← MonObj.pow_comp, (h.range _).2 ⟨x, rfl⟩, MonObj.one_comp]
  choose f hf using fun x => (h'.range _).1 (hx x)
  exact ⟨AddMonoidHom.mk' f fun x y => h'.inj (by rw [hf, h'.add, hf, hf, h.add, MonObj.mul_comp]), hf⟩

omit [AddCommGroup N] [AddCommGroup N'] in
theorem pull_mem (C : Type) [Field C] [Algebra R C] (T : TorsRep G p) (T' : TorsRep G' p) (j : G ⟶ G') [IsMonHom j]
    (jN : N → N') (hj : ∀ x, pt' (jN x) = pt x ≫ j) :
    ∀ g ∈ torsFun C T' pt', (fun x => g (jN x)) ∈ torsFun C T pt := by
  obtain ⟨ψ, hψ, -⟩ := T'.univ T.A (T.y ≫ j) (by rw [← MonObj.pow_comp, T.y_p, MonObj.one_comp])
  rintro g ⟨a, ha⟩
  refine ⟨ψ a, fun x φ hφ => ha (jN x) (φ.comp ψ) ?_⟩
  rw [← Chart.spMap_comp, Category.assoc, hψ, ← Category.assoc, hφ, hj]

end Geom

theorem leaf_abFactor (hZ : ZarhinStatement) (hD : HodgeTateDatumStatement) (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hv : v.Integers R)
    (hp : v (p : C) < 1) (hc : IsAdicComplete (Ideal.span {(p : R)}) R) {N : Type} [AddCommGroup N]
    (M : Submodule R (N → C)) (hM : IsAbFactor p M) :
    ∃ cp : R, v (algebraMap R C cp) ^ (p - 1) = v (p : C) ∧ Leaf p cp M := by
  obtain ⟨A, _, L, hA, hL, hamp, T, N', _, pt, hpt, i, π, hiπ, -, rfl⟩ := hM
  obtain ⟨P, a, r, ha, hr, har⟩ := hZ C v R hv A L hA hL hamp
  letI : Algebra ℤ_[p] R := (Av.zpLift p R hc).toAlgebra
  obtain ⟨⟨T'⟩, cp, hS, H, pt', hpt', hT⟩ := hD p C v R hv hp hc P
  obtain ⟨aN, haN⟩ := exists_hom hpt hpt' a
  obtain ⟨rN, hrN⟩ := exists_hom hpt' hpt r
  refine ⟨cp, by simpa using hS.cp_val, ?_⟩
  have h1 : Leaf p cp (torsFun C T' pt') := by
    rw [← hT T']
    exact leaf_of_afLat p cp _ (htd_afLat hS H)
  have h2 : Leaf p cp (torsFun C T pt) :=
    h1.retract aN rN (fun x => hpt.inj (by rw [hrN, haN, Category.assoc, har, Category.comp_id]))
      (pull_mem C T T' a aN haN)
  exact h2.retract i π hiπ fun g hg => ⟨g, hg, rfl⟩

theorem smul_spanOver {o C V : Type} [CommRing o] [Field C] [Algebra o C] [AddCommGroup V] [Module C V]
    (RC : Subalgebra o C) (S : Set V) {a : C} (ha : a ∈ RC) {x : V} (hx : x ∈ spanOver RC S) :
    a • x ∈ spanOver RC S := by
  refine AddSubgroup.closure_induction (fun x hx => ?_) ?_ (fun x y _ _ h1 h2 => ?_) (fun x _ h => ?_) hx
  · obtain ⟨b, hb, e, he, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * b, RC.mul_mem ha hb, e, he, smul_smul a b e⟩
  · rw [smul_zero]; exact AddSubgroup.zero_mem _
  · rw [smul_add]; exact AddSubgroup.add_mem _ h1 h2
  · rw [smul_neg]; exact AddSubgroup.neg_mem _ h

theorem sub_mem_of_fixed {R : Type} [CommRing R] {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) {x y z : R}
    (hx : x ^ p ^ n = x) (hy : y ^ p ^ n = y) (hz : z ^ p ^ n = z)
    (h : ∀ m, IsUnit (1 - (z - x - y) ^ (m + 1))) : z - x - y ∈ Ideal.span {(p : R)} := by
  obtain ⟨d, hd⟩ : ∃ d, d = z - x - y := ⟨_, rfl⟩
  rw [← hd] at h ⊢
  have hz' : z = (x + y) + d := by rw [hd]; ring
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (x + y) d n
  obtain ⟨s, hs⟩ := exists_add_pow_prime_pow_eq hp x y n
  rw [← hz', hz, hs, hx, hy] at hr
  obtain ⟨m, hm⟩ : ∃ m, p ^ n = m + 2 := by
    have := Nat.one_lt_pow hn hp.one_lt
    exact ⟨p ^ n - 2, by omega⟩
  have h1 : d * (1 - d ^ (m + 1)) ∈ Ideal.span {(p : R)} := by
    rw [Ideal.mem_span_singleton']
    refine ⟨x * y * s + (x + y) * d * r, ?_⟩
    rw [hm] at hr
    linear_combination -hd - hr
  exact (Ideal.mul_unit_mem_iff_mem _ (h m)).1 h1

theorem chi_add (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsLocalRing O] {C : Type} [Field C] [Algebra O C]
    (RC : Subalgebra O C) (v : Valuation C NNReal) (hv : ∀ c, c ∈ RC ↔ v c ≤ 1)
    {F : Type} [Field F] [Fintype F] [CharP F p] (σ : F →+* IsLocalRing.ResidueField O) (χ : F →*₀ C)
    (hχ : ∀ a (o : O), IsLocalRing.residue O o = σ a →
      χ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ a - algebraMap O C o) ≠ 1) :
    ∃ χ' : F → RC, (∀ a, χ a = χ' a) ∧ ∀ a b, χ' (a + b) - χ' a - χ' b ∈ Ideal.span {(p : RC)} := by
  have hunit : ∀ a : RC, v (a : C) = 1 → IsUnit a := fun a ha => by
    have h0 : (a : C) ≠ 0 := by
      intro h; rw [h, map_zero] at ha; exact zero_ne_one ha
    refine IsUnit.of_mul_eq_one ⟨(a : C)⁻¹, (hv _).2 (by rw [map_inv₀, ha, inv_one])⟩ ?_
    exact Subtype.ext (mul_inv_cancel₀ h0)
  have hlt : ∀ a (o : O), IsLocalRing.residue O o = σ a → v (χ a - algebraMap O C o) < 1 := fun a o ho => by
    obtain ⟨h1, h2⟩ := hχ a o ho
    refine lt_of_le_of_ne ((hv _).1 h1) fun h => ?_
    obtain ⟨u, hu⟩ := (hunit ⟨_, h1⟩ h).exists_left_inv
    exact h2 u u.2 (congrArg Subtype.val hu)
  have hmem : ∀ a, χ a ∈ RC := fun a => by
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (σ a)
    have := RC.add_mem (hχ a o ho).1 (RC.algebraMap_mem o)
    simpa using this
  refine ⟨fun a => ⟨χ a, hmem a⟩, fun _ => rfl, fun a b => ?_⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  have hroot : ∀ a, (⟨χ a, hmem a⟩ : RC) ^ p ^ (n : ℕ) = ⟨χ a, hmem a⟩ := fun a => Subtype.ext (by
    change χ a ^ p ^ (n : ℕ) = χ a
    rw [← hn, ← map_pow, FiniteField.pow_card])
  refine sub_mem_of_fixed Fact.out n.ne_zero (hroot _) (hroot _) (hroot _) fun m => hunit _ ?_
  change v (1 - (χ (a + b) - χ a - χ b) ^ (m + 1)) = 1
  obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (σ a)
  obtain ⟨o', ho'⟩ := IsLocalRing.residue_surjective (σ b)
  have h3 := v.map_sub_lt (v.map_sub_lt (hlt (a + b) (o + o') (by rw [map_add, map_add, ho, ho'])) (hlt a o ho))
    (hlt b o' ho')
  have h4 : χ (a + b) - algebraMap O C (o + o') - (χ a - algebraMap O C o) - (χ b - algebraMap O C o') =
      χ (a + b) - χ a - χ b := by rw [map_add (algebraMap O C)]; ring
  rw [h4] at h3
  refine v.map_one_sub_of_lt ?_
  rw [map_pow]
  exact pow_lt_one₀ zero_le h3 (Nat.succ_ne_zero m)

theorem exists_ratio {O C : Type} [CommRing O] [Field C] [CharZero C] [Algebra O C] (RC : Subalgebra O C)
    (v : Valuation C NNReal) (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) (p : ℕ) [Fact p.Prime] {w u : O}
    (hw : w ^ (p - 1) = u * (p : O)) (cp : RC) (hcp : v (algebraMap RC C cp) ^ (p - 1) = v (p : C)) :
    ∃ t : RC, (cp : C) * t = algebraMap O C w := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp0 : v (p : C) ≠ 0 := by simpa using (Fact.out : p.Prime).ne_zero
  have h0 : v (cp : C) ≠ 0 := by
    intro h0
    change v (cp : C) ^ (p - 1) = _ at hcp
    rw [h0, zero_pow (by omega)] at hcp
    exact hp0 hcp.symm
  have h0' : (cp : C) ≠ 0 := by simpa using h0
  have h1 : v (algebraMap O C w) ^ (p - 1) ≤ v (cp : C) ^ (p - 1) := by
    rw [← map_pow, ← map_pow, hw, map_mul, map_mul, map_natCast]
    change _ ≤ v (algebraMap RC C cp) ^ (p - 1)
    rw [hcp]
    exact mul_le_of_le_one_left zero_le ((hv _).1 (RC.algebraMap_mem u))
  have h2 : v (algebraMap O C w) ≤ v (cp : C) := le_of_pow_le_pow_left₀ (by omega) zero_le h1
  refine ⟨⟨algebraMap O C w / cp, (hv _).2 ?_⟩, mul_div_cancel₀ _ h0'⟩
  rw [map_div₀]
  exact div_le_one_of_le₀ h2 zero_le

end PositivityTheory.Xgn.TestLeafLattice

theorem PositivityTheory.Xgn.test_leaf_lattice : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → GlobalTheory.CompanionTheory.Ar.GR.IsAbFactor p (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) → ∀ τ, mulLat (algebraMap O C w) (stdLat RC _) ≤ ((chartD e b pq sc w P i).bc RC).af RC p (fun a => χ τ a) := by
  intro hZ hD E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d h1 h2 p _ h3 h4 h5 h6 b h7 φ hφ A _ _ _ m _ h8 O _ _ _ _ _ _ _
    t₀ Sg _ e φ' F _ _ _ pq sc w σ hO hsec G c' h9 P i h10 h11 C _ _ _ _ RC hT χ hχ _ _ _ v hv hvp hab τ
  obtain ⟨χ', hχσ, hf⟩ := PositivityTheory.Xgn.TestLeafLattice.chi_add p RC v hv (σ τ) (χ τ) (hχ τ)
  obtain ⟨-, -, -, -, -, -, ⟨-, ⟨u, -, hw⟩, -⟩, -⟩ := hO
  obtain ⟨hC, -, hcompl, -⟩ := hT
  haveI : CharZero C := charZero_of_injective_ringHom ((algebraMap Ω C).comp 𝔐.cst).injective
  have hint : v.Integers RC := ⟨Subtype.val_injective, fun x => (hv _).1 x.2, fun r hr => ⟨⟨r, (hv _).2 hr⟩, rfl⟩⟩
  obtain ⟨cp, hcp, hleaf⟩ := PositivityTheory.Xgn.TestLeafLattice.leaf_abFactor hZ hD p C v RC hint hvp hcompl _ hab
  obtain ⟨t, ht⟩ := PositivityTheory.Xgn.TestLeafLattice.exists_ratio RC v hv p hw cp hcp
  rintro _ ⟨z, hz, rfl⟩
  have hz' : ∀ k, z k ∈ RC := fun k => hz k (Set.mem_univ k)
  obtain ⟨g, hg, hgf⟩ := hleaf (fun x => t * ∑ k, ⟨z k, hz' k⟩ * χ' (TestPt.fromNAdd pq x k)) fun x x' => by
    rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun k _ => ?_)
    rw [← mul_sub, ← mul_sub, map_add, Pi.add_apply]
    exact Ideal.mul_mem_left _ _ (hf _ _)
  have hgM : (fun a => g (TestPt.toNAdd sc a)) ∈ ((chartD e b pq sc w P i).bc RC).M := by
    refine Submodule.span_induction (p := fun g _ => (fun a => g (TestPt.toNAdd sc a)) ∈ ((chartD e b pq sc w P i).bc RC).M)
      ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨g₀, hg₀, rfl⟩
      exact AddSubgroup.subset_closure ⟨1, RC.one_mem, _, ⟨_, ⟨g₀, hg₀, rfl⟩, rfl⟩, (one_smul _ _).symm⟩
    · exact AddSubgroup.zero_mem _
    · exact fun _ _ _ _ h h' => AddSubgroup.add_mem _ h h'
    · exact fun a _ _ h => PositivityTheory.Xgn.TestLeafLattice.smul_spanOver RC _ a.2 h
  choose s hs using fun a => Submodule.mem_span_singleton.1 (hgf (TestPt.toNAdd sc a))
  refine AddSubgroup.mem_comap.2 (AddSubgroup.mem_sup.2 ⟨_, hgM, (p : C) • fun a => -(s a : C),
    ⟨fun a => -(s a : C), fun a _ => RC.neg_mem (s a).2, rfl⟩, ?_⟩)
  funext a
  have h := hs a
  have hft : ∀ k, TestPt.fromNAdd pq (TestPt.toNAdd sc a) k = a k := fun k => hsec.1 (a k)
  simp only [hft] at h
  change (s a : C) * (p : C) = g _ - (cp : C) * ((t : C) * ((∑ k, ⟨z k, hz' k⟩ * χ' (a k) : RC) : C)) at h
  rw [← _root_.mul_assoc, ht, AddSubmonoidClass.coe_finset_sum] at h
  simp only [MulMemClass.coe_mul, ← hχσ] at h
  change g _ + (p : C) * -(s a : C) = linMap _ (fun a => χ τ a) (algebraMap O C w • z) a
  simp only [linMap, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc,
    ← Finset.mul_sum]
  linear_combination -h
