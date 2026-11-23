import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.HodgeTateSpectral.HTSpecGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.SigCEq

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace UpperTheory.Gal.Seam.Spec

open CrystallineSemistableComparison CrystallineSemistableComparison.HTSpecB

open GlobalTheory.HTLink

def HdgIso : Prop := ∀ (K : Type) [Field K] [CharZero K],
    ∃ e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] [IsProper q] (a j : ℕ),
      CrystallineSemistableComparison.HT.Hdg q a (a + j) ≃ₗ[K] CrystallineSemistableComparison.Om.HodgeC q a j,
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [IsProper q]
      [Smooth p] [IsProper p] (u : X ⟶ Y) (hu : u ≫ p = q) (a j : ℕ) (x : CrystallineSemistableComparison.HT.Hdg p a (a + j)),
      e q a j (CrystallineSemistableComparison.HT.pullH u hu a (a + j) x) = CrystallineSemistableComparison.Om.pullC u hu a j (e p a j x)

section Proj

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isProper_pstr (R : Type) [CommRing R] (N : ℕ) : IsProper (PSpace.str R N) := by
  have : IsScalarTower R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  have : IsClosedImmersion (spMap (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0))) := by
    apply IsClosedImmersion.spec_of_surjective
    rintro ⟨p, hp⟩
    have h0 : p.totalDegree = 0 := Nat.le_zero.1 (MvPolynomial.IsHomogeneous.totalDegree_le hp)
    exact ⟨p.coeff 0, Subtype.ext (MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 h0).symm⟩
  unfold PSpace.str
  infer_instance

end Proj

section Mat

variable {R : Type} [Field R] {m : Type} [Fintype m] [DecidableEq m] {d : ℕ}

theorem exists_inv_of_inj (H : Matrix m (Fin d) R) (hc : Fintype.card m = d) (hi : ∀ z, H.mulVec z = 0 → z = 0) :
    ∃ Ψ : Matrix (Fin d) m R, Ψ * H = 1 ∧ H * Ψ = 1 := by
  let e : m ≃ Fin d := Fintype.equivFinOfCardEq hc
  let H' : Matrix (Fin d) (Fin d) R := H.submatrix e.symm id
  have hdet : H'.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv
    apply hi
    funext c
    have := congrFun hv0 (e c)
    simpa [H', Matrix.mulVec, dotProduct] using this
  have hu : IsUnit H'.det := isUnit_iff_ne_zero.2 hdet
  have hH : H = H'.submatrix e (Equiv.refl (Fin d)) := by
    funext c i
    simp [H']
  refine ⟨H'⁻¹.submatrix (Equiv.refl (Fin d)) e, ?_, ?_⟩
  · rw [hH, Matrix.submatrix_mul_equiv, Matrix.nonsing_inv_mul _ hu, Matrix.submatrix_one_equiv]
  · rw [hH, Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv _ hu, Matrix.submatrix_one_equiv]

def invM (H : Matrix m (Fin d) R) : Matrix (Fin d) m R :=
  open Classical in
  if h : ∃ Ψ : Matrix (Fin d) m R, Ψ * H = 1 ∧ H * Ψ = 1 then h.choose else 0

theorem invM_spec (H : Matrix m (Fin d) R) (h : ∃ Ψ : Matrix (Fin d) m R, Ψ * H = 1 ∧ H * Ψ = 1) :
    invM H * H = 1 ∧ H * invM H = 1 := by
  unfold invM
  rw [dif_pos h]
  exact h.choose_spec

theorem mul_inv_twist {n : Type} [Fintype n] [DecidableEq n] (H : Matrix m n R) (Φ : Matrix n m R) (ρ : Matrix n n R)
    (D Dp : Matrix m m R) (Hσ : Matrix m n R) (Φσ : Matrix n m R) (h1 : Φ * H = 1) (h2 : D * Dp = 1)
    (h3 : Dp * (H * ρ) = Hσ) (h4 : Hσ * Φσ = 1) : ρ * Φσ = Φ * D := by
  calc ρ * Φσ = Φ * H * ρ * Φσ := by rw [h1, Matrix.one_mul]
    _ = Φ * (D * Dp) * H * ρ * Φσ := by rw [h2, Matrix.mul_one]
    _ = Φ * D * (Dp * (H * ρ)) * Φσ := by simp only [Matrix.mul_assoc]
    _ = Φ * D := by rw [h3, Matrix.mul_assoc (Φ * D), h4, Matrix.mul_one]

theorem mul_inv_nat {n m' n' : Type} [Fintype n] [DecidableEq n] [Fintype m'] [DecidableEq m'] [Fintype n']
    [DecidableEq n'] (H : Matrix m n R) (Φ : Matrix n m R) (H' : Matrix m' n' R) (Φ' : Matrix n' m' R) (E : Matrix n' n R)
    (G : Matrix m' m R) (h1 : Φ' * H' = 1) (h2 : H * Φ = 1) (h : H' * E = G * H) : E * Φ = Φ' * G := by
  calc E * Φ = Φ' * H' * E * Φ := by rw [h1, Matrix.one_mul]
    _ = Φ' * (G * H) * Φ := by rw [Matrix.mul_assoc Φ' H' E, h]
    _ = Φ' * G := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]

end Mat

section Dict

variable {l : ℕ} [Fact l.Prime] {K : Formalism.BasicNotions.Loc.FinExt l}

theorem sigma_eq (g : Formalism.BasicNotions.Loc.GQ l) (y : ℂ_[l]) : GaloisFrobeniusFixed.σC g y = Formalism.Per.σC g y := UpperTheory.Gal.Seam.sigC_eq l g y

example : CharZero K.1 := inferInstance

end Dict

section Build

variable {l : ℕ} [Fact l.Prime] {K : Formalism.BasicNotions.Loc.FinExt l}

theorem sm_q {M : CrystallineSemistableComparison.Model l K.1} (h : M.Sm) : IsProper M.q ∧ Smooth M.q := by
  obtain ⟨N, i, hi, hc⟩ := h.1.1
  have := isProper_pstr (CrystallineSemistableComparison.OK l K.1) N
  have hp : IsProper M.p := by rw [← hc]; infer_instance
  have hs : Smooth M.p := h.2
  exact ⟨inferInstance, inferInstance⟩

variable (K) in

abbrev IsoFam : Type 1 := ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K.1)) [Smooth q] [IsProper q] (a j : ℕ),
  CrystallineSemistableComparison.HT.Hdg q a (a + j) ≃ₗ[K.1] CrystallineSemistableComparison.Om.HodgeC q a j

def IsoNat (e : IsoFam K) : Prop := ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K.1))
  (p : Y ⟶ Spec (CommRingCat.of K.1)) [Smooth q] [IsProper q] [Smooth p] [IsProper p] (u : X ⟶ Y) (hu : u ≫ p = q)
  (a j : ℕ) (x : CrystallineSemistableComparison.HT.Hdg p a (a + j)), e q a j (CrystallineSemistableComparison.HT.pullH u hu a (a + j) x) = CrystallineSemistableComparison.Om.pullC u hu a j (e p a j x)

def eqv (e : IsoFam K) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K.1)) [Smooth q] [IsProper q] (a j m : ℕ)
    (h : a + j = m) : CrystallineSemistableComparison.HT.Hdg q a m ≃ₗ[K.1] CrystallineSemistableComparison.Om.HodgeC q a j := by
  subst h
  exact e q a j

theorem eqv_nat (e : IsoFam K) (he : IsoNat e) {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K.1))
    (p : Y ⟶ Spec (CommRingCat.of K.1)) [Smooth q] [IsProper q] [Smooth p] [IsProper p] (u : X ⟶ Y) (hu : u ≫ p = q)
    (a j m : ℕ) (h : a + j = m) (x : CrystallineSemistableComparison.HT.Hdg p a m) :
    eqv e q a j m h (CrystallineSemistableComparison.HT.pullH u hu a m x) = CrystallineSemistableComparison.Om.pullC u hu a j (eqv e p a j m h x) := by
  subst h
  exact he q p u hu a j x

theorem add_sub_fin {n : ℕ} (a : Fin (n + 1)) : (a : ℕ) + (n - a) = n := Nat.add_sub_cancel' (Nat.le_of_lt_succ a.2)

def hb (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ} (F : Frame (K := K) M.q n) (a : Fin (n + 1)) :
    Module.Basis (Fin (F.e a)) K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n) :=
  have := (sm_q hM).1
  have := (sm_q hM).2
  (F.c a).map (eqv e M.q a (n - a) n (add_sub_fin a)).symm

def bV {M : CrystallineSemistableComparison.Model l K.1} {n : ℕ} (F : Frame (K := K) M.q n) : Module.Basis (Fin F.d) ℚ_[l] (M.V n) := F.b

def Hm (P : CrystallineSemistableComparison.HT.HTPre l K.1) (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ}
    (F : Frame (K := K) M.q n) : Matrix F.Col (Fin F.d) ℂ_[l] :=
  fun c i => P.h M c.1 n (bV F i) ((hb e hM F c.1).coord c.2)

def Phi (P : CrystallineSemistableComparison.HT.HTPre l K.1) (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ}
    (F : Frame (K := K) M.q n) : Matrix (Fin F.d) F.Col ℂ_[l] :=
  invM (Hm P e hM F)

theorem sum_e (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ}
    (hr : Module.finrank ℚ_[l] (M.V n) = ∑ a ∈ Finset.range (n + 1), Module.finrank K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n))
    (F : Frame (K := K) M.q n) : ∑ a, F.e a = F.d := by
  have h1 : ∀ a : Fin (n + 1), F.e a = Module.finrank K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n) := fun a => by
    rw [Module.finrank_eq_card_basis (hb e hM F a), Fintype.card_fin]
  have h2 : F.d = Module.finrank ℚ_[l] (M.V n) := by
    have := Module.finrank_eq_card_basis F.b
    rw [Fintype.card_fin] at this
    exact this.symm
  rw [h2, hr, Finset.sum_congr rfl (fun a _ => h1 a)]
  exact Fin.sum_univ_eq_sum_range (fun a => Module.finrank K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n)) (n + 1)

theorem h_dual (P : CrystallineSemistableComparison.HT.HTPre l K.1) (M : CrystallineSemistableComparison.Model l K.1) (a n : ℕ) (v : M.V n) {ι : Type} (s : Finset ι)
    (c : ι → K.1) (φ : ι → Module.Dual K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n)) :
    P.h M a n v (∑ i ∈ s, c i • φ i) = ∑ i ∈ s, CrystallineSemistableComparison.HT.kC K.1 (c i) * P.h M a n v (φ i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => P.lin' M a n (c i) v (φ i)

theorem h_vec (P : CrystallineSemistableComparison.HT.HTPre l K.1) (M : CrystallineSemistableComparison.Model l K.1) (a n : ℕ) {ι : Type} (s : Finset ι) (r : ι → ℚ_[l])
    (v : ι → M.V n) (φ : Module.Dual K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n)) :
    P.h M a n (∑ i ∈ s, r i • v i) φ = ∑ i ∈ s, CrystallineSemistableComparison.HT.qC l (r i) * P.h M a n (v i) φ := by
  rw [map_sum, AddMonoidHom.finsetSum_apply]
  exact Finset.sum_congr rfl fun i _ => P.lin M a n (r i) (v i) φ

theorem hm_inj (P : CrystallineSemistableComparison.HT.HTPre l K.1) (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ}
    (hI : P.Inj M n) (F : Frame (K := K) M.q n) (z : Fin F.d → ℂ_[l]) (hz : (Hm P e hM F).mulVec z = 0) : z = 0 := by
  apply hI (bV F) z
  intro a φ
  by_cases ha : a ≤ n
  · let a' : Fin (n + 1) := ⟨a, Nat.lt_succ_of_le ha⟩
    let B : Module.Basis (Fin (F.e a')) K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n) := hb e hM F a'
    have hφ : φ = ∑ s, φ (B s) • B.coord s := (Module.Basis.sum_dual_apply_smul_coord B φ).symm
    have hrow : ∀ i, P.h M a n (bV F i) φ = ∑ s, CrystallineSemistableComparison.HT.kC K.1 (φ (B s)) * Hm P e hM F ⟨a', s⟩ i := by
      intro i
      calc P.h M a n (bV F i) φ = P.h M a n (bV F i) (∑ s, φ (B s) • B.coord s) := by rw [← hφ]
        _ = _ := by rw [h_dual]; rfl
    calc ∑ i, z i * P.h M a n (bV F i) φ
        = ∑ s, CrystallineSemistableComparison.HT.kC K.1 (φ (B s)) * (Hm P e hM F).mulVec z ⟨a', s⟩ := by
          simp only [hrow, Matrix.mulVec, dotProduct, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = 0 := by simp [hz]
  · have : Subsingleton (CrystallineSemistableComparison.HT.Hdg M.q a n) := (P.fin M hM a n).2 (by omega)
    have hφ : φ = 0 := by
      ext x
      rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
    simp [hφ]

theorem phi_spec (P : CrystallineSemistableComparison.HT.HTPre l K.1) (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ}
    (hr : Module.finrank ℚ_[l] (M.V n) = ∑ a ∈ Finset.range (n + 1), Module.finrank K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n))
    (hI : P.Inj M n) (F : Frame (K := K) M.q n) :
    Phi P e hM F * Hm P e hM F = 1 ∧ Hm P e hM F * Phi P e hM F = 1 := by
  apply invM_spec
  apply exists_inv_of_inj _ _ (hm_inj P e hM hI F)
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact sum_e e hM hr F

end Build

section Assembly

variable {l : ℕ} [Fact l.Prime] {K : Formalism.BasicNotions.Loc.FinExt l}

theorem equi_entry (P : CrystallineSemistableComparison.HT.HTPre l K.1) (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ}
    (F : Frame (K := K) M.q n) (σ : ↥(Formalism.BasicNotions.Loc.GK K)) (c : F.Col) (i : Fin F.d) :
    algebraMap ℚ_[l] ℂ_[l] (Formalism.L2.LocGap.Gal.χQ l σ : ℚ_[l]) ^ (c.1 : ℕ) * (Hm P e hM F * F.rho σ) c i =
      Formalism.Per.σC (σ : Formalism.BasicNotions.Loc.GQ l) (Hm P e hM F c i) := by
  have hexp : (Hm P e hM F * F.rho σ) c i =
      P.h M c.1 n (M.act n σ (bV F i)) ((hb e hM F c.1).coord c.2) := by
    rw [← (bV F).sum_repr (M.act n σ (bV F i)), h_vec]
    simp only [Matrix.mul_apply, Frame.rho, Matrix.map_apply, LinearMap.toMatrix_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
    rfl
  rw [hexp]
  have h := P.equi M hM c.1 n σ (bV F i) ((hb e hM F c.1).coord c.2)
  rw [sigma_eq] at h
  exact h

theorem isHT (P : CrystallineSemistableComparison.HT.HTPre l K.1) (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ}
    (hr : Module.finrank ℚ_[l] (M.V n) = ∑ a ∈ Finset.range (n + 1), Module.finrank K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n))
    (hI : P.Inj M n) (F : Frame (K := K) M.q n) : F.IsHT (Phi P e hM F) := by
  obtain ⟨h1, h2⟩ := phi_spec P e hM hr hI F
  refine ⟨⟨Hm P e hM F, h1, h2⟩, fun σ => ?_⟩
  have hx0 : algebraMap ℚ_[l] ℂ_[l] (Formalism.L2.LocGap.Gal.χQ l σ : ℚ_[l]) ≠ 0 := (map_ne_zero _).2 (Units.ne_zero _)
  refine mul_inv_twist (Hm P e hM F) (Phi P e hM F) (F.rho σ) _
    (Matrix.diagonal fun c : F.Col => algebraMap ℚ_[l] ℂ_[l] (Formalism.L2.LocGap.Gal.χQ l σ : ℚ_[l]) ^ (c.1 : ℕ))
    ((Hm P e hM F).map (Formalism.Per.σC (σ : Formalism.BasicNotions.Loc.GQ l))) _ h1 ?_ ?_ ?_
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext c
    show algebraMap ℚ_[l] ℂ_[l] (Formalism.L2.LocGap.Gal.χQ l σ : ℚ_[l]) ^ (-((c.1 : ℕ) : ℤ)) *
      algebraMap ℚ_[l] ℂ_[l] (Formalism.L2.LocGap.Gal.χQ l σ : ℚ_[l]) ^ (c.1 : ℕ) = 1
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hx0)]
  · funext c i
    rw [Matrix.diagonal_mul, Matrix.map_apply]
    exact equi_entry P e hM F σ c i
  · rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]

theorem coord_pull (e : IsoFam K) (he : IsoNat e) {M M' : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) (hM' : M'.Sm) {n : ℕ}
    (F : Frame (K := K) M.q n) (F' : Frame (K := K) M'.q n) (u : M'.X ⟶ M.X) (hu : u ≫ M.p = M'.p) (a : Fin (n + 1))
    (j' : Fin (F'.e a)) :
    (hb e hM' F' a).coord j' ∘ₗ CrystallineSemistableComparison.HT.pullH (CrystallineSemistableComparison.Model.genMap u hu) (CrystallineSemistableComparison.Model.genMap_q u hu) a n =
      ∑ j, LinearMap.toMatrix (F.c a) (F'.c a) (GlobalTheory.HodgeCoh.hodgePull (CrystallineSemistableComparison.Model.genMap_q u hu) a (n - a)) j' j •
        (hb e hM F a).coord j := by
  have := (sm_q hM).1
  have := (sm_q hM).2
  have := (sm_q hM').1
  have := (sm_q hM').2
  have hB : ∀ j, hb e hM F a j = (eqv e M.q a (n - a) n (add_sub_fin a)).symm (F.c a j) := fun j =>
    Module.Basis.map_apply _ _ _
  have hB' : ∀ y j, (hb e hM' F' a).repr y j = (F'.c a).repr (eqv e M'.q a (n - a) n (add_sub_fin a) y) j := by
    intro y j
    simp only [hb, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm]
  apply (hb e hM F a).ext
  intro j0
  have hnat := eqv_nat e he M'.q M.q (CrystallineSemistableComparison.Model.genMap u hu) (CrystallineSemistableComparison.Model.genMap_q u hu) a (n - a) n (add_sub_fin a)
    ((eqv e M.q a (n - a) n (add_sub_fin a)).symm (F.c a j0))
  rw [LinearEquiv.apply_symm_apply] at hnat
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, LinearMap.toMatrix_apply]
  rw [hB j0, hB', hnat]
  rfl

theorem nat_entry (P : CrystallineSemistableComparison.HT.HTPre l K.1) (e : IsoFam K) (he : IsoNat e) {M M' : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm)
    (hM' : M'.Sm) {n : ℕ} (F : Frame (K := K) M.q n) (F' : Frame (K := K) M'.q n) (u : M'.X ⟶ M.X)
    (hu : u ≫ M.p = M'.p) :
    Hm P e hM' F' * F.etMat F' (CrystallineSemistableComparison.Model.genMap_q u hu) =
      F.hodgeMat F' (CrystallineSemistableComparison.Model.genMap_q u hu) * Hm P e hM F := by
  funext c' i
  obtain ⟨a, j'⟩ := c'
  have hL : (Hm P e hM' F' * F.etMat F' (CrystallineSemistableComparison.Model.genMap_q u hu)) ⟨a, j'⟩ i =
      P.h M' a n (CrystallineSemistableComparison.Model.pullV u hu n (bV F i)) ((hb e hM' F' a).coord j') := by
    rw [← (bV F').sum_repr (CrystallineSemistableComparison.Model.pullV u hu n (bV F i)), h_vec]
    simp only [Matrix.mul_apply, Frame.etMat, Matrix.map_apply, LinearMap.toMatrix_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
    rfl
  rw [hL, P.nat M' M u hu hM' hM a n (bV F i), coord_pull e he hM hM' F F' u hu a j', h_dual, Matrix.mul_apply,
    Fintype.sum_sigma, Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Frame.hodgeMat, Matrix.map_apply, Matrix.blockDiagonal'_apply_eq]
    rfl
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro j _
    simp only [Frame.hodgeMat, Matrix.map_apply, Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hb), map_zero,
      zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem frame_ex (P : CrystallineSemistableComparison.HT.HTPre l K.1) (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ}
    (hfd : FiniteDimensional ℚ_[l] (M.V n))
    (hr : Module.finrank ℚ_[l] (M.V n) = ∑ a ∈ Finset.range (n + 1), Module.finrank K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n)) :
    ∃ F : Frame (K := K) M.q n, ∑ a, F.e a = F.d := by
  have := (sm_q hM).1
  have := (sm_q hM).2
  have : ∀ a : Fin (n + 1), FiniteDimensional K.1 (HodgeV (K := K) M.q n a) := fun a => by
    have := (P.fin M hM a n).1
    exact LinearEquiv.finiteDimensional (eqv e M.q a (n - a) n (add_sub_fin a))
  have : FiniteDimensional ℚ_[l] (EtV (K := K) M.q n) := hfd
  exact ⟨⟨_, Module.finBasis ℚ_[l] (EtV (K := K) M.q n), fun a => _,
    fun a => Module.finBasis K.1 (HodgeV (K := K) M.q n a)⟩, sum_e e hM hr _⟩

end Assembly

theorem htSpecGood_of (hB : CrystallineSemistableComparison.Onto.HTBij) (hI : HdgIso) (hF : CrystallineSemistableComparison.Onto.EtFin) : HTSpecGood := by
  intro l _ K n
  have : FiniteDimensional ℚ_[l] K.1 := K.2
  obtain ⟨P, hP⟩ := hB l K.1
  obtain ⟨e, he⟩ := hI K.1
  have hrank : ∀ M : CrystallineSemistableComparison.Model l K.1, M.Sm → (∃ d, SmoothOfRelativeDimension d M.p) →
      Module.finrank ℚ_[l] (M.V n) = ∑ a ∈ Finset.range (n + 1), Module.finrank K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n) :=
    fun M hM hd => ((hP M hM).2.2 hd.choose hd.choose_spec n).2
  refine ⟨fun M hM hd => frame_ex P e hM (hF l K.1 M hM n) (hrank M hM hd), fun M hM hd F => Phi P e hM F,
    fun M hM hd F => isHT P e hM (hrank M hM hd) ((hP M hM).1 n) F, ?_⟩
  intro M M' hM hM' hd hd' F F' u hu
  have h1 := (phi_spec P e hM' (hrank M' hM' hd') ((hP M' hM').1 n) F').1
  have h2 := (phi_spec P e hM (hrank M hM hd) ((hP M hM).1 n) F).2
  exact mul_inv_nat _ _ _ _ _ _ h1 h2 (nat_entry P e he hM hM' F F' u hu)

end UpperTheory.Gal.Seam.Spec
