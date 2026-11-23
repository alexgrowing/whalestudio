import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkedSumIrr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairGramInvCongruent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatedPairsSamePolarization

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

variable {p : ℕ} [Fact p.Prime]

structure DPair (G : HTGroup p) where

  β : G.Cˣ

  γ : G.Cˣ

  c : ℚˣ
  sym : sh G β = β
  sim : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c * β
  reg : (minpoly G.F (γ : G.C)).natDegree = G.n ∧ (minpoly G.F (γ : G.C)).Separable
  trivAf : ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ), Triv G (AfP p) β x t

  posR : ∀ v : InfinitePlace G.F, ∀ x : Fin G.n → ℂ, x ≠ 0 →
    (sigPosH (G.gram_herm v) = 1 → 0 < (star x ⬝ᵥ ((G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re) ∧
    (sigPosH (G.gram_herm v) ≠ 1 → (star x ⬝ᵥ ((G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re < 0)

namespace DPair

variable {G : HTGroup p}

def pol (P : DPair G) : Polynomial G.F := minpoly G.F (P.γ : G.C)

def Rel (P Q : DPair G) : Prop :=
  ∃ (y : G.Cˣ) (s : ℚ), 0 < s ∧ (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y) ∧ Q.γ = y * P.γ * y⁻¹

def cent (P : DPair G) : Subgroup (G.Cˣ × ℚˣ) where
  carrier := {y | y.1 * P.γ = P.γ * y.1 ∧ (y.1 : G.C) * P.β * sh G y.1 = algebraMap ℚ G.C y.2 * P.β}
  one_mem' := ⟨by simp, by simp [sh]⟩
  mul_mem' := by
    rintro ⟨y, s⟩ ⟨y', s'⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨?_, ?_⟩
    · change y * y' * P.γ = P.γ * (y * y')
      change y * P.γ = P.γ * y at h1
      change y' * P.γ = P.γ * y' at h1'
      rw [mul_assoc, h1', ← mul_assoc, h1, mul_assoc]
    · change (y : G.C) * P.β * sh G y = algebraMap ℚ G.C s * P.β at h2
      change (y' : G.C) * P.β * sh G y' = algebraMap ℚ G.C s' * P.β at h2'
      change ((y * y' : G.Cˣ) : G.C) * P.β * sh G ((y * y' : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((s * s' : ℚˣ) : ℚ) * P.β
      have e : sh G ((y * y' : G.Cˣ) : G.C) = sh G y' * sh G y := by
        simp only [sh, Units.val_mul, map_mul, MulOpposite.unop_mul]
      rw [e, Units.val_mul, Units.val_mul, map_mul]
      calc (y : G.C) * y' * P.β * (sh G y' * sh G y) = y * (y' * P.β * sh G y') * sh G y := by
            simp only [mul_assoc]
        _ = algebraMap ℚ G.C s' * (y * P.β * sh G y) := by
            rw [h2']; simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
        _ = _ := by rw [h2, ← mul_assoc, ← map_mul, ← map_mul, mul_comm (s' : ℚ)]
  inv_mem' := by
    rintro ⟨y, s⟩ ⟨h1, h2⟩
    change y * P.γ = P.γ * y at h1
    change (y : G.C) * P.β * sh G y = algebraMap ℚ G.C s * P.β at h2
    refine ⟨?_, ?_⟩
    · change y⁻¹ * P.γ = P.γ * y⁻¹
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h1, mul_inv_cancel_right]
    · change ((y⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((y⁻¹ : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * P.β
      have e : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
        simp only [sh]
        rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
      have hs : algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * algebraMap ℚ G.C (s : ℚ) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      calc ((y⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((y⁻¹ : G.Cˣ) : G.C)
          = algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * (((y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C (s : ℚ) * P.β) *
              sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
            rw [← mul_assoc, ← mul_assoc, ← mul_assoc, Algebra.commutes ((s⁻¹ : ℚˣ) : ℚ), mul_assoc ((y⁻¹ : G.Cˣ) : G.C) _ (algebraMap ℚ G.C (s : ℚ)), hs, mul_one]
        _ = algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * ((((y⁻¹ : G.Cˣ) : G.C) * y) * P.β *
              (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C))) := by
            rw [← h2]; simp only [mul_assoc]
        _ = _ := by rw [Units.inv_mul, e, one_mul, mul_one]

def self (P : DPair G) : P.cent := ⟨(P.γ, P.c), rfl, P.sim⟩

def toAf (P : DPair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) : P.cent →* G.GAf :=
  MonoidHom.codRestrict
    ((((MulAut.conj x).toMonoidHom.comp (Units.map (inC G (AfP p)).toMonoidHom)).prodMap
      (Units.map (algebraMap ℚ (AfP p)).toMonoidHom)).comp P.cent.subtype) _ fun y => by
      have h := congrArg (inC G (AfP p)) y.2.2
      rw [map_mul, map_mul, map_mul] at h
      have e1 : inC G (AfP p) (sh G y.1.1) = (starT G.star (AfP p) (inC G (AfP p) y.1.1)).unop :=
        (starT_tmul G.star (AfP p) 1 _).symm
      have e2 : inC G (AfP p) (algebraMap ℚ G.C y.1.2) =
          algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (algebraMap ℚ (AfP p) y.1.2) := by
        rw [← IsScalarTower.algebraMap_apply]
        exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C).commutes _
      rw [e1, e2] at h
      exact conj_mul_star (starT G.star (AfP p)) (inC G (AfP p) P.β) x
        (Units.map (inC G (AfP p)).toMonoidHom y.1.1) t _ hx h

def atP (P : DPair G) : Gp G := locC G (P.γ, P.c)

def toQr (P : DPair G) (r : ℕ) (z : Gr G r) : P.cent →* Gr G r :=
  ((carry G r z).comp (locC G)).comp P.cent.subtype

def termAt (P : DPair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G r) : ℂ :=
  GlobalTheory.LKCount.pointSum (P.toAf x t hx) (P.toQr r z) (sigG G r) Kf K (P.toAf x t hx P.self) δ f φ

def term (P : DPair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  if h : ∃ dz : Gr G r × Gr G r, IsNrm G r P.atP dz.1 dz.2 then
    P.termAt Kf f r K φ P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec
      h.choose.1 h.choose.2
  else 0

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
private theorem lkMid_sh_mul_eq_sh_mul_sh_rev (a b : G.C) :
    _root_.GlobalTheory.LKMid.sh G (a * b) =
      _root_.GlobalTheory.LKMid.sh G b * _root_.GlobalTheory.LKMid.sh G a := by
  simp only [_root_.GlobalTheory.LKMid.sh, map_mul, MulOpposite.unop_mul]

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
private theorem lkMid_sh_mul_sh_units_inv_eq_one (y : (G.C)ˣ) :
    _root_.GlobalTheory.LKMid.sh G y *
      _root_.GlobalTheory.LKMid.sh G ((y⁻¹ : (G.C)ˣ) : G.C) = 1 := by
  rw [← lkMid_sh_mul_eq_sh_mul_sh_rev, Units.inv_mul, _root_.GlobalTheory.LKMid.sh_one_eq]

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in

theorem _root_.GlobalTheory.LKDef.DPair.rel_equivalence (G : _root_.GlobalTheory.LKTrip.HTGroup p) :
    Equivalence (_root_.GlobalTheory.LKDef.DPair.Rel (G := G)) := by
  refine ⟨fun P => ?_, fun {P₁ P₂} h => ?_, fun {P₁ P₂ P₃} h h' => ?_⟩
  · refine ⟨1, 1, one_pos, ?_, by simp⟩
    simp [_root_.GlobalTheory.LKMid.sh_one_eq]
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_, ?_⟩
    · rw [hβ]
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul,
        inv_mul_cancel₀ hs.ne', one_smul]
      simp only [mul_assoc, Units.inv_mul_cancel_left, lkMid_sh_mul_sh_units_inv_eq_one, mul_one]
      rw [mul_inv_cancel₀ hs.ne', one_smul]
    · rw [hγ]; group
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    obtain ⟨y', s', hs', hβ', hγ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_, ?_⟩
    · rw [hβ', hβ, Units.val_mul, lkMid_sh_mul_eq_sh_mul_sh_rev]
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
      rw [mul_comm s s']
    · rw [hγ', hγ]; group

theorem pol_eq_of_rel {P Q : DPair G} (h : P.Rel Q) : Q.pol = P.pol := by
  obtain ⟨y, s, _, _, hγ⟩ := h
  have h := minpoly.algEquiv_eq (Pair.innerAlgEquiv G.F y) (P.γ : G.C)
  simp only [pol, hγ, Units.val_mul]
  exact h

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in

theorem _root_.GlobalTheory.LKDef.DPair.mk_eq_iff (P Q : _root_.GlobalTheory.LKDef.DPair G) :
    Quot.mk (_root_.GlobalTheory.LKDef.DPair.Rel (G := G)) P = Quot.mk _ Q ↔
      P.Rel Q :=
  ⟨fun h => (_root_.GlobalTheory.LKDef.DPair.rel_equivalence G).eqvGen_iff.mp (Quot.eqvGen_exact h),
    Quot.sound⟩

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in

theorem _root_.GlobalTheory.LKDef.DPair.rel_out (P : _root_.GlobalTheory.LKDef.DPair G) :
    P.Rel
      (Quot.out (Quot.mk (_root_.GlobalTheory.LKDef.DPair.Rel (G := G)) P)) :=
  (_root_.GlobalTheory.LKDef.DPair.mk_eq_iff P _).mp (Quot.out_eq _).symm

theorem beta_ne_pair (P : DPair G) (Q : Pair G) (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1)
    (y : Fin G.n → ℂ) (hy : (star y ⬝ᵥ (G.gram v *ᵥ y)).re < 0) : P.β ≠ Q.β := by
  intro h
  obtain ⟨Z, hZ⟩ := Pair.gram_psi_inv_congr p G Q v
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have e : (Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ (((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hx : ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ y ≠ 0 := fun h0 => hy0 (by
    rw [← e, h0, Matrix.mulVec_zero])
  have h1 := (P.posR v _ hx).1 hv
  rw [h, hZ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, Matrix.dotProduct_mulVec (star _) (_ᴴ),
    ← Matrix.star_mulVec, e] at h1
  exact lt_asymm h1 hy

end DPair

def DCls (G : HTGroup p) : Type := Quot (DPair.Rel (G := G))

def dSumIrr (G : HTGroup p) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ)
    (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  ∑ᶠ q : DCls G, if Irreducible (Quot.out q).pol then wt (Quot.out q).pol * (Quot.out q).term Kf f r K φ else 0

def MoveDef : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (wt sel : Polynomial G.F → ℂ), IsSel G sel →
    ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ),
      0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) →
      markedSumIrr G wt sel Kf f r K φ = dSumIrr G wt Kf f r K φ

theorem MoveDef.of_isTest (H : MoveDef) (G : HTGroup p) (ha : G.a = 1) (hn : Odd G.n) (wt sel : Polynomial G.F → ℂ)
    (hsel : IsSel G sel) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) (r : ℕ) (hr : 0 < r) (K : Subgroup (Gr G r))
    (φ : Gr G r → ℂ) (hφ : IsTest (sigG G r) (KHT p G.m G.n r G.Fw) K φ) :
    markedSumIrr G wt sel L.K.toSubgroup f r K φ = dSumIrr G wt L.K.toSubgroup f r K φ :=
  H p G ha hn wt sel hsel _ f r K φ hr hf.2.2.1 hφ.2.2.1

namespace Example

open GlobalTheory.LKTrip.Example GlobalTheory.LKMid.Example

def exD : DPair (ex 1 one_ne_zero) where
  β := exPair.β
  γ := exPair.γ
  c := exPair.c
  sym := exPair.sym
  sim := exPair.sim
  reg := exPair.reg
  trivAf := exPair.trivAf
  posR := by
    intro v x hx
    have hv : sigPosH ((ex 1 one_ne_zero).gram_herm v) = 1 := by
      exact (sigPos_Hc 1 v.embedding).trans (if_pos one_pos)
    refine ⟨fun _ => ?_, fun h => absurd hv h⟩
    show 0 < (star x ⬝ᵥ (((ex 1 one_ne_zero).gram v *
      (ex 1 one_ne_zero).psi v (((1 : (ex 1 one_ne_zero).Cˣ)⁻¹ : (ex 1 one_ne_zero).Cˣ) : (ex 1 one_ne_zero).C)) *ᵥ x)).re
    rw [inv_one, Units.val_one, map_one, Matrix.mul_one]
    revert x
    show ∀ x : Fin 1 → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (gramAt (Hc 1) (v.embedding : QI →+* ℂ) *ᵥ x)).re
    intro x hx
    have h0 : x 0 ≠ 0 := fun h => hx (by ext i; rw [Subsingleton.elim i 0]; exact h)
    have h1 : (v.embedding : QI →+* ℂ) 1 = 1 := map_one _
    have h2 := Complex.normSq_pos.2 h0
    rw [Complex.normSq_apply] at h2
    have e : gramAt (Hc 1) (v.embedding : QI →+* ℂ) = 1 := by
      ext i j; fin_cases i; fin_cases j; simp [gramAt, Hc]; exact h1
    rw [e, Matrix.one_mulVec]
    simpa [dotProduct] using h2

theorem exD_irreducible : Irreducible exD.pol := by
  have : exD.pol = Polynomial.X - Polynomial.C (2 + gi) :=
    Pair.ofScalar_pol (ex 1 one_ne_zero) rfl a21 _ norm_gaussian_element_eq_five
  rw [this]; exact Polynomial.irreducible_X_sub_C _

theorem padicInt_four_squares (l : ℕ) [Fact l.Prime] (z : ℤ_[l]) :
    ∃ a b c d : ℤ_[l], a * a + b * b + c * c + d * d = z := by
  let f : ℤ_[l] × ℤ_[l] × ℤ_[l] × ℤ_[l] → ℤ_[l] := fun t =>
    t.1 * t.1 + t.2.1 * t.2.1 + t.2.2.1 * t.2.2.1 + t.2.2.2 * t.2.2.2
  have hf : Continuous f := by fun_prop
  have hc : IsClosed (Set.range f) := (isCompact_range hf).isClosed
  have hs : Set.range (Nat.cast : ℕ → ℤ_[l]) ⊆ Set.range f := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
    refine ⟨(a, b, c, d), ?_⟩
    rw [← h]; simp only [f]; push_cast; ring
  have hz : z ∈ Set.range f :=
    (hc.closure_subset_iff.2 hs) ((PadicInt.denseRange_natCast (p := l)) z)
  obtain ⟨⟨a, b, c, d⟩, h⟩ := hz
  exact ⟨a, b, c, d, h⟩

theorem finiteAdeleRingAway_sum_four_squares_eq_neg_one (p : ℕ) : ∃ a b c d : AfP p, a * a + b * b + c * c + d * d = -1 := by
  have key : ∀ v : AwayP p, ∃ a b c d : v.1.adicCompletionIntegers ℚ, a * a + b * b + c * c + d * d = -1 := by
    intro v
    haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v.1 : ℕ)) := ⟨(Rat.HeightOneSpectrum.primesEquiv v.1).2⟩
    letI : Algebra ℤ (v.1.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
    let e : v.1.adicCompletionIntegers ℚ ≃+* ℤ_[Rat.HeightOneSpectrum.primesEquiv v.1] :=
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v.1).toAlgEquiv.toRingEquiv
    obtain ⟨a, b, c, d, h⟩ := padicInt_four_squares _ (e (-1))
    refine ⟨e.symm a, e.symm b, e.symm c, e.symm d, ?_⟩
    apply e.injective
    simpa using h
  choose a b c d h using key
  let mk : (∀ v : AwayP p, v.1.adicCompletionIntegers ℚ) → AfP p := fun a =>
    (⟨fun v => (a v : v.1.adicCompletion ℚ), Filter.Eventually.of_forall fun v => (a v).2⟩ :
      RestrictedProduct (fun v : AwayP p => v.1.adicCompletion ℚ)
        (fun v => (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) Filter.cofinite)
  refine ⟨mk a, mk b, mk c, mk d, ?_⟩
  apply Subtype.ext
  funext v
  have := congrArg (fun z : v.1.adicCompletionIntegers ℚ => (z : v.1.adicCompletion ℚ)) (h v)
  exact this

def H3 : Matrix (Fin 3) (Fin 3) QI := Matrix.diagonal ![1, -1, -1]

theorem conj_diagHermitian : H3.map (IsCMField.complexConj QI : QI →+* QI) = H3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [H3]

theorem isHermitian_diagHermitian : (H3.map (IsCMField.complexConj QI : QI →+* QI))ᵀ = H3 := by
  rw [conj_diagHermitian, H3, Matrix.diagonal_transpose]

theorem diagHermitian_mul_self : H3 * H3 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [H3]

theorem det_diagHermitian_ne_zero : H3.det ≠ 0 := by simp [H3, Fin.prod_univ_three]

theorem gramMatrix_diagHermitian (τ : QI →+* ℂ) : gramAt H3 τ = Matrix.diagonal ![1, -1, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gramAt, H3]

theorem signature_diagHermitian (τ : QI →+* ℂ) : sigPos isHermitian_diagHermitian τ = 1 ∧ sigNeg isHermitian_diagHermitian τ = 2 := by
  have hA := isHermitian_gramAt isHermitian_diagHermitian τ
  have hsq : ∀ i, hA.eigenvalues i = 1 ∨ hA.eigenvalues i = -1 := by
    intro i
    have h := hA.eigenvalues_mem_spectrum_real i
    rw [← spectrum.algebraMap_mem_iff ℂ] at h
    have hsp : spectrum ℂ (gramAt H3 τ) = Set.range ![(1 : ℂ), -1, -1] := by
      rw [gramMatrix_diagHermitian, spectrum_diagonal]
    rw [hsp] at h
    obtain ⟨j, hj⟩ := h
    fin_cases j
    · left; have : ((1 : ℝ) : ℂ) = (hA.eigenvalues i : ℂ) := by simpa using hj
      exact_mod_cast this.symm
    · right; have : ((-1 : ℝ) : ℂ) = (hA.eigenvalues i : ℂ) := by simpa using hj
      exact_mod_cast this.symm
    · right; have : ((-1 : ℝ) : ℂ) = (hA.eigenvalues i : ℂ) := by simpa using hj
      exact_mod_cast this.symm
  have ht := hA.trace_eq_sum_eigenvalues
  have htr : (gramAt H3 τ).trace = -1 := by rw [gramMatrix_diagHermitian]; simp [Matrix.trace_fin_three, Fin.sum_univ_three]
  rw [htr, Fin.sum_univ_three] at ht
  have ht' : hA.eigenvalues 0 + hA.eigenvalues 1 + hA.eigenvalues 2 = -1 := by
    have : (((-1 : ℝ)) : ℂ) = ((hA.eigenvalues 0 + hA.eigenvalues 1 + hA.eigenvalues 2 : ℝ) : ℂ) := by
      push_cast; exact ht
    exact_mod_cast this.symm
  show Fintype.card {i : Fin 3 // 0 < hA.eigenvalues i} = 1 ∧ Fintype.card {i : Fin 3 // hA.eigenvalues i < 0} = 2
  rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_filter, Finset.card_filter, Fin.sum_univ_three,
    Fin.sum_univ_three]
  rcases hsq 0 with h0 | h0 <;> rcases hsq 1 with h1 | h1 <;> rcases hsq 2 with h2 | h2 <;>
    rw [h0, h1, h2] at ht' ⊢ <;> first | (exfalso; linarith) | norm_num

theorem not_cube (b : QI) : b ^ 3 ≠ 5 * (2 + gi) := by
  intro h
  set s : ℚ_[5] := gaussianToQFive gi with hs
  have hs2 : s ^ 2 = -1 := by rw [hs, ← map_pow, zeta_sq, map_neg, map_one]
  have hn : ‖s‖ = 1 := by
    have : ‖s‖ ^ 2 = 1 := by rw [← norm_pow, hs2, norm_neg, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this
  have h2 : ‖(2 : ℚ_[5])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := 5) 2
  have hp : ‖2 + s‖ ≤ 1 := (Padic.nonarchimedean _ _).trans (max_le h2 hn.le)
  have hm : ‖2 + -s‖ ≤ 1 := (Padic.nonarchimedean _ _).trans (max_le h2 (by rw [norm_neg, hn]))
  have hpm : (2 + s) * (2 + -s) = 5 := by linear_combination (-1 : ℚ_[5]) * hs2
  have h5 : (5 : ℚ_[5]) ≠ 0 := by norm_num
  have hp0 : 2 + s ≠ 0 := left_ne_zero_of_mul (hpm ▸ h5)
  have hm0 : 2 + -s ≠ 0 := right_ne_zero_of_mul (hpm ▸ h5)
  have v5 : (5 : ℚ_[5]).valuation = 1 := by simpa using Padic.valuation_p (p := 5)
  have e1 := congrArg Padic.valuation hpm
  rw [Padic.valuation_mul hp0 hm0, v5] at e1
  have e2 := congrArg (fun z => (gaussianToQFive z).valuation) h
  simp only [map_pow, map_mul, map_add, map_ofNat] at e2
  rw [Padic.valuation_pow, ← hs, Padic.valuation_mul h5 hp0, v5] at e2
  rw [Padic.norm_le_one_iff_val_nonneg] at hp hm
  push_cast at e2
  omega

theorem quat_mul {R S : Type} [CommRing R] [Ring S] [Algebra R S] (u i j k : S) (a a' b c d : R) (ha : a' = -a)
    (h : a * a + b * b + c * c + d * d = -1)
    (uu : u * u = u) (ui : u * i = i) (uj : u * j = j) (uk : u * k = k)
    (iu : i * u = i) (ii : i * i = -u) (ij : i * j = k) (ik : i * k = -j)
    (ju : j * u = j) (ji : j * i = -k) (jj : j * j = -u) (jk : j * k = i)
    (ku : k * u = k) (ki : k * i = j) (kj : k * j = -i) (kk : k * k = -u) :
    (1 + (a - 1) • u + b • i + c • j + d • k) * (1 + (a' - 1) • u + b • i + c • j + d • k) = 1 := by
  have : (1 + (a - 1) • u + b • i + c • j + d • k) * (1 + (a' - 1) • u + b • i + c • j + d • k) =
      1 - (a * a + b * b + c * c + d * d + 1) • u := by
    subst ha
    simp only [mul_add, add_mul, smul_mul_smul_comm, one_mul, mul_one, uu, ui, uj, uk, iu, ii, ij, ik, ju, ji, jj,
      jk, ku, ki, kj, kk]
    module
  rw [this, h]; simp

theorem adjointInvolution_diagHermitian (x : Matrix (Fin 3) (Fin 3) QI) :
    (hermStar H3 det_diagHermitian_ne_zero x).unop = H3 * (x.map (IsCMField.complexConj QI : QI →+* QI))ᵀ * H3 := by
  rw [hermStar_apply, conj_diagHermitian, Matrix.inv_eq_left_inv diagHermitian_mul_self]

theorem gi_mul_gi : gi * gi = -1 := by rw [← sq]; exact zeta_sq

theorem diagHermitian_trivial_of_sumFourSquares (R : Type) [CommRing R] [Algebra ℚ R] (a b c d : R) (h : a * a + b * b + c * c + d * d = -1) :
    ∃ x : (R ⊗[ℚ] Matrix (Fin 3) (Fin 3) QI)ˣ,
      (x : R ⊗[ℚ] Matrix (Fin 3) (Fin 3) QI) * ((1 : R) ⊗ₜ H3) * (starT (hermStar H3 det_diagHermitian_ne_zero) R x).unop = 1 := by
  let u : Matrix (Fin 3) (Fin 3) QI := !![0, 0, 0; 0, 1, 0; 0, 0, 1]
  let i : Matrix (Fin 3) (Fin 3) QI := !![0, 0, 0; 0, gi, 0; 0, 0, -gi]
  let j : Matrix (Fin 3) (Fin 3) QI := !![0, 0, 0; 0, 0, 1; 0, -1, 0]
  let k : Matrix (Fin 3) (Fin 3) QI := !![0, 0, 0; 0, 0, gi; 0, gi, 0]
  let φ : Matrix (Fin 3) (Fin 3) QI →+* R ⊗[ℚ] Matrix (Fin 3) (Fin 3) QI :=
    (Algebra.TensorProduct.includeRight : Matrix (Fin 3) (Fin 3) QI →ₐ[ℚ] R ⊗[ℚ] Matrix (Fin 3) (Fin 3) QI)
  have t : (u * u = u ∧ u * i = i ∧ u * j = j ∧ u * k = k) ∧ (i * u = i ∧ i * i = -u ∧ i * j = k ∧ i * k = -j) ∧
      (j * u = j ∧ j * i = -k ∧ j * j = -u ∧ j * k = i) ∧ (k * u = k ∧ k * i = j ∧ k * j = -i ∧ k * k = -u) := by
    simp [u, i, j, k, gi_mul_gi]
    ext s; fin_cases s <;> rfl
  obtain ⟨⟨uu, ui, uj, uk⟩, ⟨iu, ii, ij, ik⟩, ⟨ju, ji, jj, jk⟩, ⟨ku, ki, kj, kk⟩⟩ := t
  have key : ∀ a a' : R, a' = -a → a * a + b * b + c * c + d * d = -1 →
      (1 + (a - 1) • φ u + b • φ i + c • φ j + d • φ k) * (1 + (a' - 1) • φ u + b • φ i + c • φ j + d • φ k) = 1 :=
    fun a a' ha h => by
      apply quat_mul _ _ _ _ _ _ _ _ _ ha h <;> rw [← map_mul] <;> simp only [*, map_neg]
  refine ⟨⟨_, _, key a (-a) rfl h, key (-a) a (neg_neg a).symm (by rw [neg_mul_neg]; exact h)⟩, ?_⟩
  rw [mul_assoc]
  convert key a (-a) rfl h using 2
  have e : ∀ (r : R) (m : Matrix (Fin 3) (Fin 3) QI), r • φ m = r ⊗ₜ m := fun r m => by
    show r • ((1 : R) ⊗ₜ[ℚ] m) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have s : H3 * (hermStar H3 det_diagHermitian_ne_zero u).unop = -u ∧ H3 * (hermStar H3 det_diagHermitian_ne_zero i).unop = i ∧
      H3 * (hermStar H3 det_diagHermitian_ne_zero j).unop = j ∧ H3 * (hermStar H3 det_diagHermitian_ne_zero k).unop = k ∧ H3 = 1 - u - u := by
    simp only [adjointInvolution_diagHermitian, ← Matrix.mul_assoc, diagHermitian_mul_self, Matrix.one_mul]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ext s t <;> fin_cases s <;> fin_cases t <;>
      simp [u, i, j, k, H3, conj_gi] <;> norm_num
  obtain ⟨su, si, sj, sk, sH⟩ := s
  simp only [e, map_add, map_one, MulOpposite.unop_add, MulOpposite.unop_one, starT_tmul, mul_add, mul_one,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, su, si, sj, sk]
  congr 3
  rw [sH, TensorProduct.tmul_sub, TensorProduct.tmul_sub, TensorProduct.tmul_neg, ← Algebra.TensorProduct.one_def,
    ← e, ← e, ← e]
  module

def g3 : Matrix (Fin 3) (Fin 3) QI := !![0, 0, 2 - gi; 2 + gi, 0, 0; 0, 2 + gi, 0]

theorem cubeRootMatrix_mul_conjTranspose : g3 * (g3.map (IsCMField.complexConj QI : QI →+* QI))ᵀ = (5 : QI) • 1 := by
  ext s t; fin_cases s <;> fin_cases t <;>
    simp [g3, Matrix.mul_apply, Fin.sum_univ_three, conj_gi, map_ofNat] <;> linear_combination (-1 : QI) * gi_mul_gi

theorem cubeRootMatrix_pow_three : g3 ^ 3 = algebraMap QI _ (5 * (2 + gi)) := by
  rw [Algebra.algebraMap_eq_smul_one, pow_three]
  ext s t; fin_cases s <;> fin_cases t <;>
    simp [g3, Matrix.mul_apply, Fin.sum_univ_three] <;> linear_combination (-(2 + gi)) * gi_mul_gi

theorem det_cubeRootMatrix_ne_zero : g3.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det cubeRootMatrix_mul_conjTranspose
  rw [Matrix.det_mul, h] at this
  simp at this
  norm_num at this

theorem irreducible_cubic : Irreducible (Polynomial.X ^ 3 - Polynomial.C (5 * (2 + gi)) : Polynomial QI) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_three not_cube

theorem minpoly_cubeRootMatrix : minpoly QI g3 = Polynomial.X ^ 3 - Polynomial.C (5 * (2 + gi)) := by
  refine (minpoly.eq_of_irreducible_of_monic irreducible_cubic ?_ (Polynomial.monic_X_pow_sub_C _ three_ne_zero)).symm
  rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, cubeRootMatrix_pow_three, sub_self]

def unitaryOneTwoGaussian : HTGroup 5 :=
  ofHerm QI ⊤ hK_QI (gaussianToQFive.comp (⊤ : Subfield QI).subtype) 3 (by norm_num) H3 isHermitian_diagHermitian det_diagHermitian_ne_zero
    (fun τ => Or.inl ⟨(signature_diagHermitian τ).1, (signature_diagHermitian τ).2⟩) 1 (fun _ => (algebraMap ℚ_[5] (PadicAlgCl 5)).comp gaussianToQFive)
    (fun _ _ => rfl) (fun i j _ _ => Subsingleton.elim i j)
    (fun τ hτ => ⟨0, AlgEquiv.refl, by ext x; exact hτ ⟨x, Subfield.mem_top x⟩⟩)
    (haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ;
      (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl 5).toRingHom)
    (haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ;
      (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ).toRingHom)

theorem unitaryOneTwo_rank_eq_three : unitaryOneTwoGaussian.n = 3 := rfl

theorem signature_unitaryOneTwo (v : InfinitePlace unitaryOneTwoGaussian.F) : sigPosH (unitaryOneTwoGaussian.gram_herm v) = 1 := (signature_diagHermitian v.embedding).1

theorem unitaryOneTwo_numSignaturePlaces : unitaryOneTwoGaussian.a = 1 := by
  show Fintype.card {v : InfinitePlace QI // sigPos isHermitian_diagHermitian v.embedding = 1} = 1
  simp only [fun v : InfinitePlace QI => (signature_diagHermitian v.embedding).1]
  rw [Fintype.card_subtype_true, card_infinitePlace_QI]

def b3 : (Matrix (Fin 3) (Fin 3) QI)ˣ := ⟨H3, H3, diagHermitian_mul_self, diagHermitian_mul_self⟩

theorem gramMatrix_mul_diagHermitian (τ : QI →+* ℂ) : gramAt H3 τ * H3.map τ = 1 := by
  rw [gramAt, ← Matrix.transpose_map, show H3ᵀ = H3 from Matrix.diagonal_transpose _, ← Matrix.map_mul, diagHermitian_mul_self,
    Matrix.map_one _ (map_zero τ) (map_one τ)]

def definitePairUnitaryOneTwo : DPair unitaryOneTwoGaussian where
  β := b3
  γ := Matrix.GeneralLinearGroup.mkOfDetNeZero g3 det_cubeRootMatrix_ne_zero
  c := Units.mk0 5 (by norm_num)
  sym := by
    show (hermStar H3 det_diagHermitian_ne_zero H3).unop = H3
    rw [adjointInvolution_diagHermitian, isHermitian_diagHermitian, diagHermitian_mul_self, Matrix.one_mul]
  sim := by
    show g3 * H3 * (hermStar H3 det_diagHermitian_ne_zero g3).unop = algebraMap ℚ (Matrix (Fin 3) (Fin 3) QI) 5 * H3
    rw [adjointInvolution_diagHermitian, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc g3 H3 H3, diagHermitian_mul_self, Matrix.mul_one,
      cubeRootMatrix_mul_conjTranspose, IsScalarTower.algebraMap_apply ℚ QI, Algebra.algebraMap_eq_smul_one (R := QI), map_ofNat]
  reg := by
    show (minpoly QI g3).natDegree = 3 ∧ (minpoly QI g3).Separable
    rw [minpoly_cubeRootMatrix]
    exact ⟨Polynomial.natDegree_X_pow_sub_C, irreducible_cubic.separable⟩
  trivAf := by
    obtain ⟨a, b, c, d, h⟩ := finiteAdeleRingAway_sum_four_squares_eq_neg_one 5
    obtain ⟨x, hx⟩ := diagHermitian_trivial_of_sumFourSquares (AfP 5) a b c d h
    exact ⟨x, 1, hx.trans (map_one (algebraMap (AfP 5) (AfP 5 ⊗[ℚ] Matrix (Fin 3) (Fin 3) QI))).symm⟩
  posR := by
    intro v x hx
    refine ⟨fun _ => ?_, fun h => absurd (signature_unitaryOneTwo v) h⟩
    suffices h : ∀ (τ : QI →+* ℂ) (x : Fin 3 → ℂ), x ≠ 0 → 0 < (star x ⬝ᵥ ((gramAt H3 τ * H3.map τ) *ᵥ x)).re from
      h v.embedding x hx
    intro τ x hx
    rw [gramMatrix_mul_diagHermitian, Matrix.one_mulVec]
    open scoped ComplexOrder in
    exact (Complex.pos_iff.1 (dotProduct_star_self_pos_iff.2 hx)).1

theorem definitePair_minpoly : definitePairUnitaryOneTwo.pol = Polynomial.X ^ 3 - Polynomial.C (5 * (2 + gi)) := minpoly_cubeRootMatrix

theorem definitePair_minpoly_irreducible : Irreducible definitePairUnitaryOneTwo.pol := by
  rw [definitePair_minpoly]; exact irreducible_cubic

theorem definitePair_unit_ne_pairUnit (Q : Pair unitaryOneTwoGaussian) : definitePairUnitaryOneTwo.β ≠ Q.β := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace unitaryOneTwoGaussian.F) := inferInstance
  refine definitePairUnitaryOneTwo.beta_ne_pair Q v (signature_unitaryOneTwo v) (![0, 1, 0] : Fin 3 → ℂ) ?_
  suffices h : ∀ τ : QI →+* ℂ, (star (![0, 1, 0] : Fin 3 → ℂ) ⬝ᵥ (gramAt H3 τ *ᵥ ![0, 1, 0])).re < 0 from
    h v.embedding
  intro τ
  rw [gramMatrix_diagHermitian]
  simp [dotProduct, Fin.sum_univ_three, Matrix.mulVec_diagonal]

theorem exists_rank_three : ∃ G : HTGroup 5, G.n = 3 ∧ G.a = 1 ∧ Odd G.n ∧ (∃ sel, IsSel G sel) ∧
    Nonempty G.Level ∧ ∃ q : DCls G, Irreducible (Quot.out q).pol :=
  ⟨unitaryOneTwoGaussian, rfl, unitaryOneTwo_numSignaturePlaces, ⟨1, rfl⟩, exists_isSel _ unitaryOneTwo_numSignaturePlaces.le, GlobalTheory.LKTrip.LevelExists.level_exists 5 unitaryOneTwoGaussian,
    Quot.mk _ definitePairUnitaryOneTwo, by rw [DPair.pol_eq_of_rel definitePairUnitaryOneTwo.rel_out]; exact definitePair_minpoly_irreducible⟩

example : (ex 1 one_ne_zero).a = 1 ∧ Odd (ex 1 one_ne_zero).n ∧ (∃ sel, IsSel (ex 1 one_ne_zero) sel) ∧
    ∃ q : DCls (ex 1 one_ne_zero), Irreducible (Quot.out q).pol :=
  ⟨a_ex_one, ⟨0, rfl⟩, exists_rootSelection_unitaryRankOne, Quot.mk _ exD, by
    rw [DPair.pol_eq_of_rel exD.rel_out]; exact exD_irreducible⟩

example : ((definitePairUnitaryOneTwo.c : ℚˣ) : ℚ) = 5 := rfl

example (G : HTGroup p) (L : G.Level) : ∀ k ∈ L.K.toSubgroup, ∀ g,
    Set.indicator (L.K.toSubgroup : Set G.GAf) (1 : G.GAf → ℂ) (k⁻¹ * g * k) =
      Set.indicator (L.K.toSubgroup : Set G.GAf) (1 : G.GAf → ℂ) g :=
  (isTest_indicator (MonoidHom.id _) L.K.toSubgroup (by simp)).2.2.1

end Example

end GlobalTheory.LKDef
