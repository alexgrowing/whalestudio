import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningAffinePreimageStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechCoverCompatible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechRestrictionCommutesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningTwistedSectionTransition
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem exists_form_of_eval {ι R B G : Type} [CommRing R] [CommRing B] [AddCommGroup G]
    [Module (MvPolynomial ι R) G] (φ : R →+* B) (r : ι → B) (μ : B →+ G) (i : ι)
    (hC : ∀ (a : R) (c : B), μ (φ a * c) = (MvPolynomial.C a : MvPolynomial ι R) • μ c)
    (hr : ∀ (j : ι) (c : B), (MvPolynomial.X i : MvPolynomial ι R) • μ (r j * c) =
      (MvPolynomial.X j : MvPolynomial ι R) • μ c) (P : MvPolynomial ι R) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ Q : MvPolynomial ι R, Q.IsHomogeneous n ∧
      (MvPolynomial.X i : MvPolynomial ι R) ^ n • μ (MvPolynomial.eval₂Hom φ r P) = Q • μ 1 := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, fun n _ => ⟨MvPolynomial.X i ^ n * MvPolynomial.C a, ?_, ?_⟩⟩
    · simpa using (MvPolynomial.isHomogeneous_X_pow (R := R) i n).mul
        (MvPolynomial.isHomogeneous_C (σ := ι) a)
    · have h := hC a 1
      rw [mul_one] at h
      rw [MvPolynomial.eval₂Hom_C, h, mul_smul]
  | add p q hp hq =>
    obtain ⟨n₁, h₁⟩ := hp
    obtain ⟨n₂, h₂⟩ := hq
    refine ⟨max n₁ n₂, fun n hn => ?_⟩
    obtain ⟨Q₁, a₁, b₁⟩ := h₁ n (le_trans (le_max_left _ _) hn)
    obtain ⟨Q₂, a₂, b₂⟩ := h₂ n (le_trans (le_max_right _ _) hn)
    refine ⟨Q₁ + Q₂, a₁.add a₂, ?_⟩
    rw [map_add, map_add, smul_add, b₁, b₂, add_smul]
  | mul_X p j hp =>
    obtain ⟨n₀, h⟩ := hp
    refine ⟨n₀ + 1, fun n hn => ?_⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨Q, a, b⟩ := h n' (by omega)
    refine ⟨MvPolynomial.X j * Q, ?_, ?_⟩
    · simpa [add_comm] using (MvPolynomial.isHomogeneous_X R j).mul a
    · rw [map_mul, MvPolynomial.eval₂Hom_X', mul_comm (MvPolynomial.eval₂Hom φ r p), pow_succ, mul_smul,
        hr, smul_smul, mul_comm _ (MvPolynomial.X j), mul_smul, b, smul_smul]

section Shift

variable {ι R : Type} [CommRing R] {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
  {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)

theorem exists_pow_smul_of_eq_zero (i : ι) (k : ℕ) : ∀ (t : ℤ) (a : A t), t + k = 0 →
    ∃ b : A 0, (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of hx t a = GrSum.of hx 0 b := by
  induction k with
  | zero =>
    intro t a h
    obtain rfl : t = 0 := by simpa using h
    exact ⟨a, by simp⟩
  | succ k ih =>
    intro t a h
    obtain ⟨b, hb⟩ := ih (t + 1) (x i t a) (by push_cast at h; omega)
    exact ⟨b, by rw [pow_succ, mul_smul, GrSum.X_smul_of, hb]⟩

theorem exists_of_eq_pow_smul (i : ι) (hb : ∀ t, Function.Surjective (x i t)) (k : ℕ) :
    ∀ (t : ℤ) (a : A t), t = k →
    ∃ b : A 0, GrSum.of hx t a = (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of hx 0 b := by
  induction k with
  | zero =>
    intro t a h
    obtain rfl : t = 0 := by simpa using h
    exact ⟨a, by simp⟩
  | succ k ih =>
    intro t a h
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by ring⟩
    obtain ⟨a', rfl⟩ := hb t' a
    obtain ⟨b, hb'⟩ := ih t' a' (by push_cast at h; omega)
    exact ⟨b, by rw [← GrSum.X_smul_of, hb', pow_succ', mul_smul]⟩

theorem exists_shift_zero (i : ι) (hb : ∀ t, Function.Surjective (x i t)) (t : ℤ) (a : A t) :
    ∃ (k l : ℕ) (b : A 0), (k : ℤ) + t = l ∧
      (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of hx t a =
        (MvPolynomial.X i : MvPolynomial ι R) ^ l • GrSum.of hx 0 b := by
  rcases le_total t 0 with h | h
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, t + k = 0 := ⟨(-t).toNat, by omega⟩
    obtain ⟨b, hb'⟩ := exists_pow_smul_of_eq_zero hx i k t a hk
    exact ⟨k, 0, b, by push_cast; omega, by simpa using hb'⟩
  · obtain ⟨l, hl⟩ : ∃ l : ℕ, t = l := ⟨t.toNat, by omega⟩
    obtain ⟨b, hb'⟩ := exists_of_eq_pow_smul hx i hb l t a hl
    exact ⟨0, l, b, by simp [hl], by simpa using hb'⟩

end Shift

theorem exists_smul_oneOn {X : Scheme.{0}} {N : LB X} (hN : N.IsLB) {a : ℤ} (h : a = 0) (V : X.Opens)
    (x : SecOn (pw N a) V) : ∃ c : Γ(X, V), c • oneOn N h V = x := by
  subst h
  obtain ⟨c, hc⟩ := GlobalTheory.LB.exists_fun_of_cover (fun k => V ⊓ N.U k) (fun k => inf_le_left)
    (GlobalTheory.LB.le_iSup_inf hN.cover V) (fun k => GlobalTheory.LB.coord x k) (fun k l => by
      have := GlobalTheory.LB.coord_rel x k l (W := (V ⊓ N.U k) ⊓ (V ⊓ N.U l)) inf_le_left inf_le_right
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
      rw [show (AbLaw.pw N 0).g k l = N.g k l ^ (0 : ℤ) from rfl, zpow_zero, Units.val_one] at this
      erw [map_one, one_mul] at this
      exact this)
  refine ⟨c, GlobalTheory.LB.sec_ext fun k => ?_⟩
  rw [GlobalTheory.LB.coord_smul]
  erw [hc k]
  exact mul_one _

section Chart

variable {X : Scheme.{0}} {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {N : LB X}
  (d : ℤ) {V : X.Opens} {ι : Type}

theorem exists_form_chart (hN : N.IsLB) (σ : ι → SecOn (pw N d) V)
    (hx : OperatorsCommute (ι := ι) (R := R) (A := fun t => SecOnR f (pw N (d * t)) V)
      fun j t => mulRight f (by ring) (σ j)) (i : ι)
    (hb : ∀ t : ℤ, Function.Surjective
      (mulRight (a := d * t) (c := d * (t + 1)) f (by ring) (σ i)))
    (r : ι → Γ(X, V))
    (hr : ∀ j (k : (pw N d).ι), GlobalTheory.LB.coord (σ j) k =
      rs X (inf_le_left : V ⊓ (pw N d).U k ≤ V) (r j) * GlobalTheory.LB.coord (σ i) k)
    (hs : Function.Surjective (MvPolynomial.eval₂Hom (cst f V) r)) (t : ℤ)
    (a : SecOnR f (pw N (d * t)) V) :
    ∃ (k n : ℕ) (Q : MvPolynomial ι R), Q.IsHomogeneous n ∧ (k : ℤ) + t = n ∧
      (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of hx t a =
        Q • GrSum.of hx 0 (SecOnR.of f _ V (oneOn N (mul_zero d) V)) := by
  set one : SecOnR f (pw N (d * 0)) V := SecOnR.of f _ V (oneOn N (mul_zero d) V) with hone
  let μ : Γ(X, V) →+ GrSum hx := AddMonoidHom.mk' (fun c => GrSum.of hx 0 (c • one))
    (fun a b => by rw [add_smul, map_add])
  have hμ : ∀ c, μ c = GrSum.of hx 0 (c • one) := fun _ => rfl
  have hC : ∀ (a : R) (c : Γ(X, V)), μ (cst f V a * c) =
      (MvPolynomial.C a : MvPolynomial ι R) • μ c := by
    intro a c
    rw [← MvPolynomial.algebraMap_eq, algebraMap_smul, hμ, hμ, mul_smul, ← SecOnR.smul_def, map_smul]
  have hr' : ∀ (j : ι) (c : Γ(X, V)), (MvPolynomial.X i : MvPolynomial ι R) • μ (r j * c) =
      (MvPolynomial.X j : MvPolynomial ι R) • μ c := by
    intro j c
    rw [hμ, hμ, GrSum.X_smul_of, GrSum.X_smul_of]
    congr 1
    refine SecOnR.ext fun (k : N.ι) => ?_
    let cd : ι → Γ(X, V ⊓ N.U k) := fun l => GlobalTheory.LB.coord (σ l) k
    change (rs X (inf_le_left : V ⊓ N.U k ≤ V) (r j * c) * (1 : Γ(X, V ⊓ N.U k))) * cd i =
      (rs X (inf_le_left : V ⊓ N.U k ≤ V) c * (1 : Γ(X, V ⊓ N.U k))) * cd j
    have hk : cd j = rs X (inf_le_left : V ⊓ N.U k ≤ V) (r j) * cd i := hr j k
    rw [hk, map_mul]
    ring
  obtain ⟨k, l, b, hkl, hab⟩ := exists_shift_zero hx i hb t a
  obtain ⟨c, hc⟩ := exists_smul_oneOn hN (mul_zero d) V ((SecOnR.of f _ V).symm b)
  obtain ⟨P, rfl⟩ := hs c
  obtain ⟨n₀, h⟩ := exists_form_of_eval (cst f V) r μ i hC hr' P
  obtain ⟨Q, hQ, hQe⟩ := h n₀ le_rfl
  have hb' : GrSum.of hx 0 b = μ (MvPolynomial.eval₂Hom (cst f V) r P) := by
    rw [hμ]; congr 1; exact hc.symm
  have h1 : μ 1 = GrSum.of hx 0 one := by rw [hμ, one_smul]
  refine ⟨n₀ + k, l + n₀, MvPolynomial.X i ^ l * Q, ?_, ?_, ?_⟩
  · exact (MvPolynomial.isHomogeneous_X_pow (R := R) i l).mul hQ
  · push_cast; omega
  · rw [pow_add, mul_smul, hab, hb', smul_comm, hQe, h1, mul_smul]

end Chart

section Step

variable (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
  (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
  (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e)))
  (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℤ) {ι : Type}
  (D : ∀ e, Finset ι → (Y e).left.Opens) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S)
  (S : Finset ι) (hDa : ∀ e, IsAffineOpen (D e S))
  (sh : ∀ e (_ : ι), SecOn (pw (N e) d) (D e S))
  (hshp : ∀ e j, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) d e S (SecOnR.of _ _ _ (sh (e + 1) j)) =
    SecOnR.of _ _ _ (sh e j))
  (hc : ∀ e, OperatorsCommute (ι := ι) (R := R) (A := fun t => Tm I Y N D d e t S)
    fun j t => mulT I Y N D d e t S (sh e j))

include hshp hDa in

theorem form_step (i : ι) (e : ℕ)
    (ih : ∀ (t : ℤ) (a : Tm I Y N D d e t S), ∃ (k n : ℕ) (Q : MvPolynomial ι R)
      (w : Tm I Y N D d e (n : ℤ) S), Q.IsHomogeneous n ∧ (k : ℤ) + t = n ∧
      w ∈ I • (⊤ : Submodule R (Tm I Y N D d e (n : ℤ) S)) ∧
      (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of (hc e) t a =
        Q • GrSum.of (hc e) 0 (oneT I Y N D d e S) + GrSum.of (hc e) (n : ℤ) w)
    (t : ℤ) (a : Tm I Y N D d (e + 1) t S) :
    ∃ (k n : ℕ) (Q : MvPolynomial ι R) (w : Tm I Y N D d (e + 1) (n : ℤ) S),
      Q.IsHomogeneous n ∧ (k : ℤ) + t = n ∧
      w ∈ I • (⊤ : Submodule R (Tm I Y N D d (e + 1) (n : ℤ) S)) ∧
      (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of (hc (e + 1)) t a =
        Q • GrSum.of (hc (e + 1)) 0 (oneT I Y N D d (e + 1) S) +
          GrSum.of (hc (e + 1)) (n : ℤ) w := by
  let ρ : ∀ n : ℤ, Tm I Y N D d (e + 1) n S →ₗ[R] Tm I Y N D d e n S := fun n =>
    red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d * n) e S
  have hred : ∀ n : ℤ, Function.Surjective (ρ n) ∧
      LinearMap.ker (ρ n) = I ^ (e + 1) • ⊤ := fun n =>
    GlobalTheory.T.thickening_affine_preimage R I Y β hβ (fun e => pw (N e) (d * n)) (fun e => pullPow (v e) (d * n))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S) (D e S)
      (hDβ e S) (hDa (e + 1))
  have hφ : ∀ (j : ι) (n : ℤ) (x : Tm I Y N D d (e + 1) n S),
      ρ (n + 1) (mulT I Y N D d (e + 1) n S (sh (e + 1) j) x) =
        mulT I Y N D d e n S (sh e j) (ρ n x) := by
    intro j n x
    have := red_secMulOn R I Y β hβ N v hN ι D (fun e S => (hDβ e S).ge) (d * n) d (d * (n + 1))
      (by ring) e S ((SecOnR.of _ _ _).symm x) (sh (e + 1) j)
    rw [hshp e j] at this
    exact this
  have hone : ρ 0 (oneT I Y N D d (e + 1) S) = oneT I Y N D d e S :=
    GlobalTheory.T.thickening_cech_restriction_commutes R I Y β hβ N v hN ι D (fun e S => (hDβ e S).ge) (d * 0) (mul_zero d) e S
  obtain ⟨k, n, Q, w, hQ, hk, hw, he⟩ := ih t (ρ t a)
  obtain ⟨w', hw', rfl⟩ : ∃ w' ∈ I • (⊤ : Submodule R (Tm I Y N D d (e + 1) (n : ℤ) S)),
      ρ n w' = w := by
    have : (I • (⊤ : Submodule R (Tm I Y N D d (e + 1) (n : ℤ) S))).map (ρ n) = I • ⊤ := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 (hred n).1]
    rw [← this] at hw
    exact hw
  let G := GrSum.map (hc (e + 1)) (hc e) ρ hφ
  have h1 : (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of (hc (e + 1)) t a ∈
      GrSum.grading (hc (e + 1)) (n : ℤ) := by
    have := grSMul_mem (GrSum.grading (hc (e + 1)))
      (mem_polyGrading_natCast.2 (MvPolynomial.isHomogeneous_X_pow (R := R) i k))
      (GrSum.of_mem_grading (hc (e + 1)) t a)
    rwa [show t + (k : ℤ) = n by omega] at this
  have h2 : Q • GrSum.of (hc (e + 1)) 0 (oneT I Y N D d (e + 1) S) ∈
      GrSum.grading (hc (e + 1)) (n : ℤ) := by
    have := grSMul_mem (GrSum.grading (hc (e + 1))) (mem_polyGrading_natCast.2 hQ)
      (GrSum.of_mem_grading (hc (e + 1)) 0 (oneT I Y N D d (e + 1) S))
    rwa [zero_add] at this
  obtain ⟨z, hz⟩ := sub_mem (sub_mem h1 h2) (GrSum.of_mem_grading (hc (e + 1)) (n : ℤ) w')
  have hGz : GrSum.of (hc e) (n : ℤ) (ρ n z) = 0 := by
    have := congrArg G hz
    rw [show G (GrSum.of (hc (e + 1)) (n : ℤ) z) = GrSum.of (hc e) (n : ℤ) (ρ n z) from
      GrSum.map_of _ _ _ _ _ _] at this
    rw [this, map_sub, map_sub, map_smul, map_smul]
    rw [show G (GrSum.of (hc (e + 1)) t a) = GrSum.of (hc e) t (ρ t a) from
        GrSum.map_of _ _ _ _ _ _,
      show G (GrSum.of (hc (e + 1)) 0 (oneT I Y N D d (e + 1) S)) =
        GrSum.of (hc e) 0 (ρ 0 (oneT I Y N D d (e + 1) S)) from GrSum.map_of _ _ _ _ _ _,
      show G (GrSum.of (hc (e + 1)) (n : ℤ) w') = GrSum.of (hc e) (n : ℤ) (ρ n w') from
        GrSum.map_of _ _ _ _ _ _, hone, he]
    abel
  have hz0 : ρ n z = 0 :=
    GrSum.of_injective (hc e) (n : ℤ) (hGz.trans (map_zero _).symm)
  have hzI : z ∈ I • (⊤ : Submodule R (Tm I Y N D d (e + 1) (n : ℤ) S)) := by
    have h3 : z ∈ LinearMap.ker (ρ n) := hz0
    rw [(hred n).2] at h3
    exact Submodule.smul_mono_left (Ideal.pow_le_self (by omega)) h3
  refine ⟨k, n, Q, w' + z, hQ, hk, add_mem hw' hzI, ?_⟩
  rw [map_add, hz]
  abel

end Step

theorem cst_comp_specMap {X : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
    (p : X ⟶ Spec (CommRingCat.of R')) (g : R →+* R') (U : X.Opens) :
    AbLaw.cst (p ≫ Spec.map (CommRingCat.ofHom g)) U = (AbLaw.cst p U).comp g := by
  ext a
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [this]

theorem exists_form_add_ideal_smul : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S)) (hsh0 : ∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) (hshp : ∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) (hshu : ∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) (hc : ∀ e S, OperatorsCommute (ι := Fin (m + 1)) (R := R) (A := fun t => Tm I Y N D (d : ℤ) e t S) fun j t => mulT I Y N D (d : ℤ) e t S (sh e j S)) (e : ℕ) (i : Fin (m + 1)) (t : ℤ) (a : Tm I Y N D (d : ℤ) e t {i}), ∃ (k : ℕ) (q : MvPolynomial (Fin (m + 1)) R) (t' : ℤ) (w : Tm I Y N D (d : ℤ) e t' {i}), w ∈ I • (⊤ : Submodule R (Tm I Y N D (d : ℤ) e t' {i})) ∧ (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) R) ^ k • GrSum.of (hc e {i}) t a = q • GrSum.of (hc e {i}) 0 (oneT I Y N D (d : ℤ) e {i}) + GrSum.of (hc e {i}) t' w := by
  intro R _ I Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa sh hsh0 hshp hshu hc e i t a
  have hi : ({i} : Finset (Fin (m + 1))).Nonempty := Finset.singleton_nonempty i
  have key : ∀ (e : ℕ) (t : ℤ) (a : Tm I Y N D (d : ℤ) e t {i}), ∃ (k n : ℕ)
      (Q : MvPolynomial (Fin (m + 1)) R) (w : Tm I Y N D (d : ℤ) e (n : ℤ) {i}),
      Q.IsHomogeneous n ∧ (k : ℤ) + t = n ∧
      w ∈ I • (⊤ : Submodule R (Tm I Y N D (d : ℤ) e (n : ℤ) {i})) ∧
      (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) R) ^ k • GrSum.of (hc e {i}) t a =
        Q • GrSum.of (hc e {i}) 0 (oneT I Y N D (d : ℤ) e {i}) +
          GrSum.of (hc e {i}) (n : ℤ) w := by
    intro e
    induction e with
    | zero =>
      intro t a
      obtain ⟨haff, r, hr, hsurj⟩ := hs.2 i
      have hV : D 0 {i} = nonzeroLocus (s i) := by rw [hD0]; simp
      have hbij : ∀ t : ℤ, Function.Surjective (mulRight (a := (d : ℤ) * t)
          (c := (d : ℤ) * (t + 1)) (toR I Y 0) (by ring) (sh 0 i {i})) := fun t => by
        obtain ⟨y, hy⟩ := hshu 0 i {i} (Finset.mem_singleton_self i)
        exact (mulT_bijective_of_inverse R I Y β hβ N v hN (d : ℤ) (Fin (m + 1)) D 0 t {i} (sh 0 i {i}) y hy).2
      let r' : Fin (m + 1) → Γ((Y 0).left, D 0 {i}) := fun j => rs _ hV.le (r j)
      have hr' : ∀ j (k : (pw (N 0) (d : ℤ)).ι), GlobalTheory.LB.coord (sh 0 j {i}) k =
          rs _ (inf_le_left : D 0 {i} ⊓ (pw (N 0) (d : ℤ)).U k ≤ D 0 {i}) (r' j) *
            GlobalTheory.LB.coord (sh 0 i {i}) k := by
        intro j k
        have := congrArg (rs _ (inf_le_inf_right _ hV.le :
          D 0 {i} ⊓ (pw (N 0) (d : ℤ)).U k ≤ nonzeroLocus (s i) ⊓ (pw (N 0) (d : ℤ)).U k)) (hr j k)
        rw [map_mul, rs_rs, rs_rs, rs_rs] at this
        rw [hsh0 j _ hi, hsh0 i _ hi, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec]
        simp only [r', rs_rs]
        exact this
      have hcomp : MvPolynomial.eval₂Hom (cst (toR I Y 0) (D 0 {i})) r' =
          ((rs _ hV.le).comp (MvPolynomial.eval₂Hom (cst (Y 0).hom (nonzeroLocus (s i))) r)).comp
            (MvPolynomial.map (Ideal.Quotient.mk (I ^ (0 + 1)))) := by
        apply MvPolynomial.ringHom_ext
        · intro x
          have h1 := RingHom.congr_fun (cst_comp_specMap (Y 0).hom
            (Ideal.Quotient.mk (I ^ (0 + 1))) (D 0 {i})) x
          simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C, rs_cst]
          exact h1
        · intro j
          simp [r']
      have hs' : Function.Surjective (MvPolynomial.eval₂Hom (cst (toR I Y 0) (D 0 {i})) r') := by
        intro c
        obtain ⟨P₀, hP₀⟩ := hsurj (rs _ hV.ge c)
        obtain ⟨P, rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective P₀
        refine ⟨P, ?_⟩
        rw [hcomp, RingHom.comp_apply, RingHom.comp_apply, hP₀, rs_rs, rs_self]
      obtain ⟨k, n, Q, hQ, hk, he⟩ := exists_form_chart (toR I Y 0) (d : ℤ) (hN 0).1
        (fun j => sh 0 j {i}) (hc 0 {i}) i hbij r' hr' hs' t a
      refine ⟨k, n, Q, 0, hQ, hk, zero_mem _, ?_⟩
      rw [map_zero, add_zero]
      exact he
    | succ e ih =>
      exact form_step R I Y β hβ N v hN (d : ℤ) D hDβ {i} (fun e => hDa e {i} hi)
        (fun e j => sh e j {i}) (fun e j => hshp e j {i} hi) (fun e => hc e {i}) i e ih
  obtain ⟨k, n, Q, w, -, -, hw, he⟩ := key e t a
  exact ⟨k, Q, n, w, hw, he⟩

end GlobalTheory.CompanionTheory.FormalAlg.Lift
