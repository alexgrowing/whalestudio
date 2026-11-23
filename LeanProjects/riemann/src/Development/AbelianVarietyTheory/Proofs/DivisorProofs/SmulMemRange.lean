import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.CyclicRecursionStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrderStatement

open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix

namespace GlobalTheory.Sandwich.HodgeTateBound

section General

variable {A O : Type} [CommRing A] [CommRing O] {h : ℕ}

theorem right_cancel [IsDomain A] {F G : Matrix (Fin h) (Fin h) A} {μ : A} (hμ : μ ≠ 0)
    (hGF : G * F = μ • (1 : Matrix (Fin h) (Fin h) A)) {X Y : Matrix (Fin h) (Fin h) A}
    (hX : X * F = Y * F) : X = Y := by
  have hdet : F.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hGF
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hμ h1.symm
  have h2 : X * F * F.adjugate = Y * F * F.adjugate := by rw [hX]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.mul_one] at h2
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h3
  exact mul_left_cancel₀ hdet h3

theorem mul_swap [IsDomain A] {F G : Matrix (Fin h) (Fin h) A} {μ : A} (hμ : μ ≠ 0)
    (hGF : G * F = μ • (1 : Matrix (Fin h) (Fin h) A)) :
    F * G = μ • (1 : Matrix (Fin h) (Fin h) A) := by
  apply right_cancel hμ hGF
  rw [Matrix.mul_assoc, hGF]
  simp

theorem range_le_ker (θ : A →+* O) {F G : Matrix (Fin h) (Fin h) A} {μ : A} (hμ : θ μ = 0)
    (hGF : G * F = μ • (1 : Matrix (Fin h) (Fin h) A)) :
    LinearMap.range (Matrix.toLin' (F.map θ)) ≤ LinearMap.ker (Matrix.toLin' (G.map θ)) := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker, ← Matrix.toLin'_mul_apply, ← Matrix.map_mul, hGF]
  have : (μ • (1 : Matrix (Fin h) (Fin h) A)).map θ = 0 := by
    ext i j
    simp [hμ]
  rw [this]
  simp

theorem smul_mem_range [IsDomain A] (θ : A →+* O) (hs : Function.Surjective θ) {ξ ν μ : A}
    (hker : RingHom.ker θ = Ideal.span {ξ}) (hξ : ξ ≠ 0) (hμ : ξ * ν = μ)
    {F G : Matrix (Fin h) (Fin h) A} (hFG : F * G = μ • (1 : Matrix (Fin h) (Fin h) A))
    (f : Fin h → O) (hf : f ∈ LinearMap.ker (Matrix.toLin' (G.map θ))) :
    θ ν • f ∈ LinearMap.range (Matrix.toLin' (F.map θ)) := by
  choose m hm using fun i => hs (f i)
  have hf' : f = θ ∘ m := by
    funext i
    exact (hm i).symm
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, hf'] at hf
  have h1 : ∀ i, ∃ x, x * ξ = (G *ᵥ m) i := by
    intro i
    rw [← Ideal.mem_span_singleton', ← hker, RingHom.mem_ker, RingHom.map_mulVec, hf]
    rfl
  choose x hx using h1
  have h2 : G *ᵥ m = ξ • x := by
    funext i
    rw [← hx i, Pi.smul_apply, smul_eq_mul, mul_comm]
  have h3 : F *ᵥ (G *ᵥ m) = μ • m := by
    rw [Matrix.mulVec_mulVec, hFG, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [h2, Matrix.mulVec_smul, ← hμ] at h3
  refine ⟨θ ∘ x, ?_⟩
  funext i
  have h4 := congrFun h3 i
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc] at h4
  have h5 := mul_left_cancel₀ hξ h4
  rw [Matrix.toLin'_apply, ← RingHom.map_mulVec, h5, map_mul, hm]
  rfl

end General

open Matrix in
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] in
private lemma mul_eq_smul_one_of_mul_eq_smul_one [IsDomain R] {A B : Matrix n n R} {c : R}
    (hc : c ≠ 0) (hBA : B * A = c • (1 : Matrix n n R)) : A * B = c • (1 : Matrix n n R) := by
  have hdet : A.det ≠ 0 := by
    intro h0
    have hprod : B.det * A.det = c ^ Fintype.card n := by
      rw [← det_mul, hBA, det_smul, det_one, mul_one]
    rw [h0, mul_zero] at hprod
    exact pow_ne_zero _ hc hprod.symm
  have key : A.det • (A * B) = A.det • (c • (1 : Matrix n n R)) := by
    calc A.det • (A * B) = (A * B) * (A * adjugate A) := by
          rw [mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
      _ = A * (B * A) * adjugate A := by simp only [Matrix.mul_assoc]
      _ = A.det • (c • (1 : Matrix n n R)) := by
          rw [hBA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, mul_adjugate, smul_smul,
            smul_smul, mul_comm]
  ext i j
  have hij := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at hij
  exact mul_left_cancel₀ hdet hij

open Matrix in
variable {A O : Type*} [CommRing A] [CommRing O] {h : ℕ} in
private lemma smul_mem_range_of_mem_ker_of_mul_eq (θ : A →+* O) (hθ : Function.Surjective θ)
    {ξ ν : A} (hker : RingHom.ker θ = Ideal.span {ξ}) (hξ : ∀ y : A, y * ξ = 0 → y = 0)
    {P Q : Matrix (Fin h) (Fin h) A} (hQP : Q * P = (ξ * ν) • (1 : Matrix (Fin h) (Fin h) A))
    (t : Fin h → O) (ht : t ∈ LinearMap.ker (toLin' (P.map θ))) :
    θ ν • t ∈ LinearMap.range (toLin' (Q.map θ)) := by
  choose s hs using fun i => hθ (t i)
  have hst : (θ ∘ s) = t := funext hs
  rw [LinearMap.mem_ker, toLin'_apply] at ht
  have hmem : ∀ i, (P *ᵥ s) i ∈ Ideal.span {ξ} := by
    intro i
    rw [← hker, RingHom.mem_ker, RingHom.map_mulVec, hst]
    exact congrFun ht i
  choose g hg using fun i => Ideal.mem_span_singleton'.mp (hmem i)
  have hQg : Q *ᵥ g = ν • s := by
    funext i
    apply sub_eq_zero.mp
    apply hξ
    have h1 : Q *ᵥ (P *ᵥ s) = (ξ * ν) • s := by
      rw [mulVec_mulVec, hQP, Matrix.smul_mulVec, one_mulVec]
    have h2 : P *ᵥ s = fun j => g j * ξ := funext fun j => (hg j).symm
    have h3 := congrFun h1 i
    rw [h2] at h3
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h3 ⊢
    have h4 : ∑ j, Q i j * (g j * ξ) = (∑ j, Q i j * g j) * ξ := by
      rw [Finset.sum_mul]
      simp only [mul_assoc]
    rw [h4] at h3
    linear_combination h3
  refine ⟨θ ∘ g, ?_⟩
  rw [toLin'_apply]
  funext i
  rw [← RingHom.map_mulVec, hQg]
  simp [← hs]

open Matrix in
variable {O : Type*} [CommRing O] {h : ℕ} in
private lemma map_iInf_eigenspace_le_of_intertwine {ι : Type*} {X Y : ι → Matrix (Fin h) (Fin h) O}
    {Z : Matrix (Fin h) (Fin h) O} (c : ι → O) (hZ : ∀ a, Y a * Z = Z * X a) :
    (⨅ a, Module.End.eigenspace (toLin' (X a)) (c a)).map (toLin' Z) ≤
      ⨅ a, Module.End.eigenspace (toLin' (Y a)) (c a) := by
  rintro _ ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf] at hx
  rw [Submodule.mem_iInf]
  intro a
  have hxa := hx a
  rw [Module.End.mem_eigenspace_iff, toLin'_apply] at hxa ⊢
  rw [toLin'_apply, mulVec_mulVec, hZ, ← mulVec_mulVec, hxa, mulVec_smul]

open Matrix in

theorem _root_.GlobalTheory.Sandwich.HodgeTateBound.bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ ε : PreTilt O p, IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p →
    ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ], ∀ (h : ℕ) (D : _root_.GlobalTheory.Sandwich.Datum ε h Λ),
    D.F * D.G =
        _root_.GlobalTheory.Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O)) ∧
      LinearMap.range D.al ≤ D.Fil ∧
      D.Lie ≤ LinearMap.ker D.al ∧
      (∀ f ∈ D.Fil, WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.nu ε) • f ∈
        LinearMap.range D.al) ∧
      (∀ t ∈ LinearMap.ker D.al,
        WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.nu ε) • t ∈ D.Lie) ∧
      (∀ τ : Λ →+* O, (D.Tsub τ).map D.al ≤
          D.Fil ⊓ D.Hsub τ ∧
        (D.Hsub τ).map D.bb ≤
          D.Lie ⊓ D.Tsub τ ∧
        D.Lie ⊓ D.Tsub τ ≤
          D.W τ) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ h D
  haveI : IsDomain (_root_.GlobalTheory.Sandwich.Ainf p O) := _root_.GlobalTheory.AinfXi.isDomain_ainf hv
  have hker := _root_.GlobalTheory.AinfXi.ker_theta hv ε hε
  have hξ := _root_.GlobalTheory.AinfXi.xi_nzd hv ε hε
  have hsurj : Function.Surjective (WittVector.fontaineTheta O p) := _root_.ReciprocityTheory.PGsh.Ainf.theta_surj p O hv
  have hμ := _root_.GlobalTheory.Sandwich.xi_mul_nu ε
  have hθξ : WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.xi ε) = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact Ideal.mem_span_singleton_self _
  have hθμ : WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.mu ε) = 0 := by
    rw [← hμ, map_mul, hθξ, zero_mul]
  have hξ0 : _root_.GlobalTheory.Sandwich.xi ε ≠ 0 := by
    intro h0
    exact one_ne_zero (hξ 1 (by rw [h0, mul_zero]))
  have hν0 : _root_.GlobalTheory.Sandwich.nu ε ≠ 0 := by
    intro h0
    have h1 : WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.nu ε) =
        PreTilt.untilt (_root_.GlobalTheory.Sandwich.root ε) - 1 := by
      simp [_root_.GlobalTheory.Sandwich.nu, WittVector.fontaineTheta_teichmuller]
    rw [h0, map_zero] at h1
    exact hε.ne_one (Fact.out : p.Prime).one_lt (sub_eq_zero.mp h1.symm)
  have hμ0 : _root_.GlobalTheory.Sandwich.mu ε ≠ 0 := by
    rw [← hμ]
    exact mul_ne_zero hξ0 hν0
  have hGF := D.G_mul_F
  have hFG := mul_eq_smul_one_of_mul_eq_smul_one hμ0 hGF
  have hA : D.G.map (WittVector.fontaineTheta O p) *
      D.F.map (WittVector.fontaineTheta O p) = 0 := by
    rw [← Matrix.map_mul, hGF]
    ext i j
    simp [hθμ]
  have hB : D.F.map (WittVector.fontaineTheta O p) *
      D.G.map (WittVector.fontaineTheta O p) = 0 := by
    rw [← Matrix.map_mul, hFG]
    ext i j
    simp [hθμ]
  have hpad : ∀ M : Matrix (Fin h) (Fin h) ℤ_[p],
      (M.map (_root_.GlobalTheory.Sandwich.ofPadic p O)).map (WittVector.fontaineTheta O p) = M.map (_root_.GlobalTheory.Sandwich.padicToO p O) := by
    intro M
    ext i j
    simp [_root_.GlobalTheory.Sandwich.padicToO]
  have hact := D.F_act
  have hGact : ∀ a, (D.ρT a).map (_root_.GlobalTheory.Sandwich.ofPadic p O) * D.G =
      D.G * D.ρM a := by
    intro a
    have e : _root_.GlobalTheory.Sandwich.mu ε •
        ((D.ρT a).map (_root_.GlobalTheory.Sandwich.ofPadic p O) * D.G) =
        _root_.GlobalTheory.Sandwich.mu ε • (D.G * D.ρM a) := by
      calc _ = D.G * D.F *
              (D.ρT a).map (_root_.GlobalTheory.Sandwich.ofPadic p O) * D.G := by
            rw [hGF, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
        _ = D.G * (D.F *
              (D.ρT a).map (_root_.GlobalTheory.Sandwich.ofPadic p O)) * D.G := by
            simp only [Matrix.mul_assoc]
        _ = D.G * (D.ρM a * D.F) *
              D.G := by rw [hact a]
        _ = D.G * D.ρM a *
              (D.F * D.G) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hFG, Matrix.mul_smul, Matrix.mul_one]
    refine Matrix.ext fun i j => ?_
    have hij := congrFun (congrFun e i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hij
    exact mul_left_cancel₀ hμ0 hij
  simp only [_root_.GlobalTheory.Sandwich.Datum.al, _root_.GlobalTheory.Sandwich.Datum.bb,
    _root_.GlobalTheory.Sandwich.Datum.Fil, _root_.GlobalTheory.Sandwich.Datum.Lie,
    _root_.GlobalTheory.Sandwich.Datum.Tsub, _root_.GlobalTheory.Sandwich.Datum.Hsub,
    _root_.GlobalTheory.Sandwich.Datum.W]
  have hrange : LinearMap.range (toLin' (D.F.map (WittVector.fontaineTheta O p))) ≤
      LinearMap.ker (toLin' (D.G.map (WittVector.fontaineTheta O p))) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, toLin'_apply, toLin'_apply, mulVec_mulVec, hA, zero_mulVec]
  have hlie : LinearMap.range (toLin' (D.G.map (WittVector.fontaineTheta O p))) ≤
      LinearMap.ker (toLin' (D.F.map (WittVector.fontaineTheta O p))) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, toLin'_apply, toLin'_apply, mulVec_mulVec, hB, zero_mulVec]
  refine ⟨hFG, hrange, hlie, ?_, ?_, ?_⟩
  · exact smul_mem_range_of_mem_ker_of_mul_eq _ hsurj hker hξ (by rw [hFG, hμ])
  · exact smul_mem_range_of_mem_ker_of_mul_eq _ hsurj hker hξ (by rw [hGF, hμ])
  · intro τ
    refine ⟨le_inf (LinearMap.map_le_range.trans hrange) ?_,
      le_inf LinearMap.map_le_range ?_, fun x hx => ⟨hx.2, hlie hx.1⟩⟩
    · refine map_iInf_eigenspace_le_of_intertwine τ fun a => ?_
      rw [← Matrix.map_mul, ← hact a, Matrix.map_mul, hpad]
    · refine map_iInf_eigenspace_le_of_intertwine τ fun a => ?_
      rw [← hpad, ← Matrix.map_mul, hGact a, Matrix.map_mul]

end GlobalTheory.Sandwich.HodgeTateBound
