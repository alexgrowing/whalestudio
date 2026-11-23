import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm

noncomputable section

open WittVector Ideal Matrix

namespace GlobalTheory.Sandwich.Model

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem xi_eq (ε : PreTilt O p) : xi ε = ReciprocityTheory.PGsh.Ainf.xi p O ε := rfl

theorem nu_eq (ε : PreTilt O p) : nu ε = ReciprocityTheory.PGsh.Ainf.nu p O ε := rfl

def mixed (ε : PreTilt O p) (h : ℕ) (S : Finset (Fin h)) : Datum ε h (Fin h → ℤ_[p]) where
  F := diagonal fun i => if i ∈ S then mu ε else 1
  G := diagonal fun i => if i ∈ S then 1 else mu ε
  Ψ := diagonal fun i => if i ∈ S then xi ε else 1
  Ψ' := diagonal fun i => if i ∈ S then 1 else xi ε
  ρT := Matrix.diagonalAlgHom ℤ_[p]
  ρM := (RingHom.mapMatrix (ofPadic p O)).comp (Matrix.diagonalRingHom _ _)
  G_mul_F := by
    rw [diagonal_mul_diagonal, smul_one_eq_diagonal]
    refine congrArg diagonal (funext fun i => ?_); split_ifs <;> simp
  F_eq := by
    rw [diagonal_map (map_zero _), diagonal_mul_diagonal]
    refine congrArg diagonal (funext fun i => ?_)
    split_ifs <;> simp [phiInv_mu, xi_mul_nu]
  Ψ_mul := by
    rw [diagonal_mul_diagonal, smul_one_eq_diagonal]
    refine congrArg diagonal (funext fun i => ?_); split_ifs <;> simp
  F_act := by
    intro a
    simp [diagonal_map (map_zero _), diagonal_mul_diagonal, mul_comm]

theorem mixed_al (ε : PreTilt O p) (hμ : fontaineTheta O p (mu ε) = 0) (h : ℕ) (S : Finset (Fin h))
    (x : Fin h → O) (i : Fin h) : (mixed ε h S).al x i = if i ∈ S then 0 else x i := by
  simp only [Datum.al, mixed, diagonal_map (map_zero _), toLin'_apply, mulVec_diagonal]
  split_ifs <;> simp [hμ]

theorem mixed_bb (ε : PreTilt O p) (hμ : fontaineTheta O p (mu ε) = 0) (h : ℕ) (S : Finset (Fin h))
    (x : Fin h → O) (i : Fin h) : (mixed ε h S).bb x i = if i ∈ S then x i else 0 := by
  simp only [Datum.bb, mixed, diagonal_map (map_zero _), toLin'_apply, mulVec_diagonal]
  split_ifs <;> simp [hμ]

theorem mem_mixed_Fil (ε : PreTilt O p) (hμ : fontaineTheta O p (mu ε) = 0) (h : ℕ)
    (S : Finset (Fin h)) (x : Fin h → O) : x ∈ (mixed ε h S).Fil ↔ ∀ i ∈ S, x i = 0 := by
  rw [Datum.Fil, LinearMap.mem_ker, funext_iff]
  simp only [mixed_bb ε hμ]
  constructor
  · intro H i hi; simpa [hi] using H i
  · intro H i; split_ifs with hi
    · exact H i hi
    · rfl

theorem mem_mixed_Lie (ε : PreTilt O p) (hμ : fontaineTheta O p (mu ε) = 0) (h : ℕ)
    (S : Finset (Fin h)) (x : Fin h → O) : x ∈ (mixed ε h S).Lie ↔ ∀ i ∉ S, x i = 0 := by
  rw [Datum.Lie, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩ i hi; simp [mixed_bb ε hμ, hi]
  · intro H; refine ⟨x, funext fun i => ?_⟩
    rw [mixed_bb ε hμ]; split_ifs with hi
    · rfl
    · exact (H i hi).symm

theorem mem_mixed_Tsub (ε : PreTilt O p) (h : ℕ) (S : Finset (Fin h)) (i : Fin h) (x : Fin h → O) :
    x ∈ (mixed ε h S).Tsub ((padicToO p O).comp (Pi.evalRingHom _ i)) ↔ ∀ j ≠ i, x j = 0 := by
  simp only [Datum.Tsub, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, mixed,
    toLin'_apply, funext_iff]
  constructor
  · intro H j hj
    have := H (Pi.single j 1) j
    simpa [diagonal_map (map_zero _), mulVec_diagonal, Pi.single_apply, hj.symm] using this
  · intro H a j
    by_cases hj : j = i
    · subst hj; simp [diagonal_map (map_zero _), mulVec_diagonal]
    · simp [diagonal_map (map_zero _), mulVec_diagonal, H j hj]

section Field

variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  (hv : v.Integers O) {ε : PreTilt O p}
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε

theorem theta_mu : fontaineTheta O p (mu ε) = 0 := by
  rw [← xi_mul_nu, map_mul, xi_eq, ReciprocityTheory.PGsh.Ainf.theta_xi p O hv ε hε, zero_mul]

theorem mu_ne_zero : mu ε ≠ 0 := by
  intro h
  rw [← xi_mul_nu, mul_comm] at h
  have := ReciprocityTheory.PGsh.Ainf.xi_nzd p O hv ε hε _ h
  exact ReciprocityTheory.PGsh.Ainf.theta_nu p O hv ε hε (by rw [← nu_eq, this, map_zero])

omit hε [IsAlgClosed C] in
theorem isDomain_Ainf : IsDomain (Ainf p O) := by
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  infer_instance

variable {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (D : Datum ε h Λ)

theorem F_mul_G : D.F * D.G = mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) := by
  haveI := isDomain_Ainf (p := p) hv
  have hd : D.F.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det D.G_mul_F
    rw [det_mul, h0, mul_zero, det_smul, det_one, mul_one] at this
    exact pow_ne_zero _ (mu_ne_zero hv hε) this.symm
  have h1 : (D.F * D.G - mu ε • 1) * D.F = 0 := by
    rw [sub_mul, mul_assoc, D.G_mul_F]; simp
  have h2 := congrArg (· * D.F.adjugate) h1
  simp only [mul_assoc, mul_adjugate, zero_mul, Matrix.mul_smul, mul_one] at h2
  refine sub_eq_zero.1 (Matrix.ext fun i j => ?_)
  have h3 : D.F.det * (D.F * D.G - mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O))) i j = 0 :=
    congrFun (congrFun h2 i) j
  exact (mul_eq_zero.1 h3).resolve_left hd

theorem al_bb (x : Fin h → O) : D.al (D.bb x) = 0 := by
  simp only [Datum.al, Datum.bb, toLin'_apply, mulVec_mulVec, ← Matrix.map_mul, F_mul_G hv hε D]
  ext i; simp [mulVec, dotProduct, theta_mu hv hε]

theorem bb_al (x : Fin h → O) : D.bb (D.al x) = 0 := by
  simp only [Datum.al, Datum.bb, toLin'_apply, mulVec_mulVec, ← Matrix.map_mul, D.G_mul_F]
  ext i; simp [mulVec, dotProduct, theta_mu hv hε]

theorem lie_inf_tsub_le_W (τ : Λ →+* O) : D.Lie ⊓ D.Tsub τ ≤ D.W τ := by
  rintro x ⟨⟨y, rfl⟩, hx⟩
  exact ⟨hx, al_bb hv hε D y⟩

theorem map_al_le (τ : Λ →+* O) : (D.Tsub τ).map D.al ≤ D.Fil ⊓ D.Hsub τ := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨bb_al hv hε D x, ?_⟩
  simp only [Datum.Tsub, Datum.Hsub, SetLike.mem_coe, Submodule.mem_iInf,
    Module.End.mem_eigenspace_iff, toLin'_apply] at hx ⊢
  intro a
  have := congrArg (fun M => M.map (fontaineTheta O p)) (D.F_act a)
  simp only [Matrix.map_mul, Matrix.map_map] at this
  rw [Datum.al, toLin'_apply, mulVec_mulVec, ← this, ← mulVec_mulVec]
  change _ *ᵥ ((D.ρT a).map (padicToO p O) *ᵥ x) = _
  rw [hx a, mulVec_smul]

theorem bound_aux (X Y : Matrix (Fin h) (Fin h) (Ainf p O)) (hXY : X * Y = mu ε • 1)
    (x : Fin h → O) (hx : Y.map (fontaineTheta O p) *ᵥ x = 0) :
    ∃ y, X.map (fontaineTheta O p) *ᵥ y = fontaineTheta O p (nu ε) • x := by
  choose m hm using fun i => ReciprocityTheory.PGsh.Ainf.theta_surj p O hv (x i)
  have h1 : ∀ i, ∃ c, (Y *ᵥ m) i = xi ε * c := by
    intro i
    have : (Y *ᵥ m) i ∈ RingHom.ker (fontaineTheta O p) := by
      rw [RingHom.mem_ker, RingHom.map_mulVec]
      have : (fontaineTheta O p) ∘ m = x := funext hm
      rw [this, hx]; rfl
    rw [ReciprocityTheory.PGsh.Ainf.ker_theta p O hv ε hε, Ideal.mem_span_singleton] at this
    exact this
  choose c hc using h1
  have h2 : Y *ᵥ m = xi ε • c := funext hc
  have h3 : ∀ i, (X *ᵥ c) i = nu ε * m i := by
    intro i
    have h4 := congrFun (congrArg (X *ᵥ ·) h2) i
    simp only [mulVec_mulVec, hXY, mulVec_smul, smul_mulVec, one_mulVec, Pi.smul_apply,
      smul_eq_mul] at h4
    refine sub_eq_zero.1 (ReciprocityTheory.PGsh.Ainf.xi_nzd p O hv ε hε _ ?_)
    rw [← xi_eq, ← xi_mul_nu] at *
    linear_combination -h4
  refine ⟨fontaineTheta O p ∘ c, funext fun i => ?_⟩
  rw [← RingHom.map_mulVec, h3, map_mul, hm]; rfl

theorem smul_Fil_le (x : Fin h → O) (hx : x ∈ D.Fil) :
    fontaineTheta O p (nu ε) • x ∈ LinearMap.range D.al :=
  bound_aux hv hε D.F D.G (F_mul_G hv hε D) x hx

theorem smul_ker_le (x : Fin h → O) (hx : x ∈ LinearMap.ker D.al) :
    fontaineTheta O p (nu ε) • x ∈ D.Lie :=
  bound_aux hv hε D.G D.F D.G_mul_F x hx

end Field

theorem exists_mixed (p : ℕ) [Fact p.Prime] :
    ∃ (_ : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p])) (_ : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p])
      (ε : PreTilt 𝓞_ℂ_[p] p) (D : Datum ε 2 (Fin 2 → ℤ_[p])),
      IsPrimitiveRoot (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε).untilt) p ∧ mu ε ≠ 0 ∧
      D.Fil ≠ ⊥ ∧ D.Fil ≠ ⊤ ∧ D.Lie ≠ ⊥ ∧ D.Lie ≠ ⊤ := by
  obtain ⟨h1, h2, ε, hv, hε⟩ := GlobalTheory.PadicComplexHost.main p
  have hμ := theta_mu hv hε
  refine ⟨h1, h2, ε, mixed ε 2 {0}, hε, mu_ne_zero hv hε, ?_, ?_, ?_, ?_⟩
  · intro H
    have : (Pi.single 1 1 : Fin 2 → 𝓞_ℂ_[p]) ∈ (mixed ε 2 {0}).Fil := by
      rw [mem_mixed_Fil ε hμ]; simp
    rw [H, Submodule.mem_bot] at this
    simpa using congrFun this 1
  · intro H
    have : (Pi.single 0 1 : Fin 2 → 𝓞_ℂ_[p]) ∈ (mixed ε 2 {0}).Fil := by rw [H]; trivial
    rw [mem_mixed_Fil ε hμ] at this
    simpa using this 0
  · intro H
    have : (Pi.single 0 1 : Fin 2 → 𝓞_ℂ_[p]) ∈ (mixed ε 2 {0}).Lie := by
      rw [mem_mixed_Lie ε hμ]; intro i hi; simp at hi; simp [hi]
    rw [H, Submodule.mem_bot] at this
    simpa using congrFun this 0
  · intro H
    have : (Pi.single 1 1 : Fin 2 → 𝓞_ℂ_[p]) ∈ (mixed ε 2 {0}).Lie := by rw [H]; trivial
    rw [mem_mixed_Lie ε hμ] at this
    simpa using this 1

end GlobalTheory.Sandwich.Model
