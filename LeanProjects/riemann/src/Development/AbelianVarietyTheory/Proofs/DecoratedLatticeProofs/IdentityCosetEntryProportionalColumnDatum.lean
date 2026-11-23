import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Formalism.LocalToGlobal.Columns.ColumnsProofs.ChainCounts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralEqFiniteSumOverNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelTestFunctionsAgreeRationalPointsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizerStatement

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.EntryBridge

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem om_one_one {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (Φ : Matrix b a k → ℂ) : om μ (1 : GL a k) (1 : GL b k) Φ = Φ := by
  have h1 : nabs k (1 : kˣ) = 1 := by simp [nabs]
  funext x; simp [om, h1]

variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

abbrev crd {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k :=
  (typeFrame S.ϖ (Equiv.refl _)).coords (typeFrame S.ϖ (Equiv.refl _)) x

theorem phi_eq (j c : ℕ) (h : j + c = s) (x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k) :
    (S.T t).Phi j c h x = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((crd S x).submatrix (stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)) (stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega))).submatrix
        (ixSucc _ t j) id) := rfl

theorem phi_supp (j c : ℕ) (h : j + c = s) (x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k)
    (hx : (S.T t).Phi j c h x ≠ 0) : IntM (crd S x) := by
  rw [phi_eq] at hx
  have H := TypeDatum.intM_of_Phi_ne_zero _ _ hx
  intro i l
  have := H ((ixSucc _ t j).symm ((stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)).symm i)) ((stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)).symm l)
  simpa using this

theorem phi_per (j c : ℕ) (h : j + c = s) (x y : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k)
    (hy : MaxM (crd S y)) : (S.T t).Phi j c h (x + y) = (S.T t).Phi j c h x := by
  have ec : crd S (x + y) = crd S x + crd S y := by
    ext i l; simp [LatFrame.coords, Matrix.mul_add, Matrix.add_mul]
  rw [phi_eq, phi_eq, ec]
  have e2 : ((crd S x + crd S y).submatrix (stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)) (stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega))).submatrix
      (ixSucc _ t j) id = ((crd S x).submatrix (stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)) (stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega))).submatrix
      (ixSucc _ t j) id + ((crd S y).submatrix (stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)) (stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega))).submatrix
      (ixSucc _ t j) id := by ext; simp
  rw [e2]
  exact TypeDatum.Phi_add _ (S.tame _) _ (fun i l => hy _ _)

end Loc
end GlobalTheory.EntryBridge

noncomputable section
namespace GlobalTheory.EntryBridge

section Arith
variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem reduction_one' (P : HeightOneSpectrum (𝓞 E)) : redP P (1 : E) = 1 := by
  simpa using reduction_coe P (1 : 𝓞 E)

theorem reduction_natCast_eq_zero (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) : redP P (q : E) = 0 := by
  have := reduction_coe P ((q : ℕ) : 𝓞 E)
  simp only [map_natCast] at this
  rw [this]
  have h2 := Ideal.Quotient.eq_zero_iff_mem.2 hq
  simpa using h2

theorem q_ne_zero (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) : (q : E) ≠ 0 := by
  intro h
  have h0 : q = 0 := by exact_mod_cast h
  subst h0
  exact hu (by simp)

theorem pow_red (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (k : ℕ) :
    IntAt P ((q : E) ^ (k + 1)) ∧ redP P ((q : E) ^ (k + 1)) = 0 := by
  induction k with
  | zero =>
    rw [zero_add, pow_one]
    exact ⟨ChainCounts.intAt_natCast P q, reduction_natCast_eq_zero hq⟩
  | succ k ih =>
    rw [pow_succ]
    exact ⟨ih.1.mul (ChainCounts.intAt_natCast P q), by
      rw [reduction_mul ih.1 (ChainCounts.intAt_natCast P q), ih.2, zero_mul]⟩

theorem valuation_one₂ (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) :
    LocE.vP P q (1 : E) = 0 := by
  have hq0 : (q : E) ≠ 0 := q_ne_zero hu
  have hI : IntAt P (1 : E) := ChainCounts.intAt_one P
  have hU : IsUnit (redP P (1 : E)) := by rw [reduction_one']; exact isUnit_one
  have hex : ∃ z : ℤ, IsUnit (redP P ((1 : E) / (q : E) ^ z)) := ⟨0, by rwa [zpow_zero, div_one]⟩
  have hspec : IsUnit (redP P ((1 : E) / (q : E) ^ LocE.vP P q (1 : E))) := by
    unfold LocE.vP
    exact Classical.epsilon_spec hex
  by_contra hne
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg (LocE.vP P q (1 : E))
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, zpow_natCast] at hspec
    by_cases hI' : IntAt P ((1 : E) / (q : E) ^ (k' + 1))
    · have e : (1 : E) = (q : E) ^ (k' + 1) * ((1 : E) / (q : E) ^ (k' + 1)) := by field_simp
      have h0 : redP P (1 : E) = 0 := by
        rw [e, reduction_mul (pow_red hq k').1 hI', (pow_red hq k').2, zero_mul]
      rw [h0] at hU
      exact not_isUnit_zero hU
    · rw [reduction_eq_zero_of_not_integral P hI'] at hspec
      exact not_isUnit_zero hspec
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, _root_.zpow_neg, zpow_natCast, div_inv_eq_mul, reduction_mul hI (pow_red hq k').1, (pow_red hq k').2,
      mul_zero] at hspec
    exact not_isUnit_zero hspec

theorem locChar_one {K : Type} [Field K] (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : LocE.locChar q cq χ (1 : E) = 1 := by
  unfold LocE.locChar
  rw [valuation_one₂ hq hu, zpow_zero, zpow_zero, one_mul, div_one]
  have hU : IsUnit (redP P (1 : E)) := by rw [reduction_one']; exact isUnit_one
  unfold LocE.unitV
  rw [dif_pos hU]
  have : hU.unit = 1 := Units.ext (by simp [reduction_one'])
  rw [this, map_one, Units.val_one]

end Arith

section Vol

theorem relIndex_ne_of_map {G : Type} [Group G] (H K : Subgroup G) {F : Type} [Finite F] (f : G → F)
    (h : ∀ x ∈ K, ∀ y ∈ K, f x = f y → x⁻¹ * y ∈ H) : H.relIndex K ≠ 0 := by
  have hinj : Function.Injective fun a : K ⧸ H.subgroupOf K => f ((Quotient.out a : K) : G) := by
    intro a b hab
    have h1 := h _ (Quotient.out a : K).2 _ (Quotient.out b : K).2 hab
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact h1
  have : Finite (K ⧸ H.subgroupOf K) := Finite.of_injective _ hinj
  exact Subgroup.index_ne_zero_of_finite

theorem relIndex_congruenceJacobiSubgroup_stabilizer_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}
    (hU : ChainCounts.UnifAt P) (k₀ rS r t n c : ℕ) :
    (Loc.Cbe (LocE.JGsym P (qOf P) k₀ rS r t n c) 1 ⊓ Loc.N1 E n c).relIndex
      (Loc.N1 E n c ⊓ stabL E (n + c) (LocE.lamY P (qOf P) n c fun i => i + 1)) ≠ 0 := by
  refine relIndex_ne_of_map _ _ (ChainCounts.redM P (LocE.scE n fun i => i + 1)) ?_
  intro x hx y hy hxy
  have hx1 := Subgroup.mem_inf.1 hx
  have hy1 := Subgroup.mem_inf.1 hy
  have hN : x⁻¹ * y ∈ Loc.N1 E n c := (Loc.N1 E n c).mul_mem ((Loc.N1 E n c).inv_mem hx1.1) hy1.1
  have hS : x⁻¹ * y ∈ stabL E (n + c) (LocE.lamY P (qOf P) n c fun i => i + 1) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hx1.2) hy1.2
  have hJ : x⁻¹ * y ∈ LocE.JGsym P (qOf P) k₀ rS r t n c :=
    ChainCounts.mem_JGsym_of_cong P hS (ChainCounts.cong_of_redM hU hx1.2 hy1.2 hxy) k₀ rS r t
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hN).1, Subgroup.mem_comap.2 ?_⟩, hN⟩
  simpa [MulAut.conj_apply] using hJ

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem volN_one_ne (j : ℕ) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (hu : ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2) :
    Loc.volN X.K (Loc.Cbe (Jat (Pr := Pr) (R := R) true j P) (1 : AutY X R j))
      (Loc.N1 X.E (R.N j) (cOf R j) ⊓ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P)) ≠ 0 := by
  have hJ : Jat (Pr := Pr) (R := R) true j P ≤ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P) := by
    unfold Jat lamYat
    rw [if_pos hP, if_pos rfl, if_pos hP]
    exact inf_le_left
  have hle : Loc.Cbe (Jat (Pr := Pr) (R := R) true j P) (1 : AutY X R j) ⊓ Loc.N1 X.E (R.N j) (cOf R j) ≤
      Loc.N1 X.E (R.N j) (cOf R j) ⊓ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P) := by
    intro g hg
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hg).2, hJ ?_⟩
    have h1 := (Subgroup.mem_inf.1 hg).1
    unfold Loc.Cbe at h1
    have h2 := (Subgroup.mem_inf.1 h1).2
    simpa using h2
  have hne := relIndex_congruenceJacobiSubgroup_stabilizer_ne_zero (E := X.E) (ChainCounts.unifAt_of_not_mem_sq P hu) R.k R.rS R.r R.t (R.N j) (cOf R j)
  unfold Loc.volN
  rw [Subgroup.relIndex_eq_one.2 hle, Nat.cast_one, one_div]
  refine inv_ne_zero ?_
  rw [Nat.cast_ne_zero]
  unfold Jat lamYat
  rw [if_pos hP, if_pos rfl, if_pos hP]
  exact hne

end Vol
end GlobalTheory.EntryBridge

noncomputable section
namespace GlobalTheory.EntryBridge

theorem omPhi_one {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
    (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu)
    (hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal) (hu : ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2) :
    omPhi Ch sel mu cst i P 1 1 = PhiAt Ch mu cst.sharp i P.1 := by
  funext x
  unfold omPhi Loc.om muAt
  simp only [map_one, Units.val_one, locChar_one hq hu, valuation_one₂ hq hu]
  simp
  rfl

theorem entry_agree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → AtType Ch sel mu cst σ₀ P ι S → EntryAgree Ch sel mu cst σ₀ P ι S ν := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s S _ _ ν hν hA
  intro j c h e' e he' he
  obtain ⟨-, -, -, -, hq, hu, -, -⟩ := GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer X.E k P.1 (qOf P.1) ι S.ϖ hA.tie.compl S.unif
  haveI := hν.1
  have hm := hA.steps
  have hdeep := hA.deep
  have hcj : cOf R j = c + 1 + 1 := by unfold cOf; omega
  have hcj1 : cOf R (j + 1) = c + 1 := by unfold cOf; omega
  have hreg : (S.T (Fin R.t)).Regular := Chain.ofType_regular _ _ _ _ _
  obtain ⟨ho, hc, -⟩ := hreg.2.2 (j + 1) (c + 1) (by omega)
  have hvN := volNat_Cgrp_pos ν ho hc ((S.T (Fin R.t)).bas (j + 1) (c + 1) (by omega)) 1
  set V : X.K := Loc.volN X.K (Loc.Cbe (Jat (Pr := Pr) (R := R) cst.sharp (j + 1) P.1) (1 : AutY X R (j + 1)))
      (Loc.N1 X.E (R.N (j + 1)) (cOf R (j + 1)) ⊓ stabL X.E _ (lamYat (Pr := Pr) (R := R) (j + 1) P.1)) with hV
  set W : ℝ := volNat ν ((S.T (Fin R.t)).bas (j + 1) (c + 1) (by omega)) (Cgrp ((S.T (Fin R.t)).lev (j + 1) (c + 1) (by omega)).J 1) with hW
  have hvol : V ≠ 0 := by
    rw [hV, hA.sharp]; exact volN_one_ne (j + 1) hA.mem hu
  let E' : XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1 + 1) ≃ Fin (R.N j + cOf R j) :=
    (e'.sumCongr (Equiv.refl _)).trans (finSumFinEquiv.trans (finCongr (by rw [hcj])))
  let E : XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1) ≃ Fin (R.N (j + 1) + cOf R (j + 1)) :=
    (e.sumCongr (Equiv.refl _)).trans (finSumFinEquiv.trans (finCongr (by rw [hcj1])))
  have hE'0 : IsOrd (yPos (fun a => (e' a).val) (R.N j)) E' := by
    rintro (a | a) <;> simp [E', yPos]
  have hE0 : IsOrd (yPos (fun a => (e a).val) (R.N (j + 1))) E := by
    rintro (a | a) <;> simp [E, yPos]
  have hf' : (fun a => (e' a).val) = xPos := funext he'
  have hf : (fun a => (e a).val) = xPos := funext he
  have hE' : IsOrd (yPos xPos (R.N j)) E' := hf' ▸ hE'0
  have hE : IsOrd (yPos xPos (R.N (j + 1))) E := hf ▸ hE0
  have hΦE := GlobalTheory.T.symLevelTestFunctions_agree_rationalPoints X.E X.K k P.1 (qOf P.1) ι σ₀ (psi0P Ch P.1) (chiP Ch P.1) s R.k S hA.tie
    R.t j (c + 1) (by omega) (R.N j) (cOf R j) (R.N (j + 1)) (cOf R (j + 1)) rfl rfl hcj hcj1 E' E hE' hE
  have hpsi : ∀ a, IntAt P.1 a → (S.ψ (ι (a / (qOf P.1 : X.E))) : ℂ) = σ₀ (cst.psi P (a / (qOf P.1 : X.E))) := by
    intro a ha
    rw [hA.tie.psi a ha, hA.psi0 a ha]
  have hsum := GlobalTheory.T.unfoldingIntegral_eq_finiteSum_overNumberField X.E X.K k P.1 (qOf P.1) ι S.ϖ σ₀ S.ψ ν (cst.psi P) hA.tie.compl S.unif S.cond hν hpsi
    (XIx (Fin R.k) (Fin R.t) j) (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) (R.N j) (cOf R j) (R.N (j + 1)) (cOf R (j + 1))
    cst.A cst.B (by omega) hcj hcj1 (by omega) hA.ok.B_pos e' e E' E hE'0 hE0 _ _ hΦE
    (fun x hx => phi_supp S (Fin R.t) j (c + 1) (by omega) x hx)
    (fun x y hy => phi_per S (Fin R.t) j (c + 1) (by omega) x y hy)
  have hrS : R.rS = S.ρ := by have := S.odd; unfold Ranks.rS; omega
  have hr : R.r = R.k + s + 1 := by unfold Ranks.r; omega
  refine ⟨((W⁻¹ : ℝ) : ℂ) / σ₀ V⁻¹, ?_, fun x => ?_⟩
  · exact div_ne_zero (by exact_mod_cast (inv_ne_zero hvN.ne')) ((map_ne_zero σ₀).2 (inv_ne_zero hvol))
  · have e1 : (S.T (Fin R.t)).entry S.ψ ν j c h 1 1 (toLoc ι e e' x) =
        ((W⁻¹ : ℝ) : ℂ) * opE S.ψ ν 1 ((S.T (Fin R.t)).Phi j (c + 1) (by omega)) (toLoc ι e e' x) := by
      simp only [Chain.entry, xi, flat, om_one_one]
      rfl
    have e2 : XiAt Ch sel mu cst j P 1 1 x = V⁻¹ * Loc.E1 (n' := R.N j) (c' := cOf R j) (n := R.N (j + 1)) (c := cOf R (j + 1))
        (cst.psi P) (LocE.valsQ X.E (qOf P.1) cst.A cst.B) (((qOf P.1 : X.K) ^ cst.B)⁻¹)
        (LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k S.ρ (R.k + s + 1) R.t (j + 1) (cOf R j) (R.N j)
          (cOf R (j + 1)) (R.N (j + 1))) x := by
      unfold XiAt E1at
      rw [omPhi_one Ch sel mu cst j P hq hu]
      unfold PhiAt
      rw [if_pos hA.mem, if_pos hA.sharp, hrS, hr]
    rw [e1, hsum x, e2, map_mul]
    have h1 : σ₀ V⁻¹ ≠ 0 := (map_ne_zero σ₀).2 (inv_ne_zero hvol)
    rw [div_mul_eq_mul_div, eq_div_iff h1]
    ring

end GlobalTheory.EntryBridge
