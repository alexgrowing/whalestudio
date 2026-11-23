import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

namespace GoodLoc

variable (hG : GoodLoc σ J T bs v ψv S σS ϖ ε)
include hG

theorem coe_pS : ((hG.pS : S) : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ := rfl

theorem cT_smul_pS (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X) :
    PositivityTheory.PfSWUS.Loc.cT σS (hG.pS • X) = hG.pS • X := by
  ext a b
  have h1 := congrFun (congrFun hX a) b
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    map_mul] at h1 ⊢
  have h2 : σS hG.pS = hG.pS := hG.quad.fix_ϖ
  rw [h2, h1]

theorem hermLev_succ (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X) :
    hG.hermLev (k + 1) (hG.pS • X) (hG.cT_smul_pS k X hX) = hG.hermLev k X hX := by
  apply Subtype.ext
  funext a b
  show (ϖ ^ (k + 1))⁻¹ • (((hG.pS • X) a b : S) : Fv F v ⊗[F] E) = (ϖ ^ k)⁻¹ • ((X a b : S) : Fv F v ⊗[F] E)
  rw [Matrix.smul_apply, smul_eq_mul, Subring.coe_mul, coe_pS, ← Algebra.smul_def, smul_smul, pow_succ, mul_inv,
    mul_assoc, inv_mul_cancel₀ hG.unif_ne, mul_one]

def liftH {k : ℕ} (B : hermMod σS hG.pS n k) : Matrix (Fin n) (Fin n) S := Classical.choose B.2

theorem liftH_herm {k : ℕ} (B : hermMod σS hG.pS n k) : PositivityTheory.PfSWUS.Loc.cT σS (hG.liftH B) = hG.liftH B :=
  (Classical.choose_spec B.2).1

theorem red_liftH {k : ℕ} (B : hermMod σS hG.pS n k) : red hG.pS k (hG.liftH B) = B.1 :=
  (Classical.choose_spec B.2).2

def iota (k : ℕ) (B : hermMod σS hG.pS n k) : HermR (Fv F v) σ n ⧸ H0 S σ n :=
  QuotientAddGroup.mk (hG.hermLev k (hG.liftH B) (hG.liftH_herm B))

theorem iota_eq (hCL : ClassLev) (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X)
    (B : hermMod σS hG.pS n k) (hB : red hG.pS k X = B.1) :
    hG.iota k B = QuotientAddGroup.mk (hG.hermLev k X hX) := by
  unfold iota
  rw [QuotientAddGroup.eq, neg_add_eq_sub]
  exact (hCL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG k X (hG.liftH B) hX (hG.liftH_herm B)).2 (by rw [hB, hG.red_liftH])

theorem iota_inj (hCL : ClassLev) (k : ℕ) : Function.Injective (hG.iota k) := by
  intro B B' h
  unfold iota at h
  rw [QuotientAddGroup.eq, neg_add_eq_sub] at h
  have := (hCL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG k (hG.liftH B') (hG.liftH B) (hG.liftH_herm B') (hG.liftH_herm B)).1 h
  rw [hG.red_liftH, hG.red_liftH] at this
  exact Subtype.ext this.symm

theorem iota_succ (hCL : ClassLev) (k : ℕ) (B : hermMod σS hG.pS n k) :
    ∃ B' : hermMod σS hG.pS n (k + 1), hG.iota (k + 1) B' = hG.iota k B := by
  refine ⟨⟨red hG.pS (k + 1) (hG.pS • hG.liftH B), hG.pS • hG.liftH B, hG.cT_smul_pS k _ (hG.liftH_herm B), rfl⟩, ?_⟩
  rw [hG.iota_eq hCL (k + 1) (hG.pS • hG.liftH B) (hG.cT_smul_pS k _ (hG.liftH_herm B)) _ rfl, hG.hermLev_succ]
  rfl

theorem iota_surj (hCL : ClassLev) (hEx : Exhaust) (c : HermR (Fv F v) σ n ⧸ H0 S σ n) :
    ∃ k B, hG.iota k B = c := by
  induction c using QuotientAddGroup.induction_on with
  | H b =>
    obtain ⟨k, X, hX, rfl⟩ := hEx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG b
    exact ⟨k, ⟨red hG.pS k X, X, hX, rfl⟩, hG.iota_eq hCL k X hX _ rfl⟩

theorem f_lev (hNP : NuPow) (hJ : JtLev) (hNL : NuLev) (hPL : PsiLev) (hT : ∀ a b, σ (T b a) = T a b)
    (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (hμ : SdW F E σ M J (Fv F v) ψv n μv)
    (lam : Measure (Fin n → Fv F v ⊗[F] E)) (L : AddSubgroup (Fin n → Fv F v ⊗[F] E)) (hlam : lam.IsAddHaarMeasure)
    (hL : (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v) (z : ℂ) (k : ℕ) (B : hermMod σS hG.pS n k) :
    whI (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z
      (hG.hermLev k (hG.liftH B) (hG.liftH_herm B)) =
    ((ε : ℂ) ^ M * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * z + n))) ^
        Nat.log (Ideal.absNorm v.asIdeal ^ 2) (nuAt hG.pS B.1) *
      hG.psiLev (c := -1) (neg_mem (one_mem _)) k (Matrix.trace (red hG.pS k (matS S T hG.T_int) * B.1)) := by
  have e1 := hNL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG lam L hlam hL k (hG.liftH B) (hG.liftH_herm B)
  have e2 := hJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG μv hμ k (hG.liftH B) (hG.liftH_herm B)
  have e3 := hPL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG hT k (hG.liftH B) (hG.liftH_herm B)
  rw [hG.red_liftH] at e1 e2 e3
  have e4 : nuAt hG.pS B.1 = (Ideal.absNorm v.asIdeal ^ 2) ^ Nat.log (Ideal.absNorm v.asIdeal ^ 2) (nuAt hG.pS B.1) :=
    hNP S σS hG.pS _ ε hG.quad n k B.1 B.2
  have hq0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    have := hG.quad.one_lt
    exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)
  simp only [whI]
  rw [e1, e2, e3]
  congr 1
  set D := Nat.log (Ideal.absNorm v.asIdeal ^ 2) (nuAt hG.pS B.1)
  set q := Ideal.absNorm v.asIdeal
  rw [e4]
  have h5 : ((((q ^ 2) ^ D : ℕ) : ℝ) : ℂ) = ((q : ℂ) ^ (2 * D : ℕ)) := by push_cast; ring
  rw [h5, ← Complex.natCast_cpow_natCast_mul]
  have h6 : ((2 * D : ℕ) : ℂ) * -(z - ((M : ℂ) - n) / 2) = (D : ℂ) * (2 * -(z - ((M : ℂ) - n) / 2)) := by push_cast; ring
  rw [h6, Complex.cpow_nat_mul, ← mul_pow]
  congr 1
  rw [← Complex.cpow_intCast, mul_left_comm, ← Complex.cpow_add _ _ hq0]
  congr 2
  push_cast
  ring

end GoodLoc

end PositivityTheory.SiegelWeilFormula.Gunr

end
