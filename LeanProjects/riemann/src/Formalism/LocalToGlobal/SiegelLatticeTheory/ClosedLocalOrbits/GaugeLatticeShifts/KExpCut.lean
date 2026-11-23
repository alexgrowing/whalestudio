import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOpStmt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolicInhab
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOpInhab
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHCut
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PoincareSeriesInner
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix

namespace Formalism.L2.SG.TermOp.KExpCut

open Formalism.L2.SG.TermOp

section Blocks

variable {ι ι' : Type} [Fintype ι] [Fintype ι'] {V V' : Type}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def blkOpL (B : ι → ι' → (V' →L[ℂ] V)) : PiLp 2 (fun _ : ι' => V') →ₗ[ℂ] PiLp 2 (fun _ : ι => V) where
  toFun φ := WithLp.toLp 2 fun ρ => ∑ ρ', B ρ ρ' (φ ρ')
  map_add' φ ψ := by
    ext ρ
    simp [Finset.sum_add_distrib]
  map_smul' c φ := by
    ext ρ
    simp [Finset.smul_sum]

def blkOp (B : ι → ι' → (V' →L[ℂ] V)) : PiLp 2 (fun _ : ι' => V') →L[ℂ] PiLp 2 (fun _ : ι => V) :=
  LinearMap.toContinuousLinearMap (blkOpL B)

def blkOpLin : (ι → ι' → (V' →L[ℂ] V)) →ₗ[ℂ] (PiLp 2 (fun _ : ι' => V') →L[ℂ] PiLp 2 (fun _ : ι => V)) where
  toFun := blkOp
  map_add' B C := by
    ext φ ρ
    simp [blkOp, blkOpL, Finset.sum_add_distrib]
  map_smul' c B := by
    ext φ ρ
    simp [blkOp, blkOpL, Finset.smul_sum]

theorem blkOpLin_apply (B : ι → ι' → (V' →L[ℂ] V)) : blkOpLin B = blkOp B := rfl

theorem hasSum_blkOp {τ : Type*} (f : τ → ι → ι' → (V' →L[ℂ] V)) (B : ι → ι' → (V' →L[ℂ] V))
    (h : ∀ ρ ρ', HasSum (fun t => f t ρ ρ') (B ρ ρ')) : HasSum (fun t => blkOp (f t)) (blkOp B) := by
  have hB : HasSum f B := Pi.hasSum.2 fun ρ => Pi.hasSum.2 fun ρ' => h ρ ρ'
  have hc : Continuous (blkOpLin (ι := ι) (ι' := ι') (V := V) (V' := V')) :=
    LinearMap.continuous_of_finiteDimensional _
  exact hB.map (blkOpLin (ι := ι) (ι' := ι') (V := V) (V' := V')) hc

theorem inner_blkOp (B : ι → ι' → (V' →L[ℂ] V)) (x : PiLp 2 (fun _ : ι' => V')) (y : PiLp 2 (fun _ : ι => V)) :
    inner ℂ (blkOp B x) y = ∑ ρ, ∑ ρ', inner ℂ (B ρ ρ' (x ρ')) (y ρ) := by
  simp only [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  change inner ℂ (∑ ρ', B ρ ρ' (x ρ')) (y ρ) = _
  rw [sum_inner]

theorem exists_norm_blkOp_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ι → ι' → (V' →L[ℂ] V), ‖blkOp B‖ ≤ C * ‖B‖ := by
  refine ⟨‖LinearMap.toContinuousLinearMap (blkOpLin (ι := ι) (ι' := ι') (V := V) (V' := V'))‖,
    norm_nonneg _, fun B => ?_⟩
  exact (LinearMap.toContinuousLinearMap (blkOpLin (ι := ι) (ι' := ι') (V := V) (V' := V'))).le_opNorm B

theorem blkOp_zero : blkOp (0 : ι → ι' → (V' →L[ℂ] V)) = 0 := by
  rw [← blkOpLin_apply, map_zero]

theorem blkOp_delta :
    blkOp (fun ρ ρ' : ι => if ρ = ρ' then ContinuousLinearMap.id ℂ V else 0) = ContinuousLinearMap.id ℂ _ := by
  ext φ ρ
  change ∑ ρ', (if ρ = ρ' then ContinuousLinearMap.id ℂ V else 0) (φ ρ') = φ ρ
  rw [Finset.sum_eq_single ρ (fun b _ hb => by simp [Ne.symm hb]) (fun h => absurd (Finset.mem_univ ρ) h)]
  simp

end Blocks

section Steps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)

theorem hasSum_aTerm {τ : Type*} (f : τ → GTerm X u u' F0 F0' what₂ rows') (B : cs.Cl → cs'.Cl → (X.Vpi u' →L[ℂ] X.Vpi u))
    (h : ∀ ρ ρ', HasSum (fun i => blk cs cs' FdN FdN' (f i) ρ ρ') (B ρ ρ')) :
    HasSum (fun i => aTerm cs cs' FdN FdN' (f i)) (blkOp B) := by
  exact hasSum_blkOp (fun i => blk cs cs' FdN FdN' (f i)) B h

theorem norm_blk_le (hK : X.LevelSubgroupCharacter) (t : GTerm X u u' F0 F0' what₂ rows') (ρ : cs.Cl) (ρ' : cs'.Cl) :
    ‖blk cs cs' FdN FdN' t ρ ρ'‖ ≤ |scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2| * ‖OOt t‖ := by
  unfold blk
  split_ifs with hc
  · rw [norm_smul, norm_smul, hK.2.2.2.2 _ hc.2.2, one_mul, Complex.norm_real, Real.norm_eq_abs]
  · rw [norm_zero]
    exact mul_nonneg (abs_nonneg _) (norm_nonneg _)

variable (F0 F0' what₂ rows') in

def OOAbs : Prop := Summable (fun t : GTerm X u u' F0 F0' what₂ rows' => ‖OOt t‖)

variable (F0 F0') in

def EntryUnfold (hK : X.LevelSubgroupCharacter) (Dt Dt' : Set X.B.I.GA) : Prop :=
  ∀ (T : Cu X u hK) (T' : Cu X u' hK),
    Kform X u u' hK Dt Dt' FdN FdN' T T' =
      ∑ ρ, ∑ ρ', inner ℂ ((∑' t : GTerm X u u' F0 F0' what₂ rows', blk cs cs' FdN FdN' t ρ ρ') (sharp hK cs' T' ρ'))
        (sharp hK cs T ρ)

variable (F0 F0' what₂ rows') in

def OOVanish : Prop := ∀ t : GTerm X u u' F0 F0' what₂ rows', ¬ t.relevant → OOt t = 0

variable (F0 F0') in

def IdOffBlocks : Prop :=
  u ≠ u' → ∀ (ρ : cs.Cl) (ρ' : cs'.Cl),
    HasSum (fun t : {t : GTerm X u u' F0 F0' what₂ rows' // t.isId} => blk cs cs' FdN FdN' t.1 ρ ρ') 0

theorem idCellOff_of (h : IdOffBlocks F0 F0' cs cs' FdN FdN') : IdCellOff F0 F0' cs cs' FdN FdN' := by
  intro hu
  have := hasSum_aTerm cs cs' FdN FdN' (fun t : {t : GTerm X u u' F0 F0' what₂ rows' // t.isId} => t.1) 0
    (fun ρ ρ' => by simpa using h hu ρ ρ')
  rwa [blkOp_zero] at this

end Steps

section StepsDiag

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (cs : ColSys X u what₂) (FdN : Set X.B.I.Ginf)

variable (F0) in

def IdDiagBlocks : Prop :=
  Formalism.L2.SG.HidaSetting.IsSFund X.B.I (NOinf X u) FdN → ∀ ρ ρ' : cs.Cl,
    HasSum (fun t : {t : GTerm X u u F0 F0 what₂ what₂ // t.isId} => blk cs cs FdN FdN t.1 ρ ρ')
      (if ρ = ρ' then ContinuousLinearMap.id ℂ (X.Vpi u) else 0)

theorem idCellDiag_of (h : IdDiagBlocks F0 cs FdN) : IdCellDiag F0 cs FdN := by
  intro hF
  have := hasSum_aTerm cs cs FdN FdN (fun t : {t : GTerm X u u F0 F0 what₂ what₂ // t.isId} => t.1)
    (fun ρ ρ' : cs.Cl => if ρ = ρ' then ContinuousLinearMap.id ℂ (X.Vpi u) else 0) (h hF)
  rwa [blkOp_delta] at this

end StepsDiag

section PsiTorsion

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem adic_torsion {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (a : v.adicCompletion F) :
    ∃ n : ℕ, 0 < n ∧ (n : v.adicCompletion F) * a ∈ v.adicCompletionIntegers F := by
  obtain ⟨b, hb, hab⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v a
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  have hn0 : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hb0
  refine ⟨Ideal.absNorm (Ideal.span {b}), Nat.pos_of_ne_zero hn0, ?_⟩
  have e1 : ((Ideal.absNorm (Ideal.span {b}) : ℕ) : v.adicCompletion F) =
      algebraMap (𝓞 F) (v.adicCompletion F) c * algebraMap (𝓞 F) (v.adicCompletion F) b := by
    rw [← map_mul, hc, map_natCast]
  rw [e1, mul_assoc, mul_comm (algebraMap _ _ b) a]
  refine mul_mem ?_ hab
  exact coe_mem_adicCompletionIntegers (K := F) v c

theorem fa_torsion {F : Type} [Field F] [NumberField F] (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ n : ℕ, 0 < n ∧ (n : FiniteAdeleRing (𝓞 F) F) * a ∈ Formalism.UG.intAd F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | a v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 a.2
  choose m hm0 hm using fun v => adic_torsion v (a v)
  refine ⟨∏ v ∈ hfin.toFinset, m v, Finset.prod_pos fun v _ => hm0 v, fun w => ?_⟩
  show ((∏ v ∈ hfin.toFinset, m v : ℕ) : w.adicCompletion F) * a w ∈ _
  by_cases hw : w ∈ hfin.toFinset
  · rw [← Finset.mul_prod_erase _ _ hw, Nat.cast_mul, mul_comm ((m w : ℕ) : w.adicCompletion F), mul_assoc]
    exact mul_mem (natCast_mem _ _) (hm w)
  · have ha : a w ∈ w.adicCompletionIntegers F := by
      simpa [Set.Finite.mem_toFinset] using hw
    exact mul_mem (natCast_mem _ _) ha

theorem int_multiple {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ n : ℕ, 0 < n ∧ (n : E) * e ∈ Formalism.UG.intOE E := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  have hn0 : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hb0
  refine ⟨Ideal.absNorm (Ideal.span {b}), Nat.pos_of_ne_zero hn0, c * a, ?_⟩
  have hbE : algebraMap (𝓞 E) E b ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)]
    exact hb0
  rw [← map_natCast (algebraMap (𝓞 E) E), ← hc, map_mul, map_mul]
  field_simp

theorem tens_torsion {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : E ⊗[F] Formalism.MainNotions.S.Af F) : ∃ n : ℕ, 0 < n ∧ n • x ∈ Formalism.MainNotions.S.IntAf F E := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩
  | tmul e a =>
    obtain ⟨d, hd0, hd⟩ := int_multiple e
    obtain ⟨m, hm0, hm⟩ := fa_torsion a
    refine ⟨d * m, Nat.mul_pos hd0 hm0, ?_⟩
    have h1 : (d * m) • (e ⊗ₜ[F] a) = ((d : E) * e) ⊗ₜ[F] (1 : Formalism.MainNotions.S.Af F) *
        (1 : E) ⊗ₜ[F] ((m : Formalism.MainNotions.S.Af F) * a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_smul, ← TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', nsmul_eq_mul, nsmul_eq_mul]
    rw [h1]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, hd⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨_, hm⟩, rfl⟩))
  | add x y hx hy =>
    obtain ⟨n1, h1, hx⟩ := hx
    obtain ⟨n2, h2, hy⟩ := hy
    refine ⟨n1 * n2, Nat.mul_pos h1 h2, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact nsmul_mem hx _
    · rw [mul_smul]
      exact nsmul_mem hy _

theorem psi_unit_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ψ : E ⊗[F] Formalism.MainNotions.S.Af F → ℂ) (hadd : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (hint : ∀ x ∈ Formalism.MainNotions.S.IntAf F E, ψ x = 1) (x : E ⊗[F] Formalism.MainNotions.S.Af F) : ‖ψ x‖ = 1 := by
  obtain ⟨n, hn, hx⟩ := tens_torsion x
  have hpow : ∀ m : ℕ, ψ (m • x) = ψ x ^ m := by
    intro m
    induction m with
    | zero =>
      have h0 : ψ 0 = 1 := by
        have := hadd (n • x) 0
        rw [add_zero, hint _ hx, one_mul] at this
        exact this.symm
      simp [h0]
    | succ m ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have h1 : ‖ψ x‖ ^ n = 1 := by rw [← norm_pow, ← hpow, hint _ hx, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1

end PsiTorsion

section Abs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting

theorem exists_bound_lin' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (L : E →ₗ[ℂ] F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖L x‖ ≤ C * ‖x‖ := by
  exact ⟨‖LinearMap.toContinuousLinearMap L‖, norm_nonneg _,
    fun x => (LinearMap.toContinuousLinearMap L).le_opNorm x⟩

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (TR : TypedRed X) (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)

variable (X) in

def PsiUnit : Prop := ∀ x, ‖X.psiEf x‖ = 1

variable (X) in

theorem psiUnit : PsiUnit X := by
  exact fun x => psi_unit_of X.psiEf X.psiEf_add X.psiEf_int x

private theorem piLp_two_norm_eq_norm_apply_of_single_support {κ : Type} [Fintype κ] {W : Type} [NormedAddCommGroup W]
    (x : PiLp 2 (fun _ : κ => W)) (q0 : κ) (hx : ∀ q, q ≠ q0 → x q = 0) : ‖x‖ = ‖x q0‖ := by
  have h := PiLp.norm_sq_eq_of_L2 (fun _ : κ => W) x
  rw [Finset.sum_eq_single q0 (fun q _ hq => by simp [hx q hq]) (fun h => absurd (Finset.mem_univ q0) h)] at h
  have := congrArg Real.sqrt h
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

theorem norm_blks_le (hK : X.LevelSubgroupCharacter) (t : GTerm X u u' F0 F0' what₂ rows') :
    ‖blk cs cs' FdN FdN' t‖ ≤ |scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2| * ‖OOt t‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun ρ =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun ρ' => norm_blk_le cs cs' FdN FdN' hK t ρ ρ'

theorem wt_le (t : GTerm X u u' F0 F0' what₂ rows') :
    |wt t| ≤ ∑ Λ ∈ what₂, ∑ Λ' ∈ rows', Real.sqrt (wRow D F0 Λ * wRow D F0' Λ') := by
  rw [abs_of_nonneg (show 0 ≤ wt t from Real.sqrt_nonneg _)]
  calc wt t = Real.sqrt (wRow D F0 t.lam * wRow D F0' t.lam') := rfl
    _ ≤ ∑ Λ' ∈ rows', Real.sqrt (wRow D F0 t.lam * wRow D F0' Λ') :=
        Finset.single_le_sum (f := fun Λ' => Real.sqrt (wRow D F0 t.lam * wRow D F0' Λ'))
          (fun _ _ => Real.sqrt_nonneg _) t.mem'
    _ ≤ _ := Finset.single_le_sum (f := fun Λ => ∑ Λ' ∈ rows', Real.sqrt (wRow D F0 Λ * wRow D F0' Λ'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _) t.mem

theorem absConvT_of (hK : X.LevelSubgroupCharacter) (hψ : PsiUnit X) (hO : OOAbs F0 F0' what₂ rows' (X := X) (u := u) (u' := u')) :
    AbsConvT F0 F0' TR cs cs' FdN FdN' := by
  obtain ⟨C1, hC1, hb1⟩ := exists_bound_lin' (Formalism.L2.SG.PackageTie.hsEmb (Wq := CM cs') (Wp := CM cs))
  obtain ⟨C2, hC2, hb2⟩ := exists_norm_blkOp_le (ι := cs.Cl) (ι' := cs'.Cl) (V := X.Vpi u) (V' := X.Vpi u')
  obtain ⟨C3, hC3, hb3⟩ := exists_bound_lin' (Formalism.L2.SG.PackageTie.hsEmb (Wq := X.Vpi u') (Wp := X.Vpi u))
  have hc : 0 ≤ |scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2| := abs_nonneg _
  unfold AbsConvT Formalism.FourierDecayAlt.PB.Terms.AbsConv
  refine ⟨?_, ?_, gamma_one_pos TR⟩
  · refine Summable.of_nonneg_of_le (fun t => norm_nonneg _) (fun t => ?_)
      (hO.mul_left (C1 * C2 * |scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2|))
    change ‖op cs cs' FdN FdN' t‖ ≤ _
    calc ‖op cs cs' FdN FdN' t‖ ≤ C1 * ‖aTerm cs cs' FdN FdN' t‖ := hb1 _
      _ = C1 * ‖blkOp (blk cs cs' FdN FdN' t)‖ := rfl
      _ ≤ C1 * (C2 * ‖blk cs cs' FdN FdN' t‖) := mul_le_mul_of_nonneg_left (hb2 _) hC1
      _ ≤ C1 * (C2 * (|scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2| * ‖OOt t‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_blks_le cs cs' FdN FdN' hK t) hC2) hC1
      _ = C1 * C2 * |scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2| * ‖OOt t‖ := by ring
  · refine Summable.of_nonneg_of_le (fun t => norm_nonneg _) (fun t => ?_)
      (hO.mul_left ((∑ Λ ∈ what₂, ∑ Λ' ∈ rows', Real.sqrt (wRow D F0 Λ * wRow D F0' Λ')) * C3 *
        |scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2|))
    change ‖vec cs cs' FdN FdN' t‖ ≤ _
    have hamp : ‖ampN cs cs' FdN FdN' t‖ = |scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2| * ‖OOt t‖ := by
      simp only [ampN, chiN, norm_smul, hψ _, Complex.norm_real, Real.norm_eq_abs, one_mul]
    have hv : ‖vec cs cs' FdN FdN' t‖ =
        ‖((wt t : ℝ) : ℂ) • Formalism.L2.SG.PackageTie.hsEmb (ampN cs cs' FdN FdN' t)‖ := by
      rw [piLp_two_norm_eq_norm_apply_of_single_support (vec cs cs' FdN FdN' t) (⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩)
        (fun q hq => by simp [vec, hq])]
      simp [vec]
    rw [hv, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |wt t| * ‖Formalism.L2.SG.PackageTie.hsEmb (ampN cs cs' FdN FdN' t)‖
        ≤ (∑ Λ ∈ what₂, ∑ Λ' ∈ rows', Real.sqrt (wRow D F0 Λ * wRow D F0' Λ')) * (C3 * ‖ampN cs cs' FdN FdN' t‖) :=
          mul_le_mul (wt_le t) (hb3 _) (norm_nonneg _) (le_trans (abs_nonneg _) (wt_le t))
      _ = _ := by rw [hamp]; ring

variable (F0 F0' what₂ rows') in

def OOLint : Prop :=
  ∀ t : GTerm X u u' F0 F0' what₂ rows',
    ∫⁻ x in FundOf t, ‖X.Wu u x‖ₑ * ‖X.Wu u' (t.pt.1⁻¹ * x)‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤

theorem norm_rankOneInnerOperator {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (v : V) (w : V') : ‖rk1 v w‖ = ‖v‖ * ‖w‖ := by
  simp only [rk1]
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]

theorem ooIntAll_of (h : OOLint F0 F0' what₂ rows' (X := X) (u := u) (u' := u')) :
    OOIntAll X u u' F0 F0' what₂ rows' := by
  intro t
  have hW := (X.Wu_spec u).2.2.1
  have hW' := (X.Wu_spec u').2.2.1
  have h1 : Continuous fun x : X.B.I.Ginf => innerSL ℂ (X.Wu u' (t.pt.1⁻¹ * x)) :=
    (innerSL ℂ).continuous.comp (hW'.comp (continuous_const.mul continuous_id))
  have hcont : Continuous fun x : X.B.I.Ginf => rk1 (X.Wu u x) (X.Wu u' (t.pt.1⁻¹ * x)) := by
    have h2 := ((ContinuousLinearMap.smulRightL ℂ (X.Vpi u') (X.Vpi u)).continuous.comp h1).clm_apply hW
    simpa [rk1] using h2
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) (h t)
  rw [← ofReal_norm, norm_rankOneInnerOperator, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
    ofReal_norm]

end Abs

section FromAbs

variable {ι ι' : Type} [Fintype ι] [Fintype ι'] {V V' : Type}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

private theorem piLp_two_norm_apply_le_norm {κ : Type} [Fintype κ] {W : Type} [NormedAddCommGroup W]
    (f : PiLp 2 (fun _ : κ => W)) (i : κ) : ‖f i‖ ≤ ‖f‖ := by
  have h := PiLp.norm_sq_eq_of_L2 (fun _ : κ => W) f
  have h2 : ‖f i‖ ^ 2 ≤ ∑ j, ‖f j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖f j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [norm_nonneg (f i), norm_nonneg f]

theorem norm_le_blkOp (B : ι → ι' → (V' →L[ℂ] V)) (ρ : ι) (ρ' : ι') : ‖B ρ ρ'‖ ≤ ‖blkOp B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  let x : PiLp 2 (fun _ : ι' => V') := WithLp.toLp 2 (fun σ => if σ = ρ' then v else 0)
  have hx0 : ∀ σ, σ ≠ ρ' → x σ = 0 := fun σ hσ => by simp [x, hσ]
  have hx : ‖x‖ = ‖v‖ := by
    have h := PiLp.norm_sq_eq_of_L2 (fun _ : ι' => V') x
    rw [Finset.sum_eq_single ρ' (fun σ _ hσ => by simp [hx0 σ hσ]) (fun h => absurd (Finset.mem_univ ρ') h)] at h
    have h' : x ρ' = v := by simp [x]
    rw [h'] at h
    have := congrArg Real.sqrt h
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  have h1 : (blkOp B x) ρ = B ρ ρ' v := by
    change ∑ σ, B ρ σ (x σ) = _
    rw [Finset.sum_eq_single ρ' (fun σ _ hσ => by simp [hx0 σ hσ]) (fun h => absurd (Finset.mem_univ ρ') h)]
    simp [x]
  calc ‖B ρ ρ' v‖ = ‖(blkOp B x) ρ‖ := by rw [h1]
    _ ≤ ‖blkOp B x‖ := piLp_two_norm_apply_le_norm _ _
    _ ≤ ‖blkOp B‖ * ‖x‖ := (blkOp B).le_opNorm x
    _ = ‖blkOp B‖ * ‖v‖ := by rw [hx]

theorem hsEmb_injective : Function.Injective (Formalism.L2.SG.PackageTie.hsEmb (Wq := V') (Wp := V)) := by
  intro A B h
  have h' : ∀ i, A (stdOrthonormalBasis ℂ V' i) = B (stdOrthonormalBasis ℂ V' i) := fun i => by
    have := congrArg (fun x : Formalism.L2.SG.PackageTie.HS V' V => x i) h
    simpa [Formalism.L2.SG.PackageTie.hsEmb] using this
  apply ContinuousLinearMap.coe_injective
  refine (stdOrthonormalBasis ℂ V').toBasis.ext fun i => ?_
  simpa using h' i

theorem exists_norm_le_hs : ∃ C : ℝ, 0 ≤ C ∧ ∀ A : V' →L[ℂ] V, ‖A‖ ≤ C * ‖Formalism.L2.SG.PackageTie.hsEmb A‖ := by
  let e := (LinearEquiv.ofInjective _ (hsEmb_injective (V := V) (V' := V'))).toContinuousLinearEquiv
  let L := e.symm.toContinuousLinearMap
  refine ⟨‖L‖, norm_nonneg _, fun A => ?_⟩
  calc ‖A‖ = ‖L (e A)‖ := by simp [L]
    _ ≤ ‖L‖ * ‖e A‖ := L.le_opNorm _
    _ = _ := rfl

end FromAbs

section FromAbsT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (TR : TypedRed X) (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)

theorem summable_blk_of_abs (hA : AbsConvT F0 F0' TR cs cs' FdN FdN') (ρ : cs.Cl) (ρ' : cs'.Cl) :
    Summable (fun t : GTerm X u u' F0 F0' what₂ rows' => blk cs cs' FdN FdN' t ρ ρ') := by
  obtain ⟨C, hC, hb⟩ := exists_norm_le_hs (V := CM cs) (V' := CM cs')
  refine Summable.of_norm_bounded (g := fun t => C * ‖op cs cs' FdN FdN' t‖) (hA.1.mul_left C) (fun t => ?_)
  calc ‖blk cs cs' FdN FdN' t ρ ρ'‖ ≤ ‖blkOp (blk cs cs' FdN FdN' t)‖ := norm_le_blkOp _ _ _
    _ = ‖aTerm cs cs' FdN FdN' t‖ := rfl
    _ ≤ C * ‖op cs cs' FdN FdN' t‖ := hb _

theorem kExpansion_of_abs (hK : X.LevelSubgroupCharacter) (Dt Dt' : Set X.B.I.GA) (hA : AbsConvT F0 F0' TR cs cs' FdN FdN')
    (hE : EntryUnfold F0 F0' cs cs' FdN FdN' hK Dt Dt') :
    KExpansion F0 F0' cs cs' FdN FdN' hK Dt Dt' := by
  refine ⟨blkOp (fun ρ ρ' => ∑' t, blk cs cs' FdN FdN' t ρ ρ'),
    hasSum_aTerm cs cs' FdN FdN' (fun t => t) _ (fun ρ ρ' => (summable_blk_of_abs TR cs cs' FdN FdN' hA ρ ρ').hasSum),
    fun T T' => ?_⟩
  rw [hE T T', inner_blkOp]

end FromAbsT

section Closed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Full Formalism.L2.SG.PoincareInHH.PoincareSetting

theorem absConvC_of
    (h : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.WuDecay.FoldOK X u Y.hK → Formalism.L2.SG.WuDecay.FoldOK X u' Y.hK →
      FundExists X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
      OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
      OOAbs (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X)) :
    AbsConvC := by
  intro D X Y u u' hF hF' hFE hOI
  exact absConvT_of Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') Y.hK (psiUnit X) (h D X Y u u' hF hF' hFE hOI)

theorem idCellOffC_of
    (h : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      FundExists X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
      OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
      IdOffBlocks (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u')) :
    IdCellOffC := by
  intro D X Y u u' hFE hOI
  exact idCellOff_of (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (h D X Y u u' hFE hOI)

theorem idCellDiagC_of
    (h : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      X.LevelSubgroupNormalized →
      FundExists X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) →
      OOIntAll X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) →
      IdDiagBlocks (X.Fu u) (Y.cs u) (Y.FN u)) :
    IdCellDiagC := by
  intro D X Y u hKL hFE hOI
  exact idCellDiag_of (Y.cs u) (Y.FN u) (h D X Y u hKL hFE hOI)

theorem ooIntAllC_of
    (h : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.WuDecay.FoldOK X u Y.hK → Formalism.L2.SG.WuDecay.FoldOK X u' Y.hK →
      FundExists X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
      OOLint (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X)) :
    OOIntAllC := by
  intro D X Y u u' hF hF' hFE
  exact ooIntAll_of (h D X Y u u' hF hF' hFE)

end Closed

section Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.PoincareSeriesSquareIntegrable

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)

theorem integral_conj_mul {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → ℂ) :
    ∫ x, conj (f x) * g x ∂μ = conj (∫ x, f x * conj (g x) ∂μ) := by
  rw [← integral_conj]
  congr 1
  funext x
  simp

variable (F0 F0') in

def DCTerms (hK : X.LevelSubgroupCharacter) (R : Set X.B.I.GA) (Fs : X.B.I.GA → Set X.B.I.GA) : Prop :=
  ∀ (T : Cu X u hK) (T' : Cu X u' hK),
    ((scl FdN FdN' (X := X) (u := u) (u' := u') : ℝ) : ℂ) *
        conj (∑' r : R, ∫ x in Fs r, Ph X u hK T x * conj (Ph X u' hK T' ((r : X.B.I.GA)⁻¹ * x))
          ∂(X.B.I.muA X.B.μf)) =
      ∑ ρ, ∑ ρ', inner ℂ ((∑' t : GTerm X u u' F0 F0' what₂ rows', blk cs cs' FdN FdN' t ρ ρ') (sharp hK cs' T' ρ'))
        (sharp hK cs T ρ)

theorem kform_unfold (hK : X.LevelSubgroupCharacter) (hR : FoldReadyX X)
    (hFB : FundBridge X) (hOK : Formalism.L2.SG.WuDecay.FoldOK X u hK) (hOK' : Formalism.L2.SG.WuDecay.FoldOK X u' hK)
    (hin : InHH X u hK) (hin' : InHH X u' hK) (Dt Dt' : Set X.B.I.GA) (hD : IsReps X u Dt) (hD' : IsReps X u' Dt')
    (R : Set X.B.I.GA) (hRt : IsDoubleTransversal (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u) (Srat X u') R)
    (Fs : X.B.I.GA → Set X.B.I.GA)
    (hFs : ∀ r ∈ R, IsFundamentalDomain (stab (Srat X u) (Srat X u') r) (Fs r) (X.B.I.muA X.B.μf))
    (T : Cu X u hK) (T' : Cu X u' hK) :
    Kform X u u' hK Dt Dt' FdN FdN' T T' =
      ((scl FdN FdN' (X := X) (u := u) (u' := u') : ℝ) : ℂ) *
        conj (∑' r : R, ∫ x in Fs r, Ph X u hK T x * conj (Ph X u' hK T' ((r : X.B.I.GA)⁻¹ * x))
          ∂(X.B.I.muA X.B.μf)) := by
  obtain ⟨⟨F, hF⟩, Ω₀, a, hc0, h10, hT⟩ := hOK
  obtain ⟨⟨F', hF'⟩, Ω₀', a', hc0', h10', hT'⟩ := hOK'
  have hΩ : IsCompact (Ω₀ ∪ Ω₀') := hc0.union hc0'
  have hm := (hin T Dt hD).2.2.1
  have hm' := (hin' T' Dt' hD').2.2.1
  have hc := @fold_l2_bound_c X.B.I.GA _ _ _ hR.1 hR.2.1 hR.2.2.1 _ hR.2.2.2.1 (X.B.I.muA X.B.μf)
    (@muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar)
  have hU := hc (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u) (Srat X u') hR.2.2.2.2 inf_le_left inf_le_left
    (Ω₀ ∪ Ω₀') hΩ (Or.inl h10) a a' (Ph X u hK T) (Ph X u' hK T')
    ((hT T).1 _ hΩ Set.subset_union_left) ((hT' T').1 _ hΩ Set.subset_union_right) F F' hF hF'
    ((hT T).2 _ hΩ F hF) ((hT' T').2 _ hΩ F' hF') Dt Dt' hD hD' R hRt Fs hFs X.B.fund hFB
  have e1 : PuFun X u hK Dt T = hm.toLp _ := dif_pos hm
  have e2 : PuFun X u' hK Dt' T' = hm'.toLp _ := dif_pos hm'
  unfold Kform scl
  rw [e1, e2, MeasureTheory.L2.inner_def]
  congr 1
  have hae : (fun x => inner ℂ ((hm.toLp _ : Lp ℂ 2 _) x) ((hm'.toLp _ : Lp ℂ 2 _) x)) =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund]
      fun x => conj (Pser X u hK Dt T x) * Pser X u' hK Dt' T' x := by
    filter_upwards [hm.coeFn_toLp, hm'.coeFn_toLp] with x h1 h2
    rw [h1, h2, RCLike.inner_apply]
    exact mul_comm _ _
  rw [integral_congr_ae hae, integral_conj_mul]
  congr 1
  exact hU.2.2.2.2

theorem entryUnfold_of (hK : X.LevelSubgroupCharacter) (hR : FoldReadyX X)
    (hFB : FundBridge X) (hOK : Formalism.L2.SG.WuDecay.FoldOK X u hK) (hOK' : Formalism.L2.SG.WuDecay.FoldOK X u' hK)
    (hin : InHH X u hK) (hin' : InHH X u' hK) (Dt Dt' : Set X.B.I.GA) (hD : IsReps X u Dt) (hD' : IsReps X u' Dt')
    (R : Set X.B.I.GA) (hRt : IsDoubleTransversal (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u) (Srat X u') R)
    (Fs : X.B.I.GA → Set X.B.I.GA)
    (hFs : ∀ r ∈ R, IsFundamentalDomain (stab (Srat X u) (Srat X u') r) (Fs r) (X.B.I.muA X.B.μf))
    (hDC : DCTerms F0 F0' cs cs' FdN FdN' hK R Fs) :
    EntryUnfold F0 F0' cs cs' FdN FdN' hK Dt Dt' := by
  intro T T'
  rw [kform_unfold FdN FdN' hK hR hFB hOK hOK' hin hin' Dt Dt' hD hD' R hRt Fs hFs T T', hDC T T']

end Unfold

theorem setIntegral_slab (I : Formalism.MainNotions.S.AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsMulLeftInvariant]
    [SigmaFinite (Formalism.L2.SG.ProjRows.muInf I)]
    (K : Set I.Gf) (hK : MeasurableSet K) (Ω : Set I.Ginf) (a : I.Gf) (f : I.GA → ℂ)
    (hf : ∀ y : I.Ginf, ∀ k ∈ K, f (y, a * k) = f (y, a))
    (hint : IntegrableOn f (Ω ×ˢ ((a * ·) '' K)) (I.muA μf)) :
    ∫ x in Ω ×ˢ ((a * ·) '' K), f x ∂(I.muA μf) =
      (μf K).toReal • ∫ y in Ω, f (y, a) ∂(Formalism.L2.SG.ProjRows.muInf I) := by
  have hKa : MeasurableSet ((a * ·) '' K) := (MeasurableEquiv.mulLeft a).measurableSet_image.2 hK
  have hvol : μf ((a * ·) '' K) = μf K := by
    rw [show ((a * ·) '' K) = (fun h => a⁻¹ * h) ⁻¹' K by
      ext z; simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨k, hk, rfl⟩; simpa using hk
      · intro hz; exact ⟨a⁻¹ * z, hz, by group⟩]
    exact measure_preimage_mul μf a⁻¹ K
  have e1 : ∫ x in Ω ×ˢ ((a * ·) '' K), f x ∂(I.muA μf) =
      ∫ y in Ω, ∫ z in (a * ·) '' K, f (y, z) ∂μf ∂(Formalism.L2.SG.ProjRows.muInf I) := by
    unfold Formalism.MainNotions.S.AutInst.muA
    exact setIntegral_prod f hint
  rw [e1, ← integral_smul]
  congr 1
  funext y
  rw [setIntegral_congr_fun hKa (g := fun _ => f (y, a)) ?_, setIntegral_const, measureReal_def, hvol]
  rintro z ⟨k, hk, rfl⟩
  exact hf y k hk

def DCSingle : Prop :=
  ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (Γ S S' : Subgroup G) [Countable Γ], S ≤ Γ → S' ≤ Γ →
  ∀ (D' : Set G), Formalism.L2.SG.FoldBound.IsRightTransversal Γ S' D' →
  ∀ (R : Set G), Formalism.L2.SG.PoincareSeriesSquareIntegrable.IsDoubleTransversal Γ S S' R →
  ∀ (Fs : G → Set G), (∀ r ∈ R, IsFundamentalDomain (Formalism.L2.SG.PoincareSeriesSquareIntegrable.stab S S' r) (Fs r) μ) →
  ∀ (F : Set G), IsFundamentalDomain S F μ →
  ∀ (f g : G → ℂ), Measurable f → Measurable g → (∀ s ∈ S, ∀ y, f (s * y) = f y) →
    (∀ s ∈ S', ∀ y, g (s * y) = g y) →
    (∑' r : R, ∫⁻ x in Fs r, ‖f x‖ₑ * ‖g ((r : G)⁻¹ * x)‖ₑ ∂μ) < ⊤ →
    (∀ x, Summable fun δ : D' => ‖g ((δ : G) * x)‖) →
    IntegrableOn (fun x => f x * conj (∑' δ : D', g ((δ : G) * x))) F μ ∧
      ∑' r : R, ∫ x in Fs r, f x * conj (g ((r : G)⁻¹ * x)) ∂μ =
        ∫ x in F, f x * conj (∑' δ : D', g ((δ : G) * x)) ∂μ

section Slab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)

variable (F0) in

def NOcol (ρ : cs.Cl) : Set X.B.I.Ginf :=
  {y | ∃ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x n ∧ y = x.1 ∧
    n ∈ NLam (cs.lamOf ρ) (lf D F0)}

def slab (ρ : cs.Cl) (Ω : Set X.B.I.Ginf) : Set X.B.I.GA :=
  Ω ×ˢ ((((cs.h ρ : X.B.I.Gf) * X.xu u) * ·) '' X.K2)

variable (F0) in

def SlabFD : Prop :=
  ∀ (FS : Set X.B.I.GA), IsFundamentalDomain (Srat X u) FS (X.B.I.muA X.B.μf) →
  ∀ (Ωs : cs.Cl → Set X.B.I.Ginf), (∀ ρ, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (NOcol F0 cs ρ) (Ωs ρ)) →
  ∀ f : X.B.I.GA → ℂ, Measurable f → (∀ s ∈ Srat X u, ∀ y, f (s * y) = f y) →
    (∀ y, f y ≠ 0 → ∃ n h k, IsDec X u y.2 n h k) → IntegrableOn f FS (X.B.I.muA X.B.μf) →
    (∀ ρ, IntegrableOn f (slab cs ρ (Ωs ρ)) (X.B.I.muA X.B.μf)) ∧
      ∫ x in FS, f x ∂(X.B.I.muA X.B.μf) = ∑ ρ, ∫ x in slab cs ρ (Ωs ρ), f x ∂(X.B.I.muA X.B.μf)

variable (F0 F0') in

def Regroup (hK : X.LevelSubgroupCharacter) (Dt' : Set X.B.I.GA) : Prop :=
  ∀ (Ωs : cs.Cl → Set X.B.I.Ginf), (∀ ρ, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (NOcol F0 cs ρ) (Ωs ρ)) →
  ∀ (T : Cu X u hK) (T' : Cu X u' hK) (ρ : cs.Cl),
    ((scl FdN FdN' (X := X) (u := u) (u' := u') : ℝ) : ℂ) * ((X.volK2 : ℝ) : ℂ) *
        ∫ y in Ωs ρ, conj (Ph X u hK T (y, (cs.h ρ : X.B.I.Gf) * X.xu u)) *
          Pser X u' hK Dt' T' (y, (cs.h ρ : X.B.I.Gf) * X.xu u) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∑ ρ', inner ℂ ((∑' t : GTerm X u u' F0 F0' what₂ rows', blk cs cs' FdN FdN' t ρ ρ') (sharp hK cs' T' ρ'))
        (sharp hK cs T ρ)

end Slab

section SlabAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.PoincareSeriesSquareIntegrable

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)

theorem dcTerms_of [SigmaFinite (Formalism.L2.SG.ProjRows.muInf X.B.I)] (hK : X.LevelSubgroupCharacter) (hKL : X.LevelSubgroupNormalized)
    (hR : FoldReadyX X) (hFB : FundBridge X)
    (hOK : Formalism.L2.SG.WuDecay.FoldOK X u hK) (hOK' : Formalism.L2.SG.WuDecay.FoldOK X u' hK)
    (hin' : InHH X u' hK) (Dt' : Set X.B.I.GA) (hD' : IsReps X u' Dt')
    (R : Set X.B.I.GA) (hRt : IsDoubleTransversal (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u) (Srat X u') R)
    (Fs : X.B.I.GA → Set X.B.I.GA)
    (hFs : ∀ r ∈ R, IsFundamentalDomain (stab (Srat X u) (Srat X u') r) (Fs r) (X.B.I.muA X.B.μf))
    (FS : Set X.B.I.GA) (hFS : IsFundamentalDomain (Srat X u) FS (X.B.I.muA X.B.μf))
    (Ωs : cs.Cl → Set X.B.I.Ginf) (hΩ : ∀ ρ, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (NOcol F0 cs ρ) (Ωs ρ))
    (hWD : PhWellDef X u hK) (hWD' : PhWellDef X u' hK) (hPM : PserMeas X u' hK)
    (hDCS : DCSingle) (hSL : SlabFD F0 cs) (hRG : Regroup F0 F0' cs cs' FdN FdN' hK Dt') :
    DCTerms F0 F0' cs cs' FdN FdN' hK R Fs := by
  intro T T'
  obtain ⟨⟨F, hF⟩, Ω₀, a, hc0, h10, hT⟩ := hOK
  obtain ⟨⟨F', hF'⟩, Ω₀', a', hc0', h10', hT'⟩ := hOK'
  have hΩc : IsCompact (Ω₀ ∪ Ω₀') := hc0.union hc0'
  obtain ⟨Dt0, hDt0⟩ := Formalism.L2.SG.Pf.exists_rightTransversal (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u) inf_le_left
  have hFD := (hT T).1 _ hΩc Set.subset_union_left
  have hFD' := (hT' T').1 _ hΩc Set.subset_union_right
  have hc := @fold_l2_bound_c X.B.I.GA _ _ _ hR.1 hR.2.1 hR.2.2.1 _ hR.2.2.2.1 (X.B.I.muA X.B.μf)
    (@muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar)
  have hU := hc (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u) (Srat X u') hR.2.2.2.2 inf_le_left inf_le_left
    (Ω₀ ∪ Ω₀') hΩc (Or.inl h10) a a' (Ph X u hK T) (Ph X u' hK T') hFD hFD' F F' hF hF'
    ((hT T).2 _ hΩc F hF) ((hT' T').2 _ hΩc F' hF') Dt0 Dt' hDt0 hD' R hRt Fs hFs X.B.fund hFB
  have hfin := hU.2.1
  have hPhM : Measurable (Ph X u hK T) := hFD.1
  have hPhM' : Measurable (Ph X u' hK T') := hFD'.1
  have hinv : ∀ s ∈ Srat X u, ∀ y, Ph X u hK T (s * y) = Ph X u hK T y := hFD.2.1
  have hinv' : ∀ s ∈ Srat X u', ∀ y, Ph X u' hK T' (s * y) = Ph X u' hK T' y := hFD'.2.1
  have hsum' := (hin' T' Dt' hD').1
  have : SecondCountableTopology X.B.I.GA := hR.2.1
  have : BorelSpace X.B.I.GA := hR.2.2.2.1
  have : DiscreteTopology (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) := hR.2.2.2.2
  have : Countable (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) := Formalism.L2.SG.Pf.countable_of_discrete _
  have := @muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar
  have : SigmaFinite (X.B.I.muA X.B.μf) := by unfold Formalism.MainNotions.S.AutInst.muA; infer_instance
  obtain ⟨hIntFS, hEq⟩ := hDCS X.B.I.GA (X.B.I.muA X.B.μf) (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u) (Srat X u')
    inf_le_left inf_le_left Dt' hD' R hRt Fs hFs FS hFS (Ph X u hK T) (Ph X u' hK T') hPhM hPhM' hinv hinv' hfin
    hsum'
  have hPhMall' : PhMeas X u' hK := fun T'' => ((hT' T'').1 Ω₀' hc0' subset_rfl).1
  have hPserM : Measurable (Pser X u' hK Dt' T') := hPM hPhMall' T' Dt' hD' hsum'
  set f : X.B.I.GA → ℂ := fun x => conj (Ph X u hK T x) * Pser X u' hK Dt' T' x with hfdef
  have e2 : conj (∫ x in FS, Ph X u hK T x * conj (∑' δ : Dt', Ph X u' hK T' ((δ : X.B.I.GA) * x))
      ∂(X.B.I.muA X.B.μf)) = ∫ x in FS, f x ∂(X.B.I.muA X.B.μf) := by
    rw [← integral_conj]
    congr 1
    funext x
    simp [f, map_mul, Pser, poinc]
  have hfm : Measurable f := (Complex.continuous_conj.measurable.comp hPhM).mul hPserM
  have hfinv : ∀ s ∈ Srat X u, ∀ y, f (s * y) = f y := by
    intro s hs y
    simp only [f]
    rw [hinv s hs y]
    congr 1
    exact poinc_left_inv (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u') Dt' hD' (Ph X u' hK T') hinv' s
      (Subgroup.mem_inf.1 hs).1 y
  have hfsupp : ∀ y, f y ≠ 0 → ∃ n h k, IsDec X u y.2 n h k := by
    intro y hy
    by_contra hn
    apply hy
    simp only [f]
    unfold Ph
    rw [dif_neg hn]
    simp
  have hfeq : f = fun x => conj (Ph X u hK T x * conj (∑' δ : Dt', Ph X u' hK T' ((δ : X.B.I.GA) * x))) := by
    funext x
    simp [f, map_mul, Pser, poinc]
  have hfint : IntegrableOn f FS (X.B.I.muA X.B.μf) := by
    rw [hfeq]
    have h1 := (Complex.conjCLE.toContinuousLinearMap).integrable_comp hIntFS
    simp only [map_mul, Complex.conj_conj] at h1 ⊢
    simp at h1
    exact h1
  obtain ⟨hIS, hSum⟩ := hSL FS hFS Ωs hΩ f hfm hfinv hfsupp hfint
  have hKm := Formalism.L2.SG.PoincareInHH.Cut.level_subgroup_measurable X hK hKL
  rw [hEq, e2, hSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hslab : ∀ (y : X.B.I.Ginf), ∀ k ∈ X.K2,
      f (y, (cs.h ρ : X.B.I.Gf) * X.xu u * k) = f (y, (cs.h ρ : X.B.I.Gf) * X.xu u) := by
    intro y k hk
    have hyk : ((y, (cs.h ρ : X.B.I.Gf) * X.xu u * k) : X.B.I.GA) =
        (y, (cs.h ρ : X.B.I.Gf) * X.xu u) * (1, k) := by
      simp
    have hn : conj (X.chi2 k) * X.chi2 k = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hK.2.2.2.2 k hk]
      simp
    simp only [f]
    rw [hyk, ph_right_K X u hK hWD T _ k hk, pser_right_K X u' hK hWD' T' Dt' _ k hk, map_mul]
    linear_combination (conj (Ph X u hK T (y, (cs.h ρ : X.B.I.Gf) * X.xu u)) *
      Pser X u' hK Dt' T' (y, (cs.h ρ : X.B.I.Gf) * X.xu u)) * hn
  have hs := setIntegral_slab X.B.I X.B.μf X.K2 hKm (Ωs ρ) ((cs.h ρ : X.B.I.Gf) * X.xu u) f hslab (hIS ρ)
  rw [← hRG Ωs hΩ T T' ρ]
  unfold slab
  rw [hs, Complex.real_smul]
  unfold Formalism.L2.SG.HidaSetting.HidaSetting.volK2
  ring

end SlabAsm

section Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.PoincareSeriesSquareIntegrable

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (TR : TypedRed X) (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)

theorem kExpansion_of_steps [SigmaFinite (Formalism.L2.SG.ProjRows.muInf X.B.I)] (hK : X.LevelSubgroupCharacter) (hKL : X.LevelSubgroupNormalized)
    (hR : FoldReadyX X) (hFB : FundBridge X)
    (hOK : Formalism.L2.SG.WuDecay.FoldOK X u hK) (hOK' : Formalism.L2.SG.WuDecay.FoldOK X u' hK)
    (hin : InHH X u hK) (hin' : InHH X u' hK) (Dt Dt' : Set X.B.I.GA) (hD : IsReps X u Dt) (hD' : IsReps X u' Dt')
    (R : Set X.B.I.GA) (hRt : IsDoubleTransversal (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u) (Srat X u') R)
    (Fs : X.B.I.GA → Set X.B.I.GA)
    (hFs : ∀ r ∈ R, IsFundamentalDomain (stab (Srat X u) (Srat X u') r) (Fs r) (X.B.I.muA X.B.μf))
    (FS : Set X.B.I.GA) (hFS : IsFundamentalDomain (Srat X u) FS (X.B.I.muA X.B.μf))
    (Ωs : cs.Cl → Set X.B.I.Ginf) (hΩ : ∀ ρ, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (NOcol F0 cs ρ) (Ωs ρ))
    (hWD : PhWellDef X u hK) (hWD' : PhWellDef X u' hK) (hPM : PserMeas X u' hK)
    (hA : AbsConvT F0 F0' TR cs cs' FdN FdN')
    (hDCS : DCSingle) (hSL : SlabFD F0 cs) (hRG : Regroup F0 F0' cs cs' FdN FdN' hK Dt') :
    KExpansion F0 F0' cs cs' FdN FdN' hK Dt Dt' := by
  exact kExpansion_of_abs TR cs cs' FdN FdN' hK Dt Dt' hA
    (entryUnfold_of cs cs' FdN FdN' hK hR hFB hOK hOK' hin hin' Dt Dt' hD hD' R hRt Fs hFs
      (dcTerms_of cs cs' FdN FdN' hK hKL hR hFB hOK hOK' hin' Dt' hD' R hRt Fs hFs FS hFS Ωs hΩ
        hWD hWD' hPM hDCS hSL hRG))

end Chain

end Formalism.L2.SG.TermOp.KExpCut
