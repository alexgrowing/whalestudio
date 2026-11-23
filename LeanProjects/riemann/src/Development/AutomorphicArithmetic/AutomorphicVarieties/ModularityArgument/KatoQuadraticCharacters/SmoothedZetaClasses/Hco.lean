import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmValuationNewformCongruence
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Thdiam
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaSystemFixedExponent
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenfunctionalZeroProjection
import Development.AbelianVarietyTheory.Definitions.Foundations.PieceEqPieceT
import Development.AbelianVarietyTheory.Definitions.Foundations.HtCoLOfEq
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleHodgeTateZetaClassParams
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleNewformZetaData
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFROfIsLamF
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Definitions.Foundations.ActWBOfInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPrimitiveRootEOmLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFunctionalOddWeightOddPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndepende
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsThBActSgDDiamIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombination
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeDiamondAction
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFR2

noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.KZ GlobalTheory.Ord2 GlobalTheory.K4

namespace GlobalTheory.LambdaValuationPowers

open ZetaCoef

theorem _root_.UpperTheory.V.Z.Kato.K5.hco : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], l ≠ 2 →
  (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (A : ValuationSubring Ω) (j : Ω →+* Qbar l), OverL l A → (∀ z : Ω, z ∈ A ↔ ‖j z‖ ≤ 1) →
  ∀ (N : ℕ) [NeZero N], ¬ l ∣ N → ∀ (c d e : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), 1 ≤ e →
  ∀ (ι : Qbar l ≃+* ℂ) (gN : Newform (2 * e + 1)) (W : R2 Ω l) (pr : X.Fn l → Fin 2 → Qbar l) (ψ : ZMod l → Qbar l) (cf : Coef l),
  ∀ (α : Qbar l), GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm α →
  (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l 1 s = 1 → rhoK W e ψ s 1 0 = 0 ∧ rhoK W e ψ s 1 1 = 1) →
  ∀ (χ : ℕ → ℤ_[l]), (∀ δ : ℕ, Nat.Coprime δ N → IsUnit (χ δ)) → (∀ a b : ℕ, χ (a * b) = χ a * χ b) →
    (∀ a b : ℕ, a % N = b % N → χ a = χ b) →
  ∀ (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), GlobalTheory.KummerEisensteinGalois.IsLamFR2 X A N (2 * e - 1) χ j pr cf lam →
  ∀ (c₀ : ℕ), ∃ (c' : ℕ) (κ₀ : Qbar l) (per : ℕ → Qbar l), κ₀ ≠ 0 ∧ (∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n)) ∧ ∀ (x : ZMod N),
  GlobalTheory.K4.AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf →
  ∀ (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
  IsZetaSystemFixedExponent X l pr W e ψ N x c d (2 * e + 1) gm cf c₀ Y →
  ∀ m : ℕ, 1 ≤ m → ∀ (y : (ZMod (l ^ m))ˣ) (β : ℕ) (t : ℤ),
    (β : ZMod (l ^ m)) = (y : ZMod (l ^ m)) → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] →
    GlobalTheory.LambdaValuationPowers.HTCoL A cf j (fun r s y' => Y r s y' 1) m c' y
      ((per m)⁻¹ * (l : Qbar l) ^ c₀ * κ₀ * ∑ δ : (ZMod N)ˣ,
        (algebraMap ℚ_[l] (Qbar l) ((χ (δ : ZMod N).val : ℤ_[l]) : ℚ_[l]))⁻¹ *
        lam (fun i => (l : Qbar l) ^ m * j (GlobalTheory.KummerEisensteinGalois.toQ (l ^ m)
          (GlobalTheory.KummerEisensteinGalois.pieceT N l m m (2 * e + 1) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ)
            ((x.val : ℤ) * t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0) (t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0)
            (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β)
            ((GlobalTheory.KummerEisensteinGalois.unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i))) := by
  intro Ω _ _ _ ε X l _ hl2 hφ A j hA hj N _ hlN c d e gm he ι gN W pr ψ cf α hadm hIne χ hχu hχmul hχper lam hlam c₀
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have halg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  obtain ⟨h5, hlcop, hgm, hα, hU⟩ := hadm
  obtain ⟨hdχ, hfin, hfixL, cL, per, hper, hLF⟩ := hlam
  obtain ⟨S, hS⟩ := GlobalTheory.KummerEisensteinGalois.FinSupp.exists_sum hfin
  obtain ⟨k, hk⟩ := GlobalTheory.KummerEisensteinGalois.exists_le_l_pow l (∑ i ∈ S, ‖lam (Pi.single i 1)‖)
  have hLk : ∀ i ∈ S, ‖lam (Pi.single i 1)‖ ≤ (l : ℝ) ^ k := fun i hi =>
    le_trans (Finset.single_le_sum (f := fun i => ‖lam (Pi.single i 1)‖) (fun _ _ => norm_nonneg _) hi) hk
  set M : Qbar l := ((Fintype.card (ZMod N)ˣ : ℕ) : Qbar l) with hM
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact_mod_cast Fintype.card_ne_zero
  obtain ⟨v, hv⟩ : ∃ v : ℕ, ‖(l : Qbar l) ^ v‖ ≤ ‖M‖ := by
    obtain ⟨v, hv⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hM0) (GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one (l := l))
    exact ⟨v, by rw [norm_pow]; exact hv.le⟩
  by_cases hex : ∃ x, GlobalTheory.K4.AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf
  swap
  · refine ⟨0, 1, per, one_ne_zero, fun n => ⟨(hper n).1, (hper n).2.1⟩, fun x hx => ?_⟩
    exact absurd ⟨x, hx⟩ hex
  obtain ⟨x₀, hx₀⟩ := hex
  obtain ⟨c₁, κ', hκ', H⟩ := UpperTheory.Kd.L.thdiam Ω ε X l hl2 hφ A j hA hj N hlN c d e gm hx₀.1 hx₀.2.1 hx₀.2.2.1 hx₀.2.2.2.1 he hx₀.2.2.2.2.2.2.2.2.2.1 hx₀.2.2.2.2.2.2.2.2.2.2.1 pr α ⟨h5, hlcop, hgm, hα, hU⟩
  refine ⟨c₁ + k + v, κ' / M, per, div_ne_zero hκ' hM0, fun n => ⟨(hper n).1, (hper n).2.1⟩, fun x hx3 Y hY m hm y β t hβy hβ1 hmt => ?_⟩
  obtain ⟨hc1, hd1, hcc, hdc, hpradd, hprsmul, hprO, hprgal, -, -, -, -⟩ := hx3
  have hw : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  have hodd : Odd (2 * e - 1) := ⟨e - 1, by omega⟩
  have hcopδ : ∀ δ : (ZMod N)ˣ, Nat.Coprime (δ : ZMod N).val N := fun δ => ZMod.val_coe_unit_coprime δ
  set u : (ZMod N)ˣ → ℤ_[l] := fun δ => (((hχu _ (hcopδ δ)).unit⁻¹ : (ℤ_[l])ˣ) : ℤ_[l]) with hu
  have huχ : ∀ δ, u δ * χ (δ : ZMod N).val = 1 := fun δ => (hχu _ (hcopδ δ)).val_inv_mul
  have hualg : ∀ δ, algebraMap ℤ_[l] (Qbar l) (u δ) = (algebraMap ℚ_[l] (Qbar l) ((χ (δ : ZMod N).val : ℤ_[l]) : ℚ_[l]))⁻¹ := by
    intro δ
    have h1 : algebraMap ℚ_[l] (Qbar l) ((u δ : ℤ_[l]) : ℚ_[l]) * algebraMap ℚ_[l] (Qbar l) ((χ (δ : ZMod N).val : ℤ_[l]) : ℚ_[l]) = 1 := by
      rw [← map_mul, ← PadicInt.coe_mul, huχ δ, PadicInt.coe_one, map_one]
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l) (u δ)]
    exact eq_inv_of_mul_eq_one_left h1
  set Qf : (ZMod N)ˣ → ℕ → Qbar l := fun δ i => j (GlobalTheory.KummerEisensteinGalois.toQ (l ^ m)
          (GlobalTheory.KummerEisensteinGalois.pieceT N l m m (2 * e + 1) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ)
            ((x.val : ℤ) * t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0) (t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0)
            (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β)
            ((GlobalTheory.KummerEisensteinGalois.unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i) with hQf
  set E : Qbar l := (l : Qbar l) ^ c₀ * κ' * ∑ δ : (ZMod N)ˣ, algebraMap ℤ_[l] (Qbar l) (u δ) * lam (fun i => (l : Qbar l) ^ m * Qf δ i) with hE
  obtain ⟨kE, hkE⟩ := GlobalTheory.KummerEisensteinGalois.exists_le_l_pow l ‖E‖
  obtain ⟨bB, hbB, b, hbO, hYb⟩ := hY m (m + kE + cL)
  rw [hw] at hbB
  choose g hgA hg using fun δ => H x m (m + kE + cL) c₀ hm (by omega) bB hbB y δ
  apply GlobalTheory.LambdaValuationPowers.ZetaCoef.htCoL_of_fintype (ι := ↥S × (ZMod N)ˣ)
    (fun p => (l : Qbar l) ^ v / M * (per (m + kE + cL))⁻¹ * ((l : Qbar l) ^ k * lam (Pi.single (p.1 : ℕ) 1)) * algebraMap ℤ_[l] (Qbar l) (u p.2))
    (fun p => (g p.2).coeff ((p.1 : ℕ) : ℚ))
  · have hfm : ∀ a b : Qbar l, FixIc cf a → FixIc cf b → FixIc cf (a * b) := by
      intro a b ha hb σ h1 h2
      rw [map_mul, ha σ h1 h2, hb σ h1 h2]
    have hfi : ∀ a : Qbar l, FixIc cf a → FixIc cf a⁻¹ := by
      intro a ha σ h1 h2
      rw [map_inv₀, ha σ h1 h2]
    have hfn : ∀ q : ℕ, FixIc cf ((l : Qbar l) ^ q) := by
      intro q σ _ _
      rw [map_pow, map_natCast]
    have hfM : FixIc cf M := by
      intro σ _ _
      exact map_natCast σ _
    have hfu : ∀ a : ℤ_[l], FixIc cf (algebraMap ℤ_[l] (Qbar l) a) := by
      intro a σ _ _
      exact (σ.restrictScalars ℤ_[l]).commutes a
    intro p
    refine ⟨?_, ?_, (hj _).1 (hgA p.2 _)⟩
    · have h1 : ‖(l : Qbar l) ^ v / M‖ ≤ 1 := by
        rw [norm_div]
        exact div_le_one_of_le₀ hv (norm_nonneg _)
      have h2 : ‖(per (m + kE + cL))⁻¹‖ ≤ 1 := by
        rw [norm_inv, (hper _).1, inv_one]
      have h3 : ‖(l : Qbar l) ^ k * lam (Pi.single (p.1 : ℕ) 1)‖ ≤ 1 :=
        GlobalTheory.LambdaValuationPowers.ZetaCoef.norm_pow_mul_le (hLk _ p.1.2)
      have h4 := GlobalTheory.LambdaValuationPowers.ZetaCoef.norm_algebraMap_le (l := l) (u p.2)
      rw [norm_mul, norm_mul, norm_mul]
      exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ h1 (norm_nonneg _) h2) (norm_nonneg _) h3) (norm_nonneg _) h4
    · refine hfm _ _ (hfm _ _ (hfm _ _ ?_ (hfi _ (hper _).2.2)) (hfm _ _ (hfn k) (hfixL _))) (hfu _)
      rw [div_eq_mul_inv]
      exact hfm _ _ (hfn v) (hfi _ hfM)
  intro s hs hsm
  set n := m + kE + cL with hn
  have hsumle : ∀ {ι' : Type} (T : Finset ι') (f : ι' → Qbar l) (r : ℝ), 0 ≤ r → (∀ i ∈ T, ‖f i‖ ≤ r) → ‖∑ i ∈ T, f i‖ ≤ r :=
    fun T f r hr h => IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr h
  have hcgsum : ∀ {ι' : Type} (T : Finset ι') (a b : ι' → Qbar l) (q : ℕ), (∀ i ∈ T, Cg q (a i) (b i)) →
      Cg q (∑ i ∈ T, a i) (∑ i ∈ T, b i) := by
    intro ι' T a b q h
    unfold Cg
    rw [← Finset.sum_sub_distrib]
    exact hsumle T _ _ (norm_nonneg _) h
  have hcgmul : ∀ (q : ℕ) (r a b : Qbar l), ‖r‖ ≤ 1 → Cg q a b → Cg q (r * a) (r * b) := by
    intro q r a b hr h
    unfold Cg at *
    rw [← mul_sub, norm_mul]
    exact le_trans (mul_le_of_le_one_left (norm_nonneg _) hr) h
  have hcgtrans : ∀ (q : ℕ) (a b c' : Qbar l), Cg q a b → Cg q b c' → Cg q a c' := by
    intro q a b c' h1 h2
    unfold Cg at *
    have : a - c' = (a - b) + (b - c') := by ring
    rw [this]
    exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le h1 h2)
  have hnpow : ∀ q : ℕ, ‖(l : Qbar l) ^ q‖ ≤ 1 := fun q => by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one (l := l)).le
  have hlnon : (l : Ω) ∈ A.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro hmem
    have h1 := (hj _).1 hmem
    rw [map_inv₀, map_natCast, norm_inv] at h1
    have h2 := GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one (l := l)
    have h3 : 0 < ‖(l : Qbar l)‖ := norm_pos_iff.2 GlobalTheory.LambdaValuationPowers.natCast_ne_zero
    have h4 : 1 < ‖(l : Qbar l)‖⁻¹ := one_lt_inv₀ h3 |>.2 h2
    linarith
  have hs1 := GlobalTheory.LambdaValuationPowers.ZetaCoef.cycMod_one_of hm hsm
  have hrho := hIne s hs hs1
  have hgal : ∀ (s' : Gal(Ω/ℚ)), ∀ b' ∈ X.B N l (2 * e - 1), (X.galB l s') b' ∈ X.B N l (2 * e - 1) :=
    GlobalTheory.KZ.StabGal.galB_mem_B ε X ε.injective hφ N l (2 * e - 1) hl2 h5 hlcop.symm hodd
  obtain ⟨hfB, hfpr⟩ := GlobalTheory.LambdaValuationPowers.ZetaCoef.pushB_spec X (N := N) (2 * e - 1) n m pr W e ψ hgal hpradd hprgal bB
    (fun σ hσ => (hbB σ hσ).1) s y
  set f := GlobalTheory.LambdaValuationPowers.ZetaCoef.pushB X l n m N bB s y with hf
  have hdB : ∀ δ : (ZMod N)ˣ, X.diam N l (δ : ZMod N).val f ∈ X.B N l (2 * e - 1) := fun δ =>
    GlobalTheory.CyclotomicQExpansion.ThnEx.diam_B X N l (2 * e - 1) _ (NeZero.pos N) hlcop.symm (hcopδ δ) f hfB
  have hφ' : ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs := by
    obtain ⟨φ, h1, h2⟩ := hφ
    exact ⟨φ, h2, h1⟩
  choose φδ hφδ _ using fun δ : (ZMod N)ˣ =>
    GlobalTheory.T.exists_cuspFunctional_oddWeight_oddPrime Ω ε X A N l halg hφ' hl2 hlN h5 hlnon n (2 * e - 1) hodd _ (hdB δ)
  obtain ⟨Φ, hΦ, hΦc⟩ := GlobalTheory.LambdaValuationPowers.ZetaCoef.exists_isThB_sum X hj hlnon Finset.univ Finset.univ_nonempty u
    (fun δ => X.diam N l (δ : ZMod N).val f) φδ hdB hφδ
  have hInChi := GlobalTheory.LambdaValuationPowers.ZetaCoef.inChi_avg X (N := N) hlcop.symm (w := 2 * e - 1) (χ := χ)
    (fun a b k _ _ hk => by rw [← hχmul]; exact hχper _ _ hk) u huχ hfB
  have hF := hLF n (by omega) _ hInChi Φ hΦ
  have hprsum : pr (∑ δ : (ZMod N)ˣ, u δ • X.diam N l (δ : ZMod N).val f) =
      ∑ δ : (ZMod N)ˣ, pr (u δ • X.diam N l (δ : ZMod N).val f) :=
    map_sum (AddMonoidHom.mk' pr hpradd) _ _
  have hpr1 : pr (∑ δ : (ZMod N)ˣ, u δ • X.diam N l (δ : ZMod N).val f) 1 = M * pr f 1 := by
    rw [hprsum, Finset.sum_apply]
    have h1 : ∀ δ : (ZMod N)ˣ, pr (u δ • X.diam N l (δ : ZMod N).val f) 1 = pr f 1 := by
      intro δ
      rw [hprsmul, hdχ _ (hcopδ δ) f hfB, smul_smul, Pi.smul_apply, smul_eq_mul, ← map_mul, ← PadicInt.coe_mul,
        huχ, PadicInt.coe_one, map_one, one_mul]
    simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hM]
  obtain ⟨tt, htt, v', u', hv', hu', htteq⟩ := GlobalTheory.LambdaValuationPowers.ZetaCoef.exists_isLamG ε hl2 hm (by omega : m ≤ n) hsm
  have hT : ∀ (δ : (ZMod N)ˣ) (i : ℕ), Cg n ((l : Qbar l) ^ c₁ * GlobalTheory.KummerEisensteinGalois.seqN 1 j (φδ δ) i)
      ((l : Qbar l) ^ c₁ * ((l : Qbar l) ^ c₀ * κ' * (tt.val : Qbar l) * (l : Qbar l) ^ m * Qf δ i) +
        (j (s ((g δ).coeff (i : ℚ))) - j ((g δ).coeff (i : ℚ)))) :=
    fun δ i => hg δ s hs hsm (φδ δ) (hφδ δ) tt htt β t hβy hβ1 hmt i
  have hY1 : Cg n (Y m s y 1) (pr f 1) := by
    have h := hYb s y 1
    rw [hsm, inv_one, mul_one, ← hfpr] at h
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hrho.1, hrho.2, Matrix.vecHead, Matrix.vecTail] using h
  set Cs : Qbar l := ∑ i ∈ S, ∑ δ : (ZMod N)ˣ, ((l : Qbar l) ^ k * lam (Pi.single i 1)) * algebraMap ℤ_[l] (Qbar l) (u δ) *
      (j (s ((g δ).coeff (i : ℚ))) - j ((g δ).coeff (i : ℚ))) with hCs
  have hlm : ‖(l : Qbar l) ^ m‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one (l := l)) (by omega)
  have hMle : ‖M‖ ≤ 1 := by
    have := GlobalTheory.LambdaValuationPowers.ZetaCoef.norm_algebraMap_le (l := l) ((Fintype.card (ZMod N)ˣ : ℕ) : ℤ_[l])
    simpa [hM] using this
  have hsA : ∀ w ∈ A, s w ∈ A := by
    intro w hw
    have h1 := hs.2 w ((A.valuation_le_one_iff w).2 hw)
    have h2 : s w - w ∈ A := (A.valuation_le_one_iff _).1 h1.le
    simpa using A.add_mem _ _ h2 hw
  have hDle : ∀ (δ : (ZMod N)ˣ) (i : ℕ), ‖j (s ((g δ).coeff (i : ℚ))) - j ((g δ).coeff (i : ℚ))‖ ≤ 1 := by
    intro δ i
    rw [← map_sub]
    exact (hj _).1 (A.sub_mem (hsA _ (hgA δ _)) (hgA δ _))
  have hCle : ‖Cs‖ ≤ 1 := by
    refine hsumle _ _ _ zero_le_one fun i hi => hsumle _ _ _ zero_le_one fun δ _ => ?_
    rw [norm_mul, norm_mul]
    exact mul_le_one₀ (mul_le_one₀ (GlobalTheory.LambdaValuationPowers.ZetaCoef.norm_pow_mul_le (hLk i hi)) (norm_nonneg _)
      (GlobalTheory.LambdaValuationPowers.ZetaCoef.norm_algebraMap_le _)) (norm_nonneg _) (hDle δ i)
  have hPle : ‖M * pr f 1‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ hMle (norm_nonneg _) (GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (hprO f hfB 1))
  have hYP : ‖M * Y m s y 1 - M * pr f 1‖ ≤ ‖(l : Qbar l) ^ m‖ :=
    hcgmul m M _ _ hMle (GlobalTheory.KummerEisensteinGalois.cg_mono (by omega) hY1)
  have hFP : ‖lam (GlobalTheory.KummerEisensteinGalois.seqN 1 j Φ) - per n * (M * pr f 1)‖ ≤ ‖(l : Qbar l) ^ m‖ := by
    have := GlobalTheory.KummerEisensteinGalois.cg_mono (by omega : m ≤ n - cL) hF
    rw [hpr1] at this
    exact this
  have hpp : ‖per n - per m‖ ≤ ‖(l : Qbar l) ^ m‖ :=
    GlobalTheory.LambdaValuationPowers.ZetaCoef.cg_per (fun q => (hper q).2.1) (by omega : m ≤ n)
  have hEν : ‖E * (l : Qbar l) ^ n‖ ≤ ‖(l : Qbar l) ^ m‖ := by
    have h1 := GlobalTheory.LambdaValuationPowers.ZetaCoef.norm_pow_mul_le hkE
    have h2 : E * (l : Qbar l) ^ n = ((l : Qbar l) ^ kE * E) * (l : Qbar l) ^ (m + cL) := by
      rw [hn]
      ring
    rw [h2, norm_mul]
    refine le_trans (mul_le_of_le_one_left (norm_nonneg _) h1) ?_
    rw [norm_pow, norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) (GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one (l := l)).le (by omega)
  have hLc : ‖(l : Qbar l) ^ c₁ * (l : Qbar l) ^ k * lam (GlobalTheory.KummerEisensteinGalois.seqN 1 j Φ) -
      ((l : Qbar l) ^ c₁ * (l : Qbar l) ^ k * (E * (tt.val : Qbar l)) + Cs)‖ ≤ ‖(l : Qbar l) ^ m‖ := by
    have hl : ∀ δ : (ZMod N)ˣ, lam (fun i => (l : Qbar l) ^ m * Qf δ i) =
        ∑ i ∈ S, lam (Pi.single i 1) * ((l : Qbar l) ^ m * Qf δ i) := fun δ => hS _
    have h1 : (l : Qbar l) ^ c₁ * (l : Qbar l) ^ k * (E * (tt.val : Qbar l)) =
        ∑ i ∈ S, ∑ δ : (ZMod N)ˣ, ((l : Qbar l) ^ k * lam (Pi.single i 1)) * algebraMap ℤ_[l] (Qbar l) (u δ) *
          ((l : Qbar l) ^ c₁ * ((l : Qbar l) ^ c₀ * κ' * (tt.val : Qbar l) * (l : Qbar l) ^ m * Qf δ i)) := by
      rw [hE, Finset.sum_congr rfl (fun δ _ => by rw [hl δ])]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    have hR : ∑ i ∈ S, ((l : Qbar l) ^ k * lam (Pi.single i 1)) * ∑ δ : (ZMod N)ˣ, algebraMap ℤ_[l] (Qbar l) (u δ) *
        ((l : Qbar l) ^ c₁ * ((l : Qbar l) ^ c₀ * κ' * (tt.val : Qbar l) * (l : Qbar l) ^ m * Qf δ i) +
          (j (s ((g δ).coeff (i : ℚ))) - j ((g δ).coeff (i : ℚ)))) =
        (l : Qbar l) ^ c₁ * (l : Qbar l) ^ k * (E * (tt.val : Qbar l)) + Cs := by
      rw [h1, hCs, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun δ _ => ?_
      ring
    have hL : (l : Qbar l) ^ c₁ * (l : Qbar l) ^ k * lam (GlobalTheory.KummerEisensteinGalois.seqN 1 j Φ) =
        ∑ i ∈ S, ((l : Qbar l) ^ k * lam (Pi.single i 1)) * ((l : Qbar l) ^ c₁ * GlobalTheory.KummerEisensteinGalois.seqN 1 j Φ i) := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hcg : Cg n ((l : Qbar l) ^ c₁ * (l : Qbar l) ^ k * lam (GlobalTheory.KummerEisensteinGalois.seqN 1 j Φ))
        ((l : Qbar l) ^ c₁ * (l : Qbar l) ^ k * (E * (tt.val : Qbar l)) + Cs) := by
      rw [hL, ← hR]
      refine hcgsum _ _ _ n fun i hi => hcgmul n _ _ _ (GlobalTheory.LambdaValuationPowers.ZetaCoef.norm_pow_mul_le (hLk i hi)) ?_
      have h2 : Cg n ((l : Qbar l) ^ c₁ * GlobalTheory.KummerEisensteinGalois.seqN 1 j Φ i)
          ((l : Qbar l) ^ c₁ * ∑ δ : (ZMod N)ˣ, algebraMap ℤ_[l] (Qbar l) (u δ) * j ((φδ δ).coeff ((i : ℚ) / ((1 : ℕ) : ℚ)))) :=
        hcgmul n _ _ _ (hnpow c₁) (hΦc _)
      refine hcgtrans n _ _ _ h2 ?_
      rw [Finset.mul_sum]
      refine hcgsum _ _ _ n fun δ _ => ?_
      have h3 := hcgmul n (algebraMap ℤ_[l] (Qbar l) (u δ)) _ _ (GlobalTheory.LambdaValuationPowers.ZetaCoef.norm_algebraMap_le _) (hT δ i)
      have h4 : (l : Qbar l) ^ c₁ * (algebraMap ℤ_[l] (Qbar l) (u δ) * j ((φδ δ).coeff ((i : ℚ) / ((1 : ℕ) : ℚ)))) =
          algebraMap ℤ_[l] (Qbar l) (u δ) * ((l : Qbar l) ^ c₁ * GlobalTheory.KummerEisensteinGalois.seqN 1 j (φδ δ) i) := by
        unfold GlobalTheory.KummerEisensteinGalois.seqN
        ring
      rw [h4]
      exact h3
    exact GlobalTheory.KummerEisensteinGalois.cg_mono (by omega) hcg
  have hch := GlobalTheory.LambdaValuationPowers.ZetaCoef.chain (l := l) (Y := M * Y m s y 1) (P := M * pr f 1) (F := lam (GlobalTheory.KummerEisensteinGalois.seqN 1 j Φ))
    (pn := per n) (pm := per m) (E := E) (t := (tt.val : Qbar l)) (a := lamv l m s) (v := v') (u := u') (C := Cs)
    (lc := (l : Qbar l) ^ c₁ * (l : Qbar l) ^ k) (μ := (l : Qbar l) ^ m) (ν := (l : Qbar l) ^ n)
    hlm (by rw [← pow_add]; exact hnpow _) hPle hCle hv' hu' (hper n).1 (hper m).1 htteq hYP hFP hLc hpp hEν
  have hvM : ‖(l : Qbar l) ^ v / M‖ ≤ 1 := by
    rw [norm_div]
    exact div_le_one_of_le₀ hv (norm_nonneg _)
  have hsumeq : ∑ p : ↥S × (ZMod N)ˣ, (l : Qbar l) ^ v / M * (per n)⁻¹ * ((l : Qbar l) ^ k * lam (Pi.single (p.1 : ℕ) 1)) *
      algebraMap ℤ_[l] (Qbar l) (u p.2) * (j (s ((g p.2).coeff ((p.1 : ℕ) : ℚ))) - j ((g p.2).coeff ((p.1 : ℕ) : ℚ))) =
      (l : Qbar l) ^ v / M * (per n)⁻¹ * Cs := by
    rw [Fintype.sum_prod_type, hCs, Finset.mul_sum, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    ring
  have hsumχ : ∑ δ : (ZMod N)ˣ, (algebraMap ℚ_[l] (Qbar l) ((χ (δ : ZMod N).val : ℤ_[l]) : ℚ_[l]))⁻¹ *
      lam (fun i => (l : Qbar l) ^ m * Qf δ i) =
      ∑ δ : (ZMod N)ˣ, algebraMap ℤ_[l] (Qbar l) (u δ) * lam (fun i => (l : Qbar l) ^ m * Qf δ i) := by
    simp only [hualg]
  unfold Cg
  rw [hsumeq, hsumχ]
  refine le_trans (le_of_eq ?_) (le_trans (mul_le_of_le_one_left (norm_nonneg _) hvM) hch)
  rw [← norm_mul]
  congr 1
  rw [hE]
  field_simp
  ring

end GlobalTheory.LambdaValuationPowers
