import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Formalism.SatakeDualWeyl.StatementE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaHalfMulUnrTorus
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory NumberField IsDedekindDomain

noncomputable section
namespace GlobalTheory.SmGL.SphCompletion

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in
private theorem valuation_le_one_iff_adicValuation_le_one (x : v.adicCompletion F) :
    letI := _root_.GlobalTheory.LocalData.complRel v
    (valuation (v.adicCompletion F)) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  have : Valuation.Compatible
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v).le_one_iff_le_one

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in
private theorem residueFieldCard_adicCompletion_lemma :
    letI := _root_.GlobalTheory.LocalData.complRel v
    haveI := _root_.GlobalTheory.LocalData.isLocalField v
    _root_.GlobalTheory.SplitWeil.resCard (v.adicCompletion F) = _root_.Formalism.UG.qV F v := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  have hmem : ∀ x : v.adicCompletion F,
      x ∈ 𝒪[v.adicCompletion F] ↔ x ∈ v.adicCompletionIntegers F := fun x => by
    simpa [Valuation.mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers] using
      valuation_le_one_iff_adicValuation_le_one v x
  let e : 𝒪[v.adicCompletion F] ≃+* v.adicCompletionIntegers F :=
    { toFun := fun x => ⟨x, (hmem x).1 x.2⟩
      invFun := fun x => ⟨x, (hmem x).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  unfold _root_.GlobalTheory.SplitWeil.resCard
  rw [← _root_.Formalism.UG.P.tjcosets_card_residue v]
  exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in

theorem _root_.GlobalTheory.SmGL.SphCompletion.ord_completion (x : (v.adicCompletion F)ˣ) :
    letI := _root_.GlobalTheory.LocalData.complRel v
    haveI := _root_.GlobalTheory.LocalData.isLocalField v
    _root_.GlobalTheory.SmGL.ord (v.adicCompletion F) x =
      -WithZero.log (Valued.v (x : v.adicCompletion F)) := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  have h := _root_.GlobalTheory.LGrp.BorelCompletion.nabs_completion v x
  rw [_root_.GlobalTheory.LGrp.nabs_eq_zpow, residueFieldCard_adicCompletion_lemma] at h
  have hq : (1 : ℝ) < _root_.Formalism.UG.qV F v := by
    rw [← residueFieldCard_adicCompletion_lemma v]
    exact_mod_cast _root_.GlobalTheory.SplitWeil.one_lt_resCard _
  have := zpow_right_injective₀ (by linarith) hq.ne' h
  omega

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in

theorem _root_.GlobalTheory.SmGL.SphCompletion.KO_completion (n : ℕ) :
    letI := _root_.GlobalTheory.LocalData.complRel v
    haveI := _root_.GlobalTheory.LocalData.isLocalField v
    _root_.GlobalTheory.SplitWeil.KO (v.adicCompletion F) (Fin n) = _root_.Formalism.UG.GLint (Fin n) (_root_.Formalism.UG.Ov F v) := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  haveI := _root_.Formalism.UG.P.tjcosets_isLocalRing v
  ext g
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff, _root_.Formalism.UG.P.tjcosets_mem_K_iff]
  simp only [Valuation.mem_integer_iff, _root_.Formalism.UG.P.cartan_mem_Ov, valuation_le_one_iff_adicValuation_le_one]

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in
private theorem natCast_zpow_neg_cpow_eq_cpow_mul (q : ℕ) (m : ℤ) (n : ℕ) (i : Fin n) :
    (((q : ℝ) ^ (-m) : ℝ) : ℂ) ^ ((((n : ℤ) - 1 - 2 * (i : ℤ) : ℤ) : ℂ) / 2) =
      (q : ℂ) ^ (-(m : ℂ) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2)) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : ((((n : ℤ) - 1 - 2 * (i : ℤ) : ℤ) : ℂ) / 2) =
      ((((n : ℝ) - 1 - 2 * (i : ℝ)) / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : (-(m : ℂ) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2)) =
      (((-m : ℝ) * (((n : ℝ) - 1 - 2 * (i : ℝ)) / 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, h2, ← Complex.ofReal_cpow (zpow_nonneg hq _), ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow hq, Real.rpow_mul hq, ← Real.rpow_intCast]
  push_cast
  rfl

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in

theorem _root_.GlobalTheory.SmGL.SphCompletion.law_completion (n : ℕ) (α : Fin n → ℂˣ)
    (b : _root_.GlobalTheory.SmGL.borel (v.adicCompletion F) (Fin n)) (c : ℂ) :
    letI := _root_.GlobalTheory.LocalData.complRel v
    haveI := _root_.GlobalTheory.LocalData.isLocalField v
    (_root_.GlobalTheory.SmGL.deltaHalf (v.adicCompletion F) (fun _ : Fin n => Unit)
        (_root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b) : ℂ) •
      ((_root_.GlobalTheory.SmGL.ofChar
          (_root_.GlobalTheory.SmGL.torusChar fun i => _root_.GlobalTheory.SmGL.unrChar (v.adicCompletion F) (α i))).comp
        (_root_.GlobalTheory.SmGL.leviTorus (v.adicCompletion F) (Fin n)).symm.toMonoidHom)
        (_root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b) c =
      _root_.Formalism.UG.chiDelta F v (fun i => (α i : ℂ)) b.1 * c := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  set t := _root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b with ht
  have hdet : ∀ i, ((Matrix.GeneralLinearGroup.det (t i) : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) = (b.1 : Matrix _ _ _) i i := by
    intro i
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    exact _root_.GlobalTheory.SmGL.leviProj_apply _ (_root_.GlobalTheory.SmGL.points (Fin n)) b i () ()
  have hsymm : ∀ i, (_root_.GlobalTheory.SmGL.leviTorus (v.adicCompletion F) (Fin n)).symm t i =
      Matrix.GeneralLinearGroup.det (t i) := fun i => rfl
  rw [_root_.GlobalTheory.SmGL.deltaHalf_apply]
  simp only [MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.ofChar_apply, smul_eq_mul,
    MulEquiv.coe_toMonoidHom, _root_.GlobalTheory.SmGL.torusChar_apply, _root_.GlobalTheory.SmGL.unrChar_apply,
    hsymm, Units.coe_prod, _root_.GlobalTheory.SmGL.val_absPow]
  unfold _root_.Formalism.UG.chiDelta
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have hord : _root_.GlobalTheory.SmGL.ord (v.adicCompletion F)
      (Matrix.GeneralLinearGroup.det (t i)) = _root_.Formalism.UG.ordV F v ((b.1 : Matrix _ _ _) i i) := by
    rw [_root_.GlobalTheory.SmGL.SphCompletion.ord_completion, _root_.GlobalTheory.LGrp.BorelCompletion.ordV_eq, hdet]
  rw [_root_.GlobalTheory.SmGL.modExp_fin _ (fun _ => Fintype.card_unit),
    _root_.GlobalTheory.LGrp.nabs_eq_zpow, hord, residueFieldCard_adicCompletion_lemma, mul_comm]
  rw [Units.val_zpow_eq_zpow_val, natCast_zpow_neg_cpow_eq_cpow_mul]

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in

theorem _root_.GlobalTheory.SmGL.SphCompletion.exists_fixed_iff {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (χ : Fin n → kˣ →* ℂˣ)
    (φ : GL (Fin n) k → ℂ) :
    (∃ f ∈ _root_.GlobalTheory.PRep.fixed (_root_.GlobalTheory.SmGL.prinSeries χ)
        (_root_.GlobalTheory.SplitWeil.KO k (Fin n)), f.1.1 = φ) ↔
      (∀ (b : _root_.GlobalTheory.SmGL.borel k (Fin n)) g, φ (b * g) =
        (_root_.GlobalTheory.SmGL.deltaHalf k (fun _ : Fin n => Unit)
            (_root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b) : ℂ) •
          ((_root_.GlobalTheory.SmGL.ofChar (_root_.GlobalTheory.SmGL.torusChar χ)).comp
              (_root_.GlobalTheory.SmGL.leviTorus k (Fin n)).symm.toMonoidHom)
            (_root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b) (φ g)) ∧
      ∀ g ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n), ∀ x, φ (x * g) = φ x := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [_root_.GlobalTheory.LGrp.mem_fixed] at hf
    refine ⟨fun b g => _root_.GlobalTheory.SmGL.parInd_law _ _ f b g, fun g hg x => ?_⟩
    have := congrArg (fun f' => f'.1.1 x) (hf g hg)
    exact (_root_.GlobalTheory.SmGL.parInd_apply _ _ g x f).symm.trans this
  · rintro ⟨hlaw, hinv⟩
    let f₀ : _root_.GlobalTheory.PRep.indSpace (_root_.GlobalTheory.SmGL.parab k (_root_.GlobalTheory.SmGL.points (Fin n)))
        ((_root_.GlobalTheory.SmGL.twist
          ((_root_.GlobalTheory.SmGL.ofChar (_root_.GlobalTheory.SmGL.torusChar χ)).comp
            (_root_.GlobalTheory.SmGL.leviTorus k (Fin n)).symm.toMonoidHom)
          (_root_.GlobalTheory.SmGL.deltaHalf k (fun _ : Fin n => Unit))).comp
          (_root_.GlobalTheory.SmGL.leviProj k (_root_.GlobalTheory.SmGL.points (Fin n)))) :=
      ⟨φ, fun b g => hlaw b g⟩
    have hfix : ∀ g ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n),
        _root_.GlobalTheory.PRep.ind _ _ g f₀ = f₀ := fun g hg => by
      ext x
      exact hinv g hg x
    have hsm : f₀ ∈ _root_.GlobalTheory.PRep.smoothPart (_root_.GlobalTheory.PRep.ind _ _) := by
      apply _root_.GlobalTheory.SmGL.mem_smoothPart_of_nhds
      refine Filter.mem_of_superset
        (_root_.GlobalTheory.SplitFlip.isOpen_KO.mem_nhds (_root_.GlobalTheory.SplitWeil.KO k (Fin n)).one_mem)
        fun g hg => hfix g hg
    refine ⟨⟨f₀, hsm⟩, ?_, rfl⟩
    rw [_root_.GlobalTheory.LGrp.mem_fixed]
    intro g hg
    ext x
    exact (_root_.GlobalTheory.SmGL.parInd_apply _ _ g x _).trans (hinv g hg x)

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in

theorem _root_.GlobalTheory.SmGL.SphCompletion.isSpherical_iff : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (α : Fin n → ℂˣ)
    (φ : GL (Fin n) (v.adicCompletion F) → ℂ),
    letI := _root_.GlobalTheory.LocalData.complRel v; haveI := _root_.GlobalTheory.LocalData.isLocalField v;
    (_root_.Formalism.UG.IsSpherical F v (fun i => (α i : ℂ)) φ ↔
      ∃ f ∈ _root_.GlobalTheory.PRep.fixed
          (_root_.GlobalTheory.SmGL.prinSeries fun i => _root_.GlobalTheory.SmGL.unrChar (v.adicCompletion F) (α i))
          (_root_.GlobalTheory.SplitWeil.KO (v.adicCompletion F) (Fin n)), f.1.1 = φ) := by
  intro F _ _ v n α φ
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  have hlaw := _root_.GlobalTheory.SmGL.SphCompletion.law_completion v n α
  have hone : _root_.Formalism.UG.chiDelta F v (fun i => (α i : ℂ)) 1 = 1 := by
    unfold _root_.Formalism.UG.chiDelta
    simp [_root_.GlobalTheory.LGrp.BorelCompletion.ordV_eq]
  have hborel : ∀ b : GL (Fin n) (v.adicCompletion F),
      _root_.Formalism.UG.IsUpperB F v b ↔ b ∈ _root_.GlobalTheory.SmGL.borel (v.adicCompletion F) (Fin n) := by
    intro b
    rw [_root_.GlobalTheory.SmGL.mem_borel]
    rfl
  rw [_root_.GlobalTheory.SmGL.SphCompletion.exists_fixed_iff,
    _root_.GlobalTheory.SmGL.SphCompletion.KO_completion]
  unfold _root_.Formalism.UG.IsSpherical
  constructor
  · intro h
    refine ⟨fun b g => ?_, fun g hg x => ?_⟩
    · rw [hlaw b (φ g)]
      simpa only [mul_one] using h b g 1 ((hborel _).2 b.2) (one_mem _)
    · simpa only [one_mul, hone] using h 1 x g ((hborel 1).2 (one_mem _)) hg
  · rintro ⟨hL, hI⟩ b g k hb hk
    rw [hI k hk, ← hlaw ⟨b, (hborel b).1 hb⟩ (φ g)]
    exact hL ⟨b, (hborel b).1 hb⟩ g

end GlobalTheory.SmGL.SphCompletion
