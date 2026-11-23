import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfTameLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatHeckeCharacterTrivialCongruentUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharFiniteOrderUnitIdele
import Formalism.LocalToGlobal.UnitaryNorms.CharExGen

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CMVal

namespace GlobalTheory.ConjValChar

variable {E : Type} [Field E] [NumberField E]

def conjFin (χ : HChar E) (σ : ℂ ≃+* ℂ) : Ideles E →* ℂˣ :=
  (Units.map (σ : ℂ →+* ℂ).toMonoidHom).comp (χ.1.comp (GlobalTheory.Mem.Chr.finPartI E))

theorem conjFin_apply (χ : HChar E) (σ : ℂ ≃+* ℂ) (a : Ideles E) :
    ((conjFin χ σ a : ℂˣ) : ℂ) = σ ((χ.1 (GlobalTheory.Mem.Chr.finPartI E a) : ℂˣ) : ℂ) := rfl

def extEmb (φ : E →+* ℂ) : (InfinitePlace.mk φ).Completion →+* ℂ := (GlobalTheory.InfTypeLocal.exists_ext φ).choose

theorem continuous_extEmb (φ : E →+* ℂ) : Continuous (extEmb φ) := (GlobalTheory.InfTypeLocal.exists_ext φ).choose_spec.1

theorem extEmb_algebraMap (φ : E →+* ℂ) (k : E) : extEmb φ (algebraMap E _ k) = φ k :=
  (GlobalTheory.InfTypeLocal.exists_ext φ).choose_spec.2 k

def infChar {I : Type} [Fintype I] (φ : I → E →+* ℂ) (n : I → ℤ) : Ideles E →* ℂˣ where
  toFun a := ∏ i, GlobalTheory.ModelChar.argU (Units.map (extEmb (φ i)).toMonoidHom
    (Units.map (GlobalTheory.ModelChar.infEv (InfinitePlace.mk (φ i))) a)) ^ n i
  map_one' := by simp only [map_one, one_zpow, Finset.prod_const_one]
  map_mul' a b := by simp only [map_mul, mul_zpow, Finset.prod_mul_distrib]

variable {I : Type} [Fintype I]

theorem continuous_infChar (φ : I → E →+* ℂ) (n : I → ℤ) : Continuous (infChar φ n) := by
  refine continuous_finsetProd _ fun i _ => ?_
  exact (GlobalTheory.ModelChar.continuous_argU.comp ((Continuous.units_map _ (continuous_extEmb (φ i))).comp
    (Continuous.units_map _ (GlobalTheory.ModelChar.continuous_infEv _)))).zpow _

theorem norm_infChar (φ : I → E →+* ℂ) (n : I → ℤ) (a : Ideles E) : ‖((infChar φ n a : ℂˣ) : ℂ)‖ = 1 := by
  show ‖((∏ i, _ : ℂˣ) : ℂ)‖ = 1
  rw [Units.coe_prod, norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Units.val_zpow_eq_zpow_val, norm_zpow, GlobalTheory.ModelChar.norm_argU, one_zpow]

end GlobalTheory.ConjValChar

namespace GlobalTheory.ConjValChar
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CMVal
variable {E : Type} [Field E] [NumberField E]

theorem continuous_conjFin (χ : HChar E) (σ : ℂ ≃+* ℂ) : Continuous (conjFin χ σ) := by
  obtain ⟨M, hM, hχ⟩ := GlobalTheory.Mem.HeckeLevel.exists_level_nat E χ
  have hM0 : ((M : 𝓞 E)) ≠ 0 := by exact_mod_cast hM.ne'
  have hfin : {P : HeightOneSpectrum (𝓞 E) | P.asIdeal ∣ Ideal.span {(M : 𝓞 E)}}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  have hval : ∀ P : HeightOneSpectrum (𝓞 E),
      Valued.v (((M : E)) : P.adicCompletion E) = P.intValuation (M : 𝓞 E) := fun P => by
    rw [show ((M : E)) = algebraMap (𝓞 E) E (M : 𝓞 E) by simp,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  have key : ∀ᶠ a in nhds (1 : Ideles E), a ∈ GlobalTheory.Mem.Chr.unitIdl E ∧ ∀ P ∈ hfin.toFinset,
      Valued.v (((a : AdeleRing (𝓞 E) E).2 P) - 1) ≤ Valued.v (((M : E)) : P.adicCompletion E) := by
    refine Filter.Eventually.and (GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.mem_nhds (one_mem (GlobalTheory.Mem.Chr.unitIdl E))) ?_
    rw [Filter.eventually_all_finset]
    intro P _
    have hc : Continuous (fun a : Ideles E => (a : AdeleRing (𝓞 E) E).2 P - 1) :=
      (GlobalTheory.Mem.UnitOpen.continuous_comp P).sub continuous_const
    have hv0 : Valued.v (((M : E)) : P.adicCompletion E) ≠ 0 := by
      rw [hval]; exact HeightOneSpectrum.intValuation_ne_zero P _ hM0
    have ho := GlobalTheory.Mem.UnitOpen.isOpen_val_le P (WithZero.log (Valued.v (((M : E)) : P.adicCompletion E)))
    rw [WithZero.exp_log hv0] at ho
    refine (ho.preimage hc).mem_nhds ?_
    show Valued.v (((1 : Ideles E) : AdeleRing (𝓞 E) E).2 P - 1) ≤ _
    rw [show ((1 : Ideles E) : AdeleRing (𝓞 E) E).2 P = 1 from rfl, sub_self, map_zero]
    exact zero_le'
  refine continuous_of_continuousAt_one _ ?_
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  filter_upwards [key] with a ha
  have hb1 : ∀ w, ((GlobalTheory.Mem.Chr.finPartI E a : Ideles E) : AdeleRing (𝓞 E) E).1 w = 1 := fun w => rfl
  have hb2 : ((GlobalTheory.Mem.Chr.finPartI E a : Ideles E) : AdeleRing (𝓞 E) E).2 = (a : AdeleRing (𝓞 E) E).2 := rfl
  have h := hχ (GlobalTheory.Mem.Chr.finPartI E a) (GlobalTheory.Mem.Chr.finPartI_mem_unitIdl.2 ha.1) hb1 (fun P => by
    rw [hb2]
    by_cases hP : P ∈ hfin.toFinset
    · exact ha.2 P hP
    · have h1 : Valued.v (((M : E)) : P.adicCompletion E) = 1 := by
        rw [hval]
        refine le_antisymm (HeightOneSpectrum.intValuation_le_one P _) (not_lt.1 fun hlt => hP ?_)
        exact hfin.mem_toFinset.2 ((HeightOneSpectrum.intValuation_lt_one_iff_dvd P _).1 hlt)
      rw [h1]
      refine (Valuation.map_sub _ _ _).trans ?_
      rw [ha.1 P, map_one, max_self])
  show 1 = Units.map (σ : ℂ →+* ℂ).toMonoidHom (χ.1 (GlobalTheory.Mem.Chr.finPartI E a))
  rw [h, map_one]

end GlobalTheory.ConjValChar

namespace GlobalTheory.ConjValChar
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CMVal
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem infChar_diag (φ : I → E →+* ℂ) (n : I → ℤ) (k : Eˣ) :
    ((infChar φ n (diagUnits E k) : ℂˣ) : ℂ) = ∏ i, (φ i (k : E) / ((‖φ i (k : E)‖ : ℝ) : ℂ)) ^ n i := by
  show ((∏ i, _ : ℂˣ) : ℂ) = _
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Units.val_zpow_eq_zpow_val, GlobalTheory.ModelChar.argU_val, GlobalTheory.ModelChar.infEv_diag]
  exact congrArg (fun z : ℂ => (z / ((‖z‖ : ℝ) : ℂ)) ^ n i) (extEmb_algebraMap (φ i) (k : E))

theorem infChar_infDiag (φ : I → E →+* ℂ) (n : I → ℤ) (k : Eˣ) :
    ((infChar φ n (infDiag k) : ℂˣ) : ℂ) = ∏ i, (φ i (k : E) / ((‖φ i (k : E)‖ : ℝ) : ℂ)) ^ n i := by
  show ((∏ i, _ : ℂˣ) : ℂ) = _
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Units.val_zpow_eq_zpow_val, GlobalTheory.ModelChar.argU_val, GlobalTheory.ModelChar.infEv_infDiag]
  exact congrArg (fun z : ℂ => (z / ((‖z‖ : ℝ) : ℂ)) ^ n i) (extEmb_algebraMap (φ i) (k : E))

theorem infChar_finPartI (φ : I → E →+* ℂ) (n : I → ℤ) (a : Ideles E) :
    infChar φ n (GlobalTheory.Mem.Chr.finPartI E a) = 1 := by
  show (∏ i, _ : ℂˣ) = 1
  refine Finset.prod_eq_one fun i _ => ?_
  have : Units.map (GlobalTheory.ModelChar.infEv (InfinitePlace.mk (φ i))) (GlobalTheory.Mem.Chr.finPartI E a) = 1 := Units.ext rfl
  rw [this, map_one, map_one, one_zpow]

theorem infChar_local (φ : I → E →+* ℂ) (n : I → ℤ) (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    infChar φ n (localIdele E v x) = 1 := by
  show (∏ i, _ : ℂˣ) = 1
  refine Finset.prod_eq_one fun i _ => ?_
  rw [GlobalTheory.ModelChar.infEv_local, map_one, map_one, one_zpow]

theorem finPartI_finIdele (y : (Af E)ˣ) : GlobalTheory.Mem.Chr.finPartI E (finIdele E y) = finIdele E y :=
  GlobalTheory.Mem.Chr.finPartI_eq_self fun _ => rfl

theorem finPartI_local (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    GlobalTheory.Mem.Chr.finPartI E (localIdele E v x) = localIdele E v x :=
  GlobalTheory.Mem.Chr.finPartI_eq_self fun _ => rfl

theorem finPartI_diag (k : Eˣ) :
    GlobalTheory.Mem.Chr.finPartI E (diagUnits E k) = finIdele E (Units.map (algebraMap E (Af E)).toMonoidHom k) :=
  Units.ext rfl

theorem finPartI_infDiag (k : Eˣ) : GlobalTheory.Mem.Chr.finPartI E (infDiag k) = 1 := by
  apply Units.ext
  refine Prod.ext rfl (RestrictedProduct.ext _ _ fun v => ?_)
  exact congrArg Units.val (GlobalTheory.ModelChar.finEv_infDiag v k)

theorem finPartI_infIdele (w : InfinitePlace E) (y : (w.Completion)ˣ) :
    GlobalTheory.Mem.Chr.finPartI E (infIdele E w y) = 1 := by
  apply Units.ext
  refine Prod.ext rfl (RestrictedProduct.ext _ _ fun v => ?_)
  exact congrArg Units.val (GlobalTheory.ModelChar.finEv_inf v w y)

theorem infChar_finIdele (φ : I → E →+* ℂ) (n : I → ℤ) (y : (Af E)ˣ) : infChar φ n (finIdele E y) = 1 := by
  rw [← finPartI_finIdele, infChar_finPartI]

end GlobalTheory.ConjValChar

namespace GlobalTheory.ConjValChar
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CMVal
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem injective_of_isCMType {φ : I → E →+* ℂ} (h : IsCMType φ) : Function.Injective φ := fun i j hij =>
  (h (φ i)).unique (Or.inl rfl) (Or.inl hij)

theorem bijective_of_isCMType {φ : I → E →+* ℂ} (h : IsCMType φ) :
    Function.Bijective fun i => InfinitePlace.mk (φ i) := by
  constructor
  · intro i j hij
    have e := InfinitePlace.mk_eq_iff.1 hij
    refine (h (φ j)).unique ?_ (Or.inl rfl)
    rcases e with e | e
    · exact Or.inl e.symm
    · exact Or.inr e.symm
  · intro w
    obtain ⟨i, hi, -⟩ := h w.embedding
    refine ⟨i, ?_⟩
    rcases hi with e | e
    · show InfinitePlace.mk (φ i) = w
      rw [← e, InfinitePlace.mk_embedding]
    · show InfinitePlace.mk (φ i) = w
      rw [← InfinitePlace.mk_conjugate_eq, ← e, InfinitePlace.mk_embedding]

theorem exists_perm {K : Type} [Field K] [Algebra K E] {φK : K →+* ℂ} {φ : I → E →+* ℂ} {σ : ℂ ≃+* ℂ}
    (hφ : IsCMType φ) (hK : ∀ i, (φ i).comp (algebraMap K E) = φK) (hc : (starRingEnd ℂ).comp φK ≠ φK)
    (hσ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ) : ∃ p : Equiv.Perm I, ∀ i x, σ (φ i x) = φ (p i) x := by
  have h1 : ∀ i, ∃ j, ∀ x, σ (φ i x) = φ j x := fun i => by
    obtain ⟨j, hj, -⟩ := hφ ((σ : ℂ →+* ℂ).comp (φ i))
    refine ⟨j, ?_⟩
    rcases hj with e | e
    · exact fun x => congrArg (fun f : E →+* ℂ => f x) e
    · exfalso
      refine hc (RingHom.ext fun y => ?_)
      have e1 := congrArg (fun f : E →+* ℂ => f (algebraMap K E y)) e
      simp only [RingHom.coe_comp, Function.comp_apply, ComplexEmbedding.conjugate_coe_eq] at e1
      have e2 : φ i (algebraMap K E y) = φK y := congrArg (fun f : K →+* ℂ => f y) (hK i)
      have e3 : φ j (algebraMap K E y) = φK y := congrArg (fun f : K →+* ℂ => f y) (hK j)
      rw [e2, e3] at e1
      rw [RingHom.comp_apply, ← e1]
      exact hσ y
  choose p hp using h1
  have hinj : Function.Injective p := fun i i' h => by
    refine injective_of_isCMType hφ (RingHom.ext fun x => σ.injective ?_)
    rw [hp, hp, h]
  exact ⟨Equiv.ofBijective p hinj.bijective_of_finite, hp⟩

theorem arg_pow_two_mul {z : ℂ} (hz : z ≠ 0) (m : ℤ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * m) = (z / starRingEnd ℂ z) ^ m := by
  rw [zpow_mul]
  congr 1
  rw [zpow_two, div_mul_div_comm, ← sq ((‖z‖ : ℝ) : ℂ), ← Complex.mul_conj', mul_div_mul_left _ _ hz]

theorem modF_rat (y : (Af E)ˣ) : ∃ q : ℚ, modF y = q := by
  unfold modF
  refine finprod_induction (fun x : ℝ => ∃ q : ℚ, x = q) ⟨1, by simp⟩ ?_ ?_
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, by push_cast; ring⟩
  · intro v
    exact ⟨((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (WithZero.log (Valued.v ((y : Af E) v))), by push_cast; rfl⟩

theorem sigma_modF (σ : ℂ ≃+* ℂ) (y : (Af E)ˣ) (s : ℕ) : σ ((modF y ^ s : ℝ) : ℂ) = ((modF y ^ s : ℝ) : ℂ) := by
  obtain ⟨q, hq⟩ := modF_rat y
  rw [hq, show (((q : ℝ) ^ s : ℝ) : ℂ) = ((q ^ s : ℚ) : ℂ) by push_cast; rfl, map_ratCast]

end GlobalTheory.ConjValChar

namespace GlobalTheory.ConjValChar
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CMVal
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem conj_diag [IsCMField E] {φ : I → E →+* ℂ} {σ : ℂ ≃+* ℂ} (p : Equiv.Perm I)
    (hp : ∀ i x, σ (φ i x) = φ (p i) x) (χ : HChar E) (m : I → ℤ) (hχ : HasInf χ φ m) (k : Eˣ) :
    infChar φ (fun j => 2 * m (p.symm j)) (diagUnits E k) * conjFin χ σ (diagUnits E k) = 1 := by
  apply Units.ext
  have hc : ∀ i, σ (starRingEnd ℂ (φ i (k : E))) = starRingEnd ℂ (φ (p i) (k : E)) := fun i => by
    rw [← IsCMField.complexEmbedding_complexConj, hp, IsCMField.complexEmbedding_complexConj]
  have h0 : ∀ j, φ j (k : E) ≠ 0 := fun j => by simp
  have hf : ((finPart χ (Units.map (algebraMap E (Af E)).toMonoidHom k) : ℂˣ) : ℂ) = ((χ.inf k : ℂˣ) : ℂ)⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [← Units.val_mul, finPart_mul_inf, Units.val_one])
  rw [Units.val_mul, conjFin_apply, finPartI_diag, infChar_diag, Units.val_one]
  show _ * σ ((finPart χ _ : ℂˣ) : ℂ) = 1
  rw [hf, (hasInfRatio_iff χ φ m).1 hχ k, map_inv₀, map_prod]
  simp only [map_zpow₀, map_div₀, hp, hc]
  rw [← Equiv.prod_comp p (fun j => (φ j (k : E) / ((‖φ j (k : E)‖ : ℝ) : ℂ)) ^ (2 * m (p.symm j)))]
  simp only [Equiv.symm_apply_apply, arg_pow_two_mul (h0 _)]
  refine mul_inv_cancel₀ ?_
  exact Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (div_ne_zero (h0 _) (by simpa using h0 (p i)))

def conjChar [IsCMField E] (φ : I → E →+* ℂ) (σ : ℂ ≃+* ℂ) (p : Equiv.Perm I) (hp : ∀ i x, σ (φ i x) = φ (p i) x)
    (χ : HChar E) (m : I → ℤ) (hχ : HasInf χ φ m) : HChar E :=
  ⟨infChar φ (fun j => 2 * m (p.symm j)) * conjFin χ σ,
    (continuous_infChar _ _).mul (continuous_conjFin χ σ), fun k => conj_diag p hp χ m hχ k⟩

variable [IsCMField E] {φ : I → E →+* ℂ} {σ : ℂ ≃+* ℂ} {p : Equiv.Perm I} {hp : ∀ i x, σ (φ i x) = φ (p i) x}
  {χ : HChar E} {m : I → ℤ} {hχ : HasInf χ φ m}

theorem conjChar_apply (a : Ideles E) :
    (conjChar φ σ p hp χ m hχ).1 a = infChar φ (fun j => 2 * m (p.symm j)) a * conjFin χ σ a := rfl

theorem conjChar_loc (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    (conjChar φ σ p hp χ m hχ).loc v x = Units.map (σ : ℂ →+* ℂ).toMonoidHom (χ.loc v x) := by
  show (conjChar φ σ p hp χ m hχ).1 (localIdele E v x) = _
  rw [conjChar_apply, infChar_local, one_mul]
  show Units.map (σ : ℂ →+* ℂ).toMonoidHom (χ.1 (GlobalTheory.Mem.Chr.finPartI E (localIdele E v x))) = _
  rw [finPartI_local]
  rfl

theorem conjChar_finPart (y : (Af E)ˣ) :
    finPart (conjChar φ σ p hp χ m hχ) y = Units.map (σ : ℂ →+* ℂ).toMonoidHom (finPart χ y) := by
  show (conjChar φ σ p hp χ m hχ).1 (finIdele E y) = _
  rw [conjChar_apply, infChar_finIdele, one_mul]
  show Units.map (σ : ℂ →+* ℂ).toMonoidHom (χ.1 (GlobalTheory.Mem.Chr.finPartI E (finIdele E y))) = _
  rw [finPartI_finIdele]
  rfl

theorem conjChar_hasInf : HasInf (conjChar φ σ p hp χ m hχ) φ (fun j => m (p.symm j)) := by
  intro k
  show (((conjChar φ σ p hp χ m hχ).1 (infDiag k) : ℂˣ) : ℂ) = _
  rw [conjChar_apply, Units.val_mul, infChar_infDiag, conjFin_apply, finPartI_infDiag, map_one, Units.val_one,
    map_one, mul_one]

end GlobalTheory.ConjValChar

namespace GlobalTheory.ConjValChar
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CMVal
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem infChar_infIdele {φ : I → E →+* ℂ} (n : I → ℤ) (hbij : Function.Bijective fun i => InfinitePlace.mk (φ i))
    (j : I) (y : ((InfinitePlace.mk (φ j)).Completion)ˣ) :
    infChar φ n (infIdele E (InfinitePlace.mk (φ j)) y) =
      GlobalTheory.ModelChar.argU (Units.map (extEmb (φ j)).toMonoidHom y) ^ n j := by
  show (∏ i, _ : ℂˣ) = _
  rw [Finset.prod_eq_single j]
  · rw [GlobalTheory.ModelChar.infEv_inf_self]
  · intro i _ hi
    rw [GlobalTheory.ModelChar.infEv_inf_ne (fun hh => hi (hbij.1 hh)), map_one, map_one, one_zpow]
  · simp

variable [IsCMField E] {φ : I → E →+* ℂ} {σ : ℂ ≃+* ℂ} {p : Equiv.Perm I} {hp : ∀ i x, σ (φ i x) = φ (p i) x}
  {χ : HChar E} {m : I → ℤ} {hχ : HasInf χ φ m}

theorem conjChar_isUnitary : (conjChar φ σ p hp χ m hχ).IsUnitary := by
  refine Formalism.L2.Host.CharEx.isUnitary_of_unitIdeles _ fun u hu => ?_
  rw [conjChar_apply, Units.val_mul, norm_mul, norm_infChar, one_mul, conjFin_apply]
  obtain ⟨n, hn, h⟩ := GlobalTheory.HeckeFin.finite_order E χ (GlobalTheory.Mem.Chr.finPartI E u) (fun _ => rfl) (fun v => hu v)
  have h2 : (σ ((χ.1 (GlobalTheory.Mem.Chr.finPartI E u) : ℂˣ) : ℂ)) ^ n = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, map_one]
  have h3 := congrArg norm h2
  rw [norm_pow, norm_one] at h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h3

theorem conjChar_levelLe_iff (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    (conjChar φ σ p hp χ m hχ).LevelLe v n ↔ χ.LevelLe v n := by
  refine forall_congr' fun x => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [conjChar_loc]
  constructor
  · intro h
    exact Units.map_injective (f := (σ : ℂ →+* ℂ).toMonoidHom) σ.injective (h.trans (map_one _).symm)
  · intro h
    rw [h, map_one]

end GlobalTheory.ConjValChar

namespace GlobalTheory.ConjValChar
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CMVal
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
variable [IsCMField E] {φ : I → E →+* ℂ} {σ : ℂ ≃+* ℂ} {p : Equiv.Perm I} {hp : ∀ i x, σ (φ i x) = φ (p i) x}
  {χ : HChar E} {m : I → ℤ} {hχ : HasInf χ φ m}

theorem conj_real (ψ : E →+* ℂ) (k : maximalRealSubfield E) :
    starRingEnd ℂ (ψ (algebraMap (maximalRealSubfield E) E k)) = ψ (algebraMap (maximalRealSubfield E) E k) := by
  rw [← IsCMField.complexEmbedding_complexConj, AlgEquiv.commutes]

theorem conjChar_trivOnF (hT : TrivOnF χ) (hbij : Function.Bijective fun i => InfinitePlace.mk (φ i)) :
    TrivOnF (conjChar φ σ p hp χ m hχ) := by
  refine ⟨fun v k => ?_, fun w k => ?_⟩
  · have h := hT.1 v k
    unfold HChar.resFin at h ⊢
    rw [MonoidHom.finset_prod_apply] at h ⊢
    have e : ∀ P : HeightOneSpectrum (𝓞 E), ((conjChar φ σ p hp χ m hχ).locK P).comp (upF (maximalRealSubfield E)) k =
        Units.map (σ : ℂ →+* ℂ).toMonoidHom ((χ.locK P).comp (upF (maximalRealSubfield E)) k) := fun P =>
      conjChar_loc (hp := hp) (hχ := hχ) _ _
    simp only [e]
    rw [← map_prod, h, map_one]
  · unfold HChar.resInf
    rw [MonoidHom.finset_prod_apply]
    refine Finset.prod_eq_one fun w' _ => ?_
    obtain ⟨j, rfl⟩ := hbij.2 w'
    apply Units.ext
    show (((conjChar φ σ p hp χ m hχ).1 (infIdele E (InfinitePlace.mk (φ j))
      (atInf (InfinitePlace.mk (φ j)) (upF (maximalRealSubfield E) k))) : ℂˣ) : ℂ) = 1
    rw [conjChar_apply, Units.val_mul, conjFin_apply, finPartI_infIdele, map_one, Units.val_one, map_one, mul_one,
      infChar_infIdele _ hbij, Units.val_zpow_eq_zpow_val, GlobalTheory.ModelChar.argU_val]
    have e1 : ((Units.map (extEmb (φ j)).toMonoidHom (atInf (InfinitePlace.mk (φ j))
        (upF (maximalRealSubfield E) k)) : ℂˣ) : ℂ) = φ j (algebraMap (maximalRealSubfield E) E k) :=
      extEmb_algebraMap (φ j) _
    have h0 : φ j (algebraMap (maximalRealSubfield E) E k) ≠ 0 := by simp
    rw [e1, arg_pow_two_mul h0, conj_real, div_self h0, one_zpow]

end GlobalTheory.ConjValChar

namespace GlobalTheory.ConjValChar
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CMVal

theorem exists_conj_valChar : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E] [Algebra K E]
    {I : Type} [Fintype I] (φK : K →+* ℂ) (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (χ : HChar E)
    (σ : ℂ ≃+* ℂ), IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = φK) → (starRingEnd ℂ).comp φK ≠ φK →
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ → IsValChar φ s κ 𝔣 ∅ χ →
    ∃ (π : Equiv.Perm I) (χ' : HChar E), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsConjWt φ σ κ (κ ∘ π) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsConjChar φ s (κ ∘ π) σ χ χ' ∧ IsValChar φ s (κ ∘ π) 𝔣 ∅ χ' := by
  intro K E _ _ _ _ _ _ I _ φK φ s κ 𝔣 χ σ hφ hK hc hσ hV
  obtain ⟨p, hp⟩ := exists_perm hφ hK hc hσ
  have hbij := bijective_of_isCMType hφ
  have hm : HasInf χ φ (fun i => (κ i : ℤ) + s) := hV.2.2.1
  refine ⟨p.symm, conjChar φ σ p hp χ _ hm, ?_, ⟨fun y => ?_, conjChar_hasInf⟩,
    ⟨conjChar_isUnitary, conjChar_trivOnF hV.2.1 hbij, conjChar_hasInf, fun v P hP => ⟨fun h => absurd h (by simp),
      fun hv n => (conjChar_levelLe_iff P n).trans ((hV.2.2.2 v P hP).2 hv n)⟩⟩⟩
  · intro i j hij
    have e : φ j = φ (p i) := RingHom.ext fun x => (hij x).symm.trans (hp i x)
    rw [injective_of_isCMType hφ e]
    simp
  · unfold GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF
    rw [conjChar_finPart, map_mul, sigma_modF]
    rfl

end GlobalTheory.ConjValChar
