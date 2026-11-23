import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DecompositionGroupMulEquivLocalGaloisCyclotomicStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowNStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntLengthEqOfCardQuotientEqCardSubmoduleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntTorsionFreeOfCardQuotientPowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntModuleFiniteOfSeparatedOfFiniteQuotientAStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QzTorsionZmodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoboundaryOfSubsingletonContCohomologyThreStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCardStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContCohomologyTransportMulEquivStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntTwoCocycleEqPowSmulOfReductionCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModLThreeCocycleConditionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisibleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sha1TorsionLevelFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCardCokerKerPadicModPowStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory.TateLimit

section Core

variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ]

abbrev lpow (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (r : ℕ) :
    Submodule ℤ_[l] X :=
  LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ r))

theorem lpow_anti (X : Type) [AddCommGroup X] [Module ℤ_[l] X] : Antitone (lpow l X) := by
  intro r s h x ⟨y, hy⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨(l : ℤ_[l]) ^ k • y, by rw [← hy, pow_add, LinearMap.lsmul_apply, LinearMap.lsmul_apply, mul_smul]⟩

theorem lpow_sep (X : Type) [AddCommGroup X] [Module ℤ_[l] X] [Module.Finite ℤ_[l] X] (x : X)
    (h : ∀ r, x ∈ lpow l X r) : x = 0 := by
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := X) (IsLocalRing.maximalIdeal ℤ_[l])
    (IsLocalRing.maximalIdeal.isMaximal ℤ_[l]).ne_top
  rw [← Submodule.mem_bot ℤ_[l], ← hK, Submodule.mem_iInf]
  intro r
  obtain ⟨y, rfl⟩ := h r
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) r

def reduceTwoCocyclesModPrimePow (ρ : Representation ℤ_[l] Γ ℤ_[l]) (r : ℕ)
    (ρr : Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r)))
    (h : ∀ g x, PadicInt.toZModPow r (ρ g x) = ρr g (PadicInt.toZModPow r x)) :
    Z2 ρ →ₛₗ[(PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r))] Z2 ρr where
  toFun z := ⟨fun p => PadicInt.toZModPow r (z.1 p),
    GlobalTheory.Published.PoitouTate.continuous_toZModPow.comp z.2.1, fun g h' k => by
      simp only [← h, ← map_sub, ← map_add, z.2.2 g h' k, map_zero]⟩
  map_add' z z' := Subtype.ext (funext fun p => map_add _ _ _)
  map_smul' c z := Subtype.ext (funext fun p => map_mul _ _ _)

def reduceH2ModPrimePow (ρ : Representation ℤ_[l] Γ ℤ_[l]) (r : ℕ)
    (ρr : Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r)))
    (h : ∀ g x, PadicInt.toZModPow r (ρ g x) = ρr g (PadicInt.toZModPow r x)) :
    H2 ρ →+ H2 ρr :=
  (Submodule.mapQ _ _ (reduceTwoCocyclesModPrimePow ρ r ρr h) fun z hz => by
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem ρ _).1 hz
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => PadicInt.toZModPow r (c g),
      GlobalTheory.Published.PoitouTate.continuous_toZModPow.comp hc, ?_⟩
    funext p
    have e := congrFun hcf p
    simp only [Submodule.coe_subtype] at e
    change _ = PadicInt.toZModPow r (z.1 p)
    rw [← e]
    simp [d1, h]).toAddMonoidHom

theorem reduction_h2_eq_zero_iff [ContinuousMul Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]) (hρ : ContAction ρ)
    (r : ℕ) (ρr : Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r)))
    (h : ∀ g x, PadicInt.toZModPow r (ρ g x) = ρr g (PadicInt.toZModPow r x)) (x : H2 ρ) :
    reduceH2ModPrimePow ρ r ρr h x = 0 ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x := by
  constructor
  · induction x using Submodule.Quotient.induction_on with
    | H z =>
      intro hz
      have hz' : reduceTwoCocyclesModPrimePow ρ r ρr h z ∈ (B2 ρr).comap (Z2 ρr).subtype :=
        (Submodule.Quotient.mk_eq_zero _).1 hz
      obtain ⟨w, hw, hb⟩ := GlobalTheory.T.exists_z2_sub_pow_smul_mem_b2_of_reduction l Γ ρ hρ r ρr h z.1 z.2 hz'
      refine ⟨Submodule.Quotient.mk ⟨w, hw⟩, ?_⟩
      rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq]
      exact hb
  · rintro ⟨y, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | H z =>
      have : reduceTwoCocyclesModPrimePow ρ r ρr h ((l : ℤ_[l]) ^ r • z) = 0 := by
        rw [LinearMap.map_smulₛₗ, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_smul]
      change Submodule.Quotient.mk (reduceTwoCocyclesModPrimePow ρ r ρr h ((l : ℤ_[l]) ^ r • z)) = 0
      rw [this, Submodule.Quotient.mk_zero]

theorem reduction_h2_surjective [ContinuousMul Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]) (hρ : ContAction ρ)
    (ρr : ∀ r, Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r)))
    (h : ∀ r g x, PadicInt.toZModPow r (ρ g x) = ρr r g (PadicInt.toZModPow r x))
    (h3 : Subsingleton (Hn (ρr 1) 3)) (r : ℕ) : Function.Surjective (reduceH2ModPrimePow ρ r (ρr r) (h r)) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H y =>
    obtain ⟨z, hz, e⟩ := GlobalTheory.T.mod_l_three_cocycle_condition l Γ ρ hρ (ρr 1) (h 1)
      (GlobalTheory.T.exists_coboundary_of_subsingleton_contCohomology_three _ Γ _ (ρr 1) h3) r (ρr r) (h r) y.1 y.2
    exact ⟨Submodule.Quotient.mk ⟨z, hz⟩,
      congrArg Submodule.Quotient.mk (Subtype.ext (funext e))⟩

theorem card_quot_lpow {X : Type} [AddCommGroup X] [Module ℤ_[l] X] {Y : Type} [AddCommGroup Y]
    (r : ℕ) (π : X →+ Y) (hs : Function.Surjective π)
    (hk : ∀ x, π x = 0 ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x) :
    Nat.card (X ⧸ lpow l X r) = Nat.card Y := by
  have : (lpow l X r).toAddSubgroup = π.ker := by
    ext x; exact (hk x).symm
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective π hs).toEquiv, ← this]
  rfl

theorem finite_h2_padic_representation [ContinuousMul Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]) (hρ : ContAction ρ)
    (ρr : ∀ r, Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r)))
    (h : ∀ r g x, PadicInt.toZModPow r (ρ g x) = ρr r g (PadicInt.toZModPow r x))
    (h1 : ∀ r, 0 < r → Finite (H1 (ρr r))) (h2 : Finite (H2 (ρr 1)))
    (h3 : Subsingleton (Hn (ρr 1) 3)) : Module.Finite ℤ_[l] (H2 ρ) := by
  refine GlobalTheory.T.padicInt_module_finite_of_separated l _ ?_ fun x hx => ?_
  · refine Nat.finite_of_card_ne_zero ?_
    rw [card_quot_lpow 1 _ (reduction_h2_surjective ρ hρ ρr h h3 1) (reduction_h2_eq_zero_iff ρ hρ 1 _ (h 1))]
    exact Nat.card_pos.ne'
  · induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.Quotient.mk_eq_zero]
      refine GlobalTheory.T.padic_coboundary_of_divisible l Γ ρ ρr h h1 z.1 z.2 fun r => ?_
      obtain ⟨y, hy⟩ := hx r
      induction y using Submodule.Quotient.induction_on with
      | H w =>
        rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq] at hy
        exact ⟨w.1, w.2, hy⟩

theorem length_eq_length_invariants_of_torsion_levels {X : Type} [AddCommGroup X] [Module ℤ_[l] X] [Module.Finite ℤ_[l] X]
    {A : Type} [AddCommGroup A] [Module ℤ_[l] A] (σ : Representation ℤ_[l] Γ A)
    (hA : ∀ a : A, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0)
    (N : ℕ → Type) [∀ r, AddCommGroup (N r)] [∀ r, Module (ZMod (l ^ r)) (N r)] [∀ r, Finite (N r)]
    (τ : ∀ r, Representation (ZMod (l ^ r)) Γ (N r)) (ι : ∀ r, N r →+ A)
    (hι : ∀ r, Function.Injective (ι r))
    (hr : ∀ r (a : A), (l : ℤ_[l]) ^ r • a = 0 ↔ a ∈ Set.range (ι r))
    (he : ∀ r g n, ι r (τ r g n) = σ g (ι r n))
    (hc : ∀ r, 0 < r → Nat.card (X ⧸ lpow l X r) = Nat.card (H0 (τ r))) :
    Module.length ℤ_[l] X = Module.length ℤ_[l] (H0 σ) := by
  refine GlobalTheory.T.padicInt_length_eq_of_card_quotient_eq l X (H0 σ) (lpow l X)
    (fun r => Submodule.torsionBy ℤ_[l] (H0 σ) ((l : ℤ_[l]) ^ r)) 1 (lpow_anti X) (lpow_sep X)
    (fun r s h => Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow _ h))
    (fun y => (hA y.1).imp fun r h => Subtype.ext h) fun r h => ?_
  let f : H0 (τ r) → Submodule.torsionBy ℤ_[l] (H0 σ) ((l : ℤ_[l]) ^ r) := fun n =>
    ⟨⟨ι r n.1, fun g => by rw [← he, n.2 g]⟩, Subtype.ext ((hr r _).2 ⟨n.1, rfl⟩)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => Subtype.ext (hι r (congrArg (fun x => x.1.1) h)), fun a => ?_⟩
    obtain ⟨n, hn⟩ := (hr r a.1.1).1 (congrArg Subtype.val a.2)
    exact ⟨⟨n, fun g => hι r (by rw [he, hn, a.1.2 g])⟩, Subtype.ext (Subtype.ext hn)⟩
  exact ⟨Finite.of_surjective f hf.2, (hc r h).trans (Nat.card_eq_of_bijective f hf)⟩

end Core

section Twist

variable {l : ℕ} [Fact l.Prime]

def redChar {Γ : Type} [Group Γ] (ψ : Γ →* ℤ_[l]ˣ) (r : ℕ) : Γ →* (ZMod (l ^ r))ˣ :=
  (Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp ψ

theorem redChar_coe {Γ : Type} [Group Γ] (ψ : Γ →* ℤ_[l]ˣ) (r : ℕ) (g : Γ) :
    ((redChar ψ r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) = PadicInt.toZModPow r (ψ g : ℤ_[l]) := rfl

local instance neZero_prime_pow (r : ℕ) : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

local instance finite_tdual (r : ℕ) : Finite (TDual (ZMod (l ^ r)) (ZMod (l ^ r))) := DFunLike.finite _

theorem exists_iota {Γ : Type} [Group Γ] (χ : Γ →* ℤ_[l]ˣ) (e : ℤ) (r : ℕ) :
    ∃ ι : TDual (ZMod (l ^ r)) (ZMod (l ^ r)) →+ QZ l, Function.Injective ι ∧
      (∀ a : QZ l, (l : ℤ_[l]) ^ r • a = 0 ↔ a ∈ Set.range ι) ∧
      ∀ g n, ι (twDual (redChar χ r) (charRep (redChar (χ ^ (e + 1)) r)) g n) =
        scalRep (QZ l) (χ ^ (-e)) g (ι n) := by
  obtain ⟨ι, h1, h2, h3⟩ := (GlobalTheory.T.qz_torsion_and_exists_zmod_pow_embedding l).2 r
  let ev : TDual (ZMod (l ^ r)) (ZMod (l ^ r)) →+ ZMod (l ^ r) :=
    { toFun := fun φ => φ 1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hlin : ∀ (φ : TDual (ZMod (l ^ r)) (ZMod (l ^ r))) (m : ZMod (l ^ r)), φ m = m * φ 1 :=
    fun φ m => by
      have := LinearMap.map_smul (show ZMod (l ^ r) →ₗ[ZMod (l ^ r)] ZMod (l ^ r) from φ) m 1
      rw [smul_eq_mul, mul_one, smul_eq_mul] at this
      exact this
  have hev : Function.Bijective ev := by
    refine ⟨fun φ ψ h => TDual.ext fun m => ?_, fun y => ⟨y • TDual.mk LinearMap.id, ?_⟩⟩
    · rw [hlin φ, hlin ψ]; exact congrArg _ h
    · exact mul_one y
  refine ⟨ι.comp ev, h1.comp hev.1, fun a => ?_, fun g n => ?_⟩
  · rw [h2, AddMonoidHom.coe_comp, hev.2.range_comp]
  · change ι (_ * n (_ * 1)) = (((χ ^ (-e)) g : ℤ_[l]ˣ) : ℤ_[l]) • ι (n 1)
    rw [← h3, mul_one, hlin n, ← mul_assoc, redChar_coe, redChar_coe, ← map_mul, ← Units.val_mul]
    congr 4
    simp only [MonoidHom.zpow_apply, map_inv]
    group

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem finite_cohomology_and_card_H2_eq_card_H0_dual (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (hv : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)
    (hA : IsPlaceOver A v) (r : ℕ) (hr : 0 < r) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (Dec (F := F) A) M) (hρ : ContAction ρ)
    (τ : Representation (ZMod (l ^ r)) (Dec (F := F) A) (TDual (ZMod (l ^ r)) M))
    (hτ : ∀ g φ m, τ g φ m = (cycMod F Ω l r g : ZMod (l ^ r)) * φ (ρ g⁻¹ m)) :
    Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Subsingleton (Hn ρ 3) ∧ Nat.card (H2 ρ) = Nat.card (H0 τ) := by
  obtain ⟨K, hK, e, he, he', hc⟩ := GlobalTheory.T.decompositionGroup_mulEquiv_localGalois_cyclotomic F Ω l v A hv hA
  let ρK : Representation (ZMod (l ^ r)) (GK l K) M := ρ.comp e.symm.toMonoidHom
  have hρK : ContAction ρK := hρ.comp' he'
  obtain ⟨-, f1, f2, f3⟩ := hF l K hK r M ρK hr hρK
  obtain ⟨⟨j⟩, -, -, -, hb⟩ := hT l K hK r M ρK hr hρK
  obtain ⟨⟨e1⟩, ⟨e2⟩, e3⟩ := GlobalTheory.T.nonempty_H1_H2_equiv_of_continuous_mulEquiv _ _ _ M e he he' ρK ρ fun g m => by simp [ρK]
  refine ⟨Finite.of_equiv _ e1, Finite.of_equiv _ e2, e3 (f3 3 le_rfl), ?_⟩
  have hfin : Finite (TDual (ZMod (l ^ r)) M) := DFunLike.finite _
  have hH : H0 τ = H0 ((twDual (cycK l K r) ρK).comp (MonoidHom.id _)) := by
    have key : ∀ g φ, τ g φ = twDual (cycK l K r) ρK (e g) φ := fun g φ => TDual.ext fun m => by
      rw [hτ, twDual_apply, hc]
      simp [ρK]
    ext φ
    rw [mem_riemannRochSpace_iff_regularAt_everywhere, mem_riemannRochSpace_iff_regularAt_everywhere]
    refine ⟨fun h g => ?_, fun h g => (key g φ).trans (h (e g))⟩
    obtain ⟨g, rfl⟩ := e.surjective g
    exact (key g φ).symm.trans (h g)
  let E : H2 ρK ≃ Module.Dual (ZMod (l ^ r)) (H0 ((twDual (cycK l K r) ρK).comp (MonoidHom.id _))) :=
    (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight j).toEquiv
  rw [← Nat.card_congr e2, Nat.card_congr E, GlobalTheory.T.card_dual_zmod_module_eq_card, hH]

omit [IsAlgClosure F Ω] in
theorem chi_loc (D : LData F Ω l) (v : D.S) (g : Dec (F := F) (D.A v)) :
    D.chi (locFam D.S D.A v g) = cycZ F Ω l g := DFunLike.congr_fun D.hchi (g : G F Ω)

omit [IsAlgClosure F Ω] in
theorem mem_above (D : LData F Ω l) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ D.S ↔ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  rw [← Finset.mem_coe, D.hS]; rfl

theorem continuous_chi (D : LData F Ω l) (n : ℤ) :
    Continuous fun g => (((D.chi ^ n) g : ℤ_[l]ˣ) : ℤ_[l]) := by
  have hc : Continuous D.chi := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    have : (D.chi ∘ QuotientGroup.mk : G F Ω → _) = cycZ F Ω l := by rw [← D.hchi]; rfl
    rw [this]; exact continuous_cycZ F Ω l
  exact Units.continuous_val.comp (hc.zpow n)

theorem contAction_zlTw (D : LData F Ω l) (n : ℤ) : ContAction (zlTw D n) :=
  ((continuous_chi D n).comp continuous_fst).mul continuous_snd

abbrev zr (D : LData F Ω l) (n : ℤ) (r : ℕ) :
    Representation (ZMod (l ^ r)) (GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) (ZMod (l ^ r)) :=
  charRep (redChar (D.chi ^ n) r)

theorem contAction_zr (D : LData F Ω l) (n : ℤ) (r : ℕ) : ContAction (zr D n r) :=
  ((GlobalTheory.Published.PoitouTate.continuous_toZModPow.comp (continuous_chi D n)).comp continuous_fst).mul
    continuous_snd

omit [IsAlgClosure F Ω] in
theorem red_zlTw (D : LData F Ω l) (n : ℤ) (r : ℕ) (g) (x : ℤ_[l]) :
    PadicInt.toZModPow r (zlTw D n g x) = zr D n r g (PadicInt.toZModPow r x) := map_mul _ _ _

abbrev zd (D : LData F Ω l) (n : ℤ) (r : ℕ) := twDual (redChar D.chi r) (zr D n r)

theorem local_zr (hF : LocalFinitenessK) (hT : LocalTateDualityK) (D : LData F Ω l) (n : ℤ)
    (v : D.S) (r : ℕ) (hr : 0 < r) :
    Finite (H1 ((zr D n r).comp (locFam D.S D.A v))) ∧
    Finite (H2 ((zr D n r).comp (locFam D.S D.A v))) ∧
    Subsingleton (Hn ((zr D n r).comp (locFam D.S D.A v)) 3) ∧
    Nat.card (H2 ((zr D n r).comp (locFam D.S D.A v))) =
      Nat.card (H0 ((zd D n r).comp (locFam D.S D.A v))) :=
  finite_cohomology_and_card_H2_eq_card_H0_dual hF hT v.1 (D.A v) ((mem_above D v.1).1 v.2) (D.hA v) r hr _ _
    ((contAction_zr D n r).comp' (continuous_locFam D.S D.A v)) _ fun g φ m => by
      change ((redChar D.chi r (locFam D.S D.A v g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * _ = _
      rw [redChar_coe, chi_loc, ← map_inv]
      rfl

abbrev redLoc (D : LData F Ω l) (n : ℤ) (v : D.S) (r : ℕ) :=
  reduceH2ModPrimePow ((zlTw D n).comp (locFam D.S D.A v)) r ((zr D n r).comp (locFam D.S D.A v))
    fun g x => red_zlTw D n r (locFam D.S D.A v g) x

theorem local_lim (hF : LocalFinitenessK) (hT : LocalTateDualityK) (D : LData F Ω l) (n : ℤ)
    (v : D.S) : Module.Finite ℤ_[l] (H2 ((zlTw D n).comp (locFam D.S D.A v))) ∧
      ∀ r, Function.Surjective (redLoc D n v r) ∧
        ∀ x, redLoc D n v r x = 0 ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x := by
  have hc : ContAction ((zlTw D n).comp (locFam D.S D.A v)) := (contAction_zlTw D n).comp (((continuous_locFam D.S D.A v).comp
    continuous_fst).prodMk continuous_snd)
  exact ⟨finite_h2_padic_representation _ hc (fun r => (zr D n r).comp (locFam D.S D.A v))
      (fun r g x => red_zlTw D n r _ x) (fun r hr => (local_zr hF hT D n v r hr).1)
      (local_zr hF hT D n v 1 one_pos).2.1 (local_zr hF hT D n v 1 one_pos).2.2.1,
    fun r => ⟨reduction_h2_surjective _ hc (fun r => (zr D n r).comp (locFam D.S D.A v))
      (fun r g x => red_zlTw D n r _ x) (local_zr hF hT D n v 1 one_pos).2.2.1 r,
      reduction_h2_eq_zero_iff _ hc r _ _⟩⟩

theorem local_tate_duality_h2_limit (hF : LocalFinitenessK) (hT : LocalTateDualityK) (D : LData F Ω l) (e : ℤ) :
    TateLocalDualityH2AtPlaces D e := by
  intro v
  obtain ⟨hfg, h⟩ := local_lim hF hT D (e + 1) v
  choose ι h1 h2 h3 using exists_iota D.chi e
  exact length_eq_length_invariants_of_torsion_levels _ (GlobalTheory.T.qz_torsion_and_exists_zmod_pow_embedding l).1 _ (fun r => (zd D (e + 1) r).comp (locFam D.S D.A v)) ι
    h1 h2 (fun r g n => h3 r _ n) fun r hr =>
      (card_quot_lpow r _ (h r).1 (h r).2).trans (local_zr hF hT D (e + 1) v r hr).2.2.2

end Twist

section Global

open GlobalTheory.Published GlobalTheory.Published.PoitouTate

attribute [local instance] neZero_prime_pow finite_tdual

variable {l : ℕ} [Fact l.Prime]
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem finite_of_ker {R X Y : Type} [Ring R] [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] [Finite Y] (f : X →ₗ[R] Y) [Finite (LinearMap.ker f)] : Finite X := by
  have : Finite (X ⧸ LinearMap.ker f) := Finite.of_equiv _ f.quotKerEquivRange.toEquiv.symm
  refine Nat.finite_of_card_ne_zero ?_
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)]
  exact mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

omit [IsAlgClosure F Ω] in
theorem redChar_chi (D : LData F Ω l) (r : ℕ) :
    (redChar D.chi r).comp (toGS Ω _) = cycMod F Ω l r := by
  rw [redChar, MonoidHom.comp_assoc, D.hchi]; rfl

variable (D : LData F Ω l) (e : ℤ)
  (hF : LocalFinitenessK) (hT : LocalTateDualityK)
  (hN : ∀ r, 0 < r → ∃ j, NineTermExact D.S D.A (redChar D.chi r) j (zr D (e + 1) r)
    (contAction_zr D (e + 1) r))
  (hS : ∀ r, 0 < r → ShaDual D.S D.A (redChar D.chi r) (zr D (e + 1) r))
  (h3 : Subsingleton (Hn (zr D (e + 1) 1) 3))

abbrev redGl (r : ℕ) := reduceH2ModPrimePow (zlTw D (e + 1)) r (zr D (e + 1) r) (red_zlTw D (e + 1) r)

include hF hT hS h3 in
theorem global_lim : Module.Finite ℤ_[l] (H2 (zlTw D (e + 1))) ∧
    ∀ r, Function.Surjective (redGl D e r) ∧
      ∀ x, redGl D e r x = 0 ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x := by
  have hc := contAction_zlTw D (e + 1)
  refine ⟨finite_h2_padic_representation _ hc (zr D (e + 1)) (red_zlTw D (e + 1)) (fun r hr => ?_) ?_ h3,
    fun r => ⟨reduction_h2_surjective _ hc (zr D (e + 1)) (red_zlTw D (e + 1)) h3 r,
      reduction_h2_eq_zero_iff _ hc r _ _⟩⟩
  · have := fun v => (local_zr hF hT D (e + 1) v r hr).1
    have : Finite (LinearMap.ker (loc1 D.S D.A (zr D (e + 1) r))) := by
      rw [loc1, LinearMap.ker_pi]; exact (hS r hr).2.1
    exact finite_of_ker (loc1 D.S D.A (zr D (e + 1) r))
  · have := fun v => (local_zr hF hT D (e + 1) v 1 one_pos).2.1
    have : Finite (LinearMap.ker (loc2 D.S D.A (zr D (e + 1) 1))) := by
      rw [loc2, LinearMap.ker_pi]; exact (hS 1 one_pos).1.2.1
    exact finite_of_ker (loc2 D.S D.A (zr D (e + 1) 1))

def redPi (r : ℕ) : (∀ v : D.S, H2 ((zlTw D (e + 1)).comp (locFam D.S D.A v))) →+
    ∀ v : D.S, H2 ((zr D (e + 1) r).comp (locFam D.S D.A v)) :=
  AddMonoidHom.pi fun v => (redLoc D (e + 1) v r).comp (Pi.evalAddMonoidHom _ v)

include hF hT hS h3 in
theorem cok_ker (r : ℕ) :
    Nat.card ((_ ⧸ LinearMap.range (localH2 D e)) ⧸ lpow l (_ ⧸ LinearMap.range (localH2 D e)) r) =
      Nat.card (_ ⧸ LinearMap.range (loc2 D.S D.A (zr D (e + 1) r))) ∧
    ((∀ x p, localH2 D e x = (l : ℤ_[l]) ^ r • p → ∃ x', localH2 D e x = (l : ℤ_[l]) ^ r • localH2 D e x') →
      Nat.card (LinearMap.ker (localH2 D e) ⧸ (lpow l _ r).comap (LinearMap.ker (localH2 D e)).subtype) =
        Nat.card (LinearMap.ker (loc2 D.S D.A (zr D (e + 1) r)))) := by
  have hg := (global_lim D e hF hT hS h3).2 r
  have hl := fun v => (local_lim hF hT D (e + 1) v).2 r
  refine GlobalTheory.T.natCard_coker_ker_padic_mod_pow l r _ _ (localH2 D e) _ _ _ (loc2 D.S D.A (zr D (e + 1) r)) (redGl D e r)
    (redPi D e r) hg.1 (fun y => ?_) hg.2 (fun x => ?_) fun x => ?_
  · choose x hx using fun v => (hl v).1 (y v)
    exact ⟨x, funext hx⟩
  · constructor
    · intro h
      choose y hy using fun v => ((hl v).2 (x v)).1 (congrFun h v)
      exact ⟨y, funext hy⟩
    · rintro ⟨y, hy⟩
      exact funext fun v => ((hl v).2 (x v)).2 ⟨y v, congrFun hy v⟩
  · induction x using Submodule.Quotient.induction_on with
    | H z => rfl

include hF hT hN hS h3 in
theorem card_cok (r : ℕ) (hr : 0 < r) :
    Nat.card ((_ ⧸ LinearMap.range (localH2 D e)) ⧸ lpow l (_ ⧸ LinearMap.range (localH2 D e)) r) =
      Nat.card (H0 (zd D (e + 1) r)) := by
  obtain ⟨j, _, _, -, -, -, -, -, -, -, hex, hs⟩ := hN r hr
  rw [(cok_ker D e hF hT hS h3 r).1, ← LinearMap.exact_iff.1 hex,
    Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ hs).toEquiv, GlobalTheory.T.card_dual_zmod_module_eq_card]

include hF hT in
theorem finite_pi : Module.Finite ℤ_[l] (∀ v : D.S, H2 ((zlTw D (e + 1)).comp (locFam D.S D.A v))) :=
  have := fun v => (local_lim hF hT D (e + 1) v).1
  inferInstance

include hF hT hN hS h3 in
theorem ptCokerAt : PTCokerAt D e := by
  intro _
  have := finite_pi D e hF hT
  choose ι h1 h2 h4 using exists_iota D.chi e
  exact length_eq_length_invariants_of_torsion_levels _ (GlobalTheory.T.qz_torsion_and_exists_zmod_pow_embedding l).1 _ (zd D (e + 1)) ι h1 h2 h4 (card_cok D e hF hT hN hS h3)

theorem exists_kill (he : e ≠ 0) : ∃ c : ℕ, ∀ (v : D.S) (a : QZ l),
    (∀ g, qzTw D e (locFam D.S D.A v g) a = a) → (l : ℤ_[l]) ^ c • a = 0 := by
  have h : ∀ v : D.S, ∃ c : ℕ, ∀ a : QZ l,
      (∀ g, qzTw D e (locFam D.S D.A v g) a = a) → (l : ℤ_[l]) ^ c • a = 0 := fun v => by
    obtain ⟨g, hg, hne⟩ := GlobalTheory.T.exists_decompositionGroup_cyclotomicCharacter_zpow_ne_one F Ω l v.1 (D.A v) ((mem_above D v.1).1 v.2) (D.hA v) (-e)
      (neg_ne_zero.2 he)
    have hx : ((cycZ F Ω l g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) - 1 ≠ 0 :=
      sub_ne_zero.2 fun h => hne (Units.ext h)
    refine ⟨(((cycZ F Ω l g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) - 1).valuation, fun a ha => ?_⟩
    · have h1 : ((D.chi (locFam D.S D.A v ⟨g, hg⟩) ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • a = a := ha ⟨g, hg⟩
      rw [chi_loc] at h1
      have h2 : (((cycZ F Ω l g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) - 1) • a = 0 := by
        rw [sub_smul, one_smul, sub_eq_zero]; exact h1
      rw [PadicInt.unitCoeff_spec hx, mul_smul] at h2
      exact (Units.isUnit _).smul_eq_zero.1 h2
  choose c hc using h
  obtain ⟨m, hm⟩ := (Set.finite_range c).bddAbove
  refine ⟨m, fun v a ha => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (hm ⟨v, rfl⟩)
  rw [hk, pow_add, mul_smul, hc v a ha, smul_zero]

omit [IsAlgClosure F Ω] in
theorem nonempty_S : Nonempty D.S := by
  have hu : ¬ IsUnit ((l : ℕ) : 𝓞 F) := fun h => by
    have h1 := h.map (Algebra.norm ℤ)
    rw [← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap,
      isUnit_pow_iff (by rw [RingOfIntegers.rank]; exact Module.finrank_pos.ne'), Int.isUnit_iff_natAbs_eq,
      Int.natAbs_natCast] at h1
    exact (Fact.out : l.Prime).one_lt.ne' h1
  obtain ⟨m, hm, hl⟩ := Ideal.exists_le_maximal (Ideal.span {((l : ℕ) : 𝓞 F)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hl' := hl (Ideal.mem_span_singleton_self _)
  have h0 : m ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hl'
    exact (Fact.out : l.Prime).ne_zero (Nat.cast_eq_zero.1 hl')
  exact ⟨⟨⟨m, hm.isPrime, h0⟩, (mem_above D _).2 hl'⟩⟩

include hF hT in

theorem exists_kill_pi (he : e ≠ 0) : ∃ m : ℕ,
    ∀ p : ∀ v : D.S, H2 ((zlTw D (e + 1)).comp (locFam D.S D.A v)), (l : ℤ_[l]) ^ m • p = 0 := by
  obtain ⟨c, hc⟩ := exists_kill D e he
  obtain ⟨ι, -, h2, -⟩ := exists_iota D.chi e c
  have hart : ∀ v : D.S, IsArtinian ℤ_[l] (H2 ((zlTw D (e + 1)).comp (locFam D.S D.A v))) :=
    fun v => by
      have : Finite (H0 ((qzTw D e).comp (locFam D.S D.A v))) :=
        ((Set.finite_range ι).subset fun a ha => (h2 a).1 (hc v a ha)).to_subtype
      have h := local_tate_duality_h2_limit hF hT D e v
      have h' : Module.length ℤ_[l] (H0 ((qzTw D e).comp (locFam D.S D.A v))) ≠ ⊤ :=
        Module.length_ne_top
      rw [← h, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at h'
      exact h'.2
  have := finite_pi D e hF hT
  obtain ⟨m, hm⟩ := IsArtinian.monotone_stabilizes (R := ℤ_[l])
    (M := ∀ v : D.S, H2 ((zlTw D (e + 1)).comp (locFam D.S D.A v)))
    ⟨fun r => OrderDual.toDual (lpow l _ r), fun r s h => lpow_anti _ h⟩
  refine ⟨m, fun p => lpow_sep (l := l) _ _ fun r => ?_⟩
  have hp : (l : ℤ_[l]) ^ m • p ∈ lpow l _ m := ⟨p, rfl⟩
  rcases le_total m r with h | h
  · exact (OrderDual.toDual.injective (hm r h)).le hp
  · exact lpow_anti _ h hp

include hF hT hN hS h3 in
theorem ptShaAt : PTShaAt D e := by
  intro _
  have hX := (global_lim D e hF hT hS h3).1
  have hP := finite_pi D e hF hT
  have hgal : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  choose ι h1 h2 h4 using exists_iota D.chi e
  obtain ⟨P, hm, hu, hc⟩ := GlobalTheory.T.sha1_torsion_level_filtration l _ D.S _ (locFam D.S D.A) (continuous_locFam D.S D.A)
    (QZ l) (qzTw D e) (GlobalTheory.T.qz_torsion_and_exists_zmod_pow_embedding l).1
  have key : ∃ c : ℕ, ∀ r, c ≤ r →
      (∀ x p, localH2 D e x = (l : ℤ_[l]) ^ r • p →
        ∃ x', localH2 D e x = (l : ℤ_[l]) ^ r • localH2 D e x') ∧
      ∀ a : QZ l, (∀ v, ∃ b : QZ l, (l : ℤ_[l]) ^ r • b = 0 ∧ ∀ g,
        qzTw D e (locFam D.S D.A v g) a - a = qzTw D e (locFam D.S D.A v g) b - b) →
        ∃ b : QZ l, (l : ℤ_[l]) ^ r • b = 0 ∧ ∀ g, qzTw D e g a - a = qzTw D e g b - b := by
    rcases eq_or_ne e 0 with he | he
    · have htr : ∀ g a, qzTw D e g a = a := fun g a => by simp [qzTw, he]
      have htf := GlobalTheory.T.padicInt_eq_zero_of_pow_smul_of_card_quotient l (_ ⧸ LinearMap.range (localH2 D e)) fun r hr => by
        have hH : H0 (zd D (e + 1) r) = ⊤ :=
          eq_top_iff.2 fun n _ g => h1 r ((h4 r g n).trans (htr g _))
        rw [card_cok D e hF hT hN hS h3 r hr, hH, Nat.card_congr Submodule.topEquiv.toEquiv]
        exact (GlobalTheory.T.card_dual_zmod_module_eq_card (l ^ r) (ZMod (l ^ r))).trans (Nat.card_zmod _)
      refine ⟨0, fun r _ => ⟨fun x p h => ?_, fun a _ => ⟨0, smul_zero _, fun g => ?_⟩⟩⟩
      · obtain ⟨x', hx'⟩ := (Submodule.Quotient.mk_eq_zero _).1 (htf r (Submodule.Quotient.mk p) (by
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact ⟨x, h⟩))
        exact ⟨x', by rw [hx', h]⟩
      · rw [htr, htr, sub_self, sub_self]
    · obtain ⟨c, hc⟩ := exists_kill D e he
      obtain ⟨m, hm⟩ := exists_kill_pi D e hF hT he
      refine ⟨c + m, fun r hr => ?_⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hr
      refine ⟨fun x p h => ⟨0, ?_⟩, fun a ha => ⟨a, ?_, fun _ => rfl⟩⟩
      · rw [h, map_zero, smul_zero, ← add_assoc, pow_add, mul_smul, hm, smul_zero]
      · obtain ⟨v⟩ := nonempty_S D
        obtain ⟨b, hb, hab⟩ := ha v
        have h0 := hc v (a - b) fun g => by
          rw [map_sub, sub_eq_sub_iff_sub_eq_sub]; exact hab g
        have h5 : (l : ℤ_[l]) ^ (k + (c + m)) • (a - b) = 0 := by
          rw [add_comm c m, ← add_assoc, pow_add, mul_smul, h0, smul_zero]
        rwa [smul_sub, hb, sub_zero] at h5
  obtain ⟨c, key⟩ := key
  have hker : Sha2Zl D e = LinearMap.ker (localH2 D e) := by rw [localH2, LinearMap.ker_pi]; rfl
  rw [hker]
  refine GlobalTheory.T.padicInt_length_eq_of_card_quotient_eq l _ _ (fun r => (lpow l _ r).comap (LinearMap.ker (localH2 D e)).subtype) P
    (c + 1) (fun r s h => Submodule.comap_mono (lpow_anti _ h))
    (fun x hx => Subtype.ext (lpow_sep (l := l) _ _ hx)) hm hu fun r hr => ?_
  obtain ⟨k1, k2⟩ := key r (by omega)
  obtain ⟨⟨f1, -, -, f2⟩, -⟩ := hS r (by omega)
  have e1 := hc r _ _ (zd D (e + 1) r) (ι r) (h1 r) (h2 r) (h4 r) k2
  refine ⟨Nat.finite_of_card_ne_zero (e1.trans_ne Nat.card_pos.ne'), ?_⟩
  refine ((cok_ker D e hF hT hS h3 r).2 k1).trans (Eq.trans ?_ (e1.trans f2).symm)
  rw [loc2, LinearMap.ker_pi]
  rfl

omit hN hS h3 in

theorem finite_level (hP : PoitouTateDuality) (hc : PTCase F l) (r : ℕ) (hr : 0 < r) :
    (∃ j, NineTermExact D.S D.A (redChar D.chi r) j (zr D (e + 1) r) (contAction_zr D (e + 1) r)) ∧
    ShaDual D.S D.A (redChar D.chi r) (zr D (e + 1) r) ∧ Subsingleton (Hn (zr D (e + 1) r) 3) := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_pow F Ω l r
  obtain ⟨inv, -, h⟩ := hP F Ω l r (hc.imp id fun h => (NumberField.nrRealPlaces_eq_zero_iff).1 h)
    hr ζ hζ
  obtain ⟨a, b, c⟩ := h D.S (fun v hv => (mem_above D v).2 hv) D.A D.hA _ (redChar_chi D r) _ _
    (contAction_zr D (e + 1) r)
  exact ⟨⟨_, a⟩, b, c 3 le_rfl⟩

end Global

theorem archimedeanSignatureMatching_of_poitouTate (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK)
    (hT : LocalTateDualityK) (hE : LocalEulerCharK) : Formalism.MainNotions.BlochKatoReduction.Gen.ArchimedeanSignatureMatching :=
  ⟨fun _ _ _ _ _ _ _ _ _ D e hc => ptCokerAt D e hF hT (fun r hr => (finite_level D e hP hc r hr).1)
      (fun r hr => (finite_level D e hP hc r hr).2.1) (finite_level D e hP hc 1 one_pos).2.2 hc,
    fun _ _ _ _ _ _ _ _ _ D e hc => ptShaAt D e hF hT (fun r hr => (finite_level D e hP hc r hr).1)
      (fun r hr => (finite_level D e hP hc r hr).2.1) (finite_level D e hP hc 1 one_pos).2.2 hc,
    fun _ _ _ _ _ _ _ _ _ D e => local_tate_duality_h2_limit hF hT D e, hF, hT, hE⟩

theorem twist_cohomology_inputs : GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK →
    LocalEulerCharK → Formalism.MainNotions.BlochKatoReduction.Gen.ArchimedeanSignatureMatching ∧ Formalism.MainNotions.BlochKatoReduction.ArchimedeanSignatureMatching :=
  fun hP hF hT hE => ⟨archimedeanSignatureMatching_of_poitouTate hP hF hT hE, archimedeanSignatureMatching_of_poitouTate hP hF hT hE⟩

end GlobalTheory.TateLimit
