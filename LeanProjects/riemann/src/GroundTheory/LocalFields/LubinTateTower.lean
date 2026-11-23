import Mathlib
import GroundTheory.LocalFields.LubinTatePoints
import GroundTheory.LocalFields.LubinTateTorsion
import GroundTheory.LocalFields.Eisenstein
import GroundTheory.LocalFields.UnitsBasic

noncomputable section

open IntermediateField

namespace GroundTheory.LocalField

open ValuativeRel Polynomial

namespace FormalGroup

section Tower

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} {f g : PowerSeries 𝒪[K]}

variable (Ω) in

def lubinTateField (hπ : Irreducible π) (hf : IsLubinTateSeries π f) (n : ℕ) :
    IntermediateField K Ω :=
  adjoin K (IdealPoint.val ''
    (lubinTateTorsion Ω hf n : Set (IdealPoint Ω (lubinTateFormalGroup hπ hf))))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem finiteDimensional_adjoin_simple (x : Ω) : FiniteDimensional K K⟮x⟯ :=
  adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral

theorem val_mem_lubinTateField (hπ : Irreducible π) (hf : IsLubinTateSeries π f) {n : ℕ}
    {x : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hx : x ∈ lubinTateTorsion Ω hf n) :
    x.val ∈ lubinTateField Ω hπ hf n :=
  subset_adjoin K _ (Set.mem_image_of_mem IdealPoint.val (SetLike.mem_coe.mpr hx))

theorem psEval_mem_adjoin_simple (φ : PowerSeries 𝒪[K]) {x : Ω} (hx : valuation Ω x < 1) :
    psEval φ (fun _ => x) ∈ K⟮x⟯ :=
  have := finiteDimensional_adjoin_simple (K := K) x
  psEval_mem φ K⟮x⟯ (fun _ => mem_adjoin_simple_self K x) fun _ => hx

variable (hπ : Irreducible π)

section SepClosed

variable [IsSepClosed Ω]

theorem exists_lubinTateField_eq_adjoin (hf : IsLubinTateSeries π f) (n : ℕ) :
    ∃ l ∈ lubinTateTorsion Ω (hπ := hπ) hf n,
      (∀ a : 𝒪[K], a • l = 0 ↔ a ∈ Ideal.span {π ^ n}) ∧
      (∀ m ∈ lubinTateTorsion Ω (hπ := hπ) hf n, ∃ a : 𝒪[K], a • l = m) ∧
      lubinTateField Ω hπ hf n = K⟮l.val⟯ := by
  obtain ⟨l, hl, hann, hgen⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  refine ⟨l, hl, hann, hgen, le_antisymm ?_ ?_⟩
  · rw [lubinTateField, adjoin_le_iff]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨a, rfl⟩ := hgen m hm
    rw [lubinTate_smul_val]
    exact psEval_mem_adjoin_simple _ l.valuation_lt_one
  · rw [adjoin_simple_le_iff]
    exact subset_adjoin K _ (Set.mem_image_of_mem IdealPoint.val (SetLike.mem_coe.mpr hl))

instance finiteDimensional_lubinTateField (hf : IsLubinTateSeries π f) (n : ℕ) :
    FiniteDimensional K (lubinTateField Ω hπ hf n) := by
  obtain ⟨l, -, -, -, h⟩ := exists_lubinTateField_eq_adjoin (Ω := Ω) hπ hf n
  rw [h]
  exact finiteDimensional_adjoin_simple _

theorem lubinTateField_eq (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g) (n : ℕ) :
    lubinTateField Ω hπ hf n = lubinTateField Ω hπ hg n := by
  have key : ∀ {f g : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)
      (hg : IsLubinTateSeries π g), lubinTateField Ω hπ hf n ≤ lubinTateField Ω hπ hg n := by
    intro f g hf hg
    rw [lubinTateField, adjoin_le_iff]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨m', rfl⟩ := (lubinTatePointEquiv hf hg).surjective m
    have hm' : m' ∈ lubinTateTorsion Ω hg n :=
      (lubinTatePointEquiv_mem_torsion_iff hf hg n m').mp hm
    rw [SetLike.mem_coe, lubinTatePointEquiv_val]
    exact psEval_mem _ _ (fun _ => val_mem_lubinTateField hπ hg hm')
      fun _ => m'.valuation_lt_one
  exact le_antisymm (key hf hg) (key hg hf)

omit [IsSepClosed Ω] in

theorem image_val_lubinTateTorsion_ltPoly (n : ℕ) :
    IdealPoint.val '' (lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) n :
      Set (IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π)))) =
      ((ltPolyIter π n).map (algebraMap 𝒪[K] K)).rootSet Ω := by
  have hp0 : (ltPolyIter π n).map (algebraMap 𝒪[K] K) ≠ 0 :=
    ((ltPolyIter_monic π n).1.map _).ne_zero
  ext z
  rw [mem_rootSet']
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Polynomial.map_ne_zero hp0, (mem_lubinTateTorsion_ltPoly_iff n x).mp hx⟩
  · rintro ⟨-, hz⟩
    exact ⟨IdealPoint.mk z (valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n hz),
      (mem_lubinTateTorsion_ltPoly_iff n _).mpr hz, rfl⟩

instance isGalois_lubinTateField (hf : IsLubinTateSeries π f) (n : ℕ) :
    IsGalois K (lubinTateField Ω hπ hf n) := by
  rw [lubinTateField_eq hπ hf (isLubinTateSeries_ltPoly π), lubinTateField,
    image_val_lubinTateTorsion_ltPoly hπ n]
  have hsep := separable_ltPolyIter hπ n
  have := adjoin_rootSet_isSplittingField (IsSepClosed.splits_codomain _ hsep)
    (L := Ω) (K := K)
  exact IsGalois.of_separable_splitting_field hsep

theorem exists_lubinTateField_eq_adjoin_eisenstein (hf : IsLubinTateSeries π f) (n : ℕ) :
    ∃ α : Ω, lubinTateField Ω hπ hf (n + 1) = K⟮α⟯ ∧
      aeval α ((ltEisenstein π n).map (algebraMap 𝒪[K] K)) = 0 := by
  obtain ⟨l, hl, hann, -, hE⟩ :=
    exists_lubinTateField_eq_adjoin (Ω := Ω) hπ (isLubinTateSeries_ltPoly π) (n + 1)
  refine ⟨l.val, (lubinTateField_eq hπ hf (isLubinTateSeries_ltPoly π) _).trans hE, ?_⟩
  refine aeval_ltEisenstein_eq_zero ((mem_lubinTateTorsion_ltPoly_iff _ l).mp hl) fun h => ?_
  have h1 : π ^ n • l = 0 := (mem_lubinTateTorsion _ _ _).mp
    ((mem_lubinTateTorsion_ltPoly_iff n l).mpr h)
  rw [hann, Ideal.mem_span_singleton, pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit] at h1
  omega

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
  [IsSepClosed Ω] in

theorem adjoin_simple_eq_top_of_eq {E : IntermediateField K Ω} {a : Ω} (hE : E = K⟮a⟯) :
    K⟮(⟨a, hE ▸ mem_adjoin_simple_self K a⟩ : E)⟯ = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  have hy : (y : Ω) ∈ (K⟮(⟨a, hE ▸ mem_adjoin_simple_self K a⟩ : E)⟯).map E.val := by
    rw [adjoin_map, Set.image_singleton]
    change (y : Ω) ∈ K⟮a⟯
    rw [← hE]
    exact y.2
  rw [IntermediateField.mem_map] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  rwa [show z = y from Subtype.ext hzy] at hz

theorem finrank_and_ramificationIndex_lubinTateField_succ (hf : IsLubinTateSeries π f) (n : ℕ) :
    Module.finrank K (lubinTateField Ω hπ hf (n + 1)) = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n ∧
      ramificationIndex K (lubinTateField Ω hπ hf (n + 1)) =
        (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
  obtain ⟨a, hE, ha⟩ := exists_lubinTateField_eq_adjoin_eisenstein (Ω := Ω) hπ hf n
  set E := lubinTateField Ω hπ hf (n + 1)
  set α : E := ⟨a, hE ▸ mem_adjoin_simple_self K a⟩
  have hgen : K⟮α⟯ = ⊤ := adjoin_simple_eq_top_of_eq hE
  have hα : aeval α (ltEisenstein π n) = 0 := by
    refine Subtype.val_injective ?_
    have h2 := aeval_algHom_apply (E.val.restrictScalars 𝒪[K]) α (ltEisenstein π n)
    simp only [AlgHom.coe_restrictScalars', coe_val] at h2
    rw [ZeroMemClass.coe_zero, ← h2]
    change aeval a (ltEisenstein π n) = 0
    rwa [← aeval_map_algebraMap K]
  have hq := one_lt_card_residueField' K
  have hn : 0 < (ltEisenstein π n).natDegree := by
    rw [(ltEisenstein_monic π n).2]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) n)
  have hEis := isEisensteinAt_ltEisenstein hπ n
  rw [← (ltEisenstein_monic π n).2]
  exact ⟨finrank_eq_natDegree_of_isEisensteinAt hEis hn hα hgen,
    ramificationIndex_eq_natDegree_of_isEisensteinAt hEis hn hα hgen⟩

end SepClosed

end Tower

section Units

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]}

theorem card_units_quotient_span_pow_succ (hπ : Irreducible π) (n : ℕ) :
    Nat.card (𝒪[K] ⧸ Ideal.span {π ^ (n + 1)})ˣ = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
  set I := Ideal.span {π ^ (n + 1)}
  have hI : I = 𝓂[K] ^ (n + 1) := by rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hIm : I ≤ 𝓂[K] := by
    rw [hI]
    exact Ideal.pow_le_self (Nat.succ_ne_zero n)
  let ψ : 𝒪[K]ˣ →* (𝒪[K] ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I : 𝒪[K] →* 𝒪[K] ⧸ I)
  have hsurj : Function.Surjective ψ := by
    intro w
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (w : 𝒪[K] ⧸ I)
    obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (↑w⁻¹ : 𝒪[K] ⧸ I)
    have huv : u * v - 1 ∈ I := by
      rw [← Ideal.Quotient.eq, map_mul, hu, hv, map_one, Units.mul_inv]
    have hunit : IsUnit (u * v) := by
      by_contra h
      have h1 : u * v ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal _).mpr h
      have h2 : (1 : 𝒪[K]) ∈ 𝓂[K] := by
        have := Ideal.sub_mem _ h1 (hIm huv)
        rwa [sub_sub_cancel] at this
      exact (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
    refine ⟨(isUnit_of_mul_isUnit_left hunit).unit, Units.ext ?_⟩
    change Ideal.Quotient.mk I u = _
    exact hu
  have hker : ψ.ker = unitFiltration K (n + 1) := by
    ext u
    rw [MonoidHom.mem_ker, mem_unitFiltration, ← hI, ← Ideal.Quotient.eq, Units.ext_iff]
    rfl
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).toEquiv, hker,
    ← Subgroup.index, index_unitFiltration K (by omega), Nat.add_sub_cancel]

end Units

section Galois

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} {hπ : Irreducible π} {f : PowerSeries 𝒪[K]}

def galPoint {F : _root_.FormalGroup 𝒪[K]} {E : IntermediateField K Ω} [FiniteDimensional K E]
    (σ : E ≃ₐ[K] E) (x : IdealPoint Ω F) (hx : x.val ∈ E) : IdealPoint Ω F :=
  IdealPoint.mk ((σ ⟨x.val, hx⟩ : E) : Ω) (by
    rw [valuation_coe_lt_one_iff, valuation_algEquiv_apply_of_isAlgebraic,
      ← valuation_coe_lt_one_iff]
    exact x.valuation_lt_one)

omit [TopologicalSpace Ω] [IsValuativeTopology Ω] in

theorem galPoint_val {F : _root_.FormalGroup 𝒪[K]} {E : IntermediateField K Ω}
    [FiniteDimensional K E] (σ : E ≃ₐ[K] E) (x : IdealPoint Ω F) (hx : x.val ∈ E) :
    (galPoint σ x hx).val = ((σ ⟨x.val, hx⟩ : E) : Ω) := rfl

theorem galPoint_smul {E : IntermediateField K Ω} [FiniteDimensional K E] (hf : IsLubinTateSeries π f)
    (σ : E ≃ₐ[K] E) (a : 𝒪[K]) (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) (hx : x.val ∈ E)
    (hax : (a • x).val ∈ E) :
    galPoint σ (a • x) hax = a • galPoint σ x hx := by
  set xE : E := ⟨x.val, hx⟩
  set φ := (lubinTateHom hπ hf hf a).toPowerSeries
  have hxE : ∀ _ : Unit, valuation Ω ((xE : E) : Ω) < 1 := fun _ => x.valuation_lt_one
  have h1 : (⟨(a • x).val, hax⟩ : E) = psEval φ fun _ => xE :=
    Subtype.ext (psEval_coe E φ (fun _ => xE) hxE)
  have hσ : ∀ _ : Unit, valuation Ω (((σ xE : E)) : Ω) < 1 := fun _ =>
    (galPoint σ x hx).valuation_lt_one
  apply IdealPoint.ext
  rw [galPoint_val, h1, algEquiv_psEval σ φ (fun _ => xE) fun _ => by
      rw [← valuation_coe_lt_one_iff]; exact x.valuation_lt_one,
    lubinTate_smul_val]
  exact (psEval_coe E φ (fun _ => σ xE) hσ).symm

variable [IsSepClosed Ω]

theorem card_units_quotient_eq_finrank (hf : IsLubinTateSeries π f) (n : ℕ) :
    Nat.card (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ = Module.finrank K (lubinTateField Ω hπ hf n) := by
  cases n with
  | zero =>
    obtain ⟨l, hl, -, -, hE⟩ := exists_lubinTateField_eq_adjoin (Ω := Ω) hπ hf 0
    rw [mem_lubinTateTorsion, pow_zero, one_smul] at hl
    rw [hE, hl, IdealPoint.val_zero, adjoin_zero, IntermediateField.finrank_bot, pow_zero,
      Ideal.span_singleton_one]
    have : Subsingleton (𝒪[K] ⧸ (⊤ : Ideal 𝒪[K])) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Nat.card_unique
  | succ n =>
    rw [card_units_quotient_span_pow_succ hπ, (finrank_and_ramificationIndex_lubinTateField_succ
      hπ hf n).1]

theorem exists_galEquiv_lubinTateField (hf : IsLubinTateSeries π f) (n : ℕ) :
    ∃ χ : (lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) ≃*
        (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ,
      ∀ (σ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n)
        (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) (hx : x ∈ lubinTateTorsion Ω hf n)
        (a : 𝒪[K]), Ideal.Quotient.mk _ a = (χ σ : 𝒪[K] ⧸ Ideal.span {π ^ n}) →
          ((σ ⟨x.val, val_mem_lubinTateField hπ hf hx⟩ : lubinTateField Ω hπ hf n) : Ω) =
            (a • x).val := by
  obtain ⟨l, hl, hann, hgen, hE⟩ := exists_lubinTateField_eq_adjoin (Ω := Ω) hπ hf n
  set E := lubinTateField Ω hπ hf n
  set Λ := lubinTateTorsion Ω (hπ := hπ) hf n
  set I := Ideal.span {π ^ n}
  have hmem : ∀ {x}, x ∈ Λ → x.val ∈ E := fun hx => val_mem_lubinTateField hπ hf hx
  have hgalΛ : ∀ (σ : E ≃ₐ[K] E) (x) (hx : x ∈ Λ), galPoint σ x (hmem hx) ∈ Λ := by
    intro σ x hx
    rw [mem_lubinTateTorsion, ← galPoint_smul hf σ _ x (hmem hx) (hmem (Λ.smul_mem _ hx))]
    apply IdealPoint.ext
    rw [galPoint_val]
    have h0 : (⟨(π ^ n • x).val, hmem (Λ.smul_mem _ hx)⟩ : E) = 0 :=
      Subtype.ext (show (π ^ n • x).val = ((0 : E) : Ω) by
        rw [(mem_lubinTateTorsion _ _ _).mp hx]; rfl)
    rw [h0, map_zero]
    rfl
  choose c hc using fun σ : E ≃ₐ[K] E => hgen _ (hgalΛ σ l hl)
  have hmk : ∀ a b : 𝒪[K], a • l = b • l ↔ Ideal.Quotient.mk I a = Ideal.Quotient.mk I b := by
    intro a b
    rw [Ideal.Quotient.eq, ← hann, sub_smul, sub_eq_zero]
  have hgal : ∀ (σ : E ≃ₐ[K] E) (x) (hx : x ∈ Λ), galPoint σ x (hmem hx) = c σ • x := by
    intro σ x hx
    obtain ⟨b, rfl⟩ := hgen x hx
    rw [galPoint_smul hf σ b l (hmem hl), ← hc, smul_comm]
  have hmul : ∀ σ τ : E ≃ₐ[K] E, c (σ * τ) • l = (c σ * c τ) • l := by
    intro σ τ
    rw [hc, mul_smul, hc]
    have h1 : galPoint (σ * τ) l (hmem hl) = galPoint σ (galPoint τ l (hmem hl))
        (hmem (hgalΛ τ l hl)) := rfl
    rw [h1, hgal σ _ (hgalΛ τ l hl), ← hc]
  have hone : c 1 • l = (1 : 𝒪[K]) • l := by
    rw [hc, one_smul]
    rfl
  let χ₀ : (E ≃ₐ[K] E) →* 𝒪[K] ⧸ I :=
    { toFun := fun σ => Ideal.Quotient.mk I (c σ)
      map_one' := by rw [(hmk _ _).mp hone, map_one]
      map_mul' := fun σ τ => by rw [(hmk _ _).mp (hmul σ τ), map_mul] }
  let χ := χ₀.toHomUnits
  have hχ : ∀ σ, (χ σ : 𝒪[K] ⧸ I) = Ideal.Quotient.mk I (c σ) := fun σ => rfl
  have hinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have h1 : c σ • l = (1 : 𝒪[K]) • l := by
      rw [hmk, map_one, ← hχ, hσ, Units.val_one]
    rw [one_smul, hc] at h1
    have hfix : σ ⟨l.val, hmem hl⟩ = ⟨l.val, hmem hl⟩ := Subtype.ext (congrArg IdealPoint.val h1)
    have htop : Algebra.adjoin K {(⟨l.val, hmem hl⟩ : E)} = ⊤ := by
      rw [← adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic _),
        adjoin_simple_eq_top_of_eq hE, top_toSubalgebra]
    have h2 := AlgHom.ext_of_adjoin_eq_top htop (φ₁ := (σ : E →ₐ[K] E)) (φ₂ := AlgHom.id K E)
      (by rintro _ rfl; exact hfix)
    exact AlgEquiv.ext fun y => congrArg (fun φ : E →ₐ[K] E => φ y) h2
  have hcard : Nat.card (E ≃ₐ[K] E) = Nat.card (𝒪[K] ⧸ I)ˣ := by
    rw [IsGalois.card_aut_eq_finrank, card_units_quotient_eq_finrank (Ω := Ω) hf n]
  have hfin : Finite (𝒪[K] ⧸ I)ˣ := Nat.finite_of_card_ne_zero (by
    rw [← hcard, IsGalois.card_aut_eq_finrank]
    exact Module.finrank_pos.ne')
  refine ⟨MulEquiv.ofBijective χ (hinj.bijective_of_nat_card_le hcard.ge), ?_⟩
  intro σ x hx a ha
  rw [MulEquiv.ofBijective_apply, hχ, ← hmk] at ha
  obtain ⟨b, rfl⟩ := hgen x hx
  rw [← galPoint_val σ (b • l) (hmem hx), hgal σ _ hx, smul_comm, ← ha, smul_comm]

variable (hπ) in

def lubinTateGalEquiv (hf : IsLubinTateSeries π f) (n : ℕ) :
    (lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) ≃* (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ :=
  Classical.choose (exists_galEquiv_lubinTateField (Ω := Ω) (hπ := hπ) hf n)

theorem lubinTateGalEquiv_spec (hf : IsLubinTateSeries π f) (n : ℕ)
    (σ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n)
    (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) (hx : x ∈ lubinTateTorsion Ω hf n) (a : 𝒪[K])
    (ha : Ideal.Quotient.mk _ a = (lubinTateGalEquiv hπ hf n σ : 𝒪[K] ⧸ Ideal.span {π ^ n})) :
    ((σ ⟨x.val, val_mem_lubinTateField hπ hf hx⟩ : lubinTateField Ω hπ hf n) : Ω) = (a • x).val :=
  Classical.choose_spec (exists_galEquiv_lubinTateField (Ω := Ω) (hπ := hπ) hf n) σ x hx a ha

end Galois

section Main

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]}

theorem finrank_lubinTateField (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    Module.finrank K (lubinTateField Ω hπ hf n) = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  exact (finrank_and_ramificationIndex_lubinTateField_succ hπ hf m).1

theorem ramificationIndex_lubinTateField (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    ramificationIndex K (lubinTateField Ω hπ hf n) =
      Module.finrank K (lubinTateField Ω hπ hf n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  rw [(finrank_and_ramificationIndex_lubinTateField_succ hπ hf m).1,
    (finrank_and_ramificationIndex_lubinTateField_succ hπ hf m).2]

theorem residueDegree_lubinTateField (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    residueDegree K (lubinTateField Ω hπ hf n) = 1 :=
  residueDegree_eq_one_of_ramificationIndex_eq_finrank K _
    (ramificationIndex_lubinTateField hπ hf hn)

theorem exists_isEisensteinAt_lubinTateField (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    ∃ (p : 𝒪[K][X]) (α : Ω), p.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]) ∧
      p.natDegree = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (n - 1) ∧
      aeval α (p.map (algebraMap 𝒪[K] K)) = 0 ∧ lubinTateField Ω hπ hf n = K⟮α⟯ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  obtain ⟨α, hE, hα⟩ := exists_lubinTateField_eq_adjoin_eisenstein (Ω := Ω) hπ hf m
  exact ⟨ltEisenstein π m, α, isEisensteinAt_ltEisenstein hπ m, (ltEisenstein_monic π m).2, hα,
    hE⟩

theorem coeff_zero_ltEisenstein (π : 𝒪[K]) (n : ℕ) : (ltEisenstein π n).coeff 0 = π := by
  have hq := one_lt_card_residueField' K
  rw [ltEisenstein, coeff_add, coeff_C_zero, coeff_zero_eq_eval_zero, eval_pow,
    ← coeff_zero_eq_eval_zero, coeff_zero_ltPolyIter, zero_pow (by omega), add_zero]

theorem exists_norm_eq_uniformizer (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    ∃ x : lubinTateField Ω hπ hf n, Algebra.norm K x = (π : K) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  have hfin := (finrank_and_ramificationIndex_lubinTateField_succ (Ω := Ω) hπ hf m).1
  obtain ⟨a, hE, ha⟩ := exists_lubinTateField_eq_adjoin_eisenstein (Ω := Ω) hπ hf m
  rw [hE] at hfin ⊢
  set p := (ltEisenstein π m).map (algebraMap 𝒪[K] K)
  have hpm : p.Monic := (ltEisenstein_monic π m).1.map _
  have hint : IsIntegral K a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  have hmin : minpoly K a = p := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hpm
      (minpoly.dvd K a ha) ?_).symm
    rw [← adjoin.finrank hint, hfin, natDegree_map_eq_of_injective
      (FaithfulSMul.algebraMap_injective 𝒪[K] K), (ltEisenstein_monic π m).2]
  set pb := adjoin.powerBasis hint
  have hdim : pb.dim = Module.finrank K K⟮a⟯ := by
    rw [adjoin.powerBasis_dim, adjoin.finrank hint]
  have hnorm : Algebra.norm K pb.gen = (-1) ^ Module.finrank K K⟮a⟯ * (π : K) := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hdim, adjoin.powerBasis_gen,
      minpoly_gen, hmin, coeff_map, coeff_zero_ltEisenstein]
    rfl
  refine ⟨-pb.gen, ?_⟩
  have h1 : (-1 : K⟮a⟯) = algebraMap K K⟮a⟯ (-1) := by simp
  rw [neg_eq_neg_one_mul, h1, map_mul, Algebra.norm_algebraMap,
    hnorm, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

end Main

section SeparableClosure

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)

example {n : ℕ} (hn : 0 < n) :
    Module.finrank K (lubinTateField (SeparableClosure K) hπ hf n) =
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (n - 1) :=
  finrank_lubinTateField hπ hf hn

example (n : ℕ) : IsGalois K (lubinTateField (SeparableClosure K) hπ hf n) := inferInstance

example (n : ℕ) :
    (lubinTateField (SeparableClosure K) hπ hf n ≃ₐ[K] lubinTateField (SeparableClosure K) hπ hf n)
      ≃* (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ :=
  lubinTateGalEquiv hπ hf n

end SeparableClosure

end FormalGroup

end GroundTheory.LocalField
