import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumCoeffChiIdemMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspProdCharTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspIndProdCharOfIsProdCuspChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsSemisimpleParameterGLFiniteField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCuspidalCharIsCuspidalOfMinpolyOfParam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeToPartFrob
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockTriangularPrimitiveCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCharsGoodFamilyOfProductIrreducible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceCompLeftFunLeft
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaOfPow

noncomputable section

namespace GlobalTheory.GoodTypeGeneric

section Groups

open GlobalTheory.BI Formalism.L2.DIV

theorem sum_character_eq_zero_iff {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    ∑ g, ρ.character g = 0 ↔ ∀ v, (∀ g, ρ g v = v) → v = 0 := by
  have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  letI := invertibleOfNonzero hc
  have h := ρ.card_inv_mul_sum_char_eq_finrank
  have e : ∑ g, ρ.character g = 0 ↔ ρ.invariants = ⊥ := by
    rw [← Submodule.finrank_eq_zero, ← Nat.cast_eq_zero (R := ℂ), ← h]
    simp [hc]
  rw [e, Submodule.eq_bot_iff]
  simp only [Representation.mem_invariants]

theorem character_coind_eq_ind {G V : Type} [Group G] [Finite G] (H : Subgroup G) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (σ : Representation ℂ H V) (g : G) :
    (Representation.coind H.subtype σ).character g = ind H σ.character g := by
  classical
  letI := Fintype.ofFinite G
  have hc : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h := GlobalTheory.BadShare.trace_coind_mul_card H.subtype σ g
  unfold ind
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, eq_inv_mul_iff_mul_eq₀ hc, mul_comm]
  refine h.trans ?_
  rw [Finset.sum_comm, ← Equiv.sum_comp (Equiv.inv G)]
  refine Finset.sum_congr rfl fun x _ => ?_
  have key : ∀ γ : H, H.subtype γ * (Equiv.inv G x * g) = Equiv.inv G x ↔ ((γ⁻¹ : H) : G) = x⁻¹ * g * x := by
    intro γ
    simp only [Subgroup.coe_subtype, Equiv.inv_apply, Subgroup.coe_inv]
    constructor
    · intro h
      have : (γ : G) = x⁻¹ * (x⁻¹ * g)⁻¹ := by rw [eq_mul_inv_iff_mul_eq, h]
      rw [this]; group
    · intro h
      have : (γ : G) = (x⁻¹ * g * x)⁻¹ := by rw [← h, inv_inv]
      rw [this]; group
  simp only [key]
  unfold ext0
  split_ifs with hx
  · rw [Finset.sum_eq_single (⟨_, hx⟩ : H)⁻¹]
    · rw [inv_inv, if_pos rfl]; rfl
    · intro γ _ hγ
      rw [if_neg]
      intro e
      exact hγ (inv_eq_iff_eq_inv.1 (Subtype.ext e))
    · simp
  · exact Finset.sum_eq_zero fun γ _ => if_neg fun e : ((γ⁻¹ : H) : G) = x⁻¹ * g * x => hx (e ▸ (γ⁻¹).2)

theorem isChar_prod {ι : Type} [Fintype ι] {G : Type} [Group G] {χ : ι → G → ℂ}
    (h : ∀ i, IsChar ℂ ℂ (χ i)) : IsChar ℂ ℂ (fun t => ∏ i, χ i t) := by
  classical
  have : ∀ s : Finset ι, IsChar ℂ ℂ (fun t => ∏ i ∈ s, χ i t) := by
    intro s
    induction s using Finset.induction with
    | empty => simpa using isChar_one ℂ ℂ G
    | insert a s ha ih =>
      have := isChar_mul_complex (h a) ih
      convert this using 1
      funext t
      rw [Finset.prod_insert ha]; rfl
  exact this _

theorem isIrrChar_of_isAbsIrrChar {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] (emb : K →+* ℂ) {χ : G → K}
    (h : IsAbsIrrChar χ) : IsIrrChar ℂ ℂ fun g => emb (χ g) := by
  obtain ⟨n, ρ, hi, hρ⟩ := h
  letI : Algebra K ℂ := emb.toAlgebra
  haveI : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  let φ : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure K) ℂ := φ.toRingHom.toAlgebra
  have h1 := pair_self_of_isIrrChar_algClosed (AlgebraicClosure K) G _ ⟨n, ρ, hi, fun _ => rfl⟩
  rw [pair_character_eq_finrank] at h1
  refine ⟨n, extendScalarsRep _ ℂ ρ, GlobalTheory.GoodFamily.irreducible_extend _ ℂ ρ (by exact_mod_cast h1), fun g => ?_⟩
  rw [character_extendScalarsRep, hρ]
  exact (φ.commutes (χ g)).symm

theorem exists_eq_of_idemOf {K G ι : Type} [Field K] [CharZero K] [Group G] [Fintype G] (emb : K →+* ℂ)
    (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (Y : Finset ι) (t : ι → G → ℂ) (ht : ∀ i ∈ Y, IsChar ℂ ℂ (t i))
    (h : ∀ g, emb ((idemOf X).coeff g) = ∑ i ∈ Y, t i 1 / (Nat.card G : ℂ) * t i g⁻¹) {χ : G → K} (hχ : χ ∈ X) :
    ∃ i ∈ Y, ∀ g, emb (χ g) = t i g := by
  classical
  have h0 := congrArg emb (GlobalTheory.IdemChar.sum_coeff_idemOf_mul K G X hX χ hχ)
  have hirr := isIrrChar_of_isAbsIrrChar emb (hX χ hχ)
  have hne := GlobalTheory.FinGL.LeviChar.irrChar_one_ne_zero hirr
  obtain ⟨n, ρ, hi, hρ⟩ := hirr
  beta_reduce at hρ
  choose! m τ hτ using ht
  have e1 : ∀ (k : ℕ) (σ : Representation ℂ G (Fin k → ℂ)), algebraMap ℂ ℂ (σ.character 1) = k := by
    intro k σ; simp
  have h1 : (n : ℂ) = ∑ i ∈ Y, (m i : ℂ) * (Module.finrank ℂ ((τ i).IntertwiningMap ρ) : ℂ) := by
    rw [← e1 n ρ, ← hρ, ← h0, map_sum]
    simp only [map_mul, h, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← pair_character_eq_finrank ℂ ℂ, ← e1 _ (τ i), ← hτ i hi, pair, finsum_eq_sum_of_fintype, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← hρ, ← hτ i hi]
    ring
  have h2 : n = ∑ i ∈ Y, m i * Module.finrank ℂ ((τ i).IntertwiningMap ρ) := by exact_mod_cast h1
  have hn : n ≠ 0 := by
    intro e
    apply hne
    rw [hρ, e1, e, Nat.cast_zero]
  obtain ⟨i, hiY, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (fun e => hn (h2.trans e))
  have hle : m i * Module.finrank ℂ ((τ i).IntertwiningMap ρ) ≤ n :=
    (Finset.single_le_sum (f := fun i => m i * Module.finrank ℂ ((τ i).IntertwiningMap ρ))
      (fun _ _ => Nat.zero_le _) hiY).trans h2.ge
  have hpos := Nat.pos_of_ne_zero (right_ne_zero_of_mul hi0)
  have hle' : m i ≤ n := le_trans (Nat.le_mul_of_pos_right _ hpos) hle
  haveI := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨f, hf⟩ := exists_ne (0 : (τ i).IntertwiningMap ρ)
  have hs : Function.Surjective f := (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hf
  have hge : n ≤ m i := by
    simpa using LinearMap.finrank_le_finrank_of_surjective (f := f.toLinearMap) hs
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) (by simp; omega)).2 hs
  refine ⟨i, hiY, fun g => ?_⟩
  rw [hρ, hτ i hiY, Representation.char_iso (f.ofBijective ⟨hinj, hs⟩)]

theorem chiIdem_mul_lvlIdem_ne_zero {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] (P : Subgroup G) [Fintype P]
    (ψ : P →* Kˣ) {χ : G → K} (h1 : χ 1 ≠ 0) (h : ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) ≠ 0) :
    chiIdem χ * lvlIdem P ψ ≠ 0 := by
  classical
  intro h0
  have h2 := congrArg (fun a : MonoidAlgebra K G => a.coeff 1) h0
  have hG : (Fintype.card G : K) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hP : (Nat.card P : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  simp only [lvlIdem, Finset.mul_sum, MonoidAlgebra.coeff_sum, Finset.sum_apply', MonoidAlgebra.coeff_mul_single_apply,
    coeff_chiIdem, one_mul, inv_inv, MonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h2
  apply h
  have h3 : χ 1 / (Fintype.card G : K) * (Nat.card P : K)⁻¹ ≠ 0 := mul_ne_zero (div_ne_zero h1 hG) (inv_ne_zero hP)
  apply mul_left_cancel₀ h3
  rw [mul_zero, ← h2, Finset.mul_sum]
  refine Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun x _ => ?_
  rw [map_inv]
  ring

end Groups

section Datum

open GlobalTheory.BI Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.FiniteGL GlobalTheory.Parabolic GlobalTheory.FinGL.LeviChar

variable {F : Type} [Field F] {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}

def blocksHom (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1) :
    blockTri (κ := F) b →* ∀ a, GL (Fin (d a)) F :=
  Pi.monoidHom fun a => (leviBlock b (fun i => e ⟨a, i⟩)
    (fun _ _ hij => sigma_mk_injective (β := fun a => Fin (d a)) (e.injective hij)) (fun i j hij => by
      obtain ⟨⟨c, l⟩, rfl⟩ := e.surjective j
      obtain rfl : a = c := (he _ _).1 hij
      exact ⟨l, rfl⟩)).comp (leviProj b)

omit [Fintype ι] [DecidableEq ι] in
theorem blocksHom_apply (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    (p : blockTri (κ := F) b) (a : ι) (i j : Fin (d a)) :
    (blocksHom b e he p a : Matrix (Fin (d a)) (Fin (d a)) F) i j =
      ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e ⟨a, i⟩) (e ⟨a, j⟩) :=
  if_pos ((he ⟨a, i⟩ ⟨a, j⟩).2 rfl)

theorem blocksHom_diagHom (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    (x : ∀ a, GL (Fin (d a)) F) : blocksHom b e he (diagHom b e he x) = x := by
  funext a
  apply Units.ext
  ext i j
  rw [blocksHom_apply, diagHom_apply, Matrix.blockDiagonal'_apply_eq]

theorem exists_isCuspDatum [Finite F] {b : Fin r → ℕ} (hb : Monotone b) (e : (Σ a, Fin (d a)) ≃ Fin r)
    (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1) (χ : ∀ a, GL (Fin (d a)) F → ℂ) (hχ : ∀ a, IsIrrChar ℂ ℂ (χ a))
    (hc : ∀ a, ∀ c : Fin (d a) → ℕ, (∃ i j, c i ≠ c j) → ∑ᶠ u : unipRadical F c, χ a u = 0) :
    ∃ (n : ℕ) (σ : Representation ℂ (blockTri (κ := F) b) (Fin n → ℂ)), IsCuspDatum b σ ∧
      ∀ p, σ.character p = ∏ a, χ a (blocksHom b e he p a) := by
  classical
  obtain ⟨⟨n, ρ, hρ⟩, h1⟩ := GlobalTheory.GoodFamily.norm_one_prod (χ := χ) fun a =>
    ⟨let ⟨n, ρ, _, h⟩ := hχ a; ⟨n, ρ, h⟩, pair_self_of_isIrrChar_algClosed ℂ _ _ (hχ a)⟩
  rw [funext hρ, pair_character_eq_finrank] at h1
  obtain ⟨h3, h4⟩ := GlobalTheory.asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one ℂ _ _ ρ (by exact_mod_cast h1)
  refine ⟨n, ρ.comp (blocksHom b e he), ⟨hb, Transport.isIrreducible_comp ρ _
    (fun x => ⟨_, blocksHom_diagHom b e he x⟩) (GlobalTheory.GoodFamily.irreducible_of_surjective ρ h4), fun p hp => ?_, ?_⟩,
    fun p => (hρ _).symm⟩
  · have : blocksHom b e he p = 1 := by
      funext a
      apply Units.ext
      ext i j
      rw [blocksHom_apply, hp _ _ ((he ⟨a, i⟩ ⟨a, j⟩).2 rfl)]
      simp [Matrix.one_apply]
    rw [MonoidHom.comp_apply, this, map_one]
  · rintro S ⟨i, j, hij, hi, hj⟩ y hy
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨a', j⟩, rfl⟩ := e.surjective j
    obtain rfl : a = a' := (he _ _).1 hij
    let c : Fin (d a) → ℕ := fun l => if e ⟨a, l⟩ ∈ S then 0 else 1
    letI : Fintype (unipRadical F c) := Fintype.ofFinite _
    let τ : Representation ℂ (unipRadical F c) (Fin n → ℂ) :=
      ρ.comp ((MonoidHom.mulSingle (fun a => GL (Fin (d a)) F) a).comp (unipRadical F c).subtype)
    refine (sum_character_eq_zero_iff τ).1 ?_ y fun u => ?_
    · have h5 := hc a c ⟨i, j, by simp [c, hi, hj]⟩
      rw [finsum_eq_sum_of_fintype] at h5
      have hv : ∀ u : unipRadical F c, τ.character u = χ a u * ∏ c' ∈ Finset.univ.erase a, χ c' 1 := by
        intro u
        refine (hρ (Pi.mulSingle a (u : GL (Fin (d a)) F))).symm.trans ?_
        beta_reduce
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), Pi.mulSingle_eq_same]
        congr 1
        refine Finset.prod_congr rfl fun c' hc' => ?_
        rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hc')]
      simp only [hv]
      rw [← Finset.sum_mul, h5, zero_mul]
    · have h6 := hy (diagHom b e he (Pi.mulSingle a (u : GL (Fin (d a)) F))) ?_
      · rw [MonoidHom.comp_apply, blocksHom_diagHom] at h6
        exact h6
      · intro k l hkl
        obtain ⟨⟨a₁, k⟩, rfl⟩ := e.surjective k
        obtain ⟨⟨a₂, l⟩, rfl⟩ := e.surjective l
        rw [diagHom_apply] at hkl
        by_cases h12 : a₁ = a₂
        · subst h12
          rw [Matrix.blockDiagonal'_apply_eq] at hkl
          have h1 : (1 : Matrix (Fin r) (Fin r) F) (e ⟨a₁, k⟩) (e ⟨a₁, l⟩) = (1 : Matrix _ _ F) k l := by
            simp [Matrix.one_apply]
          rw [h1] at hkl
          by_cases ha : a₁ = a
          · subst ha
            rw [Pi.mulSingle_eq_same] at hkl
            have h7 : ¬ c l ≤ c k := fun h => hkl (sub_eq_zero.1 (mem_unipRadical.1 u.2 k l h))
            refine ⟨(he _ _).2 rfl, ?_⟩
            simp only [c] at h7
            split_ifs at h7 <;> simp_all
          · rw [Pi.mulSingle_eq_of_ne ha] at hkl
            exact absurd rfl hkl
        · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h12, Matrix.one_apply_ne
            (fun h => h12 (congrArg Sigma.fst (e.injective h)))] at hkl
          exact absurd rfl hkl

theorem irr_and_sum_of_isCusp {p n : ℕ} [Fact p.Prime] {χ : GlobalTheory.GLq.Gn p n → ℂ} (h : GlobalTheory.GLq.IsCusp χ) :
    IsIrrChar ℂ ℂ χ ∧ ∀ c : Fin n → ℕ, (∃ i j, c i ≠ c j) → ∑ᶠ u : unipRadical (ZMod p) c, χ u = 0 := by
  classical
  obtain ⟨-, ⟨V, hV, hχ⟩, hres⟩ := h
  obtain rfl : V.character = χ := funext hχ
  have hcusp : IsCuspidal V.ρ := by
    refine (isCuspidal_iff_twoBlocks _).2 fun a h0 ha v hv => ?_
    letI : Fintype (unipRadical (ZMod p) (twoBlocks n a)) := Fintype.ofFinite _
    refine (sum_character_eq_zero_iff (show Representation ℂ _ V from
      MonoidHom.comp V.ρ (unipRadical (ZMod p) (twoBlocks n a)).subtype)).1 ?_ v fun u => hv u u.2
    have h1 := hres a h0 ha
    unfold GlobalTheory.GLq.res at h1
    have hp : ((p : ℂ) ^ (a * (n - a)))⁻¹ ≠ 0 :=
      inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
    have h2 := (mul_eq_zero.1 h1).resolve_left hp
    rw [← Finset.sum_filter] at h2
    rw [← h2]
    refine (Finset.sum_subtype _ (fun u => ?_) V.character).symm
    rw [Finset.mem_filter, ← GlobalTheory.GreenExists.mem_grUnipBlock_iff ha, mem_unipRadical]
    simp only [Finset.mem_univ, true_and, Formalism.D.Classical.grUnipBlock, Set.mem_setOf_eq, twoBlocks, Matrix.sub_apply,
      sub_eq_zero, Matrix.one_apply]
    refine forall₂_congr fun i j => ?_
    by_cases h3 : (i : ℕ) < a <;> by_cases h4 : (j : ℕ) < a <;> simp [h3, h4] <;> omega
  constructor
  · refine (isChar_and_isIrrChar_of_rep ℂ ℂ _ V V.ρ).2 ?_
    have h1 := (FDRep.simple_iff_char_is_norm_one V).1 hV
    have h2 := pair_character_eq_finrank ℂ ℂ _ _ _ V.ρ V.ρ
    rw [pair, finsum_eq_sum_of_fintype] at h2
    have h3 : (Module.finrank ℂ (Representation.IntertwiningMap V.ρ V.ρ) : ℂ) = 1 := by
      rw [← h2, inv_mul_eq_one₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne'), ← h1]
      rfl
    obtain ⟨h3, h4⟩ := GlobalTheory.asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one ℂ _ _ V.ρ (by exact_mod_cast h3)
    exact GlobalTheory.GoodFamily.irreducible_of_surjective _ h4
  · intro c hc
    letI : Fintype (unipRadical (ZMod p) c) := Fintype.ofFinite _
    rw [finsum_eq_sum_of_fintype]
    exact (sum_character_eq_zero_iff (show Representation ℂ _ V from
      MonoidHom.comp V.ρ (unipRadical (ZMod p) c).subtype)).2 fun v hv =>
      fixed_eq_bot_iff.1 ((isCuspidal_iff_forall _).1 hcusp c hc) v fun u hu => hv ⟨u, hu⟩

end Datum

section Types

open GlobalTheory.BI Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.FiniteGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

variable {p : ℕ} [Fact p.Prime] {r : ℕ}

theorem isCusp_cuspOn {s : SSParam p ℂ r} (hs : IsRegularParam s) (c : Cyc s.1) : GlobalTheory.GLq.IsCusp (cuspOn (s.2 c)) := by
  obtain ⟨L⟩ := GlobalTheory.GLq.LabelModel.inhab p
  obtain ⟨x, f, h⟩ := exists_labels p L r s
  exact (isCuspOf_cuspOn L (s.2 c) (x c) (cycLen_pos _ c) (h.1 c)
    (((GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2).2.2.2 (h.regular_iff.1 hs)).1 c)).2.1

def cycEquiv (b : Fin r → Fin r) : (Σ c : Cyc b, Fin (cycLen b c)) ≃ Fin r :=
  Equiv.ofBijective (fun x => ((Fintype.equivFin {a : Fin r // b a = x.1.1}).symm x.2).1) (by
    have hf : ∀ x : Σ c : Cyc b, Fin (cycLen b c),
        b ((Fintype.equivFin {a : Fin r // b a = x.1.1}).symm x.2).1 = x.1.1 :=
      fun x => ((Fintype.equivFin {a : Fin r // b a = x.1.1}).symm x.2).2
    constructor
    · rintro ⟨c, i⟩ ⟨c', j⟩ h
      obtain rfl : c = c' := Subtype.ext ((hf ⟨c, i⟩).symm.trans ((congrArg b h).trans (hf ⟨c', j⟩)))
      obtain rfl : i = j := (Fintype.equivFin {a : Fin r // b a = c.1}).symm.injective (Subtype.ext h)
      rfl
    · intro i
      refine ⟨⟨⟨b i, i, rfl⟩, Fintype.equivFin _ ⟨i, rfl⟩⟩, ?_⟩
      simp only [Equiv.symm_apply_apply])

theorem cycEquiv_apply (b : Fin r → Fin r) (c : Cyc b) (i : {a : Fin r // b a = c.1}) :
    cycEquiv b ⟨c, Fintype.equivFin _ i⟩ = i.1 :=
  congrArg Subtype.val ((Fintype.equivFin {a : Fin r // b a = c.1}).symm_apply_apply i)

theorem apply_cycEquiv (b : Fin r → Fin r) (x : Σ c : Cyc b, Fin (cycLen b c)) : b (cycEquiv b x) = x.1.1 :=
  ((Fintype.equivFin {a : Fin r // b a = x.1.1}).symm x.2).2

theorem isCuspProdChar_typeChar {s : SSParam p ℂ r} (hs : IsRegularParam s) :
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (typeChar s) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let b₀ : Fin r → ℕ := fun i => (s.1 i : ℕ)
  let w := Tuple.sort b₀
  let e := (cycEquiv s.1).trans w.symm
  have he : ∀ x y, (b₀ ∘ w) (e x) = (b₀ ∘ w) (e y) ↔ x.1 = y.1 := by
    intro x y
    simp only [e, b₀, Function.comp, Equiv.trans_apply, Equiv.apply_symm_apply, apply_cycEquiv, Fin.val_inj,
      Subtype.ext_iff]
  obtain ⟨n, σ, hσ, hch⟩ := exists_isCuspDatum (F := ZMod p) (Tuple.monotone_sort b₀) e he (fun c => cuspOn (s.2 c))
    (fun c => (irr_and_sum_of_isCusp (isCusp_cuspOn hs c)).1) fun c => (irr_and_sum_of_isCusp (isCusp_cuspOn hs c)).2
  refine ⟨n, b₀ ∘ w, σ, hσ, fun x => ?_⟩
  have hm : ∀ z : GL (Fin r) (ZMod p),
      ((permGL (ZMod p) w * z * (permGL (ZMod p) w)⁻¹ : GL (Fin r) (ZMod p)) :
        Matrix (Fin r) (Fin r) (ZMod p)).BlockTriangular s.1 ↔ z ∈ blockTri (κ := ZMod p) (b₀ ∘ w) := fun z =>
    Iff.trans Iff.rfl (conj_mem_blockTri (b := b₀))
  rw [character_coind_eq_ind]
  unfold typeChar ind
  congr 1
  · congr 2
    exact (Nat.card_congr ((MulAut.conj (permGL (ZMod p) w)).toEquiv.subtypeEquiv fun z => (hm z).symm)).symm
  · letI := Fintype.ofFinite (GL (Fin r) (ZMod p))
    rw [finsum_eq_sum_of_fintype]
    symm
    refine Fintype.sum_equiv (Equiv.mulRight (permGL (ZMod p) w)⁻¹) _ _ fun y => ?_
    have h1 : (Equiv.mulRight (permGL (ZMod p) w)⁻¹ y)⁻¹ * x * Equiv.mulRight (permGL (ZMod p) w)⁻¹ y =
        permGL (ZMod p) w * (y⁻¹ * x * y) * (permGL (ZMod p) w)⁻¹ := by
      simp only [Equiv.coe_mulRight]
      group
    rw [h1]
    unfold ext0
    by_cases hz : y⁻¹ * x * y ∈ blockTri (κ := ZMod p) (b₀ ∘ w)
    · rw [dif_pos hz, if_pos ((hm _).2 hz), hch]
      refine Finset.prod_congr rfl fun c _ => ?_
      unfold cuspOn
      congr 1
      ext i j
      rw [Matrix.submatrix_apply, blocksHom_apply]
      simp only [e, Equiv.trans_apply, cycEquiv_apply]
      rw [← conj_permGL_apply w, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rfl
    · rw [dif_neg hz, if_neg (mt (hm _).1 hz)]

theorem isChar_of_isCuspProdChar {θ : GL (Fin r) (ZMod p) → ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar θ) : IsChar ℂ ℂ θ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨n, b, σ, -, h⟩ := h
  rw [funext h]
  exact (isChar_and_isIrrChar_of_rep ℂ ℂ _ _ (parInd b σ)).1

end Types

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.DimPartsCompare

theorem isProdCuspChar_of_idemTie {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (hrec : R.grp_record) {om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ}
    (hI : IdemTie D om) {χ : G → D.what₂.LL} (hχ : χ ∈ A.X) :
    CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g) := by
  classical
  obtain ⟨eR, plg, iso, h1, -, h2⟩ := hrec
  let π : LevelCuspCharacters.LevelGroup D.host ≃* G0g D.nd :=
    MulEquiv.ofBijective (⟨⟨pull, rfl⟩, fun _ _ => rfl⟩ : LevelCuspCharacters.LevelGroup D.host →* G0g D.nd) pull_bijective
  let φ : G ≃* LevelCuspCharacters.LevelGroup D.host := eR.trans π.symm
  have hφ : ∀ g, pull (φ g) = eR g := fun g => π.apply_symm_apply (eR g)
  have hreg : ∀ s : ∀ v : LevelCuspCharacters.Sq D.host, LevelCuspCharacters.SSParam (D.host.g v.1) ℂ D.R.r, LevelCuspCharacters.IsGoodParam om s →
      ∀ v, CuspidalProductMultiplicity.IsCuspProdChar (LevelCuspCharacters.typeChar (s v)) := fun s hs v => isCuspProdChar_typeChar ((hs v.1).1 v.2)
  obtain ⟨τ, hτ, hχτ⟩ := exists_eq_of_idemOf D.what₂.embLL A.X hX (LevelCuspCharacters.goodTypes_finite (H := D.host) om).toFinset
    (fun τ g => τ (φ g)) (fun τ hτ => by
      obtain ⟨s, hs, rfl⟩ := (Set.Finite.mem_toFinset _).1 hτ
      letI := Fintype.ofFinite (LevelCuspCharacters.Sq D.host)
      refine isChar_prod (χ := fun v g => LevelCuspCharacters.typeChar (s v) (φ g v)) fun v => ?_
      obtain ⟨n, ρ, hρ⟩ := isChar_of_isCuspProdChar (hreg s hs v)
      exact ⟨n, ρ.comp ((Pi.evalMonoidHom _ v).comp φ.toMonoidHom), fun g => hρ _⟩) (fun g => by
      rw [h1, ← hφ, hI, Nat.card_congr φ.toEquiv]
      simp only [LevelCuspCharacters.goodIdem, LevelCuspCharacters.centralIdem, MonoidAlgebra.coeff_sum, Finset.sum_apply', map_one, map_inv]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp [Finsupp.single_apply]) hχ
  obtain ⟨s, hs, rfl⟩ := (Set.Finite.mem_toFinset _).1 hτ
  let f : (Σ k : Fin 2, D.nd.PlG k) → G → ℂ := fun kv g => LevelCuspCharacters.typeChar (s (sqEquiv D kv)) (φ g (sqEquiv D kv))
  have key : ∀ PP : R.Pg, ∃ θ : GL (Fin D.R.r) (kP PP.1) → ℂ,
      @CuspidalProductMultiplicity.IsCuspProdChar (kP PP.1) (Ideal.Quotient.field PP.1.asIdeal) D.R.r θ ∧
        ∀ g, θ (R.eG g PP) = f (plg.symm PP) g := by
    intro PP
    obtain ⟨kv, rfl⟩ := plg.surjective PP
    letI := Ideal.Quotient.field (plg kv).1.asIdeal
    refine ⟨_, GlobalTheory.FinGL.Transport.isCuspProdChar_transport _ _ (iso kv) _ _ (hreg s hs (sqEquiv D kv)), fun g => ?_⟩
    rw [Equiv.symm_apply_apply, h2, ← hφ]
    exact congrArg _ ((GlobalTheory.FinGL.Transport.glEquiv (iso kv) D.R.r).symm_apply_apply _)
  choose θ hθ hθ' using key
  refine ⟨θ, hθ, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := R.eG.surjective x
  simp only [hθ', MulEquiv.symm_apply_apply, hχτ]
  letI := Fintype.ofFinite (LevelCuspCharacters.Sq D.host)
  exact (Fintype.prod_equiv (plg.symm.trans (sqEquiv D)) _ _ fun _ => rfl).symm

theorem chiIdem_mul_lvlIdem_base_ne_zero : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → R.toLevCh.Is A.μ0 → R.IsGrp F →
    ∀ (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ), GlobalTheory.DimPartsCompare.IdemTie D om →
    ∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk _ hG om hI χ hχ
  letI : Fintype F.P0 := Fintype.ofFinite _
  refine chiIdem_mul_lvlIdem_ne_zero _ _ (fun h => ?_) ?_
  · exact GlobalTheory.FinGL.LeviChar.irrChar_one_ne_zero (isIrrChar_of_isAbsIrrChar D.what₂.embLL (hOk.irr χ hχ))
      (by rw [h, map_zero])
  · rw [GlobalTheory.RealOneVector.typeSum_base_eq_card D G Pl0 T A Ks R F hG.levels
      (fun χ hχ => isProdCuspChar_of_idemTie R hOk.irr hG.record hI hχ) χ hχ]
    exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

end GlobalTheory.GoodTypeGeneric

end
