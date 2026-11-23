import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcrossOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import ReciprocityTheory.GaloisValuations.Global

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

section Abstract

variable {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ}

private theorem flag_pull {r : Γ →* GL (Fin n) k} {r' : Γ' →* GL (Fin n) k} {H : Subgroup Γ} {H' : Subgroup Γ'}
    (f : ↥H' →* ↥H) (x : GL (Fin n) k) (hx : ∀ u : ↥H', r' u = x * r (f u) * x⁻¹)
    {κ : Fin n → ↥H →* kˣ} (h : IsFlagOn r H κ) : IsFlagOn r' H' fun i => (κ i).comp f := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g * x⁻¹, fun u => ?_⟩
  have e : g * x⁻¹ * r' u * (g * x⁻¹)⁻¹ = g * r (f u) * g⁻¹ := by rw [hx]; group
  rw [e]
  exact hg (f u)

private theorem flag_tw {r : Γ →* GL (Fin n) k} (χ : Γ →* kˣ) {H : Subgroup Γ} {κ : Fin n → ↥H →* kˣ}
    (h : IsFlagOn r H κ) : IsFlagOn (tw r χ) H fun i => κ i * χ.comp H.subtype := by
  obtain ⟨g, hg⟩ := h
  have e : ∀ s : Γ, ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (χ s : k) • ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := fun s => by
    simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · rw [e, Matrix.smul_apply, (hg s).1 i j hij, smul_zero]
  · rw [e, Matrix.smul_apply, (hg s).2 i]
    simp [mul_comm]

private theorem tw_tw_inv (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) : tw (tw r χ) χ⁻¹ = r := by
  ext s : 1
  apply Units.ext
  rw [tw_val, tw_val, smul_smul]
  simp

private theorem flag_trace {r : Γ →* GL (Fin n) k} {H : Subgroup Γ} {κ : Fin n → ↥H →* kˣ} (h : IsFlagOn r H κ)
    (s : ↥H) : (r s : Matrix (Fin n) (Fin n) k).trace = ∑ i, (κ i s : k) := by
  obtain ⟨g, hg⟩ := h
  have e : (r s : Matrix (Fin n) (Fin n) k).trace =
      ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace := by
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  rw [e, Matrix.trace]
  exact Finset.sum_congr rfl fun i _ => (hg s).2 i

private theorem flag_mem [CharZero k] {r : Γ →* GL (Fin n) k} {H : Subgroup Γ} {κ θ : Fin n → ↥H →* kˣ}
    (h : IsFlagOn r H κ) (h' : IsFlagOn r H θ) (i : Fin n) : ∃ a, θ a = κ i := by
  classical
  by_contra hne
  push Not at hne
  let cv : (↥H →* kˣ) → (↥H →* k) := fun χ => (Units.coeHom k).comp χ
  have hcv : ∀ χ χ', cv χ = cv χ' → χ = χ' := fun χ χ' e => by
    ext s
    exact congrArg (fun f : ↥H →* k => f s) e
  let a : Fin n → (↥H →* k) := fun i => cv (κ i)
  let b : Fin n → (↥H →* k) := fun i => cv (θ i)
  let t : Finset (↥H →* k) := Finset.univ.image a ∪ Finset.univ.image b
  have ha : ∀ i, a i ∈ t := fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hb : ∀ i, b i ∈ t := fun i => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have key : ∀ (e : Fin n → (↥H →* k)), (∀ i, e i ∈ t) → ∀ s : ↥H,
      ∑ f ∈ t, ((Finset.univ.filter fun i => e i = f).card : k) * f s = ∑ i, e i s := by
    intro e he s
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := t) (g := e) (fun i _ => he i)]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => f s) (fun i hi => by rw [(Finset.mem_filter.1 hi).2])]
    simp
  let c : (↥H →* k) → k := fun f =>
    ((Finset.univ.filter fun i => a i = f).card : k) - ((Finset.univ.filter fun i => b i = f).card : k)
  have hs : ∑ f ∈ t, c f • (f : ↥H → k) = 0 := by
    funext s
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, c, sub_mul, Finset.sum_sub_distrib]
    rw [key a ha s, key b hb s, sub_eq_zero]
    exact ((flag_trace h s).symm.trans (flag_trace h' s))
  have h0 := linearIndependent_iff'.1 (linearIndependent_monoidHom ↥H k) t c hs (a i) (ha i)
  have h1 : (Finset.univ.filter fun j => b j = a i) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun j _ e => hne j (hcv _ _ e)
  have h2 : 0 < (Finset.univ.filter fun j => a j = a i).card :=
    Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
  simp only [c, h1, Finset.card_empty, Nat.cast_zero, sub_zero, Nat.cast_eq_zero] at h0
  omega

end Abstract

section Gal

open scoped Pointwise

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [Algebra K L]
  [Algebra L Ω] [IsScalarTower K L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

private abbrev rs (K L Ω : Type) [Field K] [Field L] [Field Ω] [Algebra K Ω] [Algebra K L] [Algebra L Ω]
    [IsScalarTower K L Ω] : G L Ω →* G K Ω := AlgEquiv.restrictScalarsHom K

private def resD (K L : Type) {Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω]
    [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω] (A : ValuationSubring Ω) :
    ↥(Dec (F := L) A) →* ↥(Dec (F := K) A) where
  toFun u := ⟨rs K L Ω u, u.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

private def cMap (A B : ValuationSubring Ω) (γ : G K Ω) (h : γ • A = B) :
    ↥(Dec (F := K) B) →* ↥(Dec (F := K) A) where
  toFun u := ⟨γ⁻¹ * u * γ, by
    have hu := mem_Dec.1 u.2
    rw [mem_Dec, mul_smul, mul_smul, h, hu, ← h, inv_smul_smul]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

private theorem cyc_conj (γ s : G K Ω) : cycBar K Ω l (γ⁻¹ * s * γ) = cycBar K Ω l s := by
  rw [map_mul, map_mul, map_inv, mul_comm (cycBar K Ω l γ)⁻¹, mul_assoc, mul_comm _ (cycBar K Ω l γ)]
  simp

private theorem cyc_res (u : G L Ω) : cycBar K Ω l (rs K L Ω u) = cycBar L Ω l u := rfl

private theorem conj_eq (r : G K Ω →* GL (Fin n) (Qbar l)) (γ s : G K Ω) : r s = r γ * r (γ⁻¹ * s * γ) * (r γ)⁻¹ := by
  simp only [map_mul, map_inv]
  group

private def dMap (A B : ValuationSubring Ω) (γ : G K Ω) (h : γ • A = B) :
    ↥(Dec (F := L) B) →* ↥(Dec (F := K) A) := (cMap A B γ h).comp (resD K L B)

private theorem dMap_coe (A B : ValuationSubring Ω) (γ : G K Ω) (h : γ • A = B) (u : ↥(Dec (F := L) B)) :
    ((dMap (L := L) A B γ h u : ↥(Dec (F := K) A)) : G K Ω) = γ⁻¹ * rs K L Ω u * γ := rfl

private theorem flag_dMap {r : G K Ω →* GL (Fin n) (Qbar l)} {A B : ValuationSubring Ω} {γ : G K Ω} (h : γ • A = B)
    {κ : Fin n → ↥(Dec (F := K) A) →* (Qbar l)ˣ} (hκ : IsFlagOn r (Dec (F := K) A) κ) :
    IsFlagOn (r.comp (rs K L Ω)) (Dec (F := L) B) fun i => (κ i).comp (dMap A B γ h) := by
  refine flag_pull _ (r γ) (fun u => ?_) hκ
  rw [dMap_coe, MonoidHom.comp_apply]
  exact conj_eq r γ _

private theorem cyc_dMap (A B : ValuationSubring Ω) (γ : G K Ω) (h : γ • A = B) :
    ((cycBar K Ω l).comp (Dec (F := K) A).subtype).comp (dMap A B γ h) =
      (cycBar L Ω l).comp (Dec (F := L) B).subtype := by
  refine MonoidHom.ext fun u => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, dMap_coe, cyc_conj]
  rfl

private theorem pow_comp {H H' C : Type} [Group H] [Group H'] [CommGroup C] (f : H' →* H) {a b c : H →* C} {m : ℕ}
    (e : a ^ m = (b * c) ^ m) : (a.comp f) ^ m = (b.comp f * c.comp f) ^ m := by
  refine MonoidHom.ext fun u => ?_
  have e1 := DFunLike.congr_fun e (f u)
  simpa only [MonoidHom.pow_apply, MonoidHom.mul_apply, MonoidHom.comp_apply] using e1

private theorem pow_down {r : G K Ω →* GL (Fin n) (Qbar l)} {A B : ValuationSubring Ω} {γ : G K Ω} (h : γ • A = B)
    {κ : Fin n → ↥(Dec (F := K) A) →* (Qbar l)ˣ} (hκ : IsFlagOn r (Dec (F := K) A) κ)
    {θ : Fin n → ↥(Dec (F := L) B) →* (Qbar l)ˣ} (hθ : IsFlagOn (r.comp (rs K L Ω)) (Dec (F := L) B) θ) (m : ℕ)
    (hne : ∀ a b, θ a ^ m ≠ (θ b * (cycBar L Ω l).comp (Dec (F := L) B).subtype) ^ m) (i j : Fin n) :
    κ i ^ m ≠ (κ j * (cycBar K Ω l).comp (Dec (F := K) A).subtype) ^ m := by
  intro e
  have hf := flag_dMap (L := L) h hκ
  obtain ⟨a, ha⟩ := flag_mem hf hθ i
  obtain ⟨b, hb⟩ := flag_mem hf hθ j
  have e2 := pow_comp (dMap (L := L) A B γ h) e
  rw [cyc_dMap, ← ha, ← hb] at e2
  exact hne a b e2

private theorem exists_exp (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω]
    [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω] :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ s : G K Ω, ∃ u : G L Ω, rs K L Ω u = s ^ N := by
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  let R : Subgroup (G K Ω) := (rs K L Ω).range
  let e : G K Ω → (L →ₐ[K] Ω) := fun σ => (σ : Ω →ₐ[K] Ω).comp (IsScalarTower.toAlgHom K L Ω)
  have hinj : Function.Injective fun q : G K Ω ⧸ R => e q.out := by
    intro q q' hq
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    refine QuotientGroup.eq.2 ?_
    have hfix : ∀ x : L, (q.out⁻¹ * q'.out) (algebraMap L Ω x) = algebraMap L Ω x := fun x => by
      have e1 : q.out (algebraMap L Ω x) = q'.out (algebraMap L Ω x) := DFunLike.congr_fun hq x
      rw [AlgEquiv.mul_apply, ← e1]
      exact q.out.symm_apply_apply _
    exact ⟨{ (q.out⁻¹ * q'.out).toRingEquiv with commutes' := hfix }, by ext x; rfl⟩
  haveI : Finite (G K Ω ⧸ R) := Finite.of_injective _ hinj
  haveI : R.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨R.normalCore.index, Nat.one_le_iff_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero, fun s => ?_⟩
  exact Subgroup.normalCore_le R (R.normalCore.pow_index_mem s)

private theorem pow_up {A : ValuationSubring Ω} {N : ℕ} (hN : ∀ s : G K Ω, ∃ u : G L Ω, rs K L Ω u = s ^ N)
    {a b : ↥(Dec (F := K) A) →* (Qbar l)ˣ} {m : ℕ}
    (e : (a.comp (resD K L A)) ^ m = (b.comp (resD K L A) * (cycBar L Ω l).comp (Dec (F := L) A).subtype) ^ m) :
    a ^ (N * m) = (b * (cycBar K Ω l).comp (Dec (F := K) A).subtype) ^ (N * m) := by
  refine MonoidHom.ext fun s => ?_
  obtain ⟨u, hu⟩ := hN s
  have hm : rs K L Ω u ∈ Dec (F := K) A := hu ▸ pow_mem s.2 N
  have hd : resD K L A ⟨u, hm⟩ = s ^ N := Subtype.ext hu
  have e1 := DFunLike.congr_fun e ⟨u, hm⟩
  simp only [MonoidHom.pow_apply, MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, hd] at e1 ⊢
  have hc : cycBar L Ω l u = cycBar K Ω l (s : G K Ω) ^ N := by
    rw [← cyc_res (K := K), hu, map_pow]
  rw [hc, map_pow, map_pow, ← mul_pow, ← pow_mul, ← pow_mul] at e1
  exact e1

private theorem charpoly_conj' {k : Type} [Field k] {n : ℕ} (y x : GL (Fin n) k) :
    ((y * x * y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = (x : Matrix (Fin n) (Fin n) k).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

private theorem charpoly_scale {k : Type} [Field k] [CharZero k] {n : ℕ} (M : Matrix (Fin n) (Fin n) k) {c : k} (hc : c ≠ 0)
    (a : Fin n → k) (h : M.charpoly = ∏ i, (X - C (a i))) : (c • M).charpoly = ∏ i, (X - C (c * a i)) := by
  haveI : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
  refine Polynomial.funext fun x => ?_
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  have e1 : eval (c * y) (c • M).charpoly = c ^ n * eval y M.charpoly := by
    rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
    have e2 : Matrix.scalar (Fin n) (c * y) - c • M = c • (Matrix.scalar (Fin n) y - M) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul, mul_sub]
      split_ifs <;> simp
    rw [e2, Matrix.det_smul, Fintype.card_fin]
  rw [e1, h, eval_prod, eval_prod]
  simp only [eval_sub, eval_X, eval_C, ← mul_sub, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

private theorem flag_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r')
    {H : Subgroup Γ} {κ : Fin n → ↥H →* kˣ} (hκ : IsFlagOn r H κ) : IsFlagOn r' H κ := by
  obtain ⟨x, hx⟩ := h
  exact flag_pull (MonoidHom.id _) x (fun u => hx u) hκ

private theorem ineAb_iso {r r' : G K Ω →* GL (Fin n) (Qbar l)} (h : RepIso r r') (H : IneAb r) : IneAb r' := by
  intro v hv A hA
  obtain ⟨κ, hc, hp⟩ := H v hv A hA
  obtain ⟨x, hx⟩ := h
  refine ⟨κ, hc, fun g hg => ?_⟩
  rw [hx, charpoly_conj']
  exact hp g hg

private theorem flagged_iso {r r' : G K Ω →* GL (Fin n) (Qbar l)} (h : RepIso r r') (H : Flagged r) : Flagged r' := by
  intro v hv A hA
  obtain ⟨κ, hκ⟩ := H v hv A hA
  exact ⟨κ, flag_iso h hκ⟩

private theorem unl_iso {r r' : G K Ω →* GL (Fin n) (Qbar l)} (h : RepIso r r') {v : HeightOneSpectrum (𝓞 K)}
    (H : Unl1 r v) : Unl1 r' v := by
  intro A hA
  obtain ⟨κ, h1, h2⟩ := H A hA
  exact ⟨κ, flag_iso h h1, h2⟩

private theorem pot_iso {r r' : G K Ω →* GL (Fin n) (Qbar l)} (h : RepIso r r') {v : HeightOneSpectrum (𝓞 K)}
    (H : PotUnl r v) : PotUnl r' v := by
  intro A hA
  obtain ⟨κ, h1, h2⟩ := H A hA
  exact ⟨κ, flag_iso h h1, h2⟩

private theorem ineAb_tw {r : G K Ω →* GL (Fin n) (Qbar l)} {μ : G K Ω →* (Qbar l)ˣ} (hμ : Continuous μ) (H : IneAb r) :
    IneAb (tw r μ) := by
  intro v hv A hA
  obtain ⟨κ, hc, hp⟩ := H v hv A hA
  refine ⟨fun i => κ i * μ.comp (Dec (F := K) A).subtype,
    fun i => (hc i).mul (hμ.comp continuous_subtype_val), fun g hg => ?_⟩
  rw [tw_val, charpoly_scale _ (Units.ne_zero _) _ (hp g hg)]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [mul_comm]

private theorem flagged_tw {r : G K Ω →* GL (Fin n) (Qbar l)} (μ : G K Ω →* (Qbar l)ˣ) (H : Flagged r) :
    Flagged (tw r μ) := by
  intro v hv A hA
  obtain ⟨κ, hκ⟩ := H v hv A hA
  exact ⟨_, flag_tw μ hκ⟩

private theorem unl_tw {r : G K Ω →* GL (Fin n) (Qbar l)} (μ : G K Ω →* (Qbar l)ˣ) {v : HeightOneSpectrum (𝓞 K)}
    (H : Unl1 r v) : Unl1 (tw r μ) v := by
  intro A hA
  obtain ⟨κ, h1, h2⟩ := H A hA
  refine ⟨_, flag_tw μ h1, fun i j e => h2 i j ?_⟩
  have e' : κ i * μ.comp (Dec (F := K) A).subtype = κ j * μ.comp (Dec (F := K) A).subtype *
    (cycBar K Ω l).comp (Dec (F := K) A).subtype := e
  rw [mul_right_comm] at e'
  exact mul_right_cancel e'

private theorem pot_tw {r : G K Ω →* GL (Fin n) (Qbar l)} (μ : G K Ω →* (Qbar l)ˣ) {v : HeightOneSpectrum (𝓞 K)}
    (H : PotUnl r v) : PotUnl (tw r μ) v := by
  intro A hA
  obtain ⟨κ, h1, h2⟩ := H A hA
  refine ⟨_, flag_tw μ h1, fun i j m hm e => h2 i j m hm ?_⟩
  have e' : (κ i * μ.comp (Dec (F := K) A).subtype) ^ m = (κ j * μ.comp (Dec (F := K) A).subtype *
    (cycBar K Ω l).comp (Dec (F := K) A).subtype) ^ m := e
  rw [mul_right_comm, mul_pow, mul_pow (κ j * _)] at e'
  exact mul_right_cancel e'

private theorem cont_kills [IsAlgClosure K Ω] {M : ℕ} (hM : 0 < M) {φ : G K Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) :
    Continuous φ := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  have hmem : {s : G K Ω | φ s = 1} ∈ nhds (1 : G K Ω) := by
    refine Filter.mem_of_superset
      ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := K) ζ).mem_nhds ?_) fun s hs => ?_
    · simp only [Set.mem_iInter]
      exact fun ζ _ => Subgroup.one_mem _
    · simp only [Set.mem_iInter] at hs
      exact hφ s fun ζ hζ => hs ζ hζ
  refine continuous_of_continuousAt_one φ ?_
  have he : φ =ᶠ[nhds 1] fun _ => φ 1 := by
    filter_upwards [hmem] with s hs
    rw [map_one]
    exact hs
  exact continuousAt_const.congr he.symm

private theorem flagged_level [IsAlgClosure K Ω] {r : G K Ω →* GL (Fin n) (Qbar l)} {M : ℕ} {m : Fin n → ℤ}
    (H : Level l M m r) : Flagged r := by
  intro v hv A hA
  obtain ⟨A₀, hA₀, χ, κ, -, h2, -⟩ := H.above v hv
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver hA₀ hA
  exact ⟨_, flag_pull (cMap A₀ A γ hγ) (r γ) (fun u => conj_eq r γ _) h2⟩

private theorem ineAb_level [IsAlgClosure K Ω] {r : G K Ω →* GL (Fin n) (Qbar l)} {M : ℕ} {m : Fin n → ℤ} (hM : 0 < M)
    (H : Level l M m r) : IneAb r := by
  intro v hv A hA
  obtain ⟨A₀, hA₀, χ, h1, g, hg⟩ := H.away v hv
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver hA₀ hA
  refine ⟨fun i => (χ i).comp (Dec (F := K) A).subtype,
    fun i => (cont_kills hM (h1 i)).comp continuous_subtype_val, fun s hs => ?_⟩
  have ht : γ⁻¹ * (s : G K Ω) * γ ∈ Ine (F := K) A₀ :=
    (UpperTheory.V.Two.ineConj K Ω γ).1 A₀ s (hγ.symm ▸ hs)
  have e1 : (r s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      ((g * r (γ⁻¹ * (s : G K Ω) * γ) * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    rw [charpoly_conj', conj_eq r γ s, charpoly_conj']
  rw [e1, hg _ ht, Matrix.charpoly_of_upperTriangular _ (fun i j hij => Matrix.diagonal_apply_ne _ (by rintro rfl; exact lt_irrefl _ hij))]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e2 : χ i (γ⁻¹ * (s : G K Ω) * γ) = χ i s := by
    rw [map_mul, map_mul, map_inv, mul_comm (χ i γ)⁻¹, mul_assoc, mul_comm _ (χ i γ)]
    simp
  simp [e2]

private theorem isPlaceOver_under' {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A w) :
    IsPlaceOver A (w.under (𝓞 K)) := fun x => by
  rw [IsScalarTower.algebraMap_apply K L Ω]
  exact h (algebraMap (𝓞 K) (𝓞 L) x)

private theorem not_mem_under {w : HeightOneSpectrum (𝓞 L)} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) :
    ((l : ℕ) : 𝓞 K) ∉ (w.under (𝓞 K)).asIdeal := fun hm => h (by simpa using Ideal.mem_comap.1 hm)

private theorem mem_under {w : HeightOneSpectrum (𝓞 L)} (h : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) :
    ((l : ℕ) : 𝓞 K) ∈ (w.under (𝓞 K)).asIdeal := Ideal.mem_comap.2 (by simpa using h)

private theorem continuous_resD (A : ValuationSubring Ω) : Continuous (resD K L A) :=
  Continuous.subtype_mk ((continuous_restrictScalarsHom K L Ω).comp continuous_subtype_val) _

private theorem flag_resD {r : G K Ω →* GL (Fin n) (Qbar l)} {A : ValuationSubring Ω}
    {κ : Fin n → ↥(Dec (F := K) A) →* (Qbar l)ˣ} (hκ : IsFlagOn r (Dec (F := K) A) κ) :
    IsFlagOn (r.comp (rs K L Ω)) (Dec (F := L) A) fun i => (κ i).comp (resD K L A) := by
  refine flag_pull _ 1 (fun u => ?_) hκ
  simp only [inv_one, mul_one, one_mul]
  rfl

private theorem ineAb_res {r : G K Ω →* GL (Fin n) (Qbar l)} (H : IneAb r) : IneAb (r.comp (rs K L Ω)) := by
  intro w hw A hA
  obtain ⟨κ, hc, hp⟩ := H _ (not_mem_under hw) A (isPlaceOver_under' hA)
  exact ⟨fun i => (κ i).comp (resD K L A), fun i => (hc i).comp (continuous_resD A),
    fun g hg => hp (resD K L A g) ⟨hg.1, hg.2⟩⟩

private theorem flagged_res {r : G K Ω →* GL (Fin n) (Qbar l)} (H : Flagged r) : Flagged (r.comp (rs K L Ω)) := by
  intro w hw A hA
  obtain ⟨κ, hκ⟩ := H _ (mem_under hw) A (isPlaceOver_under' hA)
  exact ⟨_, flag_resD hκ⟩

private theorem pot_up {r : G K Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 L)} (H : PotUnl r (w.under (𝓞 K))) :
    PotUnl (r.comp (rs K L Ω)) w := by
  intro A hA
  obtain ⟨κ, h1, h2⟩ := H A (isPlaceOver_under' hA)
  obtain ⟨N, hN, hs⟩ := exists_exp K L Ω
  exact ⟨_, flag_resD h1, fun i j m hm e => h2 i j (N * m) (Nat.mul_pos hN hm) (pow_up hs e)⟩

private theorem pot_down [IsAlgClosure K Ω] {r : G K Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 L)}
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (hF : Flagged r) (H : PotUnl (r.comp (rs K L Ω)) w) : PotUnl r (w.under (𝓞 K)) := by
  intro A hA
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) L⟩
  obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver hA (isPlaceOver_under' (K := K) hB)
  obtain ⟨κ, hκ⟩ := hF _ (mem_under hw) A hA
  obtain ⟨θ, hθ, hne⟩ := H B hB
  exact ⟨κ, hκ, fun i j m hm => pow_down hγ hκ hθ m (fun a b => hne a b m hm) i j⟩

private theorem unl_down [IsAlgClosure K Ω] {r : G K Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 L)}
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (hF : Flagged r) (H : Unl1 (r.comp (rs K L Ω)) w) : Unl1 r (w.under (𝓞 K)) := by
  intro A hA
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) L⟩
  obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver hA (isPlaceOver_under' (K := K) hB)
  obtain ⟨κ, hκ⟩ := hF _ (mem_under hw) A hA
  obtain ⟨θ, hθ, hne⟩ := H B hB
  refine ⟨κ, hκ, fun i j e => pow_down hγ hκ hθ 1 (fun a b => ?_) i j ?_⟩
  · simpa only [pow_one] using hne a b
  · simpa only [pow_one] using e

end Gal

theorem flagLaws : FlagLaws := by
  intro K Ω _ _ _ _ _ l _ n r
  refine ⟨fun r' h => ⟨ineAb_iso h, flagged_iso h, fun v => ⟨unl_iso h, pot_iso h⟩⟩,
    fun μ => ⟨ineAb_tw, flagged_tw μ, fun v => ⟨⟨unl_tw μ, fun h => ?_⟩, ⟨pot_tw μ, fun h => ?_⟩⟩⟩,
    fun M m hM H => ⟨ineAb_level hM H, flagged_level H⟩, fun L _ _ _ _ _ =>
      ⟨ineAb_res, flagged_res, fun w hw => ⟨pot_up, fun hF => ⟨pot_down hw hF, unl_down hw hF⟩⟩⟩⟩
  · simpa only [tw_tw_inv] using unl_tw μ⁻¹ h
  · simpa only [tw_tw_inv] using pot_tw μ⁻¹ h

end UpperTheory.V.Z.Win
