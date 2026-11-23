import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem trOf_split (t : Fin n → kˣ) : ∃ b : Fin n → kˣ, Dom b ∧ Dom (b * t) := by
  classical
  let V : kˣ → ValueGroupWithZero k := fun x => valuation k (x : k)
  have hVmul : ∀ x y : kˣ, V (x * y) = V x * V y := fun x y => by simp [V]
  have hVpow : ∀ (x : kˣ) (e : ℕ), V (x ^ e) = V x ^ e := fun x e => by simp [V]
  let w : Fin n × Fin n → kˣ := fun r =>
    if 1 ≤ V (t r.1 * (t r.2)⁻¹) then t r.1 * (t r.2)⁻¹ else 1
  have hw1 : ∀ r, 1 ≤ V (w r) := by
    intro r
    simp only [w]
    split_ifs with h
    · exact h
    · simp [V]
  have hwt : ∀ i j, V (t i) ≤ V (w (i, j)) * V (t j) := by
    intro i j
    simp only [w]
    split_ifs with h
    · exact le_of_eq (by rw [← hVmul, inv_mul_cancel_right])
    · push_neg at h
      calc V (t i) = V (t i * (t j)⁻¹) * V (t j) := by rw [← hVmul, inv_mul_cancel_right]
        _ ≤ 1 * V (t j) := mul_le_mul_left h.le _
        _ = V 1 * V (t j) := by simp [V]
  let m : kˣ := ∏ r, w r
  have hVprod : V m = ∏ r, V (w r) := by simp [V, m, Units.coe_prod, map_prod]
  have hm : ∀ r, V (w r) ≤ V m := by
    intro r
    rw [hVprod]
    exact Finset.single_le_prod' (fun r _ => hw1 r) (Finset.mem_univ r)
  have hm1 : 1 ≤ V m := by
    rw [hVprod]
    exact Finset.one_le_prod' (fun r _ => hw1 r)
  have key : ∀ i j, V (t i) ≤ V m * V (t j) := fun i j =>
    (hwt i j).trans (mul_le_mul_left (hm (i, j)) _)
  refine ⟨fun i => m ^ (i : ℕ), ?_, ?_⟩
  · unfold Dom
    intro a c hac
    show V (m ^ (a : ℕ)) ≤ V (m ^ (c : ℕ))
    rw [hVpow, hVpow]
    exact pow_le_pow_right₀ hm1 hac
  · unfold Dom
    intro a c hac
    show V (m ^ (a : ℕ) * t a) ≤ V (m ^ (c : ℕ) * t c)
    rw [hVmul, hVmul, hVpow, hVpow]
    rcases eq_or_lt_of_le hac with h | h
    · rw [h]
    · calc V m ^ (a : ℕ) * V (t a) ≤ V m ^ (a : ℕ) * (V m * V (t c)) := mul_le_mul_right (key a c) _
        _ = V m ^ ((a : ℕ) + 1) * V (t c) := by rw [pow_succ, mul_assoc]
        _ ≤ V m ^ (c : ℕ) * V (t c) :=
            mul_le_mul_left (pow_le_pow_right₀ hm1 (Nat.succ_le_of_lt h)) _

private theorem trOf_conj (C : Subgroup 𝓀[k]ˣ) {a b : GL (Fin n) k} (ha : a ∈ iwC k n ⊤) (hb : b ∈ iwC k n C) :
    a * b * a⁻¹ ∈ iwC k n C :=
  (memIwC k n C).2.2.1 a (((memIwC k n ⊤).1 a).1 ha).1 b hb

private theorem trOf_norm (C : Subgroup 𝓀[k]ˣ) {a : GL (Fin n) k} (ha : a ∈ iwC k n ⊤) :
    a ∈ Subgroup.normalizer (iwC k n C : Set (GL (Fin n) k)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => trOf_conj C ha hh
  · intro hh
    have h2 := trOf_conj C ((iwC k n ⊤).inv_mem ha) hh
    simpa [mul_assoc] using h2

private theorem trOf_tor (C : Subgroup 𝓀[k]ˣ) {g : GL (Fin n) k} (hg : g ∈ iwC k n ⊤) :
    ∃ τ ∈ (diagT k (Fin n)).range ⊓ iwC k n ⊤, τ⁻¹ * g ∈ iwC k n C := by
  obtain ⟨F, hU, hM, hL, hUI, hLI, -⟩ := factTorus k n ⊤
  obtain ⟨F', hU', -, hL', hUI', hLI', -⟩ := factTorus k n C
  obtain ⟨u, hu, m, hm, l', hl, rfl⟩ := F.fact g hg
  have hmT : m ∈ (diagT k (Fin n)).range := by
    rw [← hM]
    exact hm.1
  refine ⟨m, ⟨hmT, hm.2⟩, ?_⟩
  have hu' : u ∈ iwC k n C := by
    have h1 : u ∈ F'.Uf ⊓ iwC k n C := by
      rw [hUI', ← hUI]
      exact hu
    exact h1.2
  have hl' : l' ∈ iwC k n C := by
    have h1 : l' ∈ F'.Lf ⊓ iwC k n C := by
      rw [hLI', ← hLI]
      exact hl
    exact h1.2
  have hc := trOf_conj C ((iwC k n ⊤).inv_mem hm.2) hu'
  have e : m⁻¹ * (u * m * l') = (m⁻¹ * u * m⁻¹⁻¹) * l' := by group
  rw [e]
  exact (iwC k n C).mul_mem hc hl'

private theorem trOf_reps (C : Subgroup 𝓀[k]ˣ) : ∃ S : Set (GL (Fin n) k), S.Finite ∧
    (∀ τ ∈ S, τ ∈ (diagT k (Fin n)).range ⊓ iwC k n ⊤) ∧ ∀ g ∈ iwC k n ⊤, ∃ τ ∈ S, τ⁻¹ * g ∈ iwC k n C := by
  classical
  have hO : (MulAction.orbit (iwC k n ⊤) ((1 : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).Finite :=
    ((heckePairIwC k n C).2.2 ⊤).1
  have hmem : ∀ g ∈ iwC k n ⊤, ((g : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) ∈
      MulAction.orbit (iwC k n ⊤) ((1 : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) := by
    intro g hg
    refine ⟨⟨g, hg⟩, ?_⟩
    show (g : GL (Fin n) k) • ((1 : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) = _
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  have hch : ∀ q ∈ MulAction.orbit (iwC k n ⊤) ((1 : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C),
      ∃ τ, τ ∈ (diagT k (Fin n)).range ⊓ iwC k n ⊤ ∧
        ∀ g : GL (Fin n) k, (g : GL (Fin n) k ⧸ iwC k n C) = q → τ⁻¹ * g ∈ iwC k n C := by
    rintro q ⟨a, rfl⟩
    obtain ⟨τ, hτ, hτg⟩ := trOf_tor C a.2
    refine ⟨τ, hτ, fun g hg => ?_⟩
    have hg' : ((a : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) = g := by
      rw [hg]
      show _ = (a : GL (Fin n) k) • ((1 : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    rw [QuotientGroup.eq] at hg'
    have e : τ⁻¹ * g = (τ⁻¹ * (a : GL (Fin n) k)) * ((a : GL (Fin n) k)⁻¹ * g) := by group
    rw [e]
    exact (iwC k n C).mul_mem hτg hg'
  choose! r hr hr2 using hch
  refine ⟨r '' MulAction.orbit (iwC k n ⊤) ((1 : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C),
    hO.image r, ?_, ?_⟩
  · rintro τ ⟨q, hq, rfl⟩
    exact hr q hq
  · intro g hg
    exact ⟨r ((g : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C), ⟨_, hmem g hg, rfl⟩,
      hr2 _ (hmem g hg) g rfl⟩

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M)

private theorem trOf_app (C : Subgroup 𝓀[k]ˣ) (x : GL (Fin n) k) (v : fixd ρ (iwC k n C)) :
    (hk ρ (iwC k n C) x v : M) = dc ρ (iwC k n C) (iwC k n C) x v :=
  (hkApply A _ M ρ _ _ x ((heckePairIwC k n C).1 x)).1 v

private theorem trOf_unit (C : Subgroup 𝓀[k]ˣ) {a : GL (Fin n) k} (ha : a ∈ iwC k n ⊤) {v : M}
    (hv : v ∈ fixd ρ (iwC k n C)) : dc ρ (iwC k n C) (iwC k n C) a v = ρ a v :=
  (trOf_app ρ C a ⟨v, hv⟩).symm.trans ((hkNorm A _ M ρ _ a (heckePairIwC k n C).1 (trOf_norm C ha)).1 ⟨v, hv⟩)

private theorem trOf_comm (C : Subgroup 𝓀[k]ˣ) (t : Fin n → kˣ) {a : GL (Fin n) k}
    (ha : a ∈ (diagT k (Fin n)).range ⊓ iwC k n ⊤) {v : M} (hv : v ∈ fixd ρ (iwC k n C)) :
    dc ρ (iwC k n C) (iwC k n C) (diagT k (Fin n) t) (ρ a v) =
      ρ a (dc ρ (iwC k n C) (iwC k n C) (diagT k (Fin n) t) v) := by
  obtain ⟨s, rfl⟩ := ha.1
  obtain ⟨vv, rfl⟩ : ∃ vv : fixd ρ (iwC k n C), (vv : M) = v := ⟨⟨v, hv⟩, rfl⟩
  have hP := hkNorm A _ M ρ (iwC k n C) (diagT k (Fin n) s) (heckePairIwC k n C).1 (trOf_norm C ha.2)
  have hcomm : diagT k (Fin n) t * diagT k (Fin n) s = diagT k (Fin n) s * diagT k (Fin n) t := by
    rw [← map_mul, ← map_mul, mul_comm]
  have key : (hk ρ (iwC k n C) (diagT k (Fin n) t) (hk ρ (iwC k n C) (diagT k (Fin n) s) vv) : M) =
      (hk ρ (iwC k n C) (diagT k (Fin n) s) (hk ρ (iwC k n C) (diagT k (Fin n) t) vv) : M) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← (hP.2.2.2 (diagT k (Fin n) t)).2,
      ← (hP.2.2.2 (diagT k (Fin n) t)).1, hcomm]
  calc dc ρ (iwC k n C) (iwC k n C) (diagT k (Fin n) t) (ρ (diagT k (Fin n) s) vv)
      = dc ρ (iwC k n C) (iwC k n C) (diagT k (Fin n) t)
          (hk ρ (iwC k n C) (diagT k (Fin n) s) vv : M) := by rw [hP.1 vv]
    _ = (hk ρ (iwC k n C) (diagT k (Fin n) t) (hk ρ (iwC k n C) (diagT k (Fin n) s) vv) : M) :=
          (trOf_app ρ C _ _).symm
    _ = (hk ρ (iwC k n C) (diagT k (Fin n) s) (hk ρ (iwC k n C) (diagT k (Fin n) t) vv) : M) := key
    _ = ρ (diagT k (Fin n) s) (hk ρ (iwC k n C) (diagT k (Fin n) t) vv : M) := hP.1 _
    _ = ρ (diagT k (Fin n) s) (dc ρ (iwC k n C) (iwC k n C) (diagT k (Fin n) t) vv) := by
          rw [trOf_app]

private theorem trOf_lev (C : Subgroup 𝓀[k]ˣ) {t : Fin n → kˣ} (ht : Dom t) {v : M} (hv : v ∈ fixd ρ (iwC k n ⊤))
    (hv' : v ∈ fixd ρ (iwC k n C)) : dc ρ (iwC k n ⊤) (iwC k n ⊤) (diagT k (Fin n) t) v =
      dc ρ (iwC k n C) (iwC k n C) (diagT k (Fin n) t) v := by
  obtain ⟨s, -, -, h⟩ := domSum k n t ht
  have h1 := h ⊤ A M ρ ⟨v, hv⟩
  have h2 := h C A M ρ ⟨v, hv'⟩
  rw [trOf_app] at h1 h2
  exact h1.trans h2.symm

private theorem trOf_le (C : Subgroup 𝓀[k]ˣ) : iwC k n C ≤ iwC k n ⊤ := fun g hg => by
  rw [(memIwC k n C).2.1]
  exact (((memIwC k n C).1 g).1 hg).1

private theorem trOf_gen {δ : kˣ} {C : Subgroup 𝓀[k]ˣ} (h : IsGenMod k C δ) (i : Fin n) :
    Dom (Pi.mulSingle i δ : Fin n → kˣ) ∧ diagT k (Fin n) (Pi.mulSingle i δ) ∈ iwC k n ⊤ := by
  have hδ1 : valuation k (δ : k) = 1 := by
    obtain ⟨d, hd, -⟩ := h
    rw [← (memIwC k n ⊤).2.2.2]
    unfold unitsC
    exact ⟨d, Subgroup.mem_comap.mpr (Subgroup.mem_top _), hd⟩
  have hv : ∀ c, valuation k ((Pi.mulSingle i δ : Fin n → kˣ) c : k) = 1 := by
    intro c
    by_cases hc : c = i
    · subst hc
      simpa using hδ1
    · rw [Pi.mulSingle_eq_of_ne hc, Units.val_one, map_one]
  refine ⟨?_, ?_⟩
  · unfold Dom
    intro a b _
    rw [hv a, hv b]
  · rw [(memIwC k n ⊤).2.1]
    exact GlobalTheory.SmGL.diagT_mem_iwahori (show _ ∈ GlobalTheory.SmGL.torusO k (Fin n) from hv)

end Loc

private theorem trOf_ext {T A M₁ M₂ : Type} [Group T] [CommRing A] [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup M₂] [Module A M₂] (Θ : T →* (Module.End A M₁)ˣ) (θ : T →* (Module.End A M₂)ˣ) (ι : M₁ → M₂)
    (t b : T) (hb : ∀ m, (θ b).val (ι m) = ι ((Θ b).val m))
    (htb : ∀ m, (θ (b * t)).val (ι m) = ι ((Θ (b * t)).val m)) (m : M₁) :
    (θ t).val (ι m) = ι ((Θ t).val m) := by
  have h1 : (θ b).val ((θ t).val (ι m)) = (θ b).val (ι ((Θ t).val m)) := by
    calc (θ b).val ((θ t).val (ι m)) = (θ (b * t)).val (ι m) := by
          rw [map_mul, Units.val_mul, Module.End.mul_apply]
      _ = ι ((Θ (b * t)).val m) := htb m
      _ = ι ((Θ b).val ((Θ t).val m)) := by rw [map_mul, Units.val_mul, Module.End.mul_apply]
      _ = (θ b).val (ι ((Θ t).val m)) := (hb _).symm
  have key : ∀ x, ((θ b)⁻¹).val ((θ b).val x) = x := fun x => by
    rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
  rw [← key ((θ t).val (ι m)), h1, key]

private theorem trOf_commdc {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K K' : Subgroup H) (x : H) (φ : Module.End A M) (h : ∀ g, Commute φ (ρ g)) :
    Commute φ (dc ρ K K' x) := by
  have gen : ∀ {ι : Type} (f : ι → Module.End A M), (∀ i, Commute φ (f i)) → Commute φ (∑ᶠ i, f i) := by
    intro ι f hf
    by_cases hs : (Function.support f).Finite
    · show φ * (∑ᶠ i, f i) = (∑ᶠ i, f i) * φ
      rw [mul_finsum' _ _ hs, finsum_mul' _ _ hs]
      exact finsum_congr fun i => hf i
    · rw [finsum_of_infinite_support hs]
      exact Commute.zero_right φ
  unfold dc
  exact gen _ fun q => h _

private theorem trOf_sum {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (K I : Subgroup G) (S : Set G) (hf : S.Finite) (hS : ∀ τ ∈ S, τ ∈ K)
    (h : ∀ g ∈ K, ∃ τ ∈ S, τ⁻¹ * g ∈ I) : FinOrb K I 1 ∧ ∃ s : Finset G, (∀ τ ∈ s, τ ∈ S) ∧
      ∀ v : fixd ρ I, (hk2 ρ K I 1 v : M) = ∑ y ∈ s, ρ y v := by
  classical
  have hsub : MulAction.orbit K ((1 : G) : G ⧸ I) ⊆ (fun τ : G => (τ : G ⧸ I)) '' S := by
    rintro q ⟨k, rfl⟩
    obtain ⟨τ, hτS, hτ⟩ := h k k.2
    refine ⟨τ, hτS, ?_⟩
    show (τ : G ⧸ I) = (k : G) • ((1 : G) : G ⧸ I)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
    exact hτ
  have hfin : (MulAction.orbit K ((1 : G) : G ⧸ I)).Finite := (hf.image _).subset hsub
  refine ⟨hfin, ?_⟩
  have hch : ∀ q ∈ MulAction.orbit K ((1 : G) : G ⧸ I), ∃ τ ∈ S, (τ : G ⧸ I) = q :=
    fun q hq => hsub hq
  choose! r hrS hrq using hch
  refine ⟨hfin.toFinset.image r, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hτ
    exact hrS q (hfin.mem_toFinset.mp hq)
  · intro v
    refine (hkApply A G M ρ K I 1 hfin).2.1 _ ?_ ?_ v
    · intro y hy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      have hq' := hfin.mem_toFinset.mp hq
      rw [hrq q hq']
      exact hq'
    · intro q hq
      refine ⟨r q, ⟨Finset.mem_image.mpr ⟨q, hfin.mem_toFinset.mpr hq, rfl⟩, hrq q hq⟩, ?_⟩
      rintro y ⟨hy, hyq⟩
      obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hy
      have hq'' := hfin.mem_toFinset.mp hq'
      rw [hrq q' hq''] at hyq
      rw [hyq]

private theorem trOf_smul {A M₁ M₂ : Type} [CommRing A] [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
    (f : M₁ →ₗ[A] M₂) (c : A) (φ : Module.End A M₁) (ψ : Module.End A M₂) (h : ∀ m, ψ (f m) = f (φ m)) (m : M₁) :
    f ((c • φ) m) = (c • ψ) (f m) := by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, h]

section Prod

variable {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : Representation A (GV n w) M) (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ)

private theorem trOf_fix (j : Fin q) {v : M} (hv : v ∈ fixd ρ (UC n w C)) :
    v ∈ fixd (ρ.comp (atJ n w j)) (iwC _ n (C j)) := by
  intro u hu
  apply hv
  unfold UC
  rw [Subgroup.mem_pi]
  intro i _
  unfold atJ
  by_cases hij : i = j
  · subst hij
    simpa using hu
  · rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hij]
    exact one_mem _

private theorem trOf_commQ (j : Fin q) (t : Fin n → ((w j).adicCompletion L)ˣ) (τ : GV n w)
    (hτ : τ j ∈ (diagT _ (Fin n)).range ⊓ iwC ((w j).adicCompletion L) n ⊤) {v : M} (hv : v ∈ fixd ρ (UC n w C)) :
    dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) (diagT _ (Fin n) t) (ρ τ v) =
      ρ τ (dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) (diagT _ (Fin n) t) v) := by
  have hv' := trOf_fix ρ C j hv
  have hτe : τ = (τ * (atJ n w j (τ j))⁻¹) * atJ n w j (τ j) := by group
  have hcomm : ∀ g, atJ n w j g * (τ * (atJ n w j (τ j))⁻¹) =
      (τ * (atJ n w j (τ j))⁻¹) * atJ n w j g := by
    intro g
    funext i
    by_cases hij : i = j
    · subst hij
      simp [atJ]
    · simp [atJ, Pi.mulSingle_eq_of_ne hij]
  have hc : ∀ g, Commute (ρ (τ * (atJ n w j (τ j))⁻¹)) ((ρ.comp (atJ n w j)) g) := by
    intro g
    show ρ _ * ρ (atJ n w j g) = ρ (atJ n w j g) * ρ _
    rw [← map_mul, ← map_mul, hcomm g]
  have hD := trOf_commdc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) (diagT _ (Fin n) t) _ hc
  have h8 := trOf_comm (ρ.comp (atJ n w j)) (C j) t hτ hv'
  rw [hτe, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have hx := LinearMap.congr_fun hD.eq ((ρ (atJ n w j (τ j))) v)
  simp only [Module.End.mul_apply] at hx
  rw [← hx]
  exact congrArg _ h8

private theorem trOf_main (Θ1) (h1 : IsThetaQ ρ C Θ1) (Θw) (hw : IsThetaQ ρ (fun _ => ⊤) Θw) :
    FinOrb (UC n w fun _ => ⊤) (UC n w C) 1 ∧ ∀ j t (m : fixd ρ (UC n w C)),
      (Θw j t).val (hk2 ρ (UC n w fun _ => ⊤) (UC n w C) 1 m) =
        hk2 ρ (UC n w fun _ => ⊤) (UC n w C) 1 ((Θ1 j t).val m) := by
  classical
  have hreps : ∀ j, ∃ S : Set (GLw n (w j)), S.Finite ∧
      (∀ τ ∈ S, τ ∈ (diagT _ (Fin n)).range ⊓ iwC ((w j).adicCompletion L) n ⊤) ∧
      ∀ g ∈ iwC ((w j).adicCompletion L) n ⊤, ∃ τ ∈ S, τ⁻¹ * g ∈ iwC _ n (C j) :=
    fun j => trOf_reps (C j)
  choose Sj hSf hST hSg using hreps
  have hSfin : (Set.pi Set.univ Sj : Set (GV n w)).Finite := Set.Finite.pi (fun j => hSf j)
  have hSK : ∀ τ ∈ (Set.pi Set.univ Sj : Set (GV n w)), τ ∈ UC n w (fun _ => ⊤) := by
    intro τ hτ
    unfold UC
    rw [Subgroup.mem_pi]
    intro j _
    exact (hST j (τ j) (hτ j (Set.mem_univ j))).2
  have hSg' : ∀ g ∈ UC n w (fun _ => ⊤), ∃ τ ∈ (Set.pi Set.univ Sj : Set (GV n w)),
      τ⁻¹ * g ∈ UC n w C := by
    intro g hg
    unfold UC at hg
    rw [Subgroup.mem_pi] at hg
    choose τ hτS hτg using fun j => hSg j (g j) (hg j (Set.mem_univ j))
    refine ⟨τ, fun j _ => hτS j, ?_⟩
    unfold UC
    rw [Subgroup.mem_pi]
    intro j _
    exact hτg j
  obtain ⟨hfin, s, hsS, hsum⟩ :=
    trOf_sum ρ (UC n w fun _ => ⊤) (UC n w C) _ hSfin hSK hSg'
  refine ⟨hfin, ?_⟩
  have hle : UC n w C ≤ UC n w (fun _ => ⊤) := by
    intro g hg
    unfold UC at hg ⊢
    rw [Subgroup.mem_pi] at hg ⊢
    intro j hj
    exact trOf_le (C j) (hg j hj)
  have hdom : ∀ j t, Dom t → ∀ m : fixd ρ (UC n w C),
      (Θw j t).val (hk2 ρ (UC n w fun _ => ⊤) (UC n w C) 1 m) =
        hk2 ρ (UC n w fun _ => ⊤) (UC n w C) 1 ((Θ1 j t).val m) := by
    intro j t ht m
    apply Subtype.ext
    have hv : (∑ y ∈ s, ρ y (m : M)) ∈ fixd ρ (UC n w fun _ => ⊤) := by
      rw [← hsum m]
      exact (hk2 ρ _ _ 1 m).2
    have hvC := fixd_anti ρ hle hv
    rw [hw.1 j t ht, hsum, hsum, h1.1 j t ht]
    rw [trOf_lev (ρ.comp (atJ n w j)) (C j) ht (trOf_fix ρ (fun _ => ⊤) j hv) (trOf_fix ρ C j hvC)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    exact trOf_commQ ρ C j t y (hST j (y j) (hsS y hy j (Set.mem_univ j))) m.2
  intro j t m
  obtain ⟨b, hb, hbt⟩ := trOf_split t
  exact trOf_ext (Θ1 j) (Θw j) (hk2 ρ (UC n w fun _ => ⊤) (UC n w C) 1) t b
    (fun m => hdom j b hb m) (fun m => hdom j (b * t) hbt m) m

end Prod

theorem UpperTheory.V.Pa.Lev.trOf :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (l : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) (x δ : ∀ j, ((w j).adicCompletion L)ˣ) (T : ThData l ρ x δ), (∀ j, IsGenMod _ (ellC l _) (δ j)) → (∀ j i (m : fixd ρ (UC n w fun _ => ellC l _)), (T.act1 (1 + yV A j i) m : M) = ρ (atJ n w j (diagT _ (Fin n) (Pi.mulSingle i (δ j)))) m) ∧ ∃ tr : fixd ρ (UC n w fun _ => ellC l _) →ₗ[A] fixd ρ (UC n w fun _ => ⊤), (∀ m, (tr m : M) = dc ρ (UIw n w) (UIw1 l n w) 1 m) ∧ ∀ j i m, tr (T.act1 (uV A j i) m) = T.actw (MvPolynomial.X (j, i)) (tr m) := by
  intro L _ _ n q w l A M _ _ _ ρ x δ T hδ
  obtain ⟨hF, hm⟩ := trOf_main ρ (fun _ => ellC l _) T.Θ1 T.h1 T.Θw T.hw
  refine ⟨fun j i m => ?_, hk2 ρ (UC n w fun _ => ⊤) (UC n w fun _ => ellC l _) 1, fun m => ?_, fun j i m => ?_⟩
  · obtain ⟨hd, hi⟩ := trOf_gen (hδ j) i
    rw [T.act_yVariable, T.h1.1 j _ hd]
    exact trOf_unit (ρ.comp (atJ n w j)) (ellC l _) hi (trOf_fix ρ (fun _ => ellC l _) j m.2)
  · rw [UIw_eq, UIw1_eq]
    exact (hkApply A (GV n w) M ρ (UC n w fun _ => ⊤) (UC n w fun _ => ellC l _) 1 hF).1 m
  · rw [T.act_uVariable_eq_pow, T.actw_u]
    exact trOf_smul _ _ _ _ (hm j _) m
