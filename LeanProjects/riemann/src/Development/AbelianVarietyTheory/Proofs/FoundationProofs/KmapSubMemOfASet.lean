import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.GalCont

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem exp_inj (X : Tower Ω ε) : Function.Injective X.exp :=
  X.exp.toRingHom.injective

theorem gal_eq_of_coeff (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K)
    (h : ∀ r, s ((X.exp f).coeff r) = (X.exp f).coeff r) : X.gal s f = f := by
  apply exp_inj X
  ext r
  rw [X.gal_exp]
  exact h r

theorem coeff_alg (c : Ω) (r : ℚ) :
    ((algebraMap Ω (HahnSeries ℚ Ω)) c).coeff r = if r = 0 then c else 0 := by
  rw [HahnSeries.algebraMap_apply']
  simp [PowerSeries.algebraMap_apply, HahnSeries.coeff_single, eq_comm]

theorem gal_algebraMap (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) (hc : s c = c) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K c := by
  apply gal_eq_of_coeff
  intro r
  rw [AlgHom.commutes, coeff_alg]
  split_ifs
  · exact hc
  · exact map_zero s

theorem gal_j (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : X.gal s X.jK = X.jK := by
  apply gal_eq_of_coeff
  intro r
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [hn, map_intCast]

def fixSet (X : Tower Ω ε) : Set X.K :=
  {f | ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) → X.gal s f = f}

def fixField (X : Tower Ω ε) : IntermediateField Ω X.K where
  carrier := fixSet X
  mul_mem' := by
    classical
    rintro a b ⟨E, hE⟩ ⟨F, hF⟩
    refine ⟨E ∪ F, fun s hs => ?_⟩
    rw [map_mul, hE s (fun x hx => hs x (Finset.mem_union_left _ hx)),
      hF s (fun x hx => hs x (Finset.mem_union_right _ hx))]
  add_mem' := by
    classical
    rintro a b ⟨E, hE⟩ ⟨F, hF⟩
    refine ⟨E ∪ F, fun s hs => ?_⟩
    rw [map_add, hE s (fun x hx => hs x (Finset.mem_union_left _ hx)),
      hF s (fun x hx => hs x (Finset.mem_union_right _ hx))]
  algebraMap_mem' c := ⟨{c}, fun s hs => gal_algebraMap X s c (hs c (Finset.mem_singleton_self c))⟩
  inv_mem' := by
    rintro a ⟨E, hE⟩
    exact ⟨E, fun s hs => by rw [map_inv₀, hE s hs]⟩

theorem adjoin_le_fix (X : Tower Ω ε) : IntermediateField.adjoin Ω {X.jK} ≤ fixField X := by
  rw [IntermediateField.adjoin_simple_le_iff]
  exact ⟨∅, fun s _ => gal_j X s⟩

theorem fix_fin (X : Tower Ω ε) (f : X.K) :
    ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) → X.gal s f = f := by
  classical
  obtain ⟨p, hp0, hpf⟩ := X.alg_j f
  obtain ⟨q, hq⟩ : ∃ q : Polynomial X.K, q = p.map (algebraMap (IntermediateField.adjoin Ω {X.jK}) X.K) := ⟨_, rfl⟩
  have hq0 : q ≠ 0 := hq ▸ (Polynomial.map_ne_zero_iff (algebraMap (IntermediateField.adjoin Ω {X.jK}) X.K).injective).2 hp0
  have hqf : q.eval f = 0 := by
    rw [hq, Polynomial.eval_map_algebraMap]; exact hpf
  have hcoef : ∀ i, ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) →
      X.gal s (q.coeff i) = q.coeff i := by
    intro i
    rw [hq, Polynomial.coeff_map]
    exact adjoin_le_fix X (p.coeff i).2
  choose Ec hEc using hcoef
  have hex : ∀ g : X.K, g ≠ f → ∃ r, (X.exp g).coeff r ≠ (X.exp f).coeff r := by
    intro g hg
    by_contra h
    push_neg at h
    exact hg (exp_inj X (HahnSeries.ext (funext h)))
  choose rr hrr using hex
  let E1 : Finset Ω := q.support.biUnion Ec
  let E2 : Finset Ω := q.roots.toFinset.image
    (fun g => if h : g = f then 0 else (X.exp f).coeff (rr g h))
  refine ⟨E1 ∪ E2, fun s hs => ?_⟩
  have hmap : q.map (X.gal s).toRingHom = q := by
    ext i
    rw [Polynomial.coeff_map]
    by_cases hi : i ∈ q.support
    · exact hEc i s (fun x hx => hs x (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨i, hi, hx⟩)))
    · rw [Polynomial.notMem_support_iff.1 hi, map_zero]
  have hroot : X.gal s f ∈ q.roots := by
    rw [Polynomial.mem_roots hq0, Polynomial.IsRoot.def]
    have := Polynomial.eval₂_hom (X.gal s).toRingHom f (p := q)
    rw [← Polynomial.eval_map, hmap] at this
    simpa [hqf] using this
  by_contra hne
  have hmem : (X.exp f).coeff (rr _ hne) ∈ E2 :=
    Finset.mem_image.2 ⟨X.gal s f, Multiset.mem_toFinset.2 hroot, by rw [dif_neg hne]⟩
  apply hrr _ hne
  rw [X.gal_exp]
  exact hs _ (Finset.mem_union_right _ hmem)

theorem kmap_sub_mem_of_ASet (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.Khat l) (ha : a ∈ X.ASet l)
    (n : ℕ) : ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) →
      X.kmap l (X.gal s) a - a ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  obtain ⟨f, -, hf⟩ := ha n
  obtain ⟨E, hE⟩ := fix_fin X (f : X.K)
  refine ⟨E, fun s hs => ?_⟩
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker,
    map_sub, sub_eq_zero]
  rw [AdicCompletion.eval_apply, AdicCompletion.eval_apply]
  change (AdicCompletion.map _ _ a).val n = a.val n
  rw [AdicCompletion.map_val_apply, ← AdicCompletion.eval_apply, hf]
  rw [Tower.cls, LinearMap.reduceModIdeal_apply, LinearMap.baseChange_tmul]
  have hu : Units.map (X.gal s).toMonoidHom f = f := Units.ext (hE s hs)
  congr 2

theorem cyc_sub_one_mem [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) →
      ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) - 1) ∈ (idl l) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨∅, fun _ _ => by simp⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero⟩
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  refine ⟨{ζ}, fun s hs => ?_⟩
  have h1 := cyclotomicCharacter.spec l (n := n) s.toRingEquiv ζ hζ.pow_eq_one
  have hsz : s.toRingEquiv ζ = ζ := hs ζ (Finset.mem_singleton_self ζ)
  rw [hsz] at h1
  set v := (cyclotomicCharacter Ω l s.toRingEquiv).val.toZModPow n with hv
  have h2 : v = 1 := by
    have hlt : 1 < l ^ n := Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt
    have hval : v.val = 1 := hζ.pow_inj (ZMod.val_lt v) hlt (by rw [pow_one]; exact h1.symm)
    rw [← ZMod.natCast_zmod_val v, hval, Nat.cast_one]
  rw [idl, Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, ← hv, h2,
    map_one, sub_self]

theorem kmap_sub_mem_A (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (c : X.Khat l) (hc : c ∈ X.A l) (n : ℕ) :
    ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) →
      X.kmap l (X.gal s) c - c ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  classical
  induction hc using Submodule.span_induction with
  | mem a ha => exact kmap_sub_mem_of_ASet X l a ha n
  | zero => exact ⟨∅, fun s _ => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨E, hE⟩ := ha
    obtain ⟨F, hF⟩ := hb
    refine ⟨E ∪ F, fun s hs => ?_⟩
    have := Submodule.add_mem _ (hE s fun x hx => hs x (Finset.mem_union_left _ hx))
      (hF s fun x hx => hs x (Finset.mem_union_right _ hx))
    rw [map_add]
    convert this using 1
    abel
  | smul r a _ ha =>
    obtain ⟨E, hE⟩ := ha
    refine ⟨E, fun s hs => ?_⟩
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ r (hE s hs)

theorem galB_sub_mem_of_Pol [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (b : X.Fn l)
    (hb : b ∈ X.Pol l w) (n : ℕ) :
    ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) →
      ∀ u, (X.galB l s b - b) u ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  classical
  obtain ⟨c, hcA, hbc⟩ := hb
  choose Ec hEc using fun i => kmap_sub_mem_A X l (c i) (hcA i) n
  obtain ⟨Ez, hEz⟩ := cyc_sub_one_mem (Ω := Ω) l n
  refine ⟨Ez ∪ Finset.univ.biUnion Ec, fun s hs u => ?_⟩
  have hχ := hEz s (fun x hx => hs x (Finset.mem_union_left _ hx))
  have hk : ∀ i, X.kmap l (X.gal s) (c i) - c i ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) :=
    fun i => hEc i s (fun x hx => hs x (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩)))
  set χ := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hχdef
  have hgal : X.galB l s b u = X.kmap l (X.gal s) (b ![u 0, χ * u 1]) := rfl
  rw [Pi.sub_apply, hgal, hbc, hbc, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  simp only [map_smul, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hpow : χ ^ (w - (i : ℕ)) - 1 ∈ (idl l) ^ n := by
    obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow χ 1 (w - (i : ℕ))
    rw [one_pow] at hd
    rw [hd]
    exact Ideal.mul_mem_right _ _ hχ
  have heq : (u 0 ^ (i : ℕ) * (χ * u 1) ^ (w - (i : ℕ))) • X.kmap l (X.gal s) (c i) -
      (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i =
      (u 0 ^ (i : ℕ) * (χ * u 1) ^ (w - (i : ℕ))) • (X.kmap l (X.gal s) (c i) - c i) +
      ((u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) * (χ ^ (w - (i : ℕ)) - 1)) • c i := by
    rw [mul_pow]
    module
  rw [heq]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hk i))
    (Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ hpow) Submodule.mem_top)

theorem galB_cont : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ b ∈ X.B N l w, ∀ n : ℕ,
    ∃ E0 : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s x = x) → ∀ u,
      (X.galB l s b - b) u ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  intro Ω _ _ _ ε X _ _ N l w _ _ _ _ _ b hb n
  classical
  induction hb using Submodule.span_induction with
  | mem b hb => exact galB_sub_mem_of_Pol X l w b hb.1 n
  | zero => exact ⟨∅, fun s _ u => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨E, hE⟩ := ha
    obtain ⟨F, hF⟩ := hb
    refine ⟨E ∪ F, fun s hs u => ?_⟩
    have := Submodule.add_mem _ (hE s (fun x hx => hs x (Finset.mem_union_left _ hx)) u)
      (hF s (fun x hx => hs x (Finset.mem_union_right _ hx)) u)
    rw [map_add]
    convert this using 1
    simp only [LinearMap.sub_apply, Pi.add_apply, Pi.sub_apply]
    abel
  | smul r a _ ha =>
    obtain ⟨E, hE⟩ := ha
    refine ⟨E, fun s hs u => ?_⟩
    have := Submodule.smul_mem _ r (hE s hs u)
    rw [map_smul]
    convert this using 1
    simp only [LinearMap.sub_apply, Pi.smul_apply, Pi.sub_apply, smul_sub]

end GlobalTheory.KZ.GalCont
