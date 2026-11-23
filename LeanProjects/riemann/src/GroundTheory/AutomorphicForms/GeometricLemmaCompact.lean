import Mathlib
import GroundTheory.AutomorphicForms.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemmaOrbit
import GroundTheory.AutomorphicForms.AdmissibleInduction
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Bounds

variable (F) in

abbrev EntryBound (e : ℕ) (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j, (uniformizer F : F) ^ e * A i j ∈ 𝒪[F]

theorem EntryBound.mul {a b : ℕ} {A B : Matrix (Fin n) (Fin n) F} (hA : EntryBound F a A)
    (hB : EntryBound F b B) : EntryBound F (a + b) (A * B) := by
  intro i j
  rw [mul_apply, Finset.mul_sum]
  refine sum_mem fun k _ => ?_
  have := mul_mem (hA i k) (hB k j)
  convert this using 1
  ring

theorem entryBound_of_isCompact {S : Set (GL (Fin n) F)} (hS : IsCompact S) :
    ∃ e : ℕ, ∀ g ∈ S, EntryBound F e (g : Matrix (Fin n) (Fin n) F) ∧
      EntryBound F e ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨e, he⟩ := exists_pow_mul_mem_of_isCompact F n (hS.union (hS.image continuous_inv))
  exact ⟨e, fun g hg => ⟨fun i j => he g (Or.inl hg) i j,
    fun i j => he g⁻¹ (Or.inr ⟨g, hg, rfl⟩) i j⟩⟩

theorem EntryBound.leviProj {γ : Fin n → ℕ} {e : ℕ} {p : blockUpper F n γ}
    (hp : EntryBound F e ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    EntryBound F e (((leviProj F n γ p : levi F n γ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  intro i j
  rw [leviProj_apply]
  split_ifs
  · exact hp i j
  · rw [mul_zero]
    exact zero_mem _

end Bounds

section UnipotentCompact

variable (γ : Fin n → ℕ)

def unipotentCompactG (e : ℕ) : Subgroup (GL (Fin n) F) :=
  (unipotentCompact F n γ e).map (unipotentRadical F n γ).subtype

variable {γ}

theorem unipotentCompactG_le (e : ℕ) :
    unipotentCompactG (F := F) γ e ≤ unipotentRadical F n γ := by
  rintro _ ⟨u, -, rfl⟩
  exact u.2

theorem mem_unipotentCompactG {e : ℕ} {u : GL (Fin n) F} :
    u ∈ unipotentCompactG γ e ↔ u ∈ unipotentRadical F n γ ∧
      rankTorus F n γ e * u * (rankTorus F n γ e)⁻¹ ∈ integralGL F n := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, mem_unipotentCompact.1 hv⟩
  · rintro ⟨hu, h⟩
    exact ⟨⟨u, hu⟩, mem_unipotentCompact.2 h, rfl⟩

theorem isCompact_unipotentCompactG (e : ℕ) :
    IsCompact (unipotentCompactG (F := F) γ e : Set (GL (Fin n) F)) := by
  rw [unipotentCompactG, Subgroup.coe_map]
  exact (isCompact_unipotentCompact e).image continuous_subtype_val

theorem unipotentCompactG_eq (e : ℕ) :
    unipotentCompactG (F := F) γ e = unipotentRadical F n γ ⊓
      (integralGL F n).comap (MulAut.conj (rankTorus F n γ e)).toMonoidHom := by
  ext u
  rw [mem_unipotentCompactG, Subgroup.mem_inf, Subgroup.mem_comap]
  rfl

theorem isOpen_conj_integralGL (t : GL (Fin n) F) :
    IsOpen (((integralGL F n).comap (MulAut.conj t).toMonoidHom : Subgroup (GL (Fin n) F)) :
      Set (GL (Fin n) F)) :=
  (isOpen_integralGL F n).preimage (conjHomeomorph t).continuous

theorem mem_unipotentCompactG_of_bound {e : ℕ} {u : GL (Fin n) F}
    (hu : u ∈ unipotentRadical F n γ)
    (hb : EntryBound F e (u : Matrix (Fin n) (Fin n) F))
    (hb' : EntryBound F e ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    u ∈ unipotentCompactG γ e :=
  ⟨⟨u, hu⟩, mem_unipotentCompact_of_bound (u := ⟨u, hu⟩) hb hb', rfl⟩

theorem unipotentCompactG_mono {e e' : ℕ} (h : e ≤ e') :
    unipotentCompactG (F := F) γ e ≤ unipotentCompactG γ e' := by
  intro u hu
  obtain ⟨huN, hu'⟩ := mem_unipotentCompactG.1 hu
  refine mem_unipotentCompactG.2 ⟨huN, ?_⟩
  have key : ∀ v ∈ unipotentRadical F n γ,
      (rankTorus F n γ e * v * (rankTorus F n γ e)⁻¹ : GL (Fin n) F) ∈ integralGL F n →
        ∀ i j, ((rankTorus F n γ e' * v * (rankTorus F n γ e')⁻¹ : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := by
    intro v hv hint i j
    have hij := ((mem_integralGL_iff F n).1 hint).1 i j
    rw [rankTorus_conj_apply] at hij ⊢
    obtain ⟨hvP, hv1⟩ := mem_unipotentRadical.1 hv
    rcases lt_trichotomy (γ i) (γ j) with hlt | heq | hgt
    · have hr := blockRank_lt hlt
      have : (((e' * blockRank γ j : ℕ) : ℤ) - ((e' * blockRank γ i : ℕ) : ℤ)) =
          (((e * blockRank γ j : ℕ) : ℤ) - ((e * blockRank γ i : ℕ) : ℤ)) +
            (((e' - e) * (blockRank γ j - blockRank γ i) : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub h, Nat.cast_sub hr.le]
        ring
      rw [this, zpow_add₀ uniformizer_ne_zero, zpow_natCast]
      have e1 : ((GLnLocal.uniformizer F : F) ^ ((((e * blockRank γ j : ℕ) : ℤ) -
          ((e * blockRank γ i : ℕ) : ℤ))) *
            (GLnLocal.uniformizer F : F) ^ ((e' - e) * (blockRank γ j - blockRank γ i))) *
              (v : Matrix (Fin n) (Fin n) F) i j =
          ((GLnLocal.uniformizer F : F) ^ ((((e * blockRank γ j : ℕ) : ℤ) -
            ((e * blockRank γ i : ℕ) : ℤ))) * (v : Matrix (Fin n) (Fin n) F) i j) *
            (GLnLocal.uniformizer F : F) ^ ((e' - e) * (blockRank γ j - blockRank γ i)) := by
        ring
      rw [e1]
      exact mul_mem hij (pow_mem (GLnLocal.uniformizer F).2 _)
    · rw [blockRank_eq heq, sub_self] at hij ⊢
      exact hij
    · rw [hvP hgt, mul_zero]
      exact zero_mem _
  rw [mem_integralGL_iff F n]
  refine ⟨key u huN hu', ?_⟩
  intro i j
  have : (rankTorus F n γ e' * u * (rankTorus F n γ e')⁻¹)⁻¹ =
      rankTorus F n γ e' * u⁻¹ * (rankTorus F n γ e')⁻¹ := by group
  rw [this]
  have h' : (rankTorus F n γ e * u * (rankTorus F n γ e)⁻¹)⁻¹ =
      rankTorus F n γ e * u⁻¹ * (rankTorus F n γ e)⁻¹ := by group
  have hinv := (integralGL F n).inv_mem hu'
  rw [h'] at hinv
  exact key u⁻¹ ((unipotentRadical F n γ).inv_mem huN) hinv i j

end UnipotentCompact

section Support

variable {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}

theorem isClopen_support_parabolicInd (f : parabolicIndSpace F n β σ) :
    IsClopen {g : GL (Fin n) F | (f : GL (Fin n) F → W) g ≠ 0} := by
  obtain ⟨-, K, hKo, hK⟩ := (mem_parabolicIndSpace σ).1 f.2
  have hnhds : ∀ g : GL (Fin n) F, (fun k => g * k) '' (K : Set (GL (Fin n) F)) ∈ 𝓝 g := by
    intro g
    have := (isOpenMap_mul_left g).image_mem_nhds (hKo.mem_nhds K.one_mem)
    simpa using this
  have hval : ∀ g, ∀ x ∈ (fun k => g * k) '' (K : Set (GL (Fin n) F)),
      (f : GL (Fin n) F → W) x = (f : GL (Fin n) F → W) g := by
    rintro g _ ⟨k, hk, rfl⟩
    exact hK k hk g
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro g hg
    refine Filter.mem_of_superset (hnhds g) fun x hx => ?_
    simp only [mem_compl_iff, mem_ofPred_eq, not_not] at hg ⊢
    rw [hval g x hx, hg]
  · rw [isOpen_iff_mem_nhds]
    intro g hg
    refine Filter.mem_of_superset (hnhds g) fun x hx => ?_
    simp only [mem_ofPred_eq] at hg ⊢
    rw [hval g x hx]
    exact hg

variable (w : Equiv.Perm (Fin n))

theorem exists_isCompact_support_doubleCoset {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
    (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ))
    {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y) :
    ∃ L : Set (GL (Fin n) F), IsCompact L ∧ L ⊆ blockUpper F n γ ∧
      ∀ q ∈ blockUpper F n γ, (f : GL (Fin n) F → W) (permGL F w * q) ≠ 0 →
        ∃ x ∈ blockUpper F n γ, permGL F w * x * (permGL F w)⁻¹ ∈ blockUpper F n β ∧
          ∃ l ∈ L, q = x * l := by
  set C := doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)
  set S := {g : GL (Fin n) F | (f : GL (Fin n) F → W) g ≠ 0}
  have hS := isClopen_support_parabolicInd f
  have hSY : S ⊆ Y := fun g hg => by
    by_contra hgY
    exact hg (hf g hgY)
  set Kc := (integralGL F n : Set (GL (Fin n) F)) ∩ (S ∩ closure C)
  have hKc : IsCompact Kc := (isCompact_integralGL F n).inter_right (hS.1.inter isClosed_closure)
  have hKcC : Kc ⊆ C := by
    rintro g ⟨-, hgS, hgC⟩
    rw [← hCY]
    exact ⟨hgC, hSY hgS⟩
  have hCl : IsLocallyClosed C := ⟨Y, closure C, hYo, isClosed_closure, by rw [inter_comm, hCY]⟩
  obtain ⟨L, hL, hLQ, hKL⟩ := exists_isCompact_subset_doubleCoset
    (Measures.isClosed_blockUpper F n β) (Measures.isClosed_blockUpper F n γ) hCl hKc hKcC
  refine ⟨L, hL, hLQ, fun q hq hfq => ?_⟩
  obtain ⟨p, hp, k, hk, hpk⟩ := exists_blockUpper_mul_integralGL' (β := β) (permGL F w * q)
  have hfk : (f : GL (Fin n) F → W) k ≠ 0 := by
    intro h0
    apply hfq
    rw [hpk, ((mem_parabolicIndSpace σ).1 f.2).1 ⟨p, hp⟩ k, h0, map_zero, smul_zero]
  have hkC : k ∈ C := by
    refine mem_doubleCoset.2 ⟨p⁻¹, (blockUpper F n β).inv_mem hp, q, hq, ?_⟩
    rw [mul_assoc, hpk, inv_mul_cancel_left]
  obtain ⟨p', hp', l, hl, hkl⟩ := hKL k ⟨hk, hfk, subset_closure hkC⟩
  refine ⟨q * l⁻¹, (blockUpper F n γ).mul_mem hq ((blockUpper F n γ).inv_mem (hLQ hl)), ?_, l, hl,
    by group⟩
  have : permGL F w * (q * l⁻¹) * (permGL F w)⁻¹ = p * p' := by
    have h1 : permGL F w * q = p * (p' * permGL F w * l) := by rw [hpk, hkl]
    calc permGL F w * (q * l⁻¹) * (permGL F w)⁻¹
        = (permGL F w * q) * l⁻¹ * (permGL F w)⁻¹ := by group
      _ = p * p' := by rw [h1]; group
  rw [this]
  exact (blockUpper F n β).mul_mem hp hp'

theorem exists_unipotentCompactG_support {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
    (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ))
    {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y) {m : GL (Fin n) F}
    (hm : m ∈ levi F n γ) :
    ∃ e : ℕ, ∀ u ∈ unipotentRadical F n γ, (f : GL (Fin n) F → W) (permGL F w * u * m) ≠ 0 →
      ∃ a ∈ unipotentRadical F n γ, permGL F w * a * (permGL F w)⁻¹ ∈ blockUpper F n β ∧
        ∃ v ∈ unipotentCompactG γ e, u = a * v := by
  obtain ⟨L, hL, hLQ, hsupp⟩ := exists_isCompact_support_doubleCoset w hYo hCY hf
  obtain ⟨e₀, he₀⟩ := entryBound_of_isCompact hL
  obtain ⟨e₁, he₁⟩ := entryBound_of_isCompact (isCompact_singleton (x := m))
  obtain ⟨hmb, hmb'⟩ := he₁ m rfl
  refine ⟨e₁ + e₀ + e₀ + e₁, fun u hu hfu => ?_⟩
  have hmQ : m ∈ blockUpper F n γ := levi_le_blockUpper hm
  have huQ : u ∈ blockUpper F n γ := unipotentRadical_le_blockUpper hu
  obtain ⟨x, hxQ, hxP, l, hl, hum⟩ := hsupp (u * m) ((blockUpper F n γ).mul_mem huQ hmQ)
    (by rwa [← mul_assoc])
  have hlQ := hLQ hl

  set b : levi F n γ := leviProj F n γ ⟨x, hxQ⟩
  set c : levi F n γ := leviProj F n γ ⟨l, hlQ⟩
  have hbc : (b : GL (Fin n) F) = m * (c : GL (Fin n) F)⁻¹ := by
    have h1 : leviProj F n γ ⟨u * m, (blockUpper F n γ).mul_mem huQ hmQ⟩ = b * c := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hum
    have h2 : leviProj F n γ ⟨u * m, (blockUpper F n γ).mul_mem huQ hmQ⟩ = ⟨m, hm⟩ := by
      have : (⟨u * m, (blockUpper F n γ).mul_mem huQ hmQ⟩ : blockUpper F n γ) =
          ⟨u, huQ⟩ * ⟨m, hmQ⟩ := rfl
      rw [this, map_mul, (mem_unipotentRadical_iff_leviProj (p := ⟨u, huQ⟩)).1 hu, one_mul]
      exact leviProj_of_mem_levi hm
    rw [h2] at h1
    have := congrArg (fun z : levi F n γ => (z : GL (Fin n) F)) h1
    simp only [Subgroup.coe_mul] at this
    rw [this]
    group

  have hbQ : (b : GL (Fin n) F) ∈ blockUpper F n γ := levi_le_blockUpper b.2
  have haQ : x * (b : GL (Fin n) F)⁻¹ ∈ blockUpper F n γ :=
    (blockUpper F n γ).mul_mem hxQ ((blockUpper F n γ).inv_mem hbQ)
  have haN : x * (b : GL (Fin n) F)⁻¹ ∈ unipotentRadical F n γ := by
    rw [show x * (b : GL (Fin n) F)⁻¹ = ((⟨x, hxQ⟩ * (leviIncl b)⁻¹ : blockUpper F n γ) :
      GL (Fin n) F) from rfl, mem_unipotentRadical_iff_leviProj, map_mul, map_inv,
      leviProj_leviIncl, mul_inv_cancel]
  have hxβ : x ∈ blockUpper F n (β ∘ w) := (conj_permGL_mem_blockUpper_iff w).1 hxP
  have hbβ : (b : GL (Fin n) F) ∈ blockUpper F n (β ∘ w) := by
    intro i j hij
    show ((leviProj F n γ ⟨x, hxQ⟩ : levi F n γ) : GL (Fin n) F) i j = 0
    rw [leviProj_apply]
    split_ifs
    · exact hxβ hij
    · rfl
  refine ⟨x * (b : GL (Fin n) F)⁻¹, haN, (conj_permGL_mem_blockUpper_iff w).2
    ((blockUpper F n (β ∘ w)).mul_mem hxβ ((blockUpper F n (β ∘ w)).inv_mem hbβ)),
    (b : GL (Fin n) F) * l * m⁻¹, ?_, ?_⟩
  · have hv : (b : GL (Fin n) F) * l * m⁻¹ = m * (c : GL (Fin n) F)⁻¹ * l * m⁻¹ := by rw [hbc]
    have hvN : (b : GL (Fin n) F) * l * m⁻¹ ∈ unipotentRadical F n γ := by
      have : (b : GL (Fin n) F) * l * m⁻¹ = (x * (b : GL (Fin n) F)⁻¹)⁻¹ * u := by
        rw [show u = x * l * m⁻¹ by rw [← hum]; group]
        group
      rw [this]
      exact (unipotentRadical F n γ).mul_mem ((unipotentRadical F n γ).inv_mem haN) hu
    obtain ⟨hlb, hlb'⟩ := he₀ l hl
    have hcinv : ((c : GL (Fin n) F)⁻¹ : GL (Fin n) F) =
        ((leviProj F n γ ⟨l⁻¹, (blockUpper F n γ).inv_mem hlQ⟩ : levi F n γ) : GL (Fin n) F) := by
      rw [show (⟨l⁻¹, (blockUpper F n γ).inv_mem hlQ⟩ : blockUpper F n γ) = (⟨l, hlQ⟩)⁻¹ from rfl,
        map_inv]
      rfl
    have hcb' : EntryBound F e₀ (((c : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [hcinv]
      exact EntryBound.leviProj (p := ⟨l⁻¹, (blockUpper F n γ).inv_mem hlQ⟩) hlb'
    have hcb : EntryBound F e₀ ((c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
      EntryBound.leviProj (p := ⟨l, hlQ⟩) hlb
    refine mem_unipotentCompactG_of_bound hvN ?_ ?_
    · rw [hv]
      simp only [Units.val_mul]
      exact ((hmb.mul hcb').mul hlb).mul hmb'
    · have : ((b : GL (Fin n) F) * l * m⁻¹)⁻¹ = m * l⁻¹ * (c : GL (Fin n) F) * m⁻¹ := by
        rw [hbc]
        group
      rw [this]
      simp only [Units.val_mul]
      exact ((hmb.mul hlb').mul hcb).mul hmb'
  · rw [show u = x * l * m⁻¹ by rw [← hum]; group]
    group

end Support

end Parabolic

end GroundTheory.Automorphic
