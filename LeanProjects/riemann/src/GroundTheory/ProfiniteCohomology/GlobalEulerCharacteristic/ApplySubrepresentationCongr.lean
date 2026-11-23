import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.MainCoind
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.PowDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u w

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] {R : Type w} [CommMonoid R]

omit [CommMonoid R] in

theorem apply_subrepresentation_congr (χ : (A : Rep.{u} k G) → [IsDiscreteRep A] → R)
    {A : Rep.{u} k G} [IsDiscreteRep A] {W W' : Submodule k A} (h : W = W')
    (hW : ∀ g, W ≤ W.comap (A.ρ g)) (hW' : ∀ g, W' ≤ W'.comap (A.ρ g)) :
    χ (Rep.subrepresentation A W hW) = χ (Rep.subrepresentation A W' hW') := by
  subst h
  rfl

namespace IsMultiplicativeOn

variable {P : ℕ → Prop} {χ : (A : Rep.{u} k G) → [IsDiscreteRep A] → R}

theorem rangeStep (hχ : IsMultiplicativeOn P χ) (hPdvd : ∀ m n, m ∣ n → P n → P m)
    {A : Rep.{u} k G} [IsDiscreteRep A] [Finite A] (T : Module.End k A)
    (hT : ∀ g : G, Commute T (A.ρ g)) (D : Submodule k A) (hD : ∀ g : G, D ≤ D.comap (A.ρ g))
    (hA : P (Nat.card A)) :
    χ (Rep.subrepresentation A D hD) =
      χ (Rep.subrepresentation A _ (inf_ker_le_comap T hT D hD)) *
        χ (Rep.subrepresentation A _ (map_le_comap T hT D hD)) := by
  have hdvd : Nat.card D ∣ Nat.card A :=
    AddSubgroup.card_addSubgroup_dvd_card D.toAddSubgroup
  exact hχ.shortExact (rangeStepComplex_shortExact T hT D hD) (hPdvd _ _ hdvd hA)

variable [IsTopologicalGroup G] [CompactSpace G]

theorem coind_res_eq_pow (hχ : IsMultiplicativeOn P χ) (hPdvd : ∀ m n, m ∣ n → P n → P m)
    (hPmul : ∀ m n, P m → P n → P (m * n)) (H : OpenSubgroup G)
    [hN : (H : Subgroup G).Normal] [IsCyclic (G ⧸ (H : Subgroup G))] {p a : ℕ} [hp : Fact p.Prime]
    (hcard : Nat.card (G ⧸ (H : Subgroup G)) = p ^ a) (M : Rep.{u} k G) [IsDiscreteRep M]
    [Finite M] (hM : P (Nat.card M)) (hpM : ∀ m : M, p • m = 0) :
    χ (Rep.coind (H : Subgroup G).subtype (Rep.res (H : Subgroup G).subtype M)) =
      χ M ^ (p ^ a) := by
  have hQ : Finite (G ⧸ (H : Subgroup G)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.out.ne_zero)
  obtain ⟨q, hq⟩ := IsCyclic.exists_generator (α := G ⧸ (H : Subgroup G))
  have hmk : (QuotientGroup.mk (Quotient.out q) : G ⧸ (H : Subgroup G)) = q :=
    QuotientGroup.out_eq' q
  set s : G := Quotient.out q

  have hs : ∀ g : G, s * g * s⁻¹ * g⁻¹ ∈ (H : Subgroup G) := by
    intro g
    have hc : (QuotientGroup.mk (g * s) : G ⧸ (H : Subgroup G)) = QuotientGroup.mk (s * g) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact (IsCyclic.commGroup (α := G ⧸ (H : Subgroup G))).mul_comm _ _
    have h2 := hN.conj_mem _ (QuotientGroup.eq.1 hc) (g * s)
    have e : s * g * s⁻¹ * g⁻¹ = g * s * ((g * s)⁻¹ * (s * g)) * (g * s)⁻¹ := by group
    rw [e]
    exact h2
  have hsN : s ^ (p ^ a) ∈ (H : Subgroup G) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hmk, ← hcard]
    exact pow_card_eq_one'
  have hgen : ∀ x : G, ∃ i : ℕ, x * (s ^ i)⁻¹ ∈ (H : Subgroup G) := by
    intro x
    obtain ⟨i, hi⟩ := mem_powers_iff_mem_zpowers.2 (hq (QuotientGroup.mk x))
    refine ⟨i, ?_⟩
    have h1 : (QuotientGroup.mk x : G ⧸ (H : Subgroup G)) = QuotientGroup.mk (s ^ i) := by
      rw [QuotientGroup.mk_pow, hmk]
      exact hi.symm
    have h3 := hN.conj_mem _ (inv_mem (QuotientGroup.eq.1 h1)) x
    have e : x * (s ^ i)⁻¹ = x * (x⁻¹ * s ^ i)⁻¹ * x⁻¹ := by group
    rw [e]
    exact h3

  set T : Module.End k (coindRes H M) := coindT (H := H) (M := M) s with hT_def
  have hT : ∀ g : G, Commute T ((coindRes H M).ρ g) := commute_coindShift_sub_one hs
  have hCp : ∀ f : coindRes H M, p • f = 0 := fun f =>
    Subtype.ext (funext fun x => hpM (f.1 x))
  have hTN : T ^ (p ^ a) = 0 :=
    sub_one_pow_prime_pow_eq_zero hCp (coindShift (H := H) (M := M) s) a (coindShift_pow_eq_one hsN)
  let D : ℕ → Submodule k (coindRes H M) := fun j => LinearMap.range (T ^ j)
  have hD : ∀ j (g : G), D j ≤ (D j).comap ((coindRes H M).ρ g) := by
    rintro j g _ ⟨y, rfl⟩
    exact ⟨(coindRes H M).ρ g y, by
      rw [← Module.End.mul_apply, ((hT g).pow_left j).eq, Module.End.mul_apply]⟩
  have hDsucc : ∀ j, (D j).map T = D (j + 1) := fun j => by
    simp only [D]
    rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]
  have hD0 : D 0 = ⊤ := by
    show LinearMap.range (T ^ 0) = ⊤
    rw [pow_zero]
    exact LinearMap.range_eq_top.2 fun x => ⟨x, rfl⟩
  have hDN : D (p ^ a) = ⊥ := by simp [D, hTN]
  have hK : ∀ g : G, LinearMap.ker T ≤ (LinearMap.ker T).comap ((coindRes H M).ρ g) :=
    ker_le_comap T hT

  have : Finite (Rep.res (H : Subgroup G).subtype M) := inferInstanceAs (Finite M)
  have : Finite (coindRes H M) := finite_coind H (Rep.res (H : Subgroup G).subtype M)
  have : IsDiscreteRep (coindRes H M) := isDiscreteRep_coind_res H M
  set c := Nat.card (LinearMap.ker T) with hc
  have hcM : c = Nat.card M := Nat.card_congr (kerShiftEquiv (H := H) (M := M) hgen).toEquiv.symm
  have hstep : ∀ j, Nat.card (D j) =
      Nat.card ↥(D j ⊓ LinearMap.ker T) * Nat.card (D (j + 1)) := fun j => by
    rw [card_rangeStep T (D j), hDsucc]
  have hle : ∀ j, Nat.card ↥(D j ⊓ LinearMap.ker T) ≤ c := fun j =>
    Nat.card_le_card_of_injective _
      (Submodule.inclusion_injective (inf_le_right : D j ⊓ LinearMap.ker T ≤ LinearMap.ker T))
  have hcpos : 0 < c := Nat.card_pos
  have hup : ∀ m j, j + m = p ^ a → Nat.card (D j) ≤ c ^ m := by
    intro m
    induction m with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj
      subst hj
      rw [hDN]
      simp
    | succ m ih =>
      intro j hj
      rw [hstep j, pow_succ']
      exact Nat.mul_le_mul (hle j) (ih (j + 1) (by omega))
  have hlow : c ^ (p ^ a) ≤ Nat.card (D 0) := by
    rw [hD0, Nat.card_congr (Submodule.topEquiv).toEquiv, hcM, ← hcard]
    exact card_pow_le_card_coindRes
  have hexact : ∀ j ≤ p ^ a, Nat.card (D j) = c ^ (p ^ a - j) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact le_antisymm (hup _ 0 (by simp)) (by simpa using hlow)
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      rw [hstep j] at h1
      have h2 : c ^ (p ^ a - j) = c * c ^ (p ^ a - (j + 1)) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h2] at h1
      exact (eq_and_eq_of_mul_eq_mul_of_le (hle j) (hup _ (j + 1) (by omega)) h1 hcpos
        (pow_pos hcpos _)).2
  have hfull : ∀ j < p ^ a, D j ⊓ LinearMap.ker T = LinearMap.ker T := by
    intro j hj
    have h1 := hexact j hj.le
    rw [hstep j, hexact (j + 1) hj] at h1
    have h3 : c ^ (p ^ a - j) = c * c ^ (p ^ a - (j + 1)) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h3] at h1
    have hcard' : Nat.card ↥(D j ⊓ LinearMap.ker T) = c :=
      Nat.eq_of_mul_eq_mul_right (pow_pos hcpos _) h1
    apply Submodule.toAddSubgroup_injective
    refine AddSubgroup.eq_of_le_of_card_ge
      ((Submodule.toAddSubgroup_le _ _).2 (inf_le_right : D j ⊓ LinearMap.ker T ≤ LinearMap.ker T)) ?_
    change Nat.card (LinearMap.ker T) ≤ Nat.card ↥(D j ⊓ LinearMap.ker T)
    rw [hcard']

  have hpa : 0 < p ^ a := pow_pos hp.out.pos a
  have hlast : D (p ^ a - 1) = LinearMap.ker T := by
    refine le_antisymm ?_ ((hfull _ (by omega)).symm.le.trans inf_le_left)
    intro x hx
    have hx' : T x ∈ D (p ^ a - 1 + 1) := hDsucc (p ^ a - 1) ▸ Submodule.mem_map_of_mem hx
    rw [show p ^ a - 1 + 1 = p ^ a by omega, hDN] at hx'
    exact LinearMap.mem_ker.2 ((Submodule.mem_bot k).1 hx')

  have hP : P (Nat.card (coindRes H M)) := by
    have hpow : ∀ n, P (Nat.card M ^ n) := fun n => by
      induction n with
      | zero => exact hPdvd 1 _ (one_dvd _) hM
      | succ n ih =>
        rw [pow_succ]
        exact hPmul _ _ ih hM
    exact hPdvd _ _ (card_coind_dvd H (Rep.res (H : Subgroup G).subtype M)) (hpow _)
  have hchain : ∀ j ≤ p ^ a - 1, χ (Rep.subrepresentation _ (D 0) (hD 0)) =
      χ (Rep.subrepresentation _ (LinearMap.ker T) hK) ^ j *
        χ (Rep.subrepresentation _ (D j) (hD j)) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp
    | succ j ih =>
      intro hj
      rw [ih (by omega), hχ.rangeStep hPdvd T hT (D j) (hD j) hP,
        apply_subrepresentation_congr χ (hfull j (by omega)) _ hK,
        apply_subrepresentation_congr χ (hDsucc j) _ (hD (j + 1)), pow_succ, mul_assoc]
  have : IsDiscreteRep (Rep.subrepresentation (coindRes H M) ⊤ (fun _ => le_top)) :=
    isDiscreteRep_subrepresentation (coindRes H M) ⊤ (fun _ => le_top)
  have htop : χ (coindRes H M) =
      χ (Rep.subrepresentation (coindRes H M) ⊤ (fun _ => le_top)) :=
    hχ.iso hP (subrepresentationTopIso (coindRes H M) (fun _ => le_top)).symm
  calc χ (coindRes H M)
      = χ (Rep.subrepresentation (coindRes H M) ⊤ (fun _ => le_top)) := htop
    _ = χ (Rep.subrepresentation _ (D 0) (hD 0)) :=
        apply_subrepresentation_congr χ hD0.symm _ _
    _ = χ (Rep.subrepresentation _ (LinearMap.ker T) hK) ^ (p ^ a) := by
        rw [hchain (p ^ a - 1) le_rfl, apply_subrepresentation_congr χ hlast _ hK, ← pow_succ,
          show p ^ a - 1 + 1 = p ^ a by omega]
    _ = χ M ^ (p ^ a) := by
        rw [hχ.iso hM (kerShiftIso (H := H) (M := M) hs hgen)]

end IsMultiplicativeOn

variable [IsTopologicalGroup G]

end GroundTheory.ProfCoh
