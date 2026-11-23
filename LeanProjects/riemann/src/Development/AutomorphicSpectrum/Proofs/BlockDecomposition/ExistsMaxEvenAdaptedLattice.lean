import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin.Adapted

section Lemmas

variable {R : Type} [CommRing R] {c : R →+* R} {𝔬 : Subring R}
  {V : Type} [AddCommGroup V] [Module R V] {h : V → V → R}

theorem herm_zero_right (H : IsHerm c h) (x : V) : h x 0 = 0 := by
  have := H.smul_right 0 x 0
  simpa using this

theorem herm_zero_left (H : IsHerm c h) (x : V) : h 0 x = 0 := by
  rw [H.symm x 0, herm_zero_right H, map_zero]

theorem herm_add_left (H : IsHerm c h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [H.symm z (x + y), H.add_right, map_add, ← H.symm z x, ← H.symm z y]

theorem herm_smul_left (H : IsHerm c h) (a : R) (x y : V) : h (a • x) y = c a * h x y := by
  rw [H.symm y (a • x), H.smul_right, map_mul, ← H.symm y x]

def hl (H : IsHerm c h) (w : V) : V →ₗ[R] R where
  toFun := h w
  map_add' := H.add_right w
  map_smul' a y := by simpa using H.smul_right a w y

@[simp] theorem hl_apply (H : IsHerm c h) (w z : V) : hl H w z = h w z := rfl

theorem smul_mem_of {L : Submodule 𝔬 V} {a : R} (ha : a ∈ 𝔬) {v : V} (hv : v ∈ L) : a • v ∈ L :=
  L.smul_mem ⟨a, ha⟩ hv

theorem common_denom (den : ∀ a : R, ∃ s ∈ 𝔬, IsUnit s ∧ s * a ∈ 𝔬) {ι : Type} (S : Finset ι) (a : ι → R) :
    ∃ s ∈ 𝔬, IsUnit s ∧ ∀ i ∈ S, s * a i ∈ 𝔬 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, 𝔬.one_mem, isUnit_one, by simp⟩
  | insert i S _ ih =>
    obtain ⟨s, hs, hu, hS⟩ := ih
    obtain ⟨t, ht, hv, hi⟩ := den (a i)
    refine ⟨s * t, 𝔬.mul_mem hs ht, hu.mul hv, fun j hj => ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · rw [mul_assoc]; exact 𝔬.mul_mem hs hi
    · rw [mul_right_comm]; exact 𝔬.mul_mem (hS j hj) ht

theorem evenInt_span (H : IsHerm c h) (inv : ∀ a, c (c a) = a) (cm : ∀ a ∈ 𝔬, c a ∈ 𝔬) (G : Set V)
    (h1 : ∀ g ∈ G, ∀ g' ∈ G, h g g' ∈ 𝔬) (h2 : ∀ g ∈ G, ∃ a ∈ 𝔬, h g g = a + c a) :
    IsEvenInt c 𝔬 h (Submodule.span 𝔬 G) := by
  have s1 : ∀ g ∈ G, ∀ z ∈ Submodule.span 𝔬 G, h g z ∈ 𝔬 := by
    intro g hg z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact h1 g hg x hx
    | zero => rw [herm_zero_right H]; exact 𝔬.zero_mem
    | add x y _ _ hx hy => rw [H.add_right]; exact 𝔬.add_mem hx hy
    | smul a x _ hx =>
      rw [Subring.smul_def, H.smul_right]
      exact 𝔬.mul_mem a.2 hx
  have s2 : ∀ z ∈ Submodule.span 𝔬 G, ∀ z' ∈ Submodule.span 𝔬 G, h z z' ∈ 𝔬 := by
    intro z hz z' hz'
    induction hz using Submodule.span_induction with
    | mem x hx => exact s1 x hx z' hz'
    | zero => rw [herm_zero_left H]; exact 𝔬.zero_mem
    | add x y _ _ hx hy => rw [herm_add_left H]; exact 𝔬.add_mem hx hy
    | smul a x _ hx =>
      rw [Subring.smul_def, herm_smul_left H]
      exact 𝔬.mul_mem (cm _ a.2) hx
  refine ⟨s2, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem x hx => exact h2 x hx
  | zero => exact ⟨0, 𝔬.zero_mem, by simp [herm_zero_right H]⟩
  | add x y hx' hy' hx hy =>
    obtain ⟨a, ha, ea⟩ := hx
    obtain ⟨b, hb, eb⟩ := hy
    refine ⟨a + b + h x y, 𝔬.add_mem (𝔬.add_mem ha hb) (s2 x hx' y hy'), ?_⟩
    rw [H.add_right, herm_add_left H, herm_add_left H, ea, eb, H.symm x y, map_add, map_add]
    ring
  | smul a x _ hx =>
    obtain ⟨b, hb, eb⟩ := hx
    refine ⟨c a * a * b, 𝔬.mul_mem (𝔬.mul_mem (cm _ a.2) a.2) hb, ?_⟩
    rw [Subring.smul_def, H.smul_right, herm_smul_left H, eb, map_mul, map_mul, inv]
    ring

theorem exists_maxEven (Hr : IsHermRing c 𝔬) (H : IsHerm c h) (Hp : IsPerfect h) (L₀ : Submodule 𝔬 V)
    (hL : IsLat 𝔬 L₀) (hE : IsEvenInt c 𝔬 h L₀) : ∃ L, L₀ ≤ L ∧ IsMaxEven c 𝔬 h L := by
  haveI := Hr.noeth
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL.1
  have hgL : ∀ i, g i ∈ L₀ := fun i => hg ▸ Submodule.subset_span ⟨i, rfl⟩
  let D : Submodule 𝔬 V :=
    { carrier := {z | ∀ i, h (g i) z ∈ 𝔬}
      add_mem' := fun {a b} ha hb i => by
        rw [H.add_right]; exact 𝔬.add_mem (ha i) (hb i)
      zero_mem' := fun i => by rw [herm_zero_right H]; exact 𝔬.zero_mem
      smul_mem' := fun a z hz i => by
        rw [Subring.smul_def, H.smul_right]; exact 𝔬.mul_mem a.2 (hz i) }
  let f : D →ₗ[𝔬] (Fin m → 𝔬) :=
    { toFun := fun z i => ⟨h (g i) z, z.2 i⟩
      map_add' := fun a b => by
        funext i; apply Subtype.ext; exact H.add_right _ _ _
      map_smul' := fun a z => by
        funext i; apply Subtype.ext
        change h (g i) ((a : R) • (z : V)) = (a : R) * h (g i) z
        exact H.smul_right _ _ _ }
  have finj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun z hz => ?_
    have h0 : ∀ i, h (g i) z = 0 := fun i => congrArg Subtype.val (congrFun hz i)
    have h1 : ∀ w ∈ L₀, h w z = 0 := by
      intro w hw
      rw [← hg] at hw
      induction hw using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h0 i
      | zero => exact herm_zero_left H _
      | add x y _ _ hx hy => rw [herm_add_left H, hx, hy, add_zero]
      | smul a x _ hx => rw [Subring.smul_def, herm_smul_left H, hx, mul_zero]
    have h2 : ∀ w ∈ Submodule.span R (L₀ : Set V), h w z = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact h1 x hx
      | zero => exact herm_zero_left H _
      | add x y _ _ hx hy => rw [herm_add_left H, hx, hy, add_zero]
      | smul a x _ hx => rw [herm_smul_left H, hx, mul_zero]
    apply Subtype.ext
    refine Hp.nondeg _ fun w => ?_
    rw [H.symm w, h2 w (by rw [hL.2]; trivial), map_zero]
  haveI : IsNoetherian 𝔬 D := isNoetherian_of_injective f finj
  have hD : ∀ L' : Submodule 𝔬 V, IsEvenInt c 𝔬 h L' → L₀ ≤ L' → L' ≤ D :=
    fun L' hE' hle z hz i => hE'.1 _ (hle (hgL i)) _ hz
  let S : Set (Submodule 𝔬 D) := {N | IsEvenInt c 𝔬 h (N.map D.subtype) ∧ L₀ ≤ N.map D.subtype}
  have hcm : ∀ L' : Submodule 𝔬 V, L' ≤ D → (L'.comap D.subtype).map D.subtype = L' := fun L' hl => by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.2 hl
  have hS : (L₀.comap D.subtype) ∈ S := by
    have := hcm L₀ (hD L₀ hE le_rfl)
    simp only [S, Set.mem_setOf_eq, this]
    exact ⟨hE, le_rfl⟩
  obtain ⟨N, hN, hmin⟩ := (wellFounded_gt (α := Submodule 𝔬 D)).has_min S ⟨_, hS⟩
  refine ⟨N.map D.subtype, hN.2, ⟨?_, ?_⟩, hN.1, fun L' hE' hle => ?_⟩
  · exact (IsNoetherian.noetherian N).map _
  · refine top_le_iff.1 ?_
    rw [← hL.2]
    exact Submodule.span_mono hN.2
  · have hDL : L' ≤ D := hD L' hE' (hN.2.trans hle)
    have hmem : L'.comap D.subtype ∈ S := by
      simp only [S, Set.mem_setOf_eq, hcm L' hDL]
      exact ⟨hE', hN.2.trans hle⟩
    have hNle : N ≤ L'.comap D.subtype := by
      rw [← Submodule.map_le_iff_le_comap]; exact hle
    have : ¬ N < L'.comap D.subtype := hmin _ hmem
    have heq : N = L'.comap D.subtype := by
      by_contra hne
      exact this (lt_of_le_of_ne hNle hne)
    rw [heq, hcm L' hDL]

theorem isAdapted_of {r : ℕ} {x y : Fin r → V} {L : Submodule 𝔬 V} (hE : IsEvenInt c 𝔬 h L)
    (hx : ∀ i, x i ∈ L) (hy : ∀ i, y i ∈ L) : IsAdapted 𝔬 h x y L := by
  intro z
  constructor
  · intro hz
    have ha : ∀ i, h (x i) z ∈ 𝔬 := fun i => hE.1 _ (hx i) _ hz
    have hb : ∀ i, h (y i) z ∈ 𝔬 := fun i => hE.1 _ (hy i) _ hz
    refine ⟨ha, hb, L.sub_mem (L.sub_mem hz ?_) ?_⟩
    · exact L.sum_mem fun i _ => smul_mem_of (hb i) (hx i)
    · exact L.sum_mem fun i _ => smul_mem_of (ha i) (hy i)
  · rintro ⟨ha, hb, hz⟩
    have e : z = (z - ∑ i, h (y i) z • x i - ∑ i, h (x i) z • y i) + ∑ i, h (y i) z • x i
        + ∑ i, h (x i) z • y i := by abel
    rw [e]
    refine L.add_mem (L.add_mem hz ?_) ?_
    · exact L.sum_mem fun i _ => smul_mem_of (hb i) (hx i)
    · exact L.sum_mem fun i _ => smul_mem_of (ha i) (hy i)

end Lemmas

theorem exists_maxEven_adapted : ∀ {R : Type} [CommRing R] (c : R →+* R) (𝔬 : Subring R), IsHermRing c 𝔬 →
    ∀ {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V] (h : V → V → R), IsHerm c h → IsPerfect h →
    ∀ {r : ℕ} (x y : Fin r → V), IsFrame h x y → ∃ L : Submodule 𝔬 V, IsMaxEven c 𝔬 h L ∧ IsAdapted 𝔬 h x y L := by
  intro R _ c 𝔬 Hr V _ _ _ h H Hp r x y F
  obtain ⟨m, e, he⟩ := Module.Finite.exists_fin (R := R) (M := V)
  have hyx : ∀ j i, h (y j) (x i) = if i = j then 1 else 0 := by
    intro j i
    rw [H.symm (x i) (y j), F.xy]
    split_ifs <;> simp
  let u : Fin m → V := fun k => e k - ∑ i, h (y i) (e k) • x i - ∑ i, h (x i) (e k) • y i
  have hux : ∀ j k, h (x j) (u k) = 0 := by
    intro j k
    have : hl H (x j) (u k) = 0 := by
      simp only [u, map_sub, map_sum, map_smul, hl_apply, smul_eq_mul, F.xx, F.xy]
      simp
    exact this
  have huy : ∀ j k, h (y j) (u k) = 0 := by
    intro j k
    have : hl H (y j) (u k) = 0 := by
      simp only [u, map_sub, map_sum, map_smul, hl_apply, smul_eq_mul, F.yy, hyx]
      simp
    exact this
  obtain ⟨t, ht⟩ := Hr.two.exists_right_inv
  have hct : c t = t := by
    have h2 : (2 : R) * c t = 1 := by
      have := congrArg c ht
      rw [map_mul, map_ofNat c 2, map_one] at this
      exact this
    calc c t = (2 * t) * c t := by rw [ht, one_mul]
      _ = t * (2 * c t) := by ring
      _ = t := by rw [h2, mul_one]
  obtain ⟨s, hs𝔬, hsu, hs⟩ := common_denom Hr.denom
    (Finset.univ : Finset (Fin m × Fin m)) (fun p => h (u p.1) (u p.2) * t)
  have two𝔬 : (2 : R) ∈ 𝔬 := by
    have : (2 : R) = 1 + 1 := by norm_num
    rw [this]; exact 𝔬.add_mem 𝔬.one_mem 𝔬.one_mem
  let w : Fin m → V := fun k => s • u k
  have hxw : ∀ i k, h (x i) (w k) = 0 := fun i k => by
    simp only [w, H.smul_right, hux, mul_zero]
  have hyw : ∀ i k, h (y i) (w k) = 0 := fun i k => by
    simp only [w, H.smul_right, huy, mul_zero]
  have hwx : ∀ k i, h (w k) (x i) = 0 := fun k i => by
    rw [H.symm (x i) (w k), hxw, map_zero]
  have hwy : ∀ k i, h (w k) (y i) = 0 := fun k i => by
    rw [H.symm (y i) (w k), hyw, map_zero]
  have hA : ∀ i j, c s * (s * (h (u i) (u j) * t)) ∈ 𝔬 := fun i j =>
    𝔬.mul_mem (Hr.conj_mem _ hs𝔬) (hs (i, j) (Finset.mem_univ _))
  have hww : ∀ i j, h (w i) (w j) = 2 * (c s * (s * (h (u i) (u j) * t))) := fun i j => by
    simp only [w, H.smul_right, herm_smul_left H]
    linear_combination (-(c s * s * h (u i) (u j))) * ht
  have ite𝔬 : ∀ i j : Fin r, (if i = j then (1 : R) else 0) ∈ 𝔬 := fun i j => by
    split_ifs
    · exact 𝔬.one_mem
    · exact 𝔬.zero_mem
  let G : Set V := Set.range x ∪ Set.range y ∪ Set.range w
  have g1 : ∀ g ∈ G, ∀ g' ∈ G, h g g' ∈ 𝔬 := by
    rintro g ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) g' ((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩)
    · rw [F.xx]; exact 𝔬.zero_mem
    · rw [F.xy]; exact ite𝔬 _ _
    · rw [hxw]; exact 𝔬.zero_mem
    · rw [hyx]; exact ite𝔬 _ _
    · rw [F.yy]; exact 𝔬.zero_mem
    · rw [hyw]; exact 𝔬.zero_mem
    · rw [hwx]; exact 𝔬.zero_mem
    · rw [hwy]; exact 𝔬.zero_mem
    · rw [hww]; exact 𝔬.mul_mem two𝔬 (hA i j)
  have g2 : ∀ g ∈ G, ∃ a ∈ 𝔬, h g g = a + c a := by
    rintro g ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact ⟨0, 𝔬.zero_mem, by simp [F.xx]⟩
    · exact ⟨0, 𝔬.zero_mem, by simp [F.yy]⟩
    · refine ⟨_, hA i i, ?_⟩
      have hc : c (c s * (s * (h (u i) (u i) * t))) = c s * (s * (h (u i) (u i) * t)) := by
        simp only [map_mul, Hr.invol, hct, ← H.symm]
        ring
      rw [hc, hww]
      ring
  have hE := evenInt_span (𝔬 := 𝔬) H Hr.invol Hr.conj_mem G g1 g2
  have hfin : G.Finite := ((Set.finite_range x).union (Set.finite_range y)).union (Set.finite_range w)
  have hLat : IsLat 𝔬 (Submodule.span 𝔬 G) := by
    refine ⟨Submodule.fg_span hfin, ?_⟩
    set T := Submodule.span R ((Submodule.span 𝔬 G : Submodule 𝔬 V) : Set V) with hT
    have hG : ∀ g ∈ G, g ∈ T := fun g hg => Submodule.subset_span (Submodule.subset_span hg)
    have hu : ∀ k, u k ∈ T := by
      intro k
      obtain ⟨v, rfl⟩ := hsu
      have : u k = (↑v⁻¹ : R) • w k := by
        simp only [w, smul_smul, Units.inv_mul, one_smul]
      rw [this]
      exact T.smul_mem _ (hG _ (Or.inr ⟨k, rfl⟩))
    refine top_le_iff.1 ?_
    rw [← he, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have ek : e k = u k + ∑ i, h (y i) (e k) • x i + ∑ i, h (x i) (e k) • y i := by
      simp only [u]; abel
    change e k ∈ T
    rw [ek]
    refine T.add_mem (T.add_mem (hu k) ?_) ?_
    · exact T.sum_mem fun i _ => T.smul_mem _ (hG _ (Or.inl (Or.inl ⟨i, rfl⟩)))
    · exact T.sum_mem fun i _ => T.smul_mem _ (hG _ (Or.inl (Or.inr ⟨i, rfl⟩)))
  obtain ⟨L, hle, hmax⟩ := exists_maxEven Hr H Hp _ hLat hE
  refine ⟨L, hmax, isAdapted_of hmax.2.1 (fun i => hle ?_) (fun i => hle ?_)⟩
  · exact Submodule.subset_span (Or.inl (Or.inl ⟨i, rfl⟩))
  · exact Submodule.subset_span (Or.inl (Or.inr ⟨i, rfl⟩))

end GlobalTheory.CompanionTheory.KFin.Adapted

end
