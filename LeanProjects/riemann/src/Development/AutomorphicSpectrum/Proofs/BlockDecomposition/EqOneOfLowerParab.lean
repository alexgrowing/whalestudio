import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.JPred
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlockDiagonalLeviEmbedding

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.CompanionTheory.LbcKillN

section Abstract

variable {G : Type} [Group G]

def Fil (Jm Jt Jp V : Subgroup G) : Prop :=
  V ≤ Jp ∧ ∃ W : Subgroup G, Jm ≤ W ∧ Jt ≤ W ∧ V ≤ W ∧
    ∀ w ∈ W, ∃ a ∈ Jm, ∃ b ∈ Jt, ∃ v ∈ V, w = a * b * v

variable {J Jm Jt Jp Nl T Nu : Subgroup G} {ψ : MulAut G}

theorem fil_step (hmJ : Jm ≤ J) (htJ : Jt ≤ J) (hpJ : Jp ≤ J) (hmN : Jm ≤ Nl) (htT : Jt ≤ T) (hpN : Jp ≤ Nu)
    (hfact : ∀ x ∈ J, ∃ a ∈ Jm, ∃ b ∈ Jt, ∃ c ∈ Jp, x = a * b * c)
    (huniq : ∀ a ∈ Nl, ∀ a' ∈ Nl, ∀ b ∈ T, ∀ b' ∈ T, ∀ c ∈ Nu, ∀ c' ∈ Nu,
      a * b * c = a' * b' * c' → a = a' ∧ b = b' ∧ c = c')
    (hψp : ∀ x ∈ Jp, ψ x ∈ Jp) (hψm : ∀ x ∈ Jm, ψ⁻¹ x ∈ Jm) (hψt : ∀ x ∈ Jt, ψ⁻¹ x ∈ Jt)
    (hψNl : ∀ x ∈ Jm, ψ x ∈ Nl) (hψT : ∀ x ∈ Jt, ψ x ∈ T)
    {V : Subgroup G} (hV : Fil Jm Jt Jp V) : Fil Jm Jt Jp (V.map ψ.toMonoidHom) := by
  obtain ⟨hVp, W, hmW, htW, hVW, hW⟩ := hV
  refine ⟨?_, J ⊓ W.map ψ.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hψp v (hVp hv)
  · intro x hx
    exact ⟨hmJ hx, ψ⁻¹ x, hmW (hψm x hx), by simp⟩
  · intro x hx
    exact ⟨htJ hx, ψ⁻¹ x, htW (hψt x hx), by simp⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨hpJ (hψp v (hVp hv)), v, hVW hv, rfl⟩
  · rintro w ⟨hwJ, y, hy, rfl⟩
    obtain ⟨a₀, ha₀, b₀, hb₀, c₀, hc₀, e₀⟩ := hfact _ hwJ
    obtain ⟨a, ha, b, hb, v, hv, rfl⟩ := hW y hy
    have e : a₀ * b₀ * c₀ = ψ a * ψ b * ψ v := by
      rw [← e₀]
      simp [map_mul]
    obtain ⟨h1, h2, h3⟩ := huniq _ (hmN ha₀) _ (hψNl a ha) _ (htT hb₀) _ (hψT b hb) _ (hpN hc₀) _
      (hpN (hψp v (hVp hv))) e
    exact ⟨a₀, ha₀, b₀, hb₀, c₀, h3 ▸ ⟨v, hv, rfl⟩, e₀⟩

theorem fil_top (hmJ : Jm ≤ J) (htJ : Jt ≤ J) (hpJ : Jp ≤ J)
    (hfact : ∀ x ∈ J, ∃ a ∈ Jm, ∃ b ∈ Jt, ∃ c ∈ Jp, x = a * b * c) : Fil Jm Jt Jp Jp :=
  ⟨le_rfl, J, hmJ, htJ, hpJ, hfact⟩

theorem contr (hmN : Jm ≤ Nl) (htT : Jt ≤ T) (hpN : Jp ≤ Nu)
    (huniq : ∀ a ∈ Nl, ∀ a' ∈ Nl, ∀ b ∈ T, ∀ b' ∈ T, ∀ c ∈ Nu, ∀ c' ∈ Nu,
      a * b * c = a' * b' * c' → a = a' ∧ b = b' ∧ c = c')
    {c : G} {f : G → G} (hf : ∀ w ∈ Jp, f w ∈ Jp ∧ ∃ τ ∈ Jt, ∃ a ∈ Jm, c * w = f w * τ * a)
    {V : Subgroup G} (hV : Fil Jm Jt Jp V) {w w' : G} (hw : w ∈ Jp) (hw' : w' ∈ Jp) (h : w⁻¹ * w' ∈ V) :
    (f w)⁻¹ * f w' ∈ V := by
  obtain ⟨hp, τ, hτ, a, ha, e⟩ := hf w hw
  obtain ⟨hp', τ', hτ', a', ha', e'⟩ := hf w' hw'
  obtain ⟨hVp, W, hmW, htW, hVW, hW⟩ := hV
  have key : (f w)⁻¹ * f w' = τ * a * (w⁻¹ * w') * a'⁻¹ * τ'⁻¹ := by
    have h1 : f w = c * w * (τ * a)⁻¹ := by rw [e]; group
    have h2 : f w' = c * w' * (τ' * a')⁻¹ := by rw [e']; group
    rw [h1, h2]
    group
  have hmem : (f w)⁻¹ * f w' ∈ W := by
    rw [key]
    exact mul_mem (mul_mem (mul_mem (mul_mem (htW hτ) (hmW ha)) (hVW h)) (inv_mem (hmW ha')))
      (inv_mem (htW hτ'))
  obtain ⟨a₁, ha₁, b₁, hb₁, v₁, hv₁, e₁⟩ := hW _ hmem
  have := huniq a₁ (hmN ha₁) 1 (one_mem _) b₁ (htT hb₁) 1 (one_mem _) v₁ (hpN (hVp hv₁)) _
    (hpN (mul_mem (inv_mem hp) hp')) (by simpa using e₁.symm)
  rw [← this.2.2]
  exact hv₁

theorem exists_fixed [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (hmJ : Jm ≤ J) (htJ : Jt ≤ J) (hpJ : Jp ≤ J) (hmN : Jm ≤ Nl) (htT : Jt ≤ T) (hpN : Jp ≤ Nu)
    (hfact : ∀ x ∈ J, ∃ a ∈ Jm, ∃ b ∈ Jt, ∃ c ∈ Jp, x = a * b * c)
    (huniq : ∀ a ∈ Nl, ∀ a' ∈ Nl, ∀ b ∈ T, ∀ b' ∈ T, ∀ c ∈ Nu, ∀ c' ∈ Nu,
      a * b * c = a' * b' * c' → a = a' ∧ b = b' ∧ c = c')
    (hψp : ∀ x ∈ Jp, ψ x ∈ Jp) (hψm : ∀ x ∈ Jm, ψ⁻¹ x ∈ Jm) (hψt : ∀ x ∈ Jt, ψ⁻¹ x ∈ Jt)
    (hψNl : ∀ x ∈ Jm, ψ x ∈ Nl) (hψT : ∀ x ∈ Jt, ψ x ∈ T)
    (hψc : Continuous ψ) (hcpt : IsCompact (Jp : Set G))
    (hsh : ∀ g : G, (∀ n : ℕ, ∃ x ∈ Jp, (ψ ^ n) x = g) → g = 1) {c : G} (hc : c ∈ J) :
    ∃ p ∈ Jp, ∃ τ ∈ Jt, ∃ a ∈ Jm, c * ψ p = p * τ * a := by
  have hf0 : ∀ w, ∃ p, w ∈ Jp → (p ∈ Jp ∧ ∃ τ ∈ Jt, ∃ a ∈ Jm, c * w = p * τ * a) := by
    intro w
    by_cases hw : w ∈ Jp
    · obtain ⟨a, ha, b, hb, d, hd, e⟩ := hfact ((c * w)⁻¹) (inv_mem (mul_mem hc (hpJ hw)))
      refine ⟨d⁻¹, fun _ => ⟨inv_mem hd, b⁻¹, inv_mem hb, a⁻¹, inv_mem ha, ?_⟩⟩
      rw [← inv_inv (c * w), e]
      group
    · exact ⟨1, fun h => absurd h hw⟩
  choose f hf using hf0
  let V : ℕ → Subgroup G := fun n => Jp.map (ψ ^ n).toMonoidHom
  have memV : ∀ n g, g ∈ V n ↔ ∃ x ∈ Jp, (ψ ^ n) x = g := fun n g => by
    simp [V, Subgroup.mem_map]
  have hV0 : V 0 = Jp := by
    ext g
    rw [memV]
    simp
  have hVs : ∀ n, V (n + 1) = (V n).map ψ.toMonoidHom := by
    intro n
    ext g
    simp only [memV, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(ψ ^ n) x, (memV _ _).2 ⟨x, hx, rfl⟩, by rw [pow_succ']; rfl⟩
    · rintro ⟨_, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (memV _ _).1 hy
      exact ⟨x, hx, by rw [pow_succ']; rfl⟩
  have hFil : ∀ n, Fil Jm Jt Jp (V n) := by
    intro n
    induction n with
    | zero => rw [hV0]; exact fil_top hmJ htJ hpJ hfact
    | succ n ih =>
      rw [hVs]
      exact fil_step hmJ htJ hpJ hmN htT hpN hfact huniq hψp hψm hψt hψNl hψT ih
  have hanti : ∀ n, V (n + 1) ≤ V n := by
    intro n g hg
    obtain ⟨x, hx, rfl⟩ := (memV _ _).1 hg
    exact (memV _ _).2 ⟨ψ x, hψp x hx, by rw [pow_succ]; rfl⟩
  let s : ℕ → G := fun n => (fun w => ψ (f w))^[n] 1
  have s0 : s 0 = 1 := rfl
  have ss : ∀ n, s (n + 1) = ψ (f (s n)) := fun n => Function.iterate_succ_apply' _ _ _
  have hsJ : ∀ n, s n ∈ Jp := by
    intro n
    induction n with
    | zero => exact one_mem _
    | succ n ih => rw [ss]; exact hψp _ (hf _ ih).1
  have hsV : ∀ n, (s n)⁻¹ * s (n + 1) ∈ V n := by
    intro n
    induction n with
    | zero => rw [hV0, s0, inv_one, one_mul]; exact hsJ 1
    | succ n ih =>
      rw [hVs]
      refine ⟨_, contr hmN htT hpN huniq hf (hFil n) (hsJ n) (hsJ (n + 1)) ih, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
      rw [← ss n, ← ss (n + 1)]
  have hcont : ∀ n : ℕ, Continuous (ψ ^ n : MulAut G) := by
    intro n
    induction n with
    | zero => simpa using continuous_id
    | succ n ih =>
      have : ((ψ ^ (n + 1) : MulAut G) : G → G) = ψ ∘ (ψ ^ n : MulAut G) := by
        rw [pow_succ']; rfl
      rw [this]
      exact hψc.comp ih
  let C : ℕ → Set G := fun n => (fun x => s n * (ψ ^ n) x) '' (Jp : Set G)
  have memC : ∀ n g, g ∈ C n ↔ (s n)⁻¹ * g ∈ V n := by
    intro n g
    rw [memV]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp⟩
    · rintro ⟨x, hx, e⟩
      exact ⟨x, hx, by simp [e]⟩
  have hCc : ∀ n, IsCompact (C n) := fun n => hcpt.image (continuous_const.mul (hcont n))
  have hne : (⋂ n, C n).Nonempty := by
    refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C ?_ ?_ (hCc 0)
      (fun n => (hCc n).isClosed)
    · intro n g hg
      rw [memC] at hg ⊢
      have := mul_mem (hsV n) (hanti n hg)
      simpa [mul_assoc] using this
    · intro n
      exact ⟨_, 1, one_mem _, rfl⟩
  obtain ⟨w, hw⟩ := hne
  have hw1 : ∀ n, (s n)⁻¹ * w ∈ V n := fun n => (memC n w).1 (Set.mem_iInter.1 hw n)
  have hwJ : w ∈ Jp := by
    have := hw1 0
    rwa [hV0, s0, inv_one, one_mul] at this
  have h1 : ∀ n, w⁻¹ * s n ∈ V n := fun n => by
    simpa using inv_mem (hw1 n)
  have h2 : ∀ n, (ψ (f w))⁻¹ * s (n + 1) ∈ V (n + 1) := by
    intro n
    rw [hVs, ss]
    exact ⟨_, contr hmN htT hpN huniq hf (hFil n) hwJ (hsJ n) (h1 n), by simp [map_mul]⟩
  have h3 : ∀ n, w⁻¹ * ψ (f w) ∈ V (n + 1) := by
    intro n
    have := mul_mem (h1 (n + 1)) (inv_mem (h2 n))
    simpa [mul_assoc] using this
  have hfix : w⁻¹ * ψ (f w) = 1 := hsh _ fun n => (memV _ _).1 (hanti n (h3 n))
  have hw' : ψ (f w) = w := (inv_mul_eq_one.1 hfix).symm
  obtain ⟨hp, τ, hτ, a, ha, e⟩ := hf w hwJ
  exact ⟨f w, hp, τ, hτ, a, ha, by rw [hw']; exact e⟩

end Abstract

section Matrices

variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem uniq {e : (Σ a, m a) ≃ n} :
    ∀ a ∈ unipRadLower R e, ∀ a' ∈ unipRadLower R e, ∀ b ∈ (leviEmb R e).range,
      ∀ b' ∈ (leviEmb R e).range, ∀ c ∈ unipRad R e, ∀ c' ∈ unipRad R e,
      a * b * c = a' * b' * c' → a = a' ∧ b = b' ∧ c = c' :=
  _root_.UpperTheory.Reformulated.B.Qf33.uniq

end Matrices

section Twist

variable {G : Type} [Group G]

theorem tnorm_succ (θ : MulAut G) (i : ℕ) (x : G) :
    PositivityTheory.Lbc.tnorm θ (i + 1) x = x * θ (PositivityTheory.Lbc.tnorm θ i x) := by
  simp only [PositivityTheory.Lbc.tnorm, List.ofFn_succ, List.prod_cons, map_list_prod, List.map_ofFn]
  congr 2
  refine congrArg List.ofFn (funext fun i => ?_)
  simp [pow_succ']

theorem conj_mul_pow (θ : MulAut G) (t : G) (i : ℕ) :
    (MulAut.conj t * θ) ^ i = MulAut.conj (PositivityTheory.Lbc.tnorm θ i t) * θ ^ i := by
  induction i with
  | zero => simp [PositivityTheory.Lbc.tnorm]
  | succ i ih =>
    rw [pow_succ', ih, tnorm_succ, pow_succ']
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, mul_assoc]

theorem mem_of_map {H : Subgroup G} {θ : MulAut G} (h : H.map θ.toMonoidHom = H) {x : G} (hx : x ∈ H) :
    θ x ∈ H := by
  rw [← h]
  exact ⟨x, hx, rfl⟩

theorem inv_mem_of_map {H : Subgroup G} {θ : MulAut G} (h : H.map θ.toMonoidHom = H) {x : G} (hx : x ∈ H) :
    θ⁻¹ x ∈ H := by
  rw [← h] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

theorem twist_inv_apply (θ : MulAut G) (t x : G) :
    (θ * MulAut.conj t)⁻¹ x = t⁻¹ * θ⁻¹ x * t := by
  rw [mul_inv_rev, MulAut.mul_apply, ← map_inv, MulAut.conj_apply, inv_inv]

theorem twist_pow (θ : MulAut G) (t : G) {l : ℕ} (hl : θ ^ l = 1) (j : ℕ) (x : G) :
    ((θ * MulAut.conj t) ^ (l * j)) x =
      θ (PositivityTheory.Lbc.tnorm θ l t ^ j * θ⁻¹ x * (PositivityTheory.Lbc.tnorm θ l t ^ j)⁻¹) := by
  have e : θ * MulAut.conj t = θ * (MulAut.conj t * θ) * θ⁻¹ := by group
  rw [e, conj_pow, pow_mul, conj_mul_pow, hl, mul_one, ← map_pow MulAut.conj]
  simp only [MulAut.mul_apply, MulAut.conj_apply]

end Twist

section Main

open PositivityTheory.Lbc

theorem isClosed_Nup {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) : IsClosed (Nup k N : Set (GL (Fin N) k)) := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  haveI : T2Space k := inferInstance
  have hc : ∀ i j, Continuous fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  set e := stdBlocks (ones N) (sum_ones N) with he
  have hs : (Nup k N : Set (GL (Fin N) k)) =
      (⋂ (a) (b) (i : Bl (ones N) a) (j : Bl (ones N) b) (_ : b < a),
        {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0}) ∩
      ⋂ (a) (i : Bl (ones N) a) (j : Bl (ones N) a),
        {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
          (1 : Matrix (Bl (ones N) a) (Bl (ones N) a) k) i j} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
    exact mem_unipRad.trans (and_congr mem_parab_iff Iff.rfl)
  rw [hs]
  refine IsClosed.inter ?_ ?_
  · exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun i =>
      isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (hc _ _) continuous_const
  · exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (hc _ _) continuous_const

theorem killN : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    ∀ (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (l : ℕ) (t : GL (Fin N) k),
    PositivityTheory.Lbc.admitted k N J θ l → PositivityTheory.Lbc.GoodT k N J θ l t →
    ∀ b ∈ J, ∃ j ∈ J, ∃ a ∈ J ⊓ PositivityTheory.Lbc.Nlo k N, ∃ τ ∈ J ⊓ PositivityTheory.Lbc.Tor k N,
      j⁻¹ * (t * b) * θ j = t * a * τ := by
  intro k _ _ _ _ N J θ l t hA hG b hb
  obtain ⟨hJo, hJc, hI, hθc, hl, hθl, hθJ, hθNu, hθNl, hθT⟩ := hA
  obtain ⟨htT, hdom, hstr⟩ := hG
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  haveI : T2Space k := inferInstance
  obtain ⟨s, hs, hd1, hd2, hd3⟩ := hdom 0 hl
  have hs' : torEmb k N s = t := by simpa using hs
  have d1 : ∀ n ∈ J ⊓ Nup k N, t * n * t⁻¹ ∈ J ⊓ Nup k N := by
    intro n hn
    have := hd1 n hn
    rwa [show leviEmb k (stdBlocks (ones N) (sum_ones N)) s = t from hs'] at this
  have d2 : ∀ n ∈ J ⊓ Nlo k N, t⁻¹ * n * t ∈ J ⊓ Nlo k N := by
    intro n hn
    have := hd2 n hn
    rwa [show leviEmb k (stdBlocks (ones N) (sum_ones N)) s = t from hs'] at this
  have d3 : ∀ x ∈ J ⊓ Tor k N, t⁻¹ * x * t ∈ J ⊓ Tor k N := by
    rintro _ ⟨hxJ, y, rfl⟩
    have h := (hd3 y hxJ).2
    have h' : torEmb k N (s⁻¹ * y * s) ∈ J := h
    rw [map_mul, map_mul, map_inv, hs'] at h'
    exact Subgroup.mem_inf.2 ⟨h', mul_mem (mul_mem (inv_mem htT) (show torEmb k N y ∈ Tor k N from ⟨y, rfl⟩)) htT⟩
  have nlo : ∀ σ ∈ Tor k N, ∀ n ∈ Nlo k N, σ * n * σ⁻¹ ∈ Nlo k N := by
    rintro _ ⟨y, rfl⟩ n hn
    exact (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer_lower k _ y) n).1 hn
  have hmJ : J ⊓ Nlo k N ≤ J := inf_le_left
  have htJ : J ⊓ Tor k N ≤ J := inf_le_left
  have hpJ : J ⊓ Nup k N ≤ J := inf_le_left
  have hfact : ∀ x ∈ J, ∃ a ∈ J ⊓ Nlo k N, ∃ β ∈ J ⊓ Tor k N, ∃ c ∈ J ⊓ Nup k N, x = a * β * c :=
    fun x hx => hI x hx
  have huq : ∀ a ∈ Nlo k N, ∀ a' ∈ Nlo k N, ∀ β ∈ Tor k N, ∀ β' ∈ Tor k N, ∀ c ∈ Nup k N,
      ∀ c' ∈ Nup k N, a * β * c = a' * β' * c' → a = a' ∧ β = β' ∧ c = c' := uniq
  set ψ : MulAut (GL (Fin N) k) := θ * MulAut.conj t with hψ
  have ψap : ∀ x, ψ x = θ (t * x * t⁻¹) := fun x => rfl
  have ψinv : ∀ x, ψ⁻¹ x = t⁻¹ * θ⁻¹ x * t := fun x => twist_inv_apply θ t x
  have hψp : ∀ x ∈ J ⊓ Nup k N, ψ x ∈ J ⊓ Nup k N := by
    intro x hx
    have := d1 x hx
    exact ⟨mem_of_map hθJ this.1, mem_of_map hθNu this.2⟩
  have hψm : ∀ x ∈ J ⊓ Nlo k N, ψ⁻¹ x ∈ J ⊓ Nlo k N := by
    intro x hx
    rw [ψinv]
    exact d2 _ ⟨inv_mem_of_map hθJ hx.1, inv_mem_of_map hθNl hx.2⟩
  have hψt : ∀ x ∈ J ⊓ Tor k N, ψ⁻¹ x ∈ J ⊓ Tor k N := by
    intro x hx
    rw [ψinv]
    exact d3 _ ⟨inv_mem_of_map hθJ hx.1, inv_mem_of_map hθT hx.2⟩
  have hψNl : ∀ x ∈ J ⊓ Nlo k N, ψ x ∈ Nlo k N := fun x hx =>
    mem_of_map hθNl (nlo t htT x hx.2)
  have hψT : ∀ x ∈ J ⊓ Tor k N, ψ x ∈ Tor k N := fun x hx =>
    mem_of_map hθT (mul_mem (mul_mem htT hx.2) (inv_mem htT))
  have hψc : Continuous ψ := by
    have : (ψ : GL (Fin N) k → GL (Fin N) k) = fun x => θ (t * x * t⁻¹) := rfl
    rw [this]
    exact hθc.comp ((continuous_const.mul continuous_id).mul continuous_const)
  have hcpt : IsCompact ((J ⊓ Nup k N : Subgroup (GL (Fin N) k)) : Set (GL (Fin N) k)) := by
    rw [Subgroup.coe_inf]
    exact hJc.inter_right (isClosed_Nup N)
  have hsh : ∀ g : GL (Fin N) k, (∀ n : ℕ, ∃ x ∈ J ⊓ Nup k N, (ψ ^ n) x = g) → g = 1 := by
    intro g hg
    by_contra hne
    obtain ⟨s₂, hs₂, ⟨-, hsd⟩, -⟩ := hstr
    have hU : IsOpen (θ ⁻¹' ({g}ᶜ : Set (GL (Fin N) k))) := isOpen_compl_singleton.preimage hθc
    have h1U : (1 : GL (Fin N) k) ∈ θ ⁻¹' ({g}ᶜ : Set (GL (Fin N) k)) := by
      simpa using fun h => hne h.symm
    obtain ⟨j, hj⟩ := hsd _ hU h1U
    obtain ⟨x, hx, e⟩ := hg (l * j)
    rw [hψ, twist_pow θ t hθl] at e
    have hn : θ⁻¹ x ∈ KN k N J (ones N) (sum_ones N) :=
      ⟨inv_mem_of_map hθJ hx.1, inv_mem_of_map hθNu hx.2⟩
    have := hj _ hn
    rw [show leviEmb k (stdBlocks (ones N) (sum_ones N)) s₂ = tnorm θ l t from hs₂] at this
    exact this e

  obtain ⟨am, ham, β, hβ, γ, hγ, eb⟩ := hfact b⁻¹ (inv_mem hb)
  have eb' : b = γ⁻¹ * β⁻¹ * am⁻¹ := by
    rw [← inv_inv b, eb]
    group
  set m₀ : GL (Fin N) k := θ⁻¹ am⁻¹ with hm₀
  have hm₀J : m₀ ∈ J ⊓ Nlo k N := ⟨inv_mem_of_map hθJ (inv_mem ham.1), inv_mem_of_map hθNl (inv_mem ham.2)⟩
  have hθm : θ m₀ = am⁻¹ := by simp [hm₀]
  set c : GL (Fin N) k := (t⁻¹ * m₀ * t) * γ⁻¹ * β⁻¹ with hcdef
  have hcJ : c ∈ J := mul_mem (mul_mem (d2 _ hm₀J).1 (inv_mem hγ.1)) (inv_mem hβ.1)
  obtain ⟨p, hp, τ, hτ, a, ha, ec⟩ := exists_fixed hmJ htJ hpJ inf_le_right inf_le_right inf_le_right
    hfact huq hψp hψm hψt hψNl hψT hψc hcpt hsh hcJ
  have hu := d1 p hp
  refine ⟨m₀⁻¹ * (t * p * t⁻¹), mul_mem (inv_mem hm₀J.1) hu.1, τ * a * τ⁻¹,
    Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (Subgroup.mem_inf.1 hτ).1 (Subgroup.mem_inf.1 ha).1) (inv_mem (Subgroup.mem_inf.1 hτ).1),
      nlo τ (Subgroup.mem_inf.1 hτ).2 a (Subgroup.mem_inf.1 ha).2⟩, τ, hτ, ?_⟩
  have e1 : θ (m₀⁻¹ * (t * p * t⁻¹)) = am * ψ p := by
    rw [map_mul, map_inv, hθm, inv_inv, ψap]
  rw [e1]
  have e2 : (m₀⁻¹ * (t * p * t⁻¹))⁻¹ * (t * b) * (am * ψ p) = t * p⁻¹ * t⁻¹ * t * (c * ψ p) := by
    rw [eb', hcdef]
    group
  rw [e2, ec]
  group

end Main

end GlobalTheory.CompanionTheory.LbcKillN
