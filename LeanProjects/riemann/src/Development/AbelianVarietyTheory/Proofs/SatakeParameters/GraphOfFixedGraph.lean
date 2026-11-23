import Mathlib

noncomputable section

namespace GlobalTheory.HeckeIso

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

section Avg

def avgN (ρ : G →* Module.End ℂ V) (N : Subgroup G) [Fintype (G ⧸ N)] : Module.End ℂ V :=
  ((Fintype.card (G ⧸ N) : ℂ)⁻¹) • ∑ q : G ⧸ N, ρ q.out

theorem avgN_apply (ρ : G →* Module.End ℂ V) (N : Subgroup G) [Fintype (G ⧸ N)] (x : V) :
    avgN ρ N x = ((Fintype.card (G ⧸ N) : ℂ)⁻¹) • ∑ q : G ⧸ N, ρ q.out x := by
  simp only [avgN, LinearMap.smul_apply, LinearMap.sum_apply]

theorem out_apply (ρ : G →* Module.End ℂ V) (N : Subgroup G) {x : V} (hx : ∀ s ∈ N, ρ s x = x) (g : G) :
    ρ (g : G ⧸ N).out x = ρ g x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N g
  rw [hh, map_mul, Module.End.mul_apply, hx _ h.2]

theorem avgN_fixed (ρ : G →* Module.End ℂ V) (N : Subgroup G) [Fintype (G ⧸ N)] {x : V}
    (hx : ∀ s ∈ N, ρ s x = x) (k : G) : ρ k (avgN ρ N x) = avgN ρ N x := by
  have key : ∀ q : G ⧸ N, ρ k (ρ q.out x) = ρ ((k • q).out) x := by
    intro q
    have e0 : k • q = ((k * q.out : G) : G ⧸ N) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [e0, out_apply ρ N hx, map_mul, Module.End.mul_apply]
  simp only [avgN_apply, map_smul, map_sum, key]
  congr 1
  exact Equiv.sum_comp (MulAction.toPerm k) (fun q : G ⧸ N => ρ q.out x)

theorem avgN_of_fixed (ρ : G →* Module.End ℂ V) (N : Subgroup G) [Fintype (G ⧸ N)] {y : V}
    (hy : ∀ k, ρ k y = y) : avgN ρ N y = y := by
  have hc : (Fintype.card (G ⧸ N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [avgN_apply, hy, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem avgN_translate (ρ : G →* Module.End ℂ V) (N : Subgroup G) [Fintype (G ⧸ N)] [N.Normal] {x : V}
    (hx : ∀ s ∈ N, ρ s x = x) (k : G) : avgN ρ N (ρ k x) = avgN ρ N x := by
  have key : ∀ q : G ⧸ N, ρ q.out (ρ k x) = ρ ((q * (k : G ⧸ N)).out) x := by
    intro q
    have e0 : q * (k : G ⧸ N) = ((q.out * k : G) : G ⧸ N) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [e0, out_apply ρ N hx, map_mul, Module.End.mul_apply]
  simp only [avgN_apply, key]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight (k : G ⧸ N)) (fun q : G ⧸ N => ρ q.out x)

theorem avgN_indep (ρ : G →* Module.End ℂ V) (N N' : Subgroup G) [Fintype (G ⧸ N)] [Fintype (G ⧸ N')] [N'.Normal]
    {x : V} (hx : ∀ s ∈ N, ρ s x = x) (hx' : ∀ s ∈ N', ρ s x = x) : avgN ρ N x = avgN ρ N' x := by
  have hc : (Fintype.card (G ⧸ N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [← avgN_of_fixed ρ N' (avgN_fixed ρ N hx), avgN_apply ρ N, map_smul, map_sum]
  simp only [avgN_translate ρ N' hx', Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem exists_normal (ρ : G →* Module.End ℂ V) (x : V) (hfin : (Set.range fun k => ρ k x).Finite) :
    ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧ ∀ s ∈ N, ρ s x = x := by
  letI : MulAction G V := MulAction.compHom V ρ
  haveI : Finite (MulAction.orbit G x) := hfin.to_subtype
  haveI : Finite (G ⧸ MulAction.stabilizer G x) :=
    Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer G x)
  haveI : (MulAction.stabilizer G x).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact ⟨(MulAction.stabilizer G x).normalCore, inferInstance, inferInstance,
    fun s hs => (MulAction.stabilizer G x).normalCore_le hs⟩

theorem exists_avg_top (ρ : G →* Module.End ℂ V) (hfin : ∀ x, (Set.range fun k => ρ k x).Finite) :
    ∃ P : Module.End ℂ V, (∀ x k, ρ k (P x) = P x) ∧ (∀ x, (∀ k, ρ k x = x) → P x = x) ∧
      (∀ x k, P (ρ k x) = P x) ∧
      ∀ x y, ∃ (ι : Type) (_ : Fintype ι) (k : ι → G) (c : ℂ),
        P x = c • ∑ i, ρ (k i) x ∧ P y = c • ∑ i, ρ (k i) y := by
  choose N hN1 hN2 hN3 using fun x => exists_normal ρ x (hfin x)
  letI F1 : ∀ x, Fintype (G ⧸ N x) := fun x => Fintype.ofFinite _
  letI F2 : ∀ x y, Fintype (G ⧸ (N x ⊓ N y)) := fun x y => Fintype.ofFinite _
  have h2 : ∀ x y, avgN ρ (N x) x = avgN ρ (N x ⊓ N y) x ∧ avgN ρ (N y) y = avgN ρ (N x ⊓ N y) y :=
    fun x y => ⟨avgN_indep ρ _ _ (hN3 x) (fun s hs => hN3 x s hs.1),
      avgN_indep ρ _ _ (hN3 y) (fun s hs => hN3 y s hs.2)⟩
  obtain ⟨p, hp⟩ : ∃ p : V → V, ∀ x, p x = avgN ρ (N x) x := ⟨_, fun _ => rfl⟩
  let P : Module.End ℂ V :=
    { toFun := p
      map_add' := fun x y => by
        rw [hp, hp, hp, (h2 x y).1, (h2 x y).2, ← map_add]
        exact avgN_indep ρ _ _ (hN3 _) (fun s hs => by rw [map_add, hN3 x s hs.1, hN3 y s hs.2])
      map_smul' := fun c x => by
        rw [hp, hp, RingHom.id_apply, ← map_smul]
        exact avgN_indep ρ _ _ (hN3 _) (fun s hs => by rw [map_smul, hN3 x s hs]) }
  have hP : ∀ x, P x = avgN ρ (N x) x := hp
  refine ⟨P, fun x k => ?_, fun x hx => ?_, fun x k => ?_, fun x y => ?_⟩
  · rw [hP]; exact avgN_fixed ρ _ (hN3 x) k
  · rw [hP]; exact avgN_of_fixed ρ _ hx
  · rw [hP, hP, (h2 (ρ k x) x).1, (h2 (ρ k x) x).2]
    exact avgN_translate ρ (N (ρ k x) ⊓ N x) (fun s hs => hN3 x s hs.2) k
  · refine ⟨G ⧸ (N x ⊓ N y), F2 x y, fun q => q.out, (Fintype.card (G ⧸ (N x ⊓ N y)) : ℂ)⁻¹, ?_, ?_⟩
    · rw [hP, (h2 x y).1, avgN_apply]
    · rw [hP, (h2 x y).2, avgN_apply]

structure IsAvg (ρ : G →* Module.End ℂ V) (K : Subgroup G) (P : Module.End ℂ V) : Prop where
  fix : ∀ x, ∀ k ∈ K, ρ k (P x) = P x
  self : ∀ x, (∀ k ∈ K, ρ k x = x) → P x = x
  tr : ∀ x, ∀ k ∈ K, P (ρ k x) = P x
  pair : ∀ x y, ∃ (ι : Type) (_ : Fintype ι) (k : ι → G) (c : ℂ), (∀ i, k i ∈ K) ∧
    P x = c • ∑ i, ρ (k i) x ∧ P y = c • ∑ i, ρ (k i) y

theorem exists_avg (ρ : G →* Module.End ℂ V) (K : Subgroup G)
    (hfin : ∀ x, ((fun k => ρ k x) '' (K : Set G)).Finite) : ∃ P, IsAvg ρ K P := by
  obtain ⟨P, h1, h2, h3, h4⟩ := exists_avg_top (ρ.comp K.subtype) (fun x => (hfin x).subset (by
    rintro _ ⟨k, rfl⟩
    exact ⟨k, k.2, rfl⟩))
  refine ⟨P, fun x k hk => h1 x ⟨k, hk⟩, fun x hx => h2 x fun k => hx k k.2, fun x k hk => h3 x ⟨k, hk⟩,
    fun x y => ?_⟩
  obtain ⟨ι, i, k, c, e1, e2⟩ := h4 x y
  exact ⟨ι, i, fun j => k j, c, fun j => (k j).2, e1, e2⟩

variable {ρ : G →* Module.End ℂ V} {K : Subgroup G} {P : Module.End ℂ V}

theorem IsAvg.pair_mem (h : IsAvg ρ K P) (X : Submodule ℂ (V × V))
    (hX : ∀ k ∈ K, ∀ z ∈ X, (ρ k z.1, ρ k z.2) ∈ X) {z : V × V} (hz : z ∈ X) : (P z.1, P z.2) ∈ X := by
  obtain ⟨ι, _, k, c, hk, e1, e2⟩ := h.pair z.1 z.2
  have : (P z.1, P z.2) = c • ∑ i, (ρ (k i) z.1, ρ (k i) z.2) := by
    rw [e1, e2]
    ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  rw [this]
  exact X.smul_mem _ (X.sum_mem fun i _ => hX _ (hk i) z hz)

theorem IsAvg.mem (h : IsAvg ρ K P) (S : Submodule ℂ V) (hS : ∀ k ∈ K, ∀ x ∈ S, ρ k x ∈ S) {x : V}
    (hx : x ∈ S) : P x ∈ S := by
  obtain ⟨ι, _, k, c, hk, e1, -⟩ := h.pair x x
  rw [e1]
  exact S.smul_mem _ (S.sum_mem fun i _ => hS _ (hk i) x hx)

theorem IsAvg.comm (h : IsAvg ρ K P) (T : Module.End ℂ V) (hT : ∀ k ∈ K, ∀ x, T (ρ k x) = ρ k (T x)) (x : V) :
    P (T x) = T (P x) := by
  obtain ⟨ι, _, k, c, hk, e1, e2⟩ := h.pair x (T x)
  rw [e1, e2, map_smul, map_sum]
  simp only [hT _ (hk _)]

theorem IsAvg.avg_avg (h : IsAvg ρ K P) {K' : Subgroup G} {P' : Module.End ℂ V} (h' : IsAvg ρ K' P')
    (hle : K' ≤ K) (x : V) : P (P' x) = P x := by
  have h0 : P' (P x) = P x := h'.self _ fun k hk => h.fix x k (hle hk)
  obtain ⟨ι, _, k, c, hk, e1, e2⟩ := h'.pair x (P x)
  rw [e1, map_smul, map_sum]
  rw [h0] at e2
  simp only [h.tr _ _ (hle (hk _))]
  simp only [h.fix _ _ (hle (hk _))] at e2
  exact e2.symm

end Avg

structure Irr (ρ : G →* Module.End ℂ V) (S : Submodule ℂ V) : Prop where
  stab : ∀ g, ∀ x ∈ S, ρ g x ∈ S
  simple : ∀ T ≤ S, (∀ g, ∀ x ∈ T, ρ g x ∈ T) → T = ⊥ ∨ T = S

structure IsGraph (ρ : G →* Module.End ℂ V) (H : Subgroup G) (S₁ S₂ : Submodule ℂ V) (X : Submodule ℂ (V × V)) :
    Prop where
  ne : X ≠ ⊥
  mem : ∀ z ∈ X, z.1 ∈ S₁ ∧ z.2 ∈ S₂
  stab : ∀ x ∈ H, ∀ z ∈ X, (ρ x z.1, ρ x z.2) ∈ X
  inj₁ : ∀ u, ((0 : V), u) ∈ X → u = 0
  inj₂ : ∀ u, (u, (0 : V)) ∈ X → u = 0

variable {ρ : G →* Module.End ℂ V}

theorem IsGraph.swap {H : Subgroup G} {S₁ S₂ : Submodule ℂ V} {X : Submodule ℂ (V × V)} (h : IsGraph ρ H S₁ S₂ X) :
    IsGraph ρ H S₂ S₁ (X.comap (LinearEquiv.prodComm ℂ V V).toLinearMap) where
  ne := by
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.ne
    refine (Submodule.ne_bot_iff _).2 ⟨z.swap, hz, fun e => hz0 ?_⟩
    simpa using congrArg Prod.swap e
  mem := fun z hz => (h.mem _ hz).symm
  stab := fun x hx z hz => h.stab x hx _ hz
  inj₁ := fun u hu => h.inj₂ u hu
  inj₂ := fun u hu => h.inj₁ u hu

theorem rho_mul (g h : G) (x : V) : ρ (g * h) x = ρ g (ρ h x) := by rw [map_mul]; rfl

theorem kill {A B : Subgroup G} (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hd : ∀ g, ∃ x ∈ A, ∃ y ∈ B, g = x * y) {S : Submodule ℂ V} (hS : Irr ρ S) (d : Module.End ℂ V)
    (hdB : ∀ y ∈ B, ∀ s, d (ρ y s) = ρ y (d s)) (T : Submodule ℂ V) (hT : T ≤ S) (hT0 : T ≠ ⊥)
    (hTA : ∀ x ∈ A, ∀ t ∈ T, ρ x t ∈ T) (hdT : ∀ t ∈ T, d t = 0) : ∀ s ∈ S, d s = 0 := by
  let Y : Submodule ℂ V :=
    { carrier := {s | s ∈ S ∧ ∀ x ∈ A, d (ρ x s) = 0}
      zero_mem' := ⟨S.zero_mem, fun x _ => by simp⟩
      add_mem' := fun ha hb => ⟨S.add_mem ha.1 hb.1, fun x hx => by simp [ha.2 x hx, hb.2 x hx]⟩
      smul_mem' := fun c a ha => ⟨S.smul_mem c ha.1, fun x hx => by simp [ha.2 x hx]⟩ }
  have hTY : T ≤ Y := fun t ht => ⟨hT ht, fun x hx => hdT _ (hTA x hx t ht)⟩
  rcases hS.simple Y (fun s hs => hs.1) (fun g s hs => ⟨hS.stab g s hs.1, fun x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hd g
    rw [← rho_mul, ← mul_assoc, hc _ (A.mul_mem hx ha) b hb, rho_mul, hdB b hb, hs.2 _ (A.mul_mem hx ha),
      map_zero]⟩) with h | h
  · exact absurd (le_bot_iff.1 (h ▸ hTY)) hT0
  · intro s hs
    have : s ∈ Y := h ▸ hs
    simpa using this.2 1 A.one_mem

theorem graph_of_spherical {A B K : Subgroup G} (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hd : ∀ g, ∃ x ∈ A, ∃ y ∈ B, g = x * y) (hK : K ≤ A) {P : Module.End ℂ V} (hP : IsAvg ρ K P)
    {S₁ S₂ : Submodule ℂ V} (h₁ : Irr ρ S₁) (h₂ : Irr ρ S₂) {f₁ f₂ : V} (hf₁ : f₁ ∈ S₁) (hf₂ : f₂ ∈ S₂)
    (n₁ : f₁ ≠ 0) (n₂ : f₂ ≠ 0) (k₁ : ∀ k ∈ K, ρ k f₁ = f₁) (k₂ : ∀ k ∈ K, ρ k f₂ = f₂)
    (hχ : ∀ x ∈ A, ∃ c : ℂ, P (ρ x f₁) = c • f₁ ∧ P (ρ x f₂) = c • f₂) : ∃ X, IsGraph ρ A S₁ S₂ X := by
  let X : Submodule ℂ (V × V) := Submodule.span ℂ {z | ∃ x ∈ A, z = (ρ x f₁, ρ x f₂)}
  have hst : ∀ x ∈ A, ∀ z ∈ X, (ρ x z.1, ρ x z.2) ∈ X := by
    intro x hx z hz
    have : X ≤ X.comap ((ρ x).prodMap (ρ x)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨x * y, A.mul_mem hx hy, by simp [rho_mul]⟩
    exact this hz
  have hmem : ∀ z ∈ X, z.1 ∈ S₁ ∧ z.2 ∈ S₂ := by
    have : X ≤ S₁.prod S₂ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, -, rfl⟩
      exact ⟨h₁.stab y _ hf₁, h₂.stab y _ hf₂⟩
    exact fun z hz => this hz
  have hPX : ∀ z ∈ X, ∃ c : ℂ, P z.1 = c • f₁ ∧ P z.2 = c • f₂ := by
    have : X ≤ (Submodule.span ℂ {(f₁, f₂)}).comap (P.prodMap P) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨c, e1, e2⟩ := hχ y hy
      exact Submodule.mem_span_singleton.2 ⟨c, by simp [e1, e2]⟩
    intro z hz
    obtain ⟨c, e⟩ := Submodule.mem_span_singleton.1 (this hz)
    exact ⟨c, (congrArg Prod.fst e).symm, (congrArg Prod.snd e).symm⟩
  have hPB : ∀ y ∈ B, ∀ s, P (ρ y s) = ρ y (P s) := fun y hy s =>
    hP.comm (ρ y) (fun k hk x => by rw [← rho_mul, ← hc k (hK hk) y hy, rho_mul]) s
  refine ⟨X, ?_, hmem, hst, fun u hu => ?_, fun u hu => ?_⟩
  · refine (Submodule.ne_bot_iff _).2 ⟨(f₁, f₂), Submodule.subset_span ⟨1, A.one_mem, by simp⟩, fun e => n₁ ?_⟩
    exact congrArg Prod.fst e
  · by_contra hu0
    have := kill hc hd h₂ P hPB (X.comap (LinearMap.inr ℂ V V)) (fun t ht => (hmem _ ht).2)
      ((Submodule.ne_bot_iff _).2 ⟨u, hu, hu0⟩) (fun x hx t ht => by simpa using hst x hx _ ht)
      (fun t ht => by
        obtain ⟨c, e1, e2⟩ := hPX _ ht
        have hc0 : c = 0 := by simpa [n₁] using e1.symm
        simpa [hc0] using e2) f₂ hf₂
    exact n₂ ((hP.self _ k₂).symm.trans this)
  · by_contra hu0
    have := kill hc hd h₁ P hPB (X.comap (LinearMap.inl ℂ V V)) (fun t ht => (hmem _ ht).1)
      ((Submodule.ne_bot_iff _).2 ⟨u, hu, hu0⟩) (fun x hx t ht => by simpa using hst x hx _ ht)
      (fun t ht => by
        obtain ⟨c, e1, e2⟩ := hPX _ ht
        have hc0 : c = 0 := by simpa [n₂] using e2.symm
        simpa [hc0] using e1) f₁ hf₁
    exact n₁ ((hP.self _ k₁).symm.trans this)

section Places

variable {ι : Type} (ρ : G →* Module.End ℂ V) (Gv Gc : ι → Subgroup G) (J : Subgroup G)

def locAlg (A B : Subgroup G) : Subalgebra ℂ (Module.End ℂ V) where
  carrier := {d | (∀ y ∈ B, ∀ s, d (ρ y s) = ρ y (d s)) ∧
    ∀ X : Submodule ℂ (V × V), (∀ x ∈ A, ∀ z ∈ X, (ρ x z.1, ρ x z.2) ∈ X) → ∀ z ∈ X, (d z.1, d z.2) ∈ X}
  mul_mem' := fun {a b} ha hb => ⟨fun y hy s => by simp [ha.1 y hy, hb.1 y hy],
    fun X hX z hz => ha.2 X hX _ (hb.2 X hX z hz)⟩
  add_mem' := fun {a b} ha hb => ⟨fun y hy s => by simp [ha.1 y hy, hb.1 y hy],
    fun X hX z hz => X.add_mem (ha.2 X hX z hz) (hb.2 X hX z hz)⟩
  algebraMap_mem' := fun c => ⟨fun y hy s => by simp, fun X hX z hz => X.smul_mem c hz⟩

def fixAlg : Subalgebra ℂ (Module.End ℂ V) where
  carrier := {d | ∀ f, (∀ k ∈ J, ρ k f = f) → ∀ k ∈ J, ρ k (d f) = d f}
  mul_mem' := fun {a b} ha hb f hf => ha _ (hb f hf)
  add_mem' := fun {a b} ha hb f hf k hk => by simp [ha f hf k hk, hb f hf k hk]
  algebraMap_mem' := fun c f hf k hk => by simp [hf k hk]

def fixIn (S : Submodule ℂ V) : Submodule ℂ V where
  carrier := {x | x ∈ S ∧ ∀ k ∈ J, ρ k x = x}
  add_mem' := fun {x y} hx hy => ⟨S.add_mem hx.1 hy.1, fun k hk => by rw [map_add, hx.2 k hk, hy.2 k hk]⟩
  zero_mem' := ⟨S.zero_mem, fun k _ => map_zero _⟩
  smul_mem' := fun c x hx => ⟨S.smul_mem c hx.1, fun k hk => by rw [map_smul, hx.2 k hk]⟩

structure PlaceSys : Prop where
  comm : ∀ v, ∀ x ∈ Gv v, ∀ y ∈ Gc v, x * y = y * x
  le : ∀ v w, v ≠ w → Gv w ≤ Gc v
  dec : ∀ v g, ∃ x ∈ Gv v, ∃ y ∈ Gc v, g = x * y
  decJ : ∀ v, ∀ k ∈ J, ∃ x ∈ Gv v ⊓ J, ∃ y ∈ Gc v ⊓ J, k = x * y
  ind : ∀ p : G → Prop, (∀ k ∈ J, p k) → (∀ v, ∀ x ∈ Gv v, ∀ y ∈ Gc v, p y → p (x * y)) → ∀ g, p g

variable {ρ Gv Gc J}

theorem locAlg_mem {A B : Subgroup G} {d : Module.End ℂ V} (hd : d ∈ locAlg ρ A B) {S : Submodule ℂ V}
    (hS : ∀ g, ∀ x ∈ S, ρ g x ∈ S) {x : V} (hx : x ∈ S) : d x ∈ S :=
  (hd.2 (S.prod S) (fun g _ z hz => ⟨hS g _ hz.1, hS g _ hz.2⟩) (x, x) ⟨hx, hx⟩).1

theorem locAlg_comm {A B A' B' : Subgroup G} (hle : A' ≤ B) {d d' : Module.End ℂ V} (hd : d ∈ locAlg ρ A B)
    (hd' : d' ∈ locAlg ρ A' B') (x : V) : d (d' x) = d' (d x) := by
  have := hd'.2 (LinearMap.graph d) (fun y hy z hz => by
    rw [LinearMap.mem_graph_iff] at hz ⊢
    simp only [hz, hd.1 y (hle hy)]) (x, d x) (by simp)
  rw [LinearMap.mem_graph_iff] at this
  exact this.symm

theorem rho_mem_locAlg {A B : Subgroup G} (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {x : G} (hx : x ∈ A) :
    ρ x ∈ locAlg ρ A B :=
  ⟨fun y hy s => by rw [← rho_mul, hc x hx y hy, rho_mul], fun X hX z hz => hX x hx z hz⟩

theorem avg_mem_locAlg {A B K : Subgroup G} (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hK : K ≤ A)
    {P : Module.End ℂ V} (hP : IsAvg ρ K P) : P ∈ locAlg ρ A B :=
  ⟨fun y hy s => hP.comm (ρ y) (fun k hk x => by rw [← rho_mul, ← hc k (hK hk) y hy, rho_mul]) s,
    fun X hX z hz => hP.pair_mem X (fun k hk => hX k (hK hk)) hz⟩

theorem avg_fixed {A B : Subgroup G} (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hJ : ∀ k ∈ J, ∃ x ∈ A ⊓ J, ∃ y ∈ B ⊓ J, k = x * y) {P : Module.End ℂ V} (hP : IsAvg ρ (A ⊓ J) P) {s : V}
    (hs : ∀ y ∈ B ⊓ J, ρ y s = s) : ∀ k ∈ J, ρ k (P s) = P s := by
  intro k hk
  obtain ⟨x, hx, y, hy, rfl⟩ := hJ k hk
  rw [rho_mul, ← (avg_mem_locAlg hc inf_le_left hP).1 y hy.1, hs y hy, hP.fix _ x hx]

theorem ann_transfer {A B : Subgroup G} (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hd : ∀ g, ∃ x ∈ A, ∃ y ∈ B, g = x * y)
    (hJ : ∀ k ∈ J, ∃ x ∈ A ⊓ J, ∃ y ∈ B ⊓ J, k = x * y) {P Q : Module.End ℂ V} (hP : IsAvg ρ (A ⊓ J) P)
    (hQ : IsAvg ρ (B ⊓ J) Q) {S₁ S₂ : Submodule ℂ V} (h₁ : Irr ρ S₁) (h₂ : Irr ρ S₂) (n₁ : fixIn ρ J S₁ ≠ ⊥)
    {X : Submodule ℂ (V × V)} (hX : IsGraph ρ A S₁ S₂ X) {c : Module.End ℂ V} (hcm : c ∈ locAlg ρ A B)
    (h0 : ∀ x ∈ fixIn ρ J S₁, c x = 0) : ∀ x ∈ fixIn ρ J S₂, c x = 0 := by
  have hd' : c * P ∈ locAlg ρ A B := mul_mem hcm (avg_mem_locAlg hc inf_le_left hP)
  have hQ' : Q ∈ locAlg ρ B A := avg_mem_locAlg (fun x hx y hy => (hc y hy x hx).symm) inf_le_left hQ
  have k1 : ∀ s ∈ S₁, (c * P) s = 0 := by
    refine kill hc hd h₁ _ hd'.1 (S₁.map Q) ?_ ?_ ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact locAlg_mem hQ' h₁.stab hs
    · obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot n₁
      exact (Submodule.ne_bot_iff _).2 ⟨f, ⟨f, hf.1, hQ.self f fun k hk => hf.2 k hk.2⟩, hf0⟩
    · rintro x hx _ ⟨s, hs, rfl⟩
      exact ⟨ρ x s, h₁.stab x s hs, hQ'.1 x hx s⟩
    · rintro _ ⟨s, hs, rfl⟩
      exact h0 _ ⟨locAlg_mem (avg_mem_locAlg hc inf_le_left hP) h₁.stab (locAlg_mem hQ' h₁.stab hs),
        avg_fixed hc hJ hP (hQ.fix s)⟩
  have k2 : ∀ s ∈ S₂, (c * P) s = 0 := by
    refine kill hc hd h₂ _ hd'.1 (X.map (LinearMap.snd ℂ V V)) ?_ ?_ ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact (hX.mem z hz).2
    · obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX.ne
      refine (Submodule.ne_bot_iff _).2 ⟨z.2, ⟨z, hz, rfl⟩, fun e => hz0 ?_⟩
      have : z.1 = 0 := hX.inj₂ _ (by rw [← e]; exact hz)
      exact Prod.ext this e
    · rintro x hx _ ⟨z, hz, rfl⟩
      exact ⟨_, hX.stab x hx z hz, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      have := hd'.2 X hX.stab z hz
      rw [k1 _ (hX.mem z hz).1] at this
      exact hX.inj₁ _ this
  intro x hx
  have := k2 x hx.1
  rwa [Module.End.mul_apply, hP.self x fun k hk => hx.2 k hk.2] at this

theorem stable_all (H : PlaceSys Gv Gc J) (horb : ∀ x, ((fun k => ρ k x) '' (J : Set G)).Finite)
    {P : Module.End ℂ V} (hP : IsAvg ρ J P) (X : Submodule ℂ (V × V))
    (hXf : ∀ z ∈ X, (∀ k ∈ J, ρ k z.1 = z.1) ∧ ∀ k ∈ J, ρ k z.2 = z.2)
    (hX : ∀ v, ∀ c ∈ locAlg ρ (Gv v) (Gc v) ⊓ fixAlg ρ J, ∀ z ∈ X, (c z.1, c z.2) ∈ X) (g : G) :
    ∀ z ∈ X, (P (ρ g z.1), P (ρ g z.2)) ∈ X := by
  refine H.ind (fun g => ∀ z ∈ X, (P (ρ g z.1), P (ρ g z.2)) ∈ X) (fun k hk z hz => ?_)
    (fun v x hx y hy ih z hz => ?_) g
  · rw [(hXf z hz).1 k hk, (hXf z hz).2 k hk, hP.self _ (hXf z hz).1, hP.self _ (hXf z hz).2]
    exact hz
  · obtain ⟨Pv, hPv⟩ := exists_avg ρ (Gv v ⊓ J) fun x => (horb x).subset (Set.image_mono fun k hk => hk.2)
    obtain ⟨Q, hQ⟩ := exists_avg ρ (Gc v ⊓ J) fun x => (horb x).subset (Set.image_mono fun k hk => hk.2)
    have hc' : ∀ x ∈ Gc v, ∀ y ∈ Gv v, x * y = y * x := fun x hx y hy => (H.comm v y hy x hx).symm
    have hJ' : ∀ k ∈ J, ∃ x ∈ Gc v ⊓ J, ∃ y ∈ Gv v ⊓ J, k = x * y := fun k hk => by
      obtain ⟨a, ha, b, hb, e⟩ := H.decJ v k hk
      exact ⟨b, hb, a, ha, e.trans (H.comm v a ha.1 b hb.1)⟩
    have hfx : ∀ f, (∀ k ∈ J, ρ k f = f) → ∀ k ∈ J, ρ k (Pv (ρ x f)) = Pv (ρ x f) := fun f hf =>
      avg_fixed (H.comm v) (H.decJ v) hPv fun b hb => by
        rw [← rho_mul, ← H.comm v x hx b hb.1, rho_mul, hf b hb.2]
    have hmem : Pv * ρ x ∈ locAlg ρ (Gv v) (Gc v) ⊓ fixAlg ρ J :=
      ⟨mul_mem (avg_mem_locAlg (H.comm v) inf_le_left hPv) (rho_mem_locAlg (H.comm v) hx), hfx⟩
    have key : ∀ f, (∀ k ∈ J, ρ k f = f) → P (ρ (x * y) f) = (Pv * ρ x) (P (ρ y f)) := by
      intro f hf
      have e1 : ∀ k ∈ J, ρ k (Q (ρ y f)) = Q (ρ y f) := avg_fixed hc' hJ' hQ fun a ha => by
        rw [← rho_mul, H.comm v a ha.1 y hy, rho_mul, hf a ha.2]
      have e2 : P (ρ y f) = Q (ρ y f) := by rw [← hP.avg_avg hQ inf_le_right, hP.self _ e1]
      rw [rho_mul, ← hP.avg_avg hQ inf_le_right, (avg_mem_locAlg hc' inf_le_left hQ).1 x hx, e2,
        Module.End.mul_apply, ← hP.avg_avg hPv inf_le_right, hP.self _ (hfx _ e1)]
    rw [key _ (hXf z hz).1, key _ (hXf z hz).2]
    exact hX v _ hmem _ (ih z hz)

theorem fixIn_simple (H : PlaceSys Gv Gc J) (horb : ∀ x, ((fun k => ρ k x) '' (J : Set G)).Finite)
    {S : Submodule ℂ V} (hS : Irr ρ S) (Y : Submodule ℂ V) (hY : Y ≤ fixIn ρ J S)
    (hst : ∀ v, ∀ c ∈ locAlg ρ (Gv v) (Gc v) ⊓ fixAlg ρ J, ∀ x ∈ Y, c x ∈ Y) : Y = ⊥ ∨ Y = fixIn ρ J S := by
  obtain ⟨P, hP⟩ := exists_avg ρ J horb
  have hall := stable_all H horb hP (Y.prod Y) (fun z hz => ⟨(hY hz.1).2, (hY hz.2).2⟩)
    (fun v c hc z hz => ⟨hst v c hc _ hz.1, hst v c hc _ hz.2⟩)
  let Z : Submodule ℂ V :=
    { carrier := {s | s ∈ S ∧ ∀ g, P (ρ g s) ∈ Y}
      zero_mem' := ⟨S.zero_mem, fun x => by simp⟩
      add_mem' := fun ha hb => ⟨S.add_mem ha.1 hb.1, fun x => by
        rw [map_add, map_add]; exact Y.add_mem (ha.2 x) (hb.2 x)⟩
      smul_mem' := fun c a ha => ⟨S.smul_mem c ha.1, fun x => by
        rw [map_smul, map_smul]; exact Y.smul_mem c (ha.2 x)⟩ }
  have hYZ : Y ≤ Z := fun y hy => ⟨(hY hy).1, fun g => (hall g (y, y) ⟨hy, hy⟩).1⟩
  rcases hS.simple Z (fun s hs => hs.1) (fun g s hs => ⟨hS.stab g s hs.1, fun x => by
    rw [← rho_mul]; exact hs.2 _⟩) with h | h
  · exact Or.inl (le_bot_iff.1 (h ▸ hYZ))
  · refine Or.inr (le_antisymm hY fun f hf => ?_)
    have : f ∈ Z := h ▸ hf.1
    have h1 := this.2 1
    rwa [map_one, Module.End.one_apply, hP.self f hf.2] at h1

theorem eq_zero_of_avg {P : Module.End ℂ V} (hP : IsAvg ρ J P) {S : Submodule ℂ V} (hS : Irr ρ S)
    (n : fixIn ρ J S ≠ ⊥) {u : V} (hu : u ∈ S) (h0 : ∀ g, P (ρ g u) = 0) : u = 0 := by
  let Z : Submodule ℂ V :=
    { carrier := {s | s ∈ S ∧ ∀ g, P (ρ g s) = 0}
      zero_mem' := ⟨S.zero_mem, fun x => by simp⟩
      add_mem' := fun ha hb => ⟨S.add_mem ha.1 hb.1, fun x => by simp [ha.2 x, hb.2 x]⟩
      smul_mem' := fun c a ha => ⟨S.smul_mem c ha.1, fun x => by simp [ha.2 x]⟩ }
  rcases hS.simple Z (fun s hs => hs.1) (fun g s hs => ⟨hS.stab g s hs.1, fun x => by
    rw [← rho_mul]; exact hs.2 _⟩) with h | h
  · have : u ∈ Z := ⟨hu, h0⟩
    rwa [h, Submodule.mem_bot] at this
  · obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot n
    have : f ∈ Z := h ▸ hf.1
    have h1 := this.2 1
    rw [map_one, Module.End.one_apply, hP.self f hf.2] at h1
    exact absurd h1 hf0

theorem graph_of_fixed_graph (H : PlaceSys Gv Gc J) (horb : ∀ x, ((fun k => ρ k x) '' (J : Set G)).Finite)
    {S₁ S₂ : Submodule ℂ V} (h₁ : Irr ρ S₁) (h₂ : Irr ρ S₂) (n₁ : fixIn ρ J S₁ ≠ ⊥) (n₂ : fixIn ρ J S₂ ≠ ⊥)
    (X : Submodule ℂ (V × V)) (hX0 : X ≠ ⊥) (hXm : ∀ z ∈ X, z.1 ∈ fixIn ρ J S₁ ∧ z.2 ∈ fixIn ρ J S₂)
    (hX : ∀ v, ∀ c ∈ locAlg ρ (Gv v) (Gc v) ⊓ fixAlg ρ J, ∀ z ∈ X, (c z.1, c z.2) ∈ X)
    (i₁ : ∀ u, ((0 : V), u) ∈ X → u = 0) (i₂ : ∀ u, (u, (0 : V)) ∈ X → u = 0) :
    ∃ W, IsGraph ρ ⊤ S₁ S₂ W := by
  obtain ⟨P, hP⟩ := exists_avg ρ J horb
  have hall := stable_all H horb hP X (fun z hz => ⟨(hXm z hz).1.2, (hXm z hz).2.2⟩) hX
  let W : Submodule ℂ (V × V) :=
    { carrier := {z | (z.1 ∈ S₁ ∧ z.2 ∈ S₂) ∧ ∀ g, (P (ρ g z.1), P (ρ g z.2)) ∈ X}
      zero_mem' := ⟨⟨S₁.zero_mem, S₂.zero_mem⟩, fun x => by
        simp only [Prod.fst_zero, Prod.snd_zero, map_zero]; exact X.zero_mem⟩
      add_mem' := fun ha hb => ⟨⟨S₁.add_mem ha.1.1 hb.1.1, S₂.add_mem ha.1.2 hb.1.2⟩, fun x => by
        simpa using X.add_mem (ha.2 x) (hb.2 x)⟩
      smul_mem' := fun c a ha => ⟨⟨S₁.smul_mem c ha.1.1, S₂.smul_mem c ha.1.2⟩, fun x => by
        simpa using X.smul_mem c (ha.2 x)⟩ }
  have hXW : X ≤ W := fun z hz => ⟨⟨(hXm z hz).1.1, (hXm z hz).2.1⟩, fun g => hall g z hz⟩
  refine ⟨W, fun h => hX0 (le_bot_iff.1 (h ▸ hXW)), fun z hz => hz.1, fun g _ z hz =>
    ⟨⟨h₁.stab g _ hz.1.1, h₂.stab g _ hz.1.2⟩, fun x => by
      simp only [← rho_mul]; exact hz.2 _⟩, fun u hu => ?_, fun u hu => ?_⟩
  · exact eq_zero_of_avg hP h₂ n₂ hu.1.2 fun g => i₁ _ (by simpa using hu.2 g)
  · exact eq_zero_of_avg hP h₁ n₁ hu.1.1 fun g => i₂ _ (by simpa using hu.2 g)

end Places

section Sub

def res (ρ : G →* Module.End ℂ V) (C : Submodule ℂ V) (hC : ∀ h, ∀ x ∈ C, ρ h x ∈ C) : G →* Module.End ℂ C where
  toFun g := (ρ g).restrict (hC g)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp

variable {C : Submodule ℂ V} {hC : ∀ h, ∀ x ∈ C, ρ h x ∈ C}

theorem Irr.res {S : Submodule ℂ V} (h : Irr ρ S) (hS : S ≤ C) : Irr (res ρ C hC) (S.comap C.subtype) where
  stab := fun g x hx => h.stab g _ hx
  simple := fun T hT hst => by
    rcases h.simple (T.map C.subtype) (by rintro _ ⟨x, hx, rfl⟩; exact hT hx)
      (by rintro g _ ⟨x, hx, rfl⟩; exact ⟨_, hst g x hx, rfl⟩) with e | e
    · left
      rw [← Submodule.comap_map_eq_of_injective C.injective_subtype T, e, Submodule.comap_bot, Submodule.ker_subtype]
    · right
      rw [← e, Submodule.comap_map_eq_of_injective C.injective_subtype]

theorem IsGraph.res {H : Subgroup G} {S₁ S₂ : Submodule ℂ V} {X : Submodule ℂ (V × V)} (h : IsGraph ρ H S₁ S₂ X)
    (h₁ : S₁ ≤ C) (h₂ : S₂ ≤ C) :
    IsGraph (res ρ C hC) H (S₁.comap C.subtype) (S₂.comap C.subtype) (X.comap (C.subtype.prodMap C.subtype)) where
  ne := by
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.ne
    refine (Submodule.ne_bot_iff _).2 ⟨(⟨z.1, h₁ (h.mem z hz).1⟩, ⟨z.2, h₂ (h.mem z hz).2⟩), hz, fun e => hz0 ?_⟩
    exact Prod.ext (congrArg (fun p : C × C => (p.1 : V)) e) (congrArg (fun p : C × C => (p.2 : V)) e)
  mem := fun z hz => h.mem _ hz
  stab := fun x hx z hz => h.stab x hx _ hz
  inj₁ := fun u hu => Subtype.ext (h.inj₁ _ hu)
  inj₂ := fun u hu => Subtype.ext (h.inj₂ _ hu)

theorem IsGraph.of_res {H : Subgroup G} {S₁ S₂ : Submodule ℂ V} {X : Submodule ℂ (C × C)}
    (h : IsGraph (HeckeIso.res ρ C hC) H (S₁.comap C.subtype) (S₂.comap C.subtype) X) :
    IsGraph ρ H S₁ S₂ (X.map (C.subtype.prodMap C.subtype)) where
  ne := by
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.ne
    refine (Submodule.ne_bot_iff _).2 ⟨_, ⟨z, hz, rfl⟩, fun e => hz0 ?_⟩
    exact Prod.ext (Subtype.ext (congrArg Prod.fst e)) (Subtype.ext (congrArg Prod.snd e))
  mem := by rintro _ ⟨z, hz, rfl⟩; exact h.mem z hz
  stab := by rintro x hx _ ⟨z, hz, rfl⟩; exact ⟨_, h.stab x hx z hz, rfl⟩
  inj₁ := by
    rintro u ⟨z, hz, e⟩
    have e1 : z.1 = 0 := Subtype.ext (congrArg Prod.fst e)
    have e2 : z.2 = 0 := h.inj₁ _ (by rw [← e1]; exact hz)
    rw [← show (z.2 : V) = u from congrArg Prod.snd e, e2]; rfl
  inj₂ := by
    rintro u ⟨z, hz, e⟩
    have e1 : z.2 = 0 := Subtype.ext (congrArg Prod.snd e)
    have e2 : z.1 = 0 := h.inj₂ _ (by rw [← e1]; exact hz)
    rw [← show (z.1 : V) = u from congrArg Prod.fst e, e2]; rfl

theorem sup_stab {S₁ S₂ : Submodule ℂ V} (h₁ : Irr ρ S₁) (h₂ : Irr ρ S₂) : ∀ g, ∀ x ∈ S₁ ⊔ S₂, ρ g x ∈ S₁ ⊔ S₂ := by
  intro g x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  exact Submodule.add_mem_sup (h₁.stab g a ha) (h₂.stab g b hb)

theorem orbit_res {K : Subgroup G} (horb : ∀ x ∈ C, ((fun k => ρ k x) '' (K : Set G)).Finite) (x : C) :
    ((fun k => res ρ C hC k x) '' (K : Set G)).Finite := by
  refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
  rw [Set.image_image]
  exact horb x x.2

theorem graph_of_hecke {A B K : Subgroup G} (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hd : ∀ g, ∃ x ∈ A, ∃ y ∈ B, g = x * y) (hK : K ≤ A)
    {S₁ S₂ : Submodule ℂ V} (h₁ : Irr ρ S₁) (h₂ : Irr ρ S₂)
    (horb : ∀ x ∈ S₁ ⊔ S₂, ((fun k => ρ k x) '' (K : Set G)).Finite) {f₁ f₂ : V} (hf₁ : f₁ ∈ S₁) (hf₂ : f₂ ∈ S₂)
    (n₁ : f₁ ≠ 0) (n₂ : f₂ ≠ 0) (k₁ : ∀ k ∈ K, ρ k f₁ = f₁) (k₂ : ∀ k ∈ K, ρ k f₂ = f₂)
    (hχ : ∀ x ∈ A, ∃ (R : Finset G) (c : ℂ), R.Nonempty ∧ (∀ γ ∈ R, ∃ a ∈ K, ∃ b ∈ K, γ = a * x * b) ∧
      ∑ γ ∈ R, ρ γ f₁ = c • f₁ ∧ ∑ γ ∈ R, ρ γ f₂ = c • f₂) : ∃ X, IsGraph ρ A S₁ S₂ X := by
  obtain ⟨P, hP⟩ := exists_avg (res ρ _ (sup_stab h₁ h₂)) K (orbit_res horb)
  have key : ∀ (x : G) (R : Finset G) (c : ℂ), R.Nonempty → (∀ γ ∈ R, ∃ a ∈ K, ∃ b ∈ K, γ = a * x * b) →
      ∀ f : ↥(S₁ ⊔ S₂), (∀ k ∈ K, ρ k f = f) → ∑ γ ∈ R, ρ γ f = c • (f : V) →
      P (res ρ _ (sup_stab h₁ h₂) x f) = ((R.card : ℂ)⁻¹ * c) • f := by
    intro x R c hR hγ f hf e
    have hf' : ∀ k ∈ K, res ρ _ (sup_stab h₁ h₂) k f = f := fun k hk => Subtype.ext (hf k hk)
    have e' : ∑ γ ∈ R, res ρ _ (sup_stab h₁ h₂) γ f = c • f := Subtype.ext (by
      rw [Submodule.coe_sum]; exact e)
    have e2 := congrArg P e'
    rw [map_sum, map_smul, hP.self f hf', Finset.sum_congr rfl (g := fun _ => P (res ρ _ (sup_stab h₁ h₂) x f))
      (fun γ hγ' => by
        obtain ⟨a, ha, b, hb, rfl⟩ := hγ γ hγ'
        rw [rho_mul, rho_mul, hf' b hb, hP.tr _ a ha]), Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at e2
    have hc : (R.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hR.card_pos.ne'
    rw [mul_smul, ← e2, smul_smul, inv_mul_cancel₀ hc, one_smul]
  obtain ⟨X, hX⟩ := graph_of_spherical hc hd hK hP (h₁.res le_sup_left) (h₂.res le_sup_right)
    (f₁ := ⟨f₁, Submodule.mem_sup_left hf₁⟩) (f₂ := ⟨f₂, Submodule.mem_sup_right hf₂⟩) hf₁ hf₂
    (fun e => n₁ (congrArg Subtype.val e)) (fun e => n₂ (congrArg Subtype.val e))
    (fun k hk => Subtype.ext (k₁ k hk)) (fun k hk => Subtype.ext (k₂ k hk)) (fun x hx => by
      obtain ⟨R, c, hR, hγ, e1, e2⟩ := hχ x hx
      exact ⟨_, key x R c hR hγ _ k₁ e1, key x R c hR hγ _ k₂ e2⟩)
  exact ⟨_, hX.of_res⟩

end Sub

end GlobalTheory.HeckeIso
