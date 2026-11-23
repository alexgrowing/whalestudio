import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationWeilPairingPropertiesStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

noncomputable section
namespace GlobalTheory.Ex.QStr

@[ext] structure Ext {O : Type} [CommRing O] (N : NumD O) (b : N.A) where
  x : N.X
  u : Oˣ

instance {O : Type} [CommRing O] (N : NumD O) (b : N.A) : CommGroup (Ext N b) where
  mul e e' := ⟨e.x + e'.x, e.u * e'.u / N.θ (N.c e.x) (N.c e'.x) b⟩
  one := ⟨0, 1⟩
  inv e := ⟨-e.x, N.θ (N.c (-e.x)) (N.c e.x) b / e.u⟩
  mul_assoc e e' e'' := by
    refine Ext.ext (add_assoc e.x e'.x e''.x) ?_
    change e.u * e'.u / N.θ (N.c e.x) (N.c e'.x) b * e''.u / N.θ (N.c (e.x + e'.x)) (N.c e''.x) b =
      e.u * (e'.u * e''.u / N.θ (N.c e'.x) (N.c e''.x) b) / N.θ (N.c e.x) (N.c (e'.x + e''.x)) b
    have a := congrArg Additive.ofMul (N.cub.coc (N.c e.x) (N.c e'.x) (N.c e''.x) b)
    rw [N.c_add, N.c_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at a ⊢
    linear_combination (norm := abel) -a
  one_mul e := by
    refine Ext.ext (zero_add e.x) ?_
    change 1 * e.u / N.θ (N.c 0) (N.c e.x) b = e.u
    rw [N.c_zero, N.cub.face, one_mul, div_one]
  mul_one e := by
    refine Ext.ext (add_zero e.x) ?_
    change e.u * 1 / N.θ (N.c e.x) (N.c 0) b = e.u
    rw [N.c_zero, N.cub.face₂, mul_one, div_one]
  inv_mul_cancel e := by
    refine Ext.ext (neg_add_cancel e.x) ?_
    change N.θ (N.c (-e.x)) (N.c e.x) b / e.u * e.u / N.θ (N.c (-e.x)) (N.c e.x) b = 1
    rw [div_mul_cancel, div_self']
  mul_comm e e' := by
    refine Ext.ext (add_comm e.x e'.x) ?_
    change e.u * e'.u / N.θ (N.c e.x) (N.c e'.x) b = e'.u * e.u / N.θ (N.c e'.x) (N.c e.x) b
    rw [N.cub.s01, mul_comm]

theorem exists_lift {O : Type} [CommRing O] (N : NumD O) (b : N.A) : ∃ γ : N.Gt, γ.b = b := by
  let π : Additive (Ext N b) →+ N.X := AddMonoidHom.mk' (fun e => e.toMul.x) fun _ _ => rfl
  obtain ⟨s, hs⟩ := π.toIntLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 fun x => ⟨Additive.ofMul ⟨x, 1⟩, rfl⟩)
  have h : ∀ χ, (s χ).toMul.x = χ := fun χ => LinearMap.congr_fun hs χ
  refine ⟨⟨b, fun χ => (s χ).toMul.u, fun χ χ' => ?_⟩, rfl⟩
  rw [map_add]
  change (s χ).toMul.u * (s χ').toMul.u / N.θ (N.c (s χ).toMul.x) (N.c (s χ').toMul.x) b * _ = _
  rw [h, h, div_mul_cancel]

section Chr
variable {X U ι : Type} [AddCommGroup X] [CommGroup U] [Fintype ι] (v : Module.Basis ι ℤ X)

def chr : (ι → U) →* (Multiplicative X →* U) :=
  MonoidHom.mk' (fun u => MonoidHom.mk' (fun χ => ∏ i, u i ^ v.repr χ.toAdd i) fun a b => by
    simp [zpow_add, Finset.prod_mul_distrib]) fun u u' => by
    ext χ
    simp [mul_zpow, Finset.prod_mul_distrib]

theorem chr_apply (u : ι → U) (χ : Multiplicative X) : chr v u χ = ∏ i, u i ^ v.repr χ.toAdd i := rfl

theorem chr_basis (u : ι → U) (i : ι) : chr v u (Multiplicative.ofAdd (v i)) = u i := by
  classical
  rw [chr_apply, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Finsupp.single_apply, hj.symm]
  · simp

theorem chr_eq (t : Multiplicative X →* U) : chr v (fun i => t (Multiplicative.ofAdd (v i))) = t := by
  refine MonoidHom.ext fun χ => ?_
  rw [chr_apply]
  conv_rhs => rw [← ofAdd_toAdd χ, ← v.sum_repr χ.toAdd, ofAdd_sum, map_prod]
  simp only [ofAdd_zsmul, map_zpow]

theorem chr_injective : Function.Injective (chr (U := U) v) := fun u u' h =>
  funext fun i => by rw [← chr_basis v u, h, chr_basis]

end Chr

theorem split_ext {M : Type} [CommGroup M] (k a d : ℕ) [NeZero k] (hM : ∀ x : M, x ^ k = 1)
    (i : Multiplicative (Fin d → ZMod k) →* M) (π : M →* Multiplicative (Fin a → ZMod k))
    (hi : Function.Injective i) (hπ : Function.Surjective π) (hex : ∀ x, π x = 1 ↔ ∃ y, i y = x) :
    Nonempty (M ≃* Multiplicative (Fin (a + d) → ZMod k)) := by
  letI : Module (ZMod k) (Additive M) := AddCommGroup.zmodModule (n := k) (G := Additive M) fun x => hM x.toMul
  let i' : (Fin d → ZMod k) →ₗ[ZMod k] Additive M := (MonoidHom.toAdditiveRight i).toZModLinearMap k
  let π' : Additive M →ₗ[ZMod k] (Fin a → ZMod k) := (MonoidHom.toAdditiveLeft π).toZModLinearMap k
  obtain ⟨s, hs⟩ := π'.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hπ)
  have hE : Function.Exact i' π' := fun x => hex x.toMul
  let e := (hE.splitSurjectiveEquiv hi ⟨s, hs⟩).1
  let e' : Additive M ≃ₗ[ZMod k] (Fin (a + d) → ZMod k) :=
    e.trans ((LinearEquiv.prodComm _ _ _).trans ((LinearEquiv.sumArrowLequivProdArrow _ _ _ _).symm.trans
      (LinearEquiv.funCongrLeft _ _ finSumFinEquiv.symm)))
  exact ⟨AddEquiv.toMultiplicativeRight e'.toAddEquiv⟩

theorem exists_roots (C : Type) [Field C] [IsAlgClosed C] (k : ℕ) (hk : (k : C) ≠ 0) :
    ∃ ζ : Cˣ, IsPrimitiveRoot ζ k ∧ ∃ e : Multiplicative (ZMod k) →* Cˣ, Function.Injective e ∧
      ∀ u : Cˣ, u ^ k = 1 → ∃ z, e z = u := by
  haveI : NeZero (k : C) := ⟨hk⟩
  haveI : NeZero k := ⟨by rintro rfl; simp at hk⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C k
  have h := hz.isUnit_unit (NeZero.ne k)
  refine ⟨_, h, (Subgroup.subtype _).comp (AddEquiv.toMultiplicativeLeft h.zmodEquivZPowers).toMonoidHom, ?_, ?_⟩
  · exact Subtype.val_injective.comp (AddEquiv.toMultiplicativeLeft h.zmodEquivZPowers).injective
  · intro u hu
    have : u ∈ Subgroup.zpowers _ := h.zpowers_eq ▸ (mem_rootsOfUnity k u).2 hu
    obtain ⟨y, hy⟩ := (AddEquiv.toMultiplicativeLeft h.zmodEquivZPowers).surjective ⟨u, this⟩
    exact ⟨y, congrArg Subtype.val hy⟩

section Main
variable {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ}

theorem tor_div (hk : k ≠ 0) (t : Multiplicative N.X →* Cˣ) : ∃ t' : Multiplicative N.X →* Cˣ, t' ^ k = t := by
  let v := Module.finBasis ℤ N.X
  have h : ∀ u : Cˣ, ∃ w : Cˣ, w ^ k = u := fun u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : C) (Nat.pos_of_ne_zero hk)
    have h0 : z ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by rw [← hz, zero_pow hk])
    exact ⟨Units.mk0 z h0, Units.ext (by simpa using hz)⟩
  choose w hw using h
  refine ⟨chr v fun i => w (t (Multiplicative.ofAdd (v i))), ?_⟩
  rw [← map_pow]
  conv_rhs => rw [← chr_eq v t]
  congr 1
  funext i
  exact hw _

theorem root_over (hk : k ≠ 0) (γ : N.Gt) (b : N.A) (hb : b ^ k = γ.b) : ∃ γ' : N.Gt, γ'.b = b ∧ γ' ^ k = γ := by
  obtain ⟨γ₀, h₀⟩ := exists_lift N b
  obtain ⟨t, ht⟩ := (N.exists_tor_iff (γ * (γ₀ ^ k)⁻¹)).2 (by simp [h₀, hb])
  obtain ⟨t', rfl⟩ := tor_div N hk t
  refine ⟨N.tor t' * γ₀, by simp [h₀], ?_⟩
  rw [mul_pow, ← N.tor_pow, ht, inv_mul_cancel_right]

theorem ker_struct (hk : (k : C) ≠ 0) (a : ℕ)
    (e : (powMonoidHom k : N.A →* N.A).ker ≃* Multiplicative (Fin a → ZMod k)) :
    Nonempty ((powMonoidHom k : N.Gt →* N.Gt).ker ≃* Multiplicative (Fin (a + Module.finrank ℤ N.X) → ZMod k)) := by
  haveI : NeZero k := ⟨by rintro rfl; simp at hk⟩
  obtain ⟨-, -, ε, hε, hε'⟩ := exists_roots C k hk
  let v := Module.finBasis ℤ N.X
  let j : Multiplicative (Fin (Module.finrank ℤ N.X) → ZMod k) →* (Fin (Module.finrank ℤ N.X) → Cˣ) :=
    MonoidHom.mk' (fun y i => ε (Multiplicative.ofAdd (y.toAdd i))) fun y y' => funext fun i => by
      simp [ofAdd_add]
  have hj : Function.Injective j := fun y y' h => by
    refine Multiplicative.toAdd.injective (funext fun i => ?_)
    exact Multiplicative.ofAdd.injective (hε (congrFun h i))
  let i₀ := N.torHom.comp ((chr v).comp j)
  have hpow : ∀ y, i₀ y ∈ (powMonoidHom k : N.Gt →* N.Gt).ker := fun y => by
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← map_pow]
    have : y ^ k = 1 := by
      refine Multiplicative.toAdd.injective (funext fun i => ?_)
      simp
    rw [this, map_one]
  let π₀ : (powMonoidHom k : N.Gt →* N.Gt).ker →* (powMonoidHom k : N.A →* N.A).ker :=
    (N.projB.comp (Subgroup.subtype _)).codRestrict _ fun g => by
      have h : g.1 ^ k = 1 := g.2
      change g.1.b ^ k = 1
      rw [← NumD.Gt.pow_b, h, NumD.Gt.one_b]
  refine split_ext k a _ (fun x => Subtype.ext x.2) (i₀.codRestrict _ hpow) (e.toMonoidHom.comp π₀) ?_ ?_ ?_
  · intro y y' h
    exact hj (chr_injective v (N.tor_injective (congrArg Subtype.val h)))
  · intro z
    obtain ⟨b, rfl⟩ := e.surjective z
    obtain ⟨γ, h, h'⟩ := root_over N (NeZero.ne k) 1 b.1 b.2
    exact ⟨⟨γ, h'⟩, congrArg e (Subtype.ext h)⟩
  · intro x
    constructor
    · intro h
      have h1 : π₀ x = 1 := e.injective (h.trans (map_one e).symm)
      obtain ⟨t, ht⟩ := (N.exists_tor_iff x.1).2 (congrArg Subtype.val h1)
      have h2 : t ^ k = 1 := N.tor_injective (by rw [N.tor_pow, ht, N.tor_one]; exact x.2)
      choose z hz using fun i => hε' (t (Multiplicative.ofAdd (v i))) (DFunLike.congr_fun h2 _)
      refine ⟨Multiplicative.ofAdd fun i => (z i).toAdd, Subtype.ext ?_⟩
      change N.tor (chr v _) = x.1
      rw [← ht, ← chr_eq v t]
      congr 2
      exact funext hz
    · rintro ⟨y, rfl⟩
      exact (congrArg e (Subtype.ext rfl)).trans (map_one e)

theorem exists_nsmul (hk : (k : C) ≠ 0) (y : N.X)
    (h : ∀ t : Multiplicative N.X →* Cˣ, t ^ k = 1 → t (Multiplicative.ofAdd y) = 1) : ∃ z : N.X, y = k • z := by
  classical
  obtain ⟨ζ, hζ, -⟩ := exists_roots C k hk
  let v := Module.finBasis ℤ N.X
  have hd : ∀ i, (k : ℤ) ∣ v.repr y i := fun i => by
    rw [← hζ.zpow_eq_one_iff_dvd]
    have := h (chr v (Pi.mulSingle i ζ)) (by rw [← map_pow, ← Pi.mulSingle_pow, hζ.pow_eq_one, Pi.mulSingle_one, map_one])
    rw [chr_apply, Finset.prod_eq_single i] at this
    · simpa using this
    · intro j _ hj
      simp [Pi.mulSingle_eq_of_ne hj]
    · simp
  choose c hc using hd
  refine ⟨∑ i, c i • v i, ?_⟩
  conv_lhs => rw [← v.sum_repr y]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc, mul_smul, natCast_zsmul]

theorem orth_iff (hk : (k : C) ≠ 0)
    (nd : ∀ b : N.A, b ^ k = 1 → (∀ b', b' ^ k = 1 → N.weil k b b' = 1) → b = 1) (p : N.QT k) :
    (∀ p' : N.QT k, p'.1.1 = 1 → N.wp p p' = 1) ↔ ∃ p₀ : N.QT k, N.QEq p p₀ ∧ p₀.1.1 = 1 ∧ p₀.1.2.b = 1 := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  constructor
  · intro h
    obtain ⟨z, hz⟩ := exists_nsmul N hk p.1.1.toAdd fun t ht => by
      have := h (N.qTor t ht) rfl
      rwa [N.wp_swap, N.wp_qTor, inv_eq_one] at this
    have hq : N.QEq p (p * N.qTriv k (-z)) := (N.qEq_iff _ _).2 ⟨_, rfl⟩
    have h1 : (p * N.qTriv k (-z)).1.1.toAdd = 0 := by
      change p.1.1.toAdd + k • (-z) = 0
      rw [hz, smul_neg, add_neg_cancel]
    refine ⟨_, hq, h1, nd _ ?_ fun b' hb' => ?_⟩
    · rw [N.QT_pow_b, h1, N.c_zero]
    · obtain ⟨γ, hγ, hγ'⟩ := root_over N hk0 1 b' hb'
      let p' : N.QT k := ⟨(1, γ), hγ'.trans N.io_zero.symm⟩
      have e := N.wp_of_eq_zero (p * N.qTriv k (-z)) p' h1 rfl
      rw [← (GlobalTheory.T.degenerationWeilPairing_properties C N k p _ p').2.2.2.2.1 hq, h p' rfl] at e
      rw [← hγ]
      exact e.symm
  · rintro ⟨p₀, hq, h1, h2⟩ p' hp'
    rw [(GlobalTheory.T.degenerationWeilPairing_properties C N k p p₀ p').2.2.2.2.1 hq, (GlobalTheory.T.degenerationWeilPairing_properties C N k p₀ p' p').2.2.2.2.2.1 h1 h2, hp']
    exact NumD.Gt.s_zero _

end Main

theorem qStructure : ∀ (C : Type) [NormedField C] [IsAlgClosed C] (N : NumD C) (n g : ℕ), (n : C) ≠ 0 → N.Tors n g → ∀ j : ℕ, (∀ b : N.A, ∃ γ : N.Gt, γ.b = b) ∧ (∀ γ : N.Gt, ∃ γ' : N.Gt, γ' ^ n ^ j = γ) ∧ (∀ y : N.X, ∃ p : N.QT (n ^ j), p.1.1.toAdd = y) ∧ Nonempty ((powMonoidHom (n ^ j) : N.Gt →* N.Gt).ker ≃* Multiplicative (Fin (2 * g + Module.finrank ℤ N.X) → ZMod (n ^ j))) ∧ (∀ p : N.QT (n ^ j), (∀ p' : N.QT (n ^ j), p'.1.1 = 1 → N.wp p p' = 1) ↔ ∃ p₀ : N.QT (n ^ j), N.QEq p p₀ ∧ p₀.1.1 = 1 ∧ p₀.1.2.b = 1) ∧ ∀ p : N.QT (n ^ j), (∀ p', N.wp p p' = 1) → N.QEq p 1 := by
  intro C _ _ N n g hn hT j
  have hk : ((n ^ j : ℕ) : C) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hn
  have hk0 : n ^ j ≠ 0 := fun h => hk (by rw [h, Nat.cast_zero])
  have hdiv : ∀ (i : ℕ) (x : N.A), ∃ y, y ^ n ^ i = x := by
    intro i
    induction i with
    | zero => exact fun x => ⟨x, by simp⟩
    | succ i ih =>
      intro x
      obtain ⟨y, rfl⟩ := ih x
      obtain ⟨z, rfl⟩ := hT.div y
      exact ⟨z, by rw [pow_succ', pow_mul]⟩
  have h2 : ∀ γ : N.Gt, ∃ γ' : N.Gt, γ' ^ n ^ j = γ := fun γ => by
    obtain ⟨b, hb⟩ := hdiv j γ.b
    obtain ⟨γ', -, h⟩ := root_over N hk0 γ b hb
    exact ⟨γ', h⟩
  have h3 : ∀ y : N.X, ∃ p : N.QT (n ^ j), p.1.1.toAdd = y := fun y => by
    obtain ⟨γ, h⟩ := h2 (N.io y)
    exact ⟨⟨(Multiplicative.ofAdd y, γ), h⟩, rfl⟩
  obtain ⟨e⟩ := hT.str j
  refine ⟨exists_lift N, h2, h3, ker_struct N hk _ e, orth_iff N hk (hT.nondeg j), fun p hp => ?_⟩
  obtain ⟨p₀, hq, h1, hb⟩ := (orth_iff N hk (hT.nondeg j) p).1 fun p' _ => hp p'
  have : p₀ = 1 := by
    refine Subtype.ext (Prod.ext h1 (NumD.Gt.ext hb (funext fun χ => ?_)))
    obtain ⟨p', rfl⟩ := h3 χ
    rw [← (GlobalTheory.T.degenerationWeilPairing_properties C N _ p₀ p' p').2.2.2.2.2.1 h1 hb, ← (GlobalTheory.T.degenerationWeilPairing_properties C N _ p p₀ p').2.2.2.2.1 hq, hp p']
    rfl
  rwa [this] at hq

end GlobalTheory.Ex.QStr
end
