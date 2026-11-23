import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVectorEqNsmulOfAdelicNsmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDvdOfEqNatMulIntegralAdeleAwayFromPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmulStatement

set_option autoImplicit false

noncomputable section

namespace UpperTheory.TorsionCardinalitySetup

section Alg

variable {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q]

theorem card_tors (𝔴 : Ideal R) [h𝔴 : 𝔴.IsMaximal] (s : R) (hs : s ∉ 𝔴)
    (kill : ∀ y ∈ 𝔴, ∀ t : Q, (s * y) • t = 0) :
    Nat.card {t : Q // ∀ y ∈ 𝔴, y • t = 0} = Nat.card (Q ⧸ (𝔴 • ⊤ : Submodule R Q)) := by
  obtain ⟨a, m, hm, ham⟩ := h𝔴.exists_inv hs
  have hsplit : ∀ q : Q, (a * s) • q + m • q = q := by
    intro q
    rw [← add_smul, ham, one_smul]
  have hkill : ∀ y ∈ 𝔴, ∀ q : Q, y • (a * s) • q = 0 := by
    intro y hy q
    rw [smul_smul, show y * (a * s) = a * (s * y) by ring, mul_smul, kill y hy, smul_zero]
  have hker : (𝔴 • ⊤ : Submodule R Q) ≤ LinearMap.ker ((a * s) • LinearMap.id : Q →ₗ[R] Q) := by
    rw [Submodule.smul_le]
    intro y hy t _
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
      show a * s * y = a * (s * y) by ring, mul_smul, kill y hy, smul_zero]
  let f := (𝔴 • ⊤ : Submodule R Q).liftQ ((a * s) • LinearMap.id) hker
  have hf : ∀ q : Q, f (Submodule.Quotient.mk q) = (a * s) • q := fun q => rfl
  refine Nat.card_congr
    { toFun := fun t => Submodule.Quotient.mk t.1
      invFun := fun q => ⟨f q, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · induction q using Submodule.Quotient.induction_on with
    | H q =>
      intro y hy
      rw [hf]
      exact hkill y hy q
  · intro t
    apply Subtype.ext
    change f (Submodule.Quotient.mk t.1) = t.1
    rw [hf]
    have h := hsplit t.1
    rwa [t.2 m hm, add_zero] at h
  · intro q
    induction q using Submodule.Quotient.induction_on with
    | H q =>
      change Submodule.Quotient.mk (f (Submodule.Quotient.mk q)) = Submodule.Quotient.mk q
      rw [hf, Submodule.Quotient.eq]
      have h : (a * s) • q - q = -(m • q) := by
        calc (a * s) • q - q = (a * s) • q - ((a * s) • q + m • q) := by rw [hsplit]
          _ = -(m • q) := by abel
      rw [h]
      exact neg_mem (Submodule.smul_mem_smul hm Submodule.mem_top)

theorem kill_of_pow [IsDedekindDomain R] [IsNoetherian R Q] (𝔴 𝔟 : Ideal R) [h𝔴 : 𝔴.IsMaximal] (h𝔟 : 𝔟 ≠ ⊥) (s : R) (hs : s ∉ 𝔴)
    (kill : ∀ y ∈ 𝔴, ∀ t : Q, (s * y) • t = 0)
    (other : ∀ 𝔞 : Ideal R, 𝔞 ⊔ 𝔴 = ⊤ → 𝔟 ≤ 𝔞 → (𝔞 • ⊤ : Submodule R Q) = ⊤)
    (t : Q) (ht : ∀ b ∈ 𝔟, b • t = 0) : ∀ y ∈ 𝔴, y • t = 0 := by
  let 𝔞 : Ideal R :=
    { carrier := {x | ∀ y ∈ 𝔴, (x * y) • t = 0}
      add_mem' := fun {a b} ha hb y hy => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [add_mul, add_smul, ha y hy, hb y hy, add_zero]
      zero_mem' := fun y _ => by simp
      smul_mem' := fun c x hx y hy => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
        rw [mul_assoc, mul_smul, hx y hy, smul_zero] }
  have mem𝔞 : ∀ x, x ∈ 𝔞 ↔ ∀ y ∈ 𝔴, (x * y) • t = 0 := fun x => Iff.rfl
  have hs𝔞 : s ∈ 𝔞 := (mem𝔞 s).2 fun y hy => kill y hy t
  have hcop : 𝔞 ⊔ 𝔴 = ⊤ := by
    by_contra hne
    have hle : 𝔞 ⊔ 𝔴 = 𝔴 := (h𝔴.eq_of_le hne le_sup_right).symm
    exact hs (hle ▸ Ideal.mem_sup_left hs𝔞)
  have hb : 𝔟 ≤ 𝔞 := fun b hb' => (mem𝔞 b).2 fun y _ => by
    rw [mul_comm, mul_smul, ht b hb', smul_zero]
  have htop := other 𝔞 hcop hb
  have hle : (⊤ : Submodule R Q) ≤ 𝔞 • ⊤ := by rw [htop]
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔞 (⊤ : Submodule R Q)
    (IsNoetherian.noetherian ⊤) hle
  intro y hy
  have h1 := (mem𝔞 _).1 hr1 y hy
  have h2 : (r * y) • t = 0 := by rw [mul_comm, mul_smul, hr t Submodule.mem_top, smul_zero]
  rw [sub_mul, one_mul, sub_smul, h2, zero_sub, neg_eq_zero] at h1
  exact h1

end Alg

section Core

variable {R La V P : Type} [CommRing R] [AddCommGroup La] [Module R La] [AddCommGroup V] [Module R V] [Group P]

abbrev Qt (Λ : Submodule R V) (H₀ : V →ₗ[R] V) : Type := Λ ⧸ (Λ.map H₀).submoduleOf Λ

structure Setup (Λ : Submodule R V) (ι : La →ₗ[R] V) (H₀ U U' J : V →ₗ[R] V) (M : ℕ) : Prop where
  ι_mem : ∀ x, ι x ∈ Λ
  dense : ∀ v ∈ Λ, ∃ x, ∃ w ∈ Λ, v = ι x + M • w
  dvd : ∀ x, ∀ w ∈ Λ, ι x = M • w → ∃ z, x = M • z
  tf : ∀ v : V, M • v = 0 → v = 0
  inj : Function.Injective H₀
  H₀_mem : ∀ v ∈ Λ, H₀ v ∈ Λ
  back : ∀ v ∈ Λ, ∃ v' ∈ Λ, H₀ v' = M • v
  U_mem : ∀ v ∈ Λ, U v ∈ Λ
  U'_mem : ∀ v ∈ Λ, U' v ∈ Λ
  UU' : ∀ v, U (U' v) = v
  U'U : ∀ v, U' (U v) = v
  J_eq : ∀ v, M • J v = H₀ (U v)

variable {Λ : Submodule R V} {ι : La →ₗ[R] V} {H₀ U U' J : V →ₗ[R] V} {M : ℕ}

theorem Setup.cancel (S : Setup Λ ι H₀ U U' J M) {a b : V} (h : M • a = M • b) : a = b := by
  have : M • (a - b) = 0 := by rw [smul_sub, h, sub_self]
  exact sub_eq_zero.1 (S.tf _ this)

def Wm (Λ : Submodule R V) (ι : La →ₗ[R] V) (J : V →ₗ[R] V) : Submodule R La := (Λ.comap J).comap ι

def Ps (Λ : Submodule R V) (ι : La →ₗ[R] V) (H₀ J : V →ₗ[R] V) : Wm Λ ι J →ₗ[R] Qt Λ H₀ :=
  ((Λ.map H₀).submoduleOf Λ).mkQ ∘ₗ ((J ∘ₗ ι).domRestrict (Wm Λ ι J)).codRestrict Λ (fun x => x.2)

theorem Setup.mem_W (S : Setup Λ ι H₀ U U' J M) (x : La) :
    x ∈ Wm Λ ι J ↔ ∃ v ∈ Λ, H₀ (U (ι x)) = M • v := by
  show J (ι x) ∈ Λ ↔ _
  constructor
  · intro h
    exact ⟨_, h, (S.J_eq _).symm⟩
  · rintro ⟨v, hv, he⟩
    rw [S.cancel ((S.J_eq _).trans he)]
    exact hv

theorem Setup.ps_zero (S : Setup Λ ι H₀ U U' J M) (x : Wm Λ ι J) :
    Ps Λ ι H₀ J x = 0 ↔ ∃ z, x.1 = M • z := by
  have key : Ps Λ ι H₀ J x = 0 ↔ J (ι x.1) ∈ Λ.map H₀ := by
    simp only [Ps, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    rfl
  rw [key]
  constructor
  · rintro ⟨w, hw, he⟩
    have hU : U (ι x.1) = M • w := by
      apply S.inj
      rw [map_nsmul, he, ← S.J_eq]
    obtain ⟨z, hz⟩ := S.dvd x.1 (U' w) (S.U'_mem _ hw)
      (by rw [← map_nsmul, ← hU, S.U'U])
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    refine ⟨U (ι z), S.U_mem _ (S.ι_mem _), ?_⟩
    apply S.cancel
    rw [S.J_eq, hz, map_nsmul, map_nsmul, map_nsmul]

theorem Setup.ps_surj (S : Setup Λ ι H₀ U U' J M) : Function.Surjective (Ps Λ ι H₀ J) := by
  intro q
  obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨v'', hv'', hb⟩ := S.back v hv
  obtain ⟨x, w, hw, hd⟩ := S.dense (U' v'') (S.U'_mem _ hv'')
  have hx : ι x = U' v'' - M • w := eq_sub_of_add_eq hd.symm
  have hJ : J (ι x) = v - H₀ (U w) := by
    apply S.cancel
    rw [S.J_eq, hx, map_sub, map_nsmul, S.UU', map_sub, map_nsmul, hb, smul_sub]
  have hmem : x ∈ Wm Λ ι J := by
    show J (ι x) ∈ Λ
    rw [hJ]
    exact Λ.sub_mem hv (S.H₀_mem _ (S.U_mem _ hw))
  refine ⟨⟨x, hmem⟩, ?_⟩
  simp only [Ps, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq]
  show J (ι x) - v ∈ Λ.map H₀
  rw [hJ, sub_sub_cancel_left, ← map_neg]
  exact Submodule.mem_map_of_mem (Λ.neg_mem (S.U_mem _ hw))

theorem mem_smul_top (I : Ideal R) (v : Λ) :
    Submodule.Quotient.mk (p := (Λ.map H₀).submoduleOf Λ) v ∈ (I • ⊤ : Submodule R (Qt Λ H₀)) ↔ v.1 ∈ Λ.map H₀ ⊔ I • Λ := by
  have h1 : (I • ⊤ : Submodule R (Qt Λ H₀)) =
      (I • ⊤ : Submodule R Λ).map ((Λ.map H₀).submoduleOf Λ).mkQ := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  rw [h1]
  change v ∈ Submodule.comap ((Λ.map H₀).submoduleOf Λ).mkQ
    ((I • ⊤ : Submodule R Λ).map ((Λ.map H₀).submoduleOf Λ).mkQ) ↔ _
  rw [Submodule.comap_map_mkQ, Submodule.mem_sup, Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, he⟩
    exact ⟨y.1, hy, z.1, (Submodule.mem_smul_top_iff I Λ z).mp hz, by rw [← he]; rfl⟩
  · rintro ⟨y, hy, z, hz, he⟩
    have hzΛ : z ∈ Λ := Submodule.smul_le_right hz
    have hyΛ : y ∈ Λ := by
      have : y = v.1 - z := eq_sub_of_add_eq he
      rw [this]
      exact Λ.sub_mem v.2 hzΛ
    refine ⟨⟨y, hyΛ⟩, hy, ⟨z, hzΛ⟩, (Submodule.mem_smul_top_iff I Λ _).mpr hz, ?_⟩
    ext
    exact he

theorem Setup.kill_Q (S : Setup Λ ι H₀ U U' J M) (𝔴 : Ideal R) (s : R)
    (kill : ∀ y ∈ 𝔴, ∀ v ∈ Λ, ∃ v' ∈ Λ, H₀ v' = (s * y) • v) :
    ∀ y ∈ 𝔴, ∀ t : Qt Λ H₀, (s * y) • t = 0 := by
  intro y hy t
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  obtain ⟨v', hv', he⟩ := kill y hy v.1 v.2
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact ⟨v', hv', he⟩

theorem Setup.core1 [IsDedekindDomain R] [IsNoetherian R La] (S : Setup Λ ι H₀ U U' J M) (ev : La → P) (act : R → P → P) (Kp : P → Prop)
    (ev_lin : ∀ c x, ev (c • x) = act c (ev x))
    (ev_ker : ∀ x, ev x = 1 → ∃ y, x = M • y)
    (ev_ker' : ∀ y, ev (M • y) = 1)
    (ev_K : ∀ x, Kp (ev x) ↔ ∃ v ∈ Λ, H₀ (U (ι x)) = M • v)
    (K_ev : ∀ g, Kp g → ∃ x, g = ev x)
    (𝔴 𝔟 : Ideal R) [h𝔴 : 𝔴.IsMaximal] (h𝔟 : 𝔟 ≠ ⊥) (s : R) (hs : s ∉ 𝔴)
    (kill : ∀ y ∈ 𝔴, ∀ v ∈ Λ, ∃ v' ∈ Λ, H₀ v' = (s * y) • v)
    (other : ∀ 𝔞 : Ideal R, 𝔞 ⊔ 𝔴 = ⊤ → 𝔟 ≤ 𝔞 → ∀ v ∈ Λ, H₀ v - v ∈ 𝔞 • Λ)
    (g : P) (hg : Kp g) (hb : ∀ b ∈ 𝔟, act b g = 1) : ∀ y ∈ 𝔴, act y g = 1 := by
  intro y hy
  obtain ⟨x, rfl⟩ := K_ev g hg
  have hxW : x ∈ Wm Λ ι J := (S.mem_W x).2 ((ev_K x).1 hg)
  have hkill : ∀ c : R, act c (ev x) = 1 → c • Ps Λ ι H₀ J ⟨x, hxW⟩ = 0 := by
    intro c hc
    rw [← map_smul]
    apply (S.ps_zero _).2
    obtain ⟨z, hz⟩ := ev_ker (c • x) (by rw [ev_lin]; exact hc)
    exact ⟨z, hz⟩
  have hback : ∀ c : R, c • Ps Λ ι H₀ J ⟨x, hxW⟩ = 0 → act c (ev x) = 1 := by
    intro c hc
    rw [← map_smul] at hc
    obtain ⟨z, hz⟩ := (S.ps_zero _).1 hc
    have hz' : c • x = M • z := hz
    rw [← ev_lin, hz', ev_ker']
  haveI : IsNoetherian R (Qt Λ H₀) :=
    isNoetherian_of_surjective _ (LinearMap.range_eq_top.2 (S.ps_surj))
  apply hback
  refine kill_of_pow 𝔴 𝔟 h𝔟 s hs (S.kill_Q 𝔴 s kill) ?_ _ (fun b hb' => hkill b (hb b hb')) y hy
  intro 𝔞 h1 h2
  rw [eq_top_iff]
  intro t _
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  rw [mem_smul_top]
  have h3 := other 𝔞 h1 h2 v.1 v.2
  have hv : v.1 = H₀ v.1 - (H₀ v.1 - v.1) := by abel
  rw [hv]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨v.1, v.2, rfl⟩) (Submodule.mem_sup_right h3)

theorem Setup.core2 (S : Setup Λ ι H₀ U U' J M) (ev : La → P) (act : R → P → P) (Kp : P → Prop)
    (ev_lin : ∀ c x, ev (c • x) = act c (ev x))
    (ev_ker : ∀ x, ev x = 1 → ∃ y, x = M • y)
    (ev_ker' : ∀ y, ev (M • y) = 1)
    (ev_add : ∀ x y, ev (x + y) = ev x * ev y)
    (ev_K : ∀ x, Kp (ev x) ↔ ∃ v ∈ Λ, H₀ (U (ι x)) = M • v)
    (K_ev : ∀ g, Kp g → ∃ x, g = ev x)
    (𝔴 : Ideal R) [h𝔴 : 𝔴.IsMaximal] (s : R) (hs : s ∉ 𝔴)
    (kill : ∀ y ∈ 𝔴, ∀ v ∈ Λ, ∃ v' ∈ Λ, H₀ v' = (s * y) • v)
    (C : AddSubgroup V) (hC : ∀ v, v ∈ C ↔ v ∈ Λ.map H₀ ⊔ 𝔴 • Λ) :
    Nat.card {g // Kp g ∧ ∀ y ∈ 𝔴, act y g = 1} = C.relIndex Λ.toAddSubgroup := by
  have key : ∀ x₁ x₂ : Wm Λ ι J, Ps Λ ι H₀ J x₁ = Ps Λ ι H₀ J x₂ ↔ ev x₁.1 = ev x₂.1 := by
    intro x₁ x₂
    have he : ev x₁.1 = ev (x₁ - x₂).1 * ev x₂.1 := by
      rw [← ev_add]
      congr 1
      simp
    rw [← sub_eq_zero, ← map_sub, S.ps_zero, he, mul_eq_right]
    constructor
    · rintro ⟨z, hz⟩
      rw [hz, ev_ker']
    · intro h
      exact ev_ker _ h
  have kil : ∀ x : Wm Λ ι J, (∀ y ∈ 𝔴, y • Ps Λ ι H₀ J x = 0) ↔ (∀ y ∈ 𝔴, act y (ev x.1) = 1) := by
    intro x
    refine forall₂_congr fun y _ => ?_
    rw [← map_smul, S.ps_zero, ← ev_lin]
    constructor
    · rintro ⟨z, hz⟩
      rw [show y • x.1 = M • z from hz, ev_ker']
    · intro h
      exact ev_ker _ h
  have memW : ∀ x : La, Kp (ev x) → x ∈ Wm Λ ι J := fun x h => (S.mem_W x).2 ((ev_K x).1 h)
  have inK : ∀ x : Wm Λ ι J, Kp (ev x.1) := fun x => (ev_K x.1).2 ((S.mem_W x.1).1 x.2)
  let F : {t : Qt Λ H₀ // ∀ y ∈ 𝔴, y • t = 0} → {g // Kp g ∧ ∀ y ∈ 𝔴, act y g = 1} := fun t =>
    ⟨ev (S.ps_surj t.1).choose.1, inK _,
      (kil _).1 (by rw [(S.ps_surj t.1).choose_spec]; exact t.2)⟩
  have hF : Function.Bijective F := by
    constructor
    · intro t₁ t₂ h
      apply Subtype.ext
      have h' : ev (S.ps_surj t₁.1).choose.1 = ev (S.ps_surj t₂.1).choose.1 := congrArg Subtype.val h
      have h'' := (key _ _).2 h'
      rwa [(S.ps_surj t₁.1).choose_spec, (S.ps_surj t₂.1).choose_spec] at h''
    · rintro ⟨g, hg, hk⟩
      obtain ⟨x, rfl⟩ := K_ev g hg
      let xw : Wm Λ ι J := ⟨x, memW x hg⟩
      refine ⟨⟨Ps Λ ι H₀ J xw, (kil xw).2 hk⟩, ?_⟩
      apply Subtype.ext
      exact (key _ xw).1 (S.ps_surj _).choose_spec
  rw [← Nat.card_eq_of_bijective F hF, card_tors 𝔴 s hs (S.kill_Q 𝔴 s kill)]
  let φ : Λ.toAddSubgroup →+ (Qt Λ H₀ ⧸ (𝔴 • ⊤ : Submodule R (Qt Λ H₀))) :=
    ((𝔴 • ⊤ : Submodule R (Qt Λ H₀)).mkQ ∘ₗ ((Λ.map H₀).submoduleOf Λ).mkQ).toAddMonoidHom
  have hφ : Function.Surjective φ := by
    intro t
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨v, rfl⟩
  have hker : φ.ker = C.addSubgroupOf Λ.toAddSubgroup := by
    ext v
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, hC]
    exact (Submodule.Quotient.mk_eq_zero _).trans (mem_smul_top 𝔴 v)
  rw [AddSubgroup.relIndex, AddSubgroup.index, ← hker]
  exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).toEquiv).symm

end Core

end UpperTheory.TorsionCardinalitySetup

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct

namespace UpperTheory.TorsionCardinalitySetup

section Lat

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

def rho : 𝓞 D.F →+* Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  (Module.End.baseChangeHom ℚ (AfP p) (VQ D)).toRingHom.comp
    (L.rep.toRingHom.comp ((algebraMap G.F G.C).comp (L.e.toRingHom.comp (algebraMap (𝓞 D.F) D.F))))

theorem rho_apply (c : 𝓞 D.F) : rho L c = mulF D c := by
  show Module.End.baseChangeHom ℚ (AfP p) (VQ D) (L.rep (algebraMap G.F G.C (L.e (c : D.F)))) = _
  rw [L.rep_F]
  rfl

theorem comm_central (y : AfP p ⊗[ℚ] G.C) (b : G.C) (hb : ∀ x : G.C, x * b = b * x) :
    Commute y ((1 : AfP p) ⊗ₜ[ℚ] b) := by
  induction y using TensorProduct.induction_on with
  | zero => exact Commute.zero_left _
  | tmul a x =>
    simp only [Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul]
    rw [_root_.mul_one, _root_.one_mul, hb x]
  | add y z hy hz => exact hy.add_left hz

theorem actG_mulF (g : G.GAf) (c : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D) :
    L.actG g (mulF D c v) = mulF D c (L.actG g v) := by
  have hz : mulF D c = actOn L.rep (AfP p) ((1 : AfP p) ⊗ₜ[ℚ] algebraMap G.F G.C (L.e c)) := by
    rw [← rho_apply L]
    unfold actOn
    erw [Algebra.TensorProduct.lift_tmul]
    simp only [_root_.map_one, _root_.one_mul]
    rfl
  have key : ∀ w : AfP p ⊗[ℚ] G.C,
      actOn L.rep (AfP p) w (mulF D c v) = mulF D c (actOn L.rep (AfP p) w v) := by
    intro w
    rw [hz, ← Module.End.mul_apply, ← Module.End.mul_apply, ← _root_.map_mul, ← _root_.map_mul,
      (comm_central w _ (fun x => (Algebra.commutes _ x).symm)).eq]
  exact key _

theorem mulF_mem (c : 𝓞 D.F) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) : mulF D c v ∈ LaHat D := by
  unfold LaHat at hv ⊢
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    apply AddSubgroup.subset_closure
    refine ⟨a, algebraMap (𝓞 D.F) D.O c • x, ha, ?_⟩
    simp [mulF, actQ]
    rfl
  | zero => rw [_root_.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [_root_.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [_root_.map_neg]; exact neg_mem hx

theorem inAf_add' (x y : D.La) : inAf D (x + y) = inAf D x + inAf D y := by
  simp [inAf, TensorProduct.tmul_add]

theorem inAf_zero' : inAf D (0 : D.La) = 0 := by
  simp [inAf]

theorem inAf_mem' (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by simp, rfl⟩

theorem inAf_mulF (c : 𝓞 D.F) (x : D.La) : inAf D (algebraMap (𝓞 D.F) D.O c • x) = mulF D c (inAf D x) := by
  simp [mulF, actQ, inAf, LinearMap.baseChange_tmul]
  rfl

end Lat

section Main

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

theorem lat_main (q : ℕ) (r : ℤ) (𝔴 : Ideal (𝓞 D.F)) (i : ℕ) (h₀ u : G.GAf) (hA : AtPrime D q r 𝔴)
    (hT : IsTjElt L q r 𝔴 i h₀) (hI : Integ L h₀) (hu : u ∈ L.KN 1) (M : ℕ) (hMe : M = Ideal.absNorm 𝔴 ^ i) (hM0 : 0 < M)
    (hMp : M.Coprime p) {P : Type} [Group P] (ev : D.La → P) (act : 𝓞 D.F → P → P) (Kp : P → Prop)
    (ev_add : ∀ x y, ev (x + y) = ev x * ev y)
    (ev_lin : ∀ c x, ev (algebraMap (𝓞 D.F) D.O c • x) = act c (ev x))
    (ev_ker : ∀ x, ev x = 1 → ∃ y, x = M • y)
    (ev_ker' : ∀ y, ev (M • y) = 1)
    (ev_K : ∀ x, Kp (ev x) ↔ ∃ v ∈ LaHat D, L.actG (h₀ * u) (inAf D x) = M • v)
    (K_ev : ∀ g, Kp g → ∃ x, g = ev x) :
    (∀ g, Kp g → (∃ e : ℕ, ∀ x ∈ uId D q r ^ e, act x g = 1) → ∀ y ∈ 𝔴, act y g = 1) ∧
    Nat.card {g // Kp g ∧ ∀ y ∈ 𝔴, act y g = 1} = Ideal.absNorm 𝔴 ^ i := by
  subst hMe
  haveI := hA.max
  haveI := D.finLa
  obtain ⟨s, hs, hk⟩ := hT.kill
  letI iLa : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  letI iV : Module (𝓞 D.F) (AfP p ⊗[ℚ] VQ D) := Module.compHom (AfP p ⊗[ℚ] VQ D) (rho L)
  haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ (𝓞 D.F) D.La
  have hsm : ∀ (c : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D), c • v = mulF D c v := fun c v => by
    show rho L c v = _
    rw [rho_apply]
  let Λ : Submodule (𝓞 D.F) (AfP p ⊗[ℚ] VQ D) :=
    { carrier := (LaHat D : Set (AfP p ⊗[ℚ] VQ D))
      add_mem' := fun ha hb => (LaHat D).add_mem ha hb
      zero_mem' := (LaHat D).zero_mem
      smul_mem' := fun c v hv => by
        rw [hsm]
        exact mulF_mem c hv }
  let em : D.La →ₗ[𝓞 D.F] (AfP p ⊗[ℚ] VQ D) :=
    { toFun := inAf D
      map_add' := inAf_add'
      map_smul' := fun c x => by
        rw [RingHom.id_apply, hsm]
        exact inAf_mulF c x }
  let A : G.GAf → (AfP p ⊗[ℚ] VQ D) →ₗ[𝓞 D.F] (AfP p ⊗[ℚ] VQ D) := fun g =>
    { toFun := L.actG g
      map_add' := map_add (L.actG g)
      map_smul' := fun c v => by
        rw [RingHom.id_apply, hsm, hsm]
        exact actG_mulF L g c v }
  let a : AfP p := algebraMap ℚ (AfP p) ((Ideal.absNorm 𝔴 ^ i : ℕ) : ℚ)⁻¹
  have ha : ∀ v : AfP p ⊗[ℚ] VQ D, (Ideal.absNorm 𝔴 ^ i) • (a • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul (AfP p), smul_smul, ← map_natCast (algebraMap ℚ (AfP p)), ← map_mul,
      mul_inv_cancel₀ (by exact_mod_cast hM0.ne'), map_one, one_smul]
  have ha' : ∀ v : AfP p ⊗[ℚ] VQ D, a • ((Ideal.absNorm 𝔴 ^ i) • v) = v := fun v => by
    rw [smul_comm]
    exact ha v
  let J : (AfP p ⊗[ℚ] VQ D) →ₗ[𝓞 D.F] (AfP p ⊗[ℚ] VQ D) :=
    { toFun := fun v => a • L.actG (h₀ * u) v
      map_add' := fun v w => by rw [map_add, smul_add]
      map_smul' := fun c v => by
        simp only [RingHom.id_apply, hsm]
        rw [actG_mulF, LinearMap.map_smul] }
  have hAmul : ∀ g h v, A g (A h v) = L.actG (g * h) v := fun g h v => by
    show L.actG g (L.actG h v) = _
    rw [map_mul]
    rfl
  have hS : Setup Λ em (A h₀) (A u) (A u⁻¹) J (Ideal.absNorm 𝔴 ^ i) :=
    { ι_mem := inAf_mem'
      dense := GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D _ hM0 hMp
      dvd := fun x w hw h => GlobalTheory.T.exists_latticeVector_eq_nsmul_of_adelic_nsmul p D _ hM0 hMp (GlobalTheory.T.int_dvd_of_eq_nat_mul_integralAdeleAwayFromP p _ hM0 hMp) x ⟨w, hw, h⟩
      tf := fun v hv => by rw [← ha' v, hv, smul_zero]
      inj := fun v w h => by
        have h' := congrArg (A h₀⁻¹) h
        rw [hAmul, hAmul, inv_mul_cancel, map_one] at h'
        exact h'
      H₀_mem := hI
      back := hT.back
      U_mem := integ_of_mem hu
      U'_mem := integ_of_mem (inv_mem hu)
      UU' := fun v => by rw [hAmul, mul_inv_cancel, map_one, Module.End.one_apply]
      U'U := fun v => by rw [hAmul, inv_mul_cancel, map_one, Module.End.one_apply]
      J_eq := fun v => by
        rw [hAmul]
        exact ha _ }
  have ev_K' : ∀ x, Kp (ev x) ↔ ∃ v ∈ Λ, A h₀ (A u (em x)) = (Ideal.absNorm 𝔴 ^ i) • v := fun x => by
    rw [hAmul]
    exact ev_K x
  have kill' : ∀ y ∈ 𝔴, ∀ v ∈ Λ, ∃ v' ∈ Λ, A h₀ v' = (s * y) • v := fun y hy v hv => by
    obtain ⟨v', hv', e⟩ := hk y hy v hv
    exact ⟨v', hv', by rw [hsm]; exact e⟩
  have hid : ∀ 𝔞 : Ideal (𝓞 D.F), idHat D 𝔞 = (𝔞 • Λ).toAddSubgroup := fun 𝔞 => by
    apply le_antisymm
    · show AddSubgroup.closure _ ≤ _
      rw [AddSubgroup.closure_le]
      rintro _ ⟨x, hx, v, hv, rfl⟩
      rw [← hsm]
      exact Submodule.smul_mem_smul hx hv
    · intro v hv
      refine Submodule.smul_induction_on (p := fun v => v ∈ idHat D 𝔞) hv (fun r hr n hn => ?_)
        (fun x y hx hy => add_mem hx hy)
      rw [hsm]
      exact AddSubgroup.subset_closure (k := {z | ∃ x ∈ 𝔞, ∃ v ∈ LaHat D, z = mulF D x v}) ⟨r, hr, n, hn, rfl⟩
  refine ⟨fun g hg ⟨e, he⟩ => ?_, ?_⟩
  · have h1 : uId D q r ≠ ⊥ := by
      intro h
      have hq : ((q : ℕ) : 𝓞 D.F) ∈ uId D q r := Ideal.subset_span (by simp)
      rw [h, Ideal.mem_bot] at hq
      exact hA.prime.ne_zero (by exact_mod_cast hq)
    exact hS.core1 ev act Kp ev_lin ev_ker ev_ker' ev_K' K_ev 𝔴 (uId D q r ^ e) (pow_ne_zero e h1) s hs kill'
      (fun 𝔞 h2 h3 v hv => by
        have := hT.other 𝔞 h2 ⟨e, h3⟩ v hv
        rw [hid] at this
        exact this) g hg he
  · have hCeq : AddSubgroup.map (L.actG h₀).toAddMonoidHom (LaHat D) ⊔ idHat D 𝔴 =
        (Λ.map (A h₀) ⊔ 𝔴 • Λ).toAddSubgroup := by
      rw [Submodule.sup_toAddSubgroup, hid]
      rfl
    have hC : ∀ v, v ∈ AddSubgroup.map (L.actG h₀).toAddMonoidHom (LaHat D) ⊔ idHat D 𝔴 ↔
        v ∈ Λ.map (A h₀) ⊔ 𝔴 • Λ := fun v => by
      rw [hCeq]
      rfl
    exact (hS.core2 ev act Kp ev_lin ev_ker ev_ker' ev_add ev_K' K_ev 𝔴 s hs kill' _ hC).trans hT.card

end Main

section Fin

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

theorem inAf_nsmul' (k : ℕ) (x : D.La) : inAf D (k • x) = k • inAf D x := by
  induction k with
  | zero => simp [inAf_zero']
  | succ k ih => rw [succ_nsmul, succ_nsmul, inAf_add', ih]

theorem coprime_norm {q : ℕ} (𝔴 : Ideal (𝓞 D.F)) (hq : q.Prime) (hne : q ≠ p) (hmem : (q : 𝓞 D.F) ∈ 𝔴) :
    (Ideal.absNorm 𝔴).Coprime p ∧ 0 < Ideal.absNorm 𝔴 := by
  have hle : Ideal.span {(q : 𝓞 D.F)} ≤ 𝔴 := (Ideal.span_singleton_le_iff_mem _).2 hmem
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_singleton] at hdvd
  have hn : Algebra.norm ℤ (q : 𝓞 D.F) = (q : ℤ) ^ Module.finrank ℤ (𝓞 D.F) := by
    rw [← map_natCast (algebraMap ℤ (𝓞 D.F)), Algebra.norm_algebraMap]
  rw [hn, Int.natAbs_pow, Int.natAbs_natCast] at hdvd
  refine ⟨Nat.Coprime.coprime_dvd_left hdvd (Nat.Coprime.pow_left _ ((Nat.coprime_primes hq (Fact.out)).2 hne)), ?_⟩
  exact Nat.pos_of_dvd_of_pos hdvd (pow_pos hq.pos _)

end Fin

end UpperTheory.TorsionCardinalitySetup

open UpperTheory.TorsionCardinalitySetup

theorem UpperTheory.trace_identity_of_tjElement :
    TrTj := by
  intro p _ D G L R _ _ gb h X s N' N o' o ψ hT q r 𝔴 i h₀ u hA hTj hI hu hh Ω _ _ z
  obtain ⟨_, _, ⟨ψ', d, hmon', _, h1, _, hd⟩, _, hgeo⟩ := hT
  obtain ⟨I', I'', _, _, hiff⟩ := hgeo Ω z (Spec.preimage (z ≫ s)).hom
    (by rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage])
  have hq : ((q : ℕ) : 𝓞 D.F) ∈ 𝔴 := hA.le (by
    unfold uId
    exact Ideal.subset_span (Set.mem_insert _ _))
  obtain ⟨hcop, hpos⟩ := coprime_norm 𝔴 hA.prime hA.ne hq
  obtain ⟨M, hMe⟩ : ∃ M, M = Ideal.absNorm 𝔴 ^ i := ⟨_, rfl⟩
  have hM0 : 0 < M := hMe ▸ pow_pos hpos i
  have hMp : M.Coprime p := hMe ▸ hcop.pow_left i
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      exact absurd (Nat.coprime_zero_left _ |>.1 hd) (Fact.out : p.Prime).one_lt.ne'
    · exact h0
  have ev_pow : ∀ (n : ℕ), 0 < n → ∀ (k : ℕ) (x : D.La), I'.ev n (k • x) = I'.ev n x ^ k := by
    intro n hn k x
    induction k with
    | zero =>
      rw [zero_nsmul, pow_zero]
      exact (I'.ker n hn 0).2 ⟨0, by simp⟩
    | succ k ih =>
      rw [succ_nsmul, pow_succ, ← ih]
      exact I'.add n (k • x) x
  have h0'' : ∀ (n : ℕ), 0 < n → I''.ev n (0 : D.La) = 1 := fun n hn => (I''.ker n hn 0).2 ⟨0, by simp⟩
  have hinj : Function.Injective (L.actG h₀) := by
    intro a b hab
    have := congrArg (L.actG h₀⁻¹) hab
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at this
  refine lat_main L q r 𝔴 i h₀ u hA hTj hI hu M hMe hM0 hMp (P := Over.mk z ⟶ o'.A) (I'.ev M)
    (fun c g => g ≫ o'.act.act (algebraMap (𝓞 D.F) D.O c)) (fun g => g ≫ ψ = 1)
    (I'.add M) (fun c x => I'.lin M _ x) (fun x hx => (I'.ker M hM0 x).1 hx)
    (fun y => (I'.ker M hM0 _).2 ⟨y, rfl⟩) ?_ ?_
  · intro x
    have e := hiff M hM0 hMp x 0
    rw [h0'' M hM0, hh] at e
    refine e.trans (exists_congr fun v => and_congr_right fun _ => Eq.congr_right ?_)
    rw [inAf_zero']
    exact zero_add _
  · intro g hg
    haveI := hmon'
    have e1 : g ≫ ψ ≫ ψ' = g ^ d := by rw [h1, comp_pow, Category.comp_id]
    have e0 : g ≫ ψ ≫ ψ' = 1 := by
      rw [← Category.assoc, hg]
      exact (IsMonHom.monoidHom ψ' _).map_one
    obtain ⟨x, hx⟩ := (I'.onto d hd0 g).1 (e1.symm.trans e0)
    obtain ⟨v, hv, hxv⟩ := (hiff d hd0 hd x 0).1 (by rw [hx, hg, h0'' d hd0])
    rw [inAf_zero', zero_add, hh, map_mul, Module.End.mul_apply] at hxv
    obtain ⟨v', hv', hv'e⟩ := hTj.back v hv
    rw [← hMe] at hv'e
    have e2 : M • L.actG u (inAf D x) = d • v' := hinj (by
      rw [map_nsmul, map_nsmul, hxv, hv'e, ← mul_nsmul, ← mul_nsmul, mul_comm])
    have e3 := congrArg (L.actG u⁻¹) e2
    rw [map_nsmul, map_nsmul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at e3
    have hmem : L.actG u⁻¹ v' ∈ LaHat D := by
      obtain ⟨w, hw, hwe⟩ := hu.2 v' hv'
      rw [hwe, one_nsmul]
      exact add_mem hv' hw
    obtain ⟨y, hy⟩ := GlobalTheory.T.exists_latticeVector_eq_nsmul_of_adelic_nsmul p D d hd0 hd (GlobalTheory.T.int_dvd_of_eq_nat_mul_integralAdeleAwayFromP p d hd0 hd) (M • x)
      ⟨_, hmem, (inAf_nsmul' M x).trans e3⟩
    have hgM : I'.ev d x ^ M = 1 :=
      (ev_pow d hd0 M x).symm.trans ((congrArg (I'.ev d) hy).trans ((I'.ker d hd0 _).2 ⟨y, rfl⟩))
    obtain ⟨x', hx'⟩ := (I'.onto M hM0 g).1 (hx ▸ hgM)
    exact ⟨x', hx'.symm⟩

end
