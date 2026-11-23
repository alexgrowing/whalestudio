import Mathlib
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent

noncomputable section

namespace Formalism.L2.SG.LemmaN

open NumberField IsDedekindDomain Ideal

abbrev OP (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Type :=
  P.adicCompletionIntegers E

def red {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ}
    (M : Matrix (Fin N) (Fin N) (OP E P)) :
    Matrix (Fin N) (Fin N) (IsLocalRing.ResidueField (OP E P)) :=
  M.map (IsLocalRing.residue (OP E P))

def Unram (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})], Q.ramificationIdx ℤ = 1

def LemmaNa : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → 3 ≤ p → Unram E p →
  ∀ (P : HeightOneSpectrum (𝓞 E)), (p : 𝓞 E) ∈ P.asIdeal →
  ∀ (N : ℕ) (β : GL (Fin N) (OP E P)), IsOfFinOrder β →
    red (β : Matrix (Fin N) (Fin N) (OP E P)) = 1 → β = 1

def LemmaNb : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → 3 ≤ p → Unram E p →
  ∀ (P : HeightOneSpectrum (𝓞 E)), (p : 𝓞 E) ∈ P.asIdeal →
  ∀ (N : ℕ) (β : GL (Fin N) (OP E P)), IsOfFinOrder β →
    IsNilpotent (red (β : Matrix (Fin N) (Fin N) (OP E P)) - 1) →
    ∃ t : ℕ, orderOf β = p ^ t

def IsProP (p : ℕ) (Q : Type) [Group Q] [TopologicalSpace Q] : Prop :=
  IsTopologicalGroup Q ∧ T2Space Q ∧ CompactSpace Q ∧ TotallyDisconnectedSpace Q ∧
    ∀ U : OpenNormalSubgroup Q, ∃ k : ℕ, (U.toOpenSubgroup : Subgroup Q).index = p ^ k

def LemmaNc : Prop :=
  ∀ (Γ : Type) [Group Γ] (β : Γ), IsOfFinOrder β →
  ∀ (g₁ g₂ : ℕ), g₁.Prime → g₂.Prime → g₁ ≠ g₂ → 3 ≤ g₁ → 3 ≤ g₂ →
  ∀ (Q₁ : Type) [Group Q₁] [TopologicalSpace Q₁], IsProP g₁ Q₁ →
  ∀ (Q₂ : Type) [Group Q₂] [TopologicalSpace Q₂], IsProP g₂ Q₂ →
  ∀ (f₁ : Γ →* Q₁) (f₂ : Γ →* Q₂), Function.Injective f₁ → Function.Injective f₂ →
    β = 1

def LemmaNcGlob : Prop :=
  ∀ (E V : Type) [Field E] [NumberField E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L : Submodule (𝓞 E) V),
    Submodule.IsLattice E L →
  ∀ (β : V ≃ₗ[E] V), IsOfFinOrder β →
  ∀ (g₁ g₂ : ℕ), g₁.Prime → g₂.Prime → g₁ ≠ g₂ → 3 ≤ g₁ → 3 ≤ g₂ →
    (∀ PP : Ideal (𝓞 E), PP.IsPrime → (g₁ : 𝓞 E) ∈ PP → Formalism.L2.Col.UnipMod PP L β) →
    (∀ PP : Ideal (𝓞 E), PP.IsPrime → (g₂ : 𝓞 E) ∈ PP → Formalism.L2.Col.UnipMod PP L β) →
    β = 1

theorem orderOf_dvd_of_isProP {p : ℕ} {Q : Type} [Group Q] [TopologicalSpace Q]
    (hQ : IsProP p Q) {y : Q} (hy : IsOfFinOrder y) : ∃ k : ℕ, orderOf y ∣ p ^ k := by
  obtain ⟨htg, ht2, hc, htd, hidx⟩ := hQ
  classical
  let S : Finset Q := ((Finset.range (orderOf y)).image (fun k => y ^ k)).filter (· ≠ 1)
  have hUo : IsOpen ((S : Set Q)ᶜ) := (S.finite_toSet.isClosed).isOpen_compl
  have h1U : (1 : Q) ∈ ((S : Set Q)ᶜ) := by simp [S]
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo h1U
  obtain ⟨k, hk⟩ := hidx H
  refine ⟨k, ?_⟩
  let Hs : Subgroup Q := (H.toOpenSubgroup : Subgroup Q)
  have : Hs.Normal := H.isNormal'
  have hdvd : orderOf (QuotientGroup.mk' Hs y) ∣ p ^ k := by
    rw [← hk, Subgroup.index]
    exact orderOf_dvd_natCard _
  refine dvd_trans (orderOf_dvd_of_pow_eq_one ?_) hdvd
  have hm : QuotientGroup.mk' Hs y ^ orderOf (QuotientGroup.mk' Hs y) = 1 := pow_orderOf_eq_one _
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm
  set m := orderOf (QuotientGroup.mk' Hs y)
  rw [← pow_mod_orderOf] at hm ⊢
  by_contra hne
  have hmem : y ^ (m % orderOf y) ∈ (S : Set Q) := by
    simp only [S, Finset.coe_filter, Finset.mem_image, Finset.mem_range, Set.mem_ofPred_eq]
    exact ⟨⟨m % orderOf y, Nat.mod_lt _ hy.orderOf_pos, rfl⟩, hne⟩
  exact hH hm hmem

theorem eq_one_of_dvd_two_primes {G : Type} [Group G] {β : G} {g₁ g₂ a b : ℕ}
    (hg₁ : g₁.Prime) (hg₂ : g₂.Prime) (hne : g₁ ≠ g₂)
    (ha : orderOf β ∣ g₁ ^ a) (hb : orderOf β ∣ g₂ ^ b) : β = 1 := by
  have hcop : Nat.Coprime (g₁ ^ a) (g₂ ^ b) := Nat.coprime_pow_primes a b hg₁ hg₂ hne
  have h1 : orderOf β = 1 := Nat.eq_one_of_dvd_coprimes hcop ha hb
  exact orderOf_eq_one_iff.mp h1

theorem lemmaNc : LemmaNc := by
  intro Γ _ β hfin g₁ g₂ hg₁ hg₂ hne _ _ Q₁ _ _ hQ₁ Q₂ _ _ hQ₂ f₁ f₂ i₁ i₂
  have hf₁ : IsOfFinOrder (f₁ β) := by
    rw [← orderOf_pos_iff, orderOf_injective f₁ i₁ β]; exact hfin.orderOf_pos
  have hf₂ : IsOfFinOrder (f₂ β) := by
    rw [← orderOf_pos_iff, orderOf_injective f₂ i₂ β]; exact hfin.orderOf_pos
  obtain ⟨a, ha⟩ := orderOf_dvd_of_isProP hQ₁ hf₁
  obtain ⟨b, hb⟩ := orderOf_dvd_of_isProP hQ₂ hf₂
  rw [orderOf_injective f₁ i₁ β] at ha
  rw [orderOf_injective f₂ i₂ β] at hb
  exact eq_one_of_dvd_two_primes hg₁ hg₂ hne ha hb

theorem exists_prime_over (E : Type) [Field E] [NumberField E] {g : ℕ} (hg : g.Prime) :
    ∃ PP : Ideal (𝓞 E), PP.IsPrime ∧ (g : 𝓞 E) ∈ PP := by
  have hP : (span {(g : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hg.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hg
  have hker : (⊥ : Ideal (𝓞 E)).comap (algebraMap ℤ (𝓞 E)) ≤ span {(g : ℤ)} := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot, eq_intCast, Int.cast_eq_zero] at hx
    simp [hx]
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (span {(g : ℤ)}) ⊥ hker
  refine ⟨Q, hQ, ?_⟩
  have : ((g : ℤ)) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by rw [hQc]; exact mem_span_singleton_self _
  simpa using this

theorem lemmaNcGlob_of_exists (E V : Type) [Field E] [NumberField E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L : Submodule (𝓞 E) V)
    (hL : Submodule.IsLattice E L) (β : V ≃ₗ[E] V) (hfin : IsOfFinOrder β)
    {g₁ g₂ : ℕ} (hg₁ : g₁.Prime) (hg₂ : g₂.Prime) (hne : g₁ ≠ g₂)
    {w₁ w₂ : Ideal (𝓞 E)} (hw₁ : w₁ ≠ ⊤) (hw₂ : w₂ ≠ ⊤) (hgw₁ : (g₁ : 𝓞 E) ∈ w₁)
    (hgw₂ : (g₂ : 𝓞 E) ∈ w₂) (h₁ : Formalism.L2.Col.UnipMod w₁ L β) (h₂ : Formalism.L2.Col.UnipMod w₂ L β) :
    β = 1 := by
  have : Module.IsTorsionFree (𝓞 E) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 E) E V
  obtain ⟨a, ha⟩ := h₁.exists_pow_eq_one hw₁ hL.fg hL.span_eq_top hg₁ hgw₁ hfin
  obtain ⟨b, hb⟩ := h₂.exists_pow_eq_one hw₂ hL.fg hL.span_eq_top hg₂ hgw₂ hfin
  exact eq_one_of_dvd_two_primes hg₁ hg₂ hne (orderOf_dvd_of_pow_eq_one ha)
    (orderOf_dvd_of_pow_eq_one hb)

theorem lemmaNcGlob : LemmaNcGlob := by
  intro E V _ _ _ _ _ _ _ L hL β hfin g₁ g₂ hg₁ hg₂ hne _ _ h₁ h₂
  obtain ⟨P₁, hP₁, hg₁P⟩ := exists_prime_over E hg₁
  obtain ⟨P₂, hP₂, hg₂P⟩ := exists_prime_over E hg₂
  exact lemmaNcGlob_of_exists E V L hL β hfin hg₁ hg₂ hne hP₁.ne_top hP₂.ne_top hg₁P hg₂P
    (h₁ P₁ hP₁ hg₁P) (h₂ P₂ hP₂ hg₂P)

theorem natCast_mem_maximalIdeal {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    {p : ℕ} (hp : (p : 𝓞 E) ∈ P.asIdeal) :
    ((p : ℕ) : OP E P) ∈ IsLocalRing.maximalIdeal (OP E P) := by
  have hv : Valued.v (((p : ℕ) : OP E P) : P.adicCompletion E) < 1 := by
    have h1 := P.valuedAdicCompletion_eq_valuation (K := E) ((p : ℕ) : 𝓞 E)
    have h2 := (P.valuation_lt_one_iff_mem (K := E) ((p : ℕ) : 𝓞 E)).mpr hp
    simp only [map_natCast] at h1 h2
    push_cast
    rw [h1]; exact h2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have hmul : ((u.val : OP E P) : P.adicCompletion E) * ((u.inv : OP E P) : P.adicCompletion E) = 1 := by
    have := congrArg (fun x : OP E P => (x : P.adicCompletion E)) u.val_inv
    push_cast at this
    exact this
  have hinv : Valued.v ((u.inv : OP E P) : P.adicCompletion E) ≤ 1 := u.inv.2
  rw [hu] at hmul
  have := congrArg Valued.v hmul
  rw [map_mul, map_one] at this
  have hlt := mul_lt_one_of_lt_of_le hv hinv
  rw [this] at hlt
  exact lt_irrefl _ hlt

theorem lemmaNb_of_lemmaNa (ha : LemmaNa) : LemmaNb := by
  intro E _ _ p hp h3 hun P hpP N β hfin hnil
  obtain ⟨r, hr⟩ := hnil
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    refine ⟨0, ?_⟩
    have : β = 1 := Subsingleton.elim _ _
    simp [this]
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  have hpK : ((p : ℕ) : IsLocalRing.ResidueField (OP E P)) = 0 := by
    rw [← map_natCast (IsLocalRing.residue (OP E P))]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (natCast_mem_maximalIdeal P hpP)
  have : CharP (IsLocalRing.ResidueField (OP E P)) p := (CharP.charP_iff_prime_eq_zero hp).mpr hpK
  set u := red (β : Matrix (Fin N) (Fin N) (OP E P)) with hu
  have hpow : u ^ p ^ r = 1 := by
    have h1 : (u - 1) ^ p ^ r = u ^ p ^ r - 1 := by
      rw [sub_pow_char_pow_of_commute _ _ (Commute.one_right u), one_pow]
    have h2 : (u - 1) ^ p ^ r = 0 := by
      have hle : r ≤ p ^ r := (Nat.lt_pow_self hp.one_lt).le
      rw [← Nat.add_sub_cancel' hle, pow_add, hr, zero_mul]
    rw [h2] at h1
    exact (sub_eq_zero.mp h1.symm)
  have hred : red ((β ^ p ^ r : GL (Fin N) (OP E P)) : Matrix (Fin N) (Fin N) (OP E P)) = 1 := by
    rw [← hpow, hu, Units.val_pow_eq_pow_val]
    exact map_pow ((IsLocalRing.residue (OP E P)).mapMatrix) _ _
  have h1 := ha E p hp h3 hun P hpP N (β ^ p ^ r) hfin.pow hred
  obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one h1)
  exact ⟨t, ht⟩

end Formalism.L2.SG.LemmaN
