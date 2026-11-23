import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaCharactersPowersOfOmegaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineOfInertiaTrivialOnCrystallinePeriodsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestric
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InerDecomp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobStableInertiaThrough
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaQlLeInertiaOfFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaConjMemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobInvMulMemInerStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.GoodLatt

theorem orbit_pow {G LL : Type} [Group G] [Field LL] (I : Subgroup G) (F : G) (P : G → Prop) (l : ℕ)
    (hI : ∀ g ∈ I, F⁻¹ * g * F ∈ I)
    (Sig : Finset (I →* LLˣ)) (hFS : FrobStable I F Sig)
    (hR : ∀ χ ∈ Sig, ∀ g h : I, P h → (g : G) = F⁻¹ * h * F → χ h = χ g ^ l)
    (χ : I →* LLˣ) (hχ : χ ∈ Sig) :
    (∀ n : ℕ, ∃ b ∈ Sig, ∀ g : I, P g → b g ^ (l ^ n) = χ g) ∧
      ∃ k, 1 ≤ k ∧ k ≤ Sig.card ∧ ∀ g : I, P g → χ g ^ (l ^ k) = χ g := by
  classical
  have hstep : ∀ a ∈ Sig, ∃ b ∈ Sig, ∀ g : I, P g → a g = b g ^ l := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hFS a ha
    refine ⟨b, hb, fun g hg => ?_⟩
    rw [hR a ha ⟨F⁻¹ * g * F, hI g g.2⟩ g hg rfl, hab g ⟨F⁻¹ * g * F, hI g g.2⟩ rfl]
  choose! τ hτS hτ using hstep
  let sq : ℕ → (I →* LLˣ) := fun n => τ^[n] χ
  have hsqS : ∀ n, sq n ∈ Sig := by
    intro n
    induction n with
    | zero => exact hχ
    | succ n ih =>
      simp only [sq, Function.iterate_succ_apply']
      exact hτS _ ih
  have hsq : ∀ n, ∀ g : I, P g → sq n g = sq (n + 1) g ^ l := by
    intro n g hg
    simp only [sq, Function.iterate_succ_apply']
    exact hτ _ (hsqS n) g hg
  have hpow : ∀ m n, ∀ g : I, P g → sq m g = sq (m + n) g ^ (l ^ n) := by
    intro m n g hg
    induction n with
    | zero => simp
    | succ n ih => rw [ih, hsq (m + n) g hg, ← pow_mul, ← pow_succ', ← add_assoc]
  have h0 : ∀ n, ∀ g : I, P g → χ g = sq n g ^ (l ^ n) := by
    intro n g hg
    have := hpow 0 n g hg
    simpa [sq] using this
  refine ⟨fun n => ⟨sq n, hsqS n, fun g hg => (h0 n g hg).symm⟩, ?_⟩
  have key : ∀ i j : ℕ, i < j → j ≤ Sig.card → sq i = sq j →
      ∃ k, 1 ≤ k ∧ k ≤ Sig.card ∧ ∀ g : I, P g → χ g ^ (l ^ k) = χ g := by
    intro i j hlt hj heq
    refine ⟨j - i, by omega, by omega, fun g hg => ?_⟩
    have h2 : sq i g = sq i g ^ (l ^ (j - i)) := by
      have := hpow i (j - i) g hg
      rwa [Nat.add_sub_cancel' hlt.le, ← heq] at this
    rw [h0 i g hg, ← pow_mul, mul_comm, pow_mul, ← h2]
  obtain ⟨i, -, j, -, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := (Finset.univ : Finset (Fin (Sig.card + 1)))) (t := Sig) (f := fun i => sq i)
    (by simp) (by intro i _; exact hsqS i)
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · exact key i j hlt (by omega) heq
  · exact key j i hlt (by omega) heq.symm

theorem sInf_eq_frobPeriod (l : ℕ) {e : ℕ} (d : ZMod e) (a : ℕ) (ha : 1 ≤ a)
    (hd : (l : ZMod e) ^ a * d = d) :
    sInf {k : ℕ | 1 ≤ k ∧ (l : ZMod e) ^ k * d = d} = frobPeriod l d := by
  have hit : ∀ k, (fun x : ZMod e => (l : ZMod e) * x)^[k] d = (l : ZMod e) ^ k * d := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ih, pow_succ', mul_assoc]
  have hper : ∀ k, Function.IsPeriodicPt (fun x : ZMod e => (l : ZMod e) * x) k d ↔
      (l : ZMod e) ^ k * d = d := by
    intro k
    rw [Function.IsPeriodicPt, Function.IsFixedPt, hit]
  have hmem : d ∈ Function.periodicPts (fun x : ZMod e => (l : ZMod e) * x) :=
    ⟨a, ha, (hper a).2 hd⟩
  have hne : {k : ℕ | 1 ≤ k ∧ (l : ZMod e) ^ k * d = d}.Nonempty := ⟨a, ha, hd⟩
  change _ = Function.minimalPeriod (fun x : ZMod e => (l : ZMod e) * x) d
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨Function.minimalPeriod_pos_of_mem_periodicPts hmem,
      (hper _).1 (Function.isPeriodicPt_minimalPeriod _ _)⟩
  · obtain ⟨h1, h2⟩ := Nat.sInf_mem hne
    exact Function.IsPeriodicPt.minimalPeriod_le h1 ((hper _).2 h2)

theorem pow_val_natCast {M : Type} [Monoid M] {e : ℕ} [NeZero e] (w : M) (hw : w ^ e = 1) (n : ℕ) :
    w ^ ((n : ZMod e).val) = w ^ n := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod n e, pow_add, pow_mul, hw, one_pow, one_mul]

theorem pow_val_add {M : Type} [Monoid M] {e : ℕ} [NeZero e] (w : M) (hw : w ^ e = 1) (x y : ZMod e) :
    w ^ (x + y).val = w ^ x.val * w ^ y.val := by
  have : x + y = ((x.val + y.val : ℕ) : ZMod e) := by simp
  rw [this, pow_val_natCast w hw, pow_add]

theorem pow_val_mul_pow {M : Type} [Monoid M] {e : ℕ} [NeZero e] (w : M) (hw : w ^ e = 1) (l k : ℕ)
    (x : ZMod e) : w ^ ((l : ZMod e) ^ k * x).val = (w ^ x.val) ^ (l ^ k) := by
  have : (l : ZMod e) ^ k * x = ((x.val * l ^ k : ℕ) : ZMod e) := by simp [mul_comm]
  rw [this, pow_val_natCast w hw, pow_mul]

theorem zmod_eq_of_pow {M : Type} [CommMonoid M] {e : ℕ} [NeZero e] {w : M} (hw : IsPrimitiveRoot w e)
    {c d : ZMod e} (h : w ^ c.val = w ^ d.val) : c = d :=
  ZMod.val_injective e (hw.pow_inj (ZMod.val_lt c) (ZMod.val_lt d) h)

theorem chars_main {G LL : Type} [Group G] [Field LL] (I IK H : Subgroup G) (W : G → LL → Prop)
    (l a e N : ℕ) [NeZero e] (Fr : G) (Sig : Finset (I →* LLˣ))
    (ha1 : 1 ≤ a) (hka : ∀ k, 1 ≤ k → k ≤ N → k ∣ a) (he1 : e + 1 = l ^ a)
    (hIK : IK ≤ I) (hHn : H.Normal) (hI : ∀ (F g : G), g ∈ I → F⁻¹ * g * F ∈ I)
    (hIKc : ∀ (τ g : G), g ∈ IK → τ⁻¹ * g * τ ∈ IK)
    (hdec : ∀ g ∈ I, ∃ s ∈ IK, s⁻¹ * g ∈ H)
    (hFS : FrobStable I Fr Sig) (h1 : 1 ∈ Sig) (hcard : Sig.card ≤ N)
    (hH : ∀ χ ∈ Sig, ∀ g : I, (g : G) ∈ H → χ g = 1)
    (hR : ∀ χ ∈ Sig, ∀ g h : I, (h : G) ∈ IK → (g : G) = Fr⁻¹ * h * Fr → χ h = χ g ^ l)
    (hw1 : ∀ g ∈ IK, ∃ w, W g w ∧ w ^ e = 1)
    (g0 : G) (hg0 : g0 ∈ IK) (w0 : LL) (hw0 : W g0 w0) (hprim : IsPrimitiveRoot w0 e)
    (hcx : ∀ χ ∈ Sig, (∀ g : I, (g : G) ∈ IK → χ g ^ e = 1) →
      ∃ c : ZMod e, ∀ g : I, (g : G) ∈ IK → ∀ w, W g w → ((χ g : LLˣ) : LL) = w ^ c.val) :
    ∃ Sig' : Finset (ZMod e), (∀ c ∈ Sig', (l : ZMod e) * c ∈ Sig') ∧ (0 : ZMod e) ∈ Sig' ∧
      Sig'.card ≤ N ∧ maxPeriod l Sig' = Formalism.MainNotions.ElementDenominator.rPrime I Fr Sig ∧
      ∀ χ ∈ Sig, ∃ c ∈ Sig', ∀ g : I, (g : G) ∈ IK → ∀ w, W g w → ((χ g : LLˣ) : LL) = w ^ c.val := by
  classical
  have horb : ∀ χ ∈ Sig, (∀ n : ℕ, ∃ b ∈ Sig, ∀ g : I, (g : G) ∈ IK → b g ^ (l ^ n) = χ g) ∧
      ∃ k, 1 ≤ k ∧ k ≤ Sig.card ∧ ∀ g : I, (g : G) ∈ IK → χ g ^ (l ^ k) = χ g :=
    fun χ hχ => orbit_pow I Fr (fun g => g ∈ IK) l (fun g hg => hI Fr g hg) Sig hFS hR χ hχ
  have hla : ∀ χ ∈ Sig, ∀ g : I, (g : G) ∈ IK → χ g ^ (l ^ a) = χ g := by
    intro χ hχ g hg
    obtain ⟨k, hk1, hkc, hk⟩ := (horb χ hχ).2
    obtain ⟨m, hm⟩ := hka k hk1 (hkc.trans hcard)
    rw [hm]
    clear hm
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hk g hg]
  have hre : ∀ χ ∈ Sig, ∀ g : I, (g : G) ∈ IK → χ g ^ e = 1 := by
    intro χ hχ g hg
    have := hla χ hχ g hg
    rw [← he1, pow_succ] at this
    exact mul_right_cancel (b := χ g) (by rw [one_mul]; exact this)
  have hc : ∀ χ ∈ Sig, ∃ c : ZMod e, ∀ g : I, (g : G) ∈ IK → ∀ w, W g w → ((χ g : LLˣ) : LL) = w ^ c.val :=
    fun χ hχ => hcx χ hχ (hre χ hχ)
  choose! cOf hcOf using hc
  let g0I : I := ⟨g0, hIK hg0⟩
  have hv0 : ∀ χ ∈ Sig, ((χ g0I : LLˣ) : LL) = w0 ^ (cOf χ).val :=
    fun χ hχ => hcOf χ hχ g0I hg0 w0 hw0
  have hw0e : w0 ^ e = 1 := hprim.pow_eq_one
  have hc1 : cOf 1 = 0 := by
    have := hv0 1 h1
    rw [MonoidHom.one_apply, Units.val_one] at this
    exact zmod_eq_of_pow hprim (by rw [← this, ZMod.val_zero, pow_zero])
  have hlst : ∀ χ ∈ Sig, ∃ b ∈ Sig, cOf b = (l : ZMod e) * cOf χ := by
    intro χ hχ
    obtain ⟨b, hb, hbχ⟩ := (horb χ hχ).1 (a - 1)
    refine ⟨b, hb, ?_⟩
    have ha1' : a - 1 + 1 = a := Nat.sub_add_cancel ha1
    have e1 : b g0I = χ g0I ^ l := by
      rw [← hbχ g0I hg0, ← pow_mul, ← pow_succ, ha1', hla b hb g0I hg0]
    have e2 := congrArg (fun u : LLˣ => (u : LL)) e1
    simp only [Units.val_pow_eq_pow_val] at e2
    rw [hv0 b hb, hv0 χ hχ] at e2
    have e3 : (l : ZMod e) * cOf χ = (l : ZMod e) ^ 1 * cOf χ := by rw [pow_one]
    rw [e3]
    exact zmod_eq_of_pow hprim (by rw [e2, pow_val_mul_pow w0 hw0e, pow_one])
  have hψ : ∀ χ₁ ∈ Sig, ∀ χ₂ ∈ Sig, ∀ g : I, (g : G) ∈ IK → ∀ w, W g w → w ^ e = 1 →
      (((χ₁ * χ₂⁻¹) g : LLˣ) : LL) = w ^ (cOf χ₁ - cOf χ₂).val := by
    intro χ₁ h₁ χ₂ h₂ g hg w hw hwe
    have hwne : w ≠ 0 := by
      rintro rfl
      rw [zero_pow (NeZero.ne e)] at hwe
      exact zero_ne_one hwe
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
      hcOf χ₁ h₁ g hg w hw, hcOf χ₂ h₂ g hg w hw]
    conv_lhs => rw [← sub_add_cancel (cOf χ₁) (cOf χ₂), pow_val_add w hwe]
    rw [mul_inv_cancel_right₀ (pow_ne_zero _ hwne)]
  have hsub : ∀ (k : ℕ) (g : G), g ∈ I → (Fr ^ k)⁻¹ * g * Fr ^ k ∈ I := fun k g hg => hI (Fr ^ k) g hg
  have hOrb : ∀ χ₁ ∈ Sig, ∀ χ₂ ∈ Sig,
      Formalism.MainNotions.ElementDenominator.orbLen I Fr (χ₁ * χ₂⁻¹) = frobPeriod l (cOf χ₁ - cOf χ₂) := by
    intro χ₁ h₁ χ₂ h₂
    have hRψ : ∀ g h : I, (h : G) ∈ IK → (g : G) = Fr⁻¹ * h * Fr →
        (χ₁ * χ₂⁻¹) h = (χ₁ * χ₂⁻¹) g ^ l := by
      intro g h hh hg
      rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.inv_apply,
        hR χ₁ h₁ g h hh hg, hR χ₂ h₂ g h hh hg, mul_pow, inv_pow]
    have hHψ : ∀ g : I, (g : G) ∈ H → (χ₁ * χ₂⁻¹) g = 1 := by
      intro g hg
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hH χ₁ h₁ g hg, hH χ₂ h₂ g hg, inv_one, mul_one]
    have hiter : ∀ (k : ℕ) (g : I), (g : G) ∈ IK →
        (χ₁ * χ₂⁻¹) g = (χ₁ * χ₂⁻¹) ⟨(Fr ^ k)⁻¹ * g * Fr ^ k, hsub k g g.2⟩ ^ (l ^ k) := by
      intro k
      induction k with
      | zero =>
        intro g hg
        have h0 : l ^ 0 = 1 := pow_zero l
        rw [h0, pow_one]
        congr 1
        apply Subtype.ext
        simp
      | succ k ih =>
        intro g hg
        rw [ih g hg, hRψ ⟨(Fr ^ (k + 1))⁻¹ * g * Fr ^ (k + 1), hsub (k + 1) g g.2⟩
          ⟨(Fr ^ k)⁻¹ * g * Fr ^ k, hsub k g g.2⟩ (hIKc (Fr ^ k) g hg)
          (by show (Fr ^ (k + 1))⁻¹ * (g : G) * Fr ^ (k + 1) = Fr⁻¹ * ((Fr ^ k)⁻¹ * (g : G) * Fr ^ k) * Fr
              rw [pow_succ]; group), ← pow_mul, ← pow_succ']
    have hQ : ∀ k, 1 ≤ k → ((∀ g h : I, (h : G) = (Fr ^ k)⁻¹ * g * Fr ^ k →
        (χ₁ * χ₂⁻¹) h = (χ₁ * χ₂⁻¹) g) ↔ (l : ZMod e) ^ k * (cOf χ₁ - cOf χ₂) = cOf χ₁ - cOf χ₂) := by
      intro k hk
      constructor
      · intro hq
        have e1 := hq g0I ⟨(Fr ^ k)⁻¹ * g0 * Fr ^ k, hsub k g0 g0I.2⟩ rfl
        have e2 := hiter k g0I hg0
        rw [e1] at e2
        have e3 := congrArg (fun u : LLˣ => (u : LL)) e2
        simp only [Units.val_pow_eq_pow_val] at e3
        rw [hψ χ₁ h₁ χ₂ h₂ g0I hg0 w0 hw0 hw0e] at e3
        exact zmod_eq_of_pow hprim (by rw [pow_val_mul_pow w0 hw0e, ← e3])
      · intro hdk g h hh
        obtain ⟨s, hs, hsu⟩ := hdec g g.2
        let sI : I := ⟨s, hIK hs⟩
        let uI : I := ⟨s⁻¹ * g, I.mul_mem (I.inv_mem (hIK hs)) g.2⟩
        have hg : g = sI * uI := by
          apply Subtype.ext
          show (g : G) = s * (s⁻¹ * g)
          group
        have hu : (χ₁ * χ₂⁻¹) uI = 1 := hHψ uI hsu
        let sk : I := ⟨(Fr ^ k)⁻¹ * s * Fr ^ k, hsub k s (hIK hs)⟩
        let uk : I := ⟨(Fr ^ k)⁻¹ * (s⁻¹ * g) * Fr ^ k, hsub k _ uI.2⟩
        have hh' : h = sk * uk := by
          apply Subtype.ext
          show (h : G) = ((Fr ^ k)⁻¹ * s * Fr ^ k) * ((Fr ^ k)⁻¹ * (s⁻¹ * (g : G)) * Fr ^ k)
          rw [hh]
          group
        have huk : (χ₁ * χ₂⁻¹) uk = 1 := hHψ uk (by
          have := hHn.conj_mem _ hsu (Fr ^ k)⁻¹
          rw [inv_inv] at this
          exact this)
        have hskIK : (sk : G) ∈ IK := hIKc (Fr ^ k) s hs
        have hsk : (χ₁ * χ₂⁻¹) sI = (χ₁ * χ₂⁻¹) sk := by
          rw [hiter k sI hs]
          show (χ₁ * χ₂⁻¹) sk ^ (l ^ k) = (χ₁ * χ₂⁻¹) sk
          obtain ⟨w, hw, hwe⟩ := hw1 _ hskIK
          apply Units.ext
          rw [Units.val_pow_eq_pow_val, hψ χ₁ h₁ χ₂ h₂ sk hskIK w hw hwe, ← pow_val_mul_pow w hwe, hdk]
        rw [hh', hg, map_mul, map_mul, hu, huk, mul_one, mul_one, hsk]
    have hset : {k : ℕ | 1 ≤ k ∧ ∀ g h : I, (h : G) = (Fr ^ k)⁻¹ * g * Fr ^ k →
        (χ₁ * χ₂⁻¹) h = (χ₁ * χ₂⁻¹) g} =
        {k | 1 ≤ k ∧ (l : ZMod e) ^ k * (cOf χ₁ - cOf χ₂) = cOf χ₁ - cOf χ₂} := by
      ext k
      constructor
      · rintro ⟨hk, hq⟩
        exact ⟨hk, (hQ k hk).1 hq⟩
      · rintro ⟨hk, hq⟩
        exact ⟨hk, (hQ k hk).2 hq⟩
    have hla' : (l : ZMod e) ^ a = 1 := by
      have : ((l ^ a : ℕ) : ZMod e) = 1 := by rw [← he1]; simp
      exact_mod_cast this
    unfold Formalism.MainNotions.ElementDenominator.orbLen
    rw [hset]
    exact sInf_eq_frobPeriod l _ a ha1 (by rw [hla', one_mul])
  refine ⟨Sig.image cOf, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨b, hb, hbc⟩ := hlst χ hχ
    exact Finset.mem_image.2 ⟨b, hb, hbc⟩
  · exact Finset.mem_image.2 ⟨1, h1, hc1⟩
  · exact Finset.card_image_le.trans hcard
  · unfold maxPeriod Formalism.MainNotions.ElementDenominator.rPrime
    apply le_antisymm
    · apply Finset.sup_le
      rintro ⟨c₁, c₂⟩ hp
      obtain ⟨hc₁, hc₂⟩ := Finset.mem_product.1 hp
      obtain ⟨χ₁, h₁, rfl⟩ := Finset.mem_image.1 hc₁
      obtain ⟨χ₂, h₂, rfl⟩ := Finset.mem_image.1 hc₂
      show frobPeriod l (cOf χ₁ - cOf χ₂) ≤ _
      rw [← hOrb χ₁ h₁ χ₂ h₂]
      exact Finset.le_sup (f := fun p : (I →* LLˣ) × (I →* LLˣ) => Formalism.MainNotions.ElementDenominator.orbLen I Fr (p.1 * p.2⁻¹))
        (Finset.mem_product.2 ⟨h₁, h₂⟩ : (χ₁, χ₂) ∈ Sig ×ˢ Sig)
    · apply Finset.sup_le
      rintro ⟨χ₁, χ₂⟩ hp
      obtain ⟨h₁, h₂⟩ := Finset.mem_product.1 hp
      simp only at h₁ h₂
      show Formalism.MainNotions.ElementDenominator.orbLen I Fr (χ₁ * χ₂⁻¹) ≤ _
      rw [hOrb χ₁ h₁ χ₂ h₂]
      exact Finset.le_sup (f := fun p : ZMod e × ZMod e => frobPeriod l (p.1 - p.2))
        (Finset.mem_product.2 ⟨Finset.mem_image_of_mem cOf h₁, Finset.mem_image_of_mem cOf h₂⟩ :
          (cOf χ₁, cOf χ₂) ∈ Sig.image cOf ×ˢ Sig.image cOf)
  · intro χ hχ
    exact ⟨cOf χ, Finset.mem_image_of_mem _ hχ, hcOf χ hχ⟩

section Ann

variable {G : Type} {i1 : Group G} {Qp K₀ K K₀' K' : Type} {i2 : Field Qp} {i3 : Field K₀} {i4 : Field K}
    {i5 : Field K₀'} {i6 : Field K'}
    {i7 : Algebra Qp K₀} {i8 : Algebra Qp K} {i9 : Algebra K₀ K} {i10 : IsScalarTower Qp K₀ K}
    {i11 : Algebra Qp K₀'} {i12 : Algebra Qp K'} {i13 : Algebra K₀' K'} {i14 : IsScalarTower Qp K₀' K'}
    {B BdR : Type} {i15 : CommRing B} {i16 : CommRing BdR} {i17 : Algebra Qp B} {i18 : Algebra K₀ B} {i19 : IsScalarTower Qp K₀ B}
    {i20 : Algebra K₀' B} {i21 : IsScalarTower Qp K₀' B}
    {i22 : Algebra Qp BdR} {i23 : Algebra K₀ BdR} {i24 : Algebra K BdR} {i25 : IsScalarTower Qp K BdR}
    {i26 : IsScalarTower K₀ K BdR} {i27 : IsScalarTower Qp K₀ BdR}
    {i28 : Algebra K₀' BdR} {i29 : Algebra K' BdR} {i30 : IsScalarTower Qp K' BdR}
    {i31 : IsScalarTower K₀' K' BdR} {i32 : IsScalarTower Qp K₀' BdR}
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} {i33 : Field LL} {i34 : Algebra Qp LL}
    {V : Type} {i35 : AddCommGroup V} {i36 : Module LL V} {i37 : Module Qp V} {i38 : IsScalarTower Qp LL V}

theorem dpcris_ann (ρ : Representation LL G V) (Sig : Finset (PC.Iner →* LLˣ))
    (hT : PC.InertiaThrough ρ Sig) (g : PC.Iner) (p : Polynomial LL)
    (hp : ∀ χ ∈ Sig, p.IsRoot ((χ g : LLˣ) : LL)) :
    ∀ x ∈ PC.Dpcris ρ, Polynomial.aeval (actVB PC.PD ρ (g : G)) p x = 0 := by
  intro x hx
  rw [hT.2.2] at hx
  have hle : (⨆ a ∈ Sig, PC.Eig ρ PC.Iner a) ≤
      LinearMap.ker (Polynomial.aeval (actVB PC.PD ρ (g : G)) p) := by
    refine iSup₂_le fun χ hχ y hy => ?_
    rw [LinearMap.mem_ker]
    have hy' := ((GlobalTheory.inertialEig_mem_iff PC ρ PC.Iner χ y).1 hy).2 g
    by_cases hy0 : y = 0
    · rw [hy0, map_zero]
    · have hev : Module.End.HasEigenvector (actVB PC.PD ρ (g : G)) ((χ g : LLˣ) : LL) y :=
        Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hy', hy0⟩
      rw [Module.End.aeval_apply_of_hasEigenvector hev, (hp χ hχ).eq_zero, zero_smul]
  exact hle hx

end Ann

end GlobalTheory.GoodLatt

open GlobalTheory.GoodLatt in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.GoodLatt.main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → a = (l - 1).factorial → ∀ (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (Sig : Finset ((pc Pl h hN hF hS).Iner →* (↥LL.1)ˣ)) (Fr : Gl l) (N : ℕ), (pc Pl h hN hF hS).IsFrob Fr → FrobStable (pc Pl h hN hF hS).Iner Fr Sig → 1 ∈ Sig → Sig.card ≤ N → N < l → (∀ χ ∈ Sig, ∀ g : (pc Pl h hN hF hS).Iner, (g : Gl l) ∈ (pc Pl h hN hF hS).H → χ g = 1) → (∀ χ ∈ Sig, Nat.Coprime (orderOf χ) l) → ∃ Sig' : Finset (ZMod e), (∀ c ∈ Sig', (l : ZMod e) * c ∈ Sig') ∧ (0 : ZMod e) ∈ Sig' ∧ Sig'.card ≤ N ∧ maxPeriod l Sig' = Formalism.MainNotions.ElementDenominator.rPrime (pc Pl h hN hF hS).Iner Fr Sig ∧ ∀ T : QLat LL, (pc Pl h hN hF hS).IsPotCrys T.ρ → (pc Pl h hN hF hS).InertiaThrough T.ρ Sig → IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ ∧ TameType a ϖ Pl T Sig' := by
  intro hB l _ a e _ _ ϖ LL _ _ Pl AI hStd ha K' h hN hF hS Sig Fr N hFr hFS h1 hcard hNl hH hcop
  classical
  obtain ⟨hw1, ⟨g0, hg0, w0, hw0, hprim⟩, hchar⟩ := GlobalTheory.T.tame_inertia_characters_powers_of_omega l a e ϖ LL
  have hIK : IK (Formalism.MainNotions.ElementDenominator.qlExt l) ≤ (pc Pl h hN hF hS).Iner := fun g hg => GlobalTheory.T.inertia_Ql_le_inertia_of_finite_extension l Pl K' h hN hF hS g hg
  let res : ((pc Pl h hN hF hS).Iner →* (↥LL.1)ˣ) → (↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ) :=
    fun χ => χ.comp (Subgroup.inclusion hIK)
  have hres : ∀ χ (g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))), res χ g = χ ⟨g, hIK g.2⟩ := fun _ _ => rfl
  obtain ⟨Φ, hΦ, hj⟩ := GlobalTheory.T.exists_frob_inv_mul_mem_inertia l Pl AI hStd K' h hN hF hS Fr hFr
  have hopen : ∀ χ ∈ Sig, IsOpen ((res χ).ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) := by
    intro χ hχ
    have hK'open : IsOpen ((GK K' : Subgroup (GQ l)) : Set (GQ l)) := by
      haveI : FiniteDimensional ℚ_[l] K'.1 := K'.2
      exact IntermediateField.fixingSubgroup_isOpen K'.1
    refine Subgroup.isOpen_mono (H₁ := (GK K').comap
      ((GK (Formalism.MainNotions.ElementDenominator.qlExt l)).subtype.comp (IK (Formalism.MainNotions.ElementDenominator.qlExt l)).subtype)) ?_ ?_
    · intro x hx
      rw [MonoidHom.mem_ker, hres]
      exact hH χ hχ _ hx
    · exact hK'open.preimage (continuous_subtype_val.comp continuous_subtype_val)
  have hcop' : ∀ χ ∈ Sig, Nat.Coprime (orderOf (res χ)) l := by
    intro χ hχ
    refine Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one ?_) (hcop χ hχ)
    ext g
    have h2 : (χ ^ orderOf χ) ⟨g, hIK g.2⟩ = 1 := by rw [pow_orderOf_eq_one]; rfl
    rw [MonoidHom.pow_apply] at h2
    rw [MonoidHom.pow_apply, hres, h2]
    rfl

  have hR : ∀ χ ∈ Sig, ∀ g h' : (pc Pl h hN hF hS).Iner, (h' : Gl l) ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) →
      (g : Gl l) = Fr⁻¹ * h' * Fr → χ h' = χ g ^ l := by
    intro χ hχ g h' hh' hg
    have hg' : Φ⁻¹ * (h' : Gl l) * Φ ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) := GlobalTheory.T.conj_mem_inertia_of_mem l _ Φ hh'
    have key : χ h' = χ ⟨Φ⁻¹ * (h' : Gl l) * Φ, hIK hg'⟩ ^ l :=
      (hchar (res χ) (hopen χ hχ) (hcop' χ hχ)).1 Φ hΦ ⟨_, hg'⟩ ⟨h', hh'⟩ rfl
    let j : (pc Pl h hN hF hS).Iner := ⟨Φ⁻¹ * Fr, hj⟩
    have e2 : (⟨Φ⁻¹ * (h' : Gl l) * Φ, hIK hg'⟩ : (pc Pl h hN hF hS).Iner) = j * g * j⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, j]
      rw [hg]
      group
    rw [e2, map_mul, map_mul, map_inv, mul_comm (χ j) (χ g), mul_inv_cancel_right] at key
    exact key

  have hcx : ∀ χ ∈ Sig, (∀ g : (pc Pl h hN hF hS).Iner, (g : Gl l) ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → χ g ^ e = 1) →
      ∃ c : ZMod e, ∀ g : (pc Pl h hN hF hS).Iner, (g : Gl l) ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → ∀ w : ↥LL.1,
        (w : Om l) * ϖ.seq 0 = ((g : Gl l) : GQ l) (ϖ.seq 0) → ((χ g : (↥LL.1)ˣ) : ↥LL.1) = w ^ c.val := by
    intro χ hχ hχe
    have hre : res χ ^ e = 1 := by
      ext g
      rw [MonoidHom.pow_apply, hres, hχe ⟨g, hIK g.2⟩ g.2]
      rfl
    obtain ⟨c, hc⟩ := (hchar (res χ) (hopen χ hχ) (hcop' χ hχ)).2 hre
    exact ⟨c, fun g hg w hw => hc ⟨g, hg⟩ w hw⟩
  have he1 : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := ↥LL.1) (l := l) (e := e) (a := a)
  have hka : ∀ k, 1 ≤ k → k ≤ N → k ∣ a := by
    intro k hk1 hkN
    rw [ha]
    exact Nat.dvd_factorial hk1 (by omega)
  obtain ⟨Sig', hl, h0, hc, hmax, hSig⟩ := chars_main (pc Pl h hN hF hS).Iner (IK (Formalism.MainNotions.ElementDenominator.qlExt l)) (pc Pl h hN hF hS).H
    (fun g (w : ↥LL.1) => (w : Om l) * ϖ.seq 0 = ((g : Gl l) : GQ l) (ϖ.seq 0)) l a e N Fr Sig
    (Nat.one_le_iff_ne_zero.2 (NeZero.ne a)) hka he1 hIK (pc Pl h hN hF hS).normal
    (fun F g hg => GlobalTheory.conj_mem_Iner _ F g hg) (fun τ g hg => GlobalTheory.T.conj_mem_inertia_of_mem l g τ hg)
    (fun g hg => GlobalTheory.InertiaDecomp.iner_decomp l Pl _ K' h hN hF hS g hg)
    hFS h1 hcard hH hR hw1 g0 hg0 w0 hw0 hprim hcx
  refine ⟨Sig', hl, h0, hc, hmax, ?_⟩
  intro T hpot hthr
  have hPR := GlobalTheory.PcRes.main l Pl (Formalism.MainNotions.ElementDenominator.qlExt l) K' LL h hN hF hS T.V T.ρ
  have hcrys : IsCrys (Pl.PD K') (resF T K').ρ := hPR.2.1 hpot
  have hD : ∀ x ∈ Dcris (Pl.PD K') (resF T K').ρ, x ∈ (pc Pl h hN hF hS).Dpcris T.ρ := by
    intro x hx
    have hx' : x ∈ Dcris (Pl.PD K') (T.ρ.comp (Subgroup.inclusion (GK_le h))) := hx
    exact hPR.1.ge hx'
  have hNK' : (GK K').Normal := by
    constructor
    intro n hn g
    have hmem : ∀ g' : GQ l, g' ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
      intro g'
      show g' ∈ (⊥ : IntermediateField ℚ_[l] (Om l)).fixingSubgroup
      rw [IntermediateField.mem_fixingSubgroup_iff]
      rintro x hx
      obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.1 hx
      exact g'.commutes c
    have := hN.conj_mem ⟨n, hmem n⟩ (by rw [GKin, Subgroup.mem_subgroupOf]; exact hn) ⟨g, hmem g⟩
    rw [GKin, Subgroup.mem_subgroupOf] at this
    exact this
  obtain ⟨hI1, hI2⟩ := GlobalTheory.T.crystalline_of_inertia_trivial_on_crystallinePeriods hB l LL Pl AI hStd K' (ϖ.field a) hNK' T hcrys
  refine ⟨hI1 ?_, ?_⟩
  · intro g hg hgF x hx
    have hA := dpcris_ann _ _ _ hthr ⟨g, hIK hg⟩ (Polynomial.X - Polynomial.C 1) ?_ x (hD x hx)
    · simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_one] at hA
      have h2 : actVB (pc Pl h hN hF hS).PD T.ρ g (@id (T.V ⊗[ℚ_[l]] Pl.R.B) x) -
          @id (T.V ⊗[ℚ_[l]] Pl.R.B) x = 0 := hA
      exact sub_eq_zero.1 h2
    · intro χ hχ
      obtain ⟨c, -, hcχ⟩ := hSig χ hχ
      have h1' := hcχ ⟨g, hIK hg⟩ hg 1 (by simpa using (ϖ.gal_pi a ⟨g, hgF⟩).symm)
      rw [one_pow] at h1'
      rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, h1', sub_self]
  · intro g hg w hw
    apply hI2 g hg
    intro x hx
    apply dpcris_ann _ _ _ hthr ⟨g, hIK hg⟩ _ _ x (hD x hx)
    intro χ hχ
    obtain ⟨c, hc', hcχ⟩ := hSig χ hχ
    rw [hcχ ⟨g, hIK hg⟩ hg w hw, Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero hc' (by simp)
