import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO

noncomputable section

namespace Formalism.MainNotions.PairedCharacterCondition.RT

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Polynomial CategoryTheory Formalism.MainNotions.PairedCharacterCondition

section Reps

open Formalism.IrreducibleCountingLemmas.TYPES (RepIso)

variable {Γ : Type} [Group Γ]

variable {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem repIso_symm {ρ : Representation ℂ Γ V} {ρ' : Representation ℂ Γ W} (h : RepIso ρ ρ') :
    RepIso ρ' ρ := by
  unfold Formalism.IrreducibleCountingLemmas.TYPES.RepIso at h ⊢
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun γ w => ?_⟩
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

theorem repIso_trans {ρ : Representation ℂ Γ V} {ρ' : Representation ℂ Γ W}
    {ρ'' : Representation ℂ Γ U} (h : RepIso ρ ρ') (h' : RepIso ρ' ρ'') : RepIso ρ ρ'' := by
  unfold Formalism.IrreducibleCountingLemmas.TYPES.RepIso at h h' ⊢
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun γ v => by rw [LinearEquiv.trans_apply, he, he', LinearEquiv.trans_apply]⟩

theorem isConstituent_of_repIso {τ : FDRep ℂ Γ} {ρ : Representation ℂ Γ V}
    {ρ' : Representation ℂ Γ W} (h : Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ ρ) (hi : RepIso ρ ρ') :
    Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ ρ' := by
  unfold Formalism.IrreducibleCountingLemmas.TYPES.RepIso at hi
  unfold Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent at h ⊢
  obtain ⟨e, he⟩ := hi
  obtain ⟨φ, hφ, hne⟩ := h
  refine ⟨e.toLinearMap ∘ₗ φ, ?_, ?_⟩
  · intro γ
    have h1 : φ ∘ₗ τ.ρ γ = ρ γ ∘ₗ φ := hφ γ
    ext x
    have h2 := LinearMap.congr_fun h1 x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h2 ⊢
    rw [h2, he]
  · intro h0
    apply hne
    ext x
    have h3 := LinearMap.congr_fun h0 x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.zero_apply] at h3 ⊢
    exact (LinearEquiv.map_eq_zero_iff e).1 h3

end Reps

section Blocks

open Formalism.IrreducibleCountingLemmas.TYPES

theorem twoBlock_eq_zero {n a : ℕ} (i : Fin n) : twoBlock n a i = 0 ↔ (i : ℕ) < a := by
  simp only [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩

theorem twoBlock_eq_one {n a : ℕ} (i : Fin n) : twoBlock n a i = 1 ↔ a ≤ (i : ℕ) := by
  simp only [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock]
  split_ifs with h
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h (by omega)⟩
  · exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem twoBlock_surj {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Function.Surjective (twoBlock (a + b) a) := by
  intro c
  fin_cases c
  · exact ⟨⟨0, by omega⟩, (twoBlock_eq_zero _).2 ha⟩
  · exact ⟨⟨a, by omega⟩, (twoBlock_eq_one _).2 (le_refl a)⟩

def blk0 (a b : ℕ) : {i : Fin (a + b) // twoBlock (a + b) a i = 0} ≃ Fin a where
  toFun i := ⟨i.1, (twoBlock_eq_zero i.1).1 i.2⟩
  invFun j := ⟨⟨j, by omega⟩, (twoBlock_eq_zero _).2 j.2⟩
  left_inv i := by rcases i with ⟨⟨i, hi⟩, h⟩; rfl
  right_inv j := by rcases j with ⟨j, hj⟩; rfl

def blk1 (a b : ℕ) : {i : Fin (a + b) // twoBlock (a + b) a i = 1} ≃ Fin b where
  toFun i := ⟨i.1 - a, by have := (twoBlock_eq_one i.1).1 i.2; have := i.1.2; omega⟩
  invFun j := ⟨⟨a + j, by omega⟩, (twoBlock_eq_one _).2 (by simp)⟩
  left_inv i := by
    rcases i with ⟨⟨i, hi⟩, h⟩
    have hai : a ≤ i := (twoBlock_eq_one _).1 h
    apply Subtype.ext
    apply Fin.ext
    show a + (i - a) = i
    omega
  right_inv j := by
    rcases j with ⟨j, hj⟩
    apply Fin.ext
    simp

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def pairRep {a b : ℕ} (ρ : FDRep ℂ (GL (Fin a) K)) (ρ' : FDRep ℂ (GL (Fin b) K)) :
    ∀ c : Fin 2, FDRep ℂ (GL {i : Fin (a + b) // twoBlock (a + b) a i = c} K)
  | 0 => transp (blk0 a b).symm ρ
  | 1 => transp (blk1 a b).symm ρ'

theorem repIso_of_transp {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) {ρ ρ' : FDRep ℂ (GL ι K)} (h : RepIso (transp e ρ).ρ (transp e ρ').ρ) :
    RepIso ρ.ρ ρ'.ρ := by
  unfold Formalism.IrreducibleCountingLemmas.TYPES.RepIso at h ⊢
  obtain ⟨f, hf⟩ := h
  refine ⟨f, fun γ v => ?_⟩
  have h1 := hf (Formalism.IrreducibleCountingLemmas.TYPES.glEquiv K e γ) v
  have h2 : f (ρ.ρ ((Formalism.IrreducibleCountingLemmas.TYPES.glEquiv K e).symm (Formalism.IrreducibleCountingLemmas.TYPES.glEquiv K e γ)) v) =
      ρ'.ρ ((Formalism.IrreducibleCountingLemmas.TYPES.glEquiv K e).symm (Formalism.IrreducibleCountingLemmas.TYPES.glEquiv K e γ)) (f v) := h1
  rw [MulEquiv.symm_apply_apply] at h2
  exact h2

end Blocks

section Comparison₂

open Formalism.IrreducibleCountingLemmas.TYPES

def castIrr {g : ℕ} (L : LzData g) {a a' : ℕ} (h : a = a') (τ : L.Irr a) : L.Irr a' := h ▸ τ

theorem lab_castIrr {g : ℕ} (L : LzData g) {a a' : ℕ} (h : a = a') (τ : L.Irr a) :
    L.lab (castIrr L h τ) = L.lab τ := by
  subst h
  rfl

theorem castIrr_inj {g : ℕ} (L : LzData g) {a a' : ℕ} (h : a = a') {τ σ : L.Irr a}
    (e : castIrr L h τ = castIrr L h σ) : τ = σ := by
  subst h
  exact e

structure LzTie {g : ℕ} [Fact g.Prime] {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C)
    (L : LzData g) where
  rep : ∀ {a : ℕ}, L.Irr a → FDRep ℂ (GL (Fin a) (ZMod g))
  rep_simple : ∀ {a : ℕ} (τ : L.Irr a), Simple (rep τ)
  rep_inj : ∀ {a : ℕ} (τ σ : L.Irr a), RepIso (rep τ).ρ (rep σ).ρ → τ = σ
  rep_surj : ∀ {a : ℕ} (σ : FDRep ℂ (GL (Fin a) (ZMod g))), Simple σ → ∃ τ, RepIso σ.ρ (rep τ).ρ
  idem_eq : ∀ {a : ℕ} (τ : L.Irr a), L.idem τ = zIdem (rep τ)
  lab_eq : ∀ {a : ℕ} (τ : L.Irr a), 1 ≤ a → HasLabelO O (rep τ) (L.lab τ)
  real : ∀ {a : ℕ}, L.Rep a → FDRep ℂ (GL (Fin a) (ZMod g))
  real_ext : ∀ {a : ℕ} (R R' : L.Rep a), RepIso (real R).ρ (real R').ρ → R = R'
  real_ofIrr : ∀ {a : ℕ} (τ : L.Irr a), RepIso (real (L.ofIrr τ)).ρ (rep τ).ρ
  cons_iff : ∀ {a : ℕ} (R : L.Rep a) (σ : L.Irr a), L.cons R σ ↔ IsConstituent (rep σ) (real R).ρ
  real_hc : ∀ {a b : ℕ} (τ : L.Irr a) (τ' : L.Irr b), 1 ≤ a → 1 ≤ b →
    RepIso (real (L.hc τ τ')).ρ (hcRep (ZMod g) (twoBlock (a + b) a) (pairRep (rep τ) (rep τ')))
  hc_zero_left : ∀ {b : ℕ} (τ : L.Irr 0) (τ' : L.Irr b),
    L.hc τ τ' = L.ofIrr (castIrr L (Nat.zero_add b).symm τ')
  hc_zero_right : ∀ {a : ℕ} (τ : L.Irr a) (τ' : L.Irr 0), L.hc τ τ' = L.ofIrr τ

end Comparison₂

section HC

open Formalism.IrreducibleCountingLemmas.TYPES

def HCBody {g : ℕ} (L : LzData g) : Prop :=
  ∀ (a b : ℕ) (τ : L.Irr a) (τ' : L.Irr b),
    (∀ σ, L.cons (L.hc τ τ') σ → L.lab σ = L.lab τ * L.lab τ') ∧
    (IsCoprime (L.lab τ) (L.lab τ') →
      (∃ σ, L.hc τ τ' = L.ofIrr σ) ∧
      ∀ (τ₁ : L.Irr a) (τ₁' : L.Irr b), L.lab τ₁ = L.lab τ →
        L.lab τ₁' = L.lab τ' → L.hc τ₁ τ₁' = L.hc τ τ' → τ₁ = τ ∧ τ₁' = τ')

theorem admHC_iff_forall_body {D : D7} (P : Pend D) : HarishChandraLabels P ↔ ∀ k, HCBody (P.lz k) := Iff.rfl

theorem lab_zero {g : ℕ} (L : LzData g) (τ : L.Irr 0) : L.lab τ = 1 := by
  first
  | exact (L.lab_spec τ).1.natDegree_eq_zero_iff_eq_one.1 (L.lab_spec τ).2.1
  | exact Polynomial.eq_one_of_monic_natDegree_zero (L.lab_spec τ).1 (L.lab_spec τ).2.1

theorem ofIrr_inj {g : ℕ} (L : LzData g) {a : ℕ} {τ σ : L.Irr a} (h : L.ofIrr τ = L.ofIrr σ) :
    τ = σ := by
  have h1 : L.cons (L.ofIrr τ) τ := (L.cons_ofIrr τ τ).2 rfl
  rw [h] at h1
  exact (L.cons_ofIrr σ τ).1 h1

theorem irr_zero_eq {g : ℕ} (L : LzData g) (τ σ : L.Irr 0) : τ = σ := by
  have hs : ∀ y : MonoidAlgebra ℂ (GL (Fin 0) (ZMod g)), ∃ c : ℂ, y = algebraMap ℂ _ c := by
    intro y
    refine MonoidAlgebra.induction_on (motive := fun y => ∃ c : ℂ, y = algebraMap ℂ _ c) y ?_ ?_ ?_
    · intro z
      have hz : z = 1 := Units.ext (Matrix.ext fun i _ => Fin.elim0 i)
      exact ⟨1, by rw [map_one, hz, map_one]⟩
    · intro f₁ f₂ h₁ h₂
      obtain ⟨c₁, e₁⟩ := h₁
      obtain ⟨c₂, e₂⟩ := h₂
      exact ⟨c₁ + c₂, by rw [e₁, e₂, map_add]⟩
    · intro r f₁ h₁
      obtain ⟨c₁, e₁⟩ := h₁
      exact ⟨r * c₁, by rw [e₁, map_mul, Algebra.smul_def]⟩
  have key : ∀ x : L.Irr 0, L.idem x = 1 := by
    intro x
    obtain ⟨c, hc⟩ := hs (L.idem x)
    have h1 := L.idem_idem x
    have h2 := L.idem_ne x
    rw [hc, ← map_mul] at h1
    have h3 : c * c = c := (algebraMap ℂ (MonoidAlgebra ℂ (GL (Fin 0) (ZMod g)))).injective h1
    have h4 : c ≠ 0 := by
      rintro rfl
      exact h2 (by rw [hc, map_zero])
    have h5 : c = 1 := mul_left_cancel₀ h4 (h3.trans (mul_one c).symm)
    rw [hc, h5, map_one]
  by_contra hne
  have h6 := L.idem_orth τ σ hne
  rw [key τ, key σ, one_mul] at h6
  exact one_ne_zero h6

variable {g : ℕ} [Fact g.Prime] {C : LabelConv (ZMod g)} {O : LabelMap (ZMod g) C} {L : LzData g}

theorem hcBody_of (T : LzTie O L) (hL : HCLabelO O) (hM : LabelMulO O) (hT : TranspO O)
    (hD : HCDisjointO O) : HCBody L := by
  intro a b τ τ'
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    have h0 : L.lab τ' = 1 := lab_zero L τ'
    refine ⟨fun σ hσ => ?_, fun _ => ⟨⟨τ, T.hc_zero_right τ τ'⟩, fun τ₁ τ₁' _ _ he => ?_⟩⟩
    · have h1 := hσ
      rw [T.hc_zero_right τ τ'] at h1
      have h2 := (L.cons_ofIrr τ σ).1 h1
      rw [h0, mul_one]
      exact congrArg L.lab h2
    · rw [T.hc_zero_right, T.hc_zero_right] at he
      exact ⟨ofIrr_inj L he, irr_zero_eq L _ _⟩
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have h0 : L.lab τ = 1 := lab_zero L τ
    refine ⟨fun σ hσ => ?_, fun _ => ⟨⟨_, T.hc_zero_left τ τ'⟩, fun τ₁ τ₁' _ _ he => ?_⟩⟩
    · have h1 := hσ
      rw [T.hc_zero_left τ τ'] at h1
      have h2 := (L.cons_ofIrr _ _).1 h1
      rw [h2, h0, one_mul, lab_castIrr]
    · rw [T.hc_zero_left, T.hc_zero_left] at he
      exact ⟨irr_zero_eq L _ _, castIrr_inj L _ (ofIrr_inj L he)⟩
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have hsurj := twoBlock_surj ha hb
  have hpair : ∀ (τ₀ : L.Irr a) (τ₀' : L.Irr b) (c : Fin 2),
      Simple (pairRep (T.rep τ₀) (T.rep τ₀') c) ∧
        HasLabelO O (pairRep (T.rep τ₀) (T.rep τ₀') c) (![L.lab τ₀, L.lab τ₀'] c) := by
    intro τ₀ τ₀' c
    match c with
    | 0 => exact ⟨(hT (blk0 a b).symm (T.rep τ₀)).1 (T.rep_simple τ₀),
        (hT (blk0 a b).symm (T.rep τ₀)).2 _ (T.lab_eq τ₀ ha1)⟩
    | 1 => exact ⟨(hT (blk1 a b).symm (T.rep τ₀')).1 (T.rep_simple τ₀'),
        (hT (blk1 a b).symm (T.rep τ₀')).2 _ (T.lab_eq τ₀' hb1)⟩
  refine ⟨fun σ hσ => ?_, fun hcop => ?_⟩
  · have h1 : IsConstituent (T.rep σ) (T.real (L.hc τ τ')).ρ := (T.cons_iff _ _).1 hσ
    have h2 := isConstituent_of_repIso h1 (T.real_hc τ τ' ha1 hb1)
    have h3 := hM (a + b) 2 (twoBlock (a + b) a) (pairRep (T.rep τ) (T.rep τ'))
      ![L.lab τ, L.lab τ'] (T.rep σ) hsurj (hpair τ τ') (T.rep_simple σ) h2
    have h4 := T.lab_eq σ (by omega)
    have h5 := (hL (a + b) (by omega) (T.rep σ) (T.rep_simple σ)).2 _ _ h4 h3
    rw [h5, Fin.prod_univ_two]
    all_goals rfl
  · obtain ⟨σ, hσs, hσi⟩ := (hD (a + b) (twoBlock (a + b) a) (pairRep (T.rep τ) (T.rep τ'))
      (pairRep (T.rep τ) (T.rep τ')) ![L.lab τ, L.lab τ'] hsurj
      (fun c => ⟨(hpair τ τ' c).1, (hpair τ τ' c).1, (hpair τ τ' c).2, (hpair τ τ' c).2⟩) hcop).1
    obtain ⟨τ₂, hτ₂⟩ := T.rep_surj σ hσs
    refine ⟨⟨τ₂, T.real_ext _ _ ?_⟩, fun τ₁ τ₁' e1 e2 he => ?_⟩
    · exact repIso_trans (repIso_trans (T.real_hc τ τ' ha1 hb1) (repIso_symm hσi))
        (repIso_trans hτ₂ (repIso_symm (T.real_ofIrr τ₂)))
    · have hp1 := hpair τ₁ τ₁'
      rw [e1, e2] at hp1
      have r1 := T.real_hc τ₁ τ₁' ha1 hb1
      rw [he] at r1
      have hiso := repIso_trans (repIso_symm (T.real_hc τ τ' ha1 hb1)) r1
      have hcc := (hD (a + b) (twoBlock (a + b) a) (pairRep (T.rep τ) (T.rep τ'))
        (pairRep (T.rep τ₁) (T.rep τ₁')) ![L.lab τ, L.lab τ'] hsurj
        (fun c => ⟨(hpair τ τ' c).1, (hp1 c).1, (hpair τ τ' c).2, (hp1 c).2⟩) hcop).2 hiso
      exact ⟨(T.rep_inj τ τ₁ (repIso_of_transp (ρ := T.rep τ) (ρ' := T.rep τ₁) (blk0 a b).symm
          (hcc 0))).symm,
        (T.rep_inj τ' τ₁' (repIso_of_transp (ρ := T.rep τ') (ρ' := T.rep τ₁') (blk1 a b).symm
          (hcc 1))).symm⟩

end HC

section Row

open Formalism.IrreducibleCountingLemmas.TYPES

variable {D : D7}

def AdmHarishChandraTypes (P : Pend D) : Prop :=
  ∀ k : Fin 2,
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ (C : LabelConv (ZMod (D.host.g k))) (O : LabelMap (ZMod (D.host.g k)) C),
      Nonempty (LzTie O (P.lz k)) → HCBody (P.lz k)

def TypesHC (g : ℕ) [Fact g.Prime] : Prop :=
  ∀ (C : LabelConv (ZMod g)) (O : LabelMap (ZMod g) C),
    HCLabelO O ∧ LabelMulO O ∧ TranspO O ∧ HCDisjointO O

theorem admHarishChandraRetyped_of (P : Pend D)
    (h : ∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      TypesHC (D.host.g k)) :
    AdmHarishChandraTypes P := by
  rintro k C O ⟨T⟩
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨h1, h2, h3, h4⟩ := h k C O
  exact hcBody_of T h1 h2 h3 h4

def LzCompatibility (P : Pend D) : Prop :=
  ∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ (C : LabelConv (ZMod (D.host.g k))) (O : LabelMap (ZMod (D.host.g k)) C),
      Nonempty (LzTie O (P.lz k))

theorem admHC_of_tied_labels (P : Pend D) (hT : LzCompatibility P) (h : AdmHarishChandraTypes P) : HarishChandraLabels P := by
  rw [admHC_iff_forall_body]
  intro k
  obtain ⟨C, O, hT'⟩ := hT k
  exact h k C O hT'

theorem admHC_of_GL_types (P : Pend D)
    (h : ∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      TypesHC (D.host.g k))
    (hT : LzCompatibility P) : HarishChandraLabels P := admHC_of_tied_labels P hT (admHarishChandraRetyped_of P h)

end Row

section Refute

open Formalism.IrreducibleCountingLemmas.TYPES

theorem irr_nonempty {g : ℕ} (L : LzData g) (a : ℕ) : Nonempty (L.Irr a) := by
  by_contra hne
  have h0 : ∑ τ : L.Irr a, L.idem τ = 0 :=
    Finset.sum_eq_zero (fun τ _ => absurd (Nonempty.intro τ) hne)
  exact one_ne_zero ((L.idem_sum a).symm.trans h0)

theorem spec_XsubC {g : ℕ} [Fact g.Prime] (c : ZMod g) (hc : c ≠ 0) (n : ℕ) :
    ((X - C c) ^ n).Monic ∧ ((X - C c) ^ n).natDegree = n ∧ ((X - C c) ^ n).coeff 0 ≠ 0 := by
  refine ⟨(Polynomial.monic_X_sub_C c).pow n, ?_, ?_⟩
  · first
    | rw [(Polynomial.monic_X_sub_C c).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    | simp
  · rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, zero_sub]
    exact pow_ne_zero _ (neg_ne_zero.2 hc)

def relabel {g : ℕ} [Fact g.Prime] (h2 : (2 : ZMod g) ≠ 0) (L : LzData g) : LzData g where
  Irr := L.Irr
  idem := L.idem
  idem_idem := L.idem_idem
  idem_central := L.idem_central
  idem_ne := L.idem_ne
  idem_orth := L.idem_orth
  idem_sum := L.idem_sum
  idem_prim := L.idem_prim
  lab := fun {a} τ => if a = 1 then (X - C 1) ^ 1 else if a = 2 then (X - C 2) ^ 2 else L.lab τ
  lab_spec := by
    intro a τ
    by_cases h1 : a = 1
    · subst h1; simpa using spec_XsubC (1 : ZMod g) one_ne_zero 1
    · by_cases h2' : a = 2
      · subst h2'; simpa using spec_XsubC (2 : ZMod g) h2 2
      · simpa [h1, h2'] using L.lab_spec τ
  Rep := L.Irr
  ofIrr := fun τ => τ
  cons := fun R σ => σ = R
  cons_ofIrr := fun _ _ => Iff.rfl
  hc := fun {a b} _ _ => Classical.choice (irr_nonempty L (a + b))

theorem not_HCBody_relabel {g : ℕ} [Fact g.Prime] (h2 : (2 : ZMod g) ≠ 0) (L : LzData g) :
    ¬ HCBody (relabel h2 L) := by
  intro hB
  obtain ⟨τ⟩ := irr_nonempty L 1
  have h1 := (hB 1 1 τ τ).1 ((relabel h2 L).hc τ τ) (by first | exact rfl | simp [relabel])
  have hl1 : (relabel h2 L).lab τ = X - C 1 := by simp [relabel]
  have hl2 : (relabel h2 L).lab ((relabel h2 L).hc τ τ) = (X - C 2) ^ 2 := by simp [relabel]
  rw [hl2, hl1] at h1
  have h3 := congrArg (Polynomial.eval (1 : ZMod g)) h1
  simp only [Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_self, mul_zero] at h3
  have h4 : ((1 : ZMod g) - 2) ^ 2 = 1 := by ring
  rw [h4] at h3
  exact one_ne_zero h3

theorem relabel_untied {g : ℕ} [Fact g.Prime] (h2 : (2 : ZMod g) ≠ 0) (L : LzData g)
    {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C) (hL : HCLabelO O) (hM : LabelMulO O)
    (hT : TranspO O) (hD : HCDisjointO O) : IsEmpty (LzTie O (relabel h2 L)) := ⟨fun T => not_HCBody_relabel h2 L (hcBody_of T hL hM hT hD)⟩

end Refute

section DZ

variable {D : D7}

def Occurs (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k)
    (z : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) : Prop :=
  ∃ F ∈ D.naut.typeV i PI, D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) F ≠ 0

def DZConcl (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (PI : D.naut.AV i)
    (f : (ZMod (D.host.g k))[X]) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  ∃ u : (ZMod (D.host.g k))ˣ, (u = chiJ D i k v ∨ u = (chiJ D i k v)⁻¹) ∧
    D.naut.mono0 (D.naut.locV i PI (D.naut.plGw k v)) ∧
    D.naut.items₂ k (D.naut.plGw k v) (D.naut.locV i PI (D.naut.plGw k v)) =
      f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t ∧
    ∀ w', IsConjPl D.host (D.naut.plGw k v) w' →
      D.naut.mono0 (D.naut.locV i PI w') ∧
      (D.naut.items₂ k w' (D.naut.locV i PI w')).natDegree = D.R.nV ∧
      Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w' (D.naut.locV i PI w')) =
        (Formalism.CyclotomicNorms.rootsBar (f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)).map (·⁻¹)

def AdmDepthZeroTypes : Prop :=
  ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (PI : D.naut.AV i),
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ (ρ : FDRep ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) (f : (ZMod (D.host.g k))[X]),
      Simple ρ → Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * D.ntypes.eSer k f = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ →
      Occurs i PI k v (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) → Squarefree f →
      (∀ u : (ZMod (D.host.g k))ˣ, u = chiJ D i k v ∨ u = (chiJ D i k v)⁻¹ →
        ¬ f.IsRoot (u : ZMod (D.host.g k))) →
      DZConcl i k v PI f

def KtyTie (P : Pend D) : Prop :=
  ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (τ : (P.lz k).Irr D.R.r),
    τ ∈ P.kty i PI k v → Occurs i PI k v ((P.lz k).idem τ)

theorem ktyTie_of_spec (P : Pend D) : KtyTie P := by
  intro i PI k v τ hτ
  exact (P.kty_spec i PI k v τ).1 hτ

theorem idem_mul_eSer (P : Pend D) (k : Fin 2) (τ : (P.lz k).Irr D.R.r) :
    (P.lz k).idem τ * D.ntypes.eSer k ((P.lz k).lab τ) = (P.lz k).idem τ := by
  rw [P.eSer_eq, Finset.mul_sum, Finset.sum_eq_single τ]
  · rw [if_pos rfl, (P.lz k).idem_idem τ]
  · intro σ _ hne
    split_ifs
    · exact (P.lz k).idem_orth τ σ (fun h => hne h.symm)
    · exact mul_zero _
  · intro h
    exact absurd (Finset.mem_univ τ) h

theorem admDZ_of_tied_labels (P : Pend D) (hT : LzCompatibility P) (h : AdmDepthZeroTypes (D := D)) :
    admDZ P := by
  intro i k v PI τ hτ hsq hav
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨C, O, ⟨T⟩⟩ := hT k
  have e := T.idem_eq τ
  have hz : Formalism.IrreducibleCountingLemmas.TYPES.zIdem (T.rep τ) * D.ntypes.eSer k ((P.lz k).lab τ) =
      Formalism.IrreducibleCountingLemmas.TYPES.zIdem (T.rep τ) := by
    have := idem_mul_eSer P k τ
    rwa [e] at this
  have ho : Occurs i PI k v (Formalism.IrreducibleCountingLemmas.TYPES.zIdem (T.rep τ)) := by
    have := ktyTie_of_spec P i PI k v τ hτ
    rwa [e] at this
  exact h i k v PI (T.rep τ) ((P.lz k).lab τ) (T.rep_simple τ) hz ho hsq hav

theorem kty_labels_eq (P : Pend D) (hT : LzCompatibility P) (h : AdmDepthZeroTypes (D := D))
    (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (PI : D.naut.AV i) (τ₁ τ₂ : (P.lz k).Irr D.R.r)
    (h1 : τ₁ ∈ P.kty i PI k v) (h2 : τ₂ ∈ P.kty i PI k v)
    (s1 : Squarefree ((P.lz k).lab τ₁)) (s2 : Squarefree ((P.lz k).lab τ₂))
    (a1 : ∀ u : (ZMod (D.host.g k))ˣ, u = chiJ D i k v ∨ u = (chiJ D i k v)⁻¹ →
      ¬ ((P.lz k).lab τ₁).IsRoot (u : ZMod (D.host.g k)))
    (a2 : ∀ u : (ZMod (D.host.g k))ˣ, u = chiJ D i k v ∨ u = (chiJ D i k v)⁻¹ →
      ¬ ((P.lz k).lab τ₂).IsRoot (u : ZMod (D.host.g k))) :
    (P.lz k).lab τ₁ = (P.lz k).lab τ₂ := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hA := admDZ_of_tied_labels P hT h
  obtain ⟨u₁, hu₁, -, e₁, -⟩ := hA i k v PI τ₁ h1 s1 a1
  obtain ⟨u₂, hu₂, -, e₂, -⟩ := hA i k v PI τ₂ h2 s2 a2
  have e := e₁.symm.trans e₂
  by_cases ht : D.R.t = 0
  · simp only [ht, pow_zero, mul_one] at e
    exact e
  have hu : (u₁ : ZMod (D.host.g k)) = u₂ := by
    by_contra hne
    apply a2 u₁ hu₁
    have h3 := congrArg (Polynomial.eval (u₁ : ZMod (D.host.g k))) e
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self, ne_eq, ht, not_false_eq_true, zero_pow, mul_zero] at h3
    have hne' : ((u₁ : ZMod (D.host.g k)) - u₂) ^ D.R.t ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hne)
    exact (mul_eq_zero.1 h3.symm).resolve_right hne'
  rw [hu] at e
  exact mul_right_cancel₀ (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)) e

end DZ

section TY

open Formalism.MainNotions.SumRepresentations.At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def LPMs : Prop :=
  ∀ w, ∃ (Y : Type) (m : A.LP w → Multiset Y), Function.Injective m ∧
    ∀ a b : A.LP w, m (A.lpSum a b) = m a + m b

def LPCancel : Prop := ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b

theorem lpCancel_of (h : LPMs N A) : LPCancel N A := by
  intro w a b c hab
  obtain ⟨Y, m, hinj, hadd⟩ := h w
  apply hinj
  have h1 := congrArg m hab
  rw [hadd, hadd] at h1
  exact add_right_cancel h1

def DepthZeroInertiaPolynomials : Prop :=
  (∀ (i : N.Loc) (P : A.AV i) (w : PlE H), (w ∈ N.S i ∨ w ∈ N.Q i) →
    (w ∈ N.Q i ∨ (Del N i ∧ (w ∈ placesOver H.E H.pde ∨ (N.l i = H.pde ∧ w ∈ placesOver H.E H.pde')))) →
    A.mono0 (A.locV i P w) ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      A.inePol (A.locV i P w) σ = (X - 1) ^ R.r * (X - C (iotaO N A i (chi1 N i σ))) ^ R.t) ∧
  (∀ (i : N.Loc) (P : A.AV i) (w : PlE H), w ∈ N.S i → (∃ k, w ∈ placesOver H.E (H.g k)) →
    TameGen N (N.plOm.1 w) (N.gam0 i w) →
    (A.inePol (A.locV i P w) (N.gam0 i w)).rootMultiplicity (iotaO N A i (chi1 N i (N.gam0 i w))) ≤ R.t →
    ∃ a b : A.LP w, A.locV i P w = A.lpSum a b ∧ A.lpDim a = R.r ∧ A.lpDim b = R.t ∧ A.mono0 b ∧
      ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol b σ = (X - C (iotaO N A i (chi1 N i σ))) ^ R.t)

def AdmTypeTheory : Prop := LPMs N A → DepthZeroInertiaPolynomials N A

theorem admTY_iff_and_cancel : MonodromyInertiaType N A ↔ DepthZeroInertiaPolynomials N A ∧ LPCancel N A := by
  first
  | exact Iff.rfl
  | (unfold Formalism.MainNotions.SumRepresentations.At.MonodromyInertiaType DepthZeroInertiaPolynomials LPCancel; tauto)
  | (simp only [Formalism.MainNotions.SumRepresentations.At.MonodromyInertiaType, DepthZeroInertiaPolynomials, LPCancel]; tauto)

theorem admTY_of_retyped (hLP : LPMs N A) (h : AdmTypeTheory N A) : MonodromyInertiaType N A := (admTY_iff_and_cancel N A).2 ⟨h hLP, lpCancel_of N A hLP⟩

theorem fourth_hypothesis_of_lifting (D : D7) (hLP : LPMs D.nd D.naut) (h : AdmTypeTheory D.nd D.naut) : Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D := by
  first
  | exact admTY_of_retyped D.nd D.naut hLP h
  | (unfold Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching; exact admTY_of_retyped D.nd D.naut hLP h)

theorem orSum_noMs : ¬ ∃ (Y : Type) (m : ℕ × Bool → Multiset Y), Function.Injective m ∧
    ∀ a b : ℕ × Bool, m (a.1 + b.1, a.2 || b.2) = m a + m b := by
  rintro ⟨Y, m, hinj, hadd⟩
  have h1 : m (0, true) = m (0, true) + m (0, true) := hadd (0, true) (0, true)
  have h2 : m (0, false) = m (0, false) + m (0, false) := hadd (0, false) (0, false)
  have e1 : m (0, true) = 0 := by
    have h3 := congrArg Multiset.card h1
    rw [Multiset.card_add] at h3
    exact Multiset.card_eq_zero.1 (by omega)
  have e2 : m (0, false) = 0 := by
    have h3 := congrArg Multiset.card h2
    rw [Multiset.card_add] at h3
    exact Multiset.card_eq_zero.1 (by omega)
  have h4 := congrArg Prod.snd (hinj (e1.trans e2.symm))
  first
  | exact absurd h4 (by decide)
  | simp at h4

end TY

end Formalism.MainNotions.PairedCharacterCondition.RT

end
