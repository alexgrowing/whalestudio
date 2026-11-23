import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Definitions.Foundations.Mdl
import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
import Development.AbelianVarietyTheory.Definitions.Foundations.CthFac
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC

noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.K4

open GlobalTheory.KZ GlobalTheory.NeedB GlobalTheory.KEdge

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def sgK (X : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ) : X.K :=
  Classical.epsilon fun f : X.K =>
    X.an f = (((fun z : ℂ => if h : 0 < z.im then GlobalTheory.Sieg.sg c x ⟨z, h⟩ else 0) : ℂ → ℂ) : Mero)

def fixMu (Ω : Type) [Field Ω] [Algebra ℚ Ω] (M : ℕ) : Subgroup (Ω ≃ₐ[ℚ] Ω) :=
  (IntermediateField.adjoin ℚ {z : Ω | z ^ M = 1}).fixingSubgroup

theorem mem_fixMu_iff {M : ℕ} (s : Ω ≃ₐ[ℚ] Ω) : s ∈ fixMu Ω M ↔ ∀ z : Ω, z ^ M = 1 → s z = z := by
  unfold fixMu
  rw [IntermediateField.mem_fixingSubgroup_iff]
  refine ⟨fun h z hz => h z (IntermediateField.subset_adjoin ℚ _ hz), fun h z hz => ?_⟩
  induction hz using IntermediateField.adjoin_induction with
  | mem z hz => exact h z hz
  | algebraMap q => exact s.commutes q
  | add a b _ _ ha hb => rw [map_add, ha, hb]
  | inv a _ ha => rw [map_inv₀, ha]
  | mul a b _ _ ha hb => rw [map_mul, ha, hb]

def kumH {F Ω' : Type*} [Field F] [Field Ω'] [Algebra F Ω'] (N : ℕ) (ζ θ : Ω') : (Ω' ≃ₐ[F] Ω') →* Multiplicative (ZMod N) :=
  open Classical in
  if h : ∀ a b : Ω' ≃ₐ[F] Ω', kum (K := F) (N := N) ζ θ (a * b) = kum ζ θ a + kum ζ θ b then
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (kum (K := F) (N := N) ζ θ g)) (fun a b => by rw [h]; rfl)
  else 1

def wk4 (X : Tower Ω ε) (l n r N : ℕ) (x : ZMod N) (c d : ℕ) (σ : Ω ≃ₐ[ℚ] Ω) : X.K :=
  let M : ℕ := l ^ (r + n) * N
  let L : Subfield X.K := lev X (CongruenceSubgroup.Gamma M)
  let F : Subfield X.K := mdl X (CongruenceSubgroup.Gamma M) (fixMu Ω M)
  let hFL : F ≤ L := inf_le_left
  letI : Algebra F L := (Subfield.inclusion hFL).toAlgebra
  let Kb := AlgebraicClosure L
  let t : ℚ := (((l : ZMod N) ^ (r + n))⁻¹.val : ℚ)
  let u : X.K := sgK X c ![1 / (l : ℚ) ^ (r + n), (x.val : ℚ) * t / N]
  let v : X.K := sgK X d ![0, 1 / (l : ℚ) ^ (r + n) + t / N]
  let Nn : ℕ := l ^ n
  let ζ : Kb := Classical.epsilon fun z : Kb => IsPrimitiveRoot z Nn
  let α : Kb := Classical.epsilon fun a : Kb => ∃ f : L, (f : X.K) = u ∧ a ^ Nn = algebraMap L Kb f
  let β : Kb := Classical.epsilon fun a : Kb => ∃ f : L, (f : X.K) = v ∧ a ^ Nn = algebraMap L Kb f
  let xh := kumH (F := F) Nn ζ α
  let yh := kumH (F := F) Nn ζ β
  let η : (Kb ≃ₐ[F] Kb) → ZMod Nn := Classical.epsilon fun η : (Kb ≃ₐ[F] Kb) → ZMod Nn =>
    CobOn (geo F L Kb) xh yh η ∧ IsLocallyConstant (fun g : geo F L Kb => η g) ∧
      ∀ (B : ValuationSubring Kb) (g : Kb ≃ₐ[F] Kb),
        (∀ f : L, ((f : X.K) = X.jK ∨ (f : X.K) ∈ Set.range (algebraMap Ω X.K)) → algebraMap L Kb f ∈ B) →
        (∀ z, B.valuation z ≤ 1 → B.valuation (g z - z) < 1) → g ∈ geo F L Kb → η g = 0
  let lift : Kb ≃ₐ[F] Kb := Classical.epsilon fun φ : Kb ≃ₐ[F] Kb =>
    ∀ f : L, ∃ f' : L, (f' : X.K) = X.gal σ f ∧ φ (algebraMap L Kb f) = algebraMap L Kb f'
  ((topW (K := L) ζ xh yh η lift⁻¹ : L) : X.K)

theorem kumH_apply {F Ω' : Type*} [Field F] [Field Ω'] [Algebra F Ω'] {N : ℕ} [NeZero N] {ζ θ : Ω'}
    (hζ : IsPrimitiveRoot ζ N) (hfix : ∀ g : Ω' ≃ₐ[F] Ω', g ζ = ζ) {w : F} (hw0 : w ≠ 0) (hw : θ ^ N = algebraMap F Ω' w)
    (g : Ω' ≃ₐ[F] Ω') : (kumH (F := F) N ζ θ g).toAdd = kum (K := F) (N := N) ζ θ g := by
  have hk : ∀ g : Ω' ≃ₐ[F] Ω', g θ = ζ ^ (kum (K := F) (N := N) ζ θ g).val * θ := fun g =>
    TopW.apply_eq_kum (K := F) hζ hw0 hw ((TopW.mem_geo g).2 fun z => g.commutes z)
  have hθ : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne N)] at hw
    exact hw0 ((algebraMap F Ω').injective (by rw [← hw, map_zero]))
  have h : ∀ a b : Ω' ≃ₐ[F] Ω', kum (K := F) (N := N) ζ θ (a * b) = kum ζ θ a + kum ζ θ b := fun a b => by
    apply kum_eq_of hζ hθ
    rw [AlgEquiv.mul_apply, TopW.pow_val_add hζ]
    conv_lhs => rw [hk b, map_mul, map_pow, hfix a, hk a]
    ring
  unfold kumH
  rw [dif_pos h]
  rfl

theorem eps_eOm [IsAlgClosed Ω] (q : ℚ) : ε (eOm ε q) = Complex.exp (2 * Real.pi * Complex.I * (q : ℂ)) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (q.den : Ω) := ⟨Nat.cast_ne_zero.2 q.den_ne_zero⟩
  haveI : NeZero q.den := ⟨q.den_ne_zero⟩
  have hw : Complex.exp (2 * Real.pi * Complex.I * (q : ℂ)) ^ q.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have : (q.den : ℂ) * (2 * Real.pi * Complex.I * (q : ℂ)) = q.num * (2 * Real.pi * Complex.I) := by
      have hd : (q.den : ℂ) ≠ 0 := by exact_mod_cast q.den_ne_zero
      have : (q : ℂ) = (q.num : ℂ) / q.den := by exact_mod_cast (Rat.num_div_den q).symm
      rw [this]; field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q.den Ω)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos q.den Ω q.den_pos))
  have hz' : IsPrimitiveRoot z q.den := Polynomial.isRoot_cyclotomic_iff.1 hz
  obtain ⟨i, -, hi⟩ := (hz'.map_of_injective ε.injective).eq_pow_of_pow_eq_one hw
  exact Function.invFun_eq ⟨z ^ i, by rw [map_pow, hi]⟩

theorem isPrimitiveRoot_eOm [IsAlgClosed Ω] (ε : Ω →+* ℂ) {m : ℕ} (hm : m ≠ 0) : IsPrimitiveRoot (eOm ε (1 / (m : ℚ))) m := by
  apply IsPrimitiveRoot.of_map_of_injective (f := ε) _ ε.injective
  rw [eps_eOm]
  convert Complex.isPrimitiveRoot_exp m hm using 2
  push_cast
  ring

abbrev topL (X : Tower Ω ε) (M : ℕ) : Subfield X.K := lev X (CongruenceSubgroup.Gamma M)

abbrev topF (X : Tower Ω ε) (M : ℕ) : Subfield X.K := mdl X (CongruenceSubgroup.Gamma M) (fixMu Ω M)

abbrev topBar (X : Tower Ω ε) (M : ℕ) : Type := AlgebraicClosure (topL X M)

attribute [local instance] algMdl

abbrev topGal (X : Tower Ω ε) (M : ℕ) : Type := topBar X M ≃ₐ[topF X M] topBar X M

def topZeta (X : Tower Ω ε) (M l n : ℕ) : topBar X M :=
  algebraMap (topL X M) (topBar X M) (levConst X (CongruenceSubgroup.Gamma M) (eOm ε (1 / (l : ℚ) ^ n)))

theorem isPrimitiveRoot_topZeta [IsAlgClosed Ω] (X : Tower Ω ε) (M : ℕ) {l : ℕ} (hl : l ≠ 0) (n : ℕ) :
    IsPrimitiveRoot (topZeta X M l n) (l ^ n) := by
  have h := isPrimitiveRoot_eOm ε (pow_ne_zero n hl)
  rw [Nat.cast_pow] at h
  exact (h.map_of_injective (levConst X _).injective).map_of_injective (algebraMap (topL X M) (topBar X M)).injective

theorem topGal_topZeta [IsAlgClosed Ω] (X : Tower Ω ε) {M l n : ℕ} (hl : l ≠ 0) (hM : l ^ n ∣ M) (g : topGal X M) :
    g (topZeta X M l n) = topZeta X M l n := by
  have h := isPrimitiveRoot_eOm ε (pow_ne_zero n hl)
  rw [Nat.cast_pow] at h
  have hm : algebraMap Ω X.K (eOm ε (1 / (l : ℚ) ^ n)) ∈ topF X M :=
    algebraMap_mem_mdl X _ _ _ fun s hs => (mem_fixMu_iff s).1 hs _ ((h.pow_eq_one_iff_dvd M).2 hM)
  have e : topZeta X M l n = algebraMap (topF X M) (topBar X M) ⟨_, hm⟩ :=
    (IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M) ⟨_, hm⟩).symm
  rw [e, g.commutes]

def topRoot (X : Tower Ω ε) (M m : ℕ) (w : X.K) : topBar X M :=
  Classical.epsilon fun a : topBar X M => ∃ f : topL X M, (f : X.K) = w ∧ a ^ m = algebraMap (topL X M) (topBar X M) f

theorem topRoot_pow (X : Tower Ω ε) (M : ℕ) {m : ℕ} (hm : m ≠ 0) {w : X.K} (hw : w ∈ topL X M) :
    topRoot X M m w ^ m = algebraMap (topL X M) (topBar X M) ⟨w, hw⟩ := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap (topL X M) (topBar X M) ⟨w, hw⟩) (Nat.pos_of_ne_zero hm)
  obtain ⟨f, hf, h⟩ := Classical.epsilon_spec (p := fun a : topBar X M =>
    ∃ f : topL X M, (f : X.K) = w ∧ a ^ m = algebraMap (topL X M) (topBar X M) f) ⟨a, ⟨w, hw⟩, rfl, ha⟩
  subst hf
  exact h

def topChar (X : Tower Ω ε) (M l n : ℕ) (w : X.K) : topGal X M →* Multiplicative (ZMod (l ^ n)) :=
  kumH (F := topF X M) (l ^ n) (topZeta X M l n) (topRoot X M (l ^ n) w)

theorem topChar_apply [IsAlgClosed Ω] (X : Tower Ω ε) {M l n : ℕ} (hl : l ≠ 0) (hM : l ^ n ∣ M) {w : X.K}
    (hw : w ∈ topF X M) (hw0 : w ≠ 0) (g : topGal X M) :
    (topChar X M l n w g).toAdd = kum (K := topF X M) (N := l ^ n) (topZeta X M l n) (topRoot X M (l ^ n) w) g := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero n hl⟩
  refine kumH_apply (isPrimitiveRoot_topZeta X M hl n) (topGal_topZeta X hl hM) (w := (⟨w, hw⟩ : topF X M))
    (fun h => hw0 (congrArg Subtype.val h)) ?_ g
  rw [topRoot_pow X M (pow_ne_zero n hl) (mdl_le_lev X _ _ hw),
    IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M)]
  rfl

def IsTopEta (X : Tower Ω ε) (M : ℕ) {m : ℕ} (x y : topGal X M →* Multiplicative (ZMod m)) (η : topGal X M → ZMod m) : Prop :=
  CobOn (geo (topF X M) (topL X M) (topBar X M)) x y η ∧
    IsLocallyConstant (fun g : geo (topF X M) (topL X M) (topBar X M) => η g) ∧
    ∀ (B : ValuationSubring (topBar X M)) (g : topGal X M),
      (∀ f : topL X M, ((f : X.K) = X.jK ∨ (f : X.K) ∈ Set.range (algebraMap Ω X.K)) →
        algebraMap (topL X M) (topBar X M) f ∈ B) →
      (∀ z, B.valuation z ≤ 1 → B.valuation (g z - z) < 1) → g ∈ geo (topF X M) (topL X M) (topBar X M) → η g = 0

def topEta (X : Tower Ω ε) (M : ℕ) {m : ℕ} (x y : topGal X M →* Multiplicative (ZMod m)) : topGal X M → ZMod m :=
  Classical.epsilon (IsTopEta X M x y)

theorem isTopEta_topEta (X : Tower Ω ε) (M : ℕ) {m : ℕ} {x y : topGal X M →* Multiplicative (ZMod m)}
    (h : ∃ η, IsTopEta X M x y η) : IsTopEta X M x y (topEta X M x y) :=
  Classical.epsilon_spec h

def IsTopLift (X : Tower Ω ε) (M : ℕ) (σ : Ω ≃ₐ[ℚ] Ω) (φ : topGal X M) : Prop :=
  ∀ f : topL X M, ∃ f' : topL X M, (f' : X.K) = X.gal σ f ∧
    φ (algebraMap (topL X M) (topBar X M) f) = algebraMap (topL X M) (topBar X M) f'

def topLift (X : Tower Ω ε) (M : ℕ) (σ : Ω ≃ₐ[ℚ] Ω) : topGal X M :=
  Classical.epsilon (IsTopLift X M σ)

theorem gal_mul_apply (X : Tower Ω ε) (s t : Ω ≃ₐ[ℚ] Ω) (f : X.K) : X.gal (s * t) f = X.gal s (X.gal t f) := by
  apply exp_injective X
  ext r
  rw [X.gal_exp, X.gal_exp, X.gal_exp, AlgEquiv.mul_apply]

theorem gal_one_apply (X : Tower Ω ε) (f : X.K) : X.gal 1 f = f := by
  apply exp_injective X
  ext r
  rw [X.gal_exp, AlgEquiv.one_apply]

theorem gal_mem_topL [IsAlgClosed Ω] (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) {σ : Ω ≃ₐ[ℚ] Ω} (hσ : σ ∈ fixMu Ω M) {f : X.K}
    (hf : f ∈ topL X M) : X.gal σ f ∈ topL X M := by
  rw [mem_lev_iff] at hf ⊢
  intro γ hγ
  have hζ := isPrimitiveRoot_eOm ε hM
  have h := X.recip M f (Nat.pos_of_ne_zero hM) hf _ hζ σ 1
    (by rw [zpow_one]; exact (mem_fixMu_iff σ).1 hσ _ hζ.pow_eq_one) γ γ (by simp)
  rw [← h, hf γ hγ]

theorem exists_isTopLift [IsAlgClosed Ω] (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) {σ : Ω ≃ₐ[ℚ] Ω} (hσ : σ ∈ fixMu Ω M) :
    ∃ φ, IsTopLift X M σ φ := by
  let e : topL X M ≃+* topL X M :=
    { toFun := fun f => ⟨X.gal σ f, gal_mem_topL X hM hσ f.2⟩
      invFun := fun f => ⟨X.gal σ⁻¹ f, gal_mem_topL X hM (inv_mem hσ) f.2⟩
      left_inv := fun f => Subtype.ext (by
        show X.gal σ⁻¹ (X.gal σ f) = f
        rw [← gal_mul_apply, inv_mul_cancel, gal_one_apply])
      right_inv := fun f => Subtype.ext (by
        show X.gal σ (X.gal σ⁻¹ f) = f
        rw [← gal_mul_apply, mul_inv_cancel, gal_one_apply])
      map_mul' := fun a b => Subtype.ext (map_mul (X.gal σ) (a : X.K) b)
      map_add' := fun a b => Subtype.ext (map_add (X.gal σ) (a : X.K) b) }
  let E : topBar X M ≃+* topBar X M := IsAlgClosure.equivOfEquiv (topBar X M) (topBar X M) e
  have hE : ∀ f : topL X M, E (algebraMap (topL X M) (topBar X M) f) = algebraMap (topL X M) (topBar X M) (e f) :=
    fun f => IsAlgClosure.equivOfEquiv_algebraMap _ _ e f
  refine ⟨AlgEquiv.ofRingEquiv (f := E) fun a => ?_, fun f => ⟨e f, rfl, hE f⟩⟩
  rw [IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M), hE]
  congr 1
  exact Subtype.ext (((mem_mdl_iff X _ _ _).1 a.2).2 σ hσ)

theorem isTopLift_topLift [IsAlgClosed Ω] (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) {σ : Ω ≃ₐ[ℚ] Ω} (hσ : σ ∈ fixMu Ω M) :
    IsTopLift X M σ (topLift X M σ) :=
  Classical.epsilon_spec (exists_isTopLift X hM hσ)

theorem IsTopLift.inv_mul_mem_geo {X : Tower Ω ε} {M : ℕ} {σ : Ω ≃ₐ[ℚ] Ω} {φ ψ : topGal X M} (hφ : IsTopLift X M σ φ)
    (hψ : IsTopLift X M σ ψ) : φ⁻¹ * ψ ∈ geo (topF X M) (topL X M) (topBar X M) := by
  rw [TopW.mem_geo]
  intro f
  obtain ⟨a, ha, h1⟩ := hφ f
  obtain ⟨b, hb, h2⟩ := hψ f
  have : a = b := Subtype.ext (ha.trans hb.symm)
  rw [AlgEquiv.mul_apply, h2, ← this, ← h1, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

def topT (l s N : ℕ) : ℕ := (((l : ZMod N) ^ s)⁻¹).val

theorem topT_spec {l N : ℕ} [NeZero N] (h : Nat.Coprime l N) (s : ℕ) : (l : ZMod N) ^ s * (topT l s N : ZMod N) = 1 := by
  unfold topT
  rw [ZMod.natCast_zmod_val]
  exact ZMod.mul_inv_of_unit _ (((ZMod.isUnit_iff_coprime l N).2 h).pow s)

def topU (X : Tower Ω ε) (l s N : ℕ) (x : ZMod N) (c : ℕ) : X.K :=
  siegel X c ![1 / (l : ℚ) ^ s, (x.val : ℚ) * (topT l s N : ℚ) / N]

def topV (X : Tower Ω ε) (l s N : ℕ) (d : ℕ) : X.K :=
  siegel X d ![0, 1 / (l : ℚ) ^ s + (topT l s N : ℚ) / N]

def wkTop (X : Tower Ω ε) (l n r N : ℕ) (x : ZMod N) (c d : ℕ) (σ : Ω ≃ₐ[ℚ] Ω) : X.K :=
  ((topW (K := topL X (l ^ (r + n) * N)) (topZeta X (l ^ (r + n) * N) l n)
    (topChar X (l ^ (r + n) * N) l n (topU X l (r + n) N x c))
    (topChar X (l ^ (r + n) * N) l n (topV X l (r + n) N d))
    (topEta X (l ^ (r + n) * N) (topChar X (l ^ (r + n) * N) l n (topU X l (r + n) N x c))
      (topChar X (l ^ (r + n) * N) l n (topV X l (r + n) N d)))
    (topLift X (l ^ (r + n) * N) σ)⁻¹ : topL X (l ^ (r + n) * N)) : X.K)

theorem wkTop_mem (X : Tower Ω ε) (l n r N : ℕ) (x : ZMod N) (c d : ℕ) (σ : Ω ≃ₐ[ℚ] Ω) :
    wkTop X l n r N x c d σ ∈ topL X (l ^ (r + n) * N) := Subtype.property _

theorem pow_dvd_topLevel (l n r N : ℕ) : l ^ n ∣ l ^ (r + n) * N :=
  (pow_dvd_pow l (Nat.le_add_left n r)).mul_right N

example : topT 3 1 5 = 2 ∧ topT 3 2 5 = 4 := by
  have h : ∀ s k : ℕ, k < 5 → (3 : ZMod 5) ^ s * (k : ZMod 5) = 1 → topT 3 s 5 = k := fun s k hk e => by
    have e1 := topT_spec (l := 3) (N := 5) (by norm_num) s
    have hu : IsUnit ((3 : ZMod 5) ^ s) := IsUnit.of_mul_eq_one _ e
    have e2 : ((topT 3 s 5 : ℕ) : ZMod 5) = k := hu.mul_left_cancel (by rw [e]; exact_mod_cast e1)
    have e3 : topT 3 s 5 < 5 := ZMod.val_lt _
    have e4 := congrArg ZMod.val e2
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt e3, Nat.mod_eq_of_lt hk] at e4
  exact ⟨h 1 2 (by norm_num) (by decide), h 2 4 (by norm_num) (by decide)⟩

example [IsAlgClosed Ω] : ε (eOm ε (1 / ((2 : ℕ) : ℚ) ^ 2)) = Complex.I := by
  rw [eps_eOm]
  refine Eq.trans ?_ Complex.exp_pi_div_two_mul_I
  congr 1
  push_cast
  ring

example : (Complex.conjAe.restrictScalars ℚ) ∈ fixMu ℂ 2 ∧ (Complex.conjAe.restrictScalars ℚ) ∉ fixMu ℂ 4 := by
  rw [mem_fixMu_iff, mem_fixMu_iff]
  refine ⟨fun z hz => ?_, fun h => ?_⟩
  · rcases mul_self_eq_one_iff.1 (by rw [← sq]; exact hz : z * z = 1) with rfl | rfl <;> simp
  · have := congrArg Complex.im (h Complex.I Complex.I_pow_four)
    norm_num at this

example : (kumH (F := ℝ) 2 (-1 : ℂ) Complex.I Complex.conjAe).toAdd = 1 := by
  have hζ : IsPrimitiveRoot (-1 : ℂ) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)
  rw [kumH_apply hζ (fun g => by simp) (w := (-1 : ℝ)) (by norm_num) (by simp)]
  exact kum_eq_of hζ Complex.I_ne_zero 1 (by simp [ZMod.val_one])

end GlobalTheory.K4
