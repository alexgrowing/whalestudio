import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CycMOfNot
import Development.AbelianVarietyTheory.Definitions.Foundations.IsScalarTowerMdlOm
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftSLMapMulInvMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv

noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def secT (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w : ℕ) (a : X.K) : X.Fn l :=
  fun u => (u 0) ^ w • GlobalTheory.ZetaB.clsHat X l a

open Classical in

def gamMod (N l M : ℕ) [NeZero M] : Finset SL(2, ZMod M) :=
  Finset.univ.filter fun γ : SL(2, ZMod M) =>
    γ ∈ (Gam N l).map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)))

def pushT (X : Tower Ω ε) (l N M : ℕ) [Fact l.Prime] [NeZero M] (b : X.Fn l) : X.Fn l :=
  ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ gamMod N l M,
    X.act l ((GlobalTheory.ZetaB.gR l N (r₀ : ZMod l) * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b

def clsZT (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (σ : Ω ≃ₐ[ℚ] Ω) : X.Fn l :=
  pushT X l N (topM l n r N) (secT X l (k - 2) (wkTop X l n r N x c d σ))

def crtF (m N : ℕ) : ℤ := (m : ℤ) * (((m : ZMod N)⁻¹).val : ℤ)

def sigN (m N : ℕ) : SL(2, ℤ) :=
  ⟨!![1 - crtF m N ^ 2, crtF m N ^ 3 - 2 * crtF m N; crtF m N, 1 - crtF m N ^ 2], by
    rw [Matrix.det_fin_two_of]; ring⟩

def wMat (l N : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := (sigN l N : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1]

def wB (X : Tower Ω ε) (l N : ℕ) [Fact l.Prime] : X.Fn l →ₗ[ℤ_[l]] X.Fn l := X.act l (wMat l N)

def clsBT (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (σ : Ω ≃ₐ[ℚ] Ω) : X.Fn l :=
  wB X l N (clsZT X l n r N x c d k σ)

def shArg (M : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod M)ˣ) : Ω ≃ₐ[ℚ] Ω :=
  (repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹)

def YBc (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (s : Ω ≃ₐ[ℚ] Ω)
    (y : (ZMod (topM l n r N))ˣ) : X.Fn l :=
  X.galB l (repM (topM l n r N) y)
    (clsBT X l n r N x c d k ((repM (topM l n r N) y)⁻¹ * s * repM (topM l n r N) (y * (cycM (topM l n r N) s)⁻¹)))

def YBr (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) :
    (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → X.Fn l :=
  GlobalTheory.KA.push (redM l n r N) (YBc X l n r N x c d k)

def IsZetaB (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (ρ : R2 Ω l)
    (N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (cf : Coef l)
    (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) : Prop :=
  ∀ r n : ℕ, ∃ β : (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → X.Fn l, (∀ s y, β s y ∈ X.B N l (k - 2)) ∧
    (∀ s y u, (β s y - YBr X l n r N x c d k s y) u ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))) ∧
    ∃ b : (ZMod (l ^ r))ˣ → Fin 2 → Qbar l, (∀ y i, b y i ∈ cf.O) ∧ ∀ s y,
      Cv n (Y r s y) (pr (β s y) + (mat ρ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y))

theorem Gamma_le_Gamma0 {l M : ℕ} (h : l ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma0 l := fun γ hγ => by
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact (Int.natCast_dvd_natCast.2 h).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 hγ.2.2.1)

theorem crtF_mod_left (m N : ℕ) : ((crtF m N : ℤ) : ZMod m) = 0 := by
  simp [crtF]

theorem crtF_mod_right {m N : ℕ} [NeZero N] (h : Nat.Coprime m N) : ((crtF m N : ℤ) : ZMod N) = 1 := by
  simp only [crtF, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  exact ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime m N).2 h)

theorem sigN_mem_Gamma (m N : ℕ) : sigN m N ∈ CongruenceSubgroup.Gamma m := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp [sigN, crtF_mod_left]

theorem det_wMat (l N : ℕ) : (wMat l N).det = N := by
  rw [wMat, Matrix.det_mul, (sigN l N).2, Matrix.det_fin_two_of]
  simp

theorem exists_wMat_mul {l N : ℕ} [NeZero N] (h : Nat.Coprime l N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gam N l) :
    ∃ γ' ∈ Gam N l, wMat l N * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * wMat l N := by
  obtain ⟨h1, h0⟩ := hγ
  obtain ⟨h00, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem _ _).1 h1
  have hl : ((γ 1 0 : ℤ) : ZMod l) = 0 := CongruenceSubgroup.Gamma0_mem.1 h0
  obtain ⟨t, ht⟩ : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 h10
  have htl : (t : ZMod l) = 0 := by
    rw [ht, Int.cast_mul, Int.cast_natCast] at hl
    exact (((ZMod.isUnit_iff_coprime N l).2 h.symm).mul_right_eq_zero).1 hl
  let δ : SL(2, ℤ) := ⟨!![γ 0 0, N * γ 0 1; t, γ 1 1], by
    have e := γ.2
    rw [Matrix.det_fin_two] at e
    rw [Matrix.det_fin_two_of]
    have e' : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := e
    rw [ht] at e'
    linarith⟩
  have hδ : !![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (δ : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [δ, Matrix.mul_apply, Fin.sum_univ_two, ht] <;> ring
  refine ⟨sigN l N * δ * (sigN l N)⁻¹, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · have hf := crtF_mod_right h
    have hc : ((sigN l N * δ * (sigN l N)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        !![1 - crtF l N ^ 2, crtF l N ^ 3 - 2 * crtF l N; crtF l N, 1 - crtF l N ^ 2] * !![γ 0 0, N * γ 0 1; t, γ 1 1] *
          Matrix.adjugate !![1 - crtF l N ^ 2, crtF l N ^ 3 - 2 * crtF l N; crtF l N, 1 - crtF l N ^ 2] := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
      rfl
    refine (CongruenceSubgroup.Gamma1_mem _ _).2 ⟨?_, ?_, ?_⟩ <;> rw [hc] <;>
      simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hf, h00, h11] <;> norm_num
  · have hσ := Gamma_le_Gamma0 (dvd_refl l) (sigN_mem_Gamma l N)
    exact mul_mem (mul_mem hσ (CongruenceSubgroup.Gamma0_mem.2 htl)) (inv_mem hσ)
  · rw [wMat, Matrix.mul_assoc, hδ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]

theorem vecMul_gR (l N : ℕ) [Fact l.Prime] (hN : (N : ZMod l) ≠ 0) (r₀ : ZMod l) :
    (![r₀, 1] : Fin 2 → ZMod l) ᵥ* ((GlobalTheory.ZetaB.gR l N r₀ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod l))) =
      ![0, 1] := by
  ext i
  fin_cases i <;> simp [GlobalTheory.ZetaB.gR, Matrix.vecMul, dotProduct, Fin.sum_univ_two, GlobalTheory.ZetaB.cR_mod l N hN]

def lnFn (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) : Submodule ℤ_[l] (X.Fn l) :=
  Submodule.pi Set.univ fun _ => (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))

theorem mem_lnFn (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (b : X.Fn l) :
    b ∈ lnFn X l n ↔ ∀ u, b u ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) :=
  ⟨fun h u => h u (Set.mem_univ u), fun h u _ => h u⟩

theorem act_mem_lnFn (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {n : ℕ} (m : Matrix (Fin 2) (Fin 2) ℤ) {b : X.Fn l}
    (hb : b ∈ lnFn X l n) : X.act l m b ∈ lnFn X l n :=
  (mem_lnFn X l n _).2 fun _ => Submodule.smul_top_le_comap_smul_top _ (X.kmap l _) ((mem_lnFn X l n _).1 hb _)

theorem kmap_clsHat (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) (a : X.K) :
    X.kmap l φ (GlobalTheory.ZetaB.clsHat X l a) = GlobalTheory.ZetaB.clsHat X l (φ a) := by
  have hu : Units.map φ.toMonoidHom (GlobalTheory.ZetaB.unitOf X a) = GlobalTheory.ZetaB.unitOf X (φ a) := by
    by_cases h : a = 0
    · subst h
      rw [map_zero, GlobalTheory.ZetaB.unitOf_zero, map_one]
    · apply Units.ext
      rw [GlobalTheory.ZetaB.unitOf_val X ((map_ne_zero φ).2 h), Units.coe_map, GlobalTheory.ZetaB.unitOf_val X h]
      rfl
  unfold Tower.kmap GlobalTheory.ZetaB.clsHat
  simp only [LinearMap.restrictScalars_apply]
  rw [AdicCompletion.map_of, LinearMap.baseChange_tmul, ← hu]
  rfl

theorem toGQ_coe_SL (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by rw [γ.2]; exact one_pos
  unfold toGQ
  rw [dif_pos h]
  exact Subtype.ext (Units.ext rfl)

theorem act_act_SL (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (γ γ' : SL(2, ℤ)) (b : X.Fn l) :
    X.act l (γ' : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b) =
      X.act l ((γ * γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b :=
  Tower.act_act Ω ε X l _ _ (by rw [γ.2]; exact one_pos) (by rw [γ'.2]; exact one_pos) b

def InvMod (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (H : Subgroup SL(2, ℤ)) (b : X.Fn l) : Prop :=
  ∀ γ ∈ H, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b - b ∈ lnFn X l n

theorem InvMod.act_congr {X : Tower Ω ε} {l : ℕ} [Fact l.Prime] {n : ℕ} {H : Subgroup SL(2, ℤ)} {b : X.Fn l}
    (hb : InvMod X l n H b) {m m' : SL(2, ℤ)} (h : m * m'⁻¹ ∈ H) :
    X.act l (m : Matrix (Fin 2) (Fin 2) ℤ) b - X.act l (m' : Matrix (Fin 2) (Fin 2) ℤ) b ∈ lnFn X l n := by
  have e := act_mem_lnFn X l (m' : Matrix (Fin 2) (Fin 2) ℤ) (hb _ h)
  rwa [map_sub, act_act_SL, inv_mul_cancel_right] at e

theorem invMod_secT (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {n M : ℕ} (hM : l ^ n ∣ M) (w : ℕ) {a : X.K}
    (ha : a ∈ topL X M) : InvMod X l n (CongruenceSubgroup.Gamma M) (secT X l w a) := by
  intro γ hγ
  rw [mem_lnFn]
  intro u
  have h1 : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (secT X l w a) u =
      ((mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0) ^ w • GlobalTheory.ZetaB.clsHat X l a := by
    show X.kmap l _ (_ • _) = _
    rw [map_smul, kmap_clsHat, toGQ_coe_SL]
    congr 2
    exact (mem_lev_iff X _ a).1 ha γ hγ
  rw [Pi.sub_apply, h1]
  show _ - (u 0) ^ w • GlobalTheory.ZetaB.clsHat X l a ∈ _
  rw [← sub_smul]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine Dvd.dvd.trans ?_ (sub_dvd_pow_sub_pow _ _ w)
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  have hd : ∀ a : ℤ, (a : ZMod M) = 0 → (l : ℤ_[l]) ^ n ∣ (a : ℤ_[l]) := fun a h => by
    have := (Int.natCast_dvd_natCast.2 hM).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 h)
    have e := map_dvd (Int.castRingHom ℤ_[l]) this
    simpa using e
  have e : (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0 - u 0 =
      ((γ 0 0 - 1 : ℤ) : ℤ_[l]) * u 0 + ((γ 0 1 : ℤ) : ℤ_[l]) * u 1 := by
    simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [e]
  exact dvd_add ((hd _ (by push_cast; rw [hγ.1, sub_self])).mul_right _) ((hd _ hγ.2.1).mul_right _)

theorem InvMod.wB {X : Tower Ω ε} {l N : ℕ} [Fact l.Prime] [NeZero N] (h : Nat.Coprime l N) {n : ℕ} {b : X.Fn l}
    (hb : InvMod X l n (Gam N l) b) : InvMod X l n (Gam N l) (wB X l N b) := by
  intro γ hγ
  obtain ⟨γ', hγ', e⟩ := exists_wMat_mul h hγ
  have hw : 0 < (wMat l N).det := by rw [det_wMat]; exact_mod_cast NeZero.pos N
  have h1 := act_mem_lnFn X l (wMat l N) (hb γ' hγ')
  rw [map_sub, Tower.act_act Ω ε X l _ _ (by rw [γ'.2]; exact one_pos) hw, ← e,
    ← Tower.act_act Ω ε X l _ _ hw (by rw [γ.2]; exact one_pos)] at h1
  exact h1

theorem cycM_apply [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] (s : Ω ≃ₐ[ℚ] Ω) {z : Ω} (hz : z ^ M = 1) :
    s z = z ^ (cycM M s : ZMod M).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have h : ∃ y : (ZMod M)ˣ, ∀ z : Ω, z ^ M = 1 → s z = z ^ (y : ZMod M).val := by
    refine ⟨hζ.autToPow ℚ s, fun z hz => ?_⟩
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
    rw [map_pow, ← hζ.autToPow_spec ℚ s, ← pow_mul, ← pow_mul, mul_comm]
  exact cycM_spec M s h z hz

theorem repM_apply [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] (y : (ZMod M)ˣ) {z : Ω} (hz : z ^ M = 1) :
    repM (Ω := Ω) M y z = z ^ (y : ZMod M).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have h : ∃ s : Ω ≃ₐ[ℚ] Ω, ∀ z : Ω, z ^ M = 1 → s z = z ^ (y : ZMod M).val := by
    have h2 := hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime y)
    have hm : ∀ {ξ : Ω}, IsPrimitiveRoot ξ M → Polynomial.cyclotomic M ℚ = minpoly ℚ ξ := fun hξ =>
      minpoly.eq_of_irreducible_of_monic (Polynomial.cyclotomic.irreducible_rat (NeZero.pos M))
        (by rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
            exact hξ.isRoot_cyclotomic (NeZero.pos M)) (Polynomial.cyclotomic.monic M ℚ)
    have h3 : minpoly ℚ (ζ ^ (y : ZMod M).val) = minpoly ℚ ζ := (hm h2).symm.trans (hm hζ)
    obtain ⟨s, hs⟩ := (Normal.minpoly_eq_iff_mem_orbit Ω).1 h3
    refine ⟨s, fun z hz => ?_⟩
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
    have hs' : s ζ = ζ ^ (y : ZMod M).val := hs
    rw [map_pow, hs', ← pow_mul, ← pow_mul, mul_comm]
  exact repM_spec M y h z hz

theorem shArg_mem_fixMu [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod M)ˣ) :
    shArg M s y ∈ fixMu Ω M := by
  rw [mem_fixMu_iff]
  intro z hz
  have hp : ∀ a b : ZMod M, (z ^ a.val) ^ b.val = z ^ (a * b).val := fun a b => by
    rw [← pow_mul, ZMod.val_mul, ← pow_eq_pow_mod _ hz]
  have hz' : ∀ a : ℕ, (z ^ a) ^ M = 1 := fun a => by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
  unfold shArg
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, repM_apply M _ hz, cycM_apply M s (hz' _), hp, ← Units.val_mul,
    inv_mul_cancel_right, ← repM_apply (Ω := Ω) M y hz, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

example : (sigN 3 5 : Matrix (Fin 2) (Fin 2) ℤ) = !![-35, 204; 6, -35] := by
  have h : crtF 3 5 = 6 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have e : (((3 : ℕ) : ZMod 5))⁻¹ = 2 := inv_eq_of_mul_eq_one_right (by decide +revert)
    rw [crtF, e]
    rfl
  simp [sigN, h]

example (l N : ℕ) [Fact l.Prime] (hN : (N : ZMod l) ≠ 0) (r₀ : ZMod l) :
    (![-r₀, -1] : Fin 2 → ZMod l) ᵥ* ((GlobalTheory.ZetaB.gR l N r₀ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod l))) =
      -![0, 1] := by
  rw [← vecMul_gR l N hN r₀, ← Matrix.neg_vecMul]
  congr 1
  ext i
  fin_cases i <;> simp

example (l N : ℕ) (r₀ : ZMod l) :
    (![1, 0] : Fin 2 → ℤ) ᵥ* (GlobalTheory.ZetaB.gR l N r₀ : Matrix (Fin 2) (Fin 2) ℤ) = ![1, 0] := by
  ext i
  fin_cases i <;> simp [GlobalTheory.ZetaB.gR, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

example (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.K) :
    secT X l 1 a ![1, 0] = GlobalTheory.ZetaB.clsHat X l a ∧ secT X l 1 a ![0, 1] = 0 := by
  simp [secT]

example (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (w : ℕ) (a : X.K) :
    X.galB l s (secT X l w a) = secT X l w (X.gal s a) := by
  unfold secT
  rw [galB_section_zero, kmap_clsHat]

end GlobalTheory.K4
