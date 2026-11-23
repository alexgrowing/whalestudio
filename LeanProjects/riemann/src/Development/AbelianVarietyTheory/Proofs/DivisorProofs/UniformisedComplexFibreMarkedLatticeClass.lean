import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFormTwoSmulAndKerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingComplexValueUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT

section ExpLemmas

variable {g : ℕ} {Q : Type} [CommGroup Q] {L : Type} [AddCommGroup L]
  (e : (Fin g → ℂ) → Q) (P : L →+ (Fin g → ℂ))

theorem unifCls_exp_zero (hadd : ∀ z w, e (z + w) = e z * e w) : e 0 = 1 := by
  have h := hadd 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem unifCls_exp_nsmul (hadd : ∀ z w, e (z + w) = e z * e w) (n : ℕ) (z : Fin g → ℂ) :
    e (n • z) = e z ^ n := by
  induction n with
  | zero => simp [unifCls_exp_zero e hadd]
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

theorem unifCls_nsmul_inv {n : ℕ} (hn : 0 < n) (z : Fin g → ℂ) : n • ((n : ℂ)⁻¹ • z) = z := by
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ this, one_smul]

theorem unifCls_unit_iff (hker : ∀ z, e z = 1 ↔ z ∈ P.range) (hinj : Function.Injective P) {n : ℕ}
    (hn : 0 < n) (v : L) : e ((n : ℂ)⁻¹ • P v) = 1 ↔ ∃ w, v = n • w := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (hker _).1 h
    refine ⟨u, hinj ?_⟩
    rw [map_nsmul, hu, unifCls_nsmul_inv hn]
  · rintro ⟨w, rfl⟩
    refine (hker _).2 ⟨w, ?_⟩
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ this, one_smul]

theorem unifCls_mul (hadd : ∀ z w, e (z + w) = e z * e w) (n : ℕ) (v v' : L) :
    e ((n : ℂ)⁻¹ • P (v + v')) = e ((n : ℂ)⁻¹ • P v) * e ((n : ℂ)⁻¹ • P v') := by
  rw [map_add, smul_add, hadd]

theorem unifCls_eq_iff (hadd : ∀ z w, e (z + w) = e z * e w) (hker : ∀ z, e z = 1 ↔ z ∈ P.range)
    (hinj : Function.Injective P) {n : ℕ} (hn : 0 < n) (v v' : L) :
    e ((n : ℂ)⁻¹ • P v) = e ((n : ℂ)⁻¹ • P v') ↔ ∃ w, v = v' + n • w := by
  have h : e ((n : ℂ)⁻¹ • P v) = e ((n : ℂ)⁻¹ • P (v - v')) * e ((n : ℂ)⁻¹ • P v') := by
    rw [← unifCls_mul e P hadd, sub_add_cancel]
  rw [h, mul_eq_right, unifCls_unit_iff e P hker hinj hn]
  constructor
  · rintro ⟨w, hw⟩; exact ⟨w, by rw [← hw, add_sub_cancel]⟩
  · rintro ⟨w, hw⟩; exact ⟨w, by rw [hw, add_sub_cancel_left]⟩

theorem unifCls_pow (hadd : ∀ z w, e (z + w) = e z * e w) (hker : ∀ z, e z = 1 ↔ z ∈ P.range)
    {n : ℕ} (hn : 0 < n) (v : L) : e ((n : ℂ)⁻¹ • P v) ^ n = 1 := by
  rw [← unifCls_exp_nsmul e hadd, unifCls_nsmul_inv hn]
  exact (hker _).2 ⟨v, rfl⟩

theorem unifCls_of_pow (hadd : ∀ z w, e (z + w) = e z * e w) (hsurj : Function.Surjective e)
    (hker : ∀ z, e z = 1 ↔ z ∈ P.range) {n : ℕ} (hn : 0 < n) (q : Q) (hq : q ^ n = 1) :
    ∃ v, q = e ((n : ℂ)⁻¹ • P v) := by
  obtain ⟨z, rfl⟩ := hsurj q
  rw [← unifCls_exp_nsmul e hadd] at hq
  obtain ⟨v, hv⟩ := (hker _).1 hq
  refine ⟨v, ?_⟩
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hv, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ this, one_smul]

theorem unifCls_tower (hadd : ∀ z w, e (z + w) = e z * e w) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (v : L) :
    e (((n * m : ℕ) : ℂ)⁻¹ • P v) ^ m = e ((n : ℂ)⁻¹ • P v) := by
  rw [← unifCls_exp_nsmul e hadd, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 2
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

theorem unifCls_lift {Λ : Type} [AddCommGroup Λ] [Module.Free ℤ Λ] (hadd : ∀ z w, e (z + w) = e z * e w)
    (hsurj : Function.Surjective e) (hker : ∀ z, e z = 1 ↔ z ∈ P.range) (ev : Λ → Q)
    (hev : ∀ x y, ev (x + y) = ev x * ev y) {n : ℕ} (hn : 0 < n) (htors : ∀ x, ev x ^ n = 1) :
    ∃ φ : Λ →+ L, ∀ a, ev a = e ((n : ℂ)⁻¹ • P (φ a)) := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  have hex : ∀ i, ∃ v, ev (b i) = e ((n : ℂ)⁻¹ • P v) := fun i =>
    unifCls_of_pow e P hadd hsurj hker hn _ (htors _)
  choose v hv using hex
  refine ⟨(b.constr ℤ v).toAddMonoidHom, ?_⟩
  have hev0 : ev 0 = 1 := by
    have h := hev 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  let ψ : Λ →+ Additive Q :=
    { toFun := fun a => Additive.ofMul (ev a), map_zero' := by simp [hev0], map_add' := fun x y => by simp [hev] }
  let χ : Λ →+ Additive Q :=
    { toFun := fun a => Additive.ofMul (e ((n : ℂ)⁻¹ • P (b.constr ℤ v a))),
      map_zero' := by simp [unifCls_exp_zero e hadd],
      map_add' := fun x y => by
        show Additive.ofMul (e _) = Additive.ofMul (e _) + Additive.ofMul (e _)
        rw [map_add, map_add, smul_add, hadd]; rfl }
  have hψχ : ψ.toIntLinearMap = χ.toIntLinearMap := b.ext fun i => by
    simp [ψ, χ, hv, Module.Basis.constr_basis]
  intro a
  have := congrArg (fun F : Λ →ₗ[ℤ] Additive Q => Additive.toMul (F a)) hψχ
  simpa [ψ, χ] using this

end ExpLemmas

theorem unifCls_exp_one_iff {n : ℕ} (hn : 0 < n) (x : ℤ) :
    Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / n) = 1 ↔ (n : ℤ) ∣ x := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    have : (x : ℂ) = ((n * -k : ℤ) : ℂ) := by
      field_simp at hk
      push_cast
      linear_combination -hk
    exact_mod_cast this
  · rintro ⟨c, rfl⟩
    refine ⟨-c, ?_⟩
    push_cast
    field_simp

theorem unifCls_exp_eq_iff {n : ℕ} (hn : 0 < n) (x y : ℤ) :
    Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / n) = Complex.exp (-(2 * Real.pi * Complex.I) * (y : ℂ) / n) ↔
      (n : ℤ) ∣ x - y := by
  rw [← unifCls_exp_one_iff hn, ← div_eq_one_iff_eq (Complex.exp_ne_zero _), ← Complex.exp_sub]
  congr! 2
  push_cast
  ring

theorem unifCls_root {n : ℕ} (hn : 0 < n) (ζ : ℂˣ) (hζ : IsPrimitiveRoot ζ n) :
    ∃ v : ℤ, IsCoprime v n ∧ (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (v : ℂ) / n) := by
  have h := (Complex.isPrimitiveRoot_iff (ζ : ℂ) n hn.ne').1 (IsPrimitiveRoot.coe_units_iff.2 hζ)
  obtain ⟨i, -, hi, he⟩ := h
  refine ⟨-(i : ℤ), (Nat.isCoprime_iff_coprime.2 hi).neg_left, ?_⟩
  rw [← he]
  congr 1
  push_cast
  ring

theorem unifCls_bilin {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (E : LinearMap.BilinForm ℤ L) (hE : ∀ x, E x = 0 → x = 0) :
    ∃ k : ℕ, 0 < k ∧ ∀ f : L →ₗ[ℤ] ℤ, ∃ a, E a = k • f := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let M : Matrix (Module.Free.ChooseBasisIndex ℤ L) (Module.Free.ChooseBasisIndex ℤ L) ℤ :=
    Matrix.of fun i j => E (b i) (b j)
  have hsum : ∀ (c : Module.Free.ChooseBasisIndex ℤ L → ℤ) j, E (b.equivFun.symm c) (b j) = (c ᵥ* M) j := by
    intro c j
    simp [Module.Basis.equivFun_symm_apply, map_sum, Matrix.vecMul, dotProduct, M]
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    apply hv
    have hx : E (b.equivFun.symm v) = 0 := b.ext fun j => by
      rw [hsum, hvM]; simp
    have := hE _ hx
    have h3 := congrArg b.equivFun this
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h3
  refine ⟨M.det.natAbs ^ 2, by positivity, fun f => ?_⟩
  let w : Module.Free.ChooseBasisIndex ℤ L → ℤ := fun j => f (b j)
  refine ⟨b.equivFun.symm ((M.det • w) ᵥ* M.adjugate), b.ext fun j => ?_⟩
  rw [hsum, Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul, Matrix.vecMul_one]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, w]
  push_cast
  rw [sq_abs]
  ring

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem unifAt_cls : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e,
    0 < N → N.Coprime p → UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → ∃ t', D.Cls N D' t' ∧ ∀ a, ∃ x, t' a = t a + N • x := by
  intro p _ D R _ b N σ ρ o h hL D' t P e hN hNp hU
  classical
  obtain ⟨-, hper, hexp, hker, hact, hweil, heta⟩ := hU
  have hadd : ∀ z w, e (z + w) = e z * e w := hexp.1
  have hsurj : Function.Surjective e := hexp.2.1
  have hlin : ∀ (c : D.O) x, P (c • x) = ρ c *ᵥ P x := hper.1
  have hinj : Function.Injective P := hper.2.1
  obtain ⟨I, hI⟩ := o.geom ℂ (𝟙 _) σ (Category.id_comp _)
  haveI := D.freeLa
  have hlift : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ φ : D.La →+ D'.La, ∀ a, I.ev n a = e ((n : ℂ)⁻¹ • P (φ a)) :=
    fun n hn hnp => unifCls_lift e P hadd hsurj hker (I.ev n) (I.add n) hn
      (fun x => (I.onto n hn hnp _).2 ⟨x, rfl⟩)
  have hroot : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ v : ℤ, IsCoprime v n ∧
      ((I.ζ n : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (v : ℂ) / n) :=
    fun n hn hnp => unifCls_root hn _ (I.ζ_prim n hn hnp)
  let f : ℕ → D.La →+ D'.La := fun n => if hn : 0 < n ∧ n.Coprime p then Classical.choose (hlift n hn.1 hn.2) else 0
  let ν : ℕ → ℤ := fun n => if hn : 0 < n ∧ n.Coprime p then Classical.choose (hroot n hn.1 hn.2) else 0
  have hf : ∀ (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) a, I.ev n a = e ((n : ℂ)⁻¹ • P (f n a)) := by
    intro n hn hnp a
    simp only [f, dif_pos (And.intro hn hnp)]
    exact Classical.choose_spec (hlift n hn hnp) a
  have hν : ∀ (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p), IsCoprime (ν n) n ∧
      ((I.ζ n : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν n : ℂ) / n) := by
    intro n hn hnp
    simp only [ν, dif_pos (And.intro hn hnp)]
    exact Classical.choose_spec (hroot n hn hnp)
  have heq : ∀ {n : ℕ}, 0 < n → ∀ v v' : D'.La,
      e ((n : ℂ)⁻¹ • P v) = e ((n : ℂ)⁻¹ • P v') ↔ ∃ w, v = v' + n • w :=
    fun hn v v' => unifCls_eq_iff e P hadd hker hinj hn v v'
  refine ⟨f N, ⟨⟨f, ν, rfl, ?_, ?_⟩, ?_⟩, ?_⟩
  ·
    intro n m hn hm hnm
    have hnp : n.Coprime p := (Nat.coprime_mul_iff_left.1 hnm).1
    refine ⟨?_, fun a => ?_⟩
    · have hz := I.ζ_pow n m hn hm hnm
      have hz' := congrArg (fun u : ℂˣ => (u : ℂ)) hz
      simp only [Units.val_pow_eq_pow_val] at hz'
      rw [(hν _ (Nat.mul_pos hn hm) hnm).2, (hν n hn hnp).2, ← Complex.exp_nat_mul] at hz'
      have : (m : ℂ) * (-(2 * Real.pi * Complex.I) * (ν (n * m) : ℂ) / ((n * m : ℕ) : ℂ)) =
          -(2 * Real.pi * Complex.I) * (ν (n * m) : ℂ) / n := by
        have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
        have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
        push_cast; field_simp
      rw [this] at hz'
      exact (unifCls_exp_eq_iff hn _ _).1 hz'
    · have ht := I.tower n m hn hm hnm a
      have e1 := hf _ (Nat.mul_pos hn hm) hnm a
      have e2 := hf n hn hnp a
      rw [e1, e2] at ht
      erw [unifCls_tower e P hadd hn hm] at ht
      exact (heq hn _ _).1 ht
  · intro n hn hnp
    refine ⟨(hν n hn hnp).1, fun c a => ?_, fun a => ?_, fun a' => ?_, fun a a' => ?_⟩
    · have hl := I.lin n c a
      erw [hf n hn hnp (c • a), hf n hn hnp a] at hl
      have h3 := hact c ((n : ℂ)⁻¹ • P (f n a))
      rw [Matrix.mulVec_smul, ← hlin] at h3
      exact (heq hn _ _).1 (hl.trans h3.symm)
    · have h1 := I.ker n hn hnp a
      erw [hf n hn hnp a, unifCls_unit_iff e P hker hinj hn] at h1
      exact h1
    · obtain ⟨x, hx⟩ := (I.onto n hn hnp (e ((n : ℂ)⁻¹ • P a'))).1 (unifCls_pow e P hadd hker hn a')
      rw [hf n hn hnp x] at hx
      obtain ⟨w, hw⟩ := (heq hn _ _).1 hx.symm
      exact ⟨x, w, hw⟩
    · have hiso := I.isom n hn hnp a a'
      rw [hf n hn hnp a, hf n hn hnp a'] at hiso
      have hw := hweil n (f n a) (f n a')
        (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF (f n a) (f n a') : ℂ) / n)) (Complex.exp_ne_zero _))
        hn rfl
      have hu := GlobalTheory.T.weilPairing_complex_value_unique (Sp ℂ) o.A D.g o.ab h _ hL (𝟙 _) n _ _ _ _ hiso hw
      have hu' := congrArg (fun u : ℂˣ => (u : ℂ)) hu
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at hu'
      rw [(hν n hn hnp).2, ← Complex.exp_int_mul] at hu'
      have : ((2 * D.EF a a' : ℤ) : ℂ) * (-(2 * Real.pi * Complex.I) * (ν n : ℂ) / n) =
          -(2 * Real.pi * Complex.I) * ((ν n * (2 * D.EF a a') : ℤ) : ℂ) / n := by
        push_cast; ring
      rw [this] at hu'
      have hd := (unifCls_exp_eq_iff hn _ _).1 hu'.symm
      have hpl : D.plat.EF a a' = 2 * D.EF a a' := by
        show ((2 : ℤ) • D.EF) a a' = 2 * D.EF a a'
        rfl
      rw [hpl]
      exact hd
  ·
    obtain ⟨E₁, hE, hcrit⟩ := GlobalTheory.T.diag_form_two_smul_and_ker_alt o.A D.g o.ab h o.P o.isLB o.rig₁ o.rig₂ o.symm o.ample e D'.La P D'.EF
      hexp hinj hker hweil
    obtain ⟨ee, hee, hkerP⟩ := o.kerP
    have hE₁ : ∀ x, E₁ x = 0 → x = 0 := fun x hx => D'.nondeg x fun y => by
      rw [hE]; simp [hx]
    obtain ⟨k, hk, hkf⟩ := unifCls_bilin E₁ hE₁
    refine ⟨E₁, hE, ee, hee, fun φ => ?_⟩
    obtain ⟨a, ha⟩ := hkf φ
    have hdiv : ∀ y, (k : ℤ) ∣ E₁ a y := fun y => ⟨φ y, by rw [ha]; simp⟩
    have hpow := hkerP (Over.mk (𝟙 (Sp ℂ))) (e ((k : ℂ)⁻¹ • P a)) ((hcrit k a hk).1 hdiv)
    have hpow' : e ((k : ℂ)⁻¹ • P (ee • a)) = 1 := by
      rw [map_nsmul, smul_comm, unifCls_exp_nsmul e hadd]; exact hpow
    obtain ⟨w, hw⟩ := (unifCls_unit_iff e P hker hinj hk _).1 hpow'
    refine ⟨w, LinearMap.ext fun y => ?_⟩
    have h1 := congrArg (fun x => E₁ x y) hw
    simp only [map_nsmul, LinearMap.smul_apply, ha, smul_eq_mul, nsmul_eq_mul] at h1
    have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    apply mul_left_cancel₀ hk0
    simp only [LinearMap.smul_apply, nsmul_eq_mul]
    linear_combination -h1
  · intro a
    have h3 : I.ev N a = e ((N : ℂ)⁻¹ • P (t a)) := (hI a).symm.trans (heta a)
    rw [hf N hN hNp a] at h3
    obtain ⟨w, hw⟩ := (heq hN _ _).1 h3
    exact ⟨w, hw⟩

end GlobalTheory.UPel.HT
