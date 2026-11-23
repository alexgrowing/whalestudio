import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankEqOfInjectiveOfSpan

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix nonZeroDivisors TensorProduct

namespace GlobalTheory.LatticeDatum

theorem exists_nsmul_mem {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module (𝓞 E) V] [Module E V]
    [IsScalarTower (𝓞 E) E V] (A B : Submodule (𝓞 E) V) (hA : A.FG)
    (hB : Submodule.span E (B : Set V) = ⊤) : ∃ N : ℕ, 0 < N ∧ ∀ x ∈ A, N • x ∈ B := by
  have h1 : ∀ v : V, ∃ N : ℕ, 0 < N ∧ N • v ∈ B := fun v => by
    have hv : v ∈ Submodule.span E (B : Set V) := by rw [hB]; trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ v hv
    rw [Submodule.span_eq] at ht
    have ht0 : (t : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero t
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {(t : 𝓞 E)}))
    refine ⟨Ideal.absNorm (Ideal.span {(t : 𝓞 E)}), Nat.pos_of_ne_zero ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ht0
    · rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hs, mul_smul]
      exact B.smul_mem s ht
  obtain ⟨S, rfl⟩ := hA
  choose n hn0 hn using h1
  refine ⟨∏ s ∈ S, n s, Finset.prod_pos fun s _ => hn0 s, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_coe.mp hx)
    rw [hk, mul_comm, mul_smul]
    exact B.toAddSubmonoid.nsmul_mem (hn x) k
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact B.add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact B.smul_mem c hx

theorem exists_factor {E V L L' : Type} [Field E] [NumberField E] [AddCommGroup V] [Module (𝓞 E) V] [Module E V]
    [IsScalarTower (𝓞 E) E V] [AddCommGroup L] [Module (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L']
    [Module.Finite (𝓞 E) L'] (φ : L →ₗ[𝓞 E] V) (φ' : L' →ₗ[𝓞 E] V) (hφ : Function.Injective φ)
    (hs : Submodule.span E (Set.range φ) = ⊤) :
    ∃ (N : ℕ) (ψ : L' →ₗ[𝓞 E] L), 0 < N ∧ ∀ x, φ (ψ x) = N • φ' x := by
  have hfg : (LinearMap.range φ').FG := by
    rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map φ'
  obtain ⟨N, hN, h⟩ := exists_nsmul_mem (LinearMap.range φ') (LinearMap.range φ) hfg
    (by rw [LinearMap.coe_range]; exact hs)
  choose g hg using fun x : L' => h (φ' x) ⟨x, rfl⟩
  refine ⟨N, ⟨⟨g, fun x y => hφ ?_⟩, fun a x => hφ ?_⟩, hN, hg⟩
  · rw [map_add, hg, hg, hg, map_add, smul_add]
  · rw [map_smul, hg, hg, map_smul, smul_comm]; rfl

theorem transport_complexStructure {O L L' : Type} [CommRing O] [AddCommGroup L] [Module O L]
    [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L')
    (ψ : L' →ₗ[O] L) (χ : L →ₗ[O] L') (K c : ℕ) (hK : 0 < K) (hc : 0 < c)
    (h1 : ∀ x, ψ (χ x) = K • x) (h2 : ∀ x, χ (ψ x) = K • x)
    (hB : ∀ x y, B (ψ x) (ψ y) = c * B' x y) (T : O → ℂ)
    (h : ∃ J : ℝ ⊗[ℤ] L →ₗ[ℝ] ℝ ⊗[ℤ] L, (∀ x, J (J x) = -x) ∧
      (∀ x y, B.baseChange ℝ (J x) (J y) = B.baseChange ℝ x y) ∧
      (∀ x, x ≠ 0 → 0 < B.baseChange ℝ (J x) x) ∧
      ∀ (a : O) (A : ℝ ⊗[ℤ] L →ₗ[ℝ] ℝ ⊗[ℤ] L) (t : ℂ), (∀ x : L, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) → t = T a →
        J ∘ₗ A = A ∘ₗ J ∧ LinearMap.trace ℝ _ A = 2 * t.re ∧ LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * t.im) :
    ∃ J : ℝ ⊗[ℤ] L' →ₗ[ℝ] ℝ ⊗[ℤ] L', (∀ x, J (J x) = -x) ∧
      (∀ x y, B'.baseChange ℝ (J x) (J y) = B'.baseChange ℝ x y) ∧
      (∀ x, x ≠ 0 → 0 < B'.baseChange ℝ (J x) x) ∧
      ∀ (a : O) (A : ℝ ⊗[ℤ] L' →ₗ[ℝ] ℝ ⊗[ℤ] L') (t : ℂ), (∀ x : L', A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) → t = T a →
        J ∘ₗ A = A ∘ₗ J ∧ LinearMap.trace ℝ _ A = 2 * t.re ∧ LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * t.im := by
  obtain ⟨J, hJ1, hJ2, hJ3, hJ4⟩ := h
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  let f : ℝ ⊗[ℤ] L' →ₗ[ℝ] ℝ ⊗[ℤ] L := ψ.toAddMonoidHom.toIntLinearMap.baseChange ℝ
  let g : ℝ ⊗[ℤ] L →ₗ[ℝ] ℝ ⊗[ℤ] L' := (K : ℝ)⁻¹ • χ.toAddMonoidHom.toIntLinearMap.baseChange ℝ
  have hf : ∀ (s : ℝ) x, f (s ⊗ₜ x) = s ⊗ₜ ψ x := fun s x => rfl
  have hg : ∀ (s : ℝ) x, g (s ⊗ₜ x) = (K : ℝ)⁻¹ • (s ⊗ₜ χ x) := fun s x => rfl
  have hfg : ∀ x, f (g x) = x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul s x =>
      rw [hg, map_smul, hf, h1, ← TensorProduct.mk_apply, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        inv_mul_cancel₀ hK', one_smul, TensorProduct.mk_apply]
  have hgf : ∀ x, g (f x) = x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul s x =>
      rw [hf, hg, h2, ← TensorProduct.mk_apply, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        inv_mul_cancel₀ hK', one_smul, TensorProduct.mk_apply]
  have hBf : ∀ x y, B.baseChange ℝ (f x) (f y) = c * B'.baseChange ℝ x y := fun x y => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', mul_add]
    | tmul s x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, hy, hy', mul_add]
      | tmul u y =>
        rw [hf, hf, LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hB]
        simp only [zsmul_eq_mul]; push_cast; ring
  let e : (ℝ ⊗[ℤ] L') ≃ₗ[ℝ] ℝ ⊗[ℤ] L :=
    LinearEquiv.ofLinear f g (LinearMap.ext hfg) (LinearMap.ext hgf)
  refine ⟨g ∘ₗ J ∘ₗ f, fun x => ?_, fun x y => ?_, fun x hx => ?_, fun a A t hA ht => ?_⟩
  · simp only [LinearMap.comp_apply, hfg, hJ1, map_neg, hgf]
  · apply mul_left_cancel₀ hc'.ne'
    rw [← hBf, ← hBf]
    simp only [LinearMap.comp_apply, hfg, hJ2]
  · have hx' : f x ≠ 0 := fun h0 => hx (by rw [← hgf x, h0, map_zero])
    have := hJ3 _ hx'
    rw [← mul_pos_iff_of_pos_left hc', ← hBf]
    simpa only [LinearMap.comp_apply, hfg] using this
  · obtain ⟨k1, k2, k3⟩ := hJ4 a (f ∘ₗ A ∘ₗ g) t (fun x => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hg, map_smul, hA, ← map_smul χ, ← hg, hfg]) ht
    refine ⟨LinearMap.ext fun x => ?_, ?_, ?_⟩
    · have := congrArg g (LinearMap.congr_fun k1 (f x))
      simpa only [LinearMap.comp_apply, hgf] using this
    · rw [← k2, ← LinearMap.trace_conj' A e]
      congr 1
    · rw [← k3, ← LinearMap.trace_conj' _ e]
      congr 1
      refine LinearMap.ext fun x => ?_
      change f (g (J (f (A (g x))))) = J (f (A (g x)))
      rw [hfg]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_add_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp [herm, add_mul, Finset.sum_add_distrib]

noncomputable def traceHerm (ξ : E) (G : Matrix (Fin r) (Fin r) E) : (Fin r → E) →+ (Fin r → E) →+ ℚ :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => Algebra.trace ℚ E (ξ * herm G x y))
    fun y y' => by rw [HermModel.herm_add_right, mul_add, map_add])
    fun x x' => AddMonoidHom.ext fun y => by
      change Algebra.trace ℚ E (ξ * herm G (x + x') y) =
        Algebra.trace ℚ E (ξ * herm G x y) + Algebra.trace ℚ E (ξ * herm G x' y)
      rw [herm_add_left, mul_add, map_add]

theorem exists_datum_of_embedding (H : Host E) (D : Datum H) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (hinj : Function.Injective φ)
    (hspan : Submodule.span E (Set.range φ) = ⊤)
    (hEF : ∀ x y, ((D.EF x y : ℤ) : ℚ) = traceHerm ξ Gm (φ x) (φ y))
    (L : Type) [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L]
    (φ' : L →ₗ[𝓞 E] (Fin r → E)) (hinj' : Function.Injective φ')
    (hspan' : Submodule.span E (Set.range φ') = ⊤)
    (hdual : ∀ v, (∀ y, ∃ n : ℤ, traceHerm ξ Gm v (φ' y) = n) ↔ v ∈ LinearMap.range φ') :
    ∃ (D' : Datum H) (φ'' : D'.La →ₗ[𝓞 E] (Fin r → E)), D'.p = D.p ∧ D'.q = D.q ∧
      LinearMap.range φ'' = LinearMap.range φ' ∧ Function.Injective φ'' ∧
      ∀ x y, ((D'.EF x y : ℤ) : ℚ) = traceHerm ξ Gm (φ'' x) (φ'' y) := by
  haveI := D.fin
  obtain ⟨N, ψ, hN, hψ⟩ := exists_factor φ φ' hinj hspan
  obtain ⟨M, χ, hM, hχ⟩ := exists_factor φ' φ hinj' hspan'
  have h1 : ∀ x, ψ (χ x) = (N * M) • x := fun x => hinj (by rw [hψ, hχ, map_nsmul, mul_smul])
  have h2 : ∀ x, χ (ψ x) = (N * M) • x := fun x => hinj' (by
    rw [hχ, hψ, map_nsmul, mul_comm, mul_smul])
  choose n hn using fun x : L => (hdual (φ' x)).mpr ⟨x, rfl⟩
  have hl : ∀ x x' y, n (x + x') y = n x y + n x' y := fun x x' y => by
    have := hn (x + x') y
    rw [map_add, map_add, AddMonoidHom.add_apply, hn, hn] at this
    exact_mod_cast this.symm
  have hr : ∀ x y y', n x (y + y') = n x y + n x y' := fun x y y' => by
    have := hn x (y + y')
    rw [map_add, map_add, hn, hn] at this
    exact_mod_cast this.symm
  let B : LinearMap.BilinForm ℤ L :=
    (AddMonoidHom.mk' (fun x => (AddMonoidHom.mk' (n x) (hr x)).toIntLinearMap)
      fun x x' => LinearMap.ext fun y => hl x x' y).toIntLinearMap
  have hB : ∀ x y, ((B x y : ℤ) : ℚ) = traceHerm ξ Gm (φ' x) (φ' y) := fun x y => (hn x y).symm
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hMQ : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hNN : ((N * N : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hN hN).ne'
  have hsc : ∀ x y, D.EF (ψ x) (ψ y) = (N * N : ℕ) * B x y := fun x y => by
    have := hEF (ψ x) (ψ y)
    rw [hψ, hψ, map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply, ← hB, nsmul_eq_mul, nsmul_eq_mul,
      ← mul_assoc] at this
    exact_mod_cast this
  have hmix : ∀ x y, (N : ℤ) * B x (χ y) = M * D.EF (ψ x) y := fun x y => by
    have e1 := hEF (ψ x) y
    have e2 := hB x (χ y)
    rw [hψ, map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul] at e1
    rw [hχ, map_nsmul, nsmul_eq_mul] at e2
    have : (N : ℚ) * (B x (χ y) : ℤ) = M * (D.EF (ψ x) y : ℤ) := by rw [e1, e2]; ring
    exact_mod_cast this
  have hbij : Function.Bijective B := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have h0 : ψ x = 0 := by
        apply D.unimod.1
        ext y
        have := hmix x y
        rw [hx, LinearMap.zero_apply, mul_zero] at this
        have hMZ : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
        rw [(mul_eq_zero.mp this.symm).resolve_left hMZ, map_zero, LinearMap.zero_apply]
      have h3 := hψ x
      rw [h0, map_zero, ← Nat.cast_smul_eq_nsmul ℚ] at h3
      exact hinj' (by rw [map_zero]; exact (smul_eq_zero.mp h3.symm).resolve_left hNQ)
    · intro f
      obtain ⟨x, hx⟩ := D.unimod.2 (f ∘ₗ χ.toAddMonoidHom.toIntLinearMap)
      have hx' : ∀ y, D.EF x y = f (χ y) := fun y => by rw [hx]; rfl
      have hv : ∀ z, traceHerm ξ Gm ((M : ℚ)⁻¹ • φ x) (φ' z) = f z := fun z => by
        have e1 := hEF x (ψ z)
        rw [hx', h2, map_nsmul, hψ, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at e1
        push_cast at e1
        have e2 : traceHerm ξ Gm (φ x) (φ' z) = M * traceHerm ξ Gm ((M : ℚ)⁻¹ • φ x) (φ' z) := by
          rw [← nsmul_eq_mul, ← AddMonoidHom.nsmul_apply, ← map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
            mul_inv_cancel₀ hMQ, one_smul]
        rw [e2, ← mul_assoc] at e1
        exact (mul_left_cancel₀ (mul_ne_zero hNQ hMQ) e1).symm
      obtain ⟨w, hw⟩ := (hdual _).mp fun z => ⟨f z, hv z⟩
      refine ⟨w, LinearMap.ext fun z => ?_⟩
      have := hB w z
      rw [hw, hv] at this
      exact_mod_cast this
  haveI : Module.IsTorsionFree (𝓞 E) L := Function.Injective.moduleIsTorsionFree φ' hinj' (map_smul φ')
  haveI : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective (𝓞 E) L := Module.Flat.projective_of_finitePresentation
  refine ⟨{ La := L, fin := inferInstance, proj := hproj, EF := B, alt := fun x => ?_, unimod := hbij,
            adj := fun a x y => ?_, p := D.p, q := D.q, rank := ?_, dom := ?_ }, φ', rfl, rfl, rfl, hinj', hB⟩
  · apply mul_left_cancel₀ hNN
    rw [← hsc, D.alt, mul_zero]
  · apply mul_left_cancel₀ hNN
    rw [← hsc, ← hsc, map_smul ψ, map_smul ψ, D.adj]
  · rw [← D.rank, HermModel.finrank_eq_of_injective_of_span (K := E) φ hinj hspan,
      HermModel.finrank_eq_of_injective_of_span (K := E) φ' hinj' hspan']
  · exact transport_complexStructure D.EF B ψ χ (N * M) (N * N) (Nat.mul_pos hN hM) (Nat.mul_pos hN hN)
      h1 h2 hsc _ D.dom

theorem exists_datum_of_selfDual (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E))
    (Λ' : Submodule (𝓞 E) (Fin r → E)) (_hξ : cc ξ = -ξ)
    (h : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧
      Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y)))
    (hfg : Λ'.FG) (hspan' : Submodule.span E (Λ' : Set (Fin r → E)) = ⊤)
    (hdual : ∀ v : Fin r → E, (∀ y ∈ Λ', ∃ n : ℤ, Algebra.trace ℚ E (ξ * herm Gm v y) = n) ↔ v ∈ Λ') :
    ∃ (D' : Datum H) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)), D'.p = D.p ∧ D'.q = D.q ∧ LinearMap.range φ' = Λ' ∧
      (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧
        Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ' x) (φ' y))) := by
  obtain ⟨hinj, hspan, hG, hdet, hEF⟩ := h
  haveI : Module.Finite (𝓞 E) Λ' := Module.Finite.iff_fg.mpr hfg
  obtain ⟨D', φ', hp, hq, hr, hi, hE⟩ := exists_datum_of_embedding H D ξ Gm φ hinj hspan hEF Λ' Λ'.subtype
    Λ'.injective_subtype (by rw [← LinearMap.coe_range, Submodule.range_subtype]; exact hspan')
    (fun v => by
      rw [Submodule.range_subtype, ← hdual]
      exact ⟨fun h y hy => h ⟨y, hy⟩, fun h y => h y y.2⟩)
  rw [Submodule.range_subtype] at hr
  exact ⟨D', φ', hp, hq, hr, hi, by rw [← LinearMap.coe_range, hr]; exact hspan', hG, hdet, hE⟩

end GlobalTheory.LatticeDatum
