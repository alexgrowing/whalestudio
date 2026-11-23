import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExponentialInjectivity.DgPtCgr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PtTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.EOmZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpecAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SiegelAdmissibleToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

private theorem cyc_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {m M' : ℕ} (hm : 0 < m)
    (h : m ∣ M') (s : Ω ≃ₐ[ℚ] Ω) (hs : s ∈ fixMu Ω M') : cyc m s = 1 := by
  have hfix : ∀ z : Ω, z ^ m = 1 → s z = z := by
    intro z hz
    obtain ⟨k, rfl⟩ := h
    exact (mem_fixMu_iff s).1 hs z (by rw [pow_mul, hz, one_pow])
  rcases Nat.lt_or_ge 1 m with hm1 | hm1
  · haveI : Fact (1 < m) := ⟨hm1⟩
    have hspec : ∃ y : ZMod m, ∀ z : Ω, z ^ m = 1 → s z = z ^ y.val :=
      ⟨1, fun z hz => by rw [hfix z hz, ZMod.val_one, pow_one]⟩
    have hy : ∀ z : Ω, z ^ m = 1 → s z = z ^ (cyc m s).val := Classical.epsilon_spec hspec
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    have hζ := isPrimitiveRoot_eOm ε hm.ne'
    have h1 := hy _ hζ.pow_eq_one
    rw [hfix _ hζ.pow_eq_one] at h1
    have hv : (cyc m s).val = 1 :=
      hζ.pow_inj (ZMod.val_lt _) hm1 (by rw [pow_one]; exact h1.symm)
    rw [← ZMod.natCast_zmod_val (cyc m s), hv, Nat.cast_one]
  · have hm2 : m = 1 := by omega
    subst hm2
    exact Subsingleton.elim _ _

private theorem pow_val_one {K : Type} [Field K] {m : ℕ} (hm : 0 < m) (f : Kˣ) : ∃ h : Kˣ, f ^ (1 : ZMod m).val = f * h ^ m := by
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · refine ⟨1, ?_⟩
    haveI : Fact (1 < m) := ⟨h1⟩
    simp [ZMod.val_one]
  · have hm1 : m = 1 := by omega
    subst hm1
    refine ⟨f⁻¹, ?_⟩
    rw [show (1 : ZMod 1).val = 0 by decide]
    simp

private theorem key {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {m : ℕ} (hm : 0 < m)
    {τ : X.K ≃+* X.K} {s : Ω ≃ₐ[ℚ] Ω} (hτ : admitted X τ s) (hs : cyc m s = 1) {u v : X.K} (hu : τ u = u) (hv : τ v = v) {P Q : Pt X m}
    (hP : IsPt X m u v P) (hQ : IsPt X m u v Q) {a F F' : X.Kˣ} (ha : Mv X m (RingEquiv.refl _) 1 Q P a)
    (hF : Mv X m τ s Q Q F) (hF' : Mv X m τ s P P F') : ∃ h : X.Kˣ, F * a = unU X τ a * F' * h ^ m := by
  have hadm1 : admitted X (RingEquiv.refl X.K) 1 := (admB Ω ε X).2.2.1
  have hPτ : IsPt X m (τ u) (τ v) P := by rw [hu, hv]; exact hP
  have hQτ : IsPt X m (τ u) (τ v) Q := by rw [hu, hv]; exact hQ
  have c1 := mvComp Ω ε X m hm (RingEquiv.refl X.K) τ 1 s hadm1 hτ u v Q P P hQ hP hPτ a F' ha hF'
  have c2 := mvComp Ω ε X m hm τ (RingEquiv.refl X.K) s 1 hτ hadm1 u v Q Q P hQ hQτ hPτ F a hF ha
  have e1 : (RingEquiv.refl X.K).trans τ = τ := RingEquiv.ext fun _ => rfl
  have e2 : τ.trans (RingEquiv.refl X.K) = τ := RingEquiv.ext fun _ => rfl
  rw [e1, mul_one] at c1
  rw [e2, one_mul] at c2
  have hc1 : cyc m (1 : Ω ≃ₐ[ℚ] Ω) = 1 := ((lgB Ω ε X m hm).2.2.2.2.2.2 1 1).2.1
  obtain ⟨h, hh⟩ := ((mvEx Ω ε X m hm τ s hτ u v Q hQ).2.2.2 P hPτ _ _ c1).1 c2
  rw [hc1, hs] at hh
  have hrefl : unU X (RingEquiv.refl X.K) F = F := Units.ext rfl
  rw [hrefl] at hh
  obtain ⟨h1, hh1⟩ := pow_val_one hm F
  obtain ⟨h2, hh2⟩ := pow_val_one hm (unU X τ a)
  rw [hh1, hh2] at hh
  refine ⟨h2 * h * h1⁻¹, ?_⟩
  rw [mul_pow, mul_pow, inv_pow, ← mul_left_inj (h1 ^ m)]
  calc F * a * h1 ^ m = F * h1 ^ m * a := by rw [mul_right_comm]
    _ = _ := hh
    _ = _ := by rw [mul_right_comm (unU X τ a)]; group

private theorem mem_gamma_of_dvd_of_mem_gamma' {N N' : ℕ} (h : N ∣ N') {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N') : γ ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have hc := fun (z : ℤ) => map_intCast (ZMod.castHom h (ZMod N)) z
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hc, h1, map_one]
  · rw [← hc, h2, map_zero]
  · rw [← hc, h3, map_zero]
  · rw [← hc, h4, map_one]

theorem UpperTheory.V.Z.Kato.Sym.pTop : UpperTheory.V.Z.Kato.Sym.PTop := by
  unfold UpperTheory.V.Z.Kato.Sym.PTop
  intro Ω _ _ _ ε X l n c d k M M' hl hc hd hc6 hd6 hLv hk hM' hkM hlM t w ht hw x y hxy x' y' hx' hy'
  have hm : 0 < l ^ n := pow_pos hl.pos n
  obtain ⟨hM, hcM, hdM⟩ := hLv
  have hMM' : M ∣ M' := (Dvd.intro_left k rfl).trans hkM
  have hadm := admB Ω ε X
  obtain ⟨hx0, hy0, -, -⟩ := (rowB Ω M hM).2.1 x y hxy
  obtain ⟨hUx, hslx, hgalx, hsix⟩ := sgB Ω ε X c M hc hc6 hM hcM x hx0
  obtain ⟨hUy, hsly, hgaly, hsiy⟩ := sgB Ω ε X d M hd hd6 hM hdM y hy0
  obtain ⟨hgd1, hgd2, hgd3⟩ := galDg Ω ε X k hk
  obtain ⟨Q, hQ⟩ := PC.dgPt Ω ε X (l ^ n) c d k M hm hc hd hc6 hd6 ⟨hM, hcM, hdM⟩ hk t w ht hw
  obtain ⟨hQxy, hQgal, hQsl⟩ := hQ x y hxy
  have hfixU : ∀ s ∈ fixMu Ω M', ∀ z : Row M, gr M s z = z := by
    intro s hs z
    change ![z 0, cyc M s * z 1] = z
    rw [cyc_one X hM hMM' s hs, one_mul]
    funext i
    fin_cases i <;> rfl
  have hmemF : ∀ f : X.K, (∀ γ ∈ CongruenceSubgroup.Gamma M', X.sl (ofSL γ) f = f) →
      (∀ s ∈ fixMu Ω M', X.gal s f = f) → f ∈ topF X M' := by
    intro f h1 h2
    refine Subfield.mem_inf.2 ⟨(mem_lev_iff X _ f).2 h1, ?_⟩
    simp only [Subfield.mem_iInf]
    intro s hs
    exact h2 s hs
  have hgu : ∀ s ∈ fixMu Ω M', X.gal s (X.sl (dg k) (sg X c M x)) = X.sl (dg k) (sg X c M x) := by
    intro s hs
    rw [hgd1 s, hgalx s, hfixU s hs x]
  have hgv : ∀ s ∈ fixMu Ω M', X.gal s (X.sl (dg k) (sg X d M y)) = X.sl (dg k) (sg X d M y) := by
    intro s hs
    rw [hgd1 s, hgaly s, hfixU s hs y]
  have hslu : ∀ γ ∈ CongruenceSubgroup.Gamma M',
      X.sl (ofSL γ) (X.sl (dg k) (sg X c M x)) = X.sl (dg k) (sg X c M x) := by
    intro γ hγ
    obtain ⟨γ', hγ', hcomm⟩ := hgd3 M γ (mem_gamma_of_dvd_of_mem_gamma' hkM hγ)
    rw [hgd2 γ γ' hcomm, hslx, (rowB Ω M hM).2.2.1 γ' x hγ']
  have hslv : ∀ γ ∈ CongruenceSubgroup.Gamma M',
      X.sl (ofSL γ) (X.sl (dg k) (sg X d M y)) = X.sl (dg k) (sg X d M y) := by
    intro γ hγ
    obtain ⟨γ', hγ', hcomm⟩ := hgd3 M γ (mem_gamma_of_dvd_of_mem_gamma' hkM hγ)
    rw [hgd2 γ γ' hcomm, hsly, (rowB Ω M hM).2.2.1 γ' y hγ']
  have hIu : IsU X (X.sl (dg k) (sg X c M x)) :=
    (hadm.2.2.2.2.2.1 _ _ (hadm.1 (dg k))).1 _ hUx
  have hIv : IsU X (X.sl (dg k) (sg X d M y)) :=
    (hadm.2.2.2.2.2.1 _ _ (hadm.1 (dg k))).1 _ hUy
  obtain ⟨P, hP, hPγ, hPs⟩ := ptTop Ω ε X l n M' hl hM' hlM _ _ hIu hIv
    (hmemF _ hslu hgu) (hmemF _ hslv hgv)
  obtain ⟨a, haU, ha⟩ :=
    (mvEx Ω ε X (l ^ n) hm (RingEquiv.refl X.K) 1 hadm.2.2.1 _ _ (Q x y) hQxy).1 P hP
  rw [hsix x' hx', hsiy y' hy']
  refine ⟨a, haU, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨γ', hγ', hcomm⟩ := hgd3 M γ (mem_gamma_of_dvd_of_mem_gamma' hkM hγ)
    have hF := hQsl γ γ' hcomm
    rw [(rowB Ω M hM).2.2.1 γ' x hγ', (rowB Ω M hM).2.2.1 γ' y hγ'] at hF
    obtain ⟨h, hh⟩ := key X hm (hadm.1 (ofSL γ)) ((lgB Ω ε X (l ^ n) hm).2.2.2.2.2.2 1 1).2.1
      (hslu γ hγ) (hslv γ hγ) hP hQxy ha hF (hPγ γ hγ)
    rw [one_mul, mul_one] at hh
    refine ⟨h⁻¹, ?_⟩
    change unU X (slR X (ofSL γ)) a = a * h⁻¹ ^ (l ^ n)
    rw [inv_pow]
    exact eq_mul_inv_of_mul_eq hh.symm
  · intro s hs
    have hs' : s⁻¹ ∈ fixMu Ω M' := inv_mem hs
    have hF := hQgal s
    rw [hfixU _ hs' x, hfixU _ hs' y] at hF
    obtain ⟨f, hf, hf'⟩ := hPs s hs
    obtain ⟨h, hh⟩ := key X hm (hadm.2.1 s) (cyc_one X hm hlM s hs) (hgu s hs) (hgv s hs)
      hP hQxy ha hF hf'
    refine ⟨h, ?_⟩
    have hh' := congrArg (fun z : X.Kˣ => (z : X.K)) hh
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hh'
    change X.sl (dg k) (w s x y : X.K) * (a : X.K) = X.gal s (a : X.K) * (f : X.K) * (h : X.K) ^ (l ^ n) at hh'
    change X.sl (dg k) (w s x y : X.K) =
      wGen X M' l n (X.sl (dg k) (sg X c M x)) (X.sl (dg k) (sg X d M y)) s *
        (X.gal s (a : X.K) / (a : X.K)) * (h : X.K) ^ (l ^ n)
    rw [← hf]
    have ha0 : (a : X.K) ≠ 0 := a.ne_zero
    field_simp
    linear_combination hh'
