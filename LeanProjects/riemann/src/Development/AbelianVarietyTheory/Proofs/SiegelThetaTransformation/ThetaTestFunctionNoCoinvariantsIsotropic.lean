import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NeBotOfNorm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructurePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariantStatement

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors

namespace GlobalTheory.SW.Coinv

theorem exists_kill {G ι : Type} [AddCommGroup G] (B : AddSubgroup G) (t : Finset ι)
    (χ : ι → G → ℂ) (h0 : ∀ i, χ i 0 = 1) (hm : ∀ i u v, χ i (u + v) = χ i u * χ i v)
    (hne : ∀ i ∈ t, ∃ v ∈ B, χ i v ≠ 1) :
    ∃ (s : Finset G) (a : G → ℂ), (∀ v ∈ s, v ∈ B) ∧ ∑ v ∈ s, a v ≠ 0 ∧
      ∀ i ∈ t, ∑ v ∈ s, a v * χ i v = 0 := by
  choose! v hvB hv using hne
  let ev (f : G → ℂ) (h0 : f 0 = 1) (hm : ∀ u v, f (u + v) = f u * f v) :
      AddMonoidAlgebra ℂ B →ₐ[ℂ] ℂ := AddMonoidAlgebra.lift ℂ ℂ B
    { toFun := fun b => f (b.toAdd : B), map_one' := h0, map_mul' := fun a b => hm _ _ }
  let p : AddMonoidAlgebra ℂ B := ∏ i ∈ t.attach,
    (AddMonoidAlgebra.single ⟨v i, hvB i i.2⟩ 1 - algebraMap ℂ _ (χ i (v i)))
  have key (f : G → ℂ) (h0 : f 0 = 1) (hm : ∀ u v, f (u + v) = f u * f v) :
      ∑ x ∈ p.coeff.support.map (Function.Embedding.subtype _),
      (if h : x ∈ B then p.coeff ⟨x, h⟩ else 0) * f x = ∏ i ∈ t.attach, (f (v i) - χ i (v i)) := by
    have h1 : ev f h0 hm p = ∏ i ∈ t.attach, (f (v i) - χ i (v i)) := by
      simp only [p, map_prod, map_sub, AlgHom.commutes]
      simp [ev]
    rw [← h1, Finset.sum_map]
    simp [ev, AddMonoidAlgebra.lift_apply, Finsupp.sum]
  refine ⟨p.coeff.support.map (Function.Embedding.subtype _), fun x => if h : x ∈ B then p.coeff ⟨x, h⟩ else 0,
    fun x hx => ?_, ?_, fun i hi => ?_⟩
  · obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
    exact y.2
  · have := key (fun _ => 1) rfl (fun _ _ => (mul_one _).symm)
    simp only [mul_one] at this
    rw [this]
    exact Finset.prod_ne_zero_iff.2 fun i _ => sub_ne_zero.2 (hv i i.2).symm
  · rw [key (χ i) (h0 i) (hm i)]
    exact Finset.prod_eq_zero (Finset.mem_attach _ ⟨i, hi⟩) (sub_self _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r n g : ℕ} {X : Data E r}

theorem gen_of_red (D : Level X) {u : Fin r → Fin r → E} {k : GL (Fin r) (𝓞 E ⧸ D.𝔪)}
    (h : D.Red u k) : ∃ s : 𝓞 E, s - 1 ∈ D.𝔪 ∧
      ∀ x ∈ X.Λ, s • x ∈ Submodule.span (𝓞 E) (Set.range u) := by
  obtain ⟨k', hk', hc⟩ := h
  set Q := Submodule.span (𝓞 E) (Set.range u) ⊔ D.𝔪 • X.Λ with hQ
  have hb (i) : ∑ j, k' j i • D.β j ∈ Q := by
    obtain ⟨s, hs, hs'⟩ := hc i
    obtain ⟨a, ha, m, hm, ham⟩ := Ideal.isCoprime_iff_exists.1 hs
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have hΛ : ∑ j, k' j i • D.β j ∈ X.Λ := Submodule.sum_mem _ fun j _ => X.Λ.smul_mem _ (D.β_mem j)
    generalize ∑ j, k' j i • D.β j = b at hs' hΛ
    have : b = c • (s • u i - s • (u i - b)) + m • b := by
      rw [← smul_sub, sub_sub_cancel, smul_smul, ← add_smul, ham, one_smul]
    rw [this]
    exact Q.add_mem (Q.smul_mem _ (Q.sub_mem (Submodule.mem_sup_left (Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩))) (Submodule.mem_sup_right hs')))
      (Submodule.mem_sup_right (Submodule.smul_mem_smul hm hΛ))
  choose k'' hk'' using fun i j => Ideal.Quotient.mk_surjective
    (((k⁻¹ : GL (Fin r) (𝓞 E ⧸ D.𝔪)) : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) i j)
  have hone (j l) : ∑ i, k' j i * k'' i l - (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j l ∈ D.𝔪 := by
    rw [← Ideal.Quotient.eq, map_sum]
    have := congrFun (congrFun k.mul_inv j) l
    rw [Matrix.mul_apply, ← hk'] at this
    simp only [map_mul, hk'']
    refine this.trans ?_
    simp [Matrix.one_apply]
  have hβ (l) : D.β l ∈ Q := by
    have : D.β l = ∑ i, k'' i l • ∑ j, k' j i • D.β j -
        ∑ j, (∑ i, k' j i * k'' i l - (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j l) • D.β j := by
      simp only [sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
      simp [Matrix.one_apply, mul_comm]
    rw [this]
    exact Q.sub_mem (Q.sum_mem fun i _ => Q.smul_mem _ (hb i)) (Q.sum_mem fun j _ =>
      Submodule.mem_sup_right (Submodule.smul_mem_smul (hone j l) (D.β_mem j)))
  have hle : X.Λ ≤ Q := D.β_span.trans (sup_le (Submodule.span_le.2 (by
    rintro _ ⟨l, rfl⟩; exact hβ l)) le_sup_right)
  obtain ⟨s, hs, hs'⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup X.Λ_fg le_rfl hle
  exact ⟨s, hs, fun x hx => hs' (Submodule.smul_mem_pointwise_smul _ _ _ hx)⟩

theorem not_smul_idq {𝔞 𝔟 : Ideal (𝓞 E)} (h0 : 𝔟 ≠ ⊥) (h1 : 𝔟 ≠ ⊤) (hc : IsCoprime 𝔞 𝔟)
    {L : Lt E r} (hL : L.FG) {ξ : Fin r → E} (hξ : ξ ≠ 0) (hξL : ξ ∈ L) {u : 𝓞 E}
    (hu : IsCoprime (Ideal.span {u}) 𝔟) :
    ¬∀ α : E, α • ξ ∈ idq 𝔞 𝔟 L → u • α • ξ ∈ L := by
  intro h
  obtain ⟨t, ht, ht1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := E) h0 h1
  have htP : ∀ c ∈ 𝔟, ∃ b : 𝓞 E, (b : E) = t * (c : E) := fun c hc =>
    (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff
      (FractionalIdeal.coeIdeal_ne_zero.2 h0)).1 ht _ (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 E)⁰ hc))
  obtain ⟨a, ha, m, hm, ham⟩ := Ideal.isCoprime_iff_exists.1 (hu.mul_left hc)
  obtain ⟨a, ha', rfl⟩ := Ideal.mem_span_singleton_mul.1 ha
  let N : Lt E r := L ⊓ (Submodule.span E {ξ}).restrictScalars _
  have hN : N.FG := by
    have : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian _ hL
    exact hL.of_le inf_le_left
  have hint : IsIntegral (𝓞 E) (((u * a : 𝓞 E) : E) * t) := by
    refine isIntegral_of_smul_mem_submodule N (fun hb => hξ ?_) hN _ ?_
    · have : ξ ∈ N := ⟨hξL, Submodule.mem_span_singleton_self ξ⟩
      rwa [hb] at this
    · rintro x ⟨hx, hx'⟩
      refine ⟨?_, Submodule.smul_mem (Submodule.span E {ξ}) _ hx'⟩
      obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.1 hx'
      have h2 := h ((a : E) * t * β) fun c hc => by
        obtain ⟨b, hb⟩ := htP c hc
        have : c • ((a : E) * t * β) • ξ = a • b • β • ξ := by
          change (c : E) • (_ : Fin r → E) = (a : E) • (b : E) • (_ : Fin r → E)
          rw [smul_smul, smul_smul, smul_smul, hb]
          congr 1; ring
        rw [this]
        exact Submodule.smul_mem_smul ha' (L.smul_mem _ hx)
      have h3 : (((u * a : 𝓞 E) : E) * t) • β • ξ = u • ((a : E) * t * β) • ξ := by
        change _ = (u : E) • (_ : Fin r → E)
        rw [smul_smul, smul_smul]
        congr 1; push_cast; ring
      exact h3 ▸ h2
  obtain ⟨b, hb⟩ := htP m hm
  obtain ⟨c, hc⟩ := IsIntegralClosure.isIntegral_iff (A := 𝓞 E).1 (isIntegral_trans (R := ℤ) _ hint)
  refine ht1 ((FractionalIdeal.mem_one_iff _).2 ⟨c + b, ?_⟩)
  have h3 : ((u * a : 𝓞 E) : E) + (m : E) = 1 := by
    have := congrArg (algebraMap (𝓞 E) E) ham
    rwa [map_add, map_one] at this
  rw [map_add, hc]
  change _ + (b : E) = _
  rw [hb]
  linear_combination t * h3

theorem EF_line {ξ : Fin r → E} (h : herm X.Gm ξ ξ = 0) (a b : E) :
    EF X (a • ξ) (b • ξ) = 0 := by
  have : herm X.Gm (a • ξ) (b • ξ) = a * cc b * herm X.Gm ξ ξ := by
    simp only [herm, cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [EF_def, this, h]; simp

theorem row_vecMulVec (v : Fin n → E) (ξ : Fin r → E) (k : Fin n) :
    vecMulVec v ξ k = v k • ξ := by
  funext j; simp [vecMulVec_apply]

theorem exists_pairing (D : Level X) (hn : r ≤ n) (hX : SelfD X X.Λ) {M : ℕ}
    (hM : (M : 𝓞 E) ∈ D.𝔪) {ξ : Fin r → E} (hξ : ξ ≠ 0) {L : Lt E r} (hL : L ∈ D.lats)
    {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) {y : Matrix (Fin n) (Fin r) E} (hy : D.dat hn y ≠ 0) :
    ∃ v : Fin n → E, vecMulVec v ξ ∈ tens Λ (D.sh L) ∧
      ¬∃ m : ℤ, ∑ k, EF X (vecMulVec v ξ k) (y k) = m := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ : ∃ k : D.J, D.Red (fun i => y (Fin.castLE hn i)) k := by
    by_contra h
    exact hy (by rw [Level.dat, dif_neg fun h' => h h'.1])
  obtain ⟨s₁, hs₁, hgen⟩ := gen_of_red D hk
  obtain ⟨hLs, s₂, hs₂, -, hs₂'⟩ := hL
  obtain ⟨-, -, t, -, ht, -, ht'⟩ := hΛ
  obtain ⟨c, hc, hcξ⟩ : ∃ c : E, c ≠ 0 ∧ c • ξ ∈ L := by
    obtain ⟨N, hN, h⟩ := TensLat.exists_mul_le (B := Submodule.span (𝓞 E) {ξ})
      (Submodule.fg_span_singleton ξ) (TensLat.span_of_selfD X hLs)
    exact ⟨N, by simpa using hN, h ξ (Submodule.mem_span_singleton_self ξ)⟩
  have h0 : conjI D.𝔪 ≠ ⊥ := fun h => D.ne_bot (by
    rw [← Nbr.conjI_conjI D.𝔪, h, Nbr.conjI_eq, Ideal.map_bot])
  have h1 : conjI D.𝔪 ≠ ⊤ := fun h => D.proper (by
    rw [← Nbr.conjI_conjI D.𝔪, h, Nbr.conjI_eq, Ideal.map_top])
  have hu : IsCoprime (Ideal.span {s₂ * (Nbr.co s₁ * t)}) (conjI D.𝔪) := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton]
    refine hs₂.of_mul_right_right.mul_left (IsCoprime.mul_left ?_ ?_)
    · refine Ideal.isCoprime_iff_exists.2 ⟨_, Ideal.mem_span_singleton_self _, -(Nbr.co s₁ - 1),
        neg_mem (Nbr.mem_conjI.2 ?_), by ring⟩
      rwa [map_sub, Nbr.co_co, map_one]
    · obtain ⟨a, b, hab⟩ : IsCoprime (t : 𝓞 E) (M : 𝓞 E) := ht.cast
      refine Ideal.isCoprime_iff_exists.2 ⟨_, Ideal.mul_mem_left _ a
        (Ideal.mem_span_singleton_self _), _, Ideal.mul_mem_left _ b (Nbr.mem_conjI.2 ?_), hab⟩
      rwa [map_natCast]
  refine not_smul_idq h0 h1 D.cop hLs.1 (smul_ne_zero hc hξ) hcξ hu fun α hα => ?_
  have hrow (α : E) (hα : α • ξ ∈ D.sh L) (i : Fin n) :
      ∃ m : ℤ, EF X ((t : E) • α • ξ) (y i) = m := by
    obtain ⟨m, hm⟩ := hcon (α • (t : E) • Pi.single i 1) (by
      rw [smul_vecMulVec, ← vecMulVec_smul]
      exact TensLat.pure_mem (ht' _ (Submodule.subset_span ⟨i, rfl⟩)) hα)
    refine ⟨m, hm ▸ ?_⟩
    rw [Finset.sum_eq_single i (fun j _ hj => ?_) (by simp), row_vecMulVec]
    · simp [smul_smul, mul_comm]
    · rw [row_vecMulVec]
      change EFBil X _ _ = 0
      simp [hj]
  have hspan (x) (hx : x ∈ Submodule.span (𝓞 E) (Set.range fun i => y (Fin.castLE hn i))) :
      ∀ α : E, α • ξ ∈ D.sh L → ∃ m : ℤ, EF X ((t : E) • α • ξ) x = m := by
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact fun α hα => hrow α hα _
    | zero => exact fun α _ => ⟨0, by change EFBil X _ _ = _; simp⟩
    | add a b _ _ ha hb =>
      intro α hα
      obtain ⟨m, hm⟩ := ha α hα
      obtain ⟨m', hm'⟩ := hb α hα
      refine ⟨m + m', ?_⟩
      rw [Int.cast_add, ← hm, ← hm']
      exact (EFBil X _).map_add _ _
    | smul a x _ hx =>
      intro α hα
      obtain ⟨m, hm⟩ := hx (cc (a : E) * α) (by
        rw [mul_smul]; exact (D.sh L).smul_mem (Nbr.co a) hα)
      refine ⟨m, hm ▸ ?_⟩
      rw [mul_smul, smul_comm (t : E) (cc (a : E)), TensLat.EF_smul X (cc (a : E)), Nbr.cc_cc]
      rfl
  rw [smul_smul] at hα
  rw [smul_smul α, mul_smul]
  refine hs₂' _ ((hX.2 _).2 fun x hx => ?_)
  obtain ⟨m, hm⟩ := hspan _ (hgen x hx) _ hα
  refine ⟨m, hm ▸ ?_⟩
  rw [mul_smul]
  change EF X (cc (s₁ : E) • (t : E) • (_ : Fin r → E)) x = _
  rw [TensLat.EF_smul, Nbr.cc_cc]
  rfl

theorem phi_no_coinvariants : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ ξ : Fin r → E, ξ ≠ 0 → herm X.Gm ξ ξ = 0 → ∀ L ∈ D.lats, ∀ Λ ∈ Vset E n M, ∃ (s : Finset (Fin n → E)) (a : (Fin n → E) → ℂ), ∑ v ∈ s, a v ≠ 0 ∧ ∑ v ∈ s, a v • heisG X bas (vecMulVec v ξ) (D.phi bas hn v₀ L Λ) = 0 := by
  intro E _ _ _ r X g bas idx n hs hev D hn M hM0 hM v₀ hv₀ ξ hξ hiso L hL Λ hΛ
  obtain ⟨-, hvac, h3, -⟩ := GlobalTheory.T.levelTestFunction_finite_sum_equivariant E r X g bas idx n hs hev D hn M hM0 hM v₀ hv₀ L hL Λ hΛ
  obtain ⟨t, -, ht, hphi, -⟩ := h3 L hL
  have hX := (GlobalTheory.T.level_structure_properties E r X g bas idx n hs hev D hn).1.1
  rw [hphi]
  generalize unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)) = φ at hvac
  have law := fun y => ((heisG_laws E r X g bas idx n hs hev).2.2.2 y φ hvac.1).2.2.1
  let B : AddSubgroup (Fin n → E) := (tens Λ (D.sh L)).comap
    (AddMonoidHom.mk' (fun v => vecMulVec v ξ) fun u v => add_vecMulVec _ _ _)
  let χ : Matrix (Fin n) (Fin r) E → (Fin n → E) → ℂ := fun y v =>
    cexp (-((∑ k, EF X (vecMulVec v ξ k) (y k) : ℚ) * (2 * π * I)))
  obtain ⟨s, a, hsB, ha, hk⟩ := exists_kill B t χ
    (fun y => by
      have this (k : Fin n) : EF X (vecMulVec (0 : Fin n → E) ξ k) (y k) = 0 := by
        rw [row_vecMulVec]; change EFBil X _ _ = 0; simp
      simp only [χ, this]; simp)
    (fun y u v => by
      have this (k : Fin n) : EF X (vecMulVec (u + v) ξ k) (y k) =
          EF X (vecMulVec u ξ k) (y k) + EF X (vecMulVec v ξ k) (y k) := by
        simp only [row_vecMulVec, Pi.add_apply, add_smul]
        exact (EFBil X).map_add₂ _ _ _
      simp only [χ, this, Finset.sum_add_distrib, ← Complex.exp_add]
      congr 1; push_cast; ring)
    (fun y hy => by
      obtain ⟨v, hv, hv'⟩ := exists_pairing D hn hX hM hξ hL hΛ (y := y) fun h => by
        have := (ht y hy).2.1
        rw [h, norm_zero] at this
        exact zero_ne_one this
      refine ⟨v, hv, fun h => hv' ?_⟩
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h
      rw [← neg_mul] at hm
      have := mul_right_cancel₀ Complex.two_pi_I_ne_zero hm
      refine ⟨-m, ?_⟩
      rw [neg_eq_iff_eq_neg] at this
      exact_mod_cast this)
  refine ⟨s, a, ha, ?_⟩
  have hact (v) (hv : v ∈ B) (y) : heisG X bas (vecMulVec v ξ) (heisG X bas y φ) =
      χ y v • heisG X bas y φ := by
    have h1 := hvac.2.2 _ hv
    have h2 : epsW X D.w (vecMulVec v ξ) = 1 := by
      simp [epsW, row_vecMulVec, smul_smul, EF_line hiso]
    change epsW X D.w (vecMulVec v ξ) • heisG X bas (vecMulVec v ξ) φ = φ at h1
    rw [h2, one_smul] at h1
    conv_rhs => rw [← h1]
    rw [law, law, add_comm y, smul_smul, ← Complex.exp_add]
    congr 2
    simp only [TensLat.EF_swap X (vecMulVec v ξ _) (y _), Finset.sum_neg_distrib]
    push_cast; ring
  have hlin (z : Matrix (Fin n) (Fin r) E) : heisG X bas z (∑ y ∈ t, D.dat hn y • heisG X bas y φ) =
      ∑ y ∈ t, D.dat hn y • heisG X bas z (heisG X bas y φ) := by
    funext x
    simp only [heisG, heisS, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      mul_assoc]
  rw [Finset.sum_congr rfl fun v hv => by
    rw [hlin, Finset.sum_congr rfl fun y _ => by rw [hact v (hsB v hv) y], Finset.smul_sum],
    Finset.sum_comm]
  refine Finset.sum_eq_zero fun y hy => ?_
  simp only [smul_comm _ (D.dat hn y), smul_smul (a _), ← Finset.smul_sum, ← Finset.sum_smul,
    hk y hy, zero_smul, smul_zero]

end GlobalTheory.SW.Coinv
