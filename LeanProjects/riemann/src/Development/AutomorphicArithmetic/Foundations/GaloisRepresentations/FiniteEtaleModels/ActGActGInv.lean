import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.SecInjG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeDegreeNeg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

section LatBProof

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

private theorem mulF_eq_actAf (x : 𝓞 D.F) : mulF D x = actAf D (algebraMap (𝓞 D.F) D.O x) := rfl

private theorem mulF_inAf (c : 𝓞 D.F) (x : D.La) :
    mulF D c (inAf D x) = inAf D (algebraMap (𝓞 D.F) D.O c • x) := by
  rw [mulF_eq_actAf, actAf_inAf]

private theorem mulF_mem (c : 𝓞 D.F) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) : mulF D c v ∈ LaHat D := by
  rw [mulF_eq_actAf]; exact actAf_mem_laHat D _ hv

private theorem actG_mulF (g : G.GAf) (c : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D) :
    L.actG g (mulF D c v) = mulF D c (L.actG g v) := by
  rw [mulF_eq_actAf]; exact actG_actAf L g _ v

private theorem mulF_add (c d : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D) :
    mulF D (c + d) v = mulF D c v + mulF D d v := by
  have e : mulF D (c + d) = mulF D c + mulF D d :=
    GlobalTheory.AdelicSim.ext_inAf D fun x => by
      rw [LinearMap.add_apply, mulF_inAf, mulF_inAf, mulF_inAf, map_add, add_smul, GlobalTheory.AdelicSim.inAf_add]
  rw [e]; rfl

private theorem mulF_mul (c d : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D) :
    mulF D (c * d) v = mulF D c (mulF D d v) := by
  have e : mulF D (c * d) = mulF D c * mulF D d :=
    GlobalTheory.AdelicSim.ext_inAf D fun x => by
      rw [Module.End.mul_apply, mulF_inAf, mulF_inAf, mulF_inAf, map_mul, mul_smul]
  rw [e]; rfl

private theorem mulF_one (v : AfP p ⊗[ℚ] VQ D) : mulF D 1 v = v := by
  have e : mulF D 1 = 1 :=
    GlobalTheory.AdelicSim.ext_inAf D fun x => by
      rw [mulF_inAf, map_one, one_smul, Module.End.one_apply]
  rw [e]; rfl

private theorem mulF_nat (n : ℕ) (v : AfP p ⊗[ℚ] VQ D) : mulF D (n : 𝓞 D.F) v = n • v := by
  have e : mulF D (n : 𝓞 D.F) = n • (1 : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) :=
    GlobalTheory.AdelicSim.ext_inAf D fun x => by
      rw [mulF_inAf, map_natCast, Nat.cast_smul_eq_nsmul, GlobalTheory.AdelicSim.inAf_nsmul, LinearMap.smul_apply,
        Module.End.one_apply]
  rw [e]; rfl

private theorem nsmul_cancel {n : ℕ} (hn : 0 < n) {a b : AfP p ⊗[ℚ] VQ D} (h : n • a = n • b) : a = b := by
  have e : ∀ c : AfP p ⊗[ℚ] VQ D, ((n : ℚ)⁻¹) • (n • c) = c := fun c => by
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
  rw [← e a, h, e b]

private theorem actG_inv_actG (h : G.GAf) (v : AfP p ⊗[ℚ] VQ D) : L.actG h⁻¹ (L.actG h v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem actG_actG_inv (h : G.GAf) (v : AfP p ⊗[ℚ] VQ D) : L.actG h (L.actG h⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

private theorem killed_mul {𝔞 𝔟 : Ideal (𝓞 D.F)} {u : AfP p ⊗[ℚ] VQ D}
    (h : ∀ a ∈ 𝔞, ∀ b ∈ 𝔟, mulF D (a * b) u ∈ LaHat D) : ∀ c ∈ 𝔞 * 𝔟, mulF D c u ∈ LaHat D := by
  intro c hc
  refine Submodule.mul_induction_on hc h fun x y hx hy => ?_
  rw [mulF_add]; exact add_mem hx hy

private theorem fix_of_killed {h : G.GAf} {𝔠 : Ideal (𝓞 D.F)} (hc : CongId L 𝔠 h) {n : ℕ} (hn : 0 < n)
    (hmem : (n : 𝓞 D.F) ∈ 𝔠) {t : AfP p ⊗[ℚ] VQ D} (ht : ∀ c ∈ 𝔠, mulF D c t ∈ LaHat D) :
    L.actG h t - t ∈ LaHat D := by
  have hle : Ideal.span {(n : 𝓞 D.F)} ≤ 𝔠 := (Ideal.span_singleton_le_iff_mem _).2 hmem
  obtain ⟨𝔡, e𝔡⟩ := Ideal.dvd_iff_le.2 hle
  have key : ∀ z ∈ idHat D 𝔠, ∀ d ∈ 𝔡, ∃ w ∈ LaHat D, mulF D d z = n • w := by
    intro z hz d hd
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨x, hx, v, hv, rfl⟩ := hz
      have hxd : x * d ∈ Ideal.span {(n : 𝓞 D.F)} := e𝔡 ▸ Ideal.mul_mem_mul hx hd
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hxd
      refine ⟨mulF D y v, mulF_mem _ hv, ?_⟩
      rw [← mulF_mul, mul_comm d x, ← hy, mul_comm, mulF_mul, mulF_nat]
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨w, hw, e⟩ := ha
      obtain ⟨w', hw', e'⟩ := hb
      exact ⟨w + w', add_mem hw hw', by rw [map_add, e, e', smul_add]⟩
    | neg a _ ha =>
      obtain ⟨w, hw, e⟩ := ha
      exact ⟨-w, neg_mem hw, by rw [map_neg, e, smul_neg]⟩
  have key2 : ∀ e ∈ 𝔠 * 𝔡, ∃ w ∈ LaHat D, mulF D e (L.actG h t - t) = n • w := by
    intro e he
    refine Submodule.mul_induction_on he (fun c hc' d hd => ?_) (fun a b ha hb => ?_)
    · obtain ⟨w, hw, ew⟩ := key _ (hc _ (ht c hc')) d hd
      refine ⟨w, hw, ?_⟩
      rw [← ew, mul_comm c d, mulF_mul, map_sub (mulF D c), ← actG_mulF]
    · obtain ⟨w, hw, e₁⟩ := ha
      obtain ⟨w', hw', e₂⟩ := hb
      exact ⟨w + w', add_mem hw hw', by rw [mulF_add, e₁, e₂, smul_add]⟩
  obtain ⟨w, hw, e⟩ := key2 n (e𝔡 ▸ Ideal.mem_span_singleton_self _)
  rw [mulF_nat] at e
  rw [nsmul_cancel hn e]; exact hw

private theorem lift_killed {h : G.GAf} {𝔴 : Ideal (𝓞 D.F)} (hw : 𝔴.IsMaximal) {m : ℕ}
    (hk : ∃ s : 𝓞 D.F, s ∉ 𝔴 ∧ ∀ x ∈ 𝔴, ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h v' = mulF D (s * x) v)
    {t : AfP p ⊗[ℚ] VQ D} (ht : ∀ c ∈ 𝔴 ^ m, mulF D c t ∈ LaHat D) :
    ∃ u : AfP p ⊗[ℚ] VQ D, (∀ c ∈ 𝔴 ^ (m + 1), mulF D c u ∈ LaHat D) ∧ L.actG h u - t ∈ LaHat D := by
  obtain ⟨s, hs, hk⟩ := hk
  obtain ⟨y, i, hi, e⟩ := hw.exists_inv hs
  have h1 : 𝔴 ⊔ Ideal.span {s} = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← e, add_comm]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hi)
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self s)))
  have h2 : 𝔴 ^ m ⊔ Ideal.span {s} = ⊤ := Ideal.pow_sup_eq_top h1
  obtain ⟨w, hw', z, hz, e2⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 h2)
  obtain ⟨s', rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have hu : L.actG h (L.actG h⁻¹ (mulF D (s' * s) t)) = mulF D (s' * s) t := actG_actG_inv L h _
  refine ⟨L.actG h⁻¹ (mulF D (s' * s) t), ?_, ?_⟩
  · intro c hc
    rw [pow_succ'] at hc
    refine killed_mul (fun x hx y hy => ?_) c hc
    obtain ⟨v', hv', ev⟩ := hk x hx _ (ht y hy)
    have e3 : mulF D (x * y) (L.actG h⁻¹ (mulF D (s' * s) t)) = mulF D s' v' := by
      have inj : ∀ a b : AfP p ⊗[ℚ] VQ D, L.actG h a = L.actG h b → a = b := fun a b e => by
        have e' := congrArg (L.actG h⁻¹) e
        rwa [actG_inv_actG, actG_inv_actG] at e'
      apply inj
      rw [actG_mulF L h, hu, actG_mulF L h, ev]
      simp only [← mulF_mul]
      exact congrArg (fun c => mulF D c t) (by ring)
    rw [e3]; exact mulF_mem _ hv'
  · rw [hu]
    have e4 : mulF D w t + mulF D (s' * s) t = t := by rw [← mulF_add, e2, mulF_one]
    have e5 : mulF D (s' * s) t - t = - mulF D w t := by
      generalize mulF D (s' * s) t = A at e4 ⊢
      generalize mulF D w t = B at e4 ⊢
      rw [← e4]; abel
    rw [e5]; exact neg_mem (ht _ hw')

private theorem gen_rep {a : 𝓞 D.F} {N : ℕ} {𝔟 : Ideal (𝓞 D.F)} (hN : 0 < N) (hp : N.Coprime p) (hg : IsGen a N 𝔟)
    {u : AfP p ⊗[ℚ] VQ D} (hu : ∀ c ∈ 𝔟, mulF D c u ∈ LaHat D) :
    ∃ x : D.La, ∃ v ∈ LaHat D, N • u = inAf D (algebraMap (𝓞 D.F) D.O a • x) + N • v := by
  have key : ∀ e ∈ (Ideal.span {a} ⊔ Ideal.span {(N : 𝓞 D.F)}) * 𝔟,
      ∃ w ∈ LaHat D, ∃ w' ∈ LaHat D, mulF D e u = mulF D a w + N • w' := by
    intro e he
    refine Submodule.mul_induction_on he (fun c hc b hb => ?_) (fun x y hx hy => ?_)
    · obtain ⟨c₁, h₁, c₂, h₂, rfl⟩ := Submodule.mem_sup.1 hc
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 h₁
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 h₂
      have hv := hu b hb
      refine ⟨mulF D s (mulF D b u), mulF_mem _ hv, mulF D t (mulF D b u), mulF_mem _ hv, ?_⟩
      rw [mulF_mul, mulF_add, mul_comm s a, mul_comm t (N : 𝓞 D.F), mulF_mul, mulF_mul, mulF_nat]
    · obtain ⟨w₁, h₁, w₁', h₁', e₁⟩ := hx
      obtain ⟨w₂, h₂, w₂', h₂', e₂⟩ := hy
      refine ⟨w₁ + w₂, add_mem h₁ h₂, w₁' + w₂', add_mem h₁' h₂', ?_⟩
      rw [mulF_add, e₁, e₂, map_add, smul_add]; abel
  have hg' : (Ideal.span {a} ⊔ Ideal.span {(N : 𝓞 D.F)}) * 𝔟 = Ideal.span {(N : 𝓞 D.F)} := hg
  obtain ⟨w, hw, w', hw', e⟩ := key N (by rw [hg']; exact Ideal.mem_span_singleton_self _)
  rw [mulF_nat] at e
  obtain ⟨x, w'', hw'', ex⟩ := exists_inAf_add_nsmul_of_mem_laHat p D N hN hp w hw
  refine ⟨x, mulF D a w'' + w', add_mem (mulF_mem _ hw'') hw', ?_⟩
  rw [e, ex, map_add, map_nsmul, mulF_inAf, smul_add, add_assoc]

end LatBProof

theorem UpperTheory.Gal.FiniteEtaleModels.latB_holds :
    LatB := by
  intro p _ D G L q r 𝔴 𝔟₁ 𝔟₂ i h at' hT hI hle he M₁ M₂ a₁ a₂ g₁ g₂ y
  obtain ⟨e, he⟩ := he
  have hq := at'.prime
  have hwmax := at'.max
  have hn : 0 < q ^ e := pow_pos hq.pos e
  have hqm : ((q ^ e : ℕ) : 𝓞 D.F) ∈ uId D q r ^ e := by
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_pow (Ideal.subset_span (by simp)) e
  have hb₁ : ((q ^ e : ℕ) : 𝓞 D.F) ∈ 𝔟₁ := he hqm
  have hle₂ : 𝔟₁ ≤ 𝔟₂ := hle.trans Ideal.mul_le_left
  have hq0 : ((q ^ e : ℕ) : 𝓞 D.F) ≠ 0 := by exact_mod_cast hn.ne'
  have hb₂ : 𝔟₂ ≠ ⊥ := fun h0 => hq0 (by simpa [h0] using hle₂ hb₁)
  have hw0 : 𝔴 ≠ ⊥ := by
    intro h0
    have : (q : 𝓞 D.F) ∈ 𝔴 := at'.le (Ideal.subset_span (by simp))
    rw [h0, Ideal.mem_bot] at this
    exact hq.ne_zero (by exact_mod_cast this)
  have hM₁ : 0 < M₁.1 := by have := M₁.2.1; omega
  have hM₂ : 0 < M₂.1 := by have := M₂.2.1; omega
  obtain ⟨z, hz⟩ : ∃ z : AfP p ⊗[ℚ] VQ D, M₂.1 • z = inAf D (algebraMap (𝓞 D.F) D.O a₂ • y) := by
    refine ⟨((M₂.1 : ℚ)⁻¹) • inAf D (algebraMap (𝓞 D.F) D.O a₂ • y), ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hM₂.ne'), one_smul]
  have hkz : ∀ c ∈ 𝔟₂, mulF D c z ∈ LaHat D := by
    intro c hc
    have hg' : (Ideal.span {a₂} ⊔ Ideal.span {(M₂.1 : 𝓞 D.F)}) * 𝔟₂ = Ideal.span {(M₂.1 : 𝓞 D.F)} := g₂
    have hm : a₂ * c ∈ Ideal.span {(M₂.1 : 𝓞 D.F)} := by
      rw [← hg']
      exact Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) hc
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hm
    have e1 : mulF D c z = mulF D b (inAf D y) := by
      apply nsmul_cancel hM₂
      rw [← map_nsmul (mulF D c), hz, ← mulF_inAf, ← mulF_mul, ← mulF_nat M₂.1, ← mulF_mul, mul_comm c a₂, ← hb,
        mul_comm]
    rw [e1]; exact mulF_mem _ (GlobalTheory.AdelicSim.inAf_mem D y)
  obtain ⟨m, 𝔠, hnd, e𝔟⟩ := WfDvdMonoid.max_power_factor hb₂ (Ideal.prime_of_isPrime hw0 hwmax.isPrime).irreducible
  have hcop : 𝔠 ⊔ 𝔴 = ⊤ := by
    have hlt : 𝔴 < 𝔠 ⊔ 𝔴 := by
      refine lt_of_le_of_ne le_sup_right fun heq => hnd (Ideal.dvd_iff_le.2 ?_)
      rw [heq]; exact le_sup_left
    exact hwmax.out.2 _ hlt
  have hcop' : 𝔠 ⊔ 𝔴 ^ m = ⊤ := Ideal.sup_pow_eq_top hcop
  obtain ⟨α, hα, β, hβ, eαβ⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hcop')
  have hle𝔠 : 𝔟₂ ≤ 𝔠 := e𝔟 ▸ Ideal.mul_le_right
  have hCong : CongId L 𝔠 h := hT.other 𝔠 hcop ⟨e, he.trans (hle₂.trans hle𝔠)⟩
  have k₁ : ∀ c ∈ 𝔠, mulF D c (mulF D β z) ∈ LaHat D := by
    intro c hc
    rw [← mulF_mul]
    exact hkz _ (by rw [e𝔟, mul_comm c β]; exact Ideal.mul_mem_mul hβ hc)
  have k₂ : ∀ c ∈ 𝔴 ^ m, mulF D c (mulF D α z) ∈ LaHat D := by
    intro c hc
    rw [← mulF_mul]
    exact hkz _ (by rw [e𝔟]; exact Ideal.mul_mem_mul hc hα)
  have f₁ := fix_of_killed L hCong hn (hle𝔠 (hle₂ hb₁)) k₁
  obtain ⟨u₂, ku, fu⟩ := lift_killed L hwmax hT.kill k₂
  have hle' : 𝔟₁ ≤ 𝔴 ^ (m + 1) * 𝔠 := hle.trans (le_of_eq (by rw [e𝔟]; ring))
  have ku' : ∀ c ∈ 𝔟₁, mulF D c (mulF D β z + u₂) ∈ LaHat D := by
    intro c hc
    refine killed_mul (fun x hx y hy => ?_) c (hle' hc)
    rw [map_add]
    refine add_mem ?_ ?_
    · rw [mulF_mul]; exact mulF_mem _ (k₁ y hy)
    · rw [mul_comm, mulF_mul]; exact mulF_mem _ (ku x hx)
  obtain ⟨x, v₀, hv₀, ex⟩ := gen_rep hM₁ M₁.2.2 g₁ ku'
  have hsum : mulF D α z + mulF D β z = z := by rw [← mulF_add, eαβ, mulF_one]
  have hlam : L.actG h (mulF D β z + u₂) - z ∈ LaHat D := by
    have e1 : L.actG h (mulF D β z + u₂) - z =
        (L.actG h (mulF D β z) - mulF D β z) + (L.actG h u₂ - mulF D α z) := by
      rw [map_add]
      calc L.actG h (mulF D β z) + L.actG h u₂ - z
          = L.actG h (mulF D β z) + L.actG h u₂ - (mulF D α z + mulF D β z) := by rw [hsum]
        _ = _ := by abel
    rw [e1]; exact add_mem f₁ fu
  refine ⟨x, (L.actG h (mulF D β z + u₂) - z) - L.actG h v₀, sub_mem hlam (hI _ hv₀), ?_⟩
  have hB : inAf D (algebraMap (𝓞 D.F) D.O a₁ • x) = M₁.1 • (mulF D β z + u₂) - M₁.1 • v₀ :=
    eq_sub_of_add_eq ex.symm
  rw [GlobalTheory.AdelicSim.inAf_nsmul, hB, GlobalTheory.AdelicSim.inAf_nsmul, ← hz, map_nsmul, map_sub, map_nsmul, map_nsmul]
  module
