import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.GlobWIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.HANegRight

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace PI.ScRefExists.GWG

open PI.ScRefExists.Sk

section Lemmas

variable (I : Formalism.MainNotions.S.AutInst)

theorem hG_add_left (x y z : Fin I.n → I.E) : hG I (x + y) z = hG I x z + hG I y z := by
  unfold hG Formalism.UG.hform
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.add_apply, map_add]
  ring

theorem hG_add_right (x y z : Fin I.n → I.E) : hG I x (y + z) = hG I x y + hG I x z := by
  unfold hG Formalism.UG.hform
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.add_apply, map_add]
  ring

theorem hG_zsmul_left (q : ℤ) (x y : Fin I.n → I.E) : hG I (q • x) y = (q : I.E) * hG I x y := by
  unfold hG Formalism.UG.hform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast]
  ring

theorem hG_zsmul_right (q : ℤ) (x y : Fin I.n → I.E) : hG I x (q • y) = (q : I.E) * hG I x y := by
  unfold hG Formalism.UG.hform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast]
  ring

theorem hG_zero_right (x : Fin I.n → I.E) : hG I x 0 = 0 := by
  simp [hG, Formalism.UG.hform]

theorem hG_comb (q₁ q₂ : ℤ) (x₁ x₂ y₁ y₂ : Fin I.n → I.E) :
    hG I (q₁ • x₁ + q₂ • x₂) (q₁ • y₁ + q₂ • y₂) =
      (q₁ : I.E) ^ 2 * hG I x₁ y₁ + (q₁ : I.E) * (q₂ : I.E) * (hG I x₁ y₂ + hG I x₂ y₁) +
        (q₂ : I.E) ^ 2 * hG I x₂ y₂ := by
  simp only [hG_add_left, hG_add_right, hG_zsmul_left, hG_zsmul_right]
  ring

theorem hG_int {x y : Fin I.n → I.E} (hx : x ∈ I.L) (hy : y ∈ I.L) :
    hG I x y ∈ (algebraMap (𝓞 I.E) I.E).range := (I.L_dual y).mp hy x hx

theorem theta_mem (θ : 𝓞 I.E) : (θ : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := ⟨θ, rfl⟩

theorem ite_mem {p : Prop} [Decidable p] :
    (if p then (1 : I.E) else 0) ∈ (algebraMap (𝓞 I.E) I.E).range := by
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem osmul_mem {t : I.E} (ht : t ∈ (algebraMap (𝓞 I.E) I.E).range) {v : Fin I.n → I.E}
    (hv : v ∈ I.L) : t • v ∈ I.L := by
  obtain ⟨s, rfl⟩ := ht
  rw [algebraMap_smul]
  exact I.L.smul_mem s hv

theorem crt_ge {g₁ g₂ : ℕ} {A B q₁ q₂ : ℤ} (hq₁ : q₁ = g₂ * B) (hq₂ : q₂ = g₁ * A)
    {x X₁₁ X₁₂ X₂₂ : I.E} (h₁ : GE I g₁ X₁₁) (h₂ : GE I g₂ X₂₂)
    (h₁₂ : X₁₂ ∈ (algebraMap (𝓞 I.E) I.E).range)
    (hx : x = (q₁ : I.E) ^ 2 * X₁₁ + (q₁ : I.E) * (q₂ : I.E) * X₁₂ + (q₂ : I.E) ^ 2 * X₂₂) :
    GE I (g₁ * g₂) x := by
  obtain ⟨t1, ht1⟩ := h₁
  obtain ⟨t2, ht2⟩ := h₂
  obtain ⟨s, hs⟩ := h₁₂
  have hc : ∀ u : 𝓞 I.E, (u : I.E) = algebraMap (𝓞 I.E) I.E u := fun u => rfl
  refine ⟨(g₂ : 𝓞 I.E) * (B : 𝓞 I.E) ^ 2 * t1 + (B : 𝓞 I.E) * (A : 𝓞 I.E) * s +
    (g₁ : 𝓞 I.E) * (A : 𝓞 I.E) ^ 2 * t2, ?_⟩
  rw [hx, hq₁, hq₂, ht1, ht2, ← hs]
  simp only [hc, map_add, map_mul, map_pow, map_natCast, map_intCast]
  push_cast
  try ring

theorem ge_one {x : I.E} (hx : x ∈ (algebraMap (𝓞 I.E) I.E).range) : GE I 1 x := by
  obtain ⟨s, rfl⟩ := hx
  exact ⟨s, by rw [Nat.cast_one, one_mul]⟩

def SS (r k M : ℕ) (e f : Fin r → Fin I.n → I.E) (θ : 𝓞 I.E) (z : Fin I.n → I.E)
    (b bd : Fin k → Fin I.n → I.E) : Set (Fin I.n → I.E) :=
  Set.range (fun a => M • e a) ∪ Set.range (fun a => M • f a) ∪ {z} ∪
    Set.range (fun i => (θ : I.E) • b i) ∪ Set.range (fun i => star (θ : I.E) • bd i)

theorem gL_mem (G : ℕ) {x : Fin I.n → I.E} (hx : x ∈ I.L) : (G : I.E) • x ∈ gL I G := Submodule.subset_span ⟨x, hx, rfl⟩

private theorem star_coe_mem_range_algebraMap (θ : 𝓞 I.E) :
    star (θ : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := by
  have h : IsIntegral ℤ (star (θ : I.E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe θ).map (starRingEnd I.E).toIntAlgHom
  exact ⟨⟨star (θ : I.E), h⟩, rfl⟩

theorem side_mem {r k M : ℕ} (e f : Fin r → Fin I.n → I.E) (θ : 𝓞 I.E) (G ga : ℕ) (qa qb w wab : ℤ)
    (z za zb : Fin I.n → I.E) (b ba bb bd bda bdb : Fin k → Fin I.n → I.E)
    (hza : za ∈ I.L) (hzb : zb ∈ I.L)
    (hbL : ∀ i, ba i ∈ I.L ∧ bb i ∈ I.L ∧ bda i ∈ I.L ∧ bdb i ∈ I.L)
    (hsum : (qa : I.E) + (qb : I.E) = 1) (hprod : (qa : I.E) * (qb : I.E) = (G : I.E) * (wab : I.E))
    (hga : (qa : I.E) * (ga : I.E) = (G : I.E) * (w : I.E))
    (hz : z = qa • za + qb • zb) (hb : ∀ i, b i = qa • ba i + qb • bb i)
    (hbd : ∀ i, bd i = qa • bda i + qb • bdb i) {y : Fin I.n → I.E}
    (hsp : y ∈ Submodule.span (𝓞 I.E) (SS I r k M e f θ za ba bda) ⊔ gL I ga) :
    qa • y ∈ Submodule.span (𝓞 I.E) (SS I r k M e f θ z b bd) ⊔ gL I G := by
  set S' := Submodule.span (𝓞 I.E) (SS I r k M e f θ z b bd) ⊔ gL I G with hS'
  have hsp' : ∀ v ∈ SS I r k M e f θ z b bd, v ∈ S' :=
    fun v hv => Submodule.mem_sup_left (Submodule.subset_span hv)
  have hG' : ∀ x ∈ I.L, (G : I.E) • x ∈ S' := fun x hx => Submodule.mem_sup_right (gL_mem I G hx)
  have hzs : ∀ (q : ℤ) {v : Fin I.n → I.E}, v ∈ S' → q • v ∈ S' := fun q v hv => zsmul_mem hv q
  have hwab : (wab : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := ⟨(wab : 𝓞 I.E), by simp⟩
  let φ : (Fin I.n → I.E) →ₗ[𝓞 I.E] (Fin I.n → I.E) :=
    { toFun := fun v => qa • v
      map_add' := fun a c => smul_add qa a c
      map_smul' := fun c v => smul_comm qa c v }
  suffices h : Submodule.span (𝓞 I.E) (SS I r k M e f θ za ba bda) ⊔ gL I ga ≤ S'.comap φ from h hsp
  apply sup_le
  · rw [Submodule.span_le]
    intro v hv
    simp only [SS, Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hv
    show qa • v ∈ S'
    rcases hv with ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | hvz) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact hzs qa (hsp' _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨a, rfl⟩)))))
    · exact hzs qa (hsp' _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩)))))
    · rw [hvz]
      have hv : qa • za = qa • z + (G : I.E) • ((wab : I.E) • (za - zb)) := by
        ext j
        simp only [hz, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.intCast_apply, zsmul_eq_mul, smul_eq_mul]
        linear_combination (za j - zb j) * hprod - ((qa : I.E) * za j) * hsum
      rw [hv]
      exact S'.add_mem (hzs qa (hsp' z (Or.inl (Or.inl (Or.inr rfl)))))
        (hG' _ (osmul_mem I hwab (I.L.sub_mem hza hzb)))
    · have hv : qa • ((θ : I.E) • ba i) = qa • ((θ : I.E) • b i) +
          (G : I.E) • ((wab : I.E) • ((θ : I.E) • (ba i - bb i))) := by
        ext j
        simp only [hb, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.intCast_apply, zsmul_eq_mul, smul_eq_mul]
        linear_combination (θ : I.E) * (ba i j - bb i j) * hprod - ((θ : I.E) * (qa : I.E) * ba i j) * hsum
      rw [hv]
      exact S'.add_mem (hzs qa (hsp' _ (Or.inl (Or.inr ⟨i, rfl⟩))))
        (hG' _ (osmul_mem I hwab (osmul_mem I (theta_mem I θ) (I.L.sub_mem (hbL i).1 (hbL i).2.1))))
    · have hv : qa • (star (θ : I.E) • bda i) = qa • (star (θ : I.E) • bd i) +
          (G : I.E) • ((wab : I.E) • (star (θ : I.E) • (bda i - bdb i))) := by
        ext j
        simp only [hbd, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.intCast_apply, zsmul_eq_mul, smul_eq_mul]
        linear_combination star (θ : I.E) * (bda i j - bdb i j) * hprod -
          (star (θ : I.E) * (qa : I.E) * bda i j) * hsum
      rw [hv]
      exact S'.add_mem (hzs qa (hsp' _ (Or.inr ⟨i, rfl⟩)))
        (hG' _ (osmul_mem I hwab (osmul_mem I (star_coe_mem_range_algebraMap I θ)
          (I.L.sub_mem (hbL i).2.2.1 (hbL i).2.2.2))))
  · rw [gL, Submodule.span_le]
    rintro v ⟨x, hx, rfl⟩
    show qa • ((ga : I.E) • x) ∈ S'
    have hv : qa • ((ga : I.E) • x) = (G : I.E) • ((w : I.E) • x) := by
      ext j
      simp only [Pi.smul_apply, Pi.mul_apply, Pi.intCast_apply, zsmul_eq_mul, smul_eq_mul]
      linear_combination (x j) * hga
    rw [hv]
    exact hG' _ (osmul_mem I ⟨(w : 𝓞 I.E), by simp⟩ hx)

end Lemmas

theorem chinese_remainder_gluing : GWcrt := by
  intro I g₁ g₂ r k θ e f M hcop _ hC1 hC2
  obtain ⟨A, B, hAB⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨za, ba, bda, hza, hbaL, hoza, hoba, hGa, hTa, hTTa, hspa⟩ := hC1
  obtain ⟨zb, bb, bdb, hzb, hbbL, hozb, hobb, hGb, hTb, hTTb, hspb⟩ := hC2
  set qa : ℤ := (g₂ : ℤ) * B with hqa
  set qb : ℤ := (g₁ : ℤ) * A with hqb
  have hsumZ : qa + qb = 1 := by rw [hqa, hqb]; linarith
  have hsum : (qa : I.E) + (qb : I.E) = 1 := by exact_mod_cast hsumZ
  have hprod : (qa : I.E) * (qb : I.E) = ((g₁ * g₂ : ℕ) : I.E) * ((A * B : ℤ) : I.E) := by
    rw [hqa, hqb]; push_cast; ring
  have hga : (qa : I.E) * (g₁ : I.E) = ((g₁ * g₂ : ℕ) : I.E) * (B : I.E) := by
    rw [hqa]; push_cast; ring
  have hgb : (qb : I.E) * (g₂ : I.E) = ((g₁ * g₂ : ℕ) : I.E) * (A : I.E) := by
    rw [hqb]; push_cast; ring
  have hsum' : (qb : I.E) + (qa : I.E) = 1 := by rw [add_comm]; exact hsum
  have hprod' : (qb : I.E) * (qa : I.E) = ((g₁ * g₂ : ℕ) : I.E) * ((A * B : ℤ) : I.E) := by
    rw [mul_comm]; exact hprod
  have two_mem : (2 : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := ⟨2, map_ofNat _ 2⟩
  refine ⟨qa • za + qb • zb, fun i => qa • ba i + qb • bb i, fun i => qa • bda i + qb • bdb i,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact I.L.add_mem (zsmul_mem hza qa) (zsmul_mem hzb qb)
  · exact fun i => ⟨I.L.add_mem (zsmul_mem (hbaL i).1 qa) (zsmul_mem (hbbL i).1 qb),
      I.L.add_mem (zsmul_mem (hbaL i).2 qa) (zsmul_mem (hbbL i).2 qb)⟩
  · intro a
    obtain ⟨h1, h2⟩ := hoza a
    obtain ⟨h3, h4⟩ := hozb a
    constructor <;> simp only [hG_add_right, hG_zsmul_right, h1, h2, h3, h4, mul_zero, add_zero]
  · intro a i
    obtain ⟨h1, h2, h3, h4⟩ := hoba a i
    obtain ⟨h5, h6, h7, h8⟩ := hobb a i
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [hG_add_right, hG_zsmul_right, h1, h2, h3, h4, h5, h6, h7, h8, mul_zero, add_zero]
  · refine crt_ge I hqa hqb hGa hGb
      (add_mem (add_mem (hG_int I hza hzb) (hG_int I hzb hza)) two_mem) ?_
    rw [hG_comb]
    linear_combination (-((qa : I.E) + qb + 1)) * hsum
  · intro i
    constructor
    · refine crt_ge I hqa hqb (hTa i).1 (hTb i).1
        (mul_mem (theta_mem I θ) (add_mem (hG_int I hza (hbbL i).1) (hG_int I hzb (hbaL i).1))) ?_
      beta_reduce
      rw [hG_comb]
      ring
    · refine crt_ge I hqa hqb (hTa i).2 (hTb i).2
        (mul_mem (star_coe_mem_range_algebraMap I θ)
          (add_mem (hG_int I hza (hbbL i).2) (hG_int I hzb (hbaL i).2))) ?_
      beta_reduce
      rw [hG_comb]
      ring
  · intro i j
    refine crt_ge I hqa hqb (hTTa i j) (hTTb i j)
      (mul_mem (theta_mem I θ) (sub_mem (add_mem (hG_int I (hbaL i).2 (hbbL j).1)
        (hG_int I (hbbL i).2 (hbaL j).1)) (mul_mem two_mem (ite_mem I (p := i = j))))) ?_
    beta_reduce
    rw [hG_comb]
    linear_combination ((θ : I.E) * (if i = j then (1 : I.E) else 0) * ((qa : I.E) + qb + 1)) * hsum
  · intro y hy
    have h1 := side_mem I e f θ (g₁ * g₂) g₁ qa qb B (A * B) (qa • za + qb • zb) za zb
      (fun i => qa • ba i + qb • bb i) ba bb (fun i => qa • bda i + qb • bdb i) bda bdb hza hzb
      (fun i => ⟨(hbaL i).1, (hbbL i).1, (hbaL i).2, (hbbL i).2⟩) hsum hprod hga rfl
      (fun i => rfl) (fun i => rfl) (hspa y hy)
    have h2 := side_mem I e f θ (g₁ * g₂) g₂ qb qa A (A * B) (qa • za + qb • zb) zb za
      (fun i => qa • ba i + qb • bb i) bb ba (fun i => qa • bda i + qb • bdb i) bdb bda hzb hza
      (fun i => ⟨(hbbL i).1, (hbaL i).1, (hbbL i).2, (hbaL i).2⟩) hsum' hprod' hgb (add_comm _ _)
      (fun i => add_comm _ _) (fun i => add_comm _ _) (hspb y hy)
    have hy' : y = qa • y + qb • y := by rw [← add_smul, hsumZ, one_smul]
    rw [hy']
    exact add_mem h1 h2

theorem hyp_dvd {I : Formalism.MainNotions.S.AutInst} {g g' r k : ℕ} {θ : 𝓞 I.E} {e f : Fin r → Fin I.n → I.E} {M : ℕ}
    (h : Hyp I g r k θ e f M) (hd : g' ∣ g) (h1 : 1 ≤ g') : Hyp I g' r k θ e f M := by
  obtain ⟨c, rfl⟩ := hd
  have hc : ∀ u : 𝓞 I.E, (u : I.E) = algebraMap (𝓞 I.E) I.E u := fun u => rfl
  have hGE : ∀ x, GE I (g' * c) x → GE I g' x := by
    rintro x ⟨t, rfl⟩
    refine ⟨(c : 𝓞 I.E) * t, ?_⟩
    simp only [hc, map_mul, map_natCast]
    push_cast
    ring
  obtain ⟨_, hS, hT, hn, he, hf, hef, hM, hL⟩ := h
  refine ⟨h1, ?_, ⟨hGE _ hT.1, hGE _ hT.2.1, hGE _ hT.2.2⟩, hn, he, hf, hef,
    Nat.Coprime.coprime_dvd_right (Dvd.intro c rfl) hM, hL⟩
  intro v hv
  apply hS v
  rw [Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ hv

theorem concl_one (I : Formalism.MainNotions.S.AutInst) (r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ) :
    Concl I 1 r k θ e f M := by
  have hz0 : ∀ x : Fin I.n → I.E, hG I x 0 = 0 := hG_zero_right I
  refine ⟨0, fun _ => 0, fun _ => 0, I.L.zero_mem, fun _ => ⟨I.L.zero_mem, I.L.zero_mem⟩,
    fun a => ⟨hz0 _, hz0 _⟩, fun a i => ⟨hz0 _, hz0 _, hz0 _, hz0 _⟩, ?_, ?_, ?_, ?_⟩
  · rw [hz0, zero_add]; exact ge_one I (one_mem _)
  · intro i
    simp only [hz0, mul_zero]
    exact ⟨ge_one I (zero_mem _), ge_one I (zero_mem _)⟩
  · intro i j
    exact ge_one I (mul_mem (theta_mem I θ) (sub_mem (by rw [hz0]; exact zero_mem _) (ite_mem I (p := i = j))))
  · intro y hy
    apply Submodule.mem_sup_right
    have := gL_mem I 1 hy
    rwa [Nat.cast_one, one_smul] at this

theorem globW_of (h1 : GWpp) (h2 : GWcrt) : GlobW := by
  have key : ∀ (I : Formalism.MainNotions.S.AutInst) (r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ)
      (g : ℕ), Hyp I g r k θ e f M → Concl I g r k θ e f M := by
    intro I r k θ e f M g
    induction g using Nat.recOnPosPrimePosCoprime with
    | prime_pow p n hp hn => exact h1 I p n r k θ e f M hp hn
    | zero => intro h; exact absurd h.1 (by norm_num)
    | one => intro _; exact concl_one I r k θ e f M
    | coprime a b ha hb hab iha ihb =>
      intro h
      exact h2 I a b r k θ e f M hab h (iha (hyp_dvd h (Dvd.intro b rfl) (by omega)))
        (ihb (hyp_dvd h (Dvd.intro_left a rfl) (by omega)))
  intro I g r k θ e f M hg hS hT hn he hf hef hM hL
  exact key I r k θ e f M g ⟨hg, hS, hT, hn, he, hf, hef, hM, hL⟩

end PI.ScRefExists.GWG

end
