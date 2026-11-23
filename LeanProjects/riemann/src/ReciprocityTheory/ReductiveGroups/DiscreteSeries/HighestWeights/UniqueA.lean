import Formalism.RealPlaceAnalysis.QuotientSettingHolds

noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open Formalism.REAL

variable {n : ℕ}

section

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V)

lemma uq_mem_kSpan (x : V) : x ∈ kSpan ε F x := by
    unfold kSpan
    exact Submodule.mem_sInf.2 fun _ hS => hS.1

lemma uq_kSpan_le {x : V} {S : Submodule ℂ V} (hx : x ∈ S) (hS : KStable ε F S) : kSpan ε F x ≤ S := by
    unfold kSpan
    exact sInf_le ⟨hx, hS⟩

lemma uq_kSpan_stable (x : V) : KStable ε F (kSpan ε F x) := by
  intro a b hab y hy
  unfold kSpan at hy ⊢
  rw [Submodule.mem_sInf] at hy ⊢
  exact fun S hS => hS.2 a b hab y (hy S hS)

end

lemma uq_kRel_map {A B : Type*} [Ring A] [Ring B] (ε : Fin n → Bool) (F : Fin n → Fin n → A) (f : A →+* B)
    (h : KRel ε F) : KRel ε (fun a b => f (F a b)) := by
  intro a b c d hab hcd
  have h0 := congrArg f (h a b c d hab hcd)
  simp only [map_sub, map_mul, apply_ite f, map_zero] at h0
  exact h0

lemma uq_kRel_prod {A B : Type*} [Ring A] [Ring B] (ε : Fin n → Bool) (F : Fin n → Fin n → A)
    (F' : Fin n → Fin n → B) (h : KRel ε F) (h' : KRel ε F') : KRel ε (fun a b => (F a b, F' a b)) := by
  intro a b c d hab hcd
  refine Prod.ext ?_ ?_
  · first
      | (simp only [Prod.fst_sub, Prod.fst_mul, h a b c d hab hcd, apply_ite Prod.fst, Prod.fst_zero]; done)
      | simp [h a b c d hab hcd, apply_ite Prod.fst]
  · first
      | (simp only [Prod.snd_sub, Prod.snd_mul, h' a b c d hab hcd, apply_ite Prod.snd, Prod.snd_zero]; done)
      | simp [h' a b c d hab hcd, apply_ite Prod.snd]

section

variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def uqG (F : Fin n → Fin n → Module.End ℂ V) (F' : Fin n → Fin n → Module.End ℂ V') (a b : Fin n) :
    Module.End ℂ (WithLp 2 (V × V')) :=
  LinearEquiv.conjRingEquiv (WithLp.linearEquiv 2 ℂ (V × V')).symm
    (LinearMap.prodMapRingHom ℂ V V' (F a b, F' a b))

lemma uqG_apply (F : Fin n → Fin n → Module.End ℂ V) (F' : Fin n → Fin n → Module.End ℂ V') (a b : Fin n)
    (x : WithLp 2 (V × V')) :
    WithLp.ofLp (uqG F F' a b x) = (F a b (WithLp.ofLp x).1, F' a b (WithLp.ofLp x).2) := rfl

end

section

variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

lemma uq_bij {P U : Type} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [FiniteDimensional ℂ P]
    [AddCommGroup U] [Module ℂ U] (ε : Fin n → Bool) (G : Fin n → Fin n → Module.End ℂ P)
    (F : Fin n → Fin n → Module.End ℂ U) (μ : Fin n → ℝ) (x : P) (hR : KRel ε G) (hU : KUnit ε G)
    (hx : KHighest ε G μ x) (p : P →ₗ[ℂ] U) (hp : ∀ a b, ε a = ε b → ∀ y, p (G a b y) = F a b (p y))
    (hpx : p x ≠ 0) (hT : kSpan ε F (p x) = ⊤) : Function.Bijective (p.domRestrict (kSpan ε G x)) := by

  obtain ⟨B, hBdef⟩ : ∃ B : Submodule ℂ P, B = sInf {S : Submodule ℂ P | x ∈ S ∧
      ∀ a b, b < a → ε a = ε b → ∀ y ∈ S, G a b y ∈ S} := ⟨_, rfl⟩
  have hxB : x ∈ B := by
    rw [hBdef, Submodule.mem_sInf]; exact fun S hS => hS.1
  have hlow : ∀ a b, b < a → ε a = ε b → ∀ y ∈ B, G a b y ∈ B := by
    intro a b hba hab y hy
    rw [hBdef, Submodule.mem_sInf] at hy ⊢
    exact fun S hS => hS.2 a b hba hab y (hy S hS)
  have hBle : ∀ S : Submodule ℂ P, x ∈ S →
      (∀ a b, b < a → ε a = ε b → ∀ y ∈ S, G a b y ∈ S) → B ≤ S := by
    intro S hxS hS
    rw [hBdef]; exact sInf_le ⟨hxS, hS⟩

  have hBst : KStable ε G B := by
    have key : B ≤ B ⊓ ⨅ c : Fin n, ⨅ d : Fin n, ⨅ (_ : ε c = ε d), B.comap (G c d) := by
      refine hBle _ ?_ ?_
      · refine Submodule.mem_inf.2 ⟨hxB, ?_⟩
        simp only [Submodule.mem_iInf, Submodule.mem_comap]
        intro c d hcd
        rcases lt_trichotomy c d with hlt | heq | hgt
        · rw [hx.2 c d hlt hcd]; exact B.zero_mem
        · subst heq; rw [hx.1 c]; exact B.smul_mem _ hxB
        · exact hlow c d hgt hcd x hxB
      · intro a b hba hab y hy
        rw [Submodule.mem_inf] at hy ⊢
        simp only [Submodule.mem_iInf, Submodule.mem_comap] at hy ⊢
        refine ⟨hlow a b hba hab y hy.1, fun c d hcd => ?_⟩
        have hcomm : G c d (G a b y) - G a b (G c d y) =
            (if d = a then G c b else 0) y - (if b = c then G a d else 0) y :=
          LinearMap.congr_fun (hR c d a b hcd hab) y
        have he : G c d (G a b y) = G a b (G c d y) +
            ((if d = a then G c b else 0) y - (if b = c then G a d else 0) y) := by
          rw [← hcomm]; abel
        rw [he]
        refine B.add_mem (hlow a b hba hab _ (hy.2 c d hcd)) (B.sub_mem ?_ ?_)
        · split_ifs with h
          · subst h; exact hy.2 c b (hcd.trans hab)
          · simpa using B.zero_mem
        · split_ifs with h
          · subst h; exact hy.2 a d (hab.trans hcd)
          · simpa using B.zero_mem
    intro a b hab y hy
    have hy' := key hy
    rw [Submodule.mem_inf] at hy'
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hy'
    exact hy'.2 a b hab
  have hMB : kSpan ε G x ≤ B := uq_kSpan_le ε G hxB hBst
  refine ⟨?_, ?_⟩
  · obtain ⟨N, hNdef⟩ : ∃ N : Submodule ℂ P, N = LinearMap.ker p ⊓ kSpan ε G x := ⟨_, rfl⟩
    have hNst : KStable ε G N := by
      intro a b hab z hz
      rw [hNdef, Submodule.mem_inf, LinearMap.mem_ker] at hz ⊢
      exact ⟨by rw [hp a b hab z, hz.1, map_zero], uq_kSpan_stable ε G x a b hab z hz.2⟩
    have hNo : KStable ε G Nᗮ := by
      intro a b hab m hm
      rw [Submodule.mem_orthogonal] at hm ⊢
      intro u hu
      rw [← hU b a hab.symm u m]
      exact hm _ (hNst b a hab.symm u hu)
    have hzero : ∀ v, v ∈ N → v ∈ Nᗮ → v = 0 := fun v h1 h2 =>
      inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 h2 v h1)
    obtain ⟨nn, hnn, mm, hmm, hxnm⟩ : ∃ y ∈ N, ∃ z ∈ Nᗮ, x = y + z := by
      first
        | exact N.exists_add_mem_mem_orthogonal x
        | (obtain ⟨y, hy, z, hz, e⟩ := Submodule.mem_sup.1
              (show x ∈ N ⊔ Nᗮ by rw [Submodule.sup_orthogonal_of_completeSpace]; exact Submodule.mem_top)
           exact ⟨y, hy, z, hz, e.symm⟩)
    have hnr : ∀ c d, c < d → ε c = ε d → G c d nn = 0 := by
      intro c d hcd hε
      have h0 : G c d nn + G c d mm = 0 := by rw [← map_add, ← hxnm, hx.2 c d hcd hε]
      have h1 : G c d nn = -G c d mm := eq_neg_of_add_eq_zero_left h0
      refine hzero _ (hNst c d hε nn hnn) ?_
      rw [h1]; exact Nᗮ.neg_mem (hNo c d hε mm hmm)
    have hnB : nn ∈ B := hMB (Submodule.mem_inf.1 (hNdef ▸ hnn)).2
    have hmB : mm ∈ B := by
      have hme : mm = x - nn := by rw [hxnm]; abel
      rw [hme]; exact B.sub_mem hxB hnB
    have hS : ∀ y ∈ B, ⟪nn, y⟫_ℂ * ((‖x‖ : ℂ) ^ 2) = ⟪nn, x⟫_ℂ * ⟪x, y⟫_ℂ := by
      let S : Submodule ℂ P :=
        { carrier := {y | ⟪nn, y⟫_ℂ * ((‖x‖ : ℂ) ^ 2) = ⟪nn, x⟫_ℂ * ⟪x, y⟫_ℂ}
          add_mem' := by
            intro y z hy hz
            simp only [Set.mem_setOf_eq, inner_add_right] at hy hz ⊢
            rw [add_mul, mul_add, hy, hz]
          zero_mem' := by simp
          smul_mem' := by
            intro c y hy
            simp only [Set.mem_setOf_eq, inner_smul_right] at hy ⊢
            rw [mul_assoc, hy]; ring }
      have hBS : B ≤ S := by
        refine hBle S ?_ ?_
        · show ⟪nn, x⟫_ℂ * ((‖x‖ : ℂ) ^ 2) = ⟪nn, x⟫_ℂ * ⟪x, x⟫_ℂ
          rw [inner_self_eq_norm_sq_to_K]
          first | rfl | simp | norm_cast
        · intro a b hba hab y _
          show ⟪nn, G a b y⟫_ℂ * ((‖x‖ : ℂ) ^ 2) = ⟪nn, x⟫_ℂ * ⟪x, G a b y⟫_ℂ
          rw [← hU b a hab.symm nn y, ← hU b a hab.symm x y, hnr b a hba hab.symm,
            hx.2 b a hba hab.symm]
          simp
      exact fun y hy => hBS hy
    have key := hS mm hmB
    have hnm : ⟪nn, mm⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 hmm nn hnn
    have hnx : ⟪nn, x⟫_ℂ = ⟪nn, nn⟫_ℂ := by rw [hxnm, inner_add_right, hnm, add_zero]
    have hxm : ⟪x, mm⟫_ℂ = ⟪mm, mm⟫_ℂ := by rw [hxnm, inner_add_left, hnm, zero_add]
    rw [hnm, hnx, hxm, zero_mul] at key
    have hn0 : nn = 0 := by
      rcases mul_eq_zero.1 key.symm with h | h
      · exact inner_self_eq_zero.1 h
      · exfalso
        have hm0 : mm = 0 := inner_self_eq_zero.1 h
        have hxN : x ∈ N := by rw [hxnm, hm0, add_zero]; exact hnn
        rw [hNdef, Submodule.mem_inf, LinearMap.mem_ker] at hxN
        exact hpx hxN.1
    have hxo : x ∈ Nᗮ := by rw [hxnm, hn0, zero_add]; exact hmm
    have hMo : kSpan ε G x ≤ Nᗮ := uq_kSpan_le ε G hxo hNo
    intro z₁ z₂ hz
    have hd : (z₁ : P) - z₂ ∈ N := by
      rw [hNdef, Submodule.mem_inf, LinearMap.mem_ker]
      refine ⟨?_, Submodule.sub_mem _ z₁.2 z₂.2⟩
      rw [map_sub, sub_eq_zero]; simpa using hz
    have h3 := hzero _ hd (hMo (Submodule.sub_mem _ z₁.2 z₂.2))
    exact Subtype.ext (sub_eq_zero.1 h3)
  · intro u
    have hT' : kSpan ε F (p x) ≤ (kSpan ε G x).map p := by
      refine uq_kSpan_le ε F (Submodule.mem_map_of_mem (uq_mem_kSpan ε G x)) ?_
      intro a b hab v hv
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hv
      rw [← hp a b hab z]
      exact Submodule.mem_map_of_mem (uq_kSpan_stable ε G x a b hab z hz)
    rw [hT] at hT'
    obtain ⟨z, hz, hzu⟩ := Submodule.mem_map.1 (hT' Submodule.mem_top)
    exact ⟨⟨z, hz⟩, by simpa using hzu⟩

theorem uq_exists_equiv (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V)
    (F' : Fin n → Fin n → Module.End ℂ V') (Λ : Fin n → ℝ) (w : V) (w' : V')
    (hR : KRel ε F) (hR' : KRel ε F') (hU : KUnit ε F) (hU' : KUnit ε F')
    (hw : KHighest ε F Λ w) (hw' : KHighest ε F' Λ w') (hw0 : w ≠ 0) (hw0' : w' ≠ 0)
    (hT : kSpan ε F w = ⊤) (hT' : kSpan ε F' w' = ⊤) :
    ∃ φ : V ≃ₗ[ℂ] V', (∀ a b, ε a = ε b → ∀ v, φ (F a b v) = F' a b (φ v)) ∧ φ w = w' := by
  classical
  have hRG : KRel ε (uqG F F') :=
    uq_kRel_map ε (fun a b => ((F a b, F' a b) : Module.End ℂ V × Module.End ℂ V'))
      ((LinearEquiv.conjRingEquiv (WithLp.linearEquiv 2 ℂ (V × V')).symm).toRingHom.comp
        (LinearMap.prodMapRingHom ℂ V V')) (uq_kRel_prod ε F F' hR hR')
  have hUG : KUnit ε (uqG F F') := by
    intro a b hab y z
    simp only [WithLp.prod_inner_apply, uqG_apply]
    rw [hU a b hab, hU' a b hab]
  have hxH : KHighest ε (uqG F F') Λ (WithLp.toLp 2 (w, w')) := by
    refine ⟨fun a => WithLp.ofLp_injective 2 ?_, fun a b hlt hab => WithLp.ofLp_injective 2 ?_⟩
    · rw [uqG_apply]
      simp [hw.1 a, hw'.1 a]
    · rw [uqG_apply]
      simp [hw.2 a b hlt hab, hw'.2 a b hlt hab]
  let p₁ : WithLp 2 (V × V') →ₗ[ℂ] V :=
    LinearMap.fst ℂ V V' ∘ₗ (WithLp.linearEquiv 2 ℂ (V × V')).toLinearMap
  let p₂ : WithLp 2 (V × V') →ₗ[ℂ] V' :=
    LinearMap.snd ℂ V V' ∘ₗ (WithLp.linearEquiv 2 ℂ (V × V')).toLinearMap
  have hp₁ : ∀ y, p₁ y = (WithLp.ofLp y).1 := fun _ => rfl
  have hp₂ : ∀ y, p₂ y = (WithLp.ofLp y).2 := fun _ => rfl
  have hb₁ := uq_bij ε (uqG F F') F Λ (WithLp.toLp 2 (w, w')) hRG hUG hxH p₁
    (fun a b hab y => by rw [hp₁, hp₁, uqG_apply] <;> rfl) (by rw [hp₁]; simpa using hw0)
    (by rw [hp₁]; simpa using hT)
  have hb₂ := uq_bij ε (uqG F F') F' Λ (WithLp.toLp 2 (w, w')) hRG hUG hxH p₂
    (fun a b hab y => by rw [hp₂, hp₂, uqG_apply] <;> rfl) (by rw [hp₂]; simpa using hw0')
    (by rw [hp₂]; simpa using hT')
  let e₁ := LinearEquiv.ofBijective (p₁.domRestrict (kSpan ε (uqG F F') (WithLp.toLp 2 (w, w')))) hb₁
  let e₂ := LinearEquiv.ofBijective (p₂.domRestrict (kSpan ε (uqG F F') (WithLp.toLp 2 (w, w')))) hb₂
  have he₁ : ∀ z, e₁ z = p₁ z := fun _ => rfl
  have he₂ : ∀ z, e₂ z = p₂ z := fun _ => rfl
  refine ⟨e₁.symm.trans e₂, ?_, ?_⟩
  · intro a b hab v
    have hmem : uqG F F' a b ((e₁.symm v : _) : WithLp 2 (V × V')) ∈
        kSpan ε (uqG F F') (WithLp.toLp 2 (w, w')) :=
      uq_kSpan_stable ε (uqG F F') _ a b hab _ (e₁.symm v).2
    have hv1 : (WithLp.ofLp ((e₁.symm v : _) : WithLp 2 (V × V'))).1 = v := by
      rw [← hp₁, ← he₁, LinearEquiv.apply_symm_apply]
    have h1 : e₁.symm (F a b v) = ⟨_, hmem⟩ := by
      rw [LinearEquiv.symm_apply_eq, he₁]
      show F a b v = p₁ (uqG F F' a b (e₁.symm v))
      rw [hp₁, uqG_apply, hv1]
    show e₂ (e₁.symm (F a b v)) = F' a b (e₂ (e₁.symm v))
    simp only [h1, he₂, hp₂, uqG_apply]
  · have hx : WithLp.toLp 2 (w, w') ∈ kSpan ε (uqG F F') (WithLp.toLp 2 (w, w')) :=
      uq_mem_kSpan ε _ _
    have h2 : e₁.symm w = ⟨_, hx⟩ := by
      rw [LinearEquiv.symm_apply_eq, he₁, hp₁] <;> simp
    show e₂ (e₁.symm w) = w'
    rw [h2, he₂, hp₂] <;> simp

private theorem eq_bot_of_KStable_of_highest_not_mem (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ)
    (w : V) (hR : KRel ε F) (hU : KUnit ε F) (hw : KHighest ε F Λ w) (hT : kSpan ε F w = ⊤)
    (S : Submodule ℂ V) (hS : KStable ε F S) (hwS : w ∉ S) : S = ⊥ := by
  classical
  obtain ⟨FU, hFUdef⟩ : ∃ FU : Fin n → Fin n → Module.End ℂ (V ⧸ S), FU = fun a b =>
      if h : ε a = ε b then S.mapQ S (F a b) (fun y hy => hS a b h y hy) else 0 := ⟨_, rfl⟩
  have hFU : ∀ a b, ε a = ε b → ∀ y, S.mkQ (F a b y) = FU a b (S.mkQ y) := by
    intro a b h y
    rw [hFUdef]
    simp only [dif_pos h]
    rfl
  have hTU : kSpan ε FU (S.mkQ w) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨y, rfl⟩ := S.mkQ_surjective z
    have hle : kSpan ε F w ≤ (kSpan ε FU (S.mkQ w)).comap S.mkQ :=
      uq_kSpan_le ε F (uq_mem_kSpan ε FU (S.mkQ w)) (fun a b h y hy => by
        show S.mkQ (F a b y) ∈ kSpan ε FU (S.mkQ w)
        rw [hFU a b h y]
        exact uq_kSpan_stable ε FU (S.mkQ w) a b h _ hy)
    have hy : y ∈ kSpan ε F w := by rw [hT]; exact Submodule.mem_top
    exact hle hy
  have hpw : S.mkQ w ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hbij := uq_bij ε F FU Λ w hR hU hw S.mkQ (fun a b h y => hFU a b h y) hpw hTU
  rw [eq_bot_iff]
  intro y hy
  have hy' : y ∈ kSpan ε F w := by rw [hT]; exact Submodule.mem_top
  have h0 : (0 : V) ∈ kSpan ε F w := Submodule.zero_mem _
  have key := hbij.1 (show (S.mkQ.domRestrict (kSpan ε F w)) ⟨y, hy'⟩ =
      (S.mkQ.domRestrict (kSpan ε F w)) ⟨0, h0⟩ by simpa using hy)
  rw [Submodule.mem_bot]
  exact congrArg Subtype.val key

theorem uq_exists_isometry (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V)
    (F' : Fin n → Fin n → Module.End ℂ V') (Λ : Fin n → ℝ) (w : V) (w' : V')
    (hR : KRel ε F) (hR' : KRel ε F') (hU : KUnit ε F) (hU' : KUnit ε F')
    (hw : KHighest ε F Λ w) (hw' : KHighest ε F' Λ w') (hw1 : ‖w‖ = 1) (hw1' : ‖w'‖ = 1)
    (hT : kSpan ε F w = ⊤) (hT' : kSpan ε F' w' = ⊤) :
    ∃ φ : V ≃ₗᵢ[ℂ] V', (∀ a b, ε a = ε b → ∀ v, φ (F a b v) = F' a b (φ v)) ∧ φ w = w' := by
  classical
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw1
  have hw0' : w' ≠ 0 := by rintro rfl; simp at hw1'
  obtain ⟨φ, hφ, hφw⟩ := uq_exists_equiv ε F F' Λ w w' hR hR' hU hU' hw hw' hw0 hw0' hT hT'
  obtain ⟨A, hA⟩ : ∃ A : Module.End ℂ V,
      A = LinearMap.adjoint (φ : V →ₗ[ℂ] V') ∘ₗ (φ : V →ₗ[ℂ] V') := ⟨_, rfl⟩
  have hAinner : ∀ u v, ⟪A u, v⟫_ℂ = ⟪φ u, φ v⟫_ℂ := by
    intro u v
    rw [hA, LinearMap.comp_apply, LinearMap.adjoint_inner_left] <;> rfl
  have hAF : ∀ a b, ε a = ε b → ∀ v, A (F a b v) = F a b (A v) := by
    intro a b hab v
    refine ext_inner_right ℂ fun u => ?_
    rw [hAinner, hφ a b hab, hU' a b hab, ← hφ b a hab.symm, ← hAinner, hU a b hab]
  haveI : Nontrivial V := ⟨⟨w, 0, hw0⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  have hEst : KStable ε F (Module.End.eigenspace A c) := by
    intro a b hab v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [hAF a b hab, hv, map_smul]
  have hwE : w ∈ Module.End.eigenspace A c := by
    by_contra hwE
    exact (Module.End.hasEigenvalue_iff.1 hc) (eq_bot_of_KStable_of_highest_not_mem ε F Λ w hR hU hw hT _ hEst hwE)
  have hEtop : ∀ v, A v = c • v := by
    intro v
    have h := uq_kSpan_le ε F hwE hEst
    rw [hT] at h
    exact Module.End.mem_eigenspace_iff.1 (h Submodule.mem_top)
  have hc1 : (starRingEnd ℂ) c = 1 := by
    have h1 := hAinner w w
    rw [hEtop, inner_smul_left, hφw, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hw1,
      hw1'] at h1
    simpa using h1
  have hinner : ∀ u v, ⟪φ u, φ v⟫_ℂ = ⟪u, v⟫_ℂ := by
    intro u v
    rw [← hAinner, hEtop, inner_smul_left, hc1, one_mul]
  refine ⟨φ.isometryOfInner hinner, fun a b hab v => ?_, ?_⟩
  · first | exact hφ a b hab v | simpa using hφ a b hab v
  · first | exact hφw | simpa using hφw

end

end ReciprocityTheory.ChartRestriction.DS.HW
