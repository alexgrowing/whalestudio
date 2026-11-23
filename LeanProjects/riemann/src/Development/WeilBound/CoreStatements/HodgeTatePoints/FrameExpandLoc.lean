import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
import Development.WeilBound.CoreStatements.HodgeTatePoints.CoefMemDual

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct Filter

namespace PositivityTheory.HtPt.Ge

theorem cancel_gram {Ω : Type} [Field Ω] (L : Subring Ω) {N : ℕ} (G H Z : Matrix (Fin N) (Fin N) Ω) (P Q : Ω)
    (hQ : Q ∈ L) (hH : ∀ i j, H i j ∈ L) (hZ : ∀ i j, Z i j ∈ L) (e : G * H = 1 + (P * Q) • Z)
    (r ζ : Fin N → Ω) (hr : ∀ l, r l ∈ L) (hζ : ∀ l, ζ l ∈ L) (h : Matrix.vecMul r G = P • ζ) :
    ∃ z : Fin N → Ω, (∀ l, z l ∈ L) ∧ r = P • z := by
  refine ⟨Matrix.vecMul ζ H - Q • Matrix.vecMul r Z, ?_, ?_⟩
  · intro l
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine L.sub_mem ?_ (L.mul_mem hQ ?_)
    · simp only [Matrix.vecMul, dotProduct]
      exact L.sum_mem fun i _ => L.mul_mem (hζ i) (hH i l)
    · simp only [Matrix.vecMul, dotProduct]
      exact L.sum_mem fun i _ => L.mul_mem (hr i) (hZ i l)
  · have h1 : Matrix.vecMul r (G * H) = Matrix.vecMul r 1 + Matrix.vecMul r ((P * Q) • Z) := by
      rw [e, Matrix.vecMul_add]
    rw [← Matrix.vecMul_vecMul, h, Matrix.smul_vecMul, Matrix.vecMul_one, Matrix.vecMul_smul] at h1
    rw [smul_sub, smul_smul, h1]
    abel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {B : Subalgebra o Ω} {u : Ω} {hu : u ∈ B}
  {E : Type} [Field E] [NumberField E] {c : E ≃+* E} {p R N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]

theorem frame_expand_loc (hu0 : u ≠ 0) (D : HTChart B Ω c p R N V) {σ : E →+* Ω} {m j k : ℕ}
    {i : Module.Dual B (D.omHT (σ.comp c.toRingHom)) →ₗ[B] (Fin N → B)}
    {bW : Basis (Fin j) B (Module.Dual B (D.omHT (σ.comp c.toRingHom)))} {bM : Basis (Fin k) B (D.omHT σ)}
    {g : Matrix (Fin N) (Fin j ⊕ Fin k) B} (hex : D.ExactMod σ m i) (hg : D.IsFrame σ m i bW bM g)
    (x : Fin N → Ω) (hx : ∀ l, x l ∈ loc B u hu) (t : Fin k → Ω) (ht : ∀ a, t a ∈ loc B u hu)
    (y : V) (hy : y ∈ locM (D.omHT σ) u hu)
    (e : ∑ l, x l • eigProj D.ρΩ σ (D.h (Pi.single l 1)) = ∑ a, t a • (bM a : V) + ((p : Ω) ^ m) • y) :
    ∃ (s : Fin j → Ω) (z : Fin N → Ω), (∀ a, s a ∈ loc B u hu) ∧ (∀ l, z l ∈ loc B u hu) ∧
      ∀ l, x l = ∑ a, (g l (Sum.inl a) : Ω) * s a + ∑ a, (g l (Sum.inr a) : Ω) * t a + (p : Ω) ^ m * z l := by
  have hev : ∀ᶠ n : ℕ in atTop, (∀ l, u ^ n * x l ∈ B) ∧ (∀ a, u ^ n * t a ∈ B) ∧
      u ^ n • y ∈ D.omHT σ :=
    (Filter.eventually_all.2 fun l => loc_ev (hx l)).and
      ((Filter.eventually_all.2 fun a => loc_ev (ht a)).and (locM_ev hy))
  obtain ⟨n, hxn, htn, hyn⟩ := hev.exists
  have hun : u ^ n ≠ 0 := pow_ne_zero n hu0
  let X : Fin N → B := fun l => ⟨u ^ n * x l, hxn l⟩
  let T : Fin k → B := fun a => ⟨u ^ n * t a, htn a⟩
  have hq : D.q σ X = ∑ a, T a • (bM a : V) + ((p : B) ^ m) • (u ^ n • y) := by
    have e' := congrArg (fun v => u ^ n • v) e
    simp only [Finset.smul_sum, smul_add, smul_smul] at e'
    change ∑ l, (u ^ n * x l) • eigProj D.ρΩ σ (D.h (Pi.single l 1)) =
      ∑ a, (u ^ n * t a) • (bM a : V) + (((p : B) ^ m : B) : Ω) • (u ^ n • y)
    rw [e', smul_smul]
    congr 1
    push_cast
    rw [mul_comm]
  obtain ⟨s', z', hsz⟩ := frame_expand D hex hg X T (u ^ n • y) hyn hq
  have hmem : ∀ b : B, (u ^ n)⁻¹ * (b : Ω) ∈ loc B u hu := fun b =>
    loc_of_pow n (by rw [← mul_assoc, mul_inv_cancel₀ hun, one_mul]; exact loc_of_mem b.2)
  refine ⟨fun a => (u ^ n)⁻¹ * s' a, fun l => (u ^ n)⁻¹ * z' l, fun a => hmem _, fun l => hmem _, ?_⟩
  intro l
  have hl := congrArg (fun v : Fin N → B => ((v l : B) : Ω)) hsz
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, X, T] at hl
  push_cast at hl
  apply mul_left_cancel₀ hun
  rw [hl, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    field_simp
  · refine Finset.sum_congr rfl fun a _ => ?_
    ring
  · field_simp

private theorem exists_sum_gram_eq_add_prime_pow_mul {C : Subalgebra o Ω} (D : HTChart C Ω c p R N V) {σ : E →+* Ω} {m j k : ℕ} {d : C}
    {i : Module.Dual C (D.omHT (σ.comp c.toRingHom)) →ₗ[C] (Fin N → C)}
    {W : Basis (Fin j) C (Module.Dual C (D.omHT (σ.comp c.toRingHom)))} {M : Basis (Fin k) C (D.omHT σ)}
    {g : Matrix (Fin N) (Fin j ⊕ Fin k) C} (hi : D.IsDualMap σ d m i) (hg : D.IsFrame σ m i W M g)
    (a : Fin j) (l' : Fin N) :
    ∃ (hY : eigProj D.ρΩ (σ.comp c.toRingHom) (D.h (Pi.single l' 1)) ∈ D.omHT (σ.comp c.toRingHom))
      (z : C) (x' : Fin N → C),
      ∑ l, (g l (Sum.inl a) : Ω) * D.gram σ d l l' =
        (W a ⟨_, hY⟩ : Ω) + (p : Ω) ^ m * z + (p : Ω) ^ m * ∑ l, (x' l : Ω) * D.gram σ d l l' := by
  have hY : eigProj D.ρΩ (σ.comp c.toRingHom) (D.h (Pi.single l' 1)) ∈ D.omHT (σ.comp c.toRingHom) :=
    Submodule.mem_map_of_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨_, rfl⟩))
  obtain ⟨x', hx'⟩ := hg.1 a
  obtain ⟨z, hz⟩ := hi (W a) l' ⟨_, hY⟩ rfl
  refine ⟨hY, z, x', ?_⟩
  have hcol : ∀ l, (g l (Sum.inl a) : Ω) = (i (W a) l : Ω) + (p : Ω) ^ m * x' l := fun l => by
    have h1 := congrFun hx' l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [h1]
    push_cast
    ring
  have hz' : ∑ l, (i (W a) l : Ω) * D.gram σ d l l' = (W a ⟨_, hY⟩ : Ω) + (p : Ω) ^ m * z := by
    have h2 : ∑ l, (i (W a) l : Ω) * D.gram σ d l l' =
        (((W a ⟨_, hY⟩ + (p : C) ^ m * z : C)) : Ω) := hz
    rw [h2]
    push_cast
    ring
  simp only [hcol, add_mul, Finset.sum_add_distrib, hz', Finset.mul_sum, mul_assoc]

theorem overlap [CharZero Ω] [Fact p.Prime] [IsFractionRing B Ω] (hc : ∀ x, c (c x) = x) (hu0 : u ≠ 0)
    {A : Subalgebra o Ω} (hAL : ∀ a ∈ A, a ∈ loc B u hu)
    (DA : HTChart A Ω c p R N V) (DB : HTChart B Ω c p R N V) {σ : E →+* Ω} {m j k : ℕ} (hm : m ≤ R)
    (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ B) (dA : A) (dB : B) (hd : (dA : Ω) = dB) (hdB : GeneratesDiff σ dB)
    (hρ : DA.ρΩ = DB.ρΩ) (he : DA.e = DB.e)
    (hM : ∀ x ∈ DA.omHT σ, ∃ n : ℕ, u ^ n • x ∈ DB.omHT σ)
    (hW : ∀ x ∈ DB.omHT (σ.comp c.toRingHom), ∃ n : ℕ, u⁻¹ ^ n • x ∈ DA.omHT (σ.comp c.toRingHom))
    (hh : ∀ (σ' : E →+* Ω) x, ∃ n : ℕ, ∃ z ∈ DB.omHT σ',
      u ^ n • eigProj DB.ρΩ σ' (DA.h x - DB.h x) = ((p : Ω) ^ m) • z)
    {iA : Module.Dual A (DA.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)}
    {iB : Module.Dual B (DB.omHT (σ.comp c.toRingHom)) →ₗ[B] (Fin N → B)}
    (hiA : DA.IsDualMap σ dA m iA) (hiB : DB.IsDualMap σ dB m iB) (hex : DB.ExactMod σ m iB)
    {WA : Basis (Fin j) A (Module.Dual A (DA.omHT (σ.comp c.toRingHom)))} {MA : Basis (Fin k) A (DA.omHT σ)}
    {WB : Basis (Fin j) B (Module.Dual B (DB.omHT (σ.comp c.toRingHom)))} {MB : Basis (Fin k) B (DB.omHT σ)}
    {gA : Matrix (Fin N) (Fin j ⊕ Fin k) A} {gB : Matrix (Fin N) (Fin j ⊕ Fin k) B}
    (hgA : DA.IsFrame σ m iA WA MA gA) (hgB : DB.IsFrame σ m iB WB MB gB)
    (φA φB : Fin j → Dual Ω V) (hφA : ∀ a z, (WA a z : Ω) = φA a z) (hφB : ∀ a z, (WB a z : Ω) = φB a z)
    (T : Matrix (Fin j) (Fin j) Ω) (hT : ∀ a, φA a = ∑ a', T a' a • φB a')
    (S : Matrix (Fin k) (Fin k) Ω) (hS : ∀ a, (MA a : V) = ∑ a', S a' a • (MB a' : V)) :
    ∃ (X : Matrix (Fin j) (Fin k) Ω) (Z : Matrix (Fin N) (Fin j ⊕ Fin k) Ω),
      (∀ a b, Matrix.fromBlocks T X 0 S a b ∈ loc B u hu) ∧ (∀ a b, Z a b ∈ loc B u hu) ∧
      gA.map (fun a => (a : Ω)) = gB.map (fun a => (a : Ω)) * Matrix.fromBlocks T X 0 S + ((p : Ω) ^ m) • Z := by
  classical
  have huL : u ∈ loc B u hu := loc_of_mem hu
  have hpow_inv : ∀ (n : ℕ) (a : Ω), u ^ n * a ∈ B → a ∈ loc B u hu := fun n a h =>
    loc_of_pow n (loc_of_mem h)
  have hSmem : ∀ b a, S b a ∈ loc B u hu := by
    intro b a
    obtain ⟨n, hn⟩ := hM _ (MA a).2
    refine coef_mem (DB.omHT σ).subtype Subtype.val_injective MB (fun b => S b a) n ⟨_, hn⟩ ?_ b
    simp only [Submodule.subtype_apply]
    rw [hS a]
  have hφBloc : ∀ b w, w ∈ locM (DB.omHT (σ.comp c.toRingHom)) u hu → φB b w ∈ loc B u hu := by
    intro b w hw
    obtain ⟨n, hn⟩ : ∃ n : ℕ, u ^ n • w ∈ DB.omHT (σ.comp c.toRingHom) := hw
    refine hpow_inv n _ ?_
    rw [← smul_eq_mul, ← map_smul, ← hφB b ⟨_, hn⟩]
    exact (WB b _).2
  have hTmem : ∀ b a, T b a ∈ loc B u hu := by
    intro b a
    refine coef_mem_dual (DB.omHT (σ.comp c.toRingHom)) (omHT_fg _ _) WB φB hφB (fun b => T b a) ?_ b
    intro z hz
    show (∑ b, T b a • φB b) z ∈ loc B u hu
    rw [← hT a]
    obtain ⟨n, hn⟩ := hW z hz
    have h1 : φA a (u⁻¹ ^ n • z) ∈ loc B u hu := by
      rw [← hφA a ⟨_, hn⟩]
      exact hAL _ (WA a _).2
    rw [map_smul, smul_eq_mul] at h1
    have h2 := (loc B u hu).mul_mem (pow_mem huL n) h1
    rwa [← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero n hu0), one_mul] at h2
  have hφAloc : ∀ a w, w ∈ locM (DB.omHT (σ.comp c.toRingHom)) u hu → φA a w ∈ loc B u hu := by
    intro a w hw
    rw [hT a, LinearMap.sum_apply]
    exact (loc B u hu).sum_mem fun b _ => by
      rw [LinearMap.smul_apply, smul_eq_mul]
      exact (loc B u hu).mul_mem (hTmem b a) (hφBloc b w hw)
  have hdiff : ∀ (σ' : E →+* Ω) (l : Fin N), ∃ w ∈ locM (DB.omHT σ') u hu,
      eigProj DB.ρΩ σ' (DA.h (Pi.single l 1)) = eigProj DB.ρΩ σ' (DB.h (Pi.single l 1)) + ((p : Ω) ^ m) • w := by
    intro σ' l
    obtain ⟨n, z, hz, hze⟩ := hh σ' (Pi.single l 1)
    have hun : u ^ n ≠ 0 := pow_ne_zero n hu0
    refine ⟨(u ^ n)⁻¹ • z, ⟨n, ?_⟩, ?_⟩
    · rwa [smul_smul, mul_inv_cancel₀ hun, one_smul]
    · rw [smul_comm, ← hze, smul_smul, inv_mul_cancel₀ hun, one_smul, map_sub]
      abel
  have hR : ∀ a : Fin k, ∃ (s : Fin j → Ω) (z : Fin N → Ω), (∀ b, s b ∈ loc B u hu) ∧
      (∀ l, z l ∈ loc B u hu) ∧ ∀ l, (gA l (Sum.inr a) : Ω) = ∑ b, (gB l (Sum.inl b) : Ω) * s b +
        ∑ b, (gB l (Sum.inr b) : Ω) * S b a + (p : Ω) ^ m * z l := by
    intro a
    obtain ⟨yA, hyA, hqA⟩ := hgA.2 a
    choose w hw hwe using hdiff σ
    have hyAloc : yA ∈ locM (DB.omHT σ) u hu := hM yA hyA
    refine frame_expand_loc hu0 DB hex hgB (fun l => gA l (Sum.inr a)) (fun l => hAL _ (gA l _).2)
      (fun b => S b a) (fun b => hSmem b a) (yA - ∑ l, (gA l (Sum.inr a) : Ω) • w l) ?_ ?_
    · exact (locM (DB.omHT σ) u hu).sub_mem hyAloc
        ((locM (DB.omHT σ) u hu).sum_mem fun l _ => locM_smul (hAL _ (gA l _).2) (hw l))
    · have hq' : ∑ l, (gA l (Sum.inr a) : Ω) • eigProj DB.ρΩ σ (DA.h (Pi.single l 1)) =
          (MA a : V) + (p : Ω) ^ m • yA := by
        have h1 := hqA
        simp only [HTChart.q, hρ] at h1
        rw [show ((p : Ω) ^ m) • yA = ((p : A) ^ m) • yA by
          change _ = (((p : A) ^ m : A) : Ω) • yA
          push_cast
          rfl]
        exact h1
      simp only [hwe, smul_add, Finset.sum_add_distrib] at hq'
      rw [← hS a, smul_sub, Finset.smul_sum]
      simp only [smul_comm ((p : Ω) ^ m)]
      rw [← add_sub_assoc, ← hq']
      abel
  have hinj : Function.Injective (algebraMap B Ω) := Subtype.val_injective
  obtain ⟨G, H, Zg, -, hG, hGH, -⟩ := PositivityTheory.HtPt.Ga.gram_unit B Ω hinj E c hc p R N V DB σ dB
    (fun a => ⟨⟨_, hσ a⟩, rfl⟩) hdB
  have hgram : ∀ l l', DA.gram σ dA l l' = DB.gram σ dB l l' := by
    intro l l'
    simp only [HTChart.gram, he]
    rw [show algebraMap A Ω dA = algebraMap B Ω dB from hd]
  have hΓ : ∀ l l', DB.gram σ dB l l' ∈ loc B u hu := fun l l' => by
    rw [← hG]
    exact loc_of_mem (G l l').2
  have hGH' : G.map (algebraMap B Ω) * H.map (algebraMap B Ω) =
      1 + ((p : Ω) ^ m * (p : Ω) ^ (R - m)) • Zg.map (algebraMap B Ω) := by
    rw [← pow_add, Nat.add_sub_cancel' hm, ← Matrix.map_mul, hGH]
    ext i l
    simp [Matrix.one_apply, apply_ite]
  choose hYA zA xA hA using fun a l' => exists_sum_gram_eq_add_prime_pow_mul DA hiA hgA a l'
  choose hYB zB xB hB using fun b l' => exists_sum_gram_eq_add_prime_pow_mul DB hiB hgB b l'
  choose wc hwc hwce using hdiff (σ.comp c.toRingHom)
  have hL : ∀ a : Fin j, ∃ z : Fin N → Ω, (∀ l, z l ∈ loc B u hu) ∧
      ∀ l, (gA l (Sum.inl a) : Ω) = ∑ b, (gB l (Sum.inl b) : Ω) * T b a + (p : Ω) ^ m * z l := by
    intro a
    let v : Fin N → Ω := fun l => (gA l (Sum.inl a) : Ω) - ∑ b, (gB l (Sum.inl b) : Ω) * T b a
    let ζ : Fin N → Ω := fun l' => φA a (wc l') + zA a l' + ∑ l, (xA a l' l : Ω) * DB.gram σ dB l l' -
      ∑ b, T b a * (zB b l' + ∑ l, (xB b l' l : Ω) * DB.gram σ dB l l')
    have hvmem : ∀ l, v l ∈ loc B u hu := fun l =>
      (loc B u hu).sub_mem (hAL _ (gA l _).2)
        ((loc B u hu).sum_mem fun b _ => (loc B u hu).mul_mem (loc_of_mem (gB l _).2) (hTmem b a))
    have hζmem : ∀ l', ζ l' ∈ loc B u hu := by
      intro l'
      refine (loc B u hu).sub_mem ((loc B u hu).add_mem ((loc B u hu).add_mem (hφAloc a _ (hwc l'))
        (hAL _ (zA a l').2)) ((loc B u hu).sum_mem fun l _ =>
          (loc B u hu).mul_mem (hAL _ (xA a l' l).2) (hΓ l l'))) ?_
      exact (loc B u hu).sum_mem fun b _ => (loc B u hu).mul_mem (hTmem b a)
        ((loc B u hu).add_mem (loc_of_mem (zB b l').2) ((loc B u hu).sum_mem fun l _ =>
          (loc B u hu).mul_mem (loc_of_mem (xB b l' l).2) (hΓ l l')))
    have hvec : Matrix.vecMul v (G.map (algebraMap B Ω)) = ((p : Ω) ^ m) • ζ := by
      funext l'
      simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, hG, Pi.smul_apply, smul_eq_mul]
      have eA := hA a l'
      simp only [hgram] at eA
      rw [hφA a] at eA
      have hYeq : ((⟨_, hYA a l'⟩ : DA.omHT (σ.comp c.toRingHom)) : V) =
          eigProj DB.ρΩ (σ.comp c.toRingHom) (DB.h (Pi.single l' 1)) + ((p : Ω) ^ m) • wc l' := by
        rw [← hwce l', ← hρ]
      rw [hYeq, map_add, map_smul, smul_eq_mul] at eA
      have eB : ∀ b, ∑ l, (gB l (Sum.inl b) : Ω) * DB.gram σ dB l l' =
          φB b (eigProj DB.ρΩ (σ.comp c.toRingHom) (DB.h (Pi.single l' 1))) + (p : Ω) ^ m * zB b l' +
            (p : Ω) ^ m * ∑ l, (xB b l' l : Ω) * DB.gram σ dB l l' := by
        intro b
        rw [hB b l', hφB b]
      have hφAY : φA a (eigProj DB.ρΩ (σ.comp c.toRingHom) (DB.h (Pi.single l' 1))) =
          ∑ b, T b a * φB b (eigProj DB.ρΩ (σ.comp c.toRingHom) (DB.h (Pi.single l' 1))) := by
        rw [hT a, LinearMap.sum_apply]
        rfl
      have hsplit : ∑ l, v l * DB.gram σ dB l l' = ∑ l, (gA l (Sum.inl a) : Ω) * DB.gram σ dB l l' -
          ∑ b, T b a * ∑ l, (gB l (Sum.inl b) : Ω) * DB.gram σ dB l l' := by
        simp only [v, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ => by ring
      have hsum : ∑ b, T b a * ∑ l, (gB l (Sum.inl b) : Ω) * DB.gram σ dB l l' =
          ∑ b, T b a * φB b (eigProj DB.ρΩ (σ.comp c.toRingHom) (DB.h (Pi.single l' 1))) +
            (p : Ω) ^ m * ∑ b, T b a * (zB b l' + ∑ l, (xB b l' l : Ω) * DB.gram σ dB l l') := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ => by rw [eB b]; ring
      rw [hsplit, hsum, eA, hφAY]
      simp only [ζ]
      ring
    obtain ⟨z, hz, hvz⟩ := cancel_gram (loc B u hu) (G.map (algebraMap B Ω)) (H.map (algebraMap B Ω))
      (Zg.map (algebraMap B Ω)) ((p : Ω) ^ m) ((p : Ω) ^ (R - m)) (pow_mem (natCast_mem _ p) _)
      (fun i l => loc_of_mem (H i l).2) (fun i l => loc_of_mem (Zg i l).2) hGH' v ζ hvmem hζmem hvec
    refine ⟨z, hz, fun l => ?_⟩
    have h1 := congrFun hvz l
    simp only [v, Pi.smul_apply, smul_eq_mul] at h1
    linear_combination h1
  choose sR zR hsR hzR hRe using hR
  choose zL hzL hLe using hL
  refine ⟨Matrix.of fun b a => sR a b, Matrix.of fun l c => Sum.elim (fun a => zL a l) (fun a => zR a l) c,
    ?_, ?_, ?_⟩
  · rintro (a | a) (b | b)
    · simpa using hTmem a b
    · simpa using hsR b a
    · simpa using (loc B u hu).zero_mem
    · simpa using hSmem a b
  · rintro l (a | a)
    · simpa using hzL a l
    · simpa using hzR a l
  · ext l (a | a)
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, hLe a l]
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, hRe a l]

end PositivityTheory.HtPt.Ge
