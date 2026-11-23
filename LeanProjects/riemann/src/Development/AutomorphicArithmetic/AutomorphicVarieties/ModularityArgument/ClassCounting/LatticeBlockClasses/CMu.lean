import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.MemPowEqv

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cMu :
    UpperTheory.V.ZK.Cl.CMu := by
  intro L F _ _ _ _ _ J _ k _ r b hb hsurj hsplit
  classical
  obtain ⟨cU, cAM, cA, cLoc⟩ := cRes L F k r
  obtain ⟨aV, aMul, aOne, aMem, -, -, -⟩ := cAct L F
  obtain ⟨hs1, hs2⟩ := hsplit
  have cL := (cLoc b hb).1
  have vInt : ∀ (P : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F), HeightOneSpectrum.valuation F P (a : F) ≤ 1 :=
    fun P a => P.valuation_le_one a
  have R0 : ResF r (0 : F) 0 := by simpa using cAM 0
  have Rsub : ∀ (x y : F) (u w : k), ResF r x u → ResF r y w → ResF r (x - y) (u - w) := by
    intro x y u w hx hy
    have h2 := (cA _ _ _ _ hx (cA _ _ _ _ (cAM (-1)) hy).2).1
    have e1 : ((-1 : 𝓞 F) : F) = -1 := by simp
    rw [e1, map_neg, map_one] at h2
    simpa [sub_eq_add_neg] using h2
  have Runiq : ∀ (x : J → F) (v w : Gal(F/L) × J → k), RedV L r x v → RedV L r x w → v = w := by
    intro x v w hv hw
    funext p
    exact cU _ _ _ (hv p.1 p.2) (hw p.1 p.2)
  have L0 : ∀ x : J → F, InLoc b x → ∀ (σ : Gal(F/L)) (j : J), ∃ u, ResF r (σ (x j)) u := by
    intro x hx σ j
    refine (cL (σ (x j)) ?_).2
    intro P hP
    have e : actP σ (actP σ⁻¹ P) = P := by rw [← aMul, mul_inv_cancel, aOne]
    rw [← e, aV]
    exact hx j _ (fun hm => hP ((aMem σ⁻¹ P b).1 hm))
  have Iadd : ∀ x y : J → F, InLoc b x → InLoc b y → InLoc b (x + y) := by
    intro x y hx hy j P hP
    exact le_trans (Valuation.map_add _ _ _) (max_le (hx j P hP) (hy j P hP))
  have Isub : ∀ x y : J → F, InLoc b x → InLoc b y → InLoc b (x - y) := by
    intro x y hx hy j P hP
    exact le_trans (Valuation.map_sub _ _ _) (max_le (hx j P hP) (hy j P hP))
  have Ismul : ∀ (m : 𝓞 L) (x : J → F), InLoc b x → InLoc b ((m : L) • x) := by
    intro m x hx j P hP
    rw [Pi.smul_apply, Algebra.smul_def, map_mul]
    exact mul_le_one' (vInt P (algebraMap (𝓞 L) (𝓞 F) m)) (hx j P hP)
  have GI : ∀ (g : GLoc F J b) (x : J → F), InLoc b x → InLoc b ((g : GG L F J) x) := by
    intro g x hx
    have hg : ∀ z : J → F, InLoc b z ↔ InLoc b ((g : GG L F J) z) := g.2
    exact (hg x).1 hx
  have L1 : ∀ v : Gal(F/L) × J → k, ∃ x : J → F, InLoc b x ∧ RedV L r x v := by
    intro v
    choose a ha using fun j => hs1 (fun σ => v (σ, j))
    refine ⟨fun j => (a j : F), fun j P _ => vInt P (a j), ?_⟩
    intro σ j
    have h := cAM (actO σ (a j))
    rw [ha j σ] at h
    exact h
  have Kz : ∀ (g : GLoc F J b) (y : J → F), InLoc b y → RedV L r y 0 → RedV L r ((g : GG L F J) y) 0 := by
    intro g y hy hy0
    let W : Set (J → F) := {z | RedV L r ((g : GG L F J) z) 0}
    have W0 : (0 : J → F) ∈ W := by
      intro σ j
      show ResF r (σ (((g : GG L F J) 0) j)) 0
      rw [map_zero, Pi.zero_apply, map_zero]
      exact R0
    have Wadd : ∀ z1 z2, z1 ∈ W → z2 ∈ W → z1 + z2 ∈ W := by
      intro z1 z2 h1 h2 σ j
      have := (cA _ _ _ _ (h1 σ j) (h2 σ j)).1
      show ResF r (σ (((g : GG L F J) (z1 + z2)) j)) 0
      rw [map_add, Pi.add_apply, map_add]
      simpa using this
    have Wgen : ∀ (j : J) (c : F), (∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal →
        HeightOneSpectrum.valuation F P c ≤ 1) →
        ∀ m : 𝓞 L, r (algebraMap (𝓞 L) (𝓞 F) m) = 0 → Pi.single j (c * algebraMap L F (m : L)) ∈ W := by
      intro j c hc m hm
      have hs : InLoc b (Pi.single j c : J → F) := by
        intro i P hP
        by_cases hij : i = j
        · subst hij
          simpa using hc P hP
        · simp [Pi.single_apply, hij]
      have e : (Pi.single j (c * algebraMap L F (m : L)) : J → F) = (m : L) • (Pi.single j c : J → F) := by
        ext i
        by_cases hij : i = j
        · subst hij
          simp [Algebra.smul_def, mul_comm]
        · simp [Pi.single_apply, hij]
      intro σ j'
      show ResF r (σ (((g : GG L F J) (Pi.single j (c * algebraMap L F (m : L)))) j')) 0
      rw [e, map_smul, Pi.smul_apply, Algebra.smul_def, map_mul, AlgEquiv.commutes]
      obtain ⟨u, hu⟩ := L0 _ (GI g _ hs) σ j'
      have := (cA _ _ _ _ (cAM (algebraMap (𝓞 L) (𝓞 F) m)) hu).2
      rw [hm, zero_mul] at this
      exact this
    have Wspan : ∀ a ∈ Ideal.map (algebraMap (𝓞 L) (𝓞 F)) (RingHom.ker (r.comp (algebraMap (𝓞 L) (𝓞 F)))),
        ∀ (j : J) (c : F), (∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal →
          HeightOneSpectrum.valuation F P c ≤ 1) → Pi.single j (c * (a : F)) ∈ W := by
      intro a ha
      replace ha : a ∈ Submodule.span (𝓞 F)
          (⇑(algebraMap (𝓞 L) (𝓞 F)) '' (RingHom.ker (r.comp (algebraMap (𝓞 L) (𝓞 F))))) := ha
      induction ha using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, hm, rfl⟩ := hx
        intro j c hc
        exact Wgen j c hc m (RingHom.mem_ker.1 hm)
      | zero =>
        intro j c hc
        simpa using W0
      | add x y _ _ hx hy =>
        intro j c hc
        have := Wadd _ _ (hx j c hc) (hy j c hc)
        simpa [mul_add, Pi.single_add] using this
      | smul c' x _ hx =>
        intro j c hc
        have := hx j (c * (c' : F)) (fun P hP => by
          rw [map_mul]
          exact mul_le_one' (hc P hP) (vInt P c'))
        simpa [mul_assoc] using this
    have hyW : ∀ j, Pi.single j (y j) ∈ W := by
      intro j
      obtain ⟨⟨n, a, hna⟩, -⟩ := cL (y j) (fun P hP => hy j P hP)
      have eβ : algebraMap (𝓞 L) F b = algebraMap (𝓞 F) F (algebraMap (𝓞 L) (𝓞 F) b) := rfl
      rw [eβ] at hna
      have hβ0 : algebraMap (𝓞 F) F (algebraMap (𝓞 L) (𝓞 F) b) ≠ 0 := by
        intro h0
        apply hb
        rw [IsFractionRing.injective (𝓞 F) F (h0.trans (map_zero _).symm), map_zero]
      have hmem : a ∈ Ideal.map (algebraMap (𝓞 L) (𝓞 F)) (RingHom.ker (r.comp (algebraMap (𝓞 L) (𝓞 F)))) := by
        apply hs2
        intro σ
        have h1 := cAM (actO σ a)
        have h2 : ResF r (σ (a : F)) (r (algebraMap (𝓞 L) (𝓞 F) b) ^ n * 0) := by
          rw [← hna, map_mul, map_pow]
          have hb' : σ (algebraMap (𝓞 F) F (algebraMap (𝓞 L) (𝓞 F) b)) =
              algebraMap (𝓞 F) F (algebraMap (𝓞 L) (𝓞 F) b) := AlgEquiv.commutes σ (b : L)
          rw [hb']
          have hbn := cAM (algebraMap (𝓞 L) (𝓞 F) b ^ n)
          rw [map_pow] at hbn
          have hbn' : ResF r (algebraMap (𝓞 F) F (algebraMap (𝓞 L) (𝓞 F) b) ^ n)
              (r (algebraMap (𝓞 L) (𝓞 F) b) ^ n) := by
            simpa using hbn
          exact (cA _ _ _ _ hbn' (hy0 σ j)).2
        rw [mul_zero] at h2
        exact cU _ _ _ h1 h2
      have hyj : y j = ((algebraMap (𝓞 F) F (algebraMap (𝓞 L) (𝓞 F) b)) ^ n)⁻¹ * (a : F) := by
        rw [eq_inv_mul_iff_mul_eq₀ (pow_ne_zero n hβ0)]
        exact hna
      have hc : ∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal →
          HeightOneSpectrum.valuation F P (((algebraMap (𝓞 F) F (algebraMap (𝓞 L) (𝓞 F) b)) ^ n)⁻¹) ≤ 1 := by
        intro P hP
        have h1 : HeightOneSpectrum.valuation F P (algebraMap (𝓞 F) F (algebraMap (𝓞 L) (𝓞 F) b)) = 1 := by
          rw [P.valuation_of_algebraMap]
          exact le_antisymm (P.intValuation_le_one _)
            (not_lt.1 (fun h => hP ((P.intValuation_lt_one_iff_mem _).1 h)))
        rw [map_inv₀, map_pow, h1, one_pow, inv_one]
      rw [hyj]
      exact Wspan a hmem j _ hc
    have hyW' : y ∈ W := by
      rw [← Finset.univ_sum_single y]
      exact Finset.sum_induction _ (· ∈ W) (fun a b ha hb => Wadd a b ha hb) W0 (fun j _ => hyW j)
    exact hyW'
  choose lf hlfI hlfR using L1
  let rd : (J → F) → (Gal(F/L) × J → k) := fun x p =>
    if h : ∃ u, ResF r (p.1 (x p.2)) u then h.choose else 0
  have P1 : ∀ x, InLoc b x → RedV L r x (rd x) := by
    intro x hx σ j
    have h := L0 x hx σ j
    show ResF r (σ (x j)) (if h : ∃ u, ResF r (σ (x j)) u then h.choose else 0)
    rw [dif_pos h]
    exact h.choose_spec
  let T : GLoc F J b → (Gal(F/L) × J → k) → (Gal(F/L) × J → k) := fun g v => rd ((g : GG L F J) (lf v))
  have P3 : ∀ (g : GLoc F J b) (x : J → F) (v : Gal(F/L) × J → k), InLoc b x → RedV L r x v →
      RedV L r ((g : GG L F J) x) (T g v) := by
    intro g x v hx hv
    have hd : RedV L r (x - lf v) 0 := by
      intro σ j
      have := Rsub _ _ _ _ (hv σ j) (hlfR v σ j)
      rw [sub_self] at this
      simpa using this
    have hK := Kz g _ (Isub _ _ hx (hlfI v)) hd
    have hP1 := P1 _ (GI g _ (hlfI v))
    intro σ j
    have := (cA _ _ _ _ (hK σ j) (hP1 σ j)).1
    rw [map_sub, Pi.sub_apply, map_sub, sub_add_cancel] at this
    simpa using this
  have Tadd : ∀ (g : GLoc F J b) v w, T g (v + w) = T g v + T g w := by
    intro g v w
    have h1 := P3 g (lf v + lf w) (v + w) (Iadd _ _ (hlfI v) (hlfI w)) (fun σ j => by
      have := (cA _ _ _ _ (hlfR v σ j) (hlfR w σ j)).1
      simpa using this)
    have h2 : RedV L r ((g : GG L F J) (lf v + lf w)) (T g v + T g w) := by
      intro σ j
      have := (cA _ _ _ _ (P1 _ (GI g _ (hlfI v)) σ j) (P1 _ (GI g _ (hlfI w)) σ j)).1
      rw [map_add, Pi.add_apply, map_add]
      exact this
    exact Runiq _ _ _ h1 h2
  have Tsmul : ∀ (g : GLoc F J b) (c : k) v, T g (c • v) = c • T g v := by
    intro g c v
    obtain ⟨m, hm⟩ := hsurj c
    have hm' : r (algebraMap (𝓞 L) (𝓞 F) m) = c := hm
    have h1 := P3 g _ (c • v) (Ismul m _ (hlfI v)) (fun σ j => by
      have := (cA _ _ _ _ (cAM (algebraMap (𝓞 L) (𝓞 F) m)) (hlfR v σ j)).2
      rw [hm'] at this
      show ResF r (σ (((m : L) • lf v) j)) (c * v (σ, j))
      rw [Pi.smul_apply, Algebra.smul_def, map_mul, AlgEquiv.commutes]
      exact this)
    have h2 : RedV L r ((g : GG L F J) ((m : L) • lf v)) (c • T g v) := by
      intro σ j
      have := (cA _ _ _ _ (cAM (algebraMap (𝓞 L) (𝓞 F) m)) (P1 _ (GI g _ (hlfI v)) σ j)).2
      rw [hm'] at this
      show ResF r (σ (((g : GG L F J) ((m : L) • lf v)) j)) (c * T g v (σ, j))
      rw [map_smul, Pi.smul_apply, Algebra.smul_def, map_mul, AlgEquiv.commutes]
      exact this
    exact Runiq _ _ _ h1 h2
  have Tmul : ∀ (g h : GLoc F J b) v, T (g * h) v = T g (T h v) := by
    intro g h v
    have h1 := P1 _ (GI (g * h) _ (hlfI v))
    have h2 := P3 g _ (T h v) (GI h _ (hlfI v)) (P1 _ (GI h _ (hlfI v)))
    exact Runiq _ _ _ h1 h2
  have Tone : ∀ v, T 1 v = v := by
    intro v
    exact Runiq _ _ _ (P1 _ (GI 1 _ (hlfI v))) (hlfR v)
  let Tl : GLoc F J b → ((Gal(F/L) × J → k) →ₗ[k] (Gal(F/L) × J → k)) := fun g =>
    { toFun := T g
      map_add' := Tadd g
      map_smul' := fun c v => Tsmul g c v }
  refine ⟨{ toFun := fun g => LinearEquiv.ofLinear (Tl g) (Tl g⁻¹)
              (LinearMap.ext fun v => by
                show T g (T g⁻¹ v) = v
                rw [← Tmul, mul_inv_cancel, Tone])
              (LinearMap.ext fun v => by
                show T g⁻¹ (T g v) = v
                rw [← Tmul, inv_mul_cancel, Tone])
            map_one' := LinearEquiv.ext fun v => Tone v
            map_mul' := fun g h => LinearEquiv.ext fun v => Tmul g h v }, ?_⟩
  intro g x v hx hv
  exact P3 g x v hx hv
