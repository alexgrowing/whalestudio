import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.LowAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.ContConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Normal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Lab.exNorm :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (Γ : Type) [Group Γ] [TopologicalSpace Γ] (r : Γ →* M4 𝔞.V) (u : M4 𝔞.V) (pr : Bool) (g0 : Γ) (ν : 𝔞.V),
      𝔞.Small (⟨r, fun _ => u⟩ : PD Unit _ _) → IsUnit (2 : 𝔞.V) → IsUnit ν → IsGSp ν (r g0) → IsGSp 1 u →
      ∀ X u' : M4 𝔞.V, X = adj (wM 𝔞.V pr) * r g0 * wM 𝔞.V pr → u' = adj (wM 𝔞.V pr) * u →
      (∀ i j, i ≠ j → X i j ∈ maximalIdeal 𝔞.V) → (∀ i j, i ≠ j → IsUnit (X i i - X j j)) →
      IsUnit (u' 0 0) → IsUnit (u' 0 0 * u' 1 1 - u' 0 1 * u' 1 0) →
      ∃ (P : PD Unit Γ 𝔞.V) (v b : M4 𝔞.V), 𝔞.Small P ∧ IsGSp 1 v ∧ Cg (maximalIdeal 𝔞.V) v 1 ∧
        (∀ g, P.r g = adj (wM 𝔞.V pr * v) * r g * (wM 𝔞.V pr * v)) ∧ (P.r g0).IsDiag ∧ IsLow (P.n ()) ∧ IsGSp 1 b ∧ IsUp b ∧
        adj (wM 𝔞.V pr * v) * u = P.n () * b := by
  intro l _ 𝔞 Γ _ _ r u pr g0 ν hs h2 hν hr hu X u' hX hu' hoff hdiag h00 hdet
  have gspAdj : ∀ {R : Type} [CommRing R] (μ : R) (g : M4 R), IsUnit μ → IsGSp μ g → IsGSp μ (adj g) := by
    intro R _ μ g hμ hg
    obtain ⟨c, rfl⟩ := hμ
    have hg' : adj g * g = (c : R) • (1 : M4 R) := hg
    have h1 : (((c⁻¹ : Rˣ) : R) • adj g) * g = 1 := by
      rw [Matrix.smul_mul, hg', smul_smul, Units.inv_mul, one_smul]
    have h2 : g * (((c⁻¹ : Rˣ) : R) • adj g) = 1 := mul_eq_one_comm.mp h1
    show adj (adj g) * adj g = (c : R) • (1 : M4 R)
    rw [adj_adj]
    calc g * adj g = (c : R) • (g * (((c⁻¹ : Rˣ) : R) • adj g)) := by
          rw [Matrix.mul_smul, smul_smul, Units.mul_inv, one_smul]
      _ = (c : R) • (1 : M4 R) := by rw [h2]
  obtain ⟨S, _, _, _, f, P₁, hf, hc, hmap⟩ := hs
  haveI := hf.complete
  haveI := hf.loc
  have unitS : ∀ x : S, IsUnit (f x) ↔ IsUnit x := fun x => isUnit_map_iff f x
  have memS : ∀ x : S, x ∈ maximalIdeal S ↔ f x ∈ maximalIdeal 𝔞.V := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, unitS]
  have hr_eq : ∀ g, r g = (P₁.r g).map f := by
    intro g
    have := congrArg (fun P : PD Unit Γ 𝔞.V => P.r g) hmap
    exact this.symm
  have hu_eq : u = (P₁.n ()).map f := by
    have := congrArg (fun P : PD Unit Γ 𝔞.V => P.n ()) hmap
    exact this.symm
  have gspDown : ∀ (g : M4 S) (μ : S), IsGSp (f μ) (g.map f) → IsGSp μ g := by
    intro g μ h
    have h' : adj (g.map f) * g.map f = f μ • (1 : M4 𝔞.V) := h
    rw [adj_map, ← Matrix.map_mul] at h'
    show adj g * g = μ • (1 : M4 S)
    refine Matrix.ext fun i j => hf.inj ?_
    have := congrFun (congrFun h' i) j
    rw [Matrix.map_apply] at this
    rw [this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  set w₁ := wM S pr with hw₁
  set r₀ := P₁.r g0 with hr₀def
  set u₁ := P₁.n () with hu₁def
  have hwmap : wM 𝔞.V pr = w₁.map f := (wM_map f pr).symm
  have hXmap : X = (adj w₁ * r₀ * w₁).map f := by
    rw [hX, hr_eq, hwmap, adj_map, Matrix.map_mul, Matrix.map_mul]
  have hu'map : u' = (adj w₁ * u₁).map f := by
    rw [hu', hu_eq, hwmap, adj_map, Matrix.map_mul]
  set ν₁ := (adj r₀ * r₀) 0 0 with hν₁def
  have hE : (adj r₀ * r₀).map f = ν • (1 : M4 𝔞.V) := by
    rw [Matrix.map_mul, ← adj_map, ← hr_eq]
    exact hr
  have hν₁ : f ν₁ = ν := by
    have := congrFun (congrFun hE 0) 0
    simpa using this
  have hr₀ : IsGSp ν₁ r₀ := by
    apply gspDown
    rw [hν₁, ← hr_eq]
    exact hr
  have hu₁ : IsGSp 1 u₁ := by
    apply gspDown
    rw [map_one, ← hu_eq]
    exact hu
  have h2S : IsUnit (2 : S) := (unitS 2).mp (by rw [map_ofNat]; exact h2)
  have hνS : IsUnit ν₁ := (unitS ν₁).mp (hν₁ ▸ hν)
  have hadjw₁ : IsGSp 1 (adj w₁) := gspAdj 1 w₁ isUnit_one (wM_sp pr)
  have hX₁ : IsGSp ν₁ (adj w₁ * r₀ * w₁) := by
    have := gsp_mul (gsp_mul hadjw₁ hr₀) (wM_sp (R := S) pr)
    simpa using this
  have hoff₁ : ∀ i j, i ≠ j → (adj w₁ * r₀ * w₁) i j ∈ maximalIdeal S := by
    intro i j hij
    rw [memS]
    have := hoff i j hij
    rw [hXmap] at this
    exact this
  have hd₁ : ∀ i j, i ≠ j → IsUnit ((adj w₁ * r₀ * w₁) i i - (adj w₁ * r₀ * w₁) j j) := by
    intro i j hij
    rw [← unitS]
    have := hdiag i j hij
    rw [hXmap] at this
    simpa using this
  obtain ⟨v₁, hv₁, hv₁m, hv₁d, -⟩ := normal S ν₁ (adj w₁ * r₀ * w₁) h2S hX₁ hoff₁ hd₁ hνS
  have hcg : Cg (maximalIdeal S) v₁ 1 := by
    intro i j
    have := hv₁m i j
    rwa [Matrix.sub_apply] at this
  have hadjv : Cg (maximalIdeal S) (adj v₁) 1 := by
    have := Cg.adj hcg
    rwa [adj_one] at this
  have hcgu : Cg (maximalIdeal S) (adj v₁ * (adj w₁ * u₁)) (adj w₁ * u₁) := by
    have := Cg.mul hadjv (Cg.refl (adj w₁ * u₁))
    rwa [one_mul] at this
  have hq : ∀ i j, Ideal.Quotient.mk (maximalIdeal S) ((adj v₁ * (adj w₁ * u₁)) i j) = Ideal.Quotient.mk (maximalIdeal S) ((adj w₁ * u₁) i j) :=
    fun i j => Ideal.Quotient.eq.mpr (hcgu i j)
  have unitOf : ∀ a b : S, Ideal.Quotient.mk (maximalIdeal S) a = Ideal.Quotient.mk (maximalIdeal S) b → IsUnit b → IsUnit a := by
    intro a b hab hb
    by_contra ha
    have ha' : a ∈ maximalIdeal S := (IsLocalRing.mem_maximalIdeal a).mpr ha
    have hb' : b ∈ maximalIdeal S := by
      have hd := Ideal.Quotient.eq.mp hab
      have := (maximalIdeal S).sub_mem ha' hd
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal b).mp hb' hb
  have h00₁ : IsUnit ((adj w₁ * u₁) 0 0) := by
    rw [← unitS]
    rw [hu'map] at h00
    exact h00
  have hdet₁ : IsUnit ((adj w₁ * u₁) 0 0 * (adj w₁ * u₁) 1 1 - (adj w₁ * u₁) 0 1 * (adj w₁ * u₁) 1 0) := by
    rw [← unitS]
    rw [hu'map] at hdet
    simpa using hdet
  have h00'' : IsUnit ((adj v₁ * (adj w₁ * u₁)) 0 0) := unitOf _ _ (hq 0 0) h00₁
  have hdet'' : IsUnit ((adj v₁ * (adj w₁ * u₁)) 0 0 * (adj v₁ * (adj w₁ * u₁)) 1 1 - (adj v₁ * (adj w₁ * u₁)) 0 1 * (adj v₁ * (adj w₁ * u₁)) 1 0) := by
    refine unitOf _ _ ?_ hdet₁
    simp only [map_sub, map_mul, hq]
  have hg'' : IsGSp 1 (adj v₁ * (adj w₁ * u₁)) := by
    have := gsp_mul (gspAdj 1 v₁ isUnit_one hv₁) (gsp_mul hadjw₁ hu₁)
    simpa using this
  obtain ⟨n₁, b₁, hn₁, hb₁, hbu₁, hnb⟩ := Lab.luSp S _ hg'' h00'' hdet''
  set p₁ := w₁ * v₁ with hp₁def
  have hp₁ : IsGSp 1 p₁ := by
    have := gsp_mul (wM_sp (R := S) pr) hv₁
    simpa using this
  have hleft : adj p₁ * p₁ = 1 := by
    have h : adj p₁ * p₁ = (1 : S) • (1 : M4 S) := hp₁
    rw [h, one_smul]
  have hright : p₁ * adj p₁ = 1 := by
    have h : adj (adj p₁) * adj p₁ = (1 : S) • (1 : M4 S) := gspAdj 1 p₁ isUnit_one hp₁
    rw [adj_adj, one_smul] at h
    exact h
  let r₂ : Γ →* M4 S :=
    { toFun := fun g => adj p₁ * P₁.r g * p₁
      map_one' := by
        simp only [map_one, mul_one]
        exact hleft
      map_mul' := by
        intro a b
        simp only [map_mul]
        calc adj p₁ * (P₁.r a * P₁.r b) * p₁ = adj p₁ * P₁.r a * (p₁ * adj p₁) * P₁.r b * p₁ := by
              rw [hright, mul_one]
              simp only [mul_assoc]
          _ = adj p₁ * P₁.r a * p₁ * (adj p₁ * P₁.r b * p₁) := by simp only [mul_assoc] }
  let P₂ : PD Unit Γ S := ⟨r₂, fun _ => n₁⟩
  have hcont : P₂.Cont (maximalIdeal S) := Lab.contConj Γ S (maximalIdeal S) (fun g => P₁.r g) (adj p₁) p₁ hc
  have hone : ∀ i j, (1 : M4 𝔞.V) i j = f ((1 : M4 S) i j) := by
    intro i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  refine ⟨P₂.map f, v₁.map f, b₁.map f, ⟨S, _, _, _, f, P₂, hf, hcont, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := gsp_map f hv₁
    rwa [map_one] at this
  · intro i j
    have := (memS _).mp (hcg i j)
    rw [map_sub, ← hone] at this
    exact this
  · intro g
    show (adj p₁ * P₁.r g * p₁).map f = _
    rw [hr_eq g, hwmap, ← Matrix.map_mul, adj_map, Matrix.map_mul, Matrix.map_mul]
  · show (adj p₁ * r₀ * p₁).map f |>.IsDiag
    have he : adj p₁ * r₀ * p₁ = adj v₁ * (adj w₁ * r₀ * w₁) * v₁ := by
      rw [hp₁def, adj_mul]
      simp only [mul_assoc]
    rw [he]
    exact hv₁d.map (map_zero f)
  · show IsLow (n₁.map f)
    obtain ⟨hn1, hn2, hn3⟩ := hn₁
    refine ⟨?_, ?_, ?_⟩
    · have := gsp_map f hn1
      rwa [map_one] at this
    · intro i
      simp [Matrix.map_apply, hn2 i]
    · intro i j hij
      simp [Matrix.map_apply, hn3 i j hij]
  · have := gsp_map f hb₁
    rwa [map_one] at this
  · intro i j hij
    simp [Matrix.map_apply, hbu₁ i j hij]
  · show adj (wM 𝔞.V pr * v₁.map f) * u = n₁.map f * b₁.map f
    rw [hu_eq, hwmap, ← Matrix.map_mul, adj_map, ← Matrix.map_mul, ← Matrix.map_mul, ← hnb]
    congr 1
    rw [adj_mul]
    simp only [mul_assoc]
