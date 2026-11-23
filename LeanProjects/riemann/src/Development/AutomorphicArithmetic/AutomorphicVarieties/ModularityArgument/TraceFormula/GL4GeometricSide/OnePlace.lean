import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open scoped InnerProductSpace

noncomputable section

namespace UpperTheory.V.Z.GSp4Splitting.OnePlaceCyclotomic

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E1 E2 : Fin n → Fin n → Module.End ℂ V}

private theorem mem1 (a b : Fin n) : E1 a b ∈ alg E1 E2 := Algebra.subset_adjoin ⟨a, b, Or.inl rfl⟩

private theorem mem2 (a b : Fin n) : E2 a b ∈ alg E1 E2 := Algebra.subset_adjoin ⟨a, b, Or.inr rfl⟩

private theorem adj (h : IsPair E1 E2) {a : Module.End ℂ V} (ha : a ∈ alg E1 E2) :
    ∃ a' ∈ alg E1 E2, ∀ x y : V, ⟪a x, y⟫_ℂ = ⟪x, a' y⟫_ℂ := by
  have key : ∀ a b (x y : V), ⟪E1 a b x, y⟫_ℂ = ⟪x, E2 b a y⟫_ℂ ∧ ⟪E2 a b x, y⟫_ℂ = ⟪x, E1 b a y⟫_ℂ := by
    intro a b x y
    have h1 := h.unitK a b x y
    have h2 := h.unitP a b x y
    simp only [kF, pF, LinearMap.add_apply, LinearMap.sub_apply, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right] at h1 h2
    exact ⟨by linear_combination (h1 + h2) / 2, by linear_combination (h1 - h2) / 2⟩
  induction ha using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨a, b, rfl | rfl⟩ := hz
    · exact ⟨_, mem2 b a, fun x y => (key a b x y).1⟩
    · exact ⟨_, mem1 b a, fun x y => (key a b x y).2⟩
  | algebraMap c =>
    refine ⟨algebraMap ℂ _ (starRingEnd ℂ c), Subalgebra.algebraMap_mem _ _, fun x y => ?_⟩
    simp [Module.algebraMap_end_apply, inner_smul_left, inner_smul_right, mul_comm]
  | add u v _ _ hu hv =>
    obtain ⟨u', hu', hu⟩ := hu
    obtain ⟨v', hv', hv⟩ := hv
    exact ⟨u' + v', add_mem hu' hv', fun x y => by simp [inner_add_left, inner_add_right, hu, hv]⟩
  | mul u v _ _ hu hv =>
    obtain ⟨u', hu', hu⟩ := hu
    obtain ⟨v', hv', hv⟩ := hv
    exact ⟨v' * u', mul_mem hv' hu', fun x y => by simp [hu, hv]⟩

private theorem twist {A : Module.End ℂ V} (hA : A * A = 1) (hE : ∀ a b, A * E1 a b = E2 a b * A)
    {a : Module.End ℂ V} (ha : a ∈ alg E1 E2) : A * a * A ∈ alg E1 E2 := by
  induction ha using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨a, b, rfl | rfl⟩ := hz
    · rw [hE, mul_assoc, hA, mul_one]; exact mem2 a b
    · rw [mul_assoc, ← hE, ← mul_assoc, hA, one_mul]; exact mem1 a b
  | algebraMap c =>
    rw [← Algebra.commutes, mul_assoc, hA, mul_one]; exact Subalgebra.algebraMap_mem _ _
  | add u v _ _ hu hv => rw [mul_add, add_mul]; exact add_mem hu hv
  | mul u v _ _ hu hv =>
    have : A * (u * v) * A = (A * u * A) * (A * v * A) := by
      calc A * (u * v) * A = A * u * (A * A) * v * A := by rw [hA]; simp only [mul_assoc, mul_one, one_mul]
        _ = _ := by simp only [mul_assoc]
    rw [this]; exact mul_mem hu hv

variable (E1 E2) in

private def cyc (x : V) : Submodule ℂ V where
  carrier := {y | ∃ a ∈ alg E1 E2, a x = y}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, add_mem ha hb, rfl⟩
  zero_mem' := ⟨0, zero_mem _, rfl⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    exact ⟨c • a, Subalgebra.smul_mem _ ha c, rfl⟩

private theorem cyc_self (x : V) : x ∈ cyc E1 E2 x := ⟨1, one_mem _, rfl⟩

private theorem cyc_stab {x y : V} {a : Module.End ℂ V} (ha : a ∈ alg E1 E2) (hy : y ∈ cyc E1 E2 x) :
    a y ∈ cyc E1 E2 x := by
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a * b, mul_mem ha hb, rfl⟩

private theorem cyc_K {x : V} (a b : Fin n) : ∀ y ∈ cyc E1 E2 x, kF E1 E2 a b y ∈ cyc E1 E2 x :=
  fun _ hy => cyc_stab (add_mem (mem1 a b) (mem2 a b)) hy

section Res

variable {X : Submodule ℂ V}

private theorem epow_coe {F : Fin n → Fin n → Module.End ℂ V} {F' : Fin n → Fin n → Module.End ℂ X}
    (h : ∀ a b x, (F' a b x : V) = F a b x) (m : ℕ) : ∀ a b x, (epow F' m a b x : V) = epow F m a b x := by
  induction m with
  | zero => intro a b x; simp only [epow]; split_ifs <;> simp
  | succ m ih => intro a b x; simp [epow, LinearMap.sum_apply, h, ih]

private theorem gelA_coe {F : Fin n → Fin n → Module.End ℂ V} {F' : Fin n → Fin n → Module.End ℂ X}
    (h : ∀ a b x, (F' a b x : V) = F a b x) (m : ℕ) (x : X) : (gelA F' m x : V) = gelA F m x := by
  simp [gelA, LinearMap.sum_apply, epow_coe h]

private theorem gl_res {F : Fin n → Fin n → Module.End ℂ V} {F' : Fin n → Fin n → Module.End ℂ X}
    (h : ∀ a b x, (F' a b x : V) = F a b x) (hF : Formalism.REAL.GlRel F) : Formalism.REAL.GlRel F' := by
  intro a b c d
  have := hF a b c d
  ext x
  have h2 := LinearMap.congr_fun this x
  split_ifs at h2 ⊢ <;> simpa [h] using h2

private theorem alg_res {E1' E2' : Fin n → Fin n → Module.End ℂ X}
    (h1 : ∀ a b x, (E1' a b x : V) = E1 a b x) (h2 : ∀ a b x, (E2' a b x : V) = E2 a b x)
    {a : Module.End ℂ V} (ha : a ∈ alg E1 E2) : ∃ a' ∈ alg E1' E2', ∀ x : X, (a' x : V) = a x := by
  induction ha using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨a, b, rfl | rfl⟩ := hz
    · exact ⟨_, mem1 a b, h1 a b⟩
    · exact ⟨_, mem2 a b, h2 a b⟩
  | algebraMap c =>
    exact ⟨algebraMap ℂ _ c, Subalgebra.algebraMap_mem _ _, fun x => by simp [Module.algebraMap_end_apply]⟩
  | add u v _ _ hu hv =>
    obtain ⟨u', hu', hu⟩ := hu
    obtain ⟨v', hv', hv⟩ := hv
    exact ⟨u' + v', add_mem hu' hv', fun x => by simp [hu, hv]⟩
  | mul u v _ _ hu hv =>
    obtain ⟨u', hu', hu⟩ := hu
    obtain ⟨v', hv', hv⟩ := hv
    exact ⟨u' * v', mul_mem hu' hv', fun x => by simp [hu, hv]⟩

private theorem pair_res {E1' E2' : Fin n → Fin n → Module.End ℂ X}
    (h1 : ∀ a b x, (E1' a b x : V) = E1 a b x) (h2 : ∀ a b x, (E2' a b x : V) = E2 a b x) (h : IsPair E1 E2) :
    IsPair E1' E2' where
  gl1 := gl_res h1 h.gl1
  gl2 := gl_res h2 h.gl2
  comm a b c d := by
    ext x
    simpa [h1, h2] using LinearMap.congr_fun (h.comm a b c d) x
  unitK a b x y := by simpa [kF, h1, h2, Submodule.coe_inner] using h.unitK a b x y
  unitP a b x y := by simpa [pF, h1, h2, Submodule.coe_inner] using h.unitP a b x y

private theorem fin_comap {S : Submodule ℂ V} (hS : FiniteDimensional ℂ S) :
    FiniteDimensional ℂ (S.comap X.subtype) :=
  FiniteDimensional.of_injective (X.subtype.restrict (p := S.comap X.subtype) (q := S) fun _ hx => hx)
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : S => (z : V)) h))

private theorem der_res {σ : Un n →* (V →ₗ[ℂ] V)} {σ' : Un n →* (X →ₗ[ℂ] X)} {F : Fin n → Fin n → Module.End ℂ V}
    {F' : Fin n → Fin n → Module.End ℂ X} (h : ∀ a b x, (F' a b x : V) = F a b x)
    (hσ : ∀ k x, (σ' k x : V) = σ k x) (hd : IsDerivK σ F) : IsDerivK σ' F' := by
  refine ⟨fun k x y => by simpa [Submodule.coe_inner, hσ] using hd.1 k x y, fun v => ?_⟩
  obtain ⟨S, hfd, hv, hs, hk, hder⟩ := hd.2 v
  refine ⟨S.comap X.subtype, fin_comap hfd, hv, fun k w hw => ?_, fun a b w hw => ?_, fun Y γ hγ w hw => ?_⟩
  · show (σ' k w : V) ∈ S
    rw [hσ]; exact hs k _ hw
  · show (F' a b w : V) ∈ S
    rw [h]; exact hk a b _ hw
  · have h0 : HasDerivAt (fun t : ℝ => (σ' (γ t) w : V)) ((∑ a, ∑ b, Y a b • F' a b w : X) : V) 0 := by
      simpa [hσ, h] using hder Y γ hγ w hw
    rw [hasDerivAt_iff_isLittleO_nhds_zero] at h0 ⊢
    exact Asymptotics.isLittleO_norm_left.1 h0.norm_left

private theorem isK_res {σ : Un n →* (V →ₗ[ℂ] V)} {σ' : Un n →* (X →ₗ[ℂ] X)}
    (hσ : ∀ k x, (σ' k x : V) = σ k x) (hK : IsK σ) : IsK σ' where
  iso k x y := by simpa [Submodule.coe_inner, hσ] using hK.iso k x y
  fin v := by
    obtain ⟨S, hfd, hv, hs⟩ := hK.fin v
    refine ⟨S.comap X.subtype, fin_comap hfd, hv, fun k w hw => ?_⟩
    show (σ' k w : V) ∈ S
    rw [hσ]; exact hs k _ hw
  cont v w := by simpa [Submodule.coe_inner, hσ] using hK.cont v w

private theorem rep_res {σ : Un n →* (V →ₗ[ℂ] V)} (h : ∀ k, ∀ x ∈ X, σ k x ∈ X) :
    ∃ σ' : Un n →* (X →ₗ[ℂ] X), ∀ k x, (σ' k x : V) = σ k x :=
  ⟨{ toFun := fun k => (σ k).restrict (h k)
     map_one' := by ext x; simp
     map_mul' := fun a b => by ext x; simp }, fun _ _ => rfl⟩

private theorem trOn_res {S : Submodule ℂ V} (hSX : S ≤ X) {f : Module.End ℂ V} {f' : Module.End ℂ X}
    (h : ∀ x, (f' x : V) = f x) : trOn (S.comap X.subtype) f' = trOn S f := by
  have hiff : (∀ x ∈ S.comap X.subtype, f' x ∈ S.comap X.subtype) ↔ ∀ x ∈ S, f x ∈ S := by
    constructor
    · intro H x hx
      have := H ⟨x, hSX hx⟩ hx
      rwa [Submodule.mem_comap, Submodule.subtype_apply, h] at this
    · intro H x hx
      rw [Submodule.mem_comap, Submodule.subtype_apply, h]
      exact H _ hx
  unfold trOn
  by_cases H : ∀ x ∈ S, f x ∈ S
  · rw [dif_pos H, dif_pos (hiff.2 H), ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hSX)]
    congr 1
    ext x
    simp [LinearEquiv.conj_apply, h, Submodule.comapSubtypeEquivOfLe]
  · rw [dif_neg H, dif_neg fun H' => H (hiff.1 H')]

private theorem iso_res {σ : Un n →* (V →ₗ[ℂ] V)} {σ' : Un n →* (X →ₗ[ℂ] X)}
    (hσ : ∀ k x, (σ' k x : V) = σ k x) (hK : IsK σ) (E : KMod n) {S : Submodule ℂ V} (hfd : FiniteDimensional ℂ S)
    (hSX : S ≤ X) (hSi : S ≤ isoSp σ E) (hS : ∀ x ∈ X, x ∈ isoSp σ E → x ∈ S) (hst : ∀ k, ∀ x ∈ S, σ k x ∈ S) :
    isoSp σ' E = S.comap X.subtype := by
  apply le_antisymm
  · refine iSup_le fun t => ?_
    rintro _ ⟨ξ, rfl⟩
    refine hS _ (t.1 ξ).2 ?_
    have ht : X.subtype ∘ₗ t.1 ∈ invA σ E := fun k ξ => by
      show ((t.1 _ : X) : V) = σ k (t.1 ξ : X)
      rw [t.2 k ξ, hσ]
    exact le_iSup (fun t : invA σ E => LinearMap.range t.1) ⟨_, ht⟩ ⟨ξ, rfl⟩
  · haveI : CompleteSpace S := FiniteDimensional.complete ℂ S
    have heq : ∀ k v, S.starProjection (σ k v) = σ k (S.starProjection v) := by
      intro k v
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hst k _ (S.starProjection_apply_mem v)) fun w hw => ?_
      have hw' : w = σ k (σ k⁻¹ w) := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [← map_sub, hw', hK.iso]
      exact S.starProjection_inner_eq_zero v _ (hst _ _ hw)
    let p : V →ₗ[ℂ] X := S.starProjection.toLinearMap.codRestrict X fun v => hSX (S.starProjection_apply_mem v)
    have hp : isoSp σ E ≤ (isoSp σ' E).comap p := by
      refine iSup_le fun t => ?_
      rintro _ ⟨ξ, rfl⟩
      have ht : p ∘ₗ t.1 ∈ invA σ' E := fun k ξ => by
        apply Subtype.ext
        rw [hσ]
        show S.starProjection (t.1 _) = σ k (S.starProjection (t.1 ξ))
        rw [t.2 k ξ, heq]
      exact le_iSup (fun t : invA σ' E => LinearMap.range t.1) ⟨_, ht⟩ ⟨ξ, rfl⟩
    intro x hx
    have h1 : p x = x := Subtype.ext (Submodule.starProjection_eq_self_iff.2 hx)
    have h2 : p x ∈ isoSp σ' E := hp (hSi hx)
    rwa [h1] at h2

end Res

end UpperTheory.V.Z.GSp4Splitting.OnePlaceCyclotomic

open UpperTheory.V.Z.GSp4Splitting.OnePlaceCyclotomic in
theorem UpperTheory.V.Z.GSp4Splitting.onePlace :
    CoreG → LieStab → ProjEx → AvgFacts → AvgTr → OnePlace := by
  intro hC hL hPr hAF hAT n lam hlam E T hT _ _ ν _ hν V _ _ E1 E2 σ A P hloc hP S hfd hne hSi hAS hSa hSs
  obtain ⟨x0, hx0, hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨e, he1, he2, he3, he4, -, he6⟩ := hPr n V σ hloc.isK E
  have hσc : ∀ x k, ∀ y ∈ cyc E1 E2 x, σ k y ∈ cyc E1 E2 x := fun x => hL n V σ _ hloc.der _ cyc_K
  set X := cyc E1 E2 x0 with hX
  have hSX : S ≤ X := fun y hy => hSs x0 hx0 y hy hx00
  have hXS : ∀ x ∈ X, x ∈ isoSp σ E → x ∈ S := by
    rintro _ ⟨a, ha, rfl⟩ hi
    exact hSa a ha x0 hx0 hi
  have hAX : ∀ x ∈ X, A x ∈ X := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 := cyc_stab (twist hloc.Asq hloc.AE ha) (hSX (hAS x0 hx0))
    have h2 : (A * a * A) (A x0) = A (a x0) := by
      rw [← Module.End.mul_apply, mul_assoc, hloc.Asq, mul_one, Module.End.mul_apply]
    rwa [h2] at h1
  have hσS : ∀ k, ∀ x ∈ S, σ k x ∈ S := by
    intro k x hx
    refine hXS _ (hσc x0 k x (hSX hx)) ?_
    have h1 := LinearMap.congr_fun (he4 k) x
    simp only [Module.End.mul_apply] at h1
    rw [he3 x (hSi hx)] at h1
    rw [← h1]
    exact he2 _
  have hirr : ∀ v ∈ X, ∀ w ∈ X, v ≠ 0 → w ∈ cyc E1 E2 v := by
    intro v hv w hw hv0
    have hle : cyc E1 E2 v ≤ X := by
      rintro _ ⟨a, ha, rfl⟩
      exact cyc_stab ha hv
    by_cases h0 : ∀ y ∈ cyc E1 E2 v, e y = 0
    · exfalso
      apply hv0
      obtain ⟨a, ha, hav⟩ := hv
      obtain ⟨a', ha', hadj⟩ := adj hloc.pair ha
      have h1 : ⟪a x0, v⟫_ℂ = 0 := by
        rw [hadj, ← he3 x0 (hSi hx0), he1, h0 _ (cyc_stab ha' (cyc_self v)), inner_zero_right]
      rw [hav] at h1
      exact inner_self_eq_zero.1 h1
    · push Not at h0
      obtain ⟨y, hy, hy0⟩ := h0
      have h1 : e y ∈ cyc E1 E2 v := he6 _ (hσc v) y hy
      obtain ⟨b, hb, hbx⟩ := hSs _ (hXS _ (hle h1) (he2 y)) x0 hx0 hy0
      obtain ⟨a, ha, rfl⟩ := hw
      exact cyc_stab ha (hbx ▸ cyc_stab hb h1)
  obtain ⟨σ', hσ⟩ := rep_res (X := X) (hσc x0)
  let E1' : Fin n → Fin n → Module.End ℂ X := fun a b => (E1 a b).restrict fun _ hy => cyc_stab (mem1 a b) hy
  let E2' : Fin n → Fin n → Module.End ℂ X := fun a b => (E2 a b).restrict fun _ hy => cyc_stab (mem2 a b) hy
  have h1 : ∀ a b x, (E1' a b x : V) = E1 a b x := fun _ _ _ => rfl
  have h2 : ∀ a b x, (E2' a b x : V) = E2 a b x := fun _ _ _ => rfl
  let A' : Module.End ℂ X := A.restrict hAX
  have hA : ∀ x, (A' x : V) = A x := fun _ => rfl
  have hPX : ∀ x ∈ X, P x ∈ X := (hAF n ν V σ hloc.isK E T P hT.1 hP).2.2.2.1 X (hσc x0)
  let P' : Module.End ℂ X := P.restrict hPX
  have hP' : ∀ x, (P' x : V) = P x := fun _ => rfl
  clear_value E1' E2' A' P'
  have hAσ : ∀ k, A' * σ' k = σ' k * A' := fun k => by
    ext x
    simpa [hA, hσ] using LinearMap.congr_fun (hloc.Aσ k) x
  have hcore : IsCoreMod (infOf lam) E1' E2' σ' A' :=
    { pair := pair_res h1 h2 hloc.pair
      ch1 := fun m x => Subtype.ext (by rw [gelA_coe h1, hloc.ch1]; rfl)
      ch2 := fun m x => Subtype.ext (by
        rw [gelA_coe (F := barF E2) (fun a b y => by simp [barF, h2]), hloc.ch2]; rfl)
      nontriv := ⟨⟨⟨x0, cyc_self x0⟩, 0, fun h => hx00 (congrArg Subtype.val h)⟩⟩
      irr := fun v w hv => by
        obtain ⟨a, ha, hav⟩ := hirr v v.2 w w.2 fun h => hv (Subtype.ext h)
        obtain ⟨a', ha', haa⟩ := alg_res h1 h2 ha
        exact ⟨a', ha', Subtype.ext (by rw [haa, hav])⟩
      der := der_res (F := kF E1 E2) (fun a b x => by simp [kF, h1, h2]) hσ hloc.der
      Asq := by
        ext x
        simpa [hA] using LinearMap.congr_fun hloc.Asq x
      Aiso := fun x y => by simpa [Submodule.coe_inner, hA] using hloc.Aiso x y
      Aσ := hAσ
      AE := fun a b => by
        ext x
        simpa [hA, h1, h2] using LinearMap.congr_fun (hloc.AE a b) x }
  have hiso := iso_res hσ hloc.isK E hfd hSX hSi hXS hσS
  have havg : IsAvg ν σ' E T P' := fun v w => by
    simpa only [Submodule.coe_inner, hσ, hP'] using hP v w
  obtain ⟨hf, hn, htr⟩ := hAT n ν hν X σ' (isK_res hσ hloc.isK) E T P' A' hT.1 havg hAσ (hiso ▸ fin_comap hfd)
  have hne' : isoSp σ' E ≠ ⊥ := by
    rw [hiso]
    intro h
    have hm : (⟨x0, cyc_self x0⟩ : X) ∈ S.comap X.subtype := hx0
    rw [h] at hm
    exact hx00 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 hm))
  obtain ⟨s, hs, hst⟩ := hC n lam hlam E T hT X E1' E2' σ' A' hcore hf (hn hne')
  rw [hiso, trOn_res hSX (f := P * A) (fun x => by simp [hP', hA]), hst] at htr
  rcases hs with rfl | rfl
  · left; rw [htr, one_mul]
  · right; rw [htr, neg_one_mul]
