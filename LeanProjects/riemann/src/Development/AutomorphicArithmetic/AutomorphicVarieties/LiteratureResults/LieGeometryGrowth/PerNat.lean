import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr
open scoped TensorProduct

private theorem hd_map {Γ M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (P : M →ₗ[ℂ] N)
    (b : List Γ → M) : hd (fun z => P (b z)) = fun z => P (hd b z) := by
  funext z
  simp only [hd, map_sum, map_zsmul]

private theorem zig_map {Γ V S S' : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (G : Dr.Geo Γ V S d) (G' : Dr.Geo Γ V S' d) (f : S' → S) (P : ∀ q, G.Om q →ₗ[ℂ] G'.Om q)
    (ha : ∀ q γ w, P q (G.act q γ w) = G'.act q γ (P q w))
    (hD : ∀ q w, P (q + 1) (G.dOm q w) = G'.dOm q (P q w))
    (hi : ∀ c, P 0 (G.incl c) = G'.incl (c ∘ f)) (c : List Γ → S → Fin d → ℂ) (q : ℕ) :
    ∀ (k : ℕ) (u : List Γ → G.Om q), Zig G q k u c → Zig G' q k (fun z => P q (u z)) (fun z => c z ∘ f) := by
  induction q with
  | zero =>
    intro k u h z hz
    beta_reduce
    rw [h z hz, hi]
  | succ q ih =>
    rintro k u ⟨b, h1, h2, h3⟩
    refine ⟨fun z => P q (b z), fun γ z hz => ?_, fun z hz => ?_, ?_⟩
    · beta_reduce
      rw [h1 γ z hz, ha]
    · beta_reduce
      rw [← h2 z hz, hD]
    · rw [hd_map]
      exact ih _ _ h3

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private def pb (ho : IsOpen (cone E a)) (U U' : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (f : GL (Fin a) (Af E) ⧸ U' → GL (Fin a) (Af E) ⧸ U) (q : ℕ) : (geo ho U Ξ).Om q →ₗ[ℂ] (geo ho U' Ξ).Om q where
  toFun w := ⟨fun s => w.1 (f s), fun s => w.2 (f s)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem ev_rT {d : ℕ} (x : GL (Fin a) (Af E)) (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) :
    ev ((act (.fin x)).rTensor (Fin d → ℂ) m) g = ev m (g * finGL E a x) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v => rfl
  | add m m' h h' => simp only [map_add, Pi.add_apply, h, h']

private theorem rT_map' {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T A : Module.End ℂ W)
    (B : Module.End ℂ (Fin d → ℂ)) (h : A * T = T * A) (m : W ⊗[ℂ] (Fin d → ℂ)) :
    T.rTensor _ (TensorProduct.map A B m) = TensorProduct.map A B (T.rTensor _ m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul]
    congr 1
    exact (LinearMap.congr_fun h φ).symm

private theorem cpt_fin (k : Kinf E a) (x : GL (Fin a) (Af E)) :
    act (.cpt k) * act (.fin x) = act (.fin x) * act (E := E) (.cpt k) := by
  change rt E a _ * rt E a _ = rt E a _ * rt E a _
  rw [← map_mul, ← map_mul]
  exact congrArg _ (infGL_comm _ _)

private theorem rT_lie (Ξ : AlgRep E a) (x : GL (Fin a) (Af E)) (X : Lie E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (smLie Ξ X m) = smLie Ξ X ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) m) := by
  have h1 := rT_map' (act (.fin x)) (lie E a X) LinearMap.id (lie_rt_fin X x) m
  have h2 := rT_map' (act (.fin x)) LinearMap.id (Matrix.toLin' (Ξ.dmat X)) rfl m
  change (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (_ + _) = _ + _
  rw [map_add]
  exact congrArg₂ (· + ·) h1 h2

private theorem lev_fin {U U' : Subgroup (GL (Fin a) (Af E))} {x : GL (Fin a) (Af E)} (hx : ∀ u ∈ U', x⁻¹ * u * x ∈ U)
    (Ξ : AlgRep E a) {φ : Sm E a} (h : IsLevelFn U Ξ φ) : IsLevelFn U' Ξ (act (.fin x) φ) := by
  refine ⟨fun γ g => ?_, fun u hu => ?_, fun m hm => ?_⟩
  · change φ.1 (ratGL E a γ * g * finGL E a x) = φ.1 (g * finGL E a x)
    rw [mul_assoc, h.1]
  · refine Subtype.ext (funext fun g => ?_)
    have e : φ.1 (g * finGL E a x * finGL E a (x⁻¹ * u * x)) = φ.1 (g * finGL E a x) :=
      congrFun (congrArg Subtype.val (h.2.1 _ (hx u hu))) (g * finGL E a x)
    change φ.1 (g * finGL E a u * finGL E a x) = φ.1 (g * finGL E a x)
    rw [← e, mul_assoc, mul_assoc, ← map_mul, ← map_mul]
    congr 3
    group
  · have e : lie E a (oneL E a) (act (.fin x) φ) = act (.fin x) (lie E a (oneL E a) φ) :=
      LinearMap.congr_fun (lie_rt_fin (oneL E a) x) φ
    rw [e, h.2.2 m hm, map_smul]

end

theorem UpperTheory.V.Lit.Geo.perNat :
    PerNat := by
  intro E _ _ _ a U U' x hx Ξ q α hα
  refine ⟨⟨fun k X => ?_, fun X i hi => ?_, fun X => ?_⟩, ?_, fun c c' hc h => ?_⟩
  · change (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α _) = smK Ξ k ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α X))
    rw [hα.equiv k X]
    exact rT_map' _ _ _ (cpt_fin k x) _
  · change (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α X) = 0
    rw [hα.basic X i hi, map_zero]
  · change (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α X) ∈ _
    have hm := hα.val X
    generalize α X = m at hm
    induction hm using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨φ, v, hφ, rfl⟩ := hy
      exact Submodule.subset_span ⟨_, v, lev_fin hx Ξ hφ, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul s y _ hy => rw [map_smul]; exact Submodule.smul_mem _ s hy
  · refine AlternatingMap.ext fun X => ?_
    change _ = (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (dCo (smLie Ξ) α X)
    simp only [dCo, AlternatingMap.alternatizeUncurryFin_apply, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
    exact (rT_lie Ξ x _ _).symm
  · obtain ⟨ho, w, hw, hz⟩ := h
    let f : GL (Fin a) (Af E) ⧸ U' → GL (Fin a) (Af E) ⧸ U := fun s =>
      Quotient.liftOn' s (fun y => ((y * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U)) fun y y' hy => by
        rw [QuotientGroup.leftRel_apply] at hy
        refine QuotientGroup.eq.2 ?_
        have := hx _ hy
        rwa [show (y * x)⁻¹ * (y' * x) = x⁻¹ * (y⁻¹ * y') * x by group]
    have hf : ∀ (g : GL (Fin a) (Af E)) s, f (g • s) = g • f s := fun g s => by
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
      change ((g * y * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) = ((g * (y * x) : GL (Fin a) (Af E)) : _ ⧸ U)
      rw [mul_assoc]
    have hc' : c' = fun z => c z ∘ f := by
      funext z s
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
      exact hc z y
    refine ⟨ho, pb ho U U' Ξ f q w, fun g y X => ?_, ?_⟩
    · change w.1 ((y * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) _ _ =
        Ξ.mat g *ᵥ ev ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α X)) _
      rw [ev_rT, mul_assoc, ← map_mul]
      exact hw g (y * x) X
    · rw [hc']
      refine zig_map (geo ho U Ξ) (geo ho U' Ξ) f (pb ho U U' Ξ f) (fun q γ w => ?_) (fun q w => rfl) (fun c => rfl) c q 0 _ hz
      refine Subtype.ext (funext fun s => funext fun p => ContinuousAlternatingMap.ext fun v => ?_)
      change _ *ᵥ w.1 ((geo ho U Ξ).σ γ⁻¹ (f s)) _ _ = _ *ᵥ w.1 (f ((geo ho U' Ξ).σ γ⁻¹ s)) _ _
      rw [geo_σ, geo_σ, hf]
      rfl
