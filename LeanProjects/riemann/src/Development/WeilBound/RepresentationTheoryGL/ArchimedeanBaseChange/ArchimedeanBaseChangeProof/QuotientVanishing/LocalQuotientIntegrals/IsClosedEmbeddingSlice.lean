import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.Glob2Aux

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV

theorem exists_haar_map {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (e : G ≃ₜ* H) (S : Subgroup G) (ν : Measure S) [ν.IsHaarMeasure] [ν.IsInvInvariant] (T : Subgroup H)
    (hT : S.map e.toMonoidHom = T) : ∃ ν' : Measure T, ν'.IsHaarMeasure ∧ ν'.IsInvInvariant := by
  subst hT
  have hinv : ∀ y : S.map e.toMonoidHom, e.symm y ∈ S := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
    rw [← hxy]
    change e.symm (e x) ∈ S
    rw [e.symm_apply_apply]
    exact hx
  let ψ : S ≃ₜ* S.map e.toMonoidHom :=
    { toFun := fun x => ⟨e x, Subgroup.mem_map.2 ⟨x, x.2, rfl⟩⟩
      invFun := fun y => ⟨e.symm y, hinv y⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y)
      map_mul' := fun x y => Subtype.ext (map_mul e (x : G) y)
      continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk hinv }
  refine ⟨ν.map ψ, ContinuousMulEquiv.isHaarMeasure_map ν ψ, ⟨?_⟩⟩
  have hψ : Measurable ψ := ψ.continuous.measurable
  have hi : Measurable (Inv.inv : S → S) := continuous_inv.measurable
  have hi' : Measurable (Inv.inv : S.map e.toMonoidHom → S.map e.toMonoidHom) := continuous_inv.measurable
  show Measure.map Inv.inv (ν.map ψ) = ν.map ψ
  rw [Measure.map_map hi' hψ]
  have : (Inv.inv ∘ ψ) = ψ ∘ Inv.inv := funext fun x => (map_inv ψ x).symm
  rw [this, ← Measure.map_map hψ hi, Measure.map_inv_eq_self]

theorem isClosedEmbedding_slice {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] (c : Y) :
    Topology.IsClosedEmbedding (fun x : X => (x, c)) := by
  refine ⟨isEmbedding_prodMkLeft c, ?_⟩
  have : Set.range (fun x : X => (x, c)) = Set.univ ×ˢ {c} := by
    ext p; constructor
    · rintro ⟨x, rfl⟩; exact ⟨trivial, rfl⟩
    · rintro ⟨-, hp⟩; exact ⟨p.1, Prod.ext rfl (Set.mem_singleton_iff.1 hp).symm⟩
  rw [this]; exact isClosed_univ.prod isClosed_singleton

end PositivityTheory.Rg.BcB.CV.Glob2Aux

namespace PositivityTheory.Rg.BcB.CV

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 Glob2Aux

theorem pf_Glob2 : PositivityTheory.Rg.BcB.D4.SplitAt2 → PositivityTheory.Rg.BcB.CV.LocTor → PositivityTheory.Rg.BcB.CV.QMap → PositivityTheory.Rg.BcB.CV.QProd → PositivityTheory.Rg.BcB.CV.TwoVanish → PositivityTheory.Rg.BcB.CV.Ploc → PositivityTheory.Rg.BcB.CV.FamAt → PositivityTheory.Rg.BcB.CV.AdTop → PositivityTheory.Rg.BcB.CV.Glob2 := by
  intro hS hLT hQM hQP hTV hPl hFA hAT
  intro E _ _ _ _ n m _ _ μ _ d ν _ _ Wof a V τ φ hm hP hV hVa hφ hVC
  obtain ⟨v₁, v₂, hv⟩ := exists_pair_ne (InfinitePlace E)
  obtain ⟨G', iG, iT, iTG, iLC, iSC, iM, iB, iMGL, iBGL, e, μ₁, μ₂, θ', hμ₁, hμ₂, -, he1, hev1, hev2, heθ, hcent⟩ :=
    hS E n v₁ v₂ hv μ
  have := hμ₁
  have := hμ₂
  obtain ⟨hLCA, hT2A, hSCA, hθc, hdegm, -⟩ := hAT E n
  have := hLCA
  have := hT2A
  have := hSCA
  have hmem : ∀ g, g ∈ adCent d ↔ e g ∈ ((twCent (thC n) (locGL v₁ d)).prod (twCent (thC n) (locGL v₂ d))).prod
      (twCent θ' (e (ratGL E n d)).2) := by
    intro g
    rw [← hcent d, Subgroup.mem_map]
    constructor
    · intro h; exact ⟨g, h, rfl⟩
    · rintro ⟨x, hx, hxg⟩
      change e x = e g at hxg
      have : x = g := by rw [← e.symm_apply_apply x, hxg, e.symm_apply_apply]
      rwa [← this]
  have hE1 : ∀ t ∈ twCent (thC n) (locGL v₁ d), embInf n v₁ t ∈ adCent d := fun t ht =>
    (hmem _).2 (by rw [hev1]; exact Subgroup.mem_prod.2 ⟨Subgroup.mem_prod.2 ⟨ht, one_mem _⟩, one_mem _⟩)
  have hE2 : ∀ t ∈ twCent (thC n) (locGL v₂ d), embInf n v₂ t ∈ adCent d := fun t ht =>
    (hmem _).2 (by rw [hev2]; exact Subgroup.mem_prod.2 ⟨Subgroup.mem_prod.2 ⟨one_mem _, ht⟩, one_mem _⟩)
  obtain ⟨hsep₁, hL₁⟩ := hFA E n m d Wof a V v₁ hP hVa hE1
  obtain ⟨hsep₂, hL₂⟩ := hFA E n m d Wof a V v₂ hP hVa hE2
  obtain ⟨hcl₁, hcomm₁, -, hLC, hSC⟩ := hLT n _ hsep₁
  obtain ⟨hcl₂, hcomm₂, -, -, -⟩ := hLT n _ hsep₂
  have := hLC
  have := hSC
  have : T2Space ((GL (Fin n) ℂ × GL (Fin n) ℂ) × G') := e.symm.toHomeomorph.isEmbedding.t2Space
  have : T2Space G' := (isEmbedding_prodMkRight ((1 : GL (Fin n) ℂ × GL (Fin n) ℂ))).t2Space

  have hclP : IsClosed (((twCent (thC n) (locGL v₁ d)).prod (twCent (thC n) (locGL v₂ d)) : Subgroup _) :
      Set (GL (Fin n) ℂ × GL (Fin n) ℂ)) := by
    rw [Subgroup.coe_prod]; exact hcl₁.prod hcl₂
  have hcommP : ∀ s ∈ (twCent (thC n) (locGL v₁ d)).prod (twCent (thC n) (locGL v₂ d)),
      ∀ t ∈ (twCent (thC n) (locGL v₁ d)).prod (twCent (thC n) (locGL v₂ d)), s * t = t * s := by
    intro s hs t ht
    rw [Subgroup.mem_prod] at hs ht
    exact Prod.ext (hcomm₁ _ hs.1 _ ht.1) (hcomm₂ _ hs.2 _ ht.2)
  have hcl3 : IsClosed (twCent θ' (e (ratGL E n d)).2 : Set G') := by
    have hA : IsClosed ((((twCent (thC n) (locGL v₁ d)).prod (twCent (thC n) (locGL v₂ d))).prod
        (twCent θ' (e (ratGL E n d)).2) : Subgroup _) : Set ((GL (Fin n) ℂ × GL (Fin n) ℂ) × G')) := by
      rw [← hcent d, Subgroup.coe_map]
      exact e.toHomeomorph.isClosedMap _ hP.closed
    have h2 := hA.preimage (f := fun g : G' => ((1 : GL (Fin n) ℂ × GL (Fin n) ℂ), g))
      (continuous_const.prodMk continuous_id)
    convert h2 using 1
    ext g
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_prod, one_mem, and_self, true_and]
  have hcomm3 : ∀ s ∈ twCent θ' (e (ratGL E n d)).2, ∀ t ∈ twCent θ' (e (ratGL E n d)).2, s * t = t * s := by
    intro s hs t ht
    have hs' : e.symm ((1, 1), s) ∈ adCent d := (hmem _).2 (by
      rw [e.apply_symm_apply]; exact Subgroup.mem_prod.2 ⟨Subgroup.mem_prod.2 ⟨one_mem _, one_mem _⟩, hs⟩)
    have ht' : e.symm ((1, 1), t) ∈ adCent d := (hmem _).2 (by
      rw [e.apply_symm_apply]; exact Subgroup.mem_prod.2 ⟨Subgroup.mem_prod.2 ⟨one_mem _, one_mem _⟩, ht⟩)
    have h := congrArg e (hP.comm _ hs' _ ht')
    rw [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply] at h
    exact congrArg Prod.snd h
  have : SigmaFinite μ₁ := inferInstance
  have : SigmaFinite μ₂ := inferInstance
  have : (μ₁.prod μ₁).IsHaarMeasure := inferInstance
  have : ((μ₁.prod μ₁).prod μ₂).IsHaarMeasure := inferInstance
  obtain ⟨ν', hν'1, hν'2⟩ := exists_haar_map e (adCent d) ν _ (hcent d)
  have := hν'1
  have := hν'2

  have hFm : Measurable fun x => φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x) := by
    have h1 : Continuous fun x : GA E n => twConj (thetaA E n) x (ratGL E n d) :=
      (continuous_inv.mul continuous_const).mul hθc
    refine (hφ.cont.comp h1).measurable.mul (hV.meas.comp (measurable_pi_lambda _ fun e' => ?_))
    have := hdegm (Wof e')
    rw [← BorelSpace.measurable_eq] at this
    exact measurable_const.sub this
  have hFi : ∀ t ∈ adCent d, ∀ x, φ (twConj (thetaA E n) (t * x) (ratGL E n d)) * V (yOf τ Wof (t * x)) =
      φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x) := by
    intro t ht x
    have ht' : t⁻¹ * ratGL E n d * thetaA E n t = ratGL E n d := ht
    have h1 : twConj (thetaA E n) (t * x) (ratGL E n d) = twConj (thetaA E n) x (ratGL E n d) := by
      calc (t * x)⁻¹ * ratGL E n d * thetaA E n (t * x)
          = x⁻¹ * (t⁻¹ * ratGL E n d * thetaA E n t) * thetaA E n x := by rw [map_mul]; group
        _ = x⁻¹ * ratGL E n d * thetaA E n x := by rw [ht']
    have h2 : yOf τ Wof (t * x) = fun e' => yOf τ Wof x e' - sdot e' (a t) := by
      funext e'
      simp only [yOf, hP.degT t ht x e']
      ring
    rw [h1, h2, hVa t ht]
  refine hQM (GA E n) ((GL (Fin n) ℂ × GL (Fin n) ℂ) × G') e μ ((μ₁.prod μ₁).prod μ₂) (adCent d) _ ν ν'
    (fun x => φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x)) hP.closed (hcent d) hFm hFi ?_
  refine hQP (GL (Fin n) ℂ × GL (Fin n) ℂ) G' (μ₁.prod μ₁) μ₂ _ _ ν' _ hclP hcl3 hcommP hcomm3
    (hFm.comp e.symm.continuous.measurable) ?_ (Or.inl ?_)
  · intro t ht x
    show _ * _ = _ * _
    rw [map_mul]
    exact hFi _ ((hmem _).2 (by rw [e.apply_symm_apply]; exact ht)) _
  intro ν₁ _ _ x'

  have hPl7 : ∀ v, GeneralLinearGroup.map (cV v) (ratGL E n d) = locGL v d := fun v =>
    (hPl E n v ⊥).2.2.2.2.2.2.1 d
  have hδ : e (ratGL E n d) = ((locGL v₁ d, locGL v₂ d), (e (ratGL E n d)).2) := by
    have h := he1 (ratGL E n d)
    rw [hPl7 v₁, hPl7 v₂] at h
    exact Prod.ext h rfl
  have hproj : ∀ y : (GL (Fin n) ℂ × GL (Fin n) ℂ) × G',
      GeneralLinearGroup.map (cV v₁) (e.symm y) = y.1.1 ∧ GeneralLinearGroup.map (cV v₂) (e.symm y) = y.1.2 := by
    intro y
    have h := he1 (e.symm y)
    rw [e.apply_symm_apply] at h
    exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩
  set g' := twConj θ' x' (e (ratGL E n d)).2 with hg'
  set g0 := e.symm (((1 : GL (Fin n) ℂ), (1 : GL (Fin n) ℂ)), x') with hg0
  set f : GL (Fin n) ℂ × GL (Fin n) ℂ → ℂ := fun g => φ (e.symm (g, g')) with hf
  set z : (Fin m → SignType) → ℝ := fun e' => yOf τ Wof g0 e' - pAt Wof v₁ 1 e' - pAt Wof v₂ 1 e' with hz
  have hsplit : ∀ x₁ x₂ : GL (Fin n) ℂ, e.symm ((x₁, x₂), x') = embInf n v₁ x₁ * (embInf n v₂ x₂ * g0) := by
    intro x₁ x₂
    rw [← e.symm_apply_apply (embInf n v₁ x₁ * (embInf n v₂ x₂ * g0))]
    congr 1
    rw [map_mul, map_mul, hev1, hev2, hg0, e.apply_symm_apply]
    simp
  have hφpart : ∀ x₁ x₂ : GL (Fin n) ℂ, twConj (thetaA E n) (e.symm ((x₁, x₂), x')) (ratGL E n d) =
      e.symm ((twConj (thC n) x₁ (locGL v₁ d), twConj (thC n) x₂ (locGL v₂ d)), g') := by
    intro x₁ x₂
    rw [← e.symm_apply_apply (twConj (thetaA E n) (e.symm ((x₁, x₂), x')) (ratGL E n d))]
    congr 1
    simp only [twConj, map_mul, map_inv, heθ, e.apply_symm_apply]
    rw [hδ, hg']
    rfl
  have hVpart : ∀ x₁ x₂ : GL (Fin n) ℂ, yOf τ Wof (e.symm ((x₁, x₂), x')) = pAt Wof v₁ x₁ + pAt Wof v₂ x₂ + z := by
    intro x₁ x₂
    funext e'
    have hh : e (embInf n v₂ x₂ * g0) = ((1, x₂), x') := by
      rw [map_mul, hev2, hg0, e.apply_symm_apply]; simp
    have hc1 : GeneralLinearGroup.map (cV v₁) (embInf n v₂ x₂ * g0) = 1 := by
      have h := (hproj (e (embInf n v₂ x₂ * g0))).1
      rw [e.symm_apply_apply, hh] at h
      exact h
    have hc0 : GeneralLinearGroup.map (cV v₂) g0 = 1 := (hproj _).2
    have h8a := (hPl E n v₁ (Wof e')).2.2.2.2.2.2.2 x₁ (embInf n v₂ x₂ * g0)
    have h8b := (hPl E n v₂ (Wof e')).2.2.2.2.2.2.2 x₂ g0
    rw [hc1, mul_one] at h8a
    rw [hc0, mul_one] at h8b
    rw [hsplit]
    simp only [yOf, pAt, Pi.add_apply, hz]
    linarith
  have hkey : (fun x₁ : GL (Fin n) ℂ × GL (Fin n) ℂ =>
      φ (twConj (thetaA E n) (e.symm (x₁, x')) (ratGL E n d)) * V (yOf τ Wof (e.symm (x₁, x')))) =
      fun x => f (twConj (thC n) x.1 (locGL v₁ d), twConj (thC n) x.2 (locGL v₂ d)) *
        V (pAt Wof v₁ x.1 + pAt Wof v₂ x.2 + z) := by
    funext x
    obtain ⟨x₁, x₂⟩ := x
    rw [hφpart, hVpart]
  have hz0 : z 0 = 0 := by
    have hr : Module.finrank E (Wof 0) = 0 := by rw [hP.zero]; exact finrank_bot E _
    have h1 := (hPl E n v₁ (Wof 0)).2.2.2.1 hP.zero
    have h2 := (hPl E n v₂ (Wof 0)).2.2.2.1 hP.zero
    simp only [hz, yOf, pAt, prof, hr, h1.1, h2.1, h1.2 g0]
    simp
  have hfc : Continuous f := hφ.cont.comp (e.symm.continuous.comp (continuous_id.prodMk continuous_const))
  have hfs : HasCompactSupport f :=
    hφ.supp.comp_isClosedEmbedding (e.symm.toHomeomorph.isClosedEmbedding.comp (isClosedEmbedding_slice g'))
  have hvc1 : ∀ g, VeryCusp fun x => f (x, g) := by
    intro g
    have h := hVC v₁ (e.symm ((1, g), g')) (hproj _).1
    have heq : (fun x => f (x, g)) = fun x => φ (embInf n v₁ x * e.symm ((1, g), g')) := by
      funext x
      simp only [hf]
      congr 1
      rw [← e.symm_apply_apply (embInf n v₁ x * e.symm ((1, g), g')), map_mul, hev1, e.apply_symm_apply]
      simp
    rw [heq]; exact h
  have hvc2 : ∀ g, VeryCusp fun x => f (g, x) := by
    intro g
    have h := hVC v₂ (e.symm ((g, 1), g')) (hproj _).2
    have heq : (fun x => f (g, x)) = fun x => φ (embInf n v₂ x * e.symm ((g, 1), g')) := by
      funext x
      simp only [hf]
      congr 1
      rw [← e.symm_apply_apply (embInf n v₂ x * e.symm ((g, 1), g')), map_mul, hev2, e.apply_symm_apply]
      simp
    rw [heq]; exact h
  exact (congrArg (quotIntegral (μ₁.prod μ₁) _ ν₁) hkey).trans
    (hTV n m μ₁ (locGL v₁ d) (locGL v₂ d) ν₁ f V (pAt Wof v₁) (pAt Wof v₂) z hm hsep₁ hsep₂ hfc hfs hvc1 hvc2 hV
      hL₁ hL₂ hz0)

end PositivityTheory.Rg.BcB.CV
