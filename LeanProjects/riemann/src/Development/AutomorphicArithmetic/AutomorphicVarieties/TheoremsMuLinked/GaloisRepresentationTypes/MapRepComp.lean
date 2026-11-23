import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Number
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ConjTrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.CharpolyMapRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.MapRepComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AmbZero

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th

private theorem mapRep_comp {H R R' R'' : Type} [Group H] [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'')
    (r : H →* M4 R) : mapRep (g.comp f) r = mapRep g (mapRep f r) := rfl

private theorem conj_comp {H H' K : Type} [Group H] [Group H'] [CommRing K] {r r' : H →* M4 K} (h : IsConj4 r r') (φ : H' →* H) :
    IsConj4 (r.comp φ) (r'.comp φ) := h.imp fun _ hv g => hv (φ g)

private theorem irr_sub {Γ V K k : Type} [Group Γ] [CommRing V] [Field K] [IsAlgClosed K] [CharZero K] [Field k]
    (f : V →+* K) (hf : Function.Injective f) (red : V →+* k) (r : Γ →* M4 V) (χ : Fin 4 → Γ →* kˣ)
    (htr : ∀ g, red (r g).trace = ∑ i, (χ i g : k)) (H : Subgroup Γ) [H.Normal] (hab : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H)
    (hd : ∀ i j, i ≠ j → ∃ g ∈ H, χ i g ≠ χ j g) (hi : Irr (mapRep f r)) : Irr ((mapRep f r).comp H.subtype) := by
  by_contra hred
  have hirr := ((irrIff K).1 _).1 hi
  obtain ⟨φ, hφ1, hH, -, M, hM⟩ := UpperTheory.V.U3.exists_selfTwist (mapRep f r).toHomUnits H hab
    (fun W hW => hirr.2.2 W le_top fun g => hW g trivial)
    (fun h => hred (((irrIff K).1 _).2 ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => h W fun g hg => hW ⟨g, hg⟩⟩))
  have hM' : ∀ g, (M : M4 K) * ((φ g : K) • mapRep f r g) = mapRep f r g * M := fun g => hM g trivial
  obtain ⟨g0, hg0⟩ := DFunLike.ne_iff.1 hφ1
  have h0 : ∀ h : H, ∑ i, (χ i g0 : k) * χ i h = 0 := by
    intro h
    have h1 : (φ (g0 * h) : K) • mapRep f r (g0 * h) = (M⁻¹ : (M4 K)ˣ) * mapRep f r (g0 * h) * M := by
      rw [mul_assoc, ← hM', Units.inv_mul_cancel_left]
    have h2 := congrArg Matrix.trace h1
    rw [Matrix.trace_units_conj', Matrix.trace_smul, map_mul φ, (MonoidHom.mem_ker.1 (hH h.2)), mul_one, smul_eq_mul] at h2
    have h3 : (mapRep f r (g0 * h)).trace = 0 := by
      by_contra h4
      exact hg0 (Units.ext (mul_right_cancel₀ h4 (h2.trans (one_mul _).symm)))
    have h5 : (r (g0 * h)).trace = 0 := hf (by rw [map_zero, ← h3]; simp only [Matrix.trace, Matrix.diag, map_sum f, mapRep_apply])
    have h6 := htr (g0 * h)
    rw [h5, map_zero] at h6
    simpa using h6.symm
  have hli := (linearIndependent_monoidHom H k).comp (fun i => (Units.coeHom k).comp ((χ i).comp H.subtype)) (by
    intro i j hij
    by_contra hne
    obtain ⟨g, hg, hx⟩ := hd i j hne
    have := DFunLike.congr_fun hij (⟨g, hg⟩ : H)
    exact hx (Units.ext this))
  have := Fintype.linearIndependent_iff.1 hli (fun i => (χ i g0 : k)) (by
    ext h
    simpa using h0 h) 0
  exact (χ 0 g0).ne_zero this

private theorem irr_conj {H K : Type} [Group H] [Field K] {r r' : H →* M4 K} (h : IsConj4 r r') (hi : Irr r) : Irr r' := by
  obtain ⟨u, hu⟩ := h
  rw [Irr, eq_top_iff]
  intro X _
  have key : ∀ Y ∈ Submodule.span K (Set.range r), (u : M4 K) * Y * (u⁻¹ : (M4 K)ˣ) ∈ Submodule.span K (Set.range r') := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact Submodule.subset_span ⟨g, hu g⟩
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, add_mul]; exact add_mem hx hy
    | smul a x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ a hx
  have := key ((u⁻¹ : (M4 K)ˣ) * X * u) (hi ▸ Submodule.mem_top)
  simpa [mul_assoc] using this

private theorem irr_map {H K K' : Type} [Group H] [Field K] [Field K'] (e : K ≃+* K') {r : H →* M4 K} (hi : Irr r) :
    Irr (mapRep (e : K →+* K') r) := by
  rw [Irr, eq_top_iff]
  intro X _
  have key : ∀ Y ∈ Submodule.span K (Set.range r), Y.map e ∈ Submodule.span K' (Set.range (mapRep (e : K →+* K') r)) := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact Submodule.subset_span ⟨g, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.map_add _ (map_add e)]; exact add_mem hx hy
    | smul a x _ hx =>
      have : (a • x).map e = e a • x.map e := by ext i j; simp
      rw [this]; exact Submodule.smul_mem _ _ hx
  have := key (X.map e.symm) (hi ▸ Submodule.mem_top)
  have e2 : (X.map e.symm).map e = X := by ext i j; simp
  rwa [e2] at this

private theorem conj_map {H K K' : Type} [Group H] [Field K] [Field K'] (e : K →+* K') {r r' : H →* M4 K} (h : IsConj4 r r') :
    IsConj4 (mapRep e r) (mapRep e r') := by
  obtain ⟨u, hu⟩ := h
  refine ⟨Units.map (e.mapMatrix : M4 K →+* M4 K').toMonoidHom u, fun g => ?_⟩
  show e.mapMatrix (r' g) = e.mapMatrix (u : M4 K) * e.mapMatrix (r g) * e.mapMatrix ((u⁻¹ : (M4 K)ˣ) : M4 K)
  rw [hu, map_mul, map_mul]

private theorem gsp_map' {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {ν : R} {X : M4 R} (h : IsGSp ν X) :
    IsGSp (f ν) (X.map f) := by
  have e : adj (X.map f) = (adj X).map f := by ext i j; simp [adj_apply]
  rw [IsGSp, e, ← Matrix.map_mul, h]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

private theorem conj_trans {H R : Type} [Group H] [CommRing R] {r r' r'' : H →* M4 R} (h : IsConj4 r r') (h' : IsConj4 r' r'') :
    IsConj4 r r'' := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv⟩ := h'
  exact ⟨v * u, fun g => by rw [hv, hu, mul_inv_rev, Units.val_mul, Units.val_mul]; simp only [mul_assoc]⟩

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem comm_ab (E : Type) [Field E] [Algebra ℚ E] [Algebra E Ω] [IsScalarTower ℚ E Ω] [IsAbelianGalois ℚ E]
    (a b : G ℚ Ω) (x : E) : (a * b * a⁻¹ * b⁻¹) (algebraMap E Ω x) = algebraMap E Ω x := by
  have h : AlgEquiv.restrictNormalHom E (a * b * a⁻¹ * b⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [IsMulCommutative.is_comm.comm (AlgEquiv.restrictNormalHom E a)]
    group
  rw [← AlgEquiv.restrictNormal_commutes]
  exact congrArg (algebraMap E Ω) (DFunLike.congr_fun h x)

private theorem comm_L {D : Raw Ω c} (T : Tower D) (a b : G ℚ Ω) : a * b * a⁻¹ * b⁻¹ ∈ T.L.fixingSubgroup := by
  haveI : IsGalois ℚ Ω := {}
  rw [T.hL, IntermediateField.fixingSubgroup_sup]
  refine ⟨?_, ?_⟩
  · exact fun x => comm_ab T.F a b x
  · have h2 : T.K.fixingSubgroup.index = 2 := (IntermediateField.finrank_eq_fixingSubgroup_index Ω T.K).symm.trans T.degK
    show _ ∈ T.K.fixingSubgroup
    simp only [Subgroup.mul_mem_iff_of_index_two h2, inv_mem_iff]
    tauto

private theorem rt_wt {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ) (h : Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g)
    (i j : Fin 4) : Φ.rt (wt i j) g * Φ.χ j g = Φ.χ i g := by
  have h3 : Φ.χ 3 g = (Φ.χ 0 g)⁻¹ * (Φ.χ 1 g * Φ.χ 2 g) := by rw [← h, inv_mul_cancel_left]
  show (Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ (wt i j).1 * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ (wt i j).2 * Φ.χ j g = Φ.χ i g
  apply Additive.ofMul.injective
  have h4 := congrArg Additive.ofMul h3
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at h4 ⊢
  fin_cases i <;> fin_cases j <;> simp [wt, lamW, muW, h4] <;> abel

private theorem dist_L {D : Raw Ω c} (T : Tower D) (hT : T.Ok) (i j : Fin 4) (hij : i ≠ j) :
    ∃ g ∈ T.L.fixingSubgroup, Raw.bar (D.ps i) g ≠ Raw.bar (D.ps j) g := by
  have key : ∀ i j, i ≠ j → ∃ g ∈ T.L.fixingSubgroup, Raw.bar (chi D T.pr i) g ≠ Raw.bar (chi D T.pr j) g := by
    intro i j hij
    obtain ⟨g, hg, hne⟩ := hT.g3 (wt i j) (by revert i j; decide)
    refine ⟨resQ T.F g, ?_, fun h => hne ?_⟩
    · rw [T.hL, IntermediateField.fixingSubgroup_sup]
      exact ⟨fun x => g.commutes x, hg⟩
    · have h1 := rt_wt (T.fr ∅) g (by
        show chi D T.pr 0 _ * chi D T.pr 3 _ = chi D T.pr 1 _ * chi D T.pr 2 _
        cases T.pr <;> simp [chi, lab, Raw.ps, Raw.th, mul_comm]) i j
      have h2 := congrArg (fun x : c.Oˣ => residue c.O (x : c.O)) h1
      simp only [Units.val_mul, map_mul] at h2
      have h3 : Raw.bar (chi D T.pr j) (resQ T.F g) ≠ 0 := ((chi D T.pr j _).isUnit.map (residue c.O)).ne_zero
      exact mul_right_cancel₀ h3 ((h2.trans h).trans (one_mul _).symm)
  have hl : ∀ i, lab T.pr (lab T.pr i) = i := by cases T.pr <;> decide
  have := key (lab T.pr i) (lab T.pr j) fun h => hij (by rw [← hl i, h, hl])
  simpa only [chi, hl] using this

private theorem ps_wt_any {D : Raw Ω c} (h : D.Good) {A : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1) (i : Fin 4)
    {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) (h1 : s ∈ D.ψ.ker) (h2 : s ∈ D.om.ker) :
    D.ps i s = chiO ℚ Ω l c.O s ^ D.wts4 i := by
  have hl : l.Prime := Fact.out
  obtain ⟨u, -, hu⟩ := (UpperTheory.V.Chr.placesQ Ω).2.2 l A _ hl hA (h.pl_over l hl)
  have e : ∀ γ : G ℚ Ω →* c.Oˣ, γ (u⁻¹ * s * u) = γ s := fun γ => by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  have h3 := (facts D h).2.2.2.1 i (u⁻¹ * s * u) ⟨⟨hu s hs, (e _).trans h1⟩, (e _).trans h2⟩
  rwa [e, e] at h3

private theorem map_psi {ι Γ R R' : Type} [Group Γ] [CommRing R] [CommRing R'] (P : PD ι Γ R) (f : R →+* R') (v : ι) (i : Fin 4)
    (s : Γ) : (P.map f).ψ v i s = f (P.ψ v i s) := by
  simp [PD.ψ, PD.map, Matrix.mul_apply, adj_apply, map_sum]

private theorem irr_L {D : Raw Ω c} (T : Tower D) (hT : T.Ok) (𝔞 : Amb l) (f : 𝔞.V →+* PadicAlgCl l) (hf : Function.Injective f)
    (r : G ℚ Ω →* M4 𝔞.V) (hr : ∀ g i j, r g i j - 𝔞.a c (D.r0 g i j) ∈ maximalIdeal 𝔞.V) (hi : Irr (mapRep f r)) :
    Irr ((mapRep f r).comp T.L.fixingSubgroup.subtype) := by
  haveI : T.L.fixingSubgroup.Normal := ⟨fun n hn g => by
    have := mul_mem (comm_L T g n) hn
    rwa [inv_mul_cancel_right] at this⟩
  refine irr_sub f hf (residue 𝔞.V) r
    (fun i => (Units.map (𝔞.red c).toMonoidHom).comp (D.ps i)) (fun g => ?_) _ (comm_L T) (fun i j hij => ?_) hi
  · rw [Matrix.trace, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : residue 𝔞.V (r g i i) = residue 𝔞.V (𝔞.a c (D.r0 g i i)) := Ideal.Quotient.eq.2 (hr g i i)
    have h2 : D.r0 g i i = D.ps i g := Matrix.diagonal_apply_eq _ i
    rw [h2] at h1
    exact h1
  · obtain ⟨g, hg, hne⟩ := dist_L T hT i j hij
    refine ⟨g, hg, fun h => hne ((𝔞.j c).injective ?_)⟩
    have h1 : 𝔞.red c (D.ps i g) = 𝔞.red c (D.ps j g) := congrArg Units.val h
    exact h1

private theorem point (hC : CohomologyHyp) {D : Raw Ω c} (T : Tower D) (hF : T.Fit) (𝔞 : Amb l)
    {P : PD T.ι (G T.F Ω) 𝔞.V} (hs : 𝔞.Small P) (hp : (T.fr ∅).IsPair (𝔞.a c) P)
    (hr : (T.fr ∅).IsRes (𝔞.red c) (P.map (residue 𝔞.V))) (c₁ : Coef l) :
    ∃ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (y : X.A →+* 𝔞.V), c₁.O ≤ c'.O ∧
      y.comp (algebraMap c'.O X.A) = 𝔞.a c' ∧ X.P.map y = P := by
  obtain ⟨c₃, k₃⟩ := smallCo 𝔞 P hs
  obtain ⟨d₁, a₁, a₂⟩ := (coefSup l).1 c₁ c
  obtain ⟨c', b₁, b₂⟩ := (coefSup l).1 d₁ c₃
  have h : c.O ≤ c'.O := a₂.trans b₁
  haveI : Finite (ResidueField c'.O) := by
    haveI : IsLocalHom (algebraMap ℤ_[l] c'.O) := (dvrFacts l c'.O).2.2.1
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  have hS := (std hC D T hF ∅ c' h).1 (Finset.notMem_empty 0)
  obtain ⟨X⟩ := spaceEx (T.fr ∅) l (inc h) hS
  obtain ⟨R, _, _, _, f, QR, fi, fa, fr, qc, rfl⟩ := k₃ c' b₂
  have jc : (𝔞.j c').comp ((residue c'.O).comp (inc h)) = 𝔞.red c :=
    RingHom.ext fun x => congrArg (residue 𝔞.V) (𝔞.compat c c' h x)
  have rs : (T.fr ∅).IsRes ((residue c'.O).comp (inc h)) (QR.map (res c'.O R : R →+* ResidueField c'.O)) := by
    refine (chainMap (T.fr ∅) ((residue c'.O).comp (inc h)) (𝔞.j c') _).1.1 ?_
    have e1 : (QR.map (res c'.O R : R →+* ResidueField c'.O)).map (𝔞.j c') = (QR.map f).map (residue 𝔞.V) := by
      rw [PD.map_map, PD.map_map, fr]
    rw [jc]
    exact e1 ▸ hr
  have lR : (T.fr ∅).Lifts (inc h) (QR.map (res c'.O R : R →+* ResidueField c'.O)) QR := by
    refine ⟨Asm.pair_of f fi ?_, qc, rfl⟩
    rw [← RingHom.comp_assoc, fa]
    have : (𝔞.a c').comp (inc h) = 𝔞.a c := RingHom.ext fun x => 𝔞.compat c c' h x
    rw [this]
    exact hp
  obtain ⟨f₀, hf₀⟩ := X.univ R _ _ rs lR
  refine ⟨c', h, X, f.comp (f₀ : X.A →+* R), a₁.trans b₁, ?_, ?_⟩
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, fa]
  · exact congrArg (fun Z => PD.map Z f) hf₀

theorem UpperTheory.V.Th.spPt :
    CohomologyHyp → SpPt := by
  intro hC Ω _ _ _ l _ c D hD r₀ hE hI
  have hG : D.Good := hD.elim (·.1) (·.1)
  obtain ⟨⟨𝔞, e, he⟩, -⟩ := ambZero l
  obtain ⟨r, hr', rfl⟩ := eptV D hG 𝔞 e he r₀ hE
  obtain ⟨u, hK⟩ := ptPair hC D hG 𝔞 r hr'
  have hirr : Irr (mapRep 𝔞.toK r) := by
    have h1 := irr_map e.symm hI
    have h2 : mapRep (e.symm : PadicAlgCl l →+* 𝔞.K) (mapRep ((e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK) r) = mapRep 𝔞.toK r := by
      ext g i j
      exact e.symm_apply_apply _
    rwa [h2] at h1
  obtain ⟨pr, hl, hP⟩ := labels D hG 𝔞 r u hK
  obtain ⟨T₀, rfl, hF₀, tame⟩ : ∃ T₀ : Tower D, T₀.pr = pr ∧ T₀.Fit ∧ TameL l T₀.F := by
    rcases hD with hD | hD
    · obtain ⟨T₀, e, ok, two, tame⟩ := exists_tame_tower_ok_two D hD pr hl
      exact ⟨T₀, e, ⟨ok, .inl ⟨hD, two⟩⟩, tame⟩
    · obtain ⟨T₀, e, ok, three, tame⟩ := exists_tame_tower_ok_three D hD pr hl
      first
        | exact ⟨T₀, e, ⟨ok, .inr ⟨hD, three⟩⟩, tame⟩
        | exact ⟨T₀, e, ⟨ok, .inr ⟨hD, three.five, three.sb, three.psi⟩⟩, tame⟩
  obtain ⟨P, qP, nP, cP, sP⟩ := hP _ hF₀.1.dist
  obtain ⟨P', qP', cP', lP'⟩ := lat hC D hG 𝔞 _ _ hl hF₀.1.dist P qP nP (sP (Or.inl hirr))
  obtain ⟨T, m, le, -, deep, -⟩ := layerEx D hG T₀ hF₀ tame 0
  have hfit := (leFit D hG T₀ T le).2.2.2.2.1 hF₀
  obtain ⟨P'', sm, pr'', er, -, rs, ine⟩ := restrQ D hG T₀ T hF₀ le 𝔞 P' qP' lP'
  refine ⟨T, hfit, deep, fun c₁ => ?_⟩
  obtain ⟨c', h, X, y, hc₁, hy, k5⟩ := point hC T hfit 𝔞 sm pr'' rs c₁
  have hconj := conj_trans cP cP'
  have hmult := qP'.pair.mult
  have hres : P'.r.comp (resQ T.F) = (X.P.map y).r := by rw [k5, er]
  have hin : ∀ v i, ∀ s ∈ Ine (F := T.F) (T.pl v), y (X.P.ψ v i s) = 𝔞.a c (D.ps i (resQ T.F s)) := fun v i s hs => by
    subst k5
    exact (map_psi X.P y v i s).symm.trans (ine v i s hs)
  let f : 𝔞.V →+* PadicAlgCl l := (e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK
  let y' : X.A →ₐ[c'.O] PadicAlgCl l :=
    { f.comp y with
      commutes' := fun x => by
        have h1 : y (algebraMap c'.O X.A x) = 𝔞.a c' x := DFunLike.congr_fun hy x
        exact (congrArg f h1).trans (he.1 c' x) }
  have hw : T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y' : X.A →+* PadicAlgCl l)) := by
    have hc : Continuous (resQ T.F) := UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.F Ω
    refine ⟨(D.ψ.ker ⊓ D.om.ker).comap (resQ T.F),
      (hG.psi_open.inter (facts D hG).2.2.2.2.2.2.2.2.2.2.2.2.1).preimage hc, fun v i s hs => ?_⟩
    have h1 : resQ T.F s ∈ Ine (F := ℚ) (T.pl v) := hs.2
    have h2 := ps_wt_any hG (T.ovl v) i h1 hs.1.1 hs.1.2
    have h3 : f (y (X.P.ψ v i s)) = ((D.ps i (resQ T.F s) : c.O) : PadicAlgCl l) :=
      (congrArg f (hin v i s hs.2)).trans (he.1 c _)
    have h4 : (GlobalTheory.GalOfCusp.cycBar T.F Ω l s : PadicAlgCl l) =
      ((chiO ℚ Ω l c.O (resQ T.F s) : c.O) : PadicAlgCl l) := rfl
    refine (congrArg (· ^ 2) ((map_psi X.P _ v i s).trans h3)).trans ?_
    rw [h2]
    have h5 : (2 * (D.wts4 i : ℤ)) = ((D.wts4 i * 2 : ℕ) : ℤ) := by push_cast; ring
    simp only [h5, zpow_natCast, Units.val_pow_eq_pow_val, h4, SubmonoidClass.coe_pow, pow_mul]
  have hc1 : IsConj4 (mapRep f r) (mapRep f P'.r) := by
    rw [mapRep_comp, mapRep_comp]
    exact conj_map _ hconj
  have hiL := irr_L T hfit.1 𝔞 f (e.injective.comp Subtype.val_injective) r hK.red hI
  have hm : D.Mult (mapRep f P'.r) := fun g => by
    have h1 := gsp_map' f (hmult g)
    rw [show f (𝔞.a c ((frQ D T₀.pr (resQ T₀.F T₀.g0)).ν g)) = algebraMap c.O (PadicAlgCl l) (D.th g) from he.1 c _] at h1
    exact h1
  have hr : (mapRep f P'.r).comp (resQ T.F) = (X.P.map (y' : X.A →+* PadicAlgCl l)).r := by
    ext g i j
    exact congrArg f (congrFun (congrFun (DFunLike.congr_fun hres g) i) j)
  exact ⟨c', h, X, y', mapRep f P'.r, hc₁, hc1, hm, hr, hw, irr_conj (conj_comp hc1 _) hiL⟩
