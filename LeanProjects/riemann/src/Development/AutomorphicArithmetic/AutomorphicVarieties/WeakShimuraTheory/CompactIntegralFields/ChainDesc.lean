import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section Inj

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

private theorem adj_mp (f : R →+* R') (X : M4 R) : (adj X).map f = adj (X.map f) := by
  ext i j; simp [adj_apply]

private theorem conj_mp (f : R →+* R') (n m : M4 R) (i j : Fin 4) :
    (adj (n.map f) * m.map f * n.map f) i j = f ((adj n * m * n) i j) := by
  rw [← adj_mp, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]

private theorem gsp_of (f : R →+* R') (hf : Function.Injective f) (ν : R) (X : M4 R) (h : IsGSp (f ν) (X.map f)) :
    IsGSp ν X := by
  unfold IsGSp at h ⊢
  rw [← adj_mp, ← Matrix.map_mul] at h
  ext i j
  apply hf
  have hij := congrFun (congrFun h i) j
  rw [Matrix.map_apply] at hij
  rw [hij, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem supp_of (f : R →+* R') (hf : Function.Injective f) (S : Finset (ℤ × ℤ)) (X : M4 R)
    (h : SuppM S (X.map f)) : SuppM S X := by
  intro i j hij hw
  apply hf
  rw [map_zero]
  exact h i j hij hw

private theorem cont_iff {Γ : Type} [TopologicalSpace Γ] (z : Γ → R) : AdicCont ⊥ z ↔ IsLocallyConstant z := by
  constructor
  · intro h
    refine IsLocallyConstant.desc z (Ideal.Quotient.mk ((⊥ : Ideal R) ^ 1)) (h 1) ?_
    intro x y hxy
    rw [Ideal.Quotient.eq, pow_one, Ideal.mem_bot, sub_eq_zero] at hxy
    exact hxy
  · intro h N
    exact h.comp _

variable {ι Γ : Type} [Group Γ]

private theorem ent_of (f : R →+* R') (r : Γ →* M4 R) (w : ℤ × ℤ) (h : Ent (mapRep f r) w) : Ent r w := by
  obtain ⟨g, i, j, h1, h2⟩ := h
  exact ⟨g, i, j, h1, fun h0 => h2 (by rw [mapRep_apply, h0, map_zero])⟩

private theorem map_map' (P : PD ι Γ R) (f : R →+* R') (g : R' →+* R'') : (P.map f).map g = P.map (g.comp f) := rfl

private theorem map_inj' (f : R →+* R') (hf : Function.Injective f) {P Q : PD ι Γ R} (h : P.map f = Q.map f) : P = Q := by
  have hr := congrArg PD.r h
  have hn := congrArg PD.n h
  apply PD.ext
  · ext g i j
    apply hf
    have := congrArg (fun r => r g i j) hr
    simpa [PD.map, mapRep_apply] using this
  · funext v
    ext i j
    apply hf
    have := congrArg (fun n => n v i j) hn
    simpa [PD.map] using this

private theorem psi_mp (f : R →+* R') (P : PD ι Γ R) (v : ι) (i : Fin 4) (s : Γ) : (P.map f).ψ v i s = f (P.ψ v i s) :=
  conj_mp f (P.n v) (P.r s) i i

private theorem desc_ex (f : R →+* R') (hf : Function.Injective f) (P : PD ι Γ R')
    (h1 : ∀ g i j, P.r g i j ∈ f.range) (h2 : ∀ v i j, P.n v i j ∈ f.range) : ∃ Q : PD ι Γ R, Q.map f = P := by
  have h1' : ∀ g i j, ∃ x, f x = P.r g i j := fun g i j => RingHom.mem_range.1 (h1 g i j)
  have h2' : ∀ v i j, ∃ x, f x = P.n v i j := fun v i j => RingHom.mem_range.1 (h2 v i j)
  choose r hr using h1'
  choose n hn using h2'
  let q : Γ →* M4 R :=
    { toFun := fun g => Matrix.of (r g)
      map_one' := by
        ext i j
        apply hf
        rw [Matrix.of_apply, hr, map_one, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      map_mul' := by
        intro x y
        ext i j
        apply hf
        rw [Matrix.of_apply, hr, map_mul, Matrix.mul_apply, Matrix.mul_apply, map_sum]
        simp only [map_mul, Matrix.of_apply, hr] }
  refine ⟨⟨q, fun v => Matrix.of (n v)⟩, ?_⟩
  apply PD.ext
  · ext g i j
    exact hr g i j
  · funext v
    ext i j
    exact hn v i j

variable {O : Type} [CommRing O] (Φ : Fr O Γ) (a : O →+* R)

private theorem inV_of (f : R →+* R') (hf : Function.Injective f) (P : PD Φ.ι Γ R) (h : Fr.InV (P.map f)) : Fr.InV P := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun g => supp_of f hf _ (P.r g) (h1 g), fun v => ⟨supp_of f hf _ _ (h2 v).1, fun h0 => (h2 v).2 ?_⟩⟩
  show f (P.n v 2 0) = 0
  rw [h0, map_zero]

private theorem good_of (f : R →+* R') (hf : Function.Injective f) (P : PD Φ.ι Γ R) (h : Φ.Good (f.comp a) (P.map f)) :
    Φ.Good a P := by
  have e := fun w => ent_of f P.r w
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨e _ h1, h2.imp (e _) (e _)⟩
  · exact Or.inr (Or.inl ⟨e _ h1, e _ h2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨inV_of Φ f hf P h1, e _ h2⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨inV_of Φ f hf P h1, e _ h2, e _ h3, fun v => ?_⟩))
    obtain ⟨s, hs, hne⟩ := h4 v
    exact ⟨s, hs, fun h0 => hne (by rw [RingHom.comp_apply, h0, map_one])⟩

private theorem isRes_of [TopologicalSpace Γ] (f : R →+* R') (hf : Function.Injective f) (P : PD Φ.ι Γ R)
    (h : Φ.IsRes (f.comp a) (P.map f)) : Φ.IsRes a P := by
  obtain ⟨⟨m1, m2, m3, m4, m5, m6⟩, ⟨r1, r2, r3⟩, c⟩ := h
  refine ⟨⟨fun g => gsp_of f hf _ _ (m1 g), fun g hg => ?_, fun i j hij => hf ?_, fun v => ?_,
    fun v s hs i j hij => hf ?_, fun v s hs i => hf ?_⟩, ⟨fun g i => hf ?_, fun v s hs i => hf ?_, ?_⟩, ?_⟩
  · ext i j
    apply hf
    have := congrFun (congrFun (m2 g hg) i) j
    change f (P.r g i j) = _ at this
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · rw [map_zero]
    exact m3 hij
  · obtain ⟨l1, l2, l3⟩ := m4 v
    refine ⟨gsp_of f hf 1 _ (by rw [map_one]; exact l1), fun i => hf (by rw [map_one]; exact l2 i),
      fun i j hij => hf (by rw [map_zero]; exact l3 i j hij)⟩
  · rw [map_zero, ← conj_mp]
    exact m5 v s hs i j hij
  · rw [map_one, ← psi_mp]
    exact m6 v s hs i
  · exact r1 g i
  · rw [← psi_mp]
    exact r2 v s hs i
  · exact r3.imp (fun ha => ⟨fun g => supp_of f hf _ _ (ha.1 g), fun v => supp_of f hf _ _ (ha.2 v)⟩)
      (fun ha g => supp_of f hf _ _ (ha g))
  · intro i j
    exact (cont_iff _).2 (IsLocallyConstant.desc _ f (by exact (cont_iff _).1 (c i j)) hf)

end Inj

section Ev

variable {l : ℕ} [Fact l.Prime]

private def Ev (p : Coef l → Prop) : Prop := ∃ c₁ : Coef l, ∀ c' : Coef l, c₁.O ≤ c'.O → p c'

private theorem ev_and {p q : Coef l → Prop} (hp : Ev p) (hq : Ev q) : Ev fun c => p c ∧ q c := by
  obtain ⟨c₁, h₁⟩ := hp
  obtain ⟨c₂, h₂⟩ := hq
  obtain ⟨c₃, k₁, k₂⟩ := (coefSup l).1 c₁ c₂
  exact ⟨c₃, fun c' h => ⟨h₁ c' (k₁.trans h), h₂ c' (k₂.trans h)⟩⟩

private theorem ev_mono {p q : Coef l → Prop} (hp : Ev p) (h : ∀ c, p c → q c) : Ev q := by
  obtain ⟨c₁, h₁⟩ := hp
  exact ⟨c₁, fun c' h' => h _ (h₁ c' h')⟩

private theorem ev_fin (c : Coef l) {α : Type} {p : α → Coef l → Prop} (hp : ∀ x, Ev (p x)) (S : Set α) (hS : S.Finite) :
    Ev fun c => ∀ x ∈ S, p x c := by
  refine Set.Finite.induction_on (motive := fun S _ => Ev fun c => ∀ x ∈ S, p x c) S hS ?_ ?_
  · exact ⟨c, fun c' _ x hx => by simp at hx⟩
  · intro x s _ _ ih
    refine ev_mono (ev_and (hp x) ih) ?_
    intro c' hc y hy
    rcases hy with rfl | hy
    · exact hc.1
    · exact hc.2 y hy

private theorem ev_pd (c : Coef l) {R : Coef l → Type} [∀ c, CommRing (R c)] {R' : Type} [CommRing R'] (f : ∀ c, R c →+* R')
    (hf : ∀ c, Function.Injective (f c)) (hs : ∀ x, Ev fun c => x ∈ (f c).range) {ι Γ : Type} [Finite ι] [Group Γ]
    [TopologicalSpace Γ] [CompactSpace Γ] (P : PD ι Γ R') (hP : P.Cont ⊥) : Ev fun c => ∃ Q : PD ι Γ (R c), Q.map (f c) = P := by
  classical
  have hfin : ∀ i j, (Set.range fun g => P.r g i j).Finite :=
    fun i j => ((cont_iff _).1 (hP i j)).range_finite
  let S : Set R' := (⋃ i, ⋃ j, Set.range fun g => P.r g i j) ∪
    Set.range (fun x : ι × Fin 4 × Fin 4 => P.n x.1 x.2.1 x.2.2)
  have hS : S.Finite := (Set.finite_iUnion fun i => Set.finite_iUnion fun j => hfin i j).union (Set.finite_range _)
  refine ev_mono (ev_fin c (p := fun x c => x ∈ (f c).range) (fun x => hs x) S hS) ?_
  intro c' hc
  exact desc_ex (f c') (hf c') P
    (fun g i j => hc _ (Or.inl (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨g, rfl⟩⟩⟩)))
    (fun v i j => hc _ (Or.inr ⟨(v, i, j), rfl⟩))

variable (𝔞 : Amb l)

private theorem j_comp {c c' : Coef l} (h : c.O ≤ c'.O) : (𝔞.j c').comp ((residue c'.O).comp (inc h)) = 𝔞.red c := by
  ext x
  simp only [RingHom.comp_apply, Amb.j, Amb.red, ResidueField.map_residue]
  rw [← 𝔞.compat c c' h x]
  rfl

private theorem ev_k (x : 𝔞.k) : Ev fun c => x ∈ (𝔞.j c).range := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨c0, z, hz⟩ := 𝔞.alg y
  refine ⟨c0, fun c' h => ⟨IsLocalRing.residue _ (inc h z), ?_⟩⟩
  have e := congrArg (fun φ => φ z) (j_comp 𝔞 h)
  simp only [RingHom.comp_apply] at e
  rw [e]
  exact (Ideal.Quotient.eq.2 hz).symm

private theorem ev_poly (c : Coef l) (x : 𝔞.k[X]) : Ev fun c => x ∈ (mapRingHom (𝔞.j c)).range := by
  classical
  have hS : (x.coeff '' (x.support : Set ℕ)).Finite := (x.support.finite_toSet).image _
  refine ev_mono (ev_fin c (p := fun y c => y ∈ (𝔞.j c).range) (fun y => ev_k 𝔞 y) _ hS) ?_
  intro c' hc
  rw [Polynomial.mem_map_range]
  intro n
  by_cases hn : n ∈ x.support
  · exact hc _ ⟨n, hn, rfl⟩
  · have h0 : x.coeff n = 0 := by simpa using hn
    rw [h0]
    exact zero_mem _

end Ev

theorem UpperTheory.V.Ws.chainDesc :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (c : Coef l) {Γ : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (Φ : Fr c.O Γ) (s t : PD Φ.ι Γ 𝔞.k),
      Φ.IsRes (𝔞.red c) s → Φ.Chain (𝔞.red c) s t → ∃ c₁ : Coef l, ∀ (c' : Coef l) (h : c.O ≤ c'.O), c₁.O ≤ c'.O →
        ∃ s' t' : PD Φ.ι Γ (ResidueField c'.O), s'.map (𝔞.j c') = s ∧ t'.map (𝔞.j c') = t ∧ Φ.IsRes ((residue c'.O).comp (inc h)) s' ∧ Φ.Chain ((residue c'.O).comp (inc h)) s' t' := by
  intro l _ 𝔞 c Γ _ _ _ Φ s t hs hst
  haveI := Φ.fin
  obtain ⟨hg, hrt⟩ := hst
  suffices key : ∀ t, Relation.ReflTransGen (fun x y => Φ.Good (𝔞.red c) y ∧ Φ.Linked (𝔞.red c) x y) s t →
      Ev (fun c' : Coef l => ∀ h : c.O ≤ c'.O, ∃ s' t' : PD Φ.ι Γ (ResidueField c'.O), s'.map (𝔞.j c') = s ∧
        t'.map (𝔞.j c') = t ∧ Φ.IsRes ((residue c'.O).comp (inc h)) s' ∧
        Φ.Chain ((residue c'.O).comp (inc h)) s' t') by
    obtain ⟨c1, hc1⟩ := key t hrt
    exact ⟨c1, fun c' h h1 => hc1 c' h1 h⟩
  intro t ht
  induction ht with
  | refl =>
    have lk := ev_pd c (R := fun c' => ResidueField c'.O) (fun c' => 𝔞.j c') (fun c' => (𝔞.j c').injective)
      (fun x => ev_k 𝔞 x) s hs.cont
    refine ev_mono lk ?_
    rintro c' ⟨Q, hQ⟩ h
    have hb := j_comp 𝔞 h
    refine ⟨Q, Q, hQ, hQ, ?_, ?_, Relation.ReflTransGen.refl⟩
    · apply isRes_of Φ _ (𝔞.j c') (𝔞.j c').injective
      rw [hb, hQ]
      exact hs
    · apply good_of Φ _ (𝔞.j c') (𝔞.j c').injective
      rw [hb, hQ]
      exact hg
  | tail _ hxy ih =>
    obtain ⟨hgy, P, hP, h0, h1⟩ := hxy
    have lp := ev_pd c (R := fun c' => (ResidueField c'.O)[X]) (fun c' => mapRingHom (𝔞.j c'))
      (fun c' => Polynomial.map_injective _ (𝔞.j c').injective) (fun x => ev_poly 𝔞 c x) P hP.cont
    refine ev_mono (ev_and ih lp) ?_
    rintro c' ⟨hc, Q, hQ⟩ h
    obtain ⟨s', x', hs', hx', hr', hch⟩ := hc h
    have hb := j_comp 𝔞 h
    have e0 : (𝔞.j c').comp (evalRingHom 0) = (evalRingHom 0).comp (mapRingHom (𝔞.j c')) :=
      RingHom.ext fun p => (Polynomial.eval_zero_map (𝔞.j c') p).symm
    have e1 : (𝔞.j c').comp (evalRingHom 1) = (evalRingHom 1).comp (mapRingHom (𝔞.j c')) :=
      RingHom.ext fun p => (Polynomial.eval_one_map (𝔞.j c') p).symm
    have hC : (mapRingHom (𝔞.j c')).comp (C.comp ((residue c'.O).comp (inc h))) = C.comp (𝔞.red c) := by
      rw [← hb]
      refine RingHom.ext fun z => ?_
      simp
    have hQ0 : Q.map (evalRingHom 0) = x' := by
      apply map_inj' (𝔞.j c') (𝔞.j c').injective
      rw [hx', map_map', e0, ← map_map', hQ, h0]
    refine ⟨s', Q.map (evalRingHom 1), hs', ?_, hr', hch.1, Relation.ReflTransGen.tail hch.2 ⟨?_, Q, ?_, hQ0, rfl⟩⟩
    · rw [map_map', e1, ← map_map', hQ, h1]
    · apply good_of Φ _ (𝔞.j c') (𝔞.j c').injective
      rw [hb, map_map', e1, ← map_map', hQ, h1]
      exact hgy
    · apply isRes_of Φ _ (mapRingHom (𝔞.j c')) (Polynomial.map_injective _ (𝔞.j c').injective)
      rw [hC, hQ]
      exact hP
