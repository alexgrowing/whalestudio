import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Cu

section Inj

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

private theorem adj_mp (f : R →+* R') (X : M4 R) : (adj X).map f = adj (X.map f) := by
  ext i j; simp [adj_apply]

private theorem conj_mp (f : R →+* R') (n m : M4 R) (i j : Fin 4) :
    (adj (n.map f) * m.map f * n.map f) i j = f ((adj n * m * n) i j) := by
  rw [← adj_mp, ← Matrix.map_mul, ← Matrix.map_mul]; rfl

private theorem gsp_of (f : R →+* R') (hf : Function.Injective f) (ν : R) (X : M4 R) (h : IsGSp (f ν) (X.map f)) :
    IsGSp ν X := by
  unfold IsGSp at *
  ext i j
  apply hf
  have := congrFun (congrFun h i) j
  rw [← adj_mp, ← Matrix.map_mul] at this
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at this ⊢
  rw [this]; split_ifs <;> simp

private theorem supp_of (f : R →+* R') (hf : Function.Injective f) (S : Finset (ℤ × ℤ)) (X : M4 R)
    (h : SuppM S (X.map f)) : SuppM S X := fun i j h1 h2 => (map_eq_zero_iff f hf).1 (h i j h1 h2)

private theorem cont_iff {Γ : Type} [TopologicalSpace Γ] (z : Γ → R) : AdicCont ⊥ z ↔ IsLocallyConstant z := by
  refine ⟨fun h => ?_, fun h N => h.comp (Ideal.Quotient.mk (⊥ ^ N))⟩
  refine IsLocallyConstant.desc z (Ideal.Quotient.mk (⊥ ^ 1)) (h 1) fun x y hxy => ?_
  rw [Ideal.Quotient.eq, pow_one, Ideal.mem_bot] at hxy
  exact sub_eq_zero.1 hxy

variable {ι Γ : Type} [Group Γ]

private theorem ent_of (f : R →+* R') (r : Γ →* M4 R) (w : ℤ × ℤ) (h : Ent (mapRep f r) w) : Ent r w := by
  obtain ⟨g, i, j, h1, h2⟩ := h
  exact ⟨g, i, j, h1, fun h0 => h2 (by rw [mapRep_apply, h0, map_zero])⟩

private theorem map_map' (P : PD ι Γ R) (f : R →+* R') (g : R' →+* R'') : (P.map f).map g = P.map (g.comp f) := rfl

private theorem map_inj' (f : R →+* R') (hf : Function.Injective f) {P Q : PD ι Γ R} (h : P.map f = Q.map f) : P = Q := by
  ext g i j
  · exact hf (congrArg (fun X : PD ι Γ R' => X.r g i j) h)
  · exact hf (congrArg (fun X : PD ι Γ R' => X.n g i j) h)

private theorem psi_mp (f : R →+* R') (P : PD ι Γ R) (v : ι) (i : Fin 4) (s : Γ) : (P.map f).ψ v i s = f (P.ψ v i s) :=
  conj_mp f (P.n v) (P.r s) i i

private theorem desc_ex (f : R →+* R') (hf : Function.Injective f) (P : PD ι Γ R')
    (h1 : ∀ g i j, P.r g i j ∈ f.range) (h2 : ∀ v i j, P.n v i j ∈ f.range) : ∃ Q : PD ι Γ R, Q.map f = P := by
  choose r hr using h1
  choose n hn using h2
  have e : ∀ g, (Matrix.of (r g)).map f = P.r g := fun g => by ext i j; exact hr g i j
  have hi : Function.Injective fun X : M4 R => X.map f := Matrix.map_injective hf
  refine ⟨⟨⟨⟨fun g => Matrix.of (r g), hi ?_⟩, fun a b => hi ?_⟩, fun v => Matrix.of (n v)⟩, ?_⟩
  · simp only [e, map_one]
    exact (Matrix.map_one f (map_zero f) (map_one f)).symm
  · simp only [e, map_mul, Matrix.map_mul]
  · ext g i j
    · exact hr g i j
    · exact hn g i j

variable {O : Type} [CommRing O] (Φ : Fr O Γ) (a : O →+* R)

private theorem inV_of (f : R →+* R') (hf : Function.Injective f) (P : PD Φ.ι Γ R) (h : Fr.InV (P.map f)) : Fr.InV P :=
  ⟨fun g => supp_of f hf _ _ (h.1 g), fun v => ⟨supp_of f hf _ _ (h.2 v).1, fun h0 => (h.2 v).2 (by
    show f (P.n v 2 0) = 0
    rw [h0, map_zero])⟩⟩

private theorem good_of (f : R →+* R') (hf : Function.Injective f) (P : PD Φ.ι Γ R) (h : Φ.Good (f.comp a) (P.map f)) :
    Φ.Good a P := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · exact .inl ⟨ent_of f _ _ h1, h2.imp (ent_of f _ _) (ent_of f _ _)⟩
  · exact .inr (.inl ⟨ent_of f _ _ h1, ent_of f _ _ h2⟩)
  · exact .inr (.inr (.inl ⟨inV_of Φ f hf P h1, ent_of f _ _ h2⟩))
  · refine .inr (.inr (.inr ⟨inV_of Φ f hf P h1, ent_of f _ _ h2, ent_of f _ _ h3, fun v => ?_⟩))
    obtain ⟨s, hs, h5⟩ := h4 v
    exact ⟨s, hs, fun h0 => h5 (by rw [RingHom.comp_apply, h0, map_one])⟩

private theorem inA_of (f : R →+* R') (hf : Function.Injective f) (P : PD Φ.ι Γ R) (h : InA (P.map f)) : InA P :=
  ⟨fun g => supp_of f hf _ _ (h.1 g), fun v h0 => h.2 v (by
    show f (P.n v 1 0) = 0
    rw [h0, map_zero])⟩

private theorem good_pair_of_injective (f : R →+* R') (hf : Function.Injective f) (P : PD Φ.ι Γ R) (h : Good4 Φ (f.comp a) (P.map f)) :
    Good4 Φ a P := by
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact .inl (good_of Φ a f hf P h)
  · exact .inr (.inl ⟨inA_of Φ f hf P h1, ent_of f _ _ h2⟩)
  · exact .inr (.inr ⟨inA_of Φ f hf P h1, ent_of f _ _ h2, ent_of f _ _ h3⟩)

private theorem isRes_of [TopologicalSpace Γ] (f : R →+* R') (hf : Function.Injective f) (P : PD Φ.ι Γ R)
    (h : Φ.IsRes (f.comp a) (P.map f)) : Φ.IsRes a P := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3⟩, c1⟩ := h
  refine ⟨⟨fun g => gsp_of f hf _ _ (a1 g), fun g hg => Matrix.map_injective hf ?_, fun i j hij => ?_,
    fun v => ⟨gsp_of f hf _ _ (by rw [map_one]; exact (a4 v).1), fun i => hf ?_, fun i j hij => ?_⟩,
    fun v s hs i j hij => ?_, fun v s hs i => hf ?_⟩, ⟨fun g i => hf (b1 g i), fun v s hs i => hf ?_, ?_⟩, fun i j => ?_⟩
  · exact (a2 g hg).trans (Matrix.map_one f (map_zero f) (map_one f)).symm
  · exact (map_eq_zero_iff f hf).1 (a3 hij)
  · rw [map_one]; exact (a4 v).2.1 i
  · exact (map_eq_zero_iff f hf).1 ((a4 v).2.2 i j hij)
  · exact (map_eq_zero_iff f hf).1 ((conj_mp f _ _ i j).symm.trans (a5 v s hs i j hij))
  · rw [map_one, ← psi_mp]; exact a6 v s hs i
  · rw [← psi_mp]; exact b2 v s hs i
  · exact b3.imp (fun h => ⟨fun g => supp_of f hf _ _ (h.1 g), fun v => supp_of f hf _ _ (h.2 v)⟩)
      fun h g => supp_of f hf _ _ (h g)
  · exact (cont_iff _).2 (IsLocallyConstant.desc _ f ((cont_iff _).1 (c1 i j)) hf)

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
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨c, fun _ _ x hx => hx.elim⟩
  | @insert y _ _ _ ih =>
    refine ev_mono (ev_and (hp y) ih) fun c' h x hx => ?_
    rcases hx with rfl | hx
    exacts [h.1, h.2 x hx]

private theorem ev_pd (c : Coef l) {R : Coef l → Type} [∀ c, CommRing (R c)] {R' : Type} [CommRing R'] (f : ∀ c, R c →+* R')
    (hf : ∀ c, Function.Injective (f c)) (hs : ∀ x, Ev fun c => x ∈ (f c).range) {ι Γ : Type} [Finite ι] [Group Γ]
    [TopologicalSpace Γ] [CompactSpace Γ] (P : PD ι Γ R') (hP : P.Cont ⊥) : Ev fun c => ∃ Q : PD ι Γ (R c), Q.map (f c) = P := by
  have h1 : (⋃ i, ⋃ j, Set.range fun g => P.r g i j).Finite :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun j => ((cont_iff _).1 (hP i j)).range_finite
  have h2 : (⋃ i, ⋃ j, Set.range fun v => P.n v i j).Finite :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun j => Set.finite_range _
  refine ev_mono (ev_and (ev_fin c hs _ h1) (ev_fin c hs _ h2)) fun c' h => desc_ex _ (hf c') P
    (fun g i j => h.1 _ ?_) fun g i j => h.2 _ ?_
  all_goals exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, g, rfl⟩⟩

variable (𝔞 : Amb l)

private theorem j_comp {c c' : Coef l} (h : c.O ≤ c'.O) : (𝔞.j c').comp ((residue c'.O).comp (inc h)) = 𝔞.red c := by
  ext x
  exact congrArg (residue 𝔞.V) (𝔞.compat c c' h x)

private theorem ev_k (x : 𝔞.k) : Ev fun c => x ∈ (𝔞.j c).range := by
  obtain ⟨x, rfl⟩ := residue_surjective x
  obtain ⟨c, y, hy⟩ := 𝔞.alg x
  refine ⟨c, fun c' h => ⟨residue c'.O (inc h y), ?_⟩⟩
  refine (RingHom.congr_fun (j_comp 𝔞 h) y).trans ?_
  exact (Ideal.Quotient.eq.2 hy).symm

private theorem ev_poly (c : Coef l) (x : 𝔞.k[X]) : Ev fun c => x ∈ (mapRingHom (𝔞.j c)).range := by
  refine ev_mono (ev_fin c (ev_k 𝔞) _ x.coeffs.finite_toSet) fun c' h => ?_
  rw [Polynomial.mem_map_range]
  intro n
  by_cases h0 : x.coeff n = 0
  · rw [h0]; exact zero_mem _
  · exact h _ (Polynomial.coeff_mem_coeffs h0)

end Ev

theorem UpperTheory.V.Cu.chainDesc4 : ChainDesc4 := by
  intro l _ 𝔞 c Γ _ _ _ Φ s t hs ⟨hg, hch⟩
  have key : Ev fun c' : Coef l => ∀ (h : c.O ≤ c'.O) (s' : PD Φ.ι Γ (ResidueField c'.O)), s'.map (𝔞.j c') = s →
      ∃ t' : PD Φ.ι Γ (ResidueField c'.O), t'.map (𝔞.j c') = t ∧ Relation.ReflTransGen
        (fun x y => Good4 Φ ((residue c'.O).comp (inc h)) y ∧ Φ.Linked ((residue c'.O).comp (inc h)) x y) s' t' := by
    induction hch with
    | refl => exact ⟨c, fun c' _ h s' e => ⟨s', e, .refl⟩⟩
    | tail _ hl ih =>
      obtain ⟨hy, P, hP, rfl, rfl⟩ := hl
      have hi : ∀ c' : Coef l, Function.Injective (mapRingHom (𝔞.j c')) := fun c' =>
        Polynomial.map_injective _ (𝔞.j c').injective
      refine ev_mono (ev_and ih (ev_pd c (R := fun c' => (ResidueField c'.O)[X]) (fun c' => mapRingHom (𝔞.j c')) hi
        (ev_poly 𝔞 c) P hP.cont)) ?_
      rintro c' ⟨h1, Q, rfl⟩ h s' e
      obtain ⟨b, hb, hc⟩ := h1 h s' e
      have e0 : (𝔞.j c').comp (evalRingHom 0) = (evalRingHom 0).comp (mapRingHom (𝔞.j c')) := by
        ext <;> simp
      have e1 : (𝔞.j c').comp (evalRingHom 1) = (evalRingHom 1).comp (mapRingHom (𝔞.j c')) := by
        ext <;> simp
      have f1 : (Q.map (evalRingHom 1)).map (𝔞.j c') = (Q.map (mapRingHom (𝔞.j c'))).map (evalRingHom 1) := by
        rw [map_map', map_map', e1]
      refine ⟨Q.map (evalRingHom 1), f1, hc.tail ⟨good_pair_of_injective Φ _ (𝔞.j c') (𝔞.j c').injective _ ?_, Q,
        isRes_of Φ _ _ (hi c') Q ?_, map_inj' (𝔞.j c') (𝔞.j c').injective ?_, rfl⟩⟩
      · rw [j_comp, f1]; exact hy
      · rw [← RingHom.comp_assoc, mapRingHom_comp_C, RingHom.comp_assoc, j_comp]; exact hP
      · rw [hb, map_map', map_map', e0]
  obtain ⟨c₁, h₁⟩ := ev_and key (ev_pd c (R := fun c' => ResidueField c'.O) 𝔞.j (fun c' => (𝔞.j c').injective) (ev_k 𝔞) s hs.cont)
  refine ⟨c₁, fun c' h h' => ?_⟩
  obtain ⟨k1, s', e⟩ := h₁ c' h'
  obtain ⟨t', e', hc⟩ := k1 h s' e
  refine ⟨s', t', e, e', isRes_of Φ _ (𝔞.j c') (𝔞.j c').injective _ ?_, good_pair_of_injective Φ _ (𝔞.j c') (𝔞.j c').injective _ ?_, hc⟩
  · rw [j_comp, e]; exact hs
  · rw [j_comp, e]; exact hg
