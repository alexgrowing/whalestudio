import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section

variable {R R' : Type} [CommRing R] [CommRing R'] {j : R →+* R'}

private theorem adj_map (j : R →+* R') (X : M4 R) : adj (X.map j) = (adj X).map j := by
  ext i i'
  simp only [adj_apply, Matrix.map_apply, map_zsmul]

private theorem conj_map (j : R →+* R') (n X : M4 R) :
    adj (n.map j) * X.map j * n.map j = (adj n * X * n).map j := by
  rw [adj_map, ← Matrix.map_mul, ← Matrix.map_mul]

private theorem map_inj (hj : Function.Injective j) {X Y : M4 R} : X.map j = Y.map j ↔ X = Y :=
  (Matrix.map_injective hj).eq_iff

private theorem isGSp_iff (hj : Function.Injective j) (ν : R) (X : M4 R) : IsGSp (j ν) (X.map j) ↔ IsGSp ν X := by
  have h : (j ν) • (1 : M4 R') = (ν • (1 : M4 R)).map j := by
    ext i i'
    by_cases h : i = i' <;> simp [Matrix.one_apply, h]
  unfold IsGSp
  rw [adj_map, ← Matrix.map_mul, h, map_inj hj]

private theorem one_iff (hj : Function.Injective j) (X : M4 R) : X.map j = 1 ↔ X = 1 := by
  rw [← Matrix.map_one (⇑j) (map_zero j) (map_one j), map_inj hj]

private theorem diag_iff (hj : Function.Injective j) (X : M4 R) : (X.map j).IsDiag ↔ X.IsDiag := by
  simp only [Matrix.IsDiag, Matrix.map_apply, map_eq_zero_iff j hj]

private theorem up_iff (hj : Function.Injective j) (X : M4 R) : IsUp (X.map j) ↔ IsUp X := by
  simp only [IsUp, Matrix.map_apply, map_eq_zero_iff j hj]

private theorem low_iff (hj : Function.Injective j) (X : M4 R) : IsLow (X.map j) ↔ IsLow X := by
  have h := isGSp_iff hj 1 X
  rw [map_one] at h
  simp only [IsLow, h, Matrix.map_apply, map_eq_zero_iff j hj, map_eq_one_iff j hj]

private theorem suppM_iff (hj : Function.Injective j) (S : Finset (ℤ × ℤ)) (X : M4 R) :
    SuppM S (X.map j) ↔ SuppM S X := by
  simp only [SuppM, Matrix.map_apply, map_eq_zero_iff j hj]

variable {ι Γ : Type} [Group Γ]

private theorem r_map (j : R →+* R') (c : PD ι Γ R) (g : Γ) : (c.map j).r g = (c.r g).map j := rfl

private theorem n_map (j : R →+* R') (c : PD ι Γ R) (v : ι) : (c.map j).n v = (c.n v).map j := rfl

private theorem psi_map (j : R →+* R') (c : PD ι Γ R) (v : ι) (i : Fin 4) (s : Γ) :
    (c.map j).ψ v i s = j (c.ψ v i s) := by
  simp only [PD.ψ, r_map, n_map, conj_map, Matrix.map_apply]

private theorem supp_iff (hj : Function.Injective j) (S : Finset (ℤ × ℤ)) (c : PD ι Γ R) :
    Supp S (c.map j).r ↔ Supp S c.r := by
  simp only [Supp, r_map, suppM_iff hj]

private theorem ent_iff (hj : Function.Injective j) (c : PD ι Γ R) (w : ℤ × ℤ) :
    Ent (c.map j).r w ↔ Ent c.r w := by
  simp only [Ent, r_map, Matrix.map_apply, ne_eq, map_eq_zero_iff j hj]

private theorem adic_bot {X : Type} [TopologicalSpace X] (f : X → R) : AdicCont ⊥ f ↔ IsLocallyConstant f := by
  refine ⟨fun h => ?_, fun h N => h.comp _⟩
  refine IsLocallyConstant.desc f (Ideal.Quotient.mk ((⊥ : Ideal R) ^ 1)) (h 1) ?_
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, pow_one]

private theorem cont_iff [TopologicalSpace Γ] (hj : Function.Injective j) (c : PD ι Γ R) :
    (c.map j).Cont ⊥ ↔ c.Cont ⊥ := by
  simp only [PD.Cont, adic_bot, r_map, Matrix.map_apply]
  exact forall_congr' fun a => forall_congr' fun b =>
    ⟨fun h => IsLocallyConstant.desc _ j h hj, fun h => h.comp j⟩

end

theorem UpperTheory.V.Ws.chainMap :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) {k k' : Type} [Field k] [Field k'] (a : O →+* k) (j : k →+* k') (c : PD Φ.ι Γ k),
      (Φ.IsRes (j.comp a) (c.map j) ↔ Φ.IsRes a c) ∧ (Φ.Good (j.comp a) (c.map j) ↔ Φ.Good a c) ∧ Function.Injective fun c : PD Φ.ι Γ k => c.map j := by
  intro O Γ _ _ _ _ _ _ Φ k k' _ _ a j c
  have hj : Function.Injective j := j.injective
  have e1 : ∀ g, IsGSp ((j.comp a) (Φ.ν g : O)) ((c.map j).r g) ↔ IsGSp (a (Φ.ν g)) (c.r g) :=
    fun g => by rw [RingHom.comp_apply, r_map, isGSp_iff hj]
  have e2 : ∀ g, (c.map j).r g = 1 ↔ c.r g = 1 := fun g => by rw [r_map, one_iff hj]
  have e3 : Matrix.IsDiag ((c.map j).r Φ.g0) ↔ Matrix.IsDiag (c.r Φ.g0) := by rw [r_map, diag_iff hj]
  have e4 : ∀ v, IsLow ((c.map j).n v) ↔ IsLow (c.n v) := fun v => by rw [n_map, low_iff hj]
  have e5 : ∀ v s, IsUp (adj ((c.map j).n v) * (c.map j).r s * (c.map j).n v) ↔
      IsUp (adj (c.n v) * c.r s * c.n v) :=
    fun v s => by rw [n_map, r_map, conj_map, up_iff hj]
  have e6 : ∀ v i s, (c.map j).ψ v i s = 1 ↔ c.ψ v i s = 1 :=
    fun v i s => by rw [psi_map, map_eq_one_iff j hj]
  have e7 : ∀ g i, (c.map j).r g i i = (j.comp a) (Φ.χ i g : O) ↔ c.r g i i = a (Φ.χ i g) :=
    fun g i => by rw [r_map, Matrix.map_apply, RingHom.comp_apply, hj.eq_iff]
  have e8 : ∀ v i s, (c.map j).ψ v i s = (j.comp a) (Φ.χ i s : O) ↔ c.ψ v i s = a (Φ.χ i s) :=
    fun v i s => by rw [psi_map, RingHom.comp_apply, hj.eq_iff]
  have e9 : ((Supp nP (c.map j).r ∧ ∀ v, SuppM qQ ((c.map j).n v)) ∨ Supp nM (c.map j).r) ↔
      ((Supp nP c.r ∧ ∀ v, SuppM qQ (c.n v)) ∨ Supp nM c.r) := by
    simp only [supp_iff hj, n_map, suppM_iff hj]
  have e10 : Fr.InV (Φ := Φ) (c.map j) ↔ Fr.InV (Φ := Φ) c := by
    simp only [Fr.InV, supp_iff hj, n_map, suppM_iff hj, Matrix.map_apply, ne_eq, map_eq_zero_iff j hj]
  have hP : Φ.IsPair (j.comp a) (c.map j) ↔ Φ.IsPair a c :=
    ⟨fun h => ⟨fun g => (e1 g).1 (h.mult g), fun g hg => (e2 g).1 (h.kill g hg), e3.1 h.nrm,
        fun v => (e4 v).1 (h.low v), fun v s hs => (e5 v s).1 (h.flag v s hs),
        fun v s hs i => (e6 v i s).1 (h.mu v s hs i)⟩,
      fun h => ⟨fun g => (e1 g).2 (h.mult g), fun g hg => (e2 g).2 (h.kill g hg), e3.2 h.nrm,
        fun v => (e4 v).2 (h.low v), fun v s hs => (e5 v s).2 (h.flag v s hs),
        fun v s hs i => (e6 v i s).2 (h.mu v s hs i)⟩⟩
  have hR : Φ.Res (j.comp a) (c.map j) ↔ Φ.Res a c :=
    ⟨fun h => ⟨fun g i => (e7 g i).1 (h.diag g i), fun v s hs i => (e8 v i s).1 (h.char v s hs i),
        e9.1 h.shape⟩,
      fun h => ⟨fun g i => (e7 g i).2 (h.diag g i), fun v s hs i => (e8 v i s).2 (h.char v s hs i),
        e9.2 h.shape⟩⟩
  refine ⟨⟨fun h => ⟨hP.1 h.pair, hR.1 h.res, (cont_iff hj c).1 h.cont⟩,
    fun h => ⟨hP.2 h.pair, hR.2 h.res, (cont_iff hj c).2 h.cont⟩⟩, ?_, ?_⟩
  · simp only [Fr.Good, ent_iff hj, e10, RingHom.comp_apply, ne_eq, map_eq_one_iff j hj]
  · intro x y h
    apply PD.ext
    · ext g : 1
      exact (map_inj hj).1 (congrArg (fun e : PD Φ.ι Γ k' => e.r g) h)
    · funext v
      exact (map_inj hj).1 (congrArg (fun e : PD Φ.ι Γ k' => e.n v) h)
