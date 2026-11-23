import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UnivDetMf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UniversalDeformationRingLocalCharacters
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CoCoprod
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private structure COb (O : Type) [CommRing O] [IsLocalRing O] : Type 1 where
  R : Type
  [ring : CommRing R]
  [alg : Algebra O R]
  [co : IsCO O R]

attribute [local instance] COb.ring COb.alg COb.co

private theorem coprod_opt (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (T : Type) [Finite T] (A : Type) [CommRing A] [Algebra O A] [IsCO O A]
    (B : T → Type) [∀ t, CommRing (B t)] [∀ t, Algebra O (B t)] [∀ t, IsCO O (B t)] :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (a : A →ₐ[O] R) (j : ∀ t, B t →ₐ[O] R),
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (fa : A →ₐ[O] R') (f : ∀ t, B t →ₐ[O] R'),
        ∃! g : R →ₐ[O] R', g.comp a = fa ∧ ∀ t, g.comp (j t) = f t := by
  let B' : Option T → Type := fun o => Option.rec A B o
  let iR : ∀ o, CommRing (B' o) := fun o =>
    Option.rec (motive := fun o => CommRing (B' o)) (inferInstance : CommRing A)
      (fun t => (inferInstance : CommRing (B t))) o
  let iA : ∀ o, @Algebra O (B' o) _ (iR o).toCommSemiring.toSemiring := fun o =>
    Option.rec (motive := fun o => @Algebra O (B' o) _ (iR o).toCommSemiring.toSemiring)
      (inferInstance : Algebra O A) (fun t => (inferInstance : Algebra O (B t))) o
  have iC : ∀ o, @IsCO O (B' o) _ _ (iR o) (iA o) := fun o =>
    Option.rec (motive := fun o => @IsCO O (B' o) _ _ (iR o) (iA o))
      (inferInstance : IsCO O A) (fun t => (inferInstance : IsCO O (B t))) o
  obtain ⟨R, iR', iA', iC', j, hj⟩ := @co_coprod O _ _ _ _ (Option T) _ B' iR iA iC
  refine ⟨R, iR', iA', iC', j none, fun t => j (some t), ?_⟩
  intro R' _ _ _ fa f
  let F' : ∀ o, @AlgHom O (B' o) R' _ (iR o).toCommSemiring.toSemiring _ (iA o) _ := fun o =>
    Option.rec (motive := fun o => @AlgHom O (B' o) R' _ (iR o).toCommSemiring.toSemiring _ (iA o) _) fa f o
  obtain ⟨g, hg, hu⟩ := hj R' F'
  refine ⟨g, ⟨hg none, fun t => hg (some t)⟩, ?_⟩
  rintro g' ⟨h1, h2⟩
  apply hu
  intro o
  cases o with
  | none => exact h1
  | some t => exact h2 t

section

variable {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
  [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R')

private theorem adic_map {Γ : Type} [TopologicalSpace Γ] {u : Γ → R} (hu : AdicCont (maximalIdeal R) u) :
    AdicCont (maximalIdeal R') fun g => f (u g) := by
  intro N
  have hm : maximalIdeal R ≤ (maximalIdeal R').comap (f : R →+* R') := by
    intro x hx
    rw [Ideal.mem_comap, ← res_eq_zero_iff O R']
    change res O R' (f x) = 0
    rw [res_map, res_eq_zero_iff O R]
    exact hx
  have hN : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hm) N
  have hc := (hu N).comp (Ideal.quotientMap (maximalIdeal R' ^ N) (f : R →+* R') hN)
  convert hc using 1
  funext g
  simp [Ideal.quotientMap_mk]

private theorem def_map {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] {Dbar : GDet n (ResidueField O) G}
    {D : GDet n R G} (h : IsDef O Dbar D) : IsDef O Dbar (D.map (f : R →+* R')) := by
  refine ⟨?_, ?_⟩
  · have hc := h.cont
    unfold GDet.IsCont at hc ⊢
    intro i
    have e : ∀ g : G, (D.map (f : R →+* R')).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
      intro g
      have := ((d_gmap D).2.2.1 (f : R →+* R') (MonoidAlgebra.single g 1)).2 i
      simpa [MonoidAlgebra.mapRingHom_single] using this
    simp only [e]
    exact adic_map f (hc i)
  · rw [(d_gmap D).2.1]
    have e : ((res O R' : R' →ₐ[O] ResidueField O) : R' →+* ResidueField O).comp (f : R →+* R') = (res O R : R →+* ResidueField O) := by
      ext x
      exact res_map f x
    rw [e]
    exact h.red

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n)

private theorem psi_map {v : F.Vl} {i : Fin n} {ψ : F.Gv v →* Rˣ} (h : r.IsPsi v i ψ) :
    r.IsPsi v i (pushCh (f : R →+* R') ψ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact adic_map f h.cont
  · intro g
    have := h.red g
    simp only [pushCh, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe]
    rw [← this]
    exact res_map f _
  · intro g
    simp only [pushCh, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe]
    rw [h.mu g]
    exact f.commutes _

omit [IsLocalRing O] [IsCO O R] [IsCO O R'] in
private theorem star_map (g : F.G₀) :
    MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (F.star O R n (MonoidAlgebra.single g 1)) =
      F.star O R' n (MonoidAlgebra.single g 1) := by
  unfold GFrame.star GFrame.starOp
  simp only [MonoidAlgebra.lift_single, one_smul, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op,
    MonoidAlgebra.mapRingHom_single]
  congr 1
  unfold GFrame.eps
  have hu : Units.map ((f : R →+* R') : R →* R')
      ((pushCh ((algebraMap O R).comp (algebraMap ℤ_[l] O)) (F.ε.comp F.η.ker.subtype)) g) =
      (pushCh ((algebraMap O R').comp (algebraMap ℤ_[l] O)) (F.ε.comp F.η.ker.subtype)) g := by
    ext
    simp [pushCh]
  rw [← hu, ← map_zpow (Units.map ((f : R →+* R') : R →* R'))]
  rfl

omit [IsLocalRing O] [IsCO O R] [IsCO O R'] [Algebra ℤ_[l] O] in
private theorem oEl_map (v : F.Vl) (ψ : Fin n → F.Gv v →* Rˣ) (g : Fin n → F.Gv v) :
    MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (F.oEl v ψ g) =
      F.oEl v (fun i => pushCh (f : R →+* R') (ψ i)) g := by
  unfold GFrame.oEl
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp [MonoidAlgebra.mapRingHom_single, pushCh]

private def rels (D : GDet n R F.G₀) (ψ : ∀ v, Fin n → F.Gv v →* Rˣ) : Set R :=
  {x | (∃ i g, x = D.lam i (F.star O R n (MonoidAlgebra.single g 1)) - D.lam i (MonoidAlgebra.single g 1)) ∨
    (∃ v g h, x = D.tr (MonoidAlgebra.single h 1 * F.oEl v (ψ v) g)) ∨
    ∃ u, ∃ g ∈ r.Ip u, ∃ h : F.G₀, x = D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1))}

omit [IsCO O R] [IsCO O R'] in
private theorem rels_iff (D : GDet n R F.G₀) (ψ : ∀ v, Fin n → F.Gv v →* Rˣ) :
    (∀ x ∈ rels r D ψ, f x = 0) ↔
      (∀ i g, (D.map (f : R →+* R')).lam i (F.star O R' n (MonoidAlgebra.single g 1)) =
        (D.map (f : R →+* R')).lam i (MonoidAlgebra.single g 1)) ∧
      (∀ v (g : Fin n → F.Gv v) (h : F.G₀), (D.map (f : R →+* R')).tr
        (MonoidAlgebra.single h 1 * F.oEl v (fun i => pushCh (f : R →+* R') (ψ v i)) g) = 0) ∧
      ∀ u, ∀ g ∈ r.Ip u, ∀ h : F.G₀, (D.map (f : R →+* R')).tr
        (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) = 0 := by
  have L : ∀ i (y : MonoidAlgebra R F.G₀), (D.map (f : R →+* R')).lam i
      (MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') y) = f (D.lam i y) :=
    fun i y => ((d_gmap D).2.2.1 (f : R →+* R') y).2 i
  have Tr : ∀ y : MonoidAlgebra R F.G₀, (D.map (f : R →+* R')).tr
      (MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') y) = f (D.tr y) := by
    intro y
    unfold GDet.tr
    exact L 1 y
  have s1 : ∀ g : F.G₀, MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single g 1 := by
    intro g
    simp [MonoidAlgebra.mapRingHom_single]
  have A1 : ∀ i g, (D.map (f : R →+* R')).lam i (F.star O R' n (MonoidAlgebra.single g 1)) =
      f (D.lam i (F.star O R n (MonoidAlgebra.single g 1))) := by
    intro i g
    rw [← star_map f g, L]
  have A2 : ∀ i (g : F.G₀), (D.map (f : R →+* R')).lam i (MonoidAlgebra.single g 1) =
      f (D.lam i (MonoidAlgebra.single g 1)) := by
    intro i g
    rw [← s1 g, L]
  have B : ∀ v (g : Fin n → F.Gv v) (h : F.G₀), (D.map (f : R →+* R')).tr
      (MonoidAlgebra.single h 1 * F.oEl v (fun i => pushCh (f : R →+* R') (ψ v i)) g) =
      f (D.tr (MonoidAlgebra.single h 1 * F.oEl v (ψ v) g)) := by
    intro v g h
    rw [← Tr, map_mul, s1, oEl_map]
  have C : ∀ (g h : F.G₀), (D.map (f : R →+* R')).tr
      (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) =
      f (D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1))) := by
    intro g h
    rw [← Tr, map_mul, map_sub, map_one, s1, s1]
  constructor
  · intro H
    refine ⟨fun i g => ?_, fun v g h => ?_, fun u g hg h => ?_⟩
    · rw [A1, A2, ← sub_eq_zero, ← map_sub]
      exact H _ (Or.inl ⟨i, g, rfl⟩)
    · rw [B]
      exact H _ (Or.inr (Or.inl ⟨v, g, h, rfl⟩))
    · rw [C]
      exact H _ (Or.inr (Or.inr ⟨u, g, hg, h, rfl⟩))
  · rintro ⟨H1, H2, H3⟩ x hx
    rcases hx with ⟨i, g, rfl⟩ | ⟨v, g, h, rfl⟩ | ⟨u, g, hg, h, rfl⟩
    · rw [map_sub, ← A1, ← A2, H1, sub_self]
    · rw [← B]
      exact H2 v g h
    · rw [← C]
      exact H3 u g hg h

end

private theorem pre_univ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l]
    [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) (h0 : PhiCond F.G₀ l) (hv : ∀ v, PhiCond (F.Gv v) l) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (D : GDet n R F.G₀)
      (ψ : ∀ v, Fin n → F.Gv v →* Rˣ), IsDef O r.Dbar D ∧ (∀ v i, r.IsPsi v i (ψ v i)) ∧
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (p : Pair r R'),
        ∃! f : R →ₐ[O] R', D.map (f : R →+* R') = p.D ∧ ∀ v i, pushCh (f : R →+* R') (ψ v i) = p.ψ v i := by
  haveI : CompactSpace F.G₀ := show CompactSpace F.η.ker from
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  obtain ⟨R₀, iR0, iA0, iC0, D₀, hD₀⟩ := univDet_mf l O r.chib h0 r.chib_open r.chib_inj
  have hb := fun t : F.Vl × Fin n => universalDeformationRing_localCharacters r t.1 t.2 (hv t.1)
  choose Rv iRv iAv iCv ψv hψ hU using hb
  obtain ⟨R, iR, iA, iC, a, j, hR⟩ :=
    @coprod_opt O _ _ _ _ (F.Vl × Fin n) _ R₀ iR0 iA0 iC0 Rv iRv iAv iCv
  refine ⟨R, iR, iA, iC, D₀.map (a : R₀ →+* R), fun v i => pushCh (j (v, i) : Rv (v, i) →+* R) (ψv (v, i)),
    def_map a hD₀.isDef, fun v i => psi_map (j (v, i)) r (hψ (v, i)), ?_⟩
  intro R' _ _ _ p
  have hp : IsDef O (GDet.ofChars r.chib) p.D := ⟨p.cont, p.red⟩
  obtain ⟨fD, hfD, -⟩ := hD₀.univ R' p.D hp
  have hq := fun t : F.Vl × Fin n => hU t R' (p.ψ t.1 t.2) (p.psi t.1 t.2)
  choose fv hfv using hq
  have push : ∀ (t : F.Vl × Fin n) (h : R →ₐ[O] R'),
      pushCh (h : R →+* R') (pushCh (j t : Rv t →+* R) (ψv t)) =
        pushCh ((h.comp (j t) : Rv t →ₐ[O] R') : Rv t →+* R') (ψv t) := by
    intro t h
    ext x
    simp [pushCh]
  have dmap : ∀ h : R →ₐ[O] R', (D₀.map (a : R₀ →+* R)).map (h : R →+* R') =
      D₀.map ((h.comp a : R₀ →ₐ[O] R') : R₀ →+* R') := by
    intro h
    rw [(d_gmap D₀).2.1]
    rfl
  obtain ⟨g, ⟨hga, hgj⟩, hgu⟩ := hR R' fD (fun t => fv t)
  refine ⟨g, ⟨?_, fun v i => ?_⟩, ?_⟩
  · rw [dmap, hga]
    exact hfD
  · rw [push (v, i), hgj (v, i)]
    exact (hfv (v, i)).1
  · rintro g' ⟨h1, h2⟩
    apply hgu
    refine ⟨?_, fun t => ?_⟩
    · exact (hD₀.univ R' p.D hp).unique (by rw [← dmap]; exact h1) hfD
    · refine (hfv t).2 _ ?_
      show pushCh ((g'.comp (j t) : Rv t →ₐ[O] R') : Rv t →+* R') (ψv t) = p.ψ t.1 t.2
      rw [← push t]
      exact h2 t.1 t.2

theorem UpperTheory.V.CA.universalDeformationRing_nonempty_of_nonempty_pair :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n), PhiCond F.G₀ l → (∀ v, PhiCond (F.Gv v) l) → (∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R), Nonempty (Pair r R)) → Nonempty (UniversalOrdinaryDeterminantRing r) := by
  intro l _ F O _ _ _ _ _ _ _ n r h0 hv hex
  obtain ⟨R0, iR0, iA0, iC0, ⟨p0⟩⟩ := hex
  obtain ⟨R, iR, iA, iC, D, ψ, hD, hψ, hU⟩ := pre_univ r h0 hv
  have kill : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (p : Pair r R') (f : R →ₐ[O] R'),
      D.map (f : R →+* R') = p.D → (∀ v i, pushCh (f : R →+* R') (ψ v i) = p.ψ v i) →
        ∀ x ∈ rels r D ψ, f x = 0 := by
    intro R' _ _ _ p f h1 h2
    have h2' : ∀ v, (fun i => pushCh (f : R →+* R') (ψ v i)) = p.ψ v := fun v => funext (h2 v)
    refine (rels_iff f r D ψ).mpr ⟨?_, ?_, ?_⟩
    · rw [h1]
      exact fun i g => p.P i g
    · intro v g h
      rw [h1, h2' v]
      exact p.Ord v g h
    · rw [h1]
      exact fun u g hg h => p.I u g hg h
  let I : Ideal R := Ideal.span (rels r D ψ)
  have hkill : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (p : Pair r R') (f : R →ₐ[O] R'),
      D.map (f : R →+* R') = p.D → (∀ v i, pushCh (f : R →+* R') (ψ v i) = p.ψ v i) →
        I ≤ RingHom.ker (f : R →+* R') := by
    intro R' _ _ _ p f h1 h2
    exact Ideal.span_le.mpr (fun x hx => kill R' p f h1 h2 x hx)
  have hI : I ≠ ⊤ := by
    obtain ⟨f0, ⟨h1, h2⟩, -⟩ := hU R0 p0
    intro htop
    have h1mem : (1 : R) ∈ RingHom.ker (f0 : R →+* R0) := hkill R0 p0 f0 h1 h2 (htop ▸ Submodule.mem_top)
    rw [RingHom.mem_ker, map_one] at h1mem
    exact one_ne_zero h1mem
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsCO O (R ⧸ I) := co_quot O R (R ⧸ I) (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I)
  have hzero : ∀ x ∈ rels r D ψ, Ideal.Quotient.mkₐ O I x = 0 := by
    intro x hx
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span hx
  obtain ⟨hP, hO, hIp⟩ := (rels_iff (Ideal.Quotient.mkₐ O I) r D ψ).mp hzero
  refine ⟨⟨R ⧸ I, ⟨D.map ((Ideal.Quotient.mkₐ O I : R →ₐ[O] R ⧸ I) : R →+* R ⧸ I),
    fun v i => pushCh ((Ideal.Quotient.mkₐ O I : R →ₐ[O] R ⧸ I) : R →+* R ⧸ I) (ψ v i),
    (def_map (Ideal.Quotient.mkₐ O I) hD).cont, (def_map (Ideal.Quotient.mkₐ O I) hD).red,
    fun v i => psi_map (Ideal.Quotient.mkₐ O I) r (hψ v i), hP, hO, hIp⟩, ?_⟩⟩
  intro R' _ _ _ p
  obtain ⟨f, ⟨h1, h2⟩, hfu⟩ := hU R' p
  have hk : I ≤ RingHom.ker (f : R →+* R') := hkill R' p f h1 h2
  have key : ∀ h : (R ⧸ I) →ₐ[O] R',
      ((D.map ((Ideal.Quotient.mkₐ O I : R →ₐ[O] R ⧸ I) : R →+* R ⧸ I)).map (h : R ⧸ I →+* R') = p.D ∧
        ∀ v i, pushCh (h : R ⧸ I →+* R')
          (pushCh ((Ideal.Quotient.mkₐ O I : R →ₐ[O] R ⧸ I) : R →+* R ⧸ I) (ψ v i)) = p.ψ v i) ↔
      (D.map ((h.comp (Ideal.Quotient.mkₐ O I) : R →ₐ[O] R') : R →+* R') = p.D ∧
        ∀ v i, pushCh ((h.comp (Ideal.Quotient.mkₐ O I) : R →ₐ[O] R') : R →+* R') (ψ v i) = p.ψ v i) := by
    intro h
    have e1 : (D.map ((Ideal.Quotient.mkₐ O I : R →ₐ[O] R ⧸ I) : R →+* R ⧸ I)).map (h : R ⧸ I →+* R') =
        D.map ((h.comp (Ideal.Quotient.mkₐ O I) : R →ₐ[O] R') : R →+* R') := by
      rw [(d_gmap D).2.1]
      rfl
    have e2 : ∀ v i, pushCh (h : R ⧸ I →+* R')
        (pushCh ((Ideal.Quotient.mkₐ O I : R →ₐ[O] R ⧸ I) : R →+* R ⧸ I) (ψ v i)) =
        pushCh ((h.comp (Ideal.Quotient.mkₐ O I) : R →ₐ[O] R') : R →+* R') (ψ v i) := by
      intro v i
      ext x
      simp [pushCh]
    simp only [e1, e2]
  let g : (R ⧸ I) →ₐ[O] R' := Ideal.Quotient.liftₐ I f (fun a ha => RingHom.mem_ker.mp (hk ha))
  have hgc : g.comp (Ideal.Quotient.mkₐ O I) = f := by
    ext x
    rfl
  refine ⟨g, ?_, ?_⟩
  · unfold Pair.Maps
    dsimp only
    rw [key, hgc]
    exact ⟨h1, h2⟩
  · intro g' hg'
    unfold Pair.Maps at hg'
    dsimp only at hg'
    rw [key] at hg'
    apply Ideal.Quotient.algHom_ext
    rw [hfu _ hg', hgc]
