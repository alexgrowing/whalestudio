import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UnivDetMf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UniversalDeformationRingLocalCharacters
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CoCoprod
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SubgroupQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.FiniteHomOfTopFG
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct
open UpperTheory.V.CA

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

end

private theorem finite_open_homs_to_finite_group (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (h : TopFG G)
    (Z : Type) [Group Z] [Finite Z] : Finite {φ : G →* Z // IsOpen (φ.ker : Set G)} := by
  obtain ⟨s, hs, hgen⟩ := h
  haveI : Finite s := hs.to_subtype
  refine Finite.of_injective (fun φ : {φ : G →* Z // IsOpen (φ.ker : Set G)} => fun x : s => φ.1 x) ?_
  intro φ ψ hφψ
  apply Subtype.ext
  have hsub : Subgroup.closure s ≤ φ.1.eqLocus ψ.1 := by
    rw [Subgroup.closure_le]
    intro x hx
    exact congrFun hφψ ⟨x, hx⟩
  have hopen : IsOpen ((φ.1.eqLocus ψ.1 : Subgroup G) : Set G) := by
    refine Subgroup.isOpen_mono (H₁ := φ.1.ker ⊓ ψ.1.ker) ?_ ?_
    · intro x hx
      obtain ⟨h1, h2⟩ := hx
      have e1 : φ.1 x = 1 := h1
      have e2 : ψ.1 x = 1 := h2
      show φ.1 x = ψ.1 x
      rw [e1, e2]
    · rw [Subgroup.coe_inf]
      exact φ.2.inter ψ.2
  have hclosed : IsClosed ((φ.1.eqLocus ψ.1 : Subgroup G) : Set G) := Subgroup.isClosed_of_isOpen _ hopen
  have htop : (Subgroup.closure s).topologicalClosure ≤ φ.1.eqLocus ψ.1 :=
    Subgroup.topologicalClosure_minimal _ hsub hclosed
  rw [(topGen_iff s).mp hgen] at htop
  ext x
  exact htop (Subgroup.mem_top x)

private theorem phi_of_fg (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (l : ℕ) [Fact l.Prime] (h : TopFG G) : PhiCond G l := fun H hH =>
  finite_open_homs_to_finite_group H ((TopFG.subgroup_quot G h).1 H hH) _

private theorem gDet_repAlg_mapDomainRingHom_eq_repAlg_comp {A G H : Type} [CommRing A] [Group G] [Group H] {ι : Type} [Fintype ι]
    [DecidableEq ι] (ρ : G →* Matrix ι ι A) (p : H →* G) (B : Type) [CommRing B] [Algebra A B]
    (x : MonoidAlgebra B H) :
    GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B p x) = GDet.repAlg (ρ.comp p) B x := by
  have hR : ((GDet.repAlg ρ B : MonoidAlgebra B G →ₐ[B] Matrix ι ι B) : MonoidAlgebra B G →+* Matrix ι ι B).comp
      (MonoidAlgebra.mapDomainRingHom B p) =
      ((GDet.repAlg (ρ.comp p) B : MonoidAlgebra B H →ₐ[B] Matrix ι ι B) : MonoidAlgebra B H →+* Matrix ι ι B) := by
    apply MonoidAlgebra.ringHom_ext
    · intro b
      unfold GDet.repAlg
      simp
    · intro g
      unfold GDet.repAlg
      simp
  exact RingHom.congr_fun hR x

private theorem pre_univ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l]
    [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (p : G →* F.G₀) (hp : Continuous p) (hs : Function.Surjective p)
    (h0 : PhiCond G l) (hv : ∀ v, PhiCond (F.Gv v) l) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (D : GDet n R G)
      (ψ : ∀ v, Fin n → F.Gv v →* Rˣ), IsDef O (r.Dbar.comap p) D ∧ (∀ v i, r.IsPsi v i (ψ v i)) ∧
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (D' : GDet n R' G) (ψ' : ∀ v, Fin n → F.Gv v →* R'ˣ),
        IsDef O (r.Dbar.comap p) D' → (∀ v i, r.IsPsi v i (ψ' v i)) →
        ∃! f : R →ₐ[O] R', D.map (f : R →+* R') = D' ∧ ∀ v i, pushCh (f : R →+* R') (ψ v i) = ψ' v i := by
  have hcomap : r.Dbar.comap p = GDet.ofChars (fun i => (r.chib i).comp p) := by
    apply GDet.ext
    intro B _ _ x
    show ((GDet.ofChars r.chib).comap p).D B x = _
    unfold GDet.comap GDet.ofChars GDet.ofRep GDet.diagRep
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    erw [gDet_repAlg_mapDomainRingHom_eq_repAlg_comp]
    rfl
  rw [hcomap]
  have hopen : ∀ i, IsOpen (((r.chib i).comp p).ker : Set G) := fun i => (r.chib_open i).preimage hp
  have hinj : Function.Injective (fun i => (r.chib i).comp p) := by
    intro i j hij
    apply r.chib_inj
    apply MonoidHom.ext
    intro g
    obtain ⟨x, rfl⟩ := hs g
    exact DFunLike.congr_fun hij x
  obtain ⟨R₀, iR0, iA0, iC0, D₀, hD₀⟩ := univDet_mf l O (fun i => (r.chib i).comp p) h0 hopen hinj
  have hb := fun t : F.Vl × Fin n => universalDeformationRing_localCharacters r t.1 t.2 (hv t.1)
  choose Rv iRv iAv iCv ψv hψ hU using hb
  obtain ⟨R, iR, iA, iC, a, j, hR⟩ :=
    @coprod_opt O _ _ _ _ (F.Vl × Fin n) _ R₀ iR0 iA0 iC0 Rv iRv iAv iCv
  refine ⟨R, iR, iA, iC, D₀.map (a : R₀ →+* R), fun v i => pushCh (j (v, i) : Rv (v, i) →+* R) (ψv (v, i)),
    def_map a hD₀.isDef, fun v i => psi_map (j (v, i)) r (hψ (v, i)), ?_⟩
  intro R' _ _ _ D' ψ' hD' hψ'
  obtain ⟨fD, hfD, -⟩ := hD₀.univ R' D' hD'
  have hq := fun t : F.Vl × Fin n => hU t R' (ψ' t.1 t.2) (hψ' t.1 t.2)
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
    · exact (hD₀.univ R' D' hD').unique (by rw [← dmap]; exact h1) hfD
    · refine (hfv t).2 _ ?_
      show pushCh ((g'.comp (j t) : Rv t →ₐ[O] R') : Rv t →+* R') (ψv t) = ψ' t.1 t.2
      rw [← push t]
      exact h2 t.1 t.2

theorem UpperTheory.V.Pa.Core.rrEx :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T), Nonempty (RRObj Λ A) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A
  haveI : CharP (ResidueField O) l := IsCoef.char
  haveI : IsAdicComplete (maximalIdeal O) O := IsCoef.complete
  haveI : Finite (ResidueField O) := IsCoef.finite
  have hfgPh : TopFG Λ.Ph := by
    obtain ⟨s, hs⟩ := Λ.fg
    exact ⟨_, s.finite_toSet, (topGen_iff _).mpr hs⟩
  haveI : CompactSpace (Ph0 Λ) :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ Λ.Ph0_open).isCompact
  have hfg0 : TopFG (Ph0 Λ) := (TopFG.subgroup_quot Λ.Ph hfgPh).1 _ Λ.Ph0_open
  have h0 : PhiCond (Ph0 Λ) l := phi_of_fg _ l hfg0
  have hpc : Continuous (Λ.h.p₀.comp (πo0 Λ)) := Λ.h.p₀_cont.comp Λ.πo0_cont
  have hps : Function.Surjective (Λ.h.p₀.comp (πo0 Λ)) := Λ.h.p₀_surj.comp Λ.πo0_surj
  obtain ⟨R₁, firstRealIndex, iA1, indexCFirst, D₁, ψ₁, hD₁, hψ₁, hU₁⟩ :=
    pre_univ r (Λ.h.p₀.comp (πo0 Λ)) hpc hps h0 (fun v => T.phiV v)
  let σ : Type := Unit ⊕ ((Fin T.q × Fin n) ⊕ (Fin T.q × Fin n))
  haveI : IsCO O (MvPowerSeries σ R₁) := co_mvps O R₁ σ
  let c : R₁ →ₐ[O] MvPowerSeries σ R₁ := IsScalarTower.toAlgHom O R₁ (MvPowerSeries σ R₁)
  have hc : ∀ x, c x = MvPowerSeries.C x := by
    intro x
    simp [c, MvPowerSeries.algebraMap_apply]
  have Xmem : ∀ s : σ, (MvPowerSeries.X s : MvPowerSeries σ R₁) ∈ maximalIdeal (MvPowerSeries σ R₁) := by
    intro s
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
      MvPowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  have dmap : ∀ {R' : Type} [CommRing R'] [Algebra O R'] (G : MvPowerSeries σ R₁ →ₐ[O] R'),
      (D₁.map (c : R₁ →+* MvPowerSeries σ R₁)).map (G : MvPowerSeries σ R₁ →+* R') =
        D₁.map ((G.comp c : R₁ →ₐ[O] R') : R₁ →+* R') := by
    intro R' _ _ G
    rw [(d_gmap D₁).2.1]
    rfl
  have push : ∀ {R' : Type} [CommRing R'] [Algebra O R'] (G : MvPowerSeries σ R₁ →ₐ[O] R') v i,
      pushCh (G : MvPowerSeries σ R₁ →+* R') (pushCh (c : R₁ →+* MvPowerSeries σ R₁) (ψ₁ v i)) =
        pushCh ((G.comp c : R₁ →ₐ[O] R') : R₁ →+* R') (ψ₁ v i) := by
    intro R' _ _ G v i
    ext x
    simp [pushCh]
  refine ⟨⟨MvPowerSeries σ R₁, ⟨D₁.map (c : R₁ →+* MvPowerSeries σ R₁), (def_map c hD₁).cont,
    (def_map c hD₁).red, fun v i => pushCh (c : R₁ →+* MvPowerSeries σ R₁) (ψ₁ v i),
    fun v i => psi_map c r (hψ₁ v i), MvPowerSeries.X (Sum.inl ()), Xmem _,
    fun j i => algebraMap O (MvPowerSeries σ R₁) (A.ut j i) + MvPowerSeries.X (Sum.inr (Sum.inl (j, i))),
    fun j i => by
      rw [add_sub_cancel_left]
      exact Xmem _,
    fun j i => MvPowerSeries.X (Sum.inr (Sum.inr (j, i))), fun j i => Xmem _⟩, ?_⟩⟩
  intro R' _ _ _ t'
  obtain ⟨f₁, ⟨hf1, hf2⟩, hfu⟩ := hU₁ R' t'.D t'.ψ ⟨t'.cont, t'.red⟩ t'.psi
  let a : σ → R' := fun s => Sum.elim (fun _ => t'.s)
    (Sum.elim (fun p => t'.U p.1 p.2 - algebraMap O R' (A.ut p.1 p.2)) (fun p => t'.y p.1 p.2)) s
  have ha : ∀ s, a s ∈ maximalIdeal R' := by
    rintro (⟨⟩ | ⟨j, i⟩ | ⟨j, i⟩)
    · exact t'.s_mem
    · exact t'.U_mem j i
    · exact t'.y_mem j i
  obtain ⟨F, ⟨hFC, hFX⟩, hFu⟩ := co_ev O R₁ R' σ f₁ a ha
  have hFc : F.comp c = f₁ := by
    ext x
    rw [AlgHom.comp_apply, hc, hFC]
  refine ⟨F, ?_, ?_⟩
  · unfold Tup.Maps
    dsimp only
    refine ⟨?_, fun v i => ?_, ?_, fun j i => ?_, fun j i => ?_⟩
    · show (D₁.map (c : R₁ →+* MvPowerSeries σ R₁)).map (F : MvPowerSeries σ R₁ →+* R') = t'.D
      rw [dmap, hFc]
      exact hf1
    · show pushCh (F : MvPowerSeries σ R₁ →+* R') (pushCh (c : R₁ →+* MvPowerSeries σ R₁) (ψ₁ v i)) = t'.ψ v i
      rw [push, hFc]
      exact hf2 v i
    · show F (MvPowerSeries.X (Sum.inl ())) = t'.s
      rw [hFX]
      rfl
    · show F (algebraMap O (MvPowerSeries σ R₁) (A.ut j i) + MvPowerSeries.X (Sum.inr (Sum.inl (j, i)))) = t'.U j i
      rw [map_add, AlgHom.commutes, hFX]
      show algebraMap O R' (A.ut j i) + (t'.U j i - algebraMap O R' (A.ut j i)) = t'.U j i
      ring
    · show F (MvPowerSeries.X (Sum.inr (Sum.inr (j, i)))) = t'.y j i
      rw [hFX]
      rfl
  · intro G hG
    unfold Tup.Maps at hG
    dsimp only at hG
    obtain ⟨g1, g2, g3, g4, g5⟩ := hG
    have hGc : G.comp c = f₁ := by
      apply hfu
      refine ⟨?_, fun v i => ?_⟩
      · rw [← dmap]
        exact g1
      · rw [← push]
        exact g2 v i
    apply hFu
    refine ⟨fun x => ?_, ?_⟩
    · rw [← hc, ← hGc]
      rfl
    · rintro (⟨⟩ | ⟨j, i⟩ | ⟨j, i⟩)
      · exact g3
      · have h4 : G (algebraMap O (MvPowerSeries σ R₁) (A.ut j i) +
            MvPowerSeries.X (Sum.inr (Sum.inl (j, i)))) = t'.U j i := g4 j i
        show G (MvPowerSeries.X (Sum.inr (Sum.inl (j, i)))) = t'.U j i - algebraMap O R' (A.ut j i)
        rw [← h4, map_add, AlgHom.commutes]
        ring
      · exact g5 j i
