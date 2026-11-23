import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem gdet_ofRep_diagRep_map_eq_ofRep_pushCh {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G]
    (χ : Fin n → G →* Aˣ) (f : A →+* A') :
    (GDet.ofRep (diagRep χ)).map f = GDet.ofRep (diagRep (fun i => pushCh f (χ i))) := by
  refine GDet.ext fun B _ _ x => ?_
  simp only [GDet.map, GDet.ofRep, GDet.repAlg]
  congr 4
  apply congrArg
  refine MonoidHom.ext fun s => ?_
  ext i j
  simp [diagRep, pushCh, Matrix.diagonal_apply, RingHom.algebraMap_toAlgebra]
  split_ifs <;> simp

private theorem gdet_map_chi_mapRingHom_eq_map_chi {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    {A' : Type} [CommRing A'] (f : A →+* A') (x : MonoidAlgebra A G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f x) = (D.chi x).map f := by
  letI : Algebra A (Polynomial A') := ((algebraMap A' (Polynomial A')).comp f).toAlgebra
  let φ : Polynomial A →ₐ[A] Polynomial A' :=
    { Polynomial.mapRingHom f with
      commutes' := fun a => by simp [RingHom.algebraMap_toAlgebra] }
  have key := D.nat (Polynomial A) (Polynomial A') φ
    (MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom G Polynomial.C) x)
  have e : (MonoidAlgebra.mapRingHom G (φ : Polynomial A →+* Polynomial A'))
        (MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom G Polynomial.C) x)
      = MonoidAlgebra.single 1 Polynomial.X
          - (MonoidAlgebra.mapRingHom G Polynomial.C) (MonoidAlgebra.mapRingHom G f x) := by
    rw [map_sub, MonoidAlgebra.mapRingHom_single]
    congr 1
    · simp [φ]
    · ext g
      simp [φ, MonoidAlgebra.mapRingHom]
  rw [e] at key
  exact key

private theorem gdet_map_lam_mapRingHom_eq_lam {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    {A' : Type} [CommRing A'] (f : A →+* A') (i : ℕ) (x : MonoidAlgebra A G) :
    (D.map f).lam i (MonoidAlgebra.mapRingHom G f x) = f (D.lam i x) := by
  simp only [GDet.lam, gdet_map_chi_mapRingHom_eq_map_chi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]

private theorem adicCont_maximalIdeal_comp_of_isLocalHom {Γ R R' : Type} [TopologicalSpace Γ] [CommRing R] [IsLocalRing R]
    [CommRing R'] [IsLocalRing R'] (g : R →+* R') [IsLocalHom g] {φ : Γ → R}
    (h : AdicCont (maximalIdeal R) φ) : AdicCont (maximalIdeal R') (fun x => g (φ x)) := by
  intro N
  have hm : (maximalIdeal R).map g ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.mpr fun x hx => map_nonunit g x hx
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap g := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hm N
  have := (h N).comp (Ideal.quotientMap (maximalIdeal R' ^ N) g hle)
  convert this using 1
  funext x
  simp [Ideal.quotientMap_mk]

private theorem res_eq_zero_of_mem_maximalIdeal {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [IsCO O R] (x : R) (hx : x ∈ maximalIdeal R) : res O R x = 0 := by
  show ((RingEquiv.ofBijective _ _).symm.toRingHom.comp (residue R)) x = 0
  simp [(IsLocalRing.residue_eq_zero_iff x).mpr hx]

theorem UpperTheory.V.Pa.BC.pair_bc :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra ℤ_[l] O] [Algebra ℤ_[l] O'] [IsScalarTower ℤ_[l] O O'] (n : ℕ) (r : Resid F O n) (r' : Resid F O' n), RBC r r' → ∀ (R R' : Type) [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O' R'] [IsCO O' R'] (g : R →+* R') [IsLocalHom g], (∀ a, g (algebraMap O R a) = algebraMap O' R' (algebraMap O O' a)) → ∀ p : Pair r R, (∀ x, res O' R' (g x) = ResidueField.map (algebraMap O O') (res O R x)) ∧ ∃ p' : Pair r' R', p.Maps g p'.D p'.ψ := by
  intro l _ F O O' _ _ _ _ _ _ _ _ _ n r r' hr R R' _ _ _ _ _ _ g _ hg p
  have hres : ∀ x, res O' R' (g x) = ResidueField.map (algebraMap O O') (res O R x) := by
    intro x
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
    have hx : x = algebraMap O R a + (x - algebraMap O R a) := by ring
    have h2 : g (x - algebraMap O R a) ∈ maximalIdeal R' := map_nonunit g _ ha
    rw [hx, map_add, map_add, map_add, hg, res_eq_zero_of_mem_maximalIdeal _ h2, res_eq_zero_of_mem_maximalIdeal _ ha, add_zero, add_zero,
      AlgHom.commutes, AlgHom.commutes, ResidueField.algebraMap_eq, ResidueField.algebraMap_eq,
      ResidueField.map_residue]
  have hs1 : ∀ h : F.G₀, (MonoidAlgebra.single h (1 : R') : MonoidAlgebra R' F.G₀)
      = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1) := by
    intro h
    simp [MonoidAlgebra.mapRingHom_single]
  refine ⟨hres, ⟨⟨p.D.map g, fun v i => pushCh g (p.ψ v i), ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, fun _ _ => rfl⟩⟩
  · intro i
    have key : (fun h : F.G₀ => (p.D.map g).lam i (MonoidAlgebra.single h 1))
        = fun h => g (p.D.lam i (MonoidAlgebra.single h 1)) := by
      funext h
      rw [hs1, gdet_map_lam_mapRingHom_eq_lam]
    show AdicCont _ _
    rw [key]
    exact adicCont_maximalIdeal_comp_of_isLocalHom g (p.cont i)
  · have hrg : ((res O' R' : R' →ₐ[O'] ResidueField O') : R' →+* ResidueField O').comp g
        = (ResidueField.map (algebraMap O O')).comp ((res O R : R →ₐ[O] ResidueField O) : R →+* ResidueField O) :=
      RingHom.ext hres
    have e1 : (p.D.map g).map ((res O' R' : R' →ₐ[O'] ResidueField O') : R' →+* ResidueField O')
        = (p.D.map ((res O R : R →ₐ[O] ResidueField O) : R →+* ResidueField O)).map
            (ResidueField.map (algebraMap O O')) := by
      refine GDet.ext fun B _ _ x => ?_
      simp only [GDet.map]
      congr 2
      congr 1
      refine RingHom.ext fun y => ?_
      show algebraMap (ResidueField O') B (res O' R' (g y)) = algebraMap (ResidueField O') B (ResidueField.map (algebraMap O O') (res O R y))
      rw [hres]
    rw [e1, p.red]
    show (GDet.ofRep (diagRep r.chib)).map _ = GDet.ofRep (diagRep r'.chib)
    rw [gdet_ofRep_diagRep_map_eq_ofRep_pushCh]
    congr 2
    funext i
    exact (hr.1 i).symm
  · intro v i
    refine ⟨?_, ?_, ?_⟩
    · have := adicCont_maximalIdeal_comp_of_isLocalHom g (p.psi v i).cont
      simpa [pushCh] using this
    · intro x
      have h1 := (p.psi v i).red x
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
      rw [hres, h1, hr.2.1 v i]
      simp [pushCh]
    · intro x
      have h1 := (p.psi v i).mu x
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
      rw [h1, hg, hr.2.2 v i]
      simp [pushCh]
  · intro i h
    have he : ∀ y : F.G₀, Units.map (g : R →* R') (F.eps O R y) = F.eps O' R' y := by
      intro y
      ext
      simp [GFrame.eps, pushCh, hg, ← IsScalarTower.algebraMap_apply]
    have hs : F.star O' R' n (MonoidAlgebra.single h 1)
        = MonoidAlgebra.mapRingHom F.G₀ g (F.star O R n (MonoidAlgebra.single h 1)) := by
      simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, MonoidAlgebra.mapRingHom_single, ← he]
      rw [← map_zpow]
      rfl
    rw [hs, hs1, gdet_map_lam_mapRingHom_eq_lam, gdet_map_lam_mapRingHom_eq_lam, p.P]
  · intro v gg h
    have e : MonoidAlgebra.single h 1 * F.oEl v (fun i => pushCh g (p.ψ v i)) gg
        = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1 * F.oEl v (p.ψ v) gg) := by
      rw [map_mul, ← hs1]
      congr 1
      simp [GFrame.oEl, map_list_prod, List.map_ofFn, Function.comp_def, pushCh,
        MonoidAlgebra.mapRingHom_single]
    have h0 := p.Ord v gg h
    simp only [GDet.tr] at h0 ⊢
    rw [e, gdet_map_lam_mapRingHom_eq_lam, h0, map_zero]
  · intro u x hx h
    have hx' : x ∈ r.Ip u := by
      simp only [Resid.Ip, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker] at hx ⊢
      refine ⟨hx.1, fun i => ?_⟩
      have h2 := hx.2 i
      rw [hr.1 i] at h2
      ext
      have h3 := congrArg (fun u : (ResidueField O')ˣ => (u : ResidueField O')) h2
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h3
      apply (ResidueField.map (algebraMap O O')).injective
      rw [h3, Units.val_one, map_one]
    have e : MonoidAlgebra.single h (1 : R') * (MonoidAlgebra.single x 1 - 1)
        = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1 * (MonoidAlgebra.single x 1 - 1)) := by
      simp [MonoidAlgebra.mapRingHom_single]
    have h0 := p.I u x hx' h
    simp only [GDet.tr] at h0 ⊢
    rw [e, gdet_map_lam_mapRingHom_eq_lam, h0, map_zero]
