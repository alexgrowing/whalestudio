import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.OoFiniteHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ResPull
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem adic_map {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => f (a g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  exact (ha N).comp (Ideal.quotientMap _ (f : R →+* R') hle)

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (y : MonoidAlgebra A H) : (D.comap φ).lam i y = D.lam i (MonoidAlgebra.mapDomainRingHom A φ y) := by
  have : (D.comap φ).chi y = D.chi (MonoidAlgebra.mapDomainRingHom A φ y) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom _ φ _) = D.D _ _
    congr 1
    rw [map_sub]
    congr 1
    · simp
    · induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | single g r => simp
  rw [GDet.lam, GDet.lam, this]

private theorem comap_inj {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G)
    (hφ : Function.Surjective φ) {D D' : GDet n A G} (h : D.comap φ = D'.comap φ) : D = D' := by
  refine UpperTheory.V.CA.d_gext D D' fun g i _ _ => ?_
  obtain ⟨g, rfl⟩ := hφ g
  have h1 := lam_comap D φ i (MonoidAlgebra.single g 1)
  have h2 := lam_comap D' φ i (MonoidAlgebra.single g 1)
  rw [h, h2] at h1
  simpa using h1.symm

private theorem ofRep_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (φ : H →* G) : (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ) := by
  refine GDet.ext fun B _ _ x => ?_
  change (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ x)).det = (GDet.repAlg (ρ.comp φ) B x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r => simp [GDet.repAlg]

private theorem lam_push {n : ℕ} {A A' G H : Type} [CommRing A] [CommRing A'] [Group G] [Group H] (φ : H →* G)
    (f : A →+* A') {D : GDet n A H} {D' : GDet n A' G} (h : D'.comap φ = D.map f) (i : ℕ) (y : MonoidAlgebra A H) :
    D'.lam i (((MonoidAlgebra.mapDomainRingHom A' φ).comp (MonoidAlgebra.mapRingHom H f)) y) = f (D.lam i y) := by
  rw [RingHom.comp_apply, ← lam_comap, h]
  exact ((UpperTheory.V.CA.d_gmap D).2.2.1 f y).2 i

private theorem push_single {A A' G H : Type} [CommRing A] [CommRing A'] [Group G] [Group H] (φ : H →* G)
    (f : A →+* A') (g : H) (a : A) :
    ((MonoidAlgebra.mapDomainRingHom A' φ).comp (MonoidAlgebra.mapRingHom H f)) (MonoidAlgebra.single g a) =
      MonoidAlgebra.single (φ g) (f a) := by
  simp

theorem UpperTheory.V.Pa.Core.ooPair :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) [IsCO O (W.R ⧸ ii W)], 1 ≤ n → Nonempty (OoPair W) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W _ hn
  obtain ⟨D', hD, hc⟩ := ooDet l L G0 T Λ n O r B u J D A W hn
  obtain ⟨r', c1, c2, c3⟩ := resPull l L Λ.G G0 Λ.h n O r
  have hs : Function.Surjective (πo0 Λ) := Λ.πo0_surj
  let f : W.R →ₐ[O] W.R ⧸ ii W := Ideal.Quotient.mkₐ O (ii W)
  have h0 : ∀ a, Rel W a → Ideal.Quotient.mk (ii W) a = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ha)
  have key := lam_push (πo0 Λ) (Ideal.Quotient.mk (ii W)) hD
  have ps := push_single (πo0 Λ) (Ideal.Quotient.mk (ii W))
  refine ⟨{ r' := r', compat := ⟨c1, c2, c3⟩,
            p := { D := D', ψ := fun v i => pushCh (Ideal.Quotient.mk (ii W)) (W.t.ψ v i), cont := hc, red := ?_,
                   psi := fun v i => ?_, P := fun i g => ?_, Ord := fun v g h => ?_, I := fun w g hg h => ?_ },
            D_eq := hD, ψ_eq := fun _ _ => rfl }⟩
  · refine comap_inj (πo0 Λ) hs ?_
    have e : (D'.map (res O (W.R ⧸ ii W) : (W.R ⧸ ii W) →+* ResidueField O)).comap (πo0 Λ) =
        (D'.comap (πo0 Λ)).map (res O (W.R ⧸ ii W) : (W.R ⧸ ii W) →+* ResidueField O) := rfl
    have e2 : (res O (W.R ⧸ ii W) : (W.R ⧸ ii W) →+* ResidueField O).comp (Ideal.Quotient.mk (ii W)) =
        (res O W.R : W.R →+* ResidueField O) := RingHom.ext fun x => res_map f x
    rw [e, hD, (UpperTheory.V.CA.d_gmap W.t.D).2.1, e2, W.t.red, Resid.Dbar, Resid.Dbar, ofRep_comap, ofRep_comap]
    congr 1
    refine MonoidHom.ext fun g => ?_
    change Matrix.diagonal _ = Matrix.diagonal _
    congr 1
    funext i
    rw [c1 i]
    rfl
  · refine ⟨adic_map f (W.t.psi v i).cont, fun g => ?_, fun g => ?_⟩
    · rw [c2]
      exact (res_map f _).trans ((W.t.psi v i).red g)
    · rw [c3]
      change f (W.t.ψ v i g : W.R) = _
      exact (congrArg f ((W.t.psi v i).mu g)).trans (f.commutes _)
  · obtain ⟨g, rfl⟩ := hs g
    let g' : Ph0 Λ := ⟨Λ.ct * g * Λ.ct⁻¹, (MonoidHom.normal_ker _).conj_mem _ g.2 _⟩
    have hg' : πo0 Λ g' = Λ.G.frame.conj (πo0 Λ g) := Subtype.ext (by
      change Λ.πo (Λ.ct * g * Λ.ct⁻¹) = Λ.G.c * Λ.πo g * Λ.G.c⁻¹
      rw [map_mul, map_mul, map_inv, Λ.ct_o])
    have h1 := h0 _ (Rel.pol i g g' rfl)
    rw [map_sub, sub_eq_zero, ← key, ← key, ps, ps, map_one, map_inv, hg'] at h1
    rw [← h1]
    have he : Units.map (f : W.R →* W.R ⧸ ii W) (Λ.G.frame.eps O W.R (πo0 Λ g)) =
        Λ.G.frame.eps O (W.R ⧸ ii W) (πo0 Λ g) := Units.ext (f.commutes _)
    simp only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, one_smul, MonoidHom.coe_mk, OneHom.coe_mk,
      MulOpposite.unop_op]
    rw [← he, ← map_zpow (Units.map (f : W.R →* W.R ⧸ ii W))]
    rfl
  · obtain ⟨h, rfl⟩ := hs h
    choose ga hga using fun i => hs (Λ.G.φ v (g i))
    have h1 := h0 _ (Rel.ord v g ga h hga)
    rw [GDet.tr, ← key, map_mul, ps, map_one, map_list_prod, List.map_ofFn] at h1
    rw [← h1, GDet.tr, GFrame.oEl]
    congr 4
    funext i
    rw [Function.comp_apply, map_sub, ps, ps, map_one, map_one, hga]
    rfl
  · obtain ⟨h, rfl⟩ := hs h
    obtain ⟨g, hj, rfl⟩ := hg.1
    obtain ⟨ga, hga⟩ := hs (Λ.G.φu w g)
    have h1 := h0 _ (Rel.ine w g ga h hj hga)
    rw [GDet.tr, ← key, map_mul, map_sub, ps, ps, map_one, map_one, hga] at h1
    exact h1
