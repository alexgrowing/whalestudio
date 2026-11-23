import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Factor

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem redB_chi_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (h : H) : (D.comap φ).chi (MonoidAlgebra.single h 1) = D.chi (MonoidAlgebra.single (φ h) 1) := by
  change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
  congr 1
  rw [map_sub]
  simp

private theorem redB_chi_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : W.GDet n A G) (f : A →+* B)
    (g : G) : (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
  letI : Algebra A B[X] := ((algebraMap B B[X]).comp f).toAlgebra
  have h := D.nat A[X] B[X] { Polynomial.mapRingHom f with commutes' := fun a => by simp; rfl }
    (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (MonoidAlgebra.single g 1))
  refine Eq.trans ?_ h
  change D.D B[X] _ = D.D B[X] _
  congr 1
  simp

private theorem redB_abs {n : ℕ} {O R K G : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [Field K] [Group G] (D : W.GDet n R G) (x : R →+* K) (ρ : G →* GL (Fin n) K)
    (χ : Fin n → G →* (ResidueField O)ˣ) (hx : D.map x = W.GDet.ofRep (W.mat ρ))
    (hr : D.map (res O R : R →+* ResidueField O) = W.GDet.ofRep (W.diagRep χ)) :
    ∃ (A : Type) (_ : CommRing A) (j : A →+* K) (φ : A →+* ResidueField O), Function.Injective j ∧ Pr.RedTo ρ j φ χ ∧
      ∀ b : R, ∃ a : A, j a = x b ∧ φ a = res O R b := by
  have hk : ∀ a ∈ RingHom.ker x, (res O R : R →+* ResidueField O) a = 0 := fun a ha =>
    (res_eq_zero_iff O R a).2 (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top x) ha)
  refine ⟨R ⧸ RingHom.ker x, inferInstance, RingHom.kerLift x, Ideal.Quotient.lift _ _ hk, RingHom.kerLift_injective x,
    fun g => ⟨(D.chi (MonoidAlgebra.single g 1)).map (Ideal.Quotient.mk _), ?_, ?_⟩,
    fun b => ⟨Ideal.Quotient.mk _ b, rfl, rfl⟩⟩
  · rw [Polynomial.map_map]
    refine (redB_chi_map D x g).symm.trans ?_
    rw [hx, (AlgebraTools.Det.repApi _).2.1]
    rfl
  · rw [Polynomial.map_map]
    refine (redB_chi_map D (res O R : R →+* ResidueField O) g).symm.trans ?_
    rw [hr, (AlgebraTools.Det.repApi _).2.1]
    exact Matrix.charpoly_diagonal _

theorem UpperTheory.V.Th.Det.redB :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} {B : W.UniversalOrdinaryDeterminantRing r} (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)), x.IsRep (ρ.comp V.pr) → x.D = W.GDet.ofRep (W.mat ρ) ∧ ∃ (A : Type) (_ : CommRing A) (j : A →+* Qbar l) (φ : A →+* ResidueField c.O), Function.Injective j ∧ Pr.RedTo ρ j φ r.chib ∧ ∀ (v : W.Vl l L) i g, ∃ a : A, j a = (x.psi v i g : Qbar l) ∧ φ a = (r.psib v i g : ResidueField c.O) := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B x ρ hx
  have hs : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  have hD : x.D = W.GDet.ofRep (W.mat ρ) := by
    refine CA.d_gext _ _ fun g i _ _ => ?_
    obtain ⟨h, rfl⟩ := hs g
    have e : x.D.comap V.pr = W.GDet.ofRep (W.mat (ρ.comp V.pr)) := hx
    unfold W.GDet.lam
    congr 2
    exact (redB_chi_comap x.D V.pr h).symm.trans ((congrArg (fun D => W.GDet.chi D (MonoidAlgebra.single h 1)) e).trans
      (((AlgebraTools.Det.repApi _).2.1 h).trans ((AlgebraTools.Det.repApi (W.mat ρ)).2.1 (V.pr h)).symm))
  refine ⟨hD, ?_⟩
  obtain ⟨A, _, j, φ, h1, h2, h3⟩ := redB_abs (O := c.O) B.u.D (x : B.B →+* Qbar l) ρ r.chib hD B.u.red
  refine ⟨A, inferInstance, j, φ, h1, h2, fun v i g => ?_⟩
  obtain ⟨a, ha, hb⟩ := h3 (B.u.ψ v i g : B.Bˣ)
  exact ⟨a, ha, hb.trans ((B.u.psi v i).red g)⟩
