import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.OrdVan
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdVan2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NmRegArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THidaX
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreO

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp
private theorem ofRep_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (ρ : G →* GL (Fin n) A) (φ : H →* G) :
    (GDet.ofRep (mat ρ)).comap φ = GDet.ofRep (mat (ρ.comp φ)) := by
  refine GDet.ext fun B _ _ x => ?_
  change (GDet.repAlg (mat ρ) B (MonoidAlgebra.mapDomainRingHom B φ x)).det = (GDet.repAlg (mat (ρ.comp φ)) B x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r => simp [GDet.repAlg, mat]
private theorem tr_cj {n : ℕ} {K : Type} [Field K] (Q A : GL (Fin n) K) (Z : Matrix (Fin n) (Fin n) K) (a : K) (ha : a ≠ 0)
    (h : ((a • (((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Z * Q)) * ((Q⁻¹ * A * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).trace = 0) :
    (Z * (A : Matrix (Fin n) (Fin n) K)).trace = 0 := by
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, mul_eq_zero, or_iff_right ha] at h
  have e : ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Z * Q * ((Q⁻¹ * A * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (Z * A) * Q := by
    simp only [Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  rwa [e, Matrix.trace_mul_cycle, Units.mul_inv, Matrix.one_mul] at h
private theorem mat_push {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (f : A →+* B) (ρ : G →* GL (Fin n) A) :
    f.mapMatrix.toMonoidHom.comp (mat ρ) = mat (pushRep f ρ) := rfl
private theorem mat_push' {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (f : A →+* B) (ρ : G →* GL (Fin n) A) (g : G) :
    (mat ρ g).map f = (pushRep f ρ g : Matrix (Fin n) (Fin n) B) := rfl
private theorem map_pt {n : ℕ} {O R K G : Type} [CommRing O] [CommRing R] [CommRing K] [Algebra O R] [Algebra O K] [Group G]
    (D : GDet n R G) (x : R →ₐ[O] O) (ρ : G →* GL (Fin n) O) (h : D.map x.toRingHom = GDet.ofRep (mat ρ)) :
    D.map (((Algebra.ofId O K).comp x : R →ₐ[O] K) : R →+* K) = GDet.ofRep (mat (pushRep (algebraMap O K) ρ)) := by
  have e1 := (CA.d_gmap D).2.1 x.toRingHom (algebraMap O K)
  rw [h, (CA.d_gmap (GDet.ofRep (mat ρ))).2.2.2 (algebraMap O K) (mat ρ), mat_push] at e1
  exact e1.symm
private theorem map_ch {O R K G : Type} [CommRing O] [CommRing R] [CommRing K] [Algebra O R] [Algebra O K] [Group G]
    (χ : G →* Rˣ) (x : R →ₐ[O] O) (χ' : G →* Oˣ) (h : pushCh x.toRingHom χ = χ') :
    pushCh (((Algebra.ofId O K).comp x : R →ₐ[O] K) : R →+* K) χ = pushCh (algebraMap O K) χ' := by
  subst h
  rfl
private theorem tr_fin {n : ℕ} {O K : Type} [CommRing O] [Field K] (f : O →+* K) (Q A : GL (Fin n) K) (Z : Matrix (Fin n) (Fin n) K) (a : K)
    (ha : a ≠ 0) (Z₀ A₀ : Matrix (Fin n) (Fin n) O)
    (h1 : Z₀.map f = a • (((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Z * Q))
    (h2 : A₀.map f = ((Q⁻¹ * A * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (h : (Z₀ * A₀).trace = 0) :
    (Z * (A : Matrix (Fin n) (Fin n) K)).trace = 0 := by
  have e2 := congrArg f h
  rw [map_zero, AddMonoidHom.map_trace f, Matrix.map_mul, h1, h2] at e2
  exact tr_cj Q A Z a ha e2
private theorem re_form {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (I : F.St → Subgroup F.G₀) (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [CommRing K] [Algebra O K]
    (ρ : F.G₀ →* GL (Fin n) K) (P : GL (Fin n) K) (h : F.IsForm O n ρ P) : (reIu F I).IsForm O n ρ P := h
private theorem re_coc {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (I : F.St → Subgroup F.G₀) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ) (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l))
    (h : IsOrdCoc F ρ P I ψ z) : IsOrdCoc (reIu F I) ρ P (reIu F I).Iu ψ z := ⟨h.cont, h.coc, h.pol, h.ine, h.ord⟩
private theorem modelF {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (I : F.St → Subgroup F.G₀) (c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ) (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)) (q : ℕ) (sg : Fin q → F.G₀) (h1 : Continuous ρ)
    (h2 : Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤) (h3 : F.IsForm c.O n ρ P)
    (h4 : (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -P) (h5 : ∀ u, ∀ g ∈ I u, ρ g = 1)
    (h6 : ∀ v, ∃ g, Function.Injective fun i => ψ v i g) (h7 : ∀ v i j, i < j → ψ v i ≠ ψ v j * (F.eps c.O (Qbar l)).comp (F.φ v))
    (h8 : IsOrdCoc F ρ P I ψ z) (h9 : ∀ g, IntM (mat ρ g)) (h10 : IntM (P : Matrix (Fin n) (Fin n) (Qbar l)))
    (h11 : IntM ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))) (h12 : ∀ j, (mat ρ (sg j)).charpoly.Separable) (c₁ : Coef l) :
    ∃ (c' : Coef l) (y : Pt (reIu F I) c'.O n) (z₀ : F.G₀ → Matrix (Fin n) (Fin n) c'.O) (a : Qbar l) (al : Fin q → Fin n → c'.O),
      c₁.O ≤ c'.O ∧ IsModel y ρ P ψ ∧ a ≠ 0 ∧ (∀ g, (z₀ g).map (algebraMap c'.O (Qbar l)) = a • z g) ∧ OCoc y z₀ ∧
      ∀ j, Function.Injective (al j) ∧ (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i)) :=
  model (reIu F I) c ρ P ψ z q sg h1 h2 (re_form F I _ _ ρ P h3) h4 h5 h6 h7 (re_coc F I ρ P ψ z h8) h9 h10 h11 h12 c₁
private theorem shr2 {l : ℕ} [Fact l.Prime] {n : ℕ} {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    [Algebra O (Qbar l)] {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (x : B.B →ₐ[O] O) {I : F.St → Subgroup F.G₀} (y : Pt (reIu F I) O n)
    (ρ₀ : F.G₀ →* GL (Fin n) O) (ψ₀ : ∀ v, Fin n → F.Gv v →* Oˣ) (e1 : @Eq (F.G₀ →* GL (Fin n) O) y.ρ ρ₀)
    (e2 : @Eq (∀ v, Fin n → F.Gv v →* Oˣ) y.ψ ψ₀) {q : ℕ} (sg : Fin q → F.G₀) (al : Fin q → Fin n → O)
    (h1 : B.u.Maps x.toRingHom (GDet.ofRep (mat ρ₀)) ψ₀)
    (h2 : ∀ Z : Matrix (Fin n) (Fin n) O, (∀ g ∈ F.D0, ((F.eps O O g : Oˣ) : O) • (mat ρ₀ g * Z) = Z * mat ρ₀ g) → Z = 0)
    (h3 : ∀ j, Function.Injective (al j) ∧ (mat ρ₀ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i)))
    (h4 : DetQ F O (pushRep (algebraMap O (Qbar l)) ρ₀) (GeneralLinearGroup.map (algebraMap O (Qbar l)) y.P) (Set.range sg))
    (I' : F.St → Subgroup F.G₀) (h : ∀ u, I' u ≤ I u) : ∃ y : Pt (reIu F I') O n,
        B.u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ ∧ y.N4 F.D0 ∧
        (∀ j, Function.Injective (al j) ∧ (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i))) ∧
        DetQ (reIu F I') O (pushRep (algebraMap O (Qbar l)) y.ρ) (GeneralLinearGroup.map (algebraMap O (Qbar l)) y.P) (Set.range sg) := by
  subst e1 e2
  exact ⟨shrink y I' h, h1, h2, h3, h4⟩
private theorem detq_tr' {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Algebra O (Qbar l)] [CommRing O'] [Algebra ℤ_[l] O'] [Algebra O' (Qbar l)]
    (e : (algebraMap O (Qbar l)).comp (algebraMap ℤ_[l] O) = (algebraMap O' (Qbar l)).comp (algebraMap ℤ_[l] O'))
    (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (S : Set F.G₀) (h : DetQ F O ρ P S) : DetQ F O' ρ P S := by
  have e' : F.eps O (Qbar l) = F.eps O' (Qbar l) := by rw [GFrame.eps, GFrame.eps, e]
  unfold DetQ at h
  rw [e'] at h
  exact h
private theorem pairF {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (r : Resid F c.O n) (I : F.St → Subgroup F.G₀)
    (hI : I = r.Ip) (y : Pt (reIu F I) c.O n) (z : F.G₀ → Matrix (Fin n) (Fin n) c.O) [IsCO c.O c.O] [IsCO c.O (DualNumber c.O)]
    (ρ₀ : F.G₀ →* GL (Fin n) c.O) (ψ₀ : ∀ v, Fin n → F.Gv v →* c.Oˣ) (e1 : @Eq (F.G₀ →* GL (Fin n) c.O) y.ρ ρ₀)
    (e2 : @Eq (∀ v, Fin n → F.Gv v →* c.Oˣ) y.ψ ψ₀) (hn : 1 ≤ n) (hO : OCoc y z)
    (h1 : (GDet.ofRep (mat ρ₀)).map (res c.O c.O : c.O →+* ResidueField c.O) = r.Dbar) (h2 : ∀ v i, r.IsPsi v i (ψ₀ v i)) :
    ∃ p : Pair r (DualNumber c.O), p.Maps (TrivSqZeroExt.fstHom c.O c.O c.O : DualNumber c.O →+* c.O) (GDet.ofRep (mat ρ₀)) ψ₀ ∧
      (∀ g, (p.D.tr (MonoidAlgebra.single g 1)).snd = (z g * mat ρ₀ g).trace) ∧
      ∀ v i, ∀ g ∈ F.Iv v, ((p.ψ v i g : (DualNumber c.O)ˣ) : DualNumber c.O).snd = 0 := by
  subst e1 e2 hI
  exact pairDual F c r y z hn hO h1 h2
private theorem modelG {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (I : F.St → Subgroup F.G₀) (c : Coef l) (y : Pt (reIu F I) c.O n)
    (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ) (h : IsModel y ρ P ψ)
    {q : ℕ} (sg : Fin q → F.G₀) (al : Fin q → Fin n → c.O)
    (hal : ∀ j, Function.Injective (al j) ∧ (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i))) :
    ∃ (ρ₀ : F.G₀ →* GL (Fin n) c.O) (ψ₀ : ∀ v, Fin n → F.Gv v →* c.Oˣ), @Eq (F.G₀ →* GL (Fin n) c.O) y.ρ ρ₀ ∧
      @Eq (∀ v, Fin n → F.Gv v →* c.Oˣ) y.ψ ψ₀ ∧ pushRep (algebraMap c.O (Qbar l)) ρ₀ = ρ ∧
      GeneralLinearGroup.map (algebraMap c.O (Qbar l)) y.P = P ∧ (∀ v i, pushCh (algebraMap c.O (Qbar l)) (ψ₀ v i) = ψ v i) ∧
      ∀ j, Function.Injective (al j) ∧ (mat ρ₀ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i)) :=
  ⟨y.ρ, y.ψ, rfl, rfl, h.1, h.2.1, h.2.2, hal⟩
private theorem nmAbs {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (r : Resid F c.O n) (B : UniversalOrdinaryDeterminantRing r)
    (x : B.B →ₐ[c.O] Qbar l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (hn : 1 ≤ n) (h0 : r.V0ok)
    (hD : B.u.D.map (x : B.B →+* Qbar l) = GDet.ofRep (mat ρ)) (hc : Continuous ρ)
    (hsp : Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤) (hform : F.IsForm c.O n ρ P)
    (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ) (hψ : ∀ v i, ψ v i = pushCh (x : B.B →+* Qbar l) (B.u.ψ v i))
    (hreg : ∀ v, ∃ g, Function.Injective fun i => ψ v i g)
    (hN1 : ∀ v i j, i < j → ψ v i ≠ ψ v j * (F.eps c.O (Qbar l)).comp (F.φ v))
    (q : ℕ) (sg : Fin q → F.G₀) (hsg : ∀ j, (mat ρ (sg j)).charpoly.Separable) (hdet : DetQ F c.O ρ P (Set.range sg))
    (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)) (hz : IsOrdCoc F ρ P r.Ip ψ z)
    (hB : ∀ (c' : Coef l) (r' : Resid F c'.O n) (R : Type) [CommRing R] [Algebra c'.O R] [IsCO c'.O R], Nonempty (Pair r' R) → Nonempty (UniversalOrdinaryDeterminantRing r')) :
    ∃ (c' : Coef l) (r' : Resid F c'.O n) (B' : UniversalOrdinaryDeterminantRing r') (x' : B'.B →ₐ[c'.O] c'.O) (δ : B'.B →ₗ[c'.O] c'.O) (al : Fin q → Fin n → c'.O),
      B'.u.D.map (((Algebra.ofId c'.O (Qbar l)).comp x' : B'.B →ₐ[c'.O] Qbar l) : B'.B →+* Qbar l) = GDet.ofRep (mat ρ) ∧
      (∀ v i, pushCh (((Algebra.ofId c'.O (Qbar l)).comp x' : B'.B →ₐ[c'.O] Qbar l) : B'.B →+* Qbar l) (B'.u.ψ v i) = ψ v i) ∧
      IsDer x' δ ∧ (∀ v i, ∀ g ∈ F.Iv v, δ (B'.u.ψ v i g : B'.Bˣ) = 0) ∧
      ((∀ g, δ (B'.u.D.tr (MonoidAlgebra.single g 1)) = 0) → ∃ Y, ∀ g, z g = dY F (mat ρ) Y g) ∧
      ∀ I : F.St → Subgroup F.G₀, (∀ u, I u ≤ r'.Ip u) → ∃ y : Pt (reIu F I) c'.O n,
        B'.u.Maps x'.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ ∧ y.N4 F.D0 ∧
        (∀ j, Function.Injective (al j) ∧ (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i))) ∧
        DetQ (reIu F I) c'.O (pushRep (algebraMap c'.O (Qbar l)) y.ρ) (GeneralLinearGroup.map (algebraMap c'.O (Qbar l)) y.P) (Set.range sg) := by
  obtain ⟨Q, P', hP', hsgn, hP1, hP2, hint⟩ := selfDual F c ρ P hc hsp hform
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := conjAll F c ρ P Q P' hP'
  have hD' : B.u.D.map (x : B.B →+* Qbar l) = GDet.ofRep (mat (cj Q ρ)) := hD.trans k4.symm
  have hine := (Ws.Eb.relKill B x (cj Q ρ) (k2 hsp) hD').2
  obtain ⟨c₂, hc₂, hx₂⟩ := ((GradeZeroInterpolatingElement.coPt c B.B).1 x).1
  have hz' := k7 _ _ _ hz
  have hs : ∀ j, (mat (cj Q ρ) (sg j)).charpoly.Separable := fun j => by rw [k5]; exact hsg j
  have hm := modelF F r.Ip c (cj Q ρ) P' ψ _ q sg (k1 hc) (k2 hsp) (k3 hform) hsgn hine hreg hN1 hz' hint hP1 hP2 hs c₂
  obtain ⟨c', y, z₀, a, al, hle, hM, ha, hz₀, hO, hal'⟩ := hm
  obtain ⟨ρ₀, ψ₀, e1, e2, m1, m2, m3, hal⟩ := modelG F r.Ip c' y _ _ _ hM sg al hal'
  obtain ⟨r', hr', hIp, hV0⟩ := residPush F c c' (hc₂.trans hle) r
  haveI := (abelian₂.dvr_finite l c'.O).1
  haveI : IsCO c'.O (DualNumber c'.O) := co_sqz c'.O c'.O c'.O fun _ => rfl
  obtain ⟨hred, hpsi⟩ := redOf F c c' _ r r' B.B B.u x ρ₀ ψ₀ hr' (fun b => hle (hx₂ b))
    (hD'.trans (congrArg (fun t => GDet.ofRep (mat t)) m1.symm)) fun v i => (m3 v i).trans (hψ v i)
  obtain ⟨p, hp1, hp2, hp3⟩ := pairF F c' r' r.Ip (funext hIp).symm y z₀ ρ₀ ψ₀ e1 e2 hn hO hred hpsi
  obtain ⟨B'⟩ := hB c' r' _ ⟨p⟩
  obtain ⟨x', δ, hδ, hx', hδ1, hδ2⟩ := derOf F c'.O r' B' p _ _ hp1
  have h4 := detq_tr' F c.O c'.O ((IsScalarTower.algebraMap_eq _ _ _).symm.trans (IsScalarTower.algebraMap_eq _ _ _)) _ _ _ (k6 _ hdet)
  rw [← m1, ← m2] at h4
  refine ⟨c', r', B', x', δ, al, ?_, fun v i => ?_, hδ, fun v i g hg => (hδ2 v i g).trans (hp3 v i g hg), fun key => ?_,
    fun I hI => shr2 B' x' y ρ₀ ψ₀ e1 e2 sg al hx' (n4 F c'.O r' ρ₀ (hV0 h0) hred) hal h4 I fun u => (hI u).trans (hIp u).le⟩
  · exact (map_pt B'.u.D x' ρ₀ hx'.1).trans ((congrArg (fun t => GDet.ofRep (mat t)) m1).trans k4)
  · exact (map_ch _ x' _ (hx'.2 v i)).trans (m3 v i)
  · refine trZero ρ z hsp hz.coc fun g => tr_fin (algebraMap c'.O (Qbar l)) Q (ρ g) (z g) a ha (z₀ g) (mat ρ₀ g) (hz₀ g) ?_
      ((hp2 g).symm.trans ((hδ1 g).symm.trans (key g)))
    exact (mat_push' _ _ g).trans (congrArg Units.val ((DFunLike.congr_fun m1 g).trans (cj_apply Q ρ g)))
theorem UpperTheory.V.Th.ordinary_vanishing_two_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Th.OrdVan2Alt := by
  intro hP l _ L Ω _ _ _ _ _ _ s V c n r B ι x h ρ P hS hn2 hn4 h0 hA hD hc haut hsp hform hI0 hN1 ⟨q, sg, hsg, hdet⟩ z hz
  have hn : 1 ≤ n := by omega
  have hN := hP.litN
  have hC : Pa.CohP := ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt,
    GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
  have heps : ∀ v : V.frame.Vl, (V.frame.eps c.O (Qbar l)).comp (V.frame.φ v) =
      (cycBar L Ω l).comp (Dec (F := L) (s.A (Subtype.val v))).subtype := fun v => MonoidHom.ext fun g => by
    have e : V.ε (toGS Ω V.S' (W.resP L Ω g.1)) = cycZ (W.Lp L) Ω l (W.resP L Ω g.1) := DFunLike.congr_fun V.hε _
    apply Units.ext
    change algebraMap c.O (PadicAlgCl l) (algebraMap ℤ_[l] c.O (V.ε (toGS Ω V.S' (W.resP L Ω g.1)) : ℤ_[l]ˣ)) = _
    rw [e]
    rfl
  obtain ⟨c', r', B', x', δ, al, hDx, hψ', hδ, hδ2, hfin, hy⟩ := nmAbs V.frame c r B x ρ P hn h0 hD hc hsp hform x.psi (fun _ _ => rfl)
    (fun v => _root_.UpperTheory.V.Th.Nm.regular_arithmetic_hida_of_literal_automorphy hN s h v (x.psi v) hA.1 (hA.2 v)) (fun v i j _ e => hN1 v i j (e.trans (congrArg _ (heps v))))
    q sg (fun j => (hsg j).2) hdet z hz fun c' r' R _ _ _ => b0Ex (phiAll hC) l L Ω s V c' n r' R
  obtain ⟨Λ', -⟩ := lamEx (W.locCFT hN.aut.art hC) l L Ω s V c' n r'
  obtain ⟨J, hJ, hLev⟩ := _root_.UpperTheory.V.Th.hida_x_of_printed_hida hP l L Ω s V hS c' n hn r' B' Λ' ι
  have hψ : (barPt B' x').psi = x.psi := funext fun v => funext fun i => hψ' v i
  have hAr : (barPt B' x').Arith h := ⟨hA.1, fun v j => by rw [hψ]; exact hA.2 v j⟩
  have hR : (barPt B' x').IsRep (ρ.comp V.pr) :=
    (congrArg (fun D => GDet.comap D V.pr) hDx).trans (ofRep_comap ρ V.pr)
  have hF : ∀ v : Vl l L, HasFlag ((ρ.comp V.pr).comp (Dec (F := L) (s.A v)).subtype) (x.psi v) := fun v => by
    obtain ⟨w, Y, hw⟩ := hz.ord v
    exact ⟨w⁻¹, fun g => by rw [inv_inv]; exact ⟨(hw g).1, (hw g).2.1⟩⟩
  have hJx : J ≤ RingHom.ker (barPt B' x') :=
    hJ _ h (ρ.comp V.pr) hn2 hn4 hAr hR (hc.comp (V.pr_cont continuous_resP)) haut (fun g hg => hI0 _ ⟨g, hg, rfl⟩)
      fun v => by rw [hψ]; exact ⟨hF v, hN1 v⟩
  obtain ⟨y, y1, y2, y3, y4⟩ := hy (globOf r' V).frame.Iu fun u => by
    rintro g ⟨γ, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨Subtype.val γ, h1, rfl⟩, Subgroup.mem_iInf.2 fun i => Subgroup.mem_iInf.1 h2 i⟩
  exact hfin (_root_.UpperTheory.V.Th.core_o_of_literal_automorphy_n hN l L Ω s V c' n r' B' J y x' h q sg al hS hn hLev (fun b hb => Subtype.ext (hJx hb)) hAr y1 y2
    (fun j => ⟨(hsg j).1, y3 j⟩) y4 δ hδ hδ2)
end
