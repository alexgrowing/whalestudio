import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsEigenvalueGLOneEqCuspidalLabelGen

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published.DepthZeroModel
open GlobalTheory.SerSys.TameGen

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

abbrev tauOne (θ : (ZMod g)ˣ →* ℂˣ) : FDRep ℂ (Gn g 1) :=
  FDRep.of (GlobalTheory.GLp.Model.chRep (θ.comp (Matrix.GeneralLinearGroup.det (n := Fin 1))))

theorem tauOne_character (θ : (ZMod g)ˣ →* ℂˣ) (y : Gn g 1) :
    (tauOne θ).character y = θ (Matrix.GeneralLinearGroup.det y) := by
  change LinearMap.trace ℂ ℂ (((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • LinearMap.id) = _
  simp

theorem exists_label (L : LabelDatum g) (θ : (ZMod g)ˣ →* ℂˣ) (u : (ZMod g)ˣ)
    (hu : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1) :
    ∃ P, IsCuspOf L P (tauOne θ).character ∧ liftPoly L.teich P = X - C (θ u : ℂ) := by
  obtain ⟨T, h1, -, h3⟩ := GlobalTheory.Published.GreenModel.green_one L
  have hc : GlobalTheory.GLq.IsCusp (tauOne θ).character := by
    refine ⟨one_pos, ?_, fun a h1 h2 => by omega⟩
    have := GlobalTheory.Published.GreenModel.isIrr_hom
      ((Units.coeHom ℂ).comp (θ.comp (Matrix.GeneralLinearGroup.det (n := Fin 1) (R := ZMod g))))
    convert this using 1
    funext y
    exact tauOne_character θ y
  obtain ⟨P, hP, e⟩ := h3 _ hc
  have hP' : IsCuspOf L P (tauOne θ).character := e ▸ (h1 P hP).1
  refine ⟨P, hP', ?_⟩
  have hb : -P.coeff 0 ≠ 0 := neg_ne_zero.2 hP.2.2.1
  have hr : ∀ b : ZMod g, Formalism.CyclotomicNorms.rootsBar (X - C b) = {algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) b} := fun b => by
    simp [Formalism.CyclotomicNorms.rootsBar]
  have hrP : Formalism.CyclotomicNorms.rootsBar P = {algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (-P.coeff 0)} :=
    (congrArg Formalism.CyclotomicNorms.rootsBar (GlobalTheory.Published.GreenModel.lab_eq hP)).trans (hr _)
  have hcp : ((Matrix.GeneralLinearGroup.scalar (Fin 1) u : Gn g 1) : Mt g 1).charpoly = X - C (u : ZMod g) := by
    simp [Matrix.charpoly, Matrix.GeneralLinearGroup.scalar]
  have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) u) = u := by
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  have h4 := hP'.2.2 (algebraMap _ _ (-P.coeff 0)) (by rw [hrP]; simp) (Matrix.GeneralLinearGroup.scalar (Fin 1) u) (by rw [hcp]; exact irreducible_X_sub_C _)
      (L.gen 1) (by rw [hcp, hr, hu]; simp)
  have h5 := GlobalTheory.GLq.Model.thetaOf_gen_pow L one_pos (GlobalTheory.Published.GreenModel.alg_pow hb) 1
  rw [tauOne_character, hd] at h4
  simp only [pow_one] at h5
  simp only [Nat.sub_self, pow_zero, one_mul, Finset.range_one, Finset.sum_singleton, pow_one, h5] at h4
  rw [h4, liftPoly, hrP]
  simp

theorem inflates_one (i : ℚ_[g] ≃+* w.adicCompletion E) (θ : (ZMod g)ˣ →* ℂˣ) (χ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hχ : GlobalTheory.SmGL.IsSmoothChar χ) (hθ : χ.comp (Units.map i.toRingHom.toMonoidHom) = GlobalTheory.GLp.Model.tame θ) :
    Inflates ((GlobalTheory.SmGL.IrrRep.det (Fin 1) χ hχ).ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) (tauOne θ) := by
  refine ⟨LinearMap.id, fun e => (one_ne_zero : (1 : ℂ) ≠ 0) (LinearMap.congr_fun e (1 : ℂ)), fun k (v : ℂ) => ?_⟩
  have e := GlobalTheory.GLp.Model.tame_inc θ k
  rw [← hθ] at e
  have e2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k)) =
      Units.map i.toRingHom.toMonoidHom (Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.inc g 1 k)) := by
    ext; simp
  change ((θ (Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.red g 1 k)) : ℂˣ) : ℂ) • v =
    ((χ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k))) : ℂˣ) : ℂ) • v
  rw [e2, ← e]; rfl

theorem exists_char (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i.symm) (θ : (ZMod g)ˣ →* ℂˣ) :
    ∃ χ : (w.adicCompletion E)ˣ →* ℂˣ, GlobalTheory.SmGL.IsSmoothChar χ ∧
      χ.comp (Units.map i.toRingHom.toMonoidHom) = GlobalTheory.GLp.Model.tame θ := by
  refine ⟨(GlobalTheory.GLp.Model.tame θ).comp (Units.map i.symm.toRingHom.toMonoidHom), ?_, ?_⟩
  · have hs := (isSC_tameRep θ).1.2.2.1 (1 : ℂ)
    let f : w.adicCompletion E →* Matrix (Fin 1) (Fin 1) ℚ_[g] :=
      ((Matrix.scalar (Fin 1)).comp i.symm.toRingHom).toMonoidHom
    have hf : Continuous f := continuous_matrix fun a b => by
      have : (fun x => f x a b) = i.symm := by
        funext x; rw [Subsingleton.elim a 0, Subsingleton.elim b 0]; simp [f]
      rw [this]; exact hi
    have := hs.preimage (Continuous.units_map f hf)
    unfold GlobalTheory.SmGL.IsSmoothChar
    convert this using 1
    ext x
    have e2 : Matrix.GeneralLinearGroup.det (Units.map f x) = Units.map i.symm.toRingHom.toMonoidHom x := by
      ext; simp [f]
    change GlobalTheory.GLp.Model.tame θ (Units.map i.symm.toRingHom.toMonoidHom x) = 1 ↔
      ((GlobalTheory.GLp.Model.tame θ (Matrix.GeneralLinearGroup.det (Units.map f x)) : ℂˣ) : ℂ) • (1 : ℂ) = 1
    rw [e2]; simp
  · refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.comp_apply]
    congr 1
    ext; simp

theorem rank_one (H : DepthZeroInertia) {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {ε : EpsFamily A} (hε : IsDeligneEps ε) {rc : IrrGL (w.adicCompletion E) → WD h} (hl : Laws a ha ε rc)
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : LabelDatum g) (t : G E Ω) (ht : t ∈ Ine (F := E) A)
    (hT : Formalism.L2.NT.TameCoupled A κ t L.gen) (θ : (ZMod g)ˣ →* ℂˣ) (χ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hχ : GlobalTheory.SmGL.IsSmoothChar χ) (hθ : χ.comp (Units.map i.toRingHom.toMonoidHom) = GlobalTheory.GLp.Model.tame θ)
    (u : (ZMod g)ˣ) (hu : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1) :
    χ (a (ineIncl h ⟨t, ht⟩)) = θ u := by
  obtain ⟨P, hP, e⟩ := exists_label L θ u hu
  have h1 := H E Ω g A w h rc ⟨a, ha, ε, hε, hl⟩ i hi κ L t ht hT 1 (GlobalTheory.SmGL.IrrRep.det (Fin 1) χ hχ)
    (IrrGL.isCusp_ofChar χ hχ) _ P hP (inflates_one i θ χ hχ hθ)
  have h2 : rc (cls (GlobalTheory.SmGL.IrrRep.det (Fin 1) χ hχ)) = _ := hl.one χ hχ
  rw [h2, e, WD.inePol_of_mem_Ine _ ht, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd] at h1
  have h3 := congrArg (fun p => p.coeff 0) h1
  refine Units.ext ?_
  simpa using h3

theorem degrees {rc : IrrGL (w.adicCompletion E) → WD h} (hr : IsRec h rc) (L : LabelDatum g) (t : G E Ω)
    (ht : t ∈ Ine (F := E) A) (n : ℕ) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)))
    (τ : FDRep ℂ (Gn g n)) (P : (ZMod g)[X]) (hP : IsCuspOf L P τ.character) :
    ((rc (cls σ)).inePol t).natDegree = n ∧ (liftPoly L.teich P).natDegree = n := by
  obtain ⟨a, ha, ε, -, hl⟩ := hr
  refine ⟨by rw [WD.inePol_of_mem_Ine _ ht, WD.charPol_natDegree, hl.dim], ?_⟩
  have := natDegree_multiset_prod_X_sub_C_eq_card ((Formalism.CyclotomicNorms.rootsBar P).map L.teich)
  rw [Multiset.map_map, Multiset.card_map] at this
  refine this.trans ?_
  rw [Formalism.CyclotomicNorms.rootsBar, ← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_map, hP.1.2.2.2]

theorem data_exist (p : Nat.Primes) : haveI : Fact p.1.Prime := ⟨p.2⟩
    ∃ (w : HeightOneSpectrum (𝓞 ℚ)) (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : IsPlaceOver A w)
      (i : ℚ_[p.1] ≃+* w.adicCompletion ℚ), Continuous i ∧ ∀ (L : LabelDatum p.1) (θ : (ZMod p.1)ˣ →* ℂˣ),
      ∃ (σ : GlobalTheory.SmGL.IrrRep (GL (Fin 1) (w.adicCompletion ℚ))) (P : (ZMod p.1)[X]), (cls σ).IsCusp ∧
        IsCuspOf L P (tauOne θ).character ∧
        Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) (tauOne θ) := by
  obtain ⟨w, rfl⟩ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).surjective p
  have : Fact (Rat.HeightOneSpectrum.primesEquiv w).1.Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv w).2⟩
  obtain ⟨A, hA⟩ := exists_isPlaceOver (AlgebraicClosure ℚ) w
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv w
  refine ⟨w, A, hA, e.symm.toAlgEquiv.toRingEquiv, e.symm.continuous, fun L θ => ?_⟩
  obtain ⟨χ, hχ, hθ⟩ := exists_char e.symm.toAlgEquiv.toRingEquiv e.continuous θ
  obtain ⟨b, hb, hb'⟩ := GlobalTheory.Published.GreenModel.exists_pre (GlobalTheory.Published.GreenModel.gen_prim' L).pow_eq_one
  obtain ⟨P, hP, -⟩ := exists_label L θ (Units.mk0 b hb) hb'
  exact ⟨_, P, IrrGL.isCusp_ofChar χ hχ, hP, inflates_one _ θ χ hχ hθ⟩

end GlobalTheory.Published.DepthZeroModel
