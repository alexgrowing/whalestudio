import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv

noncomputable section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem charpoly_mulLeft_eq_of_gen {F A : Type} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (u : A) (Q : F[X]) (hQ : Q.Monic) (hadj : Algebra.adjoin F {u} = ⊤) (hr : aeval u Q = 0)
    (hd : Module.finrank F A = Q.natDegree) : (LinearMap.mulLeft F u).charpoly = Q := by
  set P := (LinearMap.mulLeft F u).charpoly with hPdef
  have hP : P.Monic := LinearMap.charpoly_monic _
  have hPd : P.natDegree = Q.natDegree := by rw [hPdef, LinearMap.charpoly_natDegree, hd]
  by_cases hQ1 : Q = 1
  · subst hQ1
    rw [natDegree_one] at hPd
    exact Polynomial.eq_one_of_monic_natDegree_zero hP hPd
  set d := Q.natDegree with hddef
  let v : Fin d → A := fun i => u ^ (i : ℕ)
  have hsp : ⊤ ≤ Submodule.span F (Set.range v) := by
    intro a _
    have ha : a ∈ Algebra.adjoin F {u} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨p, rfl⟩ := ha
    show aeval u p ∈ _
    rw [← Polynomial.aeval_modByMonic_eq_self_of_root hr,
      Polynomial.aeval_eq_sum_range' (Polynomial.natDegree_modByMonic_lt p hQ hQ1)]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, Finset.mem_range.1 hi⟩, rfl⟩)
  have hli : LinearIndependent F v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hsp (by simp [hd, hddef])
  have hPu : aeval u P = 0 := by
    have h1 := LinearMap.aeval_self_charpoly (LinearMap.mulLeft F u)
    have h2 : (Algebra.lmul F A) u = LinearMap.mulLeft F u := by ext; simp
    rw [← hPdef, ← h2, Polynomial.aeval_algHom_apply] at h1
    have h3 := congrArg (fun f : Module.End F A => f 1) h1
    simpa using h3
  by_contra hne
  have hR : P - Q ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (P - Q).degree < d := by
    have := Polynomial.degree_sub_lt (p := P) (q := Q) (by rw [Polynomial.degree_eq_natDegree hP.ne_zero,
      Polynomial.degree_eq_natDegree hQ.ne_zero, hPd]) hP.ne_zero (by rw [hP.leadingCoeff, hQ.leadingCoeff])
    rwa [Polynomial.degree_eq_natDegree hP.ne_zero, hPd] at this
  have hRd : (P - Q).natDegree < d := (Polynomial.natDegree_lt_iff_degree_lt hR).2 hdeg
  have hz : aeval u (P - Q) = 0 := by simp [hPu, hr]
  rw [Polynomial.aeval_eq_sum_range' hRd, Finset.sum_range (fun i => (P - Q).coeff i • u ^ i)] at hz
  have hc := (Fintype.linearIndependent_iff.1 hli) (fun i => (P - Q).coeff i) hz ⟨_, hRd⟩
  exact hR (Polynomial.leadingCoeff_eq_zero.1 hc)

theorem charpoly_of_semilinear {F L A : Type} [Field F] [Field L] [CommRing A] [Algebra F A] [Module.Finite F A]
    (e : F ≃+* L) {n : ℕ} (u : A) (g : Matrix (Fin n) (Fin n) L) (ψ : A ≃+ (Fin n → L))
    (hψ : ∀ (c : F) (y : A), ψ (c • y) = e c • ψ y) (hu : ∀ y, ψ (u * y) = g *ᵥ ψ y) :
    g.charpoly = (LinearMap.mulLeft F u).charpoly.map (e : F →+* L) := by
  let b := Module.finBasis F A
  set d := Module.finrank F A
  let v : Fin d → (Fin n → L) := fun i => ψ (b i)
  have hsum : ∀ c : Fin d → L, ∑ i, c i • v i = ψ (∑ i, e.symm (c i) • b i) := by
    intro c
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hψ, e.apply_symm_apply]
  have hli : LinearIndependent L v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    rw [hsum, map_eq_zero_iff ψ ψ.injective] at hc
    have := (Fintype.linearIndependent_iff.1 b.linearIndependent) _ hc i
    simpa using this
  have hsp : ⊤ ≤ Submodule.span L (Set.range v) := by
    intro x _
    obtain ⟨a, rfl⟩ := ψ.surjective x
    rw [← b.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hψ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' : Module.Basis (Fin d) L (Fin n → L) := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = v i := fun i => Module.Basis.mk_apply hli hsp i
  let M := LinearMap.toMatrix b b (LinearMap.mulLeft F u)
  have key : LinearMap.toMatrix b' b' (Matrix.toLin' g) = M.map (e : F →+* L) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, hb', Matrix.toLin'_apply]
    have h1 : g *ᵥ v j = ∑ k, e (b.repr (u * b j) k) • b' k := by
      show g *ᵥ ψ (b j) = _
      rw [← hu]
      conv_lhs => rw [← b.sum_repr (u * b j)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hψ, hb']
    rw [h1, b'.repr_sum_self]
    simp [M, LinearMap.toMatrix_apply, Algebra.leftMulMatrix_eq_repr_mul]
  calc g.charpoly = (Matrix.toLin' g).charpoly := by
        rw [← LinearMap.charpoly_toMatrix (Matrix.toLin' g) (Pi.basisFun L (Fin n)),
          LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    _ = (M.map (e : F →+* L)).charpoly := by rw [← key, LinearMap.charpoly_toMatrix]
    _ = _ := by rw [Matrix.charpoly_map, LinearMap.charpoly_toMatrix]

theorem charpoly_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E) (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) (γ : GLw n w), Q.Monic → Fits w e B Q u → IsModel w e B u x γ → γ.val.charpoly = Q := by
  intro E _ _ _ w K e n Q B u x γ hQ hfit hmod
  obtain ⟨hadj, hr, hd, -⟩ := hfit
  obtain ⟨ψ, hψ, hu, -⟩ := hmod
  rw [charpoly_of_semilinear e u γ.val ψ hψ hu,
    charpoly_mulLeft_eq_of_gen u (Q.map e.symm.toRingHom) (hQ.map _) hadj hr (by rw [hd, natDegree_map]),
    Polynomial.map_map]
  ext i
  simp [Polynomial.coeff_map]

end GlobalTheory.KapLat
