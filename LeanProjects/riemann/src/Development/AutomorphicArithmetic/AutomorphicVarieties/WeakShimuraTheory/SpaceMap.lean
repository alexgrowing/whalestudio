import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

section
variable {ι Γ R R' R'' : Type} [Group Γ] [CommRing R] [CommRing R'] [CommRing R'']

theorem PD.map_map (P : PD ι Γ R) (f : R →+* R') (g : R' →+* R'') : (P.map f).map g = P.map (g.comp f) := rfl

theorem adj_map (f : R →+* R') (X : M4 R) : adj (X.map f) = (adj X).map f := by
  ext i j
  simp only [adj_apply, Matrix.map_apply]
  rw [map_zsmul]

theorem isGSp_map (f : R →+* R') {ν : R} {X : M4 R} (h : IsGSp ν X) : IsGSp (f ν) (X.map f) := by
  unfold IsGSp at h ⊢
  rw [adj_map, ← Matrix.map_mul, h]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply]
  split_ifs <;> simp

theorem PD.map_r (P : PD ι Γ R) (f : R →+* R') (g : Γ) : (P.map f).r g = (P.r g).map f := rfl

theorem PD.map_n (P : PD ι Γ R) (f : R →+* R') (v : ι) : (P.map f).n v = (P.n v).map f := rfl

theorem PD.map_flag (P : PD ι Γ R) (f : R →+* R') (v : ι) (s : Γ) :
    adj ((P.map f).n v) * (P.map f).r s * (P.map f).n v = (adj (P.n v) * P.r s * P.n v).map f := by
  rw [PD.map_r, PD.map_n, adj_map, ← Matrix.map_mul, ← Matrix.map_mul]

theorem PD.map_ψ (P : PD ι Γ R) (f : R →+* R') (v : ι) (i : Fin 4) (s : Γ) : (P.map f).ψ v i s = f (P.ψ v i s) := by
  unfold PD.ψ
  rw [PD.map_flag]
  rfl

theorem PD.Cont.map [TopologicalSpace Γ] {P : PD ι Γ R} {I : Ideal R} (h : P.Cont I) (f : R →+* R') {J : Ideal R'}
    (hf : I ≤ J.comap f) : (P.map f).Cont J := by
  intro i j N
  have hle : I ^ N ≤ (J ^ N).comap f :=
    (Ideal.pow_right_mono hf N).trans (Ideal.le_comap_pow f N)
  have := (h i j N).comp (Ideal.quotientMap (J ^ N) f hle)
  convert this using 1
  funext g
  simp only [Function.comp_apply, Ideal.quotientMap_mk]
  rfl

end

theorem Fr.IsPair.map {O Γ R R' : Type} [CommRing O] [Group Γ] [CommRing R] [CommRing R'] {Φ : Fr O Γ} {a : O →+* R}
    {P : PD Φ.ι Γ R} (h : Φ.IsPair a P) (f : R →+* R') : Φ.IsPair (f.comp a) (P.map f) where
  mult g := isGSp_map f (h.mult g)
  kill g hg := by rw [PD.map_r, h.kill g hg]; exact Matrix.map_one _ f.map_zero f.map_one
  nrm := h.nrm.map f.map_zero
  low v := ⟨by simpa [PD.map_n] using isGSp_map f (h.low v).1, fun i => by rw [PD.map_n, Matrix.map_apply, (h.low v).2.1, map_one],
    fun i j hij => by rw [PD.map_n, Matrix.map_apply, (h.low v).2.2 i j hij, map_zero]⟩
  flag v s hs i j hij := by rw [PD.map_flag, Matrix.map_apply, h.flag v s hs i j hij, map_zero]
  mu v s hs i := by rw [PD.map_ψ, h.mu v s hs i, map_one]

section
variable {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ]
  {a : O →+* Λ} (X : Space Φ a)

theorem Space.noeth : IsNoetherianRing X.A :=
  haveI := X.ft
  Algebra.FiniteType.isNoetherianRing X.B X.A

theorem Space.pair_map {R : Type} [CommRing R] [Algebra Λ R] (f : X.A →ₐ[Λ] R) :
    Φ.IsPair ((algebraMap Λ R).comp a) (X.P.map (f : X.A →+* R)) := by
  have := X.pair.map (f : X.A →+* R)
  convert this using 1
  ext x
  simp

theorem Space.cont_map {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (f : X.A →ₐ[Λ] R) :
    (X.P.map (f : X.A →+* R)).Cont (maximalIdeal R) := by
  refine X.cont.map _ (Ideal.map_le_iff_le_comap.2 fun b hb => ?_)
  show (f.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b ∈ maximalIdeal R
  rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
  exact hb

theorem Space.hom_ext {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (f f' : X.A →ₐ[Λ] R)
    (h : X.P.map (f : X.A →+* R) = X.P.map (f' : X.A →+* R)) : f = f' := by
  haveI := X.coB
  have hr : ∀ g i j, f (X.P.r g i j) = f' (X.P.r g i j) := by
    intro g i j
    have := congrArg (fun Q => Q.r g i j) h
    exact this
  have hn : ∀ v i j, f (X.P.n v i j) = f' (X.P.n v i j) := by
    intro v i j
    have := congrArg (fun Q => Q.n v i j) h
    exact this
  have hB : f.comp (IsScalarTower.toAlgHom Λ X.B X.A) = f'.comp (IsScalarTower.toAlgHom Λ X.B X.A) := by
    apply X.genB R
    · intro g n
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
      rw [← Polynomial.coeff_map, X.cp_map]
      have e : ∀ φ : X.A →ₐ[Λ] R, φ ((X.P.r g).charpoly.coeff n) =
          (((X.P.r g).map (φ : X.A →+* R)).charpoly).coeff n := by
        intro φ
        rw [Matrix.charpoly_map, Polynomial.coeff_map]
        rfl
      rw [e f, e f']
      congr 2
      ext i j
      exact hr g i j
    · intro v i s hs
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
      rw [X.ψ_map v i s hs]
      have := congrArg (fun Q => Q.ψ v i s) h
      simp only [PD.map_ψ] at this
      exact this
  ext x
  have hx : x ∈ Algebra.adjoin X.B
      ((Set.range fun x : Γ × Fin 4 × Fin 4 => X.P.r x.1 x.2.1 x.2.2) ∪
        Set.range fun x : Φ.ι × Fin 4 × Fin 4 => X.P.n x.1 x.2.1 x.2.2) := by
    rw [X.gen]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with ⟨⟨g, i, j⟩, rfl⟩ | ⟨⟨v, i, j⟩, rfl⟩
    · exact hr g i j
    · exact hn v i j
  | algebraMap b =>
    exact DFunLike.congr_fun hB b
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | mul y z _ _ hy hz => rw [map_mul, map_mul, hy, hz]

end

end UpperTheory.V.Ws
