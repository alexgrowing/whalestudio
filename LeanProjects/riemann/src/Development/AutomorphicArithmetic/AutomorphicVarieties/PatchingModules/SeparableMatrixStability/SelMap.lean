import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section

variable {A R R' : Type} [CommRing A] [CommRing R] [Algebra A R] [CommRing R'] [Algebra A R'] (f : R →ₐ[A] R') {n : ℕ}

private theorem adic_map {G : Type} [TopologicalSpace G] (t : A) (u : G → R)
    (hu : AdicCont (Ideal.span {algebraMap A R t}) u) :
    AdicCont (Ideal.span {algebraMap A R' t}) fun g => f (u g) := by
  intro N
  have hmap : Ideal.map f ((Ideal.span {algebraMap A R t}) ^ N) =
      (Ideal.span {algebraMap A R' t}) ^ N := by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, AlgHom.commutes]
  have hle : (Ideal.span {algebraMap A R t}) ^ N ≤
      ((Ideal.span {algebraMap A R' t}) ^ N).comap (f : R →+* R') := by
    rw [← Ideal.map_le_iff_le_comap]
    exact hmap.le
  have e : (fun g => Ideal.Quotient.mk ((Ideal.span {algebraMap A R' t}) ^ N) (f (u g))) =
      (Ideal.quotientMap _ (f : R →+* R') hle) ∘
        (fun g => Ideal.Quotient.mk ((Ideal.span {algebraMap A R t}) ^ N) (u g)) := by
    funext g
    simp [Ideal.quotientMap_mk]
  change IsLocallyConstant (fun g => Ideal.Quotient.mk ((Ideal.span {algebraMap A R' t}) ^ N) (f (u g)))
  rw [e]
  exact (hu N).comp _

private theorem mm_mul (M N : Matrix (Fin n) (Fin n) R) : (M * N).map f = M.map f * N.map f :=
  map_mul f.mapMatrix M N

private theorem mm_add (M N : Matrix (Fin n) (Fin n) R) : (M + N).map f = M.map f + N.map f :=
  map_add f.mapMatrix M N

private theorem mm_sub (M N : Matrix (Fin n) (Fin n) R) : (M - N).map f = M.map f - N.map f :=
  map_sub f.mapMatrix M N

private theorem mm_neg (M : Matrix (Fin n) (Fin n) R) : (-M).map f = -M.map f :=
  map_neg f.mapMatrix M

private theorem dY_map {l : ℕ} [Fact l.Prime] (F : GFrame l) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R)
    (Y : Matrix (Fin n) (Fin n) R) (g : F.G₀) :
    (dY F ρ Y g).map f = dY F (fun g => (ρ g).map f) (Y.map f) g := by
  unfold dY
  rw [mm_sub, mm_mul, mm_mul]

end

theorem UpperTheory.V.Pa.sel_map :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (A R R' : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing R'] [Algebra A R'] (f : R →ₐ[A] R') (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)) (V' : Submodule A (Matrix (Fin n) (Fin n) R')), (∀ Z ∈ V, Z.map f ∈ V') → ∀ z, (z ∈ SelZ F t ρ w wi V → (fun g => (z g).map f) ∈ SelZ F t (fun g => (ρ g).map f) (fun v => (w v).map f) (fun v => (wi v).map f) V') ∧ (z ∈ Bd F ρ V → (fun g => (z g).map f) ∈ Bd F (fun g => (ρ g).map f) V') := by
  intro l _ F n A R R' _ _ _ _ _ f t ρ w wi V V' hV z
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun g => hV _ (h1 g), fun i j => ?_, fun g k => ?_, fun g => ?_, fun u g hg => ?_,
      fun v => ?_⟩
    · exact adic_map f t (fun g => z g i j) (h2 i j)
    · beta_reduce
      rw [h3, mm_add, mm_mul, mm_mul]
    · beta_reduce
      rw [h4, mm_neg, Matrix.transpose_map]
    · beta_reduce
      rw [h5 u g hg]
      exact Matrix.map_zero _ (map_zero f)
    · obtain ⟨Y, hY, hloc⟩ := h6 v
      refine ⟨Y.map f, hV _ hY, fun g => ?_⟩
      have key : (wi v).map f * ((z ((F.φ v) g)).map f -
            dY F (fun g => (ρ g).map f) (Y.map f) ((F.φ v) g)) * (w v).map f =
          (wi v * (z ((F.φ v) g) - dY F ρ Y ((F.φ v) g)) * w v).map f := by
        rw [mm_mul, mm_mul, mm_sub, dY_map]
      obtain ⟨hl1, hl2⟩ := hloc g
      refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
      · beta_reduce
        rw [key, Matrix.map_apply, hl1 i j hij, map_zero]
      · beta_reduce
        rw [key, Matrix.map_apply, hl2 hg i, map_zero]
  · rintro ⟨Y, hY, hT, rfl⟩
    refine ⟨Y.map f, hV _ hY, ?_, ?_⟩
    · rw [← Matrix.transpose_map, hT, mm_neg]
    · funext g
      exact dY_map f F ρ Y g
