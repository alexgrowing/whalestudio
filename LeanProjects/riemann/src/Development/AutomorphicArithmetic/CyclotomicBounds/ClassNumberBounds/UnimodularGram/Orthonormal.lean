import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.UnimodularGram.UnitVector
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.UnimodularGram.IsUnimodIffGram

namespace KStar.Cstarloc

variable {R : Type*} [CommRing R] [StarRing R] {M : Type*} [AddCommGroup M] [Module R M]

private theorem projection_mem_orthogonal (h : Sesq R M) (x : M) (hx : h x x = 1) (z : M) :
    z + (-(h z x)) • x ∈ perp h x := by
  rw [mem_perp]
  simp [hx]

private theorem orthogonal_complement_independent (h : Sesq R M) (x : M) (hx : h x x = 1) (c : R) (y : M)
    (hy : y ∈ perp h x) (e : c • x + y = 0) : c = 0 := by
  rw [mem_perp] at hy
  have := congrArg (fun z => h z x) e
  simpa [hx, hy] using this

private theorem orthogonal_complement_free_finite [IsLocalRing R] [Module.Free R M] [Module.Finite R M]
    (h : Sesq R M) (x : M) (hx : h x x = 1) :
    Module.Finite R (perp h x) ∧ Module.Free R (perp h x) := by
  let p : M →ₗ[R] perp h x :=
    LinearMap.codRestrict (perp h x) (LinearMap.id - (h.flip x).smulRight x) (fun z => by
      have := projection_mem_orthogonal h x hx z
      simpa [sub_eq_add_neg] using this)
  have hp : p.comp (perp h x).subtype = LinearMap.id := by
    ext ⟨z, hz⟩
    rw [mem_perp] at hz
    simp [p, hz]
  have hs : Function.Surjective p := fun z => ⟨z, by
    have := LinearMap.congr_fun hp z
    simpa using this⟩
  haveI : Module.Finite R (perp h x) := Module.Finite.of_surjective p hs
  haveI : Module.Projective R (perp h x) := Module.Projective.of_split _ p hp
  exact ⟨inferInstance, Module.free_of_flat_of_isLocalRing⟩

universe u in
private theorem exists_orthonormal_basis_unimodular [IsLocalRing R] (hR : UnramDatum R) (n : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
      (h : Sesq R M), IsHerm h → IsUnimod h → Module.finrank R M = n →
      ∃ b : Module.Basis (Fin n) R M, IsOrthonormal h b := by
  induction n with
  | zero =>
    intro M _ _ _ _ h _ _ hn
    refine ⟨Module.finBasisOfFinrankEq R M hn, ?_⟩
    ext i
    exact i.elim0
  | succ n ih =>
    intro M _ _ _ _ h hh hu hn
    haveI : Nontrivial M := Module.nontrivial_of_finrank_eq_succ hn
    obtain ⟨x, hx⟩ := exists_norm_one hR h hh hu
    obtain ⟨hfin, hfree⟩ := orthogonal_complement_free_finite h x hx
    have hli := orthogonal_complement_independent h x hx
    have hsp : ∀ z : M, ∃ c : R, z + c • x ∈ perp h x :=
      fun z => ⟨_, projection_mem_orthogonal h x hx z⟩
    have hr : Module.finrank R (perp h x) = n := by
      have := Module.finrank_eq_card_basis
        (Module.Basis.mkFinCons x (Module.finBasis R (perp h x)) hli hsp)
      rw [hn, Fintype.card_fin] at this
      omega
    obtain ⟨b, hb⟩ := ih (perp h x) (restr h (perp h x)) (fun a c => hh a c)
      (isUnimod_restr_perp h hh hu x hx) hr
    refine ⟨Module.Basis.mkFinCons x b hli hsp, ?_⟩
    rw [Module.Basis.coe_mkFinCons]
    have h1 : ∀ j, h (b j) x = 0 := fun j => (b j).2
    have h2 : ∀ j, h x (b j) = 0 := fun j => by rw [hh, h1, star_zero]
    have h3 : ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := fun i j => by
      have := congrFun (congrFun hb i) j
      simpa [gram, Matrix.one_apply] using this
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [gram, hx]
    · simp [gram, h2, Matrix.one_apply, (Fin.succ_ne_zero j).symm]
    · simp [gram, h1, Matrix.one_apply]
    · simp [gram, h3, Matrix.one_apply]

theorem exists_congr_one [IsLocalRing R] (hR : UnramDatum R) {n : Type*} [Fintype n]
    [DecidableEq n] (G : Matrix n n R) (hG : G.IsHermitian) (hd : IsUnit G.det) :
    ∃ P : Matrix n n R, IsUnit P.det ∧ P * G * P.conjTranspose = 1 := by
  let h : Sesq R (n → R) :=
    LinearMap.mk₂'ₛₗ (RingHom.id R) (starRingEnd R) (fun x y => x ⬝ᵥ G.mulVec (star y))
      (fun _ _ _ => add_dotProduct _ _ _) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp [Matrix.mulVec_add]) (fun _ _ _ => by
        simp [Matrix.mulVec_smul, starRingEnd_apply])
  have hg : gram h (Pi.basisFun R n) = G := by
    ext i j
    simp [gram, h, ← Pi.single_star]
  have hh : IsHerm h := (isHerm_iff_gram h (Pi.basisFun R n)).2 (by rw [hg]; exact hG)
  have hu : IsUnimod h := (isUnimod_iff_gram h (Pi.basisFun R n)).2 (by rw [hg]; exact hd)
  obtain ⟨b, hb⟩ := exists_orthonormal_basis_unimodular hR (Fintype.card n) (n → R) h hh hu
    (Module.finrank_fintype_fun_eq_card R)
  let e := Fintype.equivFin n
  let P : Matrix n n R := Matrix.of fun i j => b (e i) j
  have key : P * G * P.conjTranspose = 1 := by
    rw [← hg, ← gram_comb]
    have : (fun i => ∑ j, P i j • (Pi.basisFun R n) j) = fun i => b (e i) := by
      funext i
      have := (Pi.basisFun R n).sum_repr (b (e i))
      simpa [P] using this
    rw [this]
    ext i j
    have := congrFun (congrFun hb (e i)) (e j)
    simpa [gram, Matrix.one_apply] using this
  refine ⟨P, ?_, key⟩
  rw [Matrix.mul_assoc] at key
  exact Matrix.isUnit_det_of_right_inverse key

end KStar.Cstarloc
