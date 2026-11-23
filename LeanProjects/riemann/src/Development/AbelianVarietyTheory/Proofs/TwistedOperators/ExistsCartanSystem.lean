import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CartanFinite

variable {n : ℕ}

theorem exists_scale {G : Matrix (Fin n) (Fin n) ℂ} (hG : Gᴴ = G) {z : Fin n → ℂ} (hz : Function.Injective z)
    (h : (diagonal z)ᴴ * G * diagonal z = G) :
    ∃ d : Fin n → ℂ, (∀ a, d a ≠ 0) ∧ ∀ a b, ((diagonal d)ᴴ * G * diagonal d) a b ∈ ({0, 1, -1} : Finset ℂ) := by
  have h1 : ∀ a b, G a b ≠ 0 → conj (z a) * z b = 1 := fun a b hab => by
    have := congrFun (congrFun h a) b
    rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply, Complex.star_def] at this
    exact mul_right_cancel₀ hab (by linear_combination this)
  have h2 : ∀ a b, G a b ≠ 0 → ∑ c, G a c = G a b := fun a b hab => by
    refine Finset.sum_eq_single b (fun c _ hc => ?_) (by simp)
    by_contra hac
    have h0 : conj (z a) ≠ 0 := left_ne_zero_of_mul_eq_one (h1 a b hab)
    exact hc (hz (mul_left_cancel₀ h0 ((h1 a c hac).trans (h1 a b hab).symm)))
  have h3 : ∀ a, ∃ d : ℂ, d ≠ 0 ∧ (∑ c, G a c ≠ 0 → d ^ 2 * conj (∑ c, G a c) = 1) := fun a => by
    by_cases h0 : ∑ c, G a c = 0
    · exact ⟨1, one_ne_zero, fun h => absurd h0 h⟩
    · obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (conj (∑ c, G a c))⁻¹ two_pos
      have h0' : conj (∑ c, G a c) ≠ 0 := (map_ne_zero _).2 h0
      refine ⟨d, fun e => inv_ne_zero h0' (by rw [← hd, e]; simp), fun _ => by rw [hd, inv_mul_cancel₀ h0']⟩
  choose d hd0 hd using h3
  refine ⟨d, hd0, fun a b => ?_⟩
  rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply, Complex.star_def]
  by_cases hab : G a b = 0
  · simp [hab]
  have hba : G b a = conj (G a b) := (congrFun (congrFun hG b) a).symm
  have hba0 : G b a ≠ 0 := by rw [hba]; exact (map_ne_zero _).2 hab
  have ha := hd a (by rwa [h2 a b hab])
  have hb := hd b (by rwa [h2 b a hba0])
  rw [h2 a b hab] at ha
  rw [h2 b a hba0, hba, Complex.conj_conj] at hb
  have ha' := congrArg conj ha
  rw [map_mul, map_pow, Complex.conj_conj, map_one] at ha'
  have : (conj (d a) * G a b * d b) ^ 2 = 1 := by linear_combination (d b ^ 2 * G a b) * ha' + hb
  rcases sq_eq_one_iff.1 this with e | e <;> simp [e]

def IsEigenbasis (s : Matrix (Fin n) (Fin n) ℂ) (g : GL (Fin n) ℂ) : Prop :=
  ∃ z : Fin n → ℂ, Function.Injective z ∧ s * g = g * diagonal z

theorem exists_isEigenbasis {s : Matrix (Fin n) (Fin n) ℂ} (hs : IsRegSS s) : ∃ g, IsEigenbasis s g := by
  have hc : s.charpoly.roots.card = n := by
    rw [← (IsAlgClosed.splits s.charpoly).natDegree_eq_card_roots, charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨z, hz⟩ : ∃ z : Fin n → ℂ, s.charpoly.roots = Finset.univ.val.map z := by
    induction' hr : s.charpoly.roots using Quotient.inductionOn with l
    rw [hr] at hc
    obtain rfl : l.length = n := hc
    exact ⟨l.get, by simp⟩
  have he : s.charpoly = (diagonal z).charpoly := by
    rw [charpoly_diagonal, (IsAlgClosed.splits s.charpoly).eq_prod_roots_of_monic s.charpoly_monic, hz,
      Multiset.map_map]
    rfl
  have hd : IsRegSS (diagonal z) := by rwa [IsRegSS, ← he]
  obtain ⟨g, hg⟩ := hd.exists_conj he
  refine ⟨g, z, ?_, hg⟩
  rwa [IsRegSS, charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff] at hd

theorem commute_diagonal {z : Fin n → ℂ} (hz : Function.Injective z) (w : Fin n → ℂ) {u : Matrix (Fin n) (Fin n) ℂ}
    (h : u * diagonal z = diagonal z * u) : u * diagonal w = diagonal w * u := by
  ext a b
  have := congrFun (congrFun h a) b
  rw [mul_diagonal, diagonal_mul] at this ⊢
  by_cases hab : a = b
  · rw [hab, mul_comm]
  · have h0 : u a b = 0 := by
      by_contra h0
      exact hab (hz (mul_left_cancel₀ h0 (by linear_combination -this)))
    simp [h0]

variable {ε : Fin n → Bool}

theorem exists_isEigenbasis_gram {s : UJ ε} (hs : IsRegSS (ujMat ε s)) : ∃ g : GL (Fin n) ℂ,
    IsEigenbasis (ujMat ε s) g ∧ ∀ a b, (g.1ᴴ * Jm ε * g.1) a b ∈ ({0, 1, -1} : Finset ℂ) := by
  obtain ⟨g, z, hz, hg⟩ := exists_isEigenbasis hs
  have hU : (ujMat ε s)ᴴ * Jm ε * ujMat ε s = Jm ε := s.2
  obtain ⟨d, hd0, hd⟩ := exists_scale (G := g.1ᴴ * Jm ε * g.1)
    (by simp [conjTranspose_mul, Jm_conjTranspose, Matrix.mul_assoc]) hz (by
      calc _ = (g.1 * diagonal z)ᴴ * Jm ε * (g.1 * diagonal z) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = g.1ᴴ * ((ujMat ε s)ᴴ * Jm ε * ujMat ε s) * g.1 := by
          simp only [← hg, conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hU])
  let D : GL (Fin n) ℂ := ⟨diagonal d, diagonal fun a => (d a)⁻¹, by simp [hd0], by simp [hd0]⟩
  refine ⟨g * D, ⟨z, hz, ?_⟩, fun a b => ?_⟩
  · change _ * (g.1 * diagonal d) = g.1 * diagonal d * _
    rw [← Matrix.mul_assoc, hg, Matrix.mul_assoc, Matrix.mul_assoc, commute_diagonal hz d (u := diagonal z) rfl]
  · have e : (g.1 * diagonal d)ᴴ * Jm ε * (g.1 * diagonal d) =
        (diagonal d)ᴴ * (g.1ᴴ * Jm ε * g.1) * diagonal d := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← e] at hd
    exact hd a b

theorem conj_mem_cent {s s' x u : UJ ε} {g g' : GL (Fin n) ℂ} (h : IsEigenbasis (ujMat ε s) g)
    (h' : IsEigenbasis (ujMat ε s') g') (hx : x.1 * g = g') (hu : u ∈ cent s) : x * u * x⁻¹ ∈ cent s' := by
  obtain ⟨z, hz, hg⟩ := h
  obtain ⟨w, -, hg'⟩ := h'
  have h1 : ujMat ε u * ujMat ε s = ujMat ε s * ujMat ε u := by
    rw [← map_mul, ← map_mul, GlobalTheory.Orb.mem_cent.1 hu]
  have e : ∀ {t : Matrix (Fin n) (Fin n) ℂ} {k : GL (Fin n) ℂ} {y}, t * k.1 = k.1 * diagonal y →
      diagonal y = (k⁻¹).1 * t * k.1 := fun ht => by rw [Matrix.mul_assoc, ht, Units.inv_mul_cancel_left]
  have h2 := commute_diagonal hz w (u := (g⁻¹).1 * ujMat ε u * g.1) (by
    simp only [e hg, Matrix.mul_assoc, Units.mul_inv_cancel_left]
    rw [← Matrix.mul_assoc (ujMat ε u), h1, Matrix.mul_assoc])
  rw [e hg', ← hx] at h2
  have h3 : (g⁻¹ * u.1 * g) * ((x.1 * g)⁻¹ * s'.1 * (x.1 * g)) = ((x.1 * g)⁻¹ * s'.1 * (x.1 * g)) * (g⁻¹ * u.1 * g) :=
    Units.ext h2
  refine GlobalTheory.Orb.mem_cent.2 (Subtype.ext ?_)
  have h4 := congrArg (fun y => (x.1 * g) * y * (x.1 * g)⁻¹) h3
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  simpa [mul_assoc] using h4

theorem conj_of_gram_eq {s s' : UJ ε} {g g' : GL (Fin n) ℂ} (h : IsEigenbasis (ujMat ε s) g)
    (h' : IsEigenbasis (ujMat ε s') g') (hG : g.1ᴴ * Jm ε * g.1 = g'.1ᴴ * Jm ε * g'.1) :
    ∃ x, (cent s).map (MulAut.conj x).toMonoidHom = cent s' := by
  have hx : g' * g⁻¹ ∈ UJ ε := by
    change (g'.1 * (g⁻¹).1)ᴴ * Jm ε * (g'.1 * (g⁻¹).1) = Jm ε
    calc _ = (g⁻¹).1ᴴ * (g'.1ᴴ * Jm ε * g'.1) * (g⁻¹).1 := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (g.1 * (g⁻¹).1)ᴴ * Jm ε * (g.1 * (g⁻¹).1) := by simp only [← hG, conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by simp
  refine ⟨⟨_, hx⟩, le_antisymm ?_ fun u hu => ⟨(⟨_, hx⟩ : UJ ε)⁻¹ * u * (⟨_, hx⟩ : UJ ε)⁻¹⁻¹,
    conj_mem_cent h' h (by simp) hu, by simp [mul_assoc]⟩⟩
  rintro _ ⟨u, hu, rfl⟩
  exact conj_mem_cent h h' (by simp) hu

theorem exists_system {H ι : Type} [Group H] [Finite ι] {P : Subgroup H → Prop} (R : Subgroup H → ι → Prop)
    (h1 : ∀ T, P T → ∃ i, R T i)
    (h2 : ∀ T T' i, R T i → R T' i → ∃ x, T.map (MulAut.conj x).toMonoidHom = T') :
    ∃ 𝒯 : Finset (Subgroup H), (∀ T ∈ 𝒯, P T) ∧
      ∀ T, P T → ∃! T', T' ∈ 𝒯 ∧ ∃ x, T.map (MulAut.conj x).toMonoidHom = T' := by
  classical
  have hm : ∀ (T : Subgroup H) x y, (T.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      T.map (MulAut.conj (y * x)).toMonoidHom := fun T x y => by
    rw [Subgroup.map_map, map_mul]; rfl
  have h0 : ∀ T : Subgroup H, T.map (MulAut.conj (1 : H)).toMonoidHom = T := fun T => by
    rw [map_one]; exact T.map_id
  let S : Setoid {T // P T} := ⟨fun T T' => ∃ x, T.1.map (MulAut.conj x).toMonoidHom = T'.1,
    fun T => ⟨1, h0 _⟩, fun ⟨x, hx⟩ => ⟨x⁻¹, by rw [← hx, hm, inv_mul_cancel, h0]⟩,
    fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨y * x, by rw [← hm, hx, hy]⟩⟩
  choose f hf using h1
  have : Finite (Quotient S) := Finite.of_injective (fun q : Quotient S => f q.out.1 q.out.2) fun q q' e =>
    Quotient.out_equiv_out.1 (h2 _ _ _ (hf q.out.1 q.out.2)
      ((congrArg (R q'.out.1) e).mpr (hf q'.out.1 q'.out.2)))
  have := Fintype.ofFinite (Quotient S)
  refine ⟨Finset.univ.image fun q : Quotient S => q.out.1, fun T hT => ?_, fun T hT =>
    ⟨(Quotient.mk S ⟨T, hT⟩).out.1, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
      S.symm (Quotient.mk_out (s := S) ⟨T, hT⟩)⟩, ?_⟩⟩
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hT
    exact q.out.2
  · rintro T' ⟨hT', hx⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hT'
    rw [Quotient.sound (s := S) (a := ⟨T, hT⟩) (b := q.out) hx, q.out_eq]

theorem exists_isCartanSystem : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ 𝒯 : Finset (Subgroup (UJ ε)), IsCartanSystem 𝒯 := by
  intro n ε
  refine exists_system (ι := Fin n → Fin n → ({0, 1, -1} : Finset ℂ)) (fun T i => ∃ (s : UJ ε) (g : GL (Fin n) ℂ),
    T = cent s ∧ IsEigenbasis (ujMat ε s) g ∧ ∀ a b, (g.1ᴴ * Jm ε * g.1) a b = i a b) ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨g, hg, hG⟩ := exists_isEigenbasis_gram hs
    exact ⟨fun a b => ⟨_, hG a b⟩, s, g, rfl, hg, fun _ _ => rfl⟩
  · rintro _ _ i ⟨s, g, rfl, hg, hG⟩ ⟨s', g', rfl, hg', hG'⟩
    exact conj_of_gram_eq hg hg' (Matrix.ext fun a b => (hG a b).trans (hG' a b).symm)

end GlobalTheory.CartanFinite
