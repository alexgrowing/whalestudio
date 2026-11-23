import Mathlib
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
open scoped ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes

def nlen (O : Type) [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M] : ℝ≥0∞ :=
  ((Module.length O M : ℕ∞) : ℝ≥0∞) / ((Module.length O (O ⧸ Ideal.span {(l : O)}) : ℕ∞) : ℝ≥0∞)

def vO (O : Type) [CommRing O] (l : ℕ) (x : O) : ℝ≥0∞ := nlen O l (O ⧸ Ideal.span {x})

section Exc

variable {D : D7} (L : SizeData₂ D)

def sgPlus : ℤ := ⌊2 * L.sc.b / LevelStarExponents.lStar L⌋

def baseSizes : Set ℝ :=
  {W | W = L.sc.b ∨ W = L.sc.w'' D.R.n ∨
    ∃ t : D.host.TT, W = (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ)}

def window (W : ℝ) : Set ℤ :=
  {n | W + (-L.etaSz - 2 * (sgPlus L : ℝ) - 3) ≤ (n : ℝ) ∧
    (n : ℝ) ≤ W + (L.Sc + L.etaSz + L.etaSz + 2 * (sgPlus L : ℝ) + 4)}

def Exc : Set ℕ :=
  {l | l.Prime ∧ LevelStarExponents.lStar L < (l : ℝ) ∧ ∃ W ∈ baseSizes L, ∃ n ∈ window L W, (l : ℤ) ∣ n}

end Exc

section HidaSetting

variable (D : D7) (i : D.nd.Loc)

def liftIx : Fin D.R.m := ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def param (ρ : D.what₂.Tau) : Multiset ℚ :=
  (Finset.univ : Finset (Fin (D.R.k - 1))).val.map (fun a => (D.hc ρ).v a) +
  (Finset.univ : Finset (Fin D.R.m)).val.map (fun a => -(D.hc ρ).b a) +
  (Finset.Icc 1 D.R.t).val.map
    (fun c : ℕ => -(D.hc ρ).e (liftIx D i) + ((D.R.t : ℚ) + 1) / 2 - (c : ℚ))

def embSide (ρ : D.what₂.Tau) (s : Bool) : D.host.E →+* ℂ :=
  if s then D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)
  else ComplexEmbedding.conjugate (D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG))

def WeightTie : Prop :=
  ∃ s : Bool, ∀ ρ : D.what₂.Tau, ∃ c : ℚ,
    D.naut.infWt i (embSide D ρ s) = (param D i ρ).map (fun p => ((p + c : ℚ) : ℂ)) ∧
    D.naut.infWt i (embSide D ρ (!s)) = (param D i ρ).map (fun p => ((-(p + c) : ℚ) : ℂ))

def IsRankRPart (rπ : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) ∧
  ∃ e : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)),
    ∀ (g : GE D.nd) (u : Fin D.R.nV → KK D.nd i),
      e ((((rπ g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map
          (toK D.nd i)).mulVec u) =
        ((((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map
            (toK D.nd i)).mulVec (e u).1,
          fun c : Fin D.R.t =>
            toK D.nd i ((D.nd.chi i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c)

def vCC (π : D.nd.X i) : ℝ≥0∞ :=
  ⨅ f ∈ D.nd.cc i, vO (D.nd.O i) (D.nd.l i) (((f : D.nd.T i) : D.nd.X i → D.nd.O i) π)

def sPi (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) : ℝ≥0∞ :=
  nlen (D.nd.O i) (D.nd.l i) ↥(Br.selPi D.loc D.nbr i (fun _ => ρ) π)

def shaSum : ℝ≥0∞ :=
  ∑ e ∈ Finset.Ioo 0 D.R.t, ((Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) : ℕ∞) : ℝ≥0∞)

def vClass : ℝ≥0∞ := (padicValNat (D.nd.l i) (NumberField.classNumber D.host.E) : ℝ≥0∞)

def zetaP (P : HeightOneSpectrum (𝓞 D.host.E)) : D.nd.O i :=
  ((D.ntw.psiL i (D.nd.gam0 i P) : (D.nd.O i)ˣ) : D.nd.O i)

def epsQ : ℝ≥0∞ :=
  (D.R.t : ℝ≥0∞) * ∑ P ∈ D.nd.Q i, vO (D.nd.O i) (D.nd.l i) (zetaP D i P - 1)

end HidaSetting

def CongBound_at (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ i : D.nd.Loc,
    LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → D.nd.l i ∉ Exc L →
    WeightTie D i → HG D.nd D.naut i →
    ∀ r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), GoodR D.nd i r →
    ∀ π ∈ D.nd.Z i, ∀ ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i), IsRankRPart D i (r π) ρ →
      vCC D i π ≤ sPi D i π ρ + shaSum D i + vClass D i + epsQ D i

def CongBoundF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ a : Fm.Ix x, CongBound_at (Fm.D x a) (Fm.L x a)

def CongBound (𝒞 : FamClass) : Prop := Closed 𝒞 (fun Fm _ => CongBoundF Fm)

theorem zetaP_eq (D : D7) (i : D.nd.Loc) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P ∈ D.nd.Q i) :
    zetaP D i P = D.nd.zeta i P := by
  have hl : P ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i P (Or.inr hP)
  have hS : P ∉ D.nd.S i := fun h => Finset.disjoint_left.1 (D.nd.SQ_disj i) h hP
  rw [D.nd.S_def] at hS
  have h1 : D.ntw.chi1 (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) (D.nd.gam0 i P) = 1 := by
    refine D.ntw.twistCharacterFamily_unramified _ _ _ P ?_ ?_ ?_ (D.nd.plOm.1 P) (D.nd.plOm.2 P) _ (D.nd.locNd_chebotarevPlace_mem i P)
    · rw [D.ntw.twOf_l]; exact hl
    · intro k hk
      apply hS
      refine ⟨?_, hl⟩
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
    · intro h
      apply hS
      have h' : P ∈ (D.ntw.pD (D.ntw.twOf i) : Set _) := h
      rw [D.ntw.pD_eq, D.ntw.twOf_l] at h'
      exact ⟨Or.inr (Or.inr h'), hl⟩
  unfold zetaP NData.zeta
  rw [D.ntw.chi_tw]
  simp [h1]

theorem lStar_pos {D : D7} (L : SizeData₂ D) : 0 < LevelStarExponents.lStar L := by
  have hm : (0 : ℝ) < D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 0 < D.R.m)
  have hk : (0 : ℝ) < D.R.k := by
    have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 0 < D.R.k)
  have hn : (0 : ℝ) < D.R.n := by unfold Ranks.n; positivity
  have hx : 0 < L.sc.x := by have := L.sc.one_lt_alt; linarith
  have hL : 0 < L.sc.L := by unfold Scale.L; positivity
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hS := L.Sc_pos
  unfold LevelStarExponents.lStar
  positivity

theorem vO_l (D : D7) (i : D.nd.Loc) : vO (D.nd.O i) (D.nd.l i) (D.nd.l i : D.nd.O i) = 1 := by
  have hp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have h0 : (D.nd.l i : D.nd.O i) ≠ 0 := by
    intro h
    have h1 : (D.nd.embK i) ((D.nd.l i : ℕ) : D.what₂.LL) = 0 := by
      rw [map_natCast, ← map_natCast (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))), h, map_zero]
    have h2 : ((D.nd.l i : ℕ) : D.what₂.LL) = 0 := (map_eq_zero _).1 h1
    exact hp.ne_zero (by exact_mod_cast h2)
  have hu : ¬ IsUnit (D.nd.l i : D.nd.O i) := by
    intro hu
    have hinj : Function.Injective (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      by_contra hz0
      rw [PadicInt.unitCoeff_spec hz0, map_mul, map_pow, map_natCast] at hz
      rcases mul_eq_zero.1 hz with h | h
      · exact ((PadicInt.unitCoeff hz0).isUnit.map _).ne_zero h
      · exact h0 (pow_eq_zero_iff'.1 h).1
    haveI : FaithfulSMul ℤ_[D.nd.l i] (D.nd.O i) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    have : IsUnit ((D.nd.l i : ℕ) : ℤ_[D.nd.l i]) :=
      IsLocalHom.map_nonunit (f := algebraMap ℤ_[D.nd.l i] (D.nd.O i)) _ (by rw [map_natCast]; exact hu)
    exact PadicInt.irreducible_p.not_isUnit this
  unfold vO nlen
  apply ENNReal.div_self
  · haveI : Nontrivial (D.nd.O i ⧸ Ideal.span {(D.nd.l i : D.nd.O i)}) :=
      Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])
    simpa using (Module.length_pos (R := D.nd.O i)).ne'
  · have hf : IsFiniteLength (D.nd.O i) (D.nd.O i ⧸ Ideal.span {(D.nd.l i : D.nd.O i)}) :=
      isFiniteLength_quotient_span_singleton (D.nd.O i) (mem_nonZeroDivisors_of_ne_zero h0)
    simpa using Module.length_ne_top_iff.2 hf

end GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes

end
