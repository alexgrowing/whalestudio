import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TorsSqMap
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KaFormHomogeneous
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PwIsoIsGen
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CmpValBaseChangeSimilitude
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KaBaseChange

theorem torsSq_diag {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : Matrix Ix Ix R)
    (ga : Ix → Rˣ) (t : R) (H : TorsSq deg D t) :
    TorsSq deg (Matrix.diagonal (fun p => (ga p : R)) * D * Matrix.diagonal (fun p => (((ga p)⁻¹ : Rˣ) : R)))
      (t * ((∏ p : {p // Even (deg p)}, (ga p.1 : R)) * ∏ p : {p // ¬ Even (deg p)}, (((ga p.1)⁻¹ : Rˣ) : R)) ^ 2) := by
  obtain ⟨h, h₁, h₂, e, rfl⟩ := H
  set G := Matrix.diagonal (fun p => (ga p : R)) with hG
  set G' := Matrix.diagonal (fun p => (((ga p)⁻¹ : Rˣ) : R)) with hG'
  have hGG : G * G' = 1 := by
    rw [hG, hG', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    simp
  have hGG' : G' * G = 1 := mul_eq_one_comm.mp hGG
  refine ⟨G * h * G', fun p q hpq => ?_, ?_, e, ?_⟩
  · rw [hG, hG', Matrix.mul_diagonal, Matrix.diagonal_mul, h₁ p q hpq, mul_zero, zero_mul]
  · calc G * D * G' * (G * h * G') + G * h * G' * (G * D * G')
        = G * (D * (G' * G) * h + h * (G' * G) * D) * G' := by noncomm_ring
      _ = 1 := by rw [hGG', Matrix.mul_one, Matrix.mul_one, h₂, Matrix.mul_one, hGG]
  · have e₁ : G * D * G' + G * h * G' = G * (D + h) * G' := by noncomm_ring
    have e₂ : (G * (D + h) * G').submatrix (fun p : {p // Even (deg p)} => p.1) (fun p => (e p).1) =
        Matrix.diagonal (fun p : {p // Even (deg p)} => (ga p.1 : R)) *
          (D + h).submatrix (fun p : {p // Even (deg p)} => p.1) (fun p => (e p).1) *
          Matrix.diagonal (fun p : {p // Even (deg p)} => (((ga (e p).1)⁻¹ : Rˣ) : R)) := by
      ext p q
      simp only [hG, hG', Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [e₁, e₂, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
      Equiv.prod_comp e (fun p => (((ga p.1)⁻¹ : Rˣ) : R))]
    ring

theorem torsSq_kosD_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {g d : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (ev' : ∀ j, Matrix (Fin d) (Fin (N j)) R') (c : Fin d → R'ˣ) (t : R)
    (hev : ∀ a k, ev' 0 a k * (c a : R') = f (ev 0 a k)) (H : TorsSq kdeg (kosD m ev) t) :
    TorsSq kdeg (kosD (fun i j j' => (m i j j').map f) ev') (f t * (((∏ a, c a)⁻¹ : R'ˣ) : R') ^ 2) := by
  have H' := torsSq_diag _ _ (Sum.elim (fun _ => 1) (fun a => (c a)⁻¹)) _ (torsSq_map R _ kdeg _ R' f t H)
  convert H' using 2
  · ext p q
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
    rcases p with p | a <;> rcases q with ⟨I, k⟩ | b
    · simp [kosD, apply_ite f]
    · simp [kosD]
    · by_cases hI : I = ∅
      · subst hI
        have e := hev a k
        simp only [kosD, if_true, Sum.elim_inl, Sum.elim_inr, inv_one, Units.val_one, _root_.mul_one]
        exact ((Units.eq_mul_inv_iff_mul_eq _).2 e).trans (_root_.mul_comm _ _)
      · simp [kosD, hI]
    · simp [kosD]
  · congr 1
    rw [← Finset.prod_subtype (Finset.univ.filter fun p : KIx g d N => Even (kdeg p)) (by simp)
        (fun p => ((Sum.elim (fun _ => 1) (fun a => (c a)⁻¹) p : R'ˣ) : R')),
      ← Finset.prod_subtype (Finset.univ.filter fun p : KIx g d N => ¬ Even (kdeg p)) (by simp)
        (fun p => (((Sum.elim (fun _ => 1) (fun a => (c a)⁻¹) p : R'ˣ)⁻¹ : R'ˣ) : R')),
      Finset.prod_filter, Finset.prod_filter, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, inv_one, Units.val_one, ite_self, Finset.prod_const_one, _root_.one_mul]
    simp [kdeg, ← Finset.prod_inv_distrib]

theorem kaForm_map {R R' : Type} [CommRing R] [CommRing R'] (F : Rˣ →* R'ˣ) (g n l l' : ℕ) (t t' J : Rˣ)
    (lam lam' : ℕ → Rˣ) : F (kaForm g n l l' t t' lam lam' J) =
      kaForm g n l l' (F t) (F t') (fun j => F (lam j)) (fun j => F (lam' j)) (F J) := by
  simp only [kaForm, tComb, map_mul, map_zpow, map_pow, map_prod]

theorem via_mul {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X} {w : LB.Iso L' (L.pull φ)} {l l' k : ℕ}
    (hk : l + l' = k) {a' b' : ∀ i, Γ(Y, L'.U i)} {a b : ∀ j, Γ(X, L.U j)} (ha : KeyVia.Via w l a' a)
    (hb : KeyVia.Via w l' b' b) : KeyVia.Via w k (fun i => a' i * b' i) (fun j => a j * b j) := by
  intro j i h
  rw [map_mul, map_mul, ha j i h, hb j i h, ← hk, pow_add, _root_.mul_mul_mul_comm]

theorem coords_mul {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} {φ w}
    (hx : KeyVia x' x f φ w) {n l k N : ℕ} (hk : n + l = k) {s : RR x n} {s' : RR x' n} {e : RR x l} {e' : RR x' l}
    {b : Fin N → RR x k} {b' : Fin N → RR x' k} {c : Fin N → R} (hs : SecVia x' x φ w s' s)
    (he : SecVia x' x φ w e' e) (hb : ∀ i, SecVia x' x φ w (b' i) (b i))
    (hc : Coords x b c (fun i => (show Γ(x.P.A.left, x.P.L.U i) from s.f i) * (show Γ(x.P.A.left, x.P.L.U i) from e.f i))) :
    Coords x' b' (fun i => f (c i))
      (fun i => (show Γ(x'.P.A.left, x'.P.L.U i) from s'.f i) * (show Γ(x'.P.A.left, x'.P.L.U i) from e'.f i)) := by
  obtain ⟨-, -, -, ⟨hP, -⟩, -⟩ := hx
  have H := KeyVia.Via.comb (w := w) (l := k) (b' := fun i => (b' i).f) (b := fun i => (b i).f) f x.P.A.hom
    x'.P.A.hom hP.w hb c
  have H' := via_mul (w := w) hk (a' := s'.f) (b' := e'.f) (a := s.f) (b := e.f) hs he
  have H'' := (congrArg (KeyVia.Via w k _) (funext hc)).mp H'
  exact fun i => congrFun (KeyVia.Via.unique x.P.isLB H'' H) i

theorem kaVal_baseChange : Out.Laws → ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] [IsLocalRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (hg : x'.P.g = x.P.g) (s : Fin x.P.g → RR x n) (s' : Fin x'.P.g → RR x' n) (κ : Rˣ), admitted x.P.g n l l' al → KeyVia x' x f φ w → (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) → KaVal x n l l' al s κ → KaVal x' n l l' al s' (Units.map f.toMonoidHom κ) := by
  intro laws R R' _ _ _ _ _ x x' f φ w n l l' al hg s s' κ hadm hx hs hκ
  obtain ⟨⟨A', ab, g', sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := x'
  obtain rfl : g' = x.P.g := hg
  let x' : KeyIn R' := ⟨⟨A', ab, x.P.g, sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩
  obtain ⟨z, ch, b, b₂, t, t₂, J, lam, lam₂, hz, hJ, hb, hb₂, ht, ht₂, rfl⟩ := hκ
  obtain ⟨z', ch', u, hz', hjac, hval⟩ := etZ_baseChange R R' x x' f φ w n _ rfl s s' z ch hx hs hz
  have hex := ((KeyVia.main R R' x x' f).2 φ w hx).1
  have key : ∀ (l : ℕ) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (lam : ℕ → Rˣ) (t : Rˣ),
      x.P.g * n < l →
      (∀ j ≤ x.P.g, IsBasis x (b j) ∧ IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) (b j) (lam j)) → KosVal x l s z ch b t →
      ∃ b' : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x' (l - j * n),
        (∀ j ≤ x.P.g, IsBasis x' (b' j) ∧
          IsSquareDeterminantComparison x' (l - j * n) (al (l - j * n)) (b' j) (Units.map f.toMonoidHom (lam j))) ∧
        KosVal x' l s' z' ch' b' (Units.map f.toMonoidHom t * (∏ a, u a) ^ (-2 * (l : ℤ)) : R'ˣ) := by
    intro l b lam t hl hb ⟨m, hm, ht⟩
    choose b' hb' using fun j k => (hex _ (b j k)).exists
    refine ⟨b', fun j hj => ⟨?_, ?_⟩, fun i j j' => (m i j j').map f, fun i j hj k => ?_, ?_⟩
    · have h₁ : j * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
      exact (GlobalTheory.KeyBasis.main laws R x (l - j * n) (by omega)).2 (b j) (hb j hj).1 R' f x' φ w (b' j) hx (hb' j)
    · exact GlobalTheory.SimilBaseChange.cmpVal_baseChange_similitude R R' x x' f φ w _ _ rfl (b j) (b' j) (lam j) (hadm.2.2.2 _) hx (hb' j) (hb j hj).2
    · have h₁ : (j + 1) * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
      have h₂ : n + (l - (j + 1) * n) = l - j * n := by
        rw [Nat.add_mul, Nat.one_mul] at h₁ ⊢
        omega
      exact coords_mul hx h₂ (hs i) (hb' (j + 1) k) (hb' j) (hm i j hj k)
    · have H := torsSq_kosD_map f m
        (fun j => Matrix.of fun a k => valT (T := R) (z a).left (x.P.L.U (ch a)) ((b j k).f (ch a)))
        (fun j => Matrix.of fun a k => valT (T := R') (z' a).left (x'.P.L.U (ch' a)) ((b' j k).f (ch' a)))
        (fun a => u a ^ (l - 0 * n)) t
        (fun a k => (congrArg _ (Units.val_pow_eq_pow_val _ _)).trans (hval _ (b 0 k) (b' 0 k) a (hb' 0 k))) ht
      have e : (∏ a, u a) ^ (-2 * (l : ℤ)) = (∏ a, u a ^ (l - 0 * n))⁻¹ ^ 2 := by
        rw [Finset.prod_pow, Nat.zero_mul, Nat.sub_zero]
        group
      rw [e]
      exact H
  obtain ⟨c, hc, hct⟩ := key l b lam t hadm.2.1 hb ht
  obtain ⟨c₂, hc₂, hct₂⟩ := key l' b₂ lam₂ t₂ (hadm.2.1.trans hadm.2.2.1) hb₂ ht₂
  refine ⟨z', ch', c, c₂, _, _, Units.map f.toMonoidHom J * (∏ a, u a) ^ (-((x.P.g * n : ℕ) : ℤ)), _, _,
    hz', ?_, hc, hc₂, hct, hct₂, ?_⟩
  · rw [zpow_neg, zpow_natCast, Units.val_mul, eq_comm, Units.eq_mul_inv_iff_mul_eq, Units.val_pow_eq_pow_val,
      Units.coe_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine (Finset.prod_congr rfl fun a _ => hjac a).trans ?_
    rw [← map_prod, ← hJ]
    rfl
  · have H := kaForm_homogeneous R' x.P.g n l l' (Units.map f.toMonoidHom t) (Units.map f.toMonoidHom t₂)
      (Units.map f.toMonoidHom J) (∏ a, u a) 1 1 (fun j => Units.map f.toMonoidHom (lam j))
      (fun j => Units.map f.toMonoidHom (lam₂ j)) (fun _ => 1) (fun _ => 1) hadm.2.1 hadm.2.2.1
    simp only [one_zpow, one_pow, _root_.mul_one, Finset.prod_const_one] at H
    exact (kaForm_map _ _ _ _ _ _ _ _ _ _).trans H.symm

end GlobalTheory.KaBaseChange
end
